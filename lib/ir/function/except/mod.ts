import { BlockAddr, FunctionExceptionHandler } from '../../../hbc/disassembly/function.ts';
import { RegisterIndex } from '../../../hbc/disassembly/instruction.ts';
import { RegisterVersion, SSABasicBlock, SSAInstruction, SSARegister } from '../../../ssa.ts';
import { AddressSet, setEquals } from '../../../utils/set.ts';
import { LiftError } from '../../error.ts';
import { IRFunction } from '../mod.ts';
import { exceptionHandlersByAddress } from '../../../hbc/utils/exceptions.ts';
import { AddressMap, MapWithDefault } from '../../../utils/map.ts';
import { AddressGraph } from '../../../utils/graph.ts';
import DominanceGraph from '../../../utils/DominanceGraph.ts';

type InstrPointer = {
	block: SSABasicBlock;
	index: number;
};
function findPointer(func: IRFunction, addr: number): InstrPointer | undefined {
	for (const block of func.ssa.basicBlocks.values()) {
		for (let index = 0; index < block.ssaInstructions.length; index++) {
			const instr = block.ssaInstructions[index];
			if (instr.instruction === 'Phi') {
				continue;
			}

			if (addr === instr.functionLocalOffset) {
				return { block, index };
			}
		}
	}
}

class SSARegisterMap<V> {
	#map = new MapWithDefault<RegisterIndex, Map<RegisterVersion, V>>();

	set(key: SSARegister, value: V) {
		this.#map.getWithDefault(
			key.index,
			() => new Map(),
		).set(
			key.version,
			value,
		);
	}

	get(key: SSARegister): V | undefined {
		return this.#map.get(key.index)?.get(key.version);
	}
}

function compareBlocks(func: IRFunction, [canonicalStart, ...otherStart]: [number, ...number[]]) {
	if (otherStart.length === 0) return true;

    const canonicalToBlock = new AddressMap<SSARegisterMap<SSARegister>>();
    const blockToCanonical = new AddressMap<SSARegisterMap<SSARegister>>();

	const canonicalPtr = findPointer(func, canonicalStart);
	if (!canonicalPtr) throw new LiftError('');

	const pointers: InstrPointer[] = [];
	for (const addr of otherStart) {
		const pointer = findPointer(func, addr);
		if (!pointer) throw new Error();

		pointers.push(pointer);
	}

    const nInstr = canonicalPtr.block.instructions.length - canonicalPtr.index;

    const registersEqual = (canonical: SSARegister, current: SSARegister, addr: BlockAddr): boolean => {
		const toBlock = canonicalToBlock.getWithDefault(
			addr,
			() => new SSARegisterMap(),
		);
		const toCanonical = blockToCanonical.getWithDefault(
			addr,
			() => new SSARegisterMap(),
		);
        const mapped = toBlock.get(canonical);
        const reverse = toCanonical.get(current);

        if (mapped && (mapped.index !== current.index || mapped.version !== current.version)) return false;
        if (reverse && (reverse.index !== canonical.index || reverse.version !== canonical.version)) return false;

        if (!mapped) {
			if (reverse) throw new Error();

            toBlock.set(canonical, current);
            toCanonical.set(current, canonical);
        }

        return true;
    };

    const instrsEqual = (instrs: SSAInstruction[]): boolean => {
        const canonical = instrs[0];

        for (let i = 1; i < instrs.length; i++) {
            const other = instrs[i];
			if (canonical.instruction !== 'Phi' && other.instruction !== 'Phi') {
				if (canonical.instruction !== other.instruction) return false;
				if (!setEquals(new Set(Object.keys(canonical.defs)), new Set(Object.keys(other.defs)))) return false;
				if (!setEquals(new Set(Object.keys(canonical.uses)), new Set(Object.keys(other.uses)))) return false;

				// TODO: other args
				// if (JSON.stringify(canonical.immediates ?? []) !== JSON.stringify(other.immediates ?? []))
				// 	return false;
			}
        }

        // All pairwise register mappings must hold
        for (let i = 1; i < instrs.length; i++) {
            const other = instrs[i];
            const blockName = pointers[i].block.address;

            if (canonical.instruction === 'Phi' && other.instruction === 'Phi') {
				if (!registersEqual(canonical.destination, other.destination, blockName)) return false;
				if (!setEquals(new Set(canonical.sources.keys()), new Set(other.sources.keys())))  return false;
                for (const pred of canonical.sources.keys()) {
                    const ca = canonical.sources.get(pred)!;
                    const cb = other.sources.get(pred)!;

                    if (!registersEqual(ca, cb, blockName)) return false;
                }
				continue;
            } else if (canonical.instruction !== 'Phi' && other.instruction !== 'Phi') {
				for (const key in canonical.uses) {
					// @ts-ignore
					const canonicalUse = canonical.uses[key];
					// @ts-ignore
					const otherUse = other.uses[key];
					if (Array.isArray(canonicalUse)) {
						if (Array.isArray(otherUse) && canonicalUse.length === otherUse.length) {
							for (let i = 0; i < canonicalUse.length; i++) {
								if (!registersEqual(canonicalUse[i], otherUse[i], blockName)) return false;
							}
						} else {
							return false;
						}
					} else {
						if (Array.isArray(otherUse)) return false;
						// @ts-ignore
						if (!registersEqual(canonical.uses[key], other.uses[key], blockName)) return false;
					}
				}

				for (const key in canonical.defs) {
					// @ts-ignore
					if (!registersEqual(canonical.defs[key], other.defs[key], blockName)) return false;
				}
			} else {
				return false;
			}
        }

        return true;
    };

    // Compare instruction-by-instruction
    for (let i = nInstr; i < nInstr; i++) {
        const instrs = pointers.map(({ block, index }) => block.ssaInstructions[index]);
        if (!instrsEqual(instrs)) return false;
		for (const p of pointers) p.index += 1;
    }

    return true;
}

/*
There are several instances of where a finally block is duplicated
- "Canonical": the "original" copy, a exception handler for a JS catch block
	- for when an error is raised in the catch block
- "TryTrailer": a copy after a try block
	- has the corresponding FunctionExceptionHandler end just as this finally code starts
	- end of Try blocks may just jump to "CatchTrailer" 
- "ControlFlowPrologue": a copy before a Ret, Jmp (break, continue) instruction
	- has the corresponding FunctionExceptionHandler end just as this finally code starts
	- may split the exception range for a try block
	- may not be an exact match with "Canonical" due to header code deduplication if one consequent address is a terminal block
- "CatchTrailer": a copy after a catch block
	- has the FunctionExceptionHandler "caught" by the "canonical" block end just as this finally code starts
*/

/*
Finally termination types
- "Rethrow"
- "Return"
- "ReturnOverride"
*/

export class ExceptionRange {
	index: number;

	start: BlockAddr;
	end: BlockAddr;

	protectedBlocks = new AddressSet(); // "directly" protected blocks

	constructor(index: number, info: FunctionExceptionHandler) {
		this.index = index;
		this.start = info.tryStart;
		this.end = info.tryEnd;
	}
}

export type HandlerId = BlockAddr;
export class HandlerRecord {
	catchAddress: BlockAddr; // Also handlerId
	innerTryRecords = new AddressSet<HandlerId>();
	ranges: ExceptionRange[] = [];

	catchBody: AddressSet | null = null; // "directly" protected blocks within the catch body, usually catch blocks of inner trys
	canonicalFinallyAddress: FinallyId | null = null;

	constructor(catchAddress: number) {
		this.catchAddress = catchAddress;
	}

	isProtectingBlock(address: BlockAddr) {
		return this.ranges.some(({start, end}) => address >= start && address < end);
	}

	get protectedBlocks() {
		return this.ranges.reduce((a, {protectedBlocks}) => a.union(protectedBlocks), new AddressSet());
	}

	toString() {
		return `TryRecord @ ${this.catchAddress.toString(16)} { protectedBlocks: {${[...this.protectedBlocks].map(n => n.toString(16)).join(', ')}}, innerTryRecords: {${[...this.innerTryRecords].map(n => n.toString(16)).join(', ')}} }`
	}
}

export class HandlerGraph {
	#records = new AddressMap<HandlerRecord, number>();
	#rangeToHandlers = new AddressMap<AddressGraph>();

    #strictDominatorMap = new AddressGraph<HandlerId, HandlerId>();
    #strictDominanceMap = new AddressGraph<HandlerId, HandlerId>();
	#dominatorTree = new AddressGraph<HandlerId, HandlerId>();
    
    constructor(
		func: IRFunction,
    ) {
		if (func._exceptionHandlers.length === 0) return;

		const handlerToRange = new Map<FunctionExceptionHandler, ExceptionRange>();
		for (let i = 0; i < func._exceptionHandlers.length; i++) {
			const handler = func._exceptionHandlers[i];
			const range = new ExceptionRange(i, handler);
			handlerToRange.set(handler, range);

			this.#records.getWithDefault(
				handler.catchOffset,
				() => new HandlerRecord(handler.catchOffset),
			).ranges.push(range);

			this.#rangeToHandlers.getWithDefault(
				handler.tryStart,
				() => new AddressGraph(),
			).addEdge(handler.tryEnd, handler.catchOffset);
		}

		for (const addr of func.ssa.basicBlocks.keys()) {
			for (const handler of exceptionHandlersByAddress(addr, func._exceptionHandlers)) {
				handlerToRange.get(handler)!.protectedBlocks.add(addr);
			}
		}

		// TODO: first construct finallyrecords from records where ranges.length == 1 and

        // For each handler, find which other handler "dominates" it
        // (i.e., protects it most directly)
        
        for (const [catchAddress, record] of this.#records) {
			const dominators = new AddressSet(
				this.#records.values().filter(
					r => HandlerGraph.#isStrictDominator(r, record)
				).map(r => r.catchAddress),
			);

			this.#strictDominatorMap.set(catchAddress, dominators);

			// TODO: consider selecting record with smallest protection size? 
        }

		/*
		let changed = false;
		do {
			changed = false;

			for (const [child, dominators] of this.#strictlyDominatedBy) {
				if (this.#immediatelyDominatedBy.has(child)) continue;

				const parents = new AddressSet();
				const filteredDominators = new AddressSet(dominators);
				for (const parent of dominators) {
					const grandparent = this.#immediatelyDominatedBy.get(parent);
					if (grandparent == null) continue;
					if (!filteredDominators.has(parent) || !filteredDominators.has(grandparent)) continue;

					filteredDominators.delete(parent);
					filteredDominators.delete(grandparent);

					parents.add(parent);
				}

				if (parents.size > 1) console.log(parents);
				let knownParent = null;
				if (parents.size === 1) {
					knownParent = [...parents][0];
				}

				if (filteredDominators.size === 0) {
					if (parents.size > 1) {
						throw new LiftError('Unresolved exception parent');
					}
					this.#immediatelyDominatedBy.set(child, knownParent);
					changed = true;
					continue;
				} else if (filteredDominators.size === 1) {
					const dominator = [...dominators][0];
					if (this.#immediatelyDominatedBy.get(dominator) === null) {
						this.#immediatelyDominatedBy.set(child, dominator);
						changed = true;
					}

					continue;
				}
			}
		} while (changed);
		*/
	
		for (const [key, value] of this.#strictDominatorMap) {
			for (const v of value) {
				this.#strictDominanceMap.addEdge(v, key);
			}
		}

		for (const [block, strictlyDominated] of this.#strictDominanceMap) {
			this.#dominatorTree.set(block, strictlyDominated.difference(new AddressSet(
				Array.from(strictlyDominated).flatMap((child) => [...(this.#strictDominanceMap.get(child)! ?? [])])
			)));
		}

		console.log(this.#strictDominatorMap);
		console.log(this.#dominatorTree);

		const getUnprotectedSuccessors = (addr: HandlerId) => {
			const record = this.#records.get(addr)!;
			return new AddressSet(
				[...record.protectedBlocks].flatMap(addr => func.ssa.basicBlocks.get(addr)!.consequentAddresses),
			).difference(
				record.protectedBlocks
			);
		}

		const g = new DominanceGraph(func.ssa);
		for (const [canonicalFinally, potentialCatches] of this.#dominatorTree) {
			const potentialFinallyStarts = getUnprotectedSuccessors(canonicalFinally)
			console.log(canonicalFinally.toString(16), potentialFinallyStarts);

			const fullyOverlappingCatches = new AddressSet();
			for (const potentialCatch of potentialCatches) {
				const unprotected = getUnprotectedSuccessors(potentialCatch);
				console.log(potentialCatch.toString(16), "unprotected", unprotected);
				if (unprotected.isSubsetOf(potentialFinallyStarts)) fullyOverlappingCatches.add(potentialCatch);
			}

			let attributedCatch = null;
			if (fullyOverlappingCatches.size === 1) {
				attributedCatch = [...fullyOverlappingCatches][0];
			} else {
				for (const c of fullyOverlappingCatches) {
					if (fullyOverlappingCatches.isSupersetOf(new AddressSet(g.dominatedBy(c)))) {
						attributedCatch = c;
						break;
					}
				}
			}

			if (attributedCatch === null) continue;
			
			console.log(canonicalFinally.toString(16), attributedCatch.toString(16));
		}
    }

	static #isStrictDominator(dominator: HandlerRecord, dominated: HandlerRecord) {
		if (dominator.catchAddress === dominated.catchAddress) return false;
		if (!dominator.isProtectingBlock(dominated.catchAddress)) return false;

		if (!dominated.protectedBlocks.isSubsetOf(dominator.protectedBlocks)) return false;

		return true;
	}
}

export interface FinallyRange {
	start: BlockAddr;
	end: BlockAddr | null;
}

export type FinallyId = BlockAddr;
export class FinallyRecord {
	canonicalFinallyAddress: BlockAddr; // also finallyId

	innerCanonicalFinallies = new AddressSet<FinallyId>();

	tryTrailer: FinallyRange | null = null;
	earlyTrailers: FinallyRange[] = [];
	catchTrailer: FinallyRange | null = null;

	constructor(address: BlockAddr) {
		this.canonicalFinallyAddress = address;
	}
};

