import { assert } from 'node:console';
import { BlockAddr, FunctionExceptionHandler } from '../../disassembly/function.ts';
import { RegisterIndex } from '../../disassembly/instruction.ts';
import { RegisterVersion, SSABasicBlock, SSAInstruction, SSARegister } from '../../ssa.ts';
import { setEquals } from '../../utils/set.ts';
import { LiftError } from '../error.ts';
import { IRFunction } from './mod.ts';

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

function compareBlocks(func: IRFunction, [canonicalStart, ...otherStart]: [number, ...number[]]) {
	if (otherStart.length === 0) return true;

    const canonicalToBlock = new Map<BlockAddr, Map<RegisterIndex, Map<RegisterVersion, SSARegister>>>();
    const blockToCanonical = new Map<BlockAddr, Map<RegisterIndex, Map<RegisterVersion, SSARegister>>>();

    const ensureMaps = (addr: BlockAddr, reg?: RegisterIndex) => {
        if (!canonicalToBlock.has(addr)) canonicalToBlock.set(addr, new Map());
        if (!blockToCanonical.has(addr)) blockToCanonical.set(addr, new Map());

		if (reg) {
			const toBlock = canonicalToBlock.get(addr)!;
			const toCanonical = blockToCanonical.get(addr)!;

			if (!toBlock.has(reg)) toBlock.set(reg, new Map());
			if (!toCanonical.has(reg)) toCanonical.set(reg, new Map());
		}
    };

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
        ensureMaps(addr, canonical.index);
        ensureMaps(addr, current.index);

        const toBlock = canonicalToBlock.get(addr)!;
        const toCanonical = blockToCanonical.get(addr)!;

        const mapped = toBlock.get(canonical.index)!.get(canonical.version);
        if (mapped && (mapped.index !== current.index || mapped.version !== current.version)) return false;

        const reverse = toCanonical.get(current.index)!.get(current.version);
        if (reverse && (reverse.index !== canonical.index || reverse.version !== canonical.version)) return false;

        if (!mapped) {
            toBlock.get(canonical.index)!.set(canonical.version, current);
            toCanonical.get(current.index)!.set(current.version, canonical);
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

type TryRecordId = BlockAddr;

class TryRecord {
	catchAddress: BlockAddr | TryRecordId;
	ranges: FunctionExceptionHandler[] = [];
	innerTryRecords = new Set<TryRecordId>();

	catchBody: Set<BlockAddr> | null = null; // "directly" protected blocks within the catch body, usually catch blocks of inner trys
	finallyAddress: number | null = null;

	constructor(catchAddress: number) {
		this.catchAddress = catchAddress;
	}

	get minTryStart() {
		return Math.min(...this.ranges.map(({tryStart}) => tryStart))
	}

	get maxTryEnd() {
		return Math.max(...this.ranges.map(({tryEnd}) => tryEnd))
	}


	toString() {
		return `TryRecord @ ${this.catchAddress.toString(16)} { protectedBlocks: {${[...this.protectedBlocks].map(n => n.toString(16)).join(', ')}}, innerTryRecords: {${[...this.innerTryRecords].map(n => n.toString(16)).join(', ')}} }`
	}
}

export function structureTry(func: IRFunction) {
	if (func.exceptionHandlers.length === 0) return;

	// https://github.com/leibnitz27/cfr/blob/3d1d0f4c6db372090d9cd4c08c55f88a0ffe7237/src/org/benf/cfr/reader/entities/exceptions/ExceptionAggregator.java#L256
	// TODO: need to expand ranges into try catch returns
	// 1: Ret
	// 2: ResumeGenerator and its corresponding return block
	// 3: YieldStar
	// 4: Break/Continue(??)
	const records = new Map<BlockAddr, TryRecord>();
	for (const handler of func.exceptionHandlers) {
		if (!records.has(handler.catchOffset)) {
			records.set(handler.catchOffset, new TryRecord(handler.catchOffset));
		}

		records.get(handler.catchOffset)!.ranges.push(handler);
	}

    for (const record of records.values()) {
        record.ranges.sort((a, b) => a.tryStart - b.tryStart);
    }

	interface Event {
		pos: BlockAddr;
		isStart: boolean;
		catchOffset: BlockAddr;
	}

	const events: Event[] = [];
	for (const r of func.ssa.exceptionHandlers) {
		events.push({ pos: r.tryStart, isStart: true, catchOffset: r.catchOffset});
		events.push({ pos: r.tryEnd, isStart: false, catchOffset: r.catchOffset});
	}

	events.sort((a, b) =>
		a.pos !== b.pos
			? a.pos - b.pos
			: (a.isStart === b.isStart ? 0 : a.isStart ? -1 : 1)
	);

	const stack: BlockAddr[] = [];

	const parentOf = new Map<BlockAddr, BlockAddr | null>();

	for (const catchOffset of records.keys()) {
		parentOf.set(catchOffset, null);
	}

	// --- Sweep line ----------------------------------------------------------
	for (const ev of events) {
		if (ev.isStart) {
			// Starting a handler range
			if (stack.length > 0) {
				const parent = stack[stack.length - 1];
				parentOf.set(ev.catchOffset, parent);
			}
			stack.push(ev.catchOffset);
		} else {
			// Ending a handler range
			// Pop matching handler from stack
			let popped: BlockAddr | undefined = undefined;
			if (stack.length && stack[stack.length - 1] === ev.catchOffset) {
				popped = stack.pop();
			} else {
				const idx = stack.lastIndexOf(ev.catchOffset);
				if (idx >= 0) {
					stack.splice(idx, 1);
					popped = ev.catchOffset;
				}
			}
		}
	}

	// --- Construct tree from parentOf map -----------------------------------
	for (const [childId, parentId] of parentOf.entries()) {
		if (parentId) {
			const parent = records.get(parentId)!;
			parent.innerTryRecords.add(childId);
		}
	}


	/*
	const potentialTrys = new Set<BlockAddr>();
	const potentialFinallies = new Set<BlockAddr>();

	const allCatchAddrs = new Set(records.keys());

	for (const { protectedRanges } of records.values()) {
		if (new Set(protectedRanges.keys()).intersection(allCatchAddrs).size === 0) {
			//TODO
			continue;
		}
	}
	*/

	// TODO:
	// check: finally blocks have a TryRecord protecting only the body and catch blocks of the actual TryRecord
	debugger;
}

export function findFinallyBlocks(func: IRFunction) {
	if (func.exceptionHandlers.length === 0) return;

	// TODO: Catch deduplication here
	// Gather every block which may have a catch
	const regionHandlers = new Map<BlockAddr, Map<BlockAddr, Set<BlockAddr>>>();
	const catchFlows = new Map<BlockAddr, { tryStart: BlockAddr, tryEnd: BlockAddr }[]>();
	for (const { tryStart, tryEnd, catchOffset } of func.ssa.exceptionHandlers) {
		let startMap = regionHandlers.get(tryStart);
		if (!startMap) {
			regionHandlers.set(tryStart, startMap = new Map());
		}

		let handlers = startMap.get(tryEnd);
		if (!handlers) {
			startMap.set(tryEnd, handlers = new Set());
		}

		handlers.add(catchOffset);

		let incomingRegions = catchFlows.get(catchOffset);
		if (!incomingRegions) {
			catchFlows.set(catchOffset, incomingRegions = []);
		}

		incomingRegions.push({ tryStart, tryEnd });
	}

	// K: Canonical catch block V: { [Child catch address]: Finally trailer start }
	const finallyBlocks = new Map<BlockAddr, Map<BlockAddr, BlockAddr>>();
	const yieldRetToFinally = new Map<BlockAddr, Set<BlockAddr>>();
	for (const innerCatchAddr of catchFlows.keys()) {
		const catchEnds = regionHandlers.get(innerCatchAddr);
		if (!catchEnds) continue;

		for (const [innerCatchEnd, parentCatches] of catchEnds) {
			for (const parentCatchAddr of parentCatches) {
				let catchAddr = innerCatchAddr;
				let catchTrailerAddr = innerCatchEnd;
				let finallyCatchAddr = parentCatchAddr;

				if (parentCatches.size > 1 && regionHandlers.has(parentCatchAddr)) {
					const surroundingCatch = parentCatchAddr;
					const surroundingCatchEnds = regionHandlers.get(surroundingCatch);
					if (surroundingCatchEnds?.size !== 1) {
						throw new LiftError('Expected a catch block');
					}

					const [surroundingCatchTrailer, grandparentCatches] = surroundingCatchEnds.entries().next().value!;
					if (grandparentCatches.size !== 1) {
						throw new LiftError('Expected a finally block to handle catch');
					}

					const outerCatchAddr = grandparentCatches.values().next().value!;

					catchAddr = surroundingCatch;
					catchTrailerAddr = surroundingCatchTrailer;
					finallyCatchAddr = outerCatchAddr;
				}

				let finallyCopies = finallyBlocks.get(finallyCatchAddr);
				if (!finallyCopies) finallyBlocks.set(finallyCatchAddr, finallyCopies = new Map());
				if (finallyCopies.has(catchAddr)) {
					assert(finallyCopies.get(catchAddr) === catchTrailerAddr, `${finallyCopies.get(catchAddr)} === ${catchTrailerAddr}`);
				} else {
					finallyCopies.set(catchAddr, catchTrailerAddr);
				}

				if (func.returnBlocks.has(catchTrailerAddr)) {
					let yieldRetSet = yieldRetToFinally.get(catchTrailerAddr);
					if (!yieldRetSet) yieldRetToFinally.set(catchTrailerAddr, yieldRetSet = new Set());
					yieldRetSet.add(finallyCatchAddr)
				}
			}
		}
	}

	// expect
	// c5 (canonical)
	//	93, ab (catch trailer)
	//	41?, 58
	//  71?, 7a
	for (const [k, v] of finallyBlocks) {
		console.log(k.toString(16));
		for (const [kk, vv] of v) {
			console.log("\t" + kk.toString(16) + ", " + vv.toString(16));
		}
	}

	debugger;

	// const tryInfo: { tryStart: BlockAddr; catchStart: BlockAddr; finallyStart?: BlockAddr}[] = [];

	/*
	if (this.isGenerator) {
		console.log(this.yieldEndBlocks)
		for (const [tryStart, ends] of regionHandlers) {
			try {
				if (ends.size !== 2) continue;
			
				console.log(tryStart, ends);

				const regionCatches = new Map([...ends].map(([tryEnd, catches]) => {
					if (catches.size !== 1) throw new LiftError('bruh');
					return [tryEnd, catches.values().next().value!];
				}));

				console.log(regionCatches);
			} catch {
				continue;
			}
		}
		debugger;
	}
	*/
}
