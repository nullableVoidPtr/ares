import { BasicBlock, BlockAddr, Function } from './hbc/disassembly/function.ts';
import {
	asRegister,
	Instruction,
	isRegister,
	Register,
	RegisterIndex,
} from './hbc/disassembly/instruction.ts';
import DominanceGraph from './utils/DominanceGraph.ts';
import { exceptionHandlersByAddress } from './hbc/utils/exceptions.ts';
import { livenessAnalysis } from './utils/liveness.ts';
import { analyseUseDefines } from './utils/useDefines.ts';
import { AddressMap, MapWithDefault } from './utils/map.ts';
import { AddressSet } from './utils/set.ts';

/**
 * A private copy of a function's disassembly, for building SSA over it.
 *
 * `SSAFunction`'s constructor rewrites what it is handed --
 * `trimProtectedRangeStarts` and `splitProtectedBlocks` both mutate the block
 * map -- so anything that builds SSA over a function it does not own has to copy
 * first, or the next reader sees a structure that has already been transformed.
 */
export function copyFunctionForSSA(func: Function): Function {
	return {
		...func,
		exceptionHandlers: func.exceptionHandlers.map((handler) => ({
			...handler,
		})),
		basicBlocks: new Map(
			[...func.basicBlocks].map(([address, block]) => [
				address,
				{
					...block,
					instructions: block.instructions.slice(),
					consequentAddresses: block.consequentAddresses.slice(),
					predicate: block.predicate == null
						? null
						: { ...block.predicate },
				},
			]),
		),
		trampolines: new Map(func.trampolines),
	};
}

export type RegisterVersion = number;
export interface SSARegister extends Register {
	version: RegisterVersion;
}

export function ssaRegisterEquals(left: SSARegister, right: SSARegister) {
	if (left.index !== right.index) return false;
	if (left.version !== right.version) return false;

	return true;
}

export type InstructionWithSSA<T> = T extends Instruction ? T & {
		defs: {
			[K in keyof T as T[K] extends Register ? K : never]: SSARegister;
		};
		uses:
			& {
				[
					K in keyof T as T[K] extends Register | Register[] ? K
						: never
				]: T[K] extends Register ? SSARegister : SSARegister[];
			}
			& {
				[
					K in keyof T as K extends 'argumentCount'
						? T[K] extends number ? 'arguments' : never
						: never
				]: SSARegister[];
			};
	}
	: never;

export interface PhiInst {
	instruction: 'Phi';
	destination: SSARegister;
	sources: AddressMap<SSARegister>;
}

export type SSAInstruction = InstructionWithSSA<Instruction> | PhiInst;

export interface SSABasicBlock extends BasicBlock {
	ssaInstructions: SSAInstruction[];
}

function splitBlockAt(func: Function, block: BasicBlock, start: BlockAddr) {
	const instrIndex = block.instructions.findIndex(({ functionLocalOffset }) =>
		functionLocalOffset === start
	);
	if (instrIndex === -1) {
		throw new Error(
			`Cannot split block 0x${block.address.toString(16)} at ` +
				`0x${start.toString(16)}: instruction is not in the block`,
		);
	}
	if (instrIndex === 0) return block;

	func.basicBlocks.set(start, {
		address: start,
		consequentAddresses: block.consequentAddresses,
		instructions: block.instructions.slice(instrIndex),
		predicate: block.predicate,
	});

	block.instructions = block.instructions.slice(0, instrIndex);
	block.consequentAddresses = [start];
	block.predicate = null;

	return func.basicBlocks.get(start)!;
}

function canHoistOutOfProtectedRange(instr: Instruction) {
	switch (instr.instruction) {
		case 'GetGlobalObject':
		case 'LoadConst':
		case 'LoadParam':
		case 'Mov':
			return true;
		default:
			return false;
	}
}

function trimProtectedRangeStarts(func: Function) {
	for (const handler of func.exceptionHandlers) {
		while (true) {
			const block = func.basicBlocks.get(handler.tryStart);
			if (!block) break;

			const firstProtected = block.instructions.find((instr) =>
				!canHoistOutOfProtectedRange(instr)
			);
			if (!firstProtected) {
				if (block.consequentAddresses.length !== 1) break;
				const successor = block.consequentAddresses[0];
				if (successor >= handler.tryEnd) break;
				handler.tryStart = successor;
				continue;
			}

			if (firstProtected.functionLocalOffset === handler.tryStart) break;
			if (firstProtected.functionLocalOffset >= handler.tryEnd) break;

			handler.tryStart = firstProtected.functionLocalOffset;
			splitBlockAt(func, block, handler.tryStart);
			break;
		}
	}
}

function splitProtectedBlocks(func: Function) {
	const liveness = livenessAnalysis(func);
	// https://raw.githubusercontent.com/LLVM-but-worse/maple-ir/master/docs/maple-ir.pdf
	const localsMap = AddressMap.mapEachBlock(
		func.basicBlocks,
		() => new Set<RegisterIndex>(),
	);
	for (const [addr, block] of func.basicBlocks) {
		let newLocals = localsMap.get(addr)!;
		for (
			const { catchOffset } of exceptionHandlersByAddress(
				block.address,
				func.exceptionHandlers,
			)
		) {
			newLocals = newLocals.union(
				liveness.blockLiveness.get(catchOffset)!.liveIn,
			);
		}

		localsMap.set(addr, newLocals);
	}

	// Splitting mutates func.basicBlocks. Only analyse the original blocks: every
	// new suffix inherits the live catch locals and is already covered by the
	// split points planned for its original block below.
	for (const [addr, block] of [...func.basicBlocks]) {
		const locals = localsMap.get(addr);
		if (!locals) continue;
		if (locals.size === 0) continue;

		const splitStarts: BlockAddr[] = [];
		let catchStateChanged = false;
		for (const instruction of block.instructions) {
			// One basic block has one exceptional edge and therefore one source
			// value for each landing-pad Phi. Once a catch-live register changes,
			// the next instruction that can throw must start a new block: an
			// exception before the write observes the old value, while an exception
			// after the successful write observes the new one.
			if (
				catchStateChanged && startsProtectedExceptionPoint(instruction)
			) {
				splitStarts.push(instruction.functionLocalOffset);
				catchStateChanged = false;
			}
			const { defs } = analyseUseDefines(instruction);
			const writesLocal = Object.values(defs).some((d) =>
				locals.has(d.index)
			);
			catchStateChanged ||= writesLocal;
		}

		// splitBlockAt truncates `block`. Applying offsets from the end keeps every
		// earlier offset in that block and builds the intended A -> B -> C chain.
		for (const start of splitStarts.toReversed()) {
			splitBlockAt(func, block, start);
		}
	}
}

/**
 * Reuse the small set of instructions that can safely be hoisted out of a
 * protected range as the definitely-non-throwing set. Sampling slightly before
 * any other non-throwing instruction is harmless, while sampling after a
 * throwing destination write observes a value that was never committed.
 */
function startsProtectedExceptionPoint(instruction: Instruction): boolean {
	return instruction.instruction !== 'Catch' &&
		!canHoistOutOfProtectedRange(instruction);
}

export class SSAFunction {
	_func: Function;
	basicBlocks: AddressMap<SSABasicBlock>;

	constructor(func: Function) {
		this._func = func;

		trimProtectedRangeStarts(this._func);
		splitProtectedBlocks(this._func);

		const { basicBlocks } = this._func;
		if (!basicBlocks.has(0)) {
			this.basicBlocks = new AddressMap<SSABasicBlock>();
			return;
		}

		const liveness = livenessAnalysis(func);

		// TODO: use liveness instead?
		const varDefs = new MapWithDefault<RegisterIndex, AddressSet>();
		for (const block of basicBlocks.values()) {
			for (const instr of block.instructions) {
				for (
					const assigned of Object.values(
						analyseUseDefines(instr).defs,
					)
				) {
					varDefs.getWithDefault(
						assigned.index,
						() => new AddressSet(),
					)!.add(block.address);
				}
			}
		}

		const g = new DominanceGraph(this._func, 0);

		const phiNodes = AddressMap.mapEachBlock(
			basicBlocks,
			() => new Set<RegisterIndex>(),
		);
		// A throwing instruction's destinations do not exist on its exceptional
		// edge. Model every catch-live register written by the protected region
		// explicitly at the landing pad, even when ordinary dominance would claim
		// a single protected definition reaches it. Treating the landing pad as a
		// definition also propagates the value into Phis at normal joins after the
		// catch.
		const forcedCatchPhis: Array<{
			catchOffset: BlockAddr;
			register: RegisterIndex;
		}> = [];
		for (const { catchOffset } of this._func.exceptionHandlers) {
			const catchPhis = phiNodes.get(catchOffset);
			if (!catchPhis) continue;
			for (
				const register
					of liveness.blockLiveness.get(catchOffset)?.liveIn ??
						[]
			) {
				const protectedDefinition = [...varDefs.get(register) ?? []]
					.some(
						(address) =>
							exceptionHandlersByAddress(
								address,
								this._func.exceptionHandlers,
							).some((handler) =>
								handler.catchOffset === catchOffset
							),
					);
				if (!protectedDefinition) continue;
				forcedCatchPhis.push({ catchOffset, register });
			}
		}
		for (const { catchOffset, register } of forcedCatchPhis) {
			phiNodes.get(catchOffset)!.add(register);
			varDefs.getWithDefault(register, () => new AddressSet())!.add(
				catchOffset,
			);
		}
		for (const [r, defBlocks] of varDefs.entries()) {
			const work = [...defBlocks];
			while (work.length) {
				const defBlock = work.pop()!;
				for (const block of g.dominanceFrontierOf(defBlock)) {
					const blockPhis = phiNodes.get(block)!;
					if (blockPhis.has(r)) continue;

					blockPhis.add(r);
					if (!(work.includes(block))) work.push(block);
				}
			}
		}

		const ssaBasicBlocks = new AddressMap<SSABasicBlock>();
		const phiSourcesBySuccessor = AddressMap.mapEachBlock(
			basicBlocks,
			() => new MapWithDefault<RegisterIndex, AddressMap<SSARegister>>(),
		);
		const phiDests = AddressMap.mapEachBlock(
			basicBlocks,
			() => new Map<RegisterIndex, SSARegister>(),
		);

		const renameBlock = (addr: BlockAddr) => {
			const block = basicBlocks.get(addr)!;
			const ssaInstructions: SSAInstruction[] = [];
			const exceptionalSuccessors = new AddressSet(
				exceptionHandlersByAddress(
					addr,
					this._func.exceptionHandlers,
				).map(({ catchOffset }) => catchOffset),
			);
			const exceptionalPhiSources = new AddressMap<
				Map<RegisterIndex, SSARegister>
			>();
			let sampledExceptionalSources = false;
			const sampleExceptionalSources = () => {
				if (sampledExceptionalSources) return;
				sampledExceptionalSources = true;
				for (const successor of exceptionalSuccessors) {
					const sources = new Map<RegisterIndex, SSARegister>();
					for (const phi of phiNodes.get(successor) ?? []) {
						sources.set(phi, this.#currentVersionOf(phi));
					}
					exceptionalPhiSources.set(successor, sources);
				}
			};

			for (const phiRegDest of phiNodes.get(addr) ?? []) {
				phiDests.get(addr)!.set(
					phiRegDest,
					this.#nextVersionOf(phiRegDest),
				);
			}

			// rename normal instructions
			for (const instr of block.instructions) {
				// An instruction destination does not exist when that instruction
				// throws. Protected blocks are split before every later write to a
				// catch-live register, so the state immediately before the first
				// possible throw is the value every exceptional edge from this block
				// must carry.
				if (startsProtectedExceptionPoint(instr)) {
					sampleExceptionalSources();
				}
				const { defs, uses } = analyseUseDefines(instr);
				const ssaUses = Object.fromEntries(
					Object.entries(uses).map(([key, u]) => {
						if (Array.isArray(u)) {
							return [
								key,
								u.map(({ index }) =>
									this.#currentVersionOf(index)
								),
							];
						}
						return [key, this.#currentVersionOf(u.index)];
					}),
				);

				const ssaDefs = Object.fromEntries(
					Object.entries(defs).map(([key, d]) => {
						return [key, this.#pushRegisterStack(d)];
					}),
				) as InstructionWithSSA<typeof instr>['defs'];
				ssaInstructions.push({
					...instr,
					defs: ssaDefs as any,
					uses: ssaUses,
				});
			}
			sampleExceptionalSources();

			for (const s of g.successorsOf(addr)) {
				const successorPhiSources = phiSourcesBySuccessor.get(s)!;
				for (const phi of phiNodes.get(s) ?? []) {
					const sourceMap = successorPhiSources.getWithDefault(
						phi,
						() => new AddressMap(),
					);

					if (sourceMap.has(addr)) {
						throw new Error();
					}

					const source = exceptionalSuccessors.has(s)
						? exceptionalPhiSources.get(s)?.get(phi)
						: undefined;
					sourceMap.set(
						addr,
						source ?? this.#currentVersionOf(phi),
					);
				}
			}

			// finalize block
			ssaBasicBlocks.set(addr, {
				...block,
				ssaInstructions,
			});

			for (const c of g.immediatelyDominatedBy(addr)) {
				renameBlock(c);
			}

			// pop stack after leaving block — normal instruction defs first, then phi defs.
			// Note: phi instructions are added to ssaInstructions via unshift() AFTER
			// renameBlock returns, so the Phi branch below never fires. Phi destinations
			// must be popped explicitly using the phiNodes set for this block.
			for (const instr of ssaInstructions.toReversed()) {
				if (instr.instruction === 'Phi') continue;
				for (const def of Object.values(instr.defs).toReversed()) {
					this.#popRegisterStack(def);
				}
			}
			for (const phiRegDest of phiNodes.get(addr) ?? []) {
				this.#popRegisterStack(phiRegDest);
			}
		};

		renameBlock(0);

		for (const [addr, phiDestinations] of phiDests) {
			const ssaBlock = ssaBasicBlocks.get(addr)!;
			for (const destination of phiDestinations.values()) {
				if (
					!liveness.blockLiveness.get(addr)!.liveIn.has(
						destination.index,
					)
				) continue;

				const sources = phiSourcesBySuccessor.get(addr)!.get(
					destination.index,
				)!;
				if (
					[...sources.values()].every((source) =>
						ssaRegisterEquals(source, destination)
					)
				) continue;

				// TODO: deal with predecessors that do not assign to phi'd registers
				const reachablePredecessors = new AddressSet(
					[...g.predecessorsOf(addr)].filter((predecessor) =>
						ssaBasicBlocks.has(predecessor)
					),
				);
				if (
					!reachablePredecessors.equals(
						new AddressSet(sources.keys()),
					)
				) {
					console.log(addr);
					console.log(reachablePredecessors);
					console.log(sources.keys());
					throw new Error();
				}

				ssaBlock.ssaInstructions.unshift({
					instruction: 'Phi',
					destination,
					sources,
				});
			}
		}

		this.basicBlocks = ssaBasicBlocks;
	}

	get id() {
		return this._func.id;
	}
	get name() {
		return this._func.name;
	}
	get paramCount() {
		return this._func.paramCount;
	}
	get frameSize() {
		return this._func.frameSize;
	}
	get envSize() {
		return this._func.envSize;
	}
	get loopDepth() {
		return this._func.loopDepth;
	}
	get numberRegCount() {
		return this._func.numberRegCount;
	}
	get nonPtrRegCount() {
		return this._func.nonPtrRegCount;
	}
	get highestReadCacheIndex() {
		return this._func.highestReadCacheIndex;
	}
	get highestWriteCacheIndex() {
		return this._func.highestWriteCacheIndex;
	}
	get readCacheSize() {
		return this._func.readCacheSize;
	}
	get writeCacheSize() {
		return this._func.writeCacheSize;
	}
	get privateNameCacheSize() {
		return this._func.privateNameCacheSize;
	}
	get strict() {
		return this._func.strict;
	}
	get prohibitInvoke() {
		return this._func.prohibitInvoke;
	}
	get exceptionHandlers() {
		return this._func.exceptionHandlers;
	}

	get trampolines() {
		return this._func.trampolines;
	}
	/**
	 * Allocate a definition introduced after the initial SSA rename.
	 *
	 * Keeping this counter on the SSA function preserves the single version
	 * namespace when later recovery passes replace bytecode control state with
	 * source-level definitions.
	 */
	allocateRegisterVersion(reg: Register | RegisterIndex): SSARegister {
		if (isRegister(reg)) reg = reg.index;

		const version = (this.#versionCounters.get(reg) ?? 0) + 1;
		this.#versionCounters.set(reg, version);
		return { ...asRegister(reg), version };
	}
	/** Allocate a register family for a memory location promoted after renaming. */
	allocateSyntheticRegisterIndex(): RegisterIndex {
		if (this.#nextSyntheticRegisterIndex == null) {
			this.#nextSyntheticRegisterIndex = Math.max(
				999_999,
				this.frameSize - 1,
				...this.#versionCounters.keys(),
			) + 1;
		}
		return this.#nextSyntheticRegisterIndex++;
	}

	#nextSyntheticRegisterIndex?: RegisterIndex;
	#versionCounters = new Map<RegisterIndex, RegisterVersion>();
	#stacks = new MapWithDefault<RegisterIndex, SSARegister[]>();

	#nextVersionOf(reg: Register | RegisterIndex): SSARegister {
		const versioned = this.allocateRegisterVersion(reg);
		this.#stacks.getWithDefault(versioned.index, () => [])!.push(versioned);
		return versioned;
	}

	#currentVersionOf(reg: Register | RegisterIndex): SSARegister {
		if (isRegister(reg)) reg = reg.index;

		const stack = this.#stacks.get(reg) ?? [];
		if (stack.length === 0) return { ...asRegister(reg), version: 0 }; // undefined version
		return stack[stack.length - 1];
	}

	#pushRegisterStack(reg: Register | RegisterIndex) {
		if (isRegister(reg)) reg = reg.index;

		return this.#nextVersionOf(reg);
	}

	#popRegisterStack(reg: Register | RegisterIndex) {
		if (isRegister(reg)) reg = reg.index;

		return this.#stacks.get(reg)?.pop();
	}
}
