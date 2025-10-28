import { BasicBlock, Function, BlockAddr } from "./disassembly/function.ts";
import { asRegister, Instruction, isRegister, Register, RegisterIndex } from "./disassembly/instruction.ts";
import DominanceGraph from './utils/DominanceGraph.ts';
import { exceptionHandlersByAddress } from './utils/exceptions.ts';
import { analyseUseDefines, livenessAnalysis } from './utils/liveness.ts';
import mapEachBlocks from './utils/mapEachBlock.ts';
import { setEquals } from './utils/set.ts';

export type RegisterVersion = number;
export interface SSARegister extends Register {
	version: RegisterVersion;
};

export function ssaRegisterEquals(left: SSARegister, right: SSARegister) {
	if (left.index !== right.index) return false;
	if (left.version !== right.version) return false;

	return true;
}

export type InstructionWithSSA<T> = T extends Instruction ? T & {
	defs: {
		[K in keyof T as T[K] extends Register ? K : never]: SSARegister;
	};
	uses: {
		[K in keyof T as T[K] extends Register | Register[] ? K : never]: T[K] extends Register ? SSARegister : SSARegister[];
	} & {
		[K in keyof T as K extends 'argumentCount' ? T[K] extends number ? 'arguments' : never : never]: SSARegister[];
	};
} : never;


export interface PhiInst {
	instruction: 'Phi';
	destination: SSARegister;
	sources: Map<BlockAddr, SSARegister>;
};

export type SSAInstruction = InstructionWithSSA<Instruction> | PhiInst;

export interface SSABasicBlock extends BasicBlock {
	ssaInstructions: SSAInstruction[];
};

function splitProtectedBlocks(func: Function) {
	const liveness = livenessAnalysis(func);
	// https://raw.githubusercontent.com/LLVM-but-worse/maple-ir/master/docs/maple-ir.pdf
	const localsMap = mapEachBlocks(func.basicBlocks, () => new Set<RegisterIndex>());
	for (const [addr, block] of func.basicBlocks) {
		let newLocals = localsMap.get(addr)!
		for (const { catchOffset } of exceptionHandlersByAddress(block.address, func.exceptionHandlers)) {
			newLocals = newLocals.union(liveness.blockLiveness.get(catchOffset)!.liveIn);
		}

		localsMap.set(addr, newLocals);
	}

	function split(block: BasicBlock, start: BlockAddr) {
		const instrIndex = block.instructions.findIndex(({ functionLocalOffset }) => functionLocalOffset === start);
		if (instrIndex === -1) throw new Error();

		func.basicBlocks.set(start, {
			address: start,
			consequentAddresses: block.consequentAddresses,
			instructions: block.instructions.slice(instrIndex),
			predicate: block.predicate,
		});

		block.instructions = block.instructions.slice(0, instrIndex)
		block.consequentAddresses = [start];
		block.predicate = null;
	}

	for (const [addr, block] of func.basicBlocks) {
		const locals = localsMap.get(addr)!;
		if (locals.size === 0) continue;

		let checkSplit = false;
		for (const instruction of block.instructions) {
			if (checkSplit && instruction.instruction == 'Mov' && locals.has(instruction.destination.index)) {
				split(block, instruction.functionLocalOffset);
				checkSplit = false;
			} else if (!['Mov', 'Catch'].includes(instruction.instruction)) {
				checkSplit = true;
			}
		}
	}
}

export class SSAFunction {
	_func: Function;
	basicBlocks: Map<BlockAddr, SSABasicBlock>;

	constructor(func: Function) {
		this._func = func;

		splitProtectedBlocks(this._func);

		const { basicBlocks } = this._func;

		const liveness = livenessAnalysis(func);

		// TODO: use liveness instead?
		const varDefs = new Map<RegisterIndex, Set<BlockAddr>>();
		for (const block of basicBlocks.values()) {
			for (const instr of block.instructions) {
				for (const assigned of Object.values(analyseUseDefines(instr).defs)) {
					if (!varDefs.has(assigned.index)) {
						varDefs.set(assigned.index, new Set());
					}

					varDefs.get(assigned.index)!.add(block.address);
				}
			}
		}

		const g = new DominanceGraph(this._func);

		const phiNodes = mapEachBlocks(basicBlocks, () => new Set<RegisterIndex>());
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

		// TODO: handle catch_addr phis and split at definitions of each input??

		const ssaBasicBlocks = new Map<BlockAddr, SSABasicBlock>();
		const phiSourcesBySuccessor = mapEachBlocks(basicBlocks, () => new Map<RegisterIndex, Map<BlockAddr, SSARegister>>());
		const phiDests = mapEachBlocks(basicBlocks, () => new Map<RegisterIndex, SSARegister>());

		const renameBlock = (addr: BlockAddr) => {
			const block = basicBlocks.get(addr)!;
			const ssaInstructions: SSAInstruction[] = [];

			for (const phiRegDest of phiNodes.get(addr) ?? []) {
				phiDests.get(addr)!.set(phiRegDest, this.#nextVersionOf(phiRegDest));
			}

			// rename normal instructions
			for (const instr of block.instructions) {
				const { defs, uses } = analyseUseDefines(instr);
				const ssaUses = Object.fromEntries(Object.entries(uses).map(([key, u]) => {
					if (Array.isArray(u)) {
						return [key, u.map(({index}) => this.#currentVersionOf(index))]
					}
					return [key, this.#currentVersionOf(u.index)]
				}));

				const ssaDefs = Object.fromEntries(Object.entries(defs).map(([key, d]) => {
					return [key, this.#pushRegisterStack(d)];
				})) as InstructionWithSSA<typeof instr>['defs'];
				ssaInstructions.push({ ...instr, defs: ssaDefs as any, uses: ssaUses });
			}

			for (const s of g.successorsOf(addr)) {
				const successorPhiSources = phiSourcesBySuccessor.get(s)!;
				for (const phi of phiNodes.get(s) ?? []) {
					let sourceMap = successorPhiSources.get(phi);
					if (!sourceMap) {
						successorPhiSources.set(phi, sourceMap = new Map());
					}

					if (sourceMap.has(addr)) {
						throw new Error();
					}

					sourceMap.set(addr, this.#currentVersionOf(phi));
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

			// pop stack after leaving block
			for (const instr of ssaInstructions) {
				if (instr.instruction === 'Phi') {
					this.#popRegisterStack(instr.destination);
					continue;
				}
				Object.values(instr.defs).forEach(this.#popRegisterStack.bind(this))
			}
		}

		renameBlock(0);

		for (const [addr, phiDestinations] of phiDests) {
			const ssaBlock = ssaBasicBlocks.get(addr)!;
			for (const destination of phiDestinations.values()) {
				if (!liveness.blockLiveness.get(addr)!.liveIn.has(destination.index)) continue;

				const sources = phiSourcesBySuccessor.get(addr)!.get(destination.index)!;

				// TODO: deal with predecessors that do not assign to phi'd registers
				if (!setEquals(
					new Set(g.predecessorsOf(addr)),
					new Set(sources.keys()),
				)) {
					console.log(addr);
					console.log(g.predecessorsOf(addr));
					console.log(sources.keys())
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

	get id() { return this._func.id; }
	get name() { return this._func.name; }
	get paramCount() { return this._func.paramCount; }
	get frameSize() { return this._func.frameSize; }
	get envSize() { return this._func.envSize; }
	get highestReadCacheIndex() { return this._func.highestReadCacheIndex; }
	get highestWriteCacheIndex() { return this._func.highestWriteCacheIndex; }
	get strict() { return this._func.strict; }
	get prohibitInvoke() { return this._func.prohibitInvoke; }
	get exceptionHandlers() { return this._func.exceptionHandlers; }

	get trampolines() { return this._func.trampolines; }

	#versionCounters = new Map<RegisterIndex, RegisterVersion>();
	#stacks = new Map<RegisterIndex, SSARegister[]>();

	#nextVersionOf(reg: Register | RegisterIndex): SSARegister {
		if (isRegister(reg)) reg = reg.index;

		const cur = this.#versionCounters.get(reg) ?? 0;
		const newVersion = cur + 1;
		this.#versionCounters.set(reg, newVersion);

		const versioned = { ...asRegister(reg), version: newVersion }; 
		if (!this.#stacks.has(reg)) this.#stacks.set(reg, []);
		this.#stacks.get(reg)!.push(versioned);
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

		const ssa = this.#nextVersionOf(reg);
		if (!this.#stacks.has(reg)) this.#stacks.set(reg, []);
		this.#stacks.get(reg)!.push(ssa);

		return ssa;
	}

	#popRegisterStack(reg: Register | RegisterIndex) {
		if (isRegister(reg)) reg = reg.index;

		return this.#stacks.get(reg)?.pop();
	}
};