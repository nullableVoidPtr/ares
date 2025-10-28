import { BlockAddr, FunctionExceptionHandler } from '../disassembly/function.ts';
import { Instruction, Register, RegisterIndex } from '../disassembly/instruction.ts';
import { exceptionHandlersByAddress } from './exceptions.ts';
import { setEquals } from './set.ts';

export function analyseUseDefines<T extends Instruction>(instr: T): { defs: Record<string, Register>; uses: Record<string, Register | Register[]> } {
	const defs: Record<string, Register> = {};
	const uses: Record<string, Register | Register[]> = {};

	if ("destination" in instr) defs.destination = instr.destination;
	if ("argument" in instr) uses.argument = instr.argument;
	if ("left" in instr) uses.left = instr.left;
	if ("right" in instr) uses.right = instr.right;
	if ("predicate" in instr) uses.predicate = instr.predicate;

	switch (instr.instruction) {
		case 'NewObjectWithParent':
			uses.parent = instr.parent;
			break;

		case 'Mov':
		case 'ThrowIfEmpty':
		case 'IteratorBegin':
			uses.source = instr.source;
			break;

		case 'StoreToEnvironment':
		case 'StoreNPToEnvironment':
			uses.value = instr.value;
		/* falls through */
		case 'LoadFromEnvironment':
		case 'CreateClosure':
		case 'CreateGeneratorClosure':
		case 'CreateAsyncClosure':
		case 'CreateGenerator':
			uses.environment = instr.environment;
			break;

		case 'PutByVal':
		case 'PutOwnByVal':
			uses.property = instr.property;
		/* falls through */
		case 'PutById':
		case 'TryPutById':
		case 'PutNewOwnById':
		case 'PutNewOwnNEById':
		case 'PutOwnByIndex':
			uses.value = instr.value;
		/* falls through */
		case 'TryGetById':
		case 'GetById':
		case 'DelById':
			uses.object = instr.object;
			break;

		case 'PutOwnGetterSetterByVal':
			uses.getter = instr.getter;
			uses.setter = instr.setter;
		/* falls through */
		case 'DelByVal':
		case 'GetByVal':
			uses.object = instr.object;
			uses.property = instr.property;
			break;

		case 'GetPNameList':
		case 'GetNextPName':
			uses.object = instr.object;
			uses.index = instr.index;
			uses.propertyListSize = instr.propertyListSize;
			break;

		case 'Call':
		case 'Construct': {
			uses.closure = instr.closure;
			uses.arguments = instr.arguments.slice();
			break;
		}

		case 'Ret':
			uses.argument = instr.argument;
			break;

		case 'DirectEval':
			uses.code = instr.code;
			break;

		case 'Throw':
			uses.exception = instr.exception;
			break;

		case 'CreateThis':
			uses.prototype = instr.prototype;
			uses.constructorRef = instr.constructorRef;
			break;

		case 'SelectObject':
			uses.thisObject = instr.thisObject;
			uses.constructorReturnValue = instr.constructorReturnValue;
			break;

		case 'GetArgumentsByPropVal':
			uses.argumentsIndex = instr.argumentsIndex;
		/* falls through */
		case 'GetArgumentsLength':
		case 'ReifyArguments':
			defs.lazyLoad = instr.lazyLoad;
			uses.lazyLoad = instr.lazyLoad;
			break;

		case 'SwitchImm':
			uses.discriminant = instr.discriminant;
			break;

		case 'ResumeGenerator':
			uses.isReturn = instr.isReturn;
			break;

		case 'IteratorNext':
			uses.iterator = instr.iterator;
			uses.sourceOrNext = instr.sourceOrNext;
			break;

		case 'IteratorClose':
			uses.iterator = instr.iterator;
			uses.ignoreException = instr.ignoreException;
			break;

		case 'Store8':
		case 'Store16':
		case 'Store32':
			uses.value = instr.value;
		/* falls through */
		case 'Loadi8':
		case 'Loadu8':
		case 'Loadi16':
		case 'Loadu16':
		case 'Loadi32':
		case 'Loadu32':
			uses.heap = instr.heap;
			uses.offset = instr.offset;
			break;
	}
	return { defs, uses };
}

/** Result types for the analyser */
export interface BlockLiveness {
	liveIn: Set<RegisterIndex>;   // set of register ids
	liveOut: Set<RegisterIndex>;
	uses: Set<RegisterIndex>;     // block-level uses (before any def in block)
	defs: Set<RegisterIndex>;     // block-level defs (first def of register in block)
}

export interface InstrLiveness {
	liveIn: Set<RegisterIndex>;
	liveOut: Set<RegisterIndex>;
	uses: Set<RegisterIndex>;
	defs: Set<RegisterIndex>;
}

export function livenessAnalysis<T extends {
	basicBlocks: Map<BlockAddr, {
		consequentAddresses: BlockAddr[];
		instructions: Instruction[];
	}>;
	exceptionHandlers: FunctionExceptionHandler[];
}>(
	func: T,
) {
	const blockUsesDefs = new Map<BlockAddr, { uses: Set<RegisterIndex>; defs: Set<RegisterIndex> }>();

	for (const [addr, block] of func.basicBlocks) {
		const uses = new Set<RegisterIndex>();
		const defs = new Set<RegisterIndex>(); // registers already defined earlier in the block

		for (const instr of block.instructions) {
			const { defs: dmap, uses: umap } = analyseUseDefines(instr);

			// process uses: if a used reg hasn't been defined in this block yet, it's a block use
			for (const reg of Object.values(umap)) {
				for (const { index } of Array.isArray(reg) ? reg : [reg]) {
					if (!defs.has(index)) {
						uses.add(index);
					}
				}
			}

			// process defs: any def becomes "defined" for the remainder of the block
			for (const { index } of Object.values(dmap)) {
				defs.add(index);
			}
		}

		blockUsesDefs.set(addr, { uses, defs });
	}

	// Initialize liveIn/liveOut maps
	const liveIn = new Map<BlockAddr, Set<RegisterIndex>>();
	const liveOut = new Map<BlockAddr, Set<RegisterIndex>>();

	for (const addr of func.basicBlocks.keys()) {
		liveIn.set(addr, new Set());
		liveOut.set(addr, new Set());
	}

	// Iterative fixpoint: in[B] = use[B] U (out[B] \ def[B])
	// out[B] = union_{s in succs[B]} in[s]
	let changed = true;
	while (changed) {
		changed = false;

		// iterate blocks in any order (reverse-postorder would converge faster, but not required)
		for (const [addr, block] of func.basicBlocks) {
			const oldIn = liveIn.get(addr)!;
			const oldOut = liveOut.get(addr)!;

			// compute newOut = union of in[succ]
			const newOut = new Set<RegisterIndex>();
			for (const succAddr of [...block.consequentAddresses, ...exceptionHandlersByAddress(addr, func.exceptionHandlers).map(({ catchOffset }) => catchOffset)]) {
				const succIn = liveIn.get(succAddr);
				if (succIn) {
					for (const r of succIn) newOut.add(r);
				}
				// if succ is missing from map, treat as empty (could warn)
			}

			// compute newIn = use[B] U (newOut \ def[B])
			const { uses: blockUses, defs: blockDefs } = blockUsesDefs.get(addr)!;
			const newIn = new Set<RegisterIndex>(blockUses); // start with uses

			for (const r of newOut) {
				if (!blockDefs.has(r)) newIn.add(r);
			}

			// check changed
			if (!setEquals(oldOut, newOut) || !setEquals(oldIn, newIn)) {
				changed = true;
				// replace maps
				liveOut.set(addr, newOut);
				liveIn.set(addr, newIn);
			}
		}
	}

	// Prepare block-level result structure
	const blockLiveness = new Map<BlockAddr, BlockLiveness>();
	for (const [addr] of func.basicBlocks) {
		const { uses, defs } = blockUsesDefs.get(addr)!;
		blockLiveness.set(addr, {
			uses: new Set(uses),
			defs: new Set(defs),
			liveIn: new Set(liveIn.get(addr)),
			liveOut: new Set(liveOut.get(addr)),
		});
	}

	// Optionally compute per-instruction liveness (backwards scan within each block)
	const instrLiveness = new Map<BlockAddr, InstrLiveness[]>();
	for (const [addr, block] of func.basicBlocks) {
		const n = block.instructions.length;
		const perInstr: InstrLiveness[] = new Array(n);

		// last instruction liveOut is block.liveOut
		let nextLive = new Set<RegisterIndex>(liveOut.get(addr) ?? []);

		// iterate instructions backwards
		for (let i = n - 1; i >= 0; --i) {
			const instr = block.instructions[i];
			const { defs: dmap, uses: umap } = analyseUseDefines(instr);

			const defs = new Set<RegisterIndex>(Object.values(dmap).map(({ index }) => index));
			const uses = new Set<RegisterIndex>(Object.values(umap).flatMap(r => r).map(({ index }) => index));

			// liveOut(instr) = nextLive
			const liveOutInstr = new Set<RegisterIndex>(nextLive);

			// liveIn(instr) = uses U (liveOut \ defs)
			const liveInInstr = new Set<RegisterIndex>(uses);
			for (const r of liveOutInstr) {
				if (!defs.has(r)) liveInInstr.add(r);
			}

			perInstr[i] = {
				uses,
				defs,
				liveIn: liveInInstr,
				liveOut: liveOutInstr,
			};

			// set nextLive for previous instruction: previous's liveOut = liveIn of this instruction
			nextLive = new Set<RegisterIndex>(liveInInstr);
		}

		instrLiveness.set(addr, perInstr);
	}

	return {
		blockLiveness,
		instrLiveness,
	};
}
