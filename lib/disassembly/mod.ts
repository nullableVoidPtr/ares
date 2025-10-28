import { BasicBlock, BlockAddr, FunctionExceptionHandler } from "./function.ts";
import { Instruction } from "./instruction.ts";

export function structureInstructions(code: Instruction[], exceptionHandlers?: FunctionExceptionHandler[]): {
	basicBlocks: Map<BlockAddr, BasicBlock>;
	trampolines: Map<BlockAddr, BlockAddr>;
} {
	exceptionHandlers ??= [];

	const basicBlocks = new Map<number, BasicBlock>();
	const starts: number[] = [code[0].functionLocalOffset];
	const indexMap = new Map<number, number>();
	for (let i = 0; i < code.length; i++) {
		const instruction = code[i];
		const offset = instruction.functionLocalOffset;

		indexMap.set(instruction.functionLocalOffset, i);

		switch (instruction.instruction) {
			case 'ResumeGenerator':
			case 'Catch':
				starts.push(offset);
				break;

			case 'JmpTrue':
			case 'JmpFalse':
			case 'JmpUndefined':
			case 'JLess':
			case 'JNotLess':
			case 'JLessEqual':
			case 'JNotLessEqual':
			case 'JGreater':
			case 'JNotGreater':
			case 'JGreaterEqual':
			case 'JNotGreaterEqual':
			case 'JEqual':
			case 'JNotEqual':
			case 'JStrictEqual':
			case 'JStrictNotEqual':
				starts.push(code[i + 1].functionLocalOffset);
				/* falls through */
			case 'Jmp':
			case 'SaveGenerator':
				starts.push(offset + instruction.relativeTarget);
				break;
			
			// case 'TryGetById':
			// case 'TryPutById':
			case 'ThrowIfEmpty':
			case 'ThrowIfUndefined':
				starts.push(code[i + 1].functionLocalOffset);
				break;
		}
	}

	for (const { tryStart, tryEnd, catchOffset} of exceptionHandlers) {
		if (!starts.includes(tryStart)) {
			starts.push(tryStart);
		}
		if (!starts.includes(tryEnd)) {
			starts.push(tryEnd);
		}
		if (!starts.includes(catchOffset)) {
			starts.push(catchOffset);
		}
	}

	const unvisited = new Set(code.map(({functionLocalOffset}) => functionLocalOffset));
	for (const start of starts) {
		const block: BasicBlock = {
			address: start,
			instructions: [],

			predicate: null,
			consequentAddresses: [],
		};

		let generatorContinuation: number | undefined = undefined;
		basicBlockLoop: for (let i = indexMap.get(start)!; i < code.length; i++) {
			const instruction = code[i];
			if (instruction.functionLocalOffset !== start && starts.includes(instruction.functionLocalOffset)) {
				if (block.consequentAddresses.length > 0) {
					throw new Error();
				}
				block.consequentAddresses = [
					instruction.functionLocalOffset,
				];
				break;
			}

			block.instructions.push(instruction);
			unvisited.delete(instruction.functionLocalOffset);

			if (instruction.instruction == 'SaveGenerator') {
				if (typeof generatorContinuation != 'undefined') throw new Error('expected only one SaveGenerator in a basic block');
				generatorContinuation = instruction.functionLocalOffset + instruction.relativeTarget;
			}

			switch (instruction.instruction) {
				case 'Ret':
					if (typeof generatorContinuation == 'number') {
						block.consequentAddresses = [
							generatorContinuation,
						];
					}
					/* falls through */
				case 'Throw':
					break basicBlockLoop;
				case 'Jmp':
					block.consequentAddresses = [
						instruction.functionLocalOffset + instruction.relativeTarget,
					];
					break basicBlockLoop;
				case 'JmpTrue':
				case 'JmpFalse':
					block.consequentAddresses = [
						code[i+1].functionLocalOffset,
						instruction.functionLocalOffset + instruction.relativeTarget
					];
					block.predicate = {
						not: instruction.instruction == 'JmpFalse',
						predicate: instruction.predicate,
					}
					break basicBlockLoop;
				case 'JmpUndefined':
					block.consequentAddresses = [
						code[i+1].functionLocalOffset,
						instruction.functionLocalOffset + instruction.relativeTarget
					];
					block.predicate = {
						not: false,
						left: instruction.predicate,
						operation: '==',
						right: undefined,
					}
					break basicBlockLoop;
				case 'JLess':
				case 'JNotLess':
				case 'JLessEqual':
				case 'JNotLessEqual':
				case 'JGreater':
				case 'JNotGreater':
				case 'JGreaterEqual':
				case 'JNotGreaterEqual':
				case 'JEqual':
				case 'JNotEqual':
				case 'JStrictEqual':
				case 'JStrictNotEqual':
					block.consequentAddresses = [
						code[i+1].functionLocalOffset,
						instruction.functionLocalOffset + instruction.relativeTarget
					];
					block.predicate = {
						not: {
							'JLess': false,
							'JNotLess': true,
							'JLessEqual': false,
							'JNotLessEqual': true,
							'JGreater': false,
							'JNotGreater': true,
							'JGreaterEqual': false,
							'JNotGreaterEqual': true,
							'JEqual': false,
							'JNotEqual': true,
							'JStrictEqual': false,
							'JStrictNotEqual': true,
						}[instruction.instruction],
						left: instruction.left,
						operation: ({
							'JLess': '<',
							'JNotLess': '<',
							'JLessEqual': '<=',
							'JNotLessEqual': '<=',
							'JGreater': '>',
							'JNotGreater': '>',
							'JGreaterEqual': '>=',
							'JNotGreaterEqual': '>=',
							'JEqual': '==',
							'JNotEqual': '==',
							'JStrictEqual': '===',
							'JStrictNotEqual': '===',
						} as const)[instruction.instruction],
						right: instruction.right,
					}
					break basicBlockLoop;
			}
		}

		basicBlocks.set(start, block);
	}

	if (unvisited.size > 0) {
		throw new Error();
	}

	const unconditionalJmps = new Map<BlockAddr, BlockAddr>();
	for (const [addr, block] of basicBlocks) {
		if (block.instructions.length > 1) continue;

		const jmp = block.instructions[0];
		if (jmp.instruction != 'Jmp') continue;

		const target = jmp.functionLocalOffset + jmp.relativeTarget;
		unconditionalJmps.set(addr, target);
	}

	const trampolines = new Map<BlockAddr, BlockAddr>();
	for (const [src, target] of unconditionalJmps) {
		let newTarget = unconditionalJmps.get(target);
		if (newTarget == null) {
			trampolines.set(src, target);
			continue;
		}

		const visited = new Set<BlockAddr>([target, newTarget]);
		while (unconditionalJmps.has(newTarget)) {
			newTarget = unconditionalJmps.get(newTarget)!;
			if (visited.has(newTarget)) throw new Error();
		}

		trampolines.set(src, newTarget);
	}

	for (const predecessor of basicBlocks.values()) {
		predecessor.consequentAddresses = predecessor.consequentAddresses.map((consequent) => {
			return trampolines.get(consequent) ?? consequent
		});
	}


	for (const addr of trampolines.keys()) {
		basicBlocks.delete(addr);
	}

	return {
		basicBlocks,
		trampolines,
	};
}