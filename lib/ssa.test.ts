import { strict as assert } from 'node:assert';
import {
	BasicBlock,
	Function,
	FunctionKind,
} from './hbc/disassembly/function.ts';
import {
	asRegister,
	Instruction,
	InstructionLength,
	InstructionStrictness,
	InstructionType,
} from './hbc/disassembly/instruction.ts';
import { SSAFunction } from './ssa.ts';
import DominanceGraph from './utils/DominanceGraph.ts';

function call(offset: number, destination: number): Instruction {
	return {
		instruction: 'Call',
		functionLocalOffset: offset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
		destination: asRegister(destination),
		closure: asRegister(0),
		arguments: [],
	};
}

function ret(offset: number, argument: number): Instruction {
	return {
		instruction: 'Ret',
		functionLocalOffset: offset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
		argument: asRegister(argument),
	};
}

function block(
	address: number,
	instructions: Instruction[],
	consequentAddresses: number[],
): BasicBlock {
	return {
		address,
		instructions,
		consequentAddresses,
		predicate: null,
	};
}

Deno.test('protected blocks support multiple SSA consistency splits', () => {
	const func: Function = {
		id: 1,
		offset: 0,
		name: 'multipleProtectedSplits',
		paramCount: 1,
		frameSize: 3,
		envSize: 0,
		loopDepth: 0,
		numberRegCount: 0,
		nonPtrRegCount: 0,
		highestReadCacheIndex: 0,
		highestWriteCacheIndex: 0,
		readCacheSize: 0,
		writeCacheSize: 0,
		privateNameCacheSize: 0,
		strict: false,
		prohibitInvoke: 2,
		functionKind: FunctionKind.NormalFunction,
		exceptionHandlers: [{ tryStart: 0, tryEnd: 5, catchOffset: 100 }],
		basicBlocks: new Map([
			[
				0,
				block(
					0,
					[
						call(0, 1),
						call(1, 2),
						call(2, 1),
						call(3, 2),
						call(4, 1),
					],
					[10],
				),
			],
			[10, block(10, [ret(10, 1)], [])],
			[100, block(100, [ret(100, 1)], [])],
		]),
		trampolines: new Map(),
	};

	const ssa = new SSAFunction(func);

	assert.deepEqual([...func.basicBlocks.keys()], [0, 10, 100, 3, 1]);
	assert.deepEqual(func.basicBlocks.get(0)?.consequentAddresses, [1]);
	assert.deepEqual(func.basicBlocks.get(1)?.consequentAddresses, [3]);
	assert.deepEqual(func.basicBlocks.get(3)?.consequentAddresses, [10]);
	assert.deepEqual(
		func.basicBlocks.get(0)?.instructions.map((instruction) =>
			instruction.functionLocalOffset
		),
		[0],
	);
	assert.deepEqual(
		func.basicBlocks.get(1)?.instructions.map((instruction) =>
			instruction.functionLocalOffset
		),
		[1, 2],
	);
	assert.deepEqual(
		func.basicBlocks.get(3)?.instructions.map((instruction) =>
			instruction.functionLocalOffset
		),
		[3, 4],
	);
	const catchPhi = ssa.basicBlocks.get(100)?.ssaInstructions.find((instr) =>
		instr.instruction === 'Phi' && instr.destination.index === 1
	);
	assert.equal(catchPhi?.instruction, 'Phi');
	if (catchPhi?.instruction === 'Phi') {
		assert.deepEqual(
			[...catchPhi.sources].map(([address, source]) => [
				address,
				source.version,
			]),
			[
				[0, 0],
				[1, 1],
				// The catch Phi itself consumes version 2 in the global version
				// counter, so the successful write in block 1 becomes version 3.
				[3, 3],
			],
		);
	}
});

Deno.test('unreachable predecessors do not break reachable dominance', () => {
	const graph = new DominanceGraph({
		basicBlocks: new Map([
			[0, { consequentAddresses: [1, 2] }],
			[1, { consequentAddresses: [3] }],
			[2, { consequentAddresses: [3] }],
			[3, { consequentAddresses: [] }],
			// A bytecode-only catch block can name a reachable loop header without
			// itself being reachable from the function entry.
			[4, { consequentAddresses: [3] }],
		]),
		exceptionHandlers: [],
	}, 0);

	assert.equal(graph.dominatorsOf(3).has(0), true);
	assert.equal(graph.dominatorsOf(3).has(4), false);
	assert.equal(graph.immediatelyDominatedBy(0).has(3), true);
});
