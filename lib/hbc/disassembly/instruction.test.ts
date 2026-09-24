import { strict as assert } from 'node:assert';
import {
	asRegister,
	asStringRef,
	createInstruction,
	InstructionLength,
	InstructionStrictness,
} from './instruction.ts';
import { structureInstructions } from './mod.ts';

Deno.test('DelById encoding variants normalize to DelById', () => {
	const variants = [
		['DelById', InstructionLength.NORMAL, InstructionStrictness.NORMAL],
		['DelByIdLong', InstructionLength.LONG, InstructionStrictness.NORMAL],
		['DelByIdLoose', InstructionLength.NORMAL, InstructionStrictness.LOOSE],
		[
			'DelByIdStrict',
			InstructionLength.NORMAL,
			InstructionStrictness.STRICT,
		],
		[
			'DelByIdLooseLong',
			InstructionLength.LONG,
			InstructionStrictness.LOOSE,
		],
		[
			'DelByIdStrictLong',
			InstructionLength.LONG,
			InstructionStrictness.STRICT,
		],
	] as const;

	for (const [mnemonic, length, strict] of variants) {
		const instruction = createInstruction(
			mnemonic,
			[asRegister(0), asRegister(1), asStringRef(123_456)],
			7,
		);

		assert.equal(instruction.instruction, 'DelById');
		assert.equal(instruction.length, length);
		assert.equal(instruction.strict, strict);
		assert.deepEqual(instruction, {
			functionLocalOffset: 7,
			instruction: 'DelById',
			length,
			type: 0,
			strict,
			destination: asRegister(0),
			object: asRegister(1),
			property: asStringRef(123_456),
		});
	}
});

Deno.test('relational JNot branches normalize by swapping successors', () => {
	const { basicBlocks } = structureInstructions([
		createInstruction('JNotLess', [20, asRegister(0), asRegister(1)], 0),
		createInstruction('Ret', [asRegister(2)], 4),
		createInstruction('Ret', [asRegister(3)], 20),
	]);

	const block = basicBlocks.get(0);
	assert.deepEqual(block?.consequentAddresses, [20, 4]);
	assert.deepEqual(block?.predicate, {
		not: false,
		left: asRegister(0),
		operation: '<',
		right: asRegister(1),
	});
});

Deno.test('equality JNot branches keep predicate negation', () => {
	const { basicBlocks } = structureInstructions([
		createInstruction('JNotEqual', [20, asRegister(0), asRegister(1)], 0),
		createInstruction('Ret', [asRegister(2)], 4),
		createInstruction('Ret', [asRegister(3)], 20),
	]);

	const block = basicBlocks.get(0);
	assert.deepEqual(block?.consequentAddresses, [4, 20]);
	assert.deepEqual(block?.predicate, {
		not: true,
		left: asRegister(0),
		operation: '==',
		right: asRegister(1),
	});
});
