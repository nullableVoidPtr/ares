import { strict as assert } from 'node:assert';
import { blockConstantNumber } from './recognition.ts';
import type { RawInstructionLike } from './types.ts';

Deno.test('block constant lookup respects the last local register definition', () => {
	const constants = new Map<number, unknown>([[2, 0]]);
	const instructions = [
		{
			instruction: 'LoadConst',
			destination: { index: 2 },
			value: 1,
		},
		{
			instruction: 'LoadFromEnvironment',
			destination: { index: 2 },
		},
	] as RawInstructionLike[];

	assert.equal(blockConstantNumber(constants, { instructions }, 2), null);
});

Deno.test('block constant lookup uses the last local constant definition', () => {
	const constants = new Map<number, unknown>([[2, 0]]);
	const instructions = [
		{
			instruction: 'LoadFromEnvironment',
			destination: { index: 2 },
		},
		{
			instruction: 'LoadConst',
			destination: { index: 2 },
			value: 2,
		},
	] as RawInstructionLike[];

	assert.equal(blockConstantNumber(constants, { instructions }, 2), 2);
});
