import assert from 'node:assert/strict';
import { applyArrayDelta } from './arrayDelta.ts';
import { getVersionInfo } from './VersionInfo.ts';

Deno.test('applyArrayDelta does not mutate its base or replacement', () => {
	const base = ['b', 'c'];
	const replacement = ['x', 'y'];

	assert.deepEqual(
		applyArrayDelta(base, {
			exclude: ['c'],
			prepend: ['a'],
			append: ['d'],
			insertAfter: [['b', ['b2']]],
		}),
		['a', 'b', 'b2', 'd'],
	);
	assert.deepEqual(base, ['b', 'c']);
	assert.deepEqual(applyArrayDelta(base, replacement), replacement);
	assert.notStrictEqual(applyArrayDelta(base, replacement), replacement);
	assert.deepEqual(replacement, ['x', 'y']);
});

Deno.test('version resolution is stable across call order', () => {
	const firstV95 = getVersionInfo(95);
	const v99 = getVersionInfo(99);
	const secondV95 = getVersionInfo(95);

	assert.deepEqual(secondV95.opcodeMap, firstV95.opcodeMap);
	assert.deepEqual(secondV95.builtins, firstV95.builtins);
	assert.notStrictEqual(secondV95.opcodeMap, firstV95.opcodeMap);
	assert.notDeepEqual(firstV95.opcodeMap, v99.opcodeMap);
});
