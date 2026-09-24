import assert from 'node:assert/strict';
import { HBCFile } from './file.ts';

Deno.test('serialized literals respect a buffer view range', () => {
	const file = Object.create(HBCFile.prototype) as HBCFile;
	file.version = 99;
	const backing = new Uint8Array([0xff, 0xff, 0x02]);

	assert.deepEqual(
		file.readSerializedLiterals(backing.subarray(2), 0, 2),
		[null, null],
	);
});
