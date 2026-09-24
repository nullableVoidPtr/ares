import assert from 'node:assert/strict';
import { DataReader } from './DataReader.ts';

Deno.test('DataReader respects an ArrayBufferView range', () => {
	const backing = new Uint8Array([0xaa, 0xbb, 1, 2, 3, 4, 0xcc]);
	const reader = new DataReader(backing.subarray(2, 6));

	assert.equal(reader.UInt8(), 1);
	assert.equal(reader.UInt16(), 0x0302);
	assert.equal(reader.UInt8(), 4);
	assert.equal(reader.remaining, false);
});
