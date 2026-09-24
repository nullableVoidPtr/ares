import { strict as assert } from 'node:assert';
import { HBCFile } from './file.ts';

/** A file carrying nothing but a bigint table, for the decoder. */
function fileWithBigInts(entries: number[][]): HBCFile {
	return HBCFile.fromParts({
		data: new Uint8Array(0),
		version: 96,
		stringTable: [],
		arrayBuffer: new Uint8Array(0),
		literalValueBuffer: new Uint8Array(0),
		objectKeyBuffer: new Uint8Array(0),
		objectValueBuffer: new Uint8Array(0),
		objectShapes: [],
		bigintTable: entries.map((bytes) => Uint8Array.from(bytes)),
		functions: [],
	});
}

Deno.test('bigint digits decode little-endian', () => {
	const file = fileWithBigInts([
		[0x20],
		[0x00, 0x01],
		[0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
		[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x1f, 0x00],
	]);
	assert.equal(file.getBigInt(0), 32n);
	assert.equal(file.getBigInt(1), 256n);
	assert.equal(file.getBigInt(2), 32n);
	assert.equal(file.getBigInt(3), 9007199254740991n);
});

Deno.test('a set top bit decodes as a negative value', () => {
	const file = fileWithBigInts([
		[0xff],
		[0x80],
		[0x00, 0x80],
		[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
	]);
	assert.equal(file.getBigInt(0), -1n);
	assert.equal(file.getBigInt(1), -128n);
	assert.equal(file.getBigInt(2), -32768n);
	assert.equal(file.getBigInt(3), -1n);
});

Deno.test('an absent or empty bigint decodes as zero', () => {
	const file = fileWithBigInts([[]]);
	assert.equal(file.getBigInt(0), 0n);
	assert.equal(file.getBigInt(7), 0n);
});
