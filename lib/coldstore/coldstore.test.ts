import { strict as assert } from 'node:assert';
import * as t from '@babel/types';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { HBCFile } from '../parser/file.ts';
import { SSAFunction } from '../ssa.ts';
import { HermesEmpty } from '../hbc/disassembly/instruction.ts';
import { IRFunction } from '../ir/function/mod.ts';
import { type ColdStore, hashOptions, openColdStore } from './mod.ts';
import { readColdFile, writeColdFile } from './file.ts';
import {
	buildBytecodeDerivedPlan,
	readColdPlan,
	writeColdPlan,
} from './plan.ts';
import { putColdSnapshot, readColdSnapshot } from './snapshot.ts';
import { decodeFromStore, encodeForStore } from './codec.ts';

const SAMPLES = new URL('../../samples/', import.meta.url).pathname;

async function withStore<T>(fn: (store: ColdStore) => Promise<T>): Promise<T> {
	const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'ares-coldstore-'));
	const store = await openColdStore(dir);
	try {
		return await fn(store);
	} finally {
		await store.close();
		fs.rmSync(dir, { recursive: true, force: true });
	}
}

/**
 * Structural equality including property order.
 *
 * Deliberately stricter than `assertEquals`: the whole point of the store is
 * that a decoded record is indistinguishable from the original, and object key
 * order is observable through `Object.keys` in the passes that consume these.
 */
function assertSameShape(actual: unknown, expected: unknown, at = '$'): void {
	if (Object.is(actual, expected)) return;
	assert.equal(
		typeof actual,
		typeof expected,
		`${at}: type ${typeof actual} vs ${typeof expected}`,
	);
	if (actual === null || expected === null || typeof actual !== 'object') {
		assert.equal(actual, expected, `${at}: ${actual} vs ${expected}`);
		return;
	}
	assert.equal(
		Array.isArray(actual),
		Array.isArray(expected as object),
		`${at}: array-ness differs`,
	);
	if (Array.isArray(actual)) {
		const other = expected as unknown[];
		assert.equal(actual.length, other.length, `${at}: length differs`);
		for (let i = 0; i < actual.length; i++) {
			assertSameShape(actual[i], other[i], `${at}[${i}]`);
		}
		return;
	}
	const actualKeys = Object.keys(actual as object);
	const expectedKeys = Object.keys(expected as object);
	assert.deepEqual(actualKeys, expectedKeys, `${at}: keys differ`);
	for (const key of actualKeys) {
		assertSameShape(
			(actual as Record<string, unknown>)[key],
			(expected as Record<string, unknown>)[key],
			`${at}.${key}`,
		);
	}
}

function sampleFile(name: string): HBCFile {
	return HBCFile.fromBytes(fs.readFileSync(path.join(SAMPLES, name)));
}

Deno.test('snapshots survive the store unchanged, including key order', async () => {
	const file = sampleFile('v96/generator.hbc');
	await withStore(async (store) => {
		const originals = new Map<number, ReturnType<IRFunction['snapshot']>>();
		await store.root.transaction(() => {
			for (let id = 0; id < file.functions.length; id++) {
				const func = new IRFunction(
					file,
					new SSAFunction(file.functions[id]),
					{ cfgReducer: { mode: 'recursive' } },
				);
				const snapshot = func.snapshot();
				originals.set(id, snapshot);
				putColdSnapshot(store, id, snapshot);
			}
		});

		assert.ok(originals.size > 0, 'sample produced no functions');
		for (const [id, original] of originals) {
			const restored = readColdSnapshot(store, id);
			assert.ok(restored, `function #${id} missing from the store`);
			// Field by field, because the head/body split necessarily moves
			// `blocks` to the end of the reassembled container. That top-level
			// order is not observable -- `fromSnapshot` reads named fields and
			// nothing enumerates the snapshot itself -- whereas the key order
			// *inside* it is, since those are Babel nodes that passes walk with
			// `Object.keys`. So the outer order is exempt and everything below
			// it is not.
			assert.deepEqual(
				Object.keys(restored).toSorted(),
				Object.keys(original).toSorted(),
				`#${id}: fields differ`,
			);
			for (const key of Object.keys(original)) {
				assertSameShape(
					(restored as unknown as Record<string, unknown>)[key],
					(original as unknown as Record<string, unknown>)[key],
					`#${id}.${key}`,
				);
			}
		}
	});
});

Deno.test('the HermesEmpty sentinel survives both records', async () => {
	// v99 class samples are the only fixtures that emit `LoadConstEmpty`, and
	// the sentinel is a Symbol, which the encoder refuses outright.
	const file = sampleFile('v99/class.hbc');
	const loadsEmpty = file.functions.some((func) =>
		[...func.basicBlocks.values()].some((block) =>
			block.instructions.some((instruction) =>
				(instruction as { value?: unknown }).value === HermesEmpty
			)
		)
	);
	assert.ok(loadsEmpty, 'fixture no longer contains LoadConstEmpty');

	await withStore(async (store) => {
		await writeColdFile(store, file);
		const { file: cold } = readColdFile(store);
		for (let id = 0; id < file.functions.length; id++) {
			assertSameShape(
				[...cold.functions[id].basicBlocks],
				[...file.functions[id].basicBlocks],
				`#${id}.basicBlocks`,
			);
		}
	});
});

Deno.test('a paged file answers exactly like the parsed one', async () => {
	const file = sampleFile('v96/tryCatch.test.hbc');
	await withStore(async (store) => {
		await writeColdFile(store, file);
		// Deliberately smaller than the function count, so eviction and
		// re-decoding are on the tested path rather than only first reads.
		const { file: cold, stats } = readColdFile(store, { cacheLimit: 2 });

		assert.equal(cold.functions.length, file.functions.length);
		assert.equal(cold.version, file.version);
		assert.equal(cold.stringTable.length, file.stringTable.length);
		for (let id = 0; id < file.stringTable.length; id++) {
			assert.equal(cold.getString(id), file.getString(id));
		}
		for (let id = 0; id < file.functions.length; id++) {
			assertSameShape(
				[...cold.functions[id].basicBlocks],
				[...file.functions[id].basicBlocks],
				`#${id}.basicBlocks`,
			);
		}
		assert.ok(stats.pageIns > 0, 'nothing was paged in');
	});
});

Deno.test('the bytecode plan survives the store', async () => {
	const file = sampleFile('v96/class.hbc');
	const plan = buildBytecodeDerivedPlan(file);
	await withStore(async (store) => {
		await writeColdPlan(store, plan);
		const restored = readColdPlan(store);
		assert.deepEqual(
			[...restored.soleFunctionParents],
			[...plan.soleFunctionParents],
		);
		assert.deepEqual(
			[...restored.nonSoleFunctionReferences],
			[...plan.nonSoleFunctionReferences],
		);
		assert.deepEqual(
			[...restored.closureReferences],
			[...plan.closureReferences],
		);
		assert.deepEqual(
			[...restored.environmentCreators],
			[...plan.environmentCreators],
		);
		// Insertion order matters: the global-name set is iterated to build
		// the shared-globals list a composition unit is handed.
		assert.deepEqual(
			[...restored.bytecodeGlobalNames],
			[...plan.bytecodeGlobalNames],
		);
		assert.deepEqual(
			restored.functionBytecodeLengths,
			plan.functionBytecodeLengths,
		);
		assert.equal(restored.functionCount, plan.functionCount);
	});
});

Deno.test('awkward values survive the encoder', async () => {
	await withStore(async (store) => {
		const cases: [string, unknown][] = [
			['undefined in an array', [1, undefined, null, false]],
			['undefined-valued property', { a: undefined, b: 1 }],
			['NaN', { value: NaN }],
			['max safe integer', { value: Number.MAX_SAFE_INTEGER }],
			['empty containers', { a: {}, b: [] }],
			['string ref', { type: 'string', stringTableIndex: 7 }],
		];
		for (const [name, value] of cases) {
			await store.plan.put(name, value);
			assertSameShape(store.plan.get(name), value, name);
		}

		// msgpackr silently encodes -0 as the integer 0, which is not
		// unobservable: React's profiler initialises `actualDuration = -0` and
		// Babel prints that literal as `-0`, so losing it changed 452 lines of
		// composed TestApp output. The codec carries it explicitly.
		const negativeZero = encodeForStore({ value: -0 });
		assert.equal(negativeZero.tagged, true);
		assert.equal(
			Object.is(decodeFromStore(negativeZero.value).value, -0),
			true,
		);
	});
});

Deno.test('negative zero survives a snapshot round trip', async () => {
	const file = sampleFile('v96/tryCatch.test.hbc');
	await withStore(async (store) => {
		const func = new IRFunction(
			file,
			new SSAFunction(file.functions[0]),
			{ cfgReducer: { mode: 'recursive' } },
		);
		const snapshot = func.snapshot();
		// Planted rather than found: no sample happens to lift a -0, and the
		// bundle that does is 69MB. What matters is that a -0 buried in a block
		// body comes back as -0 and not as 0.
		const [, block] = snapshot.blocks[0];
		// Built by hand: Babel's `numericLiteral` builder validates the value
		// as non-negative and rejects -0, so the literal is assembled the way
		// the lifter ends up with one rather than through the builder.
		const planted = {
			type: 'NumericLiteral',
			value: -0,
		} as t.NumericLiteral;
		block.body.unshift(
			t.expressionStatement(planted) as typeof block.body[0],
		);

		await store.root.transaction(() => {
			putColdSnapshot(store, 0, snapshot);
		});
		const restored = readColdSnapshot(store, 0);
		const statement = restored!.blocks[0][1]
			.body[0] as t.ExpressionStatement;
		const literal = statement.expression as t.NumericLiteral;
		assert.equal(Object.is(literal.value, -0), true);
	});
});

Deno.test('the codec refuses symbols it has no stored form for', () => {
	assert.throws(
		() => encodeForStore({ value: Symbol('not hermes empty') }),
		/only HermesEmpty has a stored form/,
	);
});

Deno.test('option hashing ignores property order but not values', () => {
	assert.equal(
		hashOptions({ a: 1, b: { c: 2, d: 3 } }),
		hashOptions({ b: { d: 3, c: 2 }, a: 1 }),
	);
	assert.notEqual(
		hashOptions({ cfgReducer: { mode: 'recursive' } }),
		hashOptions({ cfgReducer: { materialize: false } }),
	);
});
