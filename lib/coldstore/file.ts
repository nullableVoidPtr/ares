/**
 * Spilling the parsed bundle, so a worker never rebuilds it.
 *
 * `new HBCFile(bytes)` disassembles every function up front. On a 127k-function
 * bundle that is 2,583MB of resident set and six seconds, and `--parallel-lift`
 * used to pay it once per worker. Everything it produces is a pure function of
 * the bytes, so it is computed once, written here, and paged back in per
 * function.
 *
 * The split is between what is small enough to hold and what is not. The string
 * table, the literal buffers and the object shapes are tens of megabytes and are
 * read by index from all over the lifter, so they are stored as single records
 * and held whole. The functions are the 2.5GB, so they are stored one per key
 * and paged through a bounded cache.
 */
import { type Function as HBCFunction } from '../hbc/disassembly/function.ts';
import {
	HBCFile,
	type HBCFileParts,
	type ObjectShapeEntry,
	type StringTableEntry,
} from '../parser/file.ts';
import { type ColdStore, DecodedCache } from './mod.ts';
import { encodeForStore, type TaggedRecord, unwrapStored } from './codec.ts';

/** The one non-function record: everything held whole. */
interface ColdFileHeader {
	version: number;
	functionCount: number;
	stringTable: StringTableEntry[];
	arrayBuffer: Uint8Array;
	literalValueBuffer: Uint8Array;
	objectKeyBuffer: Uint8Array;
	objectValueBuffer: Uint8Array;
	objectShapes: ObjectShapeEntry[];
	bigintTable: Uint8Array[];
}

const HEADER_KEY = 'file:header';

/**
 * `Map`s do not survive the encoder in a shape worth relying on, and the two on
 * a `Function` are the hot ones, so they cross as entry arrays -- the same
 * convention `IRFunctionSnapshot` already uses for its address maps.
 */
interface ColdFunctionRecord extends
	Omit<
		HBCFunction,
		'basicBlocks' | 'trampolines'
	> {
	basicBlocks: [
		number,
		HBCFunction['basicBlocks'] extends Map<number, infer V> ? V : never,
	][];
	trampolines: [number, number][];
}

function encodeFunction(func: HBCFunction): TaggedRecord<ColdFunctionRecord> {
	return encodeForStore<ColdFunctionRecord>({
		...func,
		basicBlocks: [...func.basicBlocks],
		trampolines: [...func.trampolines],
	});
}

function decodeFunction(stored: TaggedRecord<ColdFunctionRecord>): HBCFunction {
	const record = unwrapStored(stored)!;
	return {
		...record,
		basicBlocks: new Map(record.basicBlocks),
		trampolines: new Map(record.trampolines),
	} as HBCFunction;
}

/**
 * Write a parsed file into the store.
 *
 * Batched into transactions rather than awaited per function: the writer is a
 * single background thread and a commit per record would serialise the whole
 * phase on it.
 */
export async function writeColdFile(
	store: ColdStore,
	file: HBCFile,
	onProgress?: (written: number, total: number) => void,
	batchSize = 512,
): Promise<void> {
	const header: ColdFileHeader = {
		version: file.version,
		functionCount: file.functions.length,
		// Materialised, not passed through. A freshly parsed file's entries are
		// wasm-bindgen handles whose fields live behind prototype getters, so an
		// encoder walking own properties would faithfully store a pointer into a
		// WASM heap that no longer exists by the time anything reads it.
		stringTable: file.stringTable.map((entry) => ({
			kind: entry.kind,
			value: entry.value,
		})),
		arrayBuffer: file.arrayBuffer,
		literalValueBuffer: file.literalValueBuffer,
		objectKeyBuffer: file.objectKeyBuffer,
		objectValueBuffer: file.objectValueBuffer,
		objectShapes: file.objectShapes.map((shape) => ({
			keyBufferOffset: shape.keyBufferOffset,
			numProps: shape.numProps,
		})),
		bigintTable: file.bigintTable,
	};
	await store.plan.put(HEADER_KEY, header);

	const total = file.functions.length;
	for (let start = 0; start < total; start += batchSize) {
		const end = Math.min(start + batchSize, total);
		await store.root.transaction(() => {
			for (let id = start; id < end; id++) {
				store.fn.put(id, encodeFunction(file.functions[id]));
			}
		});
		onProgress?.(end, total);
	}
}

/** Counts how many functions a cold file has had to decode, for verification. */
export interface ColdFileStats {
	/** Distinct decodes, including ones later evicted and decoded again. */
	pageIns: number;
	/** Reads served from the decoded cache. */
	hits: number;
}

export interface ColdFileOptions {
	/**
	 * How many decoded functions to keep. Each is a few hundred kilobytes of JS
	 * objects, and lifting touches one at a time, so this is small on purpose:
	 * the point of the store is that the OS holds the encoded pages instead.
	 */
	cacheLimit?: number;
	/**
	 * Only needed by code paths that still ship raw bytes elsewhere. Left empty
	 * by default so a worker does not hold a copy of the bundle it never reads.
	 */
	data?: Uint8Array;
}

/**
 * Build a file whose `functions` are paged from the store.
 *
 * The array is a `Proxy` rather than a class with a `get` method because
 * `HBCFile.functions` is a plain array everywhere it is used -- indexed,
 * `.length`-ed, and in four places iterated. The proxy keeps every one of those
 * working; the iterating callers are the ones that have to be routed through
 * `lib/coldstore/plan.ts` instead, or they page in the whole bundle and the
 * store buys nothing.
 */
export function readColdFile(
	store: ColdStore,
	options: ColdFileOptions = {},
): { file: HBCFile; stats: ColdFileStats } {
	const header = store.plan.get(HEADER_KEY) as ColdFileHeader | undefined;
	if (!header) {
		throw new Error(
			`Cold store at ${store.path} has no file header; ` +
				'the file phase did not complete',
		);
	}

	const stats: ColdFileStats = { pageIns: 0, hits: 0 };
	const cache = new DecodedCache<number, HBCFunction>(
		options.cacheLimit ?? 64,
	);

	const load = (id: number): HBCFunction | undefined => {
		const cached = cache.get(id);
		if (cached) {
			stats.hits++;
			return cached;
		}
		const record = store.fn.get(id) as
			| TaggedRecord<ColdFunctionRecord>
			| undefined;
		if (!record) return undefined;
		stats.pageIns++;
		const decoded = decodeFunction(record);
		cache.set(id, decoded);
		return decoded;
	};

	const target = new Array<HBCFunction>(header.functionCount);
	const functions = new Proxy(target, {
		get(inner, property, receiver) {
			if (property === 'length') return header.functionCount;
			if (typeof property === 'string') {
				const index = Number(property);
				if (Number.isInteger(index) && index >= 0) {
					return load(index);
				}
			}
			return Reflect.get(inner, property, receiver);
		},
		has(inner, property) {
			if (typeof property === 'string') {
				const index = Number(property);
				if (Number.isInteger(index) && index >= 0) {
					return index < header.functionCount;
				}
			}
			return Reflect.has(inner, property);
		},
		getOwnPropertyDescriptor(inner, property) {
			if (typeof property === 'string') {
				const index = Number(property);
				if (
					Number.isInteger(index) && index >= 0 &&
					index < header.functionCount
				) {
					// Reported as configurable because the value is synthesised
					// per read; a non-configurable descriptor over a hole is an
					// invariant violation the proxy would throw on.
					return {
						configurable: true,
						enumerable: true,
						writable: true,
						value: load(index),
					};
				}
			}
			return Reflect.getOwnPropertyDescriptor(inner, property);
		},
	});

	const parts: HBCFileParts = {
		data: options.data ?? new Uint8Array(0),
		version: header.version,
		stringTable: header.stringTable,
		arrayBuffer: header.arrayBuffer,
		literalValueBuffer: header.literalValueBuffer,
		objectKeyBuffer: header.objectKeyBuffer,
		objectValueBuffer: header.objectValueBuffer,
		objectShapes: header.objectShapes,
		bigintTable: header.bigintTable,
		functions,
	};
	return { file: HBCFile.fromParts(parts), stats };
}
