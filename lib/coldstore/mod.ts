/**
 * On-disk cold storage for the parallel pipeline, backed by LMDB.
 *
 * `--parallel-lift` used to hand every worker a copy of the bundle bytes and let
 * each one rebuild the whole `HBCFile`, which on a 127k-function bundle is
 * 2.5GB of resident set per worker before a single function has been lifted.
 * Everything replicated that way -- the per-function disassembly, the whole-file
 * plans derived from it, and the lifted IR snapshots -- is a deterministic
 * function of the bundle bytes, written once and read many times.
 *
 * LMDB is the right shape for that: readers are lock-free and zero-copy out of a
 * shared mmap, so the OS page cache becomes one reclaimable cache shared by every
 * thread instead of N private V8 heaps the collector will never hand back. It is
 * also durable, so a second run over the same bundle can skip lifting entirely.
 *
 * Deliberately *not* named `spill`: `spillMetroModuleFactories` already means
 * something unrelated in `lib/ir/lift.ts` (rendering module factories out to
 * fragment source), and overloading the word in two directions would be worse
 * than a slightly longer name.
 */
// Type-only, deliberately: a value import would load the native addon as soon
// as anything in `lib/ir/lift.ts` is imported, which would make every serial
// run demand `--allow-ffi` for a store it never opens. The real module is
// pulled in by `openColdStore`, the only place that needs it.
import type { Database, RootDatabase } from 'lmdb';

/**
 * Bumped whenever an encoded record's shape changes.
 *
 * A store whose schema does not match is rebuilt rather than migrated: the
 * contents are a cache of work that can always be redone, so migration code
 * would be pure liability.
 */
// 5: snapshot records carry their own structures instead of a shared table.
// 6: generated-register placement runs before binding-based IR cleanup.
// 7: corrected parameter defaults and transactional natural-loop snapshots.
// 8: partial recursive loops use whole-function safety rollback.
export const COLDSTORE_SCHEMA_VERSION = 8;

/** Identifies the inputs a store's contents were derived from. */
export interface ColdStoreFingerprint {
	schema: number;
	/** SHA-256 of the bundle bytes, hex. */
	bundleHash: string;
	bundleLength: number;
	hermesVersion: number;
	/** Everything about the run that changes what lifting produces. */
	optionsHash: string;
}

/** Which phases have completed, so a resumed run knows what it can trust. */
export type ColdStorePhase = 'fn' | 'plan' | 'snap';

export interface ColdStoreOptions {
	readOnly?: boolean;
	/**
	 * Virtual, and the file is sparse, so this costs nothing until written.
	 * It must be large enough for the whole run: growing it means reopening.
	 */
	mapSize?: number;
	compression?: boolean;
}

const DEFAULT_MAP_SIZE = 64 * 1024 ** 3;

/**
 * The named sub-databases.
 *
 * `snap` is split in two because the two halves are asked for at very different
 * rates: composition tests flags, `referencedFunctionIds` and exception records
 * constantly, and materialises block ASTs comparatively rarely. Keeping the AST
 * payload in its own database means the cheap questions never page it in.
 */
export interface ColdStore {
	readonly path: string;
	readonly root: RootDatabase;
	/** Fingerprint and phase markers. String keys. */
	readonly meta: Database;
	/** functionId -> encoded `Function` (post-`structureInstructions`). */
	readonly fn: Database;
	/** Whole-file derived structures, by name. */
	readonly plan: Database;
	/** functionId -> `IRFunctionSnapshot` minus `blocks`. */
	readonly snapHead: Database;
	/** functionId -> the `blocks` array. */
	readonly snapBody: Database;
	/** fragment order index -> composed source text. */
	readonly frag: Database;
	/**
	 * Close the environment. **Only the thread that owns the session may call
	 * this**, and only once nothing else is using the store.
	 *
	 * lmdb-js hands every `open` of the same path the same *native* env, which
	 * is what makes concurrent readers cheap -- but `close()` tears that env
	 * down unconditionally (`read.js`: `env.address = 0; env.close()`), with no
	 * refcount across opens. Worse, it zeroes only the calling handle's
	 * address, so other threads keep a live-looking handle onto a closed env
	 * and read freed memory rather than getting an error. That surfaced as a
	 * garbled instruction name mid-lift.
	 */
	close(): Promise<void>;
	/**
	 * Release this thread's read transaction without touching the env.
	 *
	 * What a worker should do when it is finished: it frees the reader slot,
	 * which is the only per-thread resource it holds, and leaves the shared
	 * environment alone for everyone still reading.
	 */
	releaseReader(): void;
}

/**
 * Open (or create) a store.
 *
 * Every thread that touches a store calls this with the same path. lmdb-js keeps
 * one env per path per process and hands the same handle to each caller, which
 * is what makes it safe for several Deno workers to share a store: LMDB's own
 * rule is that a process must not open the same file twice, because closing
 * either handle would drop the POSIX record locks held for both.
 */
export async function openColdStore(
	path: string,
	options: ColdStoreOptions = {},
): Promise<ColdStore> {
	const { open } = await import('lmdb');
	const compression = options.compression ?? true;
	const root = open({
		path,
		maxDbs: 16,
		mapSize: options.mapSize ?? DEFAULT_MAP_SIZE,
		readOnly: options.readOnly ?? false,
		compression,
		// Readers hold no locks and never block the writer, so a reader that
		// outlives a write transaction cannot stall reclamation into a leak.
		noSync: false,
	});

	// Structures are per-database: the records in `fn` are HBC instructions and
	// the records in `snapBody` are Babel nodes, and pooling them would waste
	// most of the 32 slots msgpackr keeps.
	//
	// Only a database with a single writer may share them. A shared-structures
	// record is itself store state that every writer extends as it meets new
	// record shapes, and each Deno worker is its own realm with its own env
	// handle and its own structure cache -- so two workers extending it
	// concurrently leave a decoder mapping keys and strings through the wrong
	// table. That corrupts values while keeping the record's shape intact: an
	// audit selection candidate came back as `m_107238_5` (a slice of
	// `_param_107238_5`) with `mode: "pressio"` (a slice of the store's own
	// `compression` option), which is unrelated buffer content, not data any
	// writer wrote.
	//
	// `fn` and `plan` are filled once by the coordinator before any worker
	// starts, so they keep the pooling.
	const sub = (name: string, shared: boolean) =>
		root.openDB(name, {
			compression,
			...(shared
				? { sharedStructuresKey: Symbol.for(`ares.coldstore.${name}`) }
				: {}),
		});

	const store: ColdStore = {
		path,
		root,
		meta: sub('meta', false),
		fn: sub('fn', true),
		plan: sub('plan', true),
		snapHead: sub('snapHead', false),
		snapBody: sub('snapBody', false),
		frag: sub('frag', false),
		close: () => root.close(),
		releaseReader: () => root.resetReadTxn(),
	};
	return store;
}

/** SHA-256 of the bundle bytes, hex, for the fingerprint. */
export async function hashBytes(bytes: Uint8Array): Promise<string> {
	// A view rather than a copy: the bundle is tens of megabytes and this runs
	// on the hot path of every startup. The cast is because `Uint8Array` over an
	// `ArrayBufferLike` is not assignable to `BufferSource`, which excludes
	// `SharedArrayBuffer`; nothing here ever holds one.
	const view = new Uint8Array(
		bytes.buffer,
		bytes.byteOffset,
		bytes.byteLength,
	) as unknown as BufferSource;
	const digest = await crypto.subtle.digest('SHA-256', view);
	return [...new Uint8Array(digest)]
		.map((byte) => byte.toString(16).padStart(2, '0'))
		.join('');
}

/** A stable hash of anything JSON-shaped, for the options half of a fingerprint. */
export function hashOptions(value: unknown): string {
	// Sorted keys so that an option object built in a different order still
	// matches: a fingerprint that depends on property order would reject stores
	// that are in fact valid.
	const canonical = JSON.stringify(value, (_key, inner) => {
		if (
			inner == null || typeof inner !== 'object' || Array.isArray(inner)
		) {
			return inner;
		}
		const sorted: Record<string, unknown> = {};
		for (const key of Object.keys(inner as object).sort()) {
			sorted[key] = (inner as Record<string, unknown>)[key];
		}
		return sorted;
	});
	let hash = 0x811c9dc5;
	for (let i = 0; i < canonical.length; i++) {
		hash ^= canonical.charCodeAt(i);
		hash = Math.imul(hash, 0x01000193) >>> 0;
	}
	return hash.toString(16).padStart(8, '0');
}

export function readFingerprint(
	store: ColdStore,
): ColdStoreFingerprint | undefined {
	return store.meta.get('fingerprint') as ColdStoreFingerprint | undefined;
}

export async function writeFingerprint(
	store: ColdStore,
	fingerprint: ColdStoreFingerprint,
): Promise<void> {
	await store.meta.put('fingerprint', fingerprint);
}

export function fingerprintsMatch(
	left: ColdStoreFingerprint | undefined,
	right: ColdStoreFingerprint,
): boolean {
	return left != null &&
		left.schema === right.schema &&
		left.bundleHash === right.bundleHash &&
		left.bundleLength === right.bundleLength &&
		left.hermesVersion === right.hermesVersion &&
		left.optionsHash === right.optionsHash;
}

export function phaseComplete(
	store: ColdStore,
	phase: ColdStorePhase,
): boolean {
	return store.meta.get(`phase:${phase}`) === true;
}

export async function markPhaseComplete(
	store: ColdStore,
	phase: ColdStorePhase,
): Promise<void> {
	await store.meta.put(`phase:${phase}`, true);
}

/**
 * A bounded most-recently-used cache over decoded records.
 *
 * The store's own cache is the OS page cache, which holds *encoded* pages; this
 * bounds how many decoded JS object graphs are alive at once, which is the term
 * that actually cost 2.5GB per worker.
 */
export class DecodedCache<K, V> {
	#entries = new Map<K, V>();

	constructor(readonly limit: number) {}

	get(key: K): V | undefined {
		const value = this.#entries.get(key);
		if (value === undefined) return undefined;
		// Re-insert so iteration order stays least-recently-used first.
		this.#entries.delete(key);
		this.#entries.set(key, value);
		return value;
	}

	set(key: K, value: V): void {
		this.#entries.delete(key);
		this.#entries.set(key, value);
		while (this.#entries.size > Math.max(1, this.limit)) {
			const oldest = this.#entries.keys().next().value as K | undefined;
			if (oldest === undefined) break;
			this.#entries.delete(oldest);
		}
	}

	delete(key: K): boolean {
		return this.#entries.delete(key);
	}

	clear(): void {
		this.#entries.clear();
	}

	get size(): number {
		return this.#entries.size;
	}
}
