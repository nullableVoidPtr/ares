/**
 * An `IRFunctionStore` whose functions live in the cold store until asked for.
 *
 * The eager store is handed a `Map` that already holds every lifted function.
 * Building that map is what `buildIRFunctionsParallel` did up front: decode
 * every snapshot, rehydrate every `IRFunction`, keep both alive for the whole
 * run. This store starts empty and materialises on demand, which matters most
 * on the parallel Metro path, where the compose workers consume most functions
 * and the main thread never has to build them at all.
 *
 * Materialised functions are then held strongly until they are consumed, and
 * that is deliberate rather than lazy design. Composition mutates what the store
 * hands it -- `tryGetFunctionExpr` reduces in place, and `cloneNestedFunctionRef`
 * reads the same function again on a bounded-cache miss -- so handing back a
 * fresh object for a second `get` of a live function would silently discard the
 * first one's work. Eviction needs a notion of which functions are checked out;
 * until then, consumption is what bounds this, and on the Metro path
 * consumption is exactly what happens.
 */
import type { FunctionId } from '../hbc/disassembly/instruction.ts';
import type { HBCFile } from '../parser/file.ts';
import { IRFunction, type IRFunctionOptions } from '../ir/function/mod.ts';
import type { IRFunctionStore } from '../ir/function/store.ts';
import { copyFunctionForSSA, SSAFunction } from '../ssa.ts';
import { type ColdStore, DecodedCache } from './mod.ts';
import { hasColdSnapshot, readColdSnapshot } from './snapshot.ts';

export interface ColdIRFunctionStoreStats {
	/** Snapshots decoded and rehydrated into an `IRFunction`. */
	materialised: number;
	/** Functions consumed, and so dropped from memory again. */
	consumed: number;
	/** Functions currently held, pinned plus cached. */
	live: number;
	/** Of those, the ones composition wrote back and that cannot be evicted. */
	pinned: number;
	/** The most ever held at once -- what an eviction bound would cap. */
	peakLive: number;
}

export class ColdIRFunctionStore implements IRFunctionStore {
	#consumed = new Set<FunctionId>();
	/**
	 * Functions composition has written back through `set`.
	 *
	 * Never evicted: these are run state, not a decode of something the store
	 * still holds, so dropping one would destroy work rather than defer it.
	 */
	#pinned = new Map<FunctionId, IRFunction>();
	/**
	 * Functions materialised by `get`, bounded.
	 *
	 * Safe to evict because each is re-derivable from its snapshot -- the same
	 * assumption `relift` makes when it rebuilds a consumed function from
	 * scratch, and that `cloneNestedFunctionRef` makes when its own bounded
	 * cache misses.
	 */
	#cache: DecodedCache<FunctionId, IRFunction>;
	#materialised = 0;
	#peakLive = 0;

	constructor(
		readonly file: HBCFile,
		readonly cold: ColdStore,
		readonly options: IRFunctionOptions,
		/**
		 * Restrict reads to these ids, or serve the whole store when absent.
		 *
		 * A compose worker used to be handed snapshots and could therefore only
		 * see what it was sent. Reading straight from the store would silently
		 * widen that to the entire program, so the caller passes the same
		 * reference closure it used to ship. This is a read set, not a consume
		 * set -- `SubtreeIRFunctionStore` still owns the latter -- because a
		 * function referenced from several places is cloned rather than
		 * consumed and belongs to no single subtree.
		 */
		readonly readable?: ReadonlySet<FunctionId>,
		/**
		 * How many materialised functions to keep.
		 *
		 * Unbounded retention is what killed the 127k-function bundle: a
		 * resumed run finds nearly every module ready at once, `enumerate`
		 * materialises each factory to check whether it composes, and at
		 * ~280KB apiece 16,646 of them is ~4.6GB against V8's ~4GB per-isolate
		 * cap. The main thread died in 21 seconds with `consumed=0`.
		 */
		cacheLimit = 512,
	) {
		this.#cache = new DecodedCache(cacheLimit);
	}

	#readable(functionId: FunctionId): boolean {
		return this.readable == null || this.readable.has(functionId);
	}

	has(functionId: FunctionId): boolean {
		if (this.#consumed.has(functionId)) return false;
		if (this.#pinned.has(functionId)) return true;
		if (!this.#readable(functionId)) return false;
		return hasColdSnapshot(this.cold, functionId);
	}

	get(functionId: FunctionId): IRFunction | undefined {
		if (this.#consumed.has(functionId)) return undefined;
		const pinned = this.#pinned.get(functionId);
		if (pinned) return pinned;
		const cached = this.#cache.get(functionId);
		if (cached) return cached;
		if (!this.#readable(functionId)) return undefined;

		const snapshot = readColdSnapshot(this.cold, functionId);
		if (!snapshot) return undefined;
		const func = IRFunction.fromSnapshot(this.file, snapshot);
		this.#materialised++;
		this.#cache.set(functionId, func);
		const live = this.#pinned.size + this.#cache.size;
		if (live > this.#peakLive) this.#peakLive = live;
		return func;
	}

	delete(functionId: FunctionId): boolean {
		if (!this.has(functionId)) return false;
		this.#consumed.add(functionId);
		this.#pinned.delete(functionId);
		this.#cache.delete(functionId);
		return true;
	}

	/**
	 * Report the store's occupancy, for sizing an eviction bound.
	 *
	 * Straight to the file descriptor, not through `console.error`, because
	 * `src/ares.ts` replaces that with a no-op under `--no-progress` -- and a
	 * diagnostic that the measurement harness can silence is worse than none,
	 * since its absence reads as "nothing happened".
	 */
	logStats(label: string): void {
		const { materialised, consumed, live, pinned, peakLive } = this.stats;
		Deno.stderr.writeSync(
			new TextEncoder().encode(
				`[coldstore] ${label}: materialised=${materialised} ` +
					`consumed=${consumed} live=${live} pinned=${pinned} ` +
					`peakLive=${peakLive}\n`,
			),
		);
	}

	set(functionId: FunctionId, func: IRFunction): void {
		// An overlay, never a write back to the store. The spill is the clean
		// baseline for the run; a function that composition has rewritten is
		// run state, and persisting it would make a resumed run start from
		// half-composed input.
		this.#consumed.delete(functionId);
		this.#cache.delete(functionId);
		this.#pinned.set(functionId, func);
	}

	relift(functionId: FunctionId): IRFunction | undefined {
		if (!this.#consumed.has(functionId)) return;
		return new IRFunction(
			this.file,
			new SSAFunction(
				copyFunctionForSSA(this.file.functions[functionId]),
			),
			this.options,
		);
	}

	get stats(): ColdIRFunctionStoreStats {
		return {
			materialised: this.#materialised,
			consumed: this.#consumed.size,
			live: this.#pinned.size + this.#cache.size,
			pinned: this.#pinned.size,
			peakLive: this.#peakLive,
		};
	}
}
