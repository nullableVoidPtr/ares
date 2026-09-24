/**
 * Spilling lifted IR snapshots.
 *
 * A snapshot used to make two trips through structured clone -- serialised in
 * the lift worker, deserialised on the main thread -- after which the main
 * thread held every one of them plus a rehydrated `IRFunction` for each, for the
 * whole run. On a 127k-function bundle the encoded snapshots alone are ~3.2GiB.
 *
 * Writing them here instead is measurably cheaper than the `postMessage` it
 * replaces (0.45ms/snapshot to store against 0.58ms to structured-clone), and
 * the worker can write each one as it finishes rather than accumulating a whole
 * chunk to hand back at the end.
 *
 * The record is split in two. Everything except `blocks` is small, and is what
 * cheap questions want: whether a function is a generator, what it references,
 * its handler graph, its recursive-CFG summary. `blocks` is the Babel AST and
 * is the whole 3.2GiB. Keeping them apart means asking a cheap question never
 * pages in an AST -- which is what lets the recursive-summary collection walk
 * every function without materialising any of them.
 */
import type { FunctionId } from '../hbc/disassembly/instruction.ts';
import type { IRFunctionSnapshot } from '../ir/function/mod.ts';
import type { RecursiveCFGSummary } from '../ir/function/cfg/recursiveSummary.ts';
import type { ColdStore } from './mod.ts';
import { encodeForStore, type TaggedRecord, unwrapStored } from './codec.ts';

/** A snapshot without its block bodies. */
export type ColdSnapshotHead = Omit<IRFunctionSnapshot, 'blocks'>;

/** The block bodies on their own. */
type ColdSnapshotBody = IRFunctionSnapshot['blocks'];

/**
 * Queue a snapshot for writing.
 *
 * Not awaited per call and not transactional per call on purpose: callers batch
 * these inside one `store.root.transaction`, because a commit per function
 * would serialise every lift worker on the single writer thread.
 */
export function putColdSnapshot(
	store: ColdStore,
	functionId: FunctionId,
	snapshot: IRFunctionSnapshot,
): Promise<unknown> {
	const { blocks, ...head } = snapshot;
	store.snapHead.put(functionId, encodeForStore(head as ColdSnapshotHead));
	// The body settles last, so awaiting it is enough to know both are
	// committed -- lmdb-js queues writes in call order.
	return store.snapBody.put(
		functionId,
		encodeForStore(blocks as ColdSnapshotBody),
	);
}

export function hasColdSnapshot(
	store: ColdStore,
	functionId: FunctionId,
): boolean {
	return store.snapHead.doesExist(functionId);
}

export function deleteColdSnapshot(
	store: ColdStore,
	functionId: FunctionId,
): void {
	store.snapHead.remove(functionId);
	store.snapBody.remove(functionId);
}

export function readColdSnapshotHead(
	store: ColdStore,
	functionId: FunctionId,
): ColdSnapshotHead | undefined {
	return unwrapStored(
		store.snapHead.get(functionId) as
			| TaggedRecord<ColdSnapshotHead>
			| undefined,
	);
}

export function readColdSnapshot(
	store: ColdStore,
	functionId: FunctionId,
): IRFunctionSnapshot | undefined {
	const head = readColdSnapshotHead(store, functionId);
	if (!head) return undefined;
	const blocks = unwrapStored(
		store.snapBody.get(functionId) as
			| TaggedRecord<ColdSnapshotBody>
			| undefined,
	);
	if (!blocks) {
		throw new Error(
			`Cold store at ${store.path} has a head but no body for ` +
				`function #${functionId}`,
		);
	}
	return { ...head, blocks };
}

/**
 * Every recursive-CFG summary in the store, in function order.
 *
 * Reads heads only. The eager path collected these by walking every rehydrated
 * `IRFunction`, which against a lazily materialised store would defeat the
 * point of not materialising them.
 */
export function readColdRecursiveSummaries(
	store: ColdStore,
	functionCount: number,
): RecursiveCFGSummary[] {
	const summaries: RecursiveCFGSummary[] = [];
	for (let id = 0; id < functionCount; id++) {
		const head = readColdSnapshotHead(store, id);
		if (head?.recursiveCFGSummary) summaries.push(head.recursiveCFGSummary);
	}
	return summaries;
}

/**
 * Functions that could not be lifted, kept with the store rather than only in
 * a log.
 *
 * A resumed run re-attempts them -- the `snap` phase is deliberately never
 * marked complete while any failed -- so without a record it would rediscover
 * the same set silently every time, and the list would live only in whichever
 * terminal scrollback happened to catch it.
 */
const FAILURES_KEY = 'lift:failures';

export async function recordLiftFailures(
	store: ColdStore,
	failures: ReadonlyMap<FunctionId, string>,
): Promise<void> {
	if (failures.size === 0) return;
	// Merged, not replaced: a resumed run only attempts what is outstanding,
	// so its failures are a subset and would otherwise drop the rest.
	const merged = new Map(readLiftFailures(store));
	for (const [functionId, reason] of failures) merged.set(functionId, reason);
	await store.meta.put(FAILURES_KEY, [...merged]);
}

export function readLiftFailures(store: ColdStore): Map<FunctionId, string> {
	const stored = store.meta.get(FAILURES_KEY) as
		| [FunctionId, string][]
		| undefined;
	return new Map(stored ?? []);
}

/** Drop the record for functions that have since lifted successfully. */
export async function clearLiftFailures(
	store: ColdStore,
	functionIds: Iterable<FunctionId>,
): Promise<void> {
	const merged = readLiftFailures(store);
	let changed = false;
	for (const id of functionIds) changed = merged.delete(id) || changed;
	if (changed) await store.meta.put(FAILURES_KEY, [...merged]);
}
