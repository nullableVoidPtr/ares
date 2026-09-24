import { SSAFunction } from '../../ssa.ts';
import { FunctionId } from '../../hbc/disassembly/instruction.ts';
import { type ColdStore, openColdStore } from '../../coldstore/mod.ts';
import { readColdFile } from '../../coldstore/file.ts';
import { putColdSnapshot } from '../../coldstore/snapshot.ts';
import { compactRecursiveCFGSummary } from './cfg/recursiveSummary.ts';
import traverse from '@babel/traverse';
import {
	IRFunction,
	type IRFunctionOptions,
	type IRFunctionSnapshot,
} from './mod.ts';

/**
 * A lift worker takes batches until it is told to stop.
 *
 * It receives no bundle and hands back no snapshots: it pages the functions it
 * was asked for out of the cold store and writes their snapshots straight back
 * into it, so nothing crosses the message boundary but ids. Rebuilding the
 * `HBCFile` here cost 2,583MB of resident set per worker on a large bundle, for
 * a chunk of ids that needs a handful of its functions.
 *
 * Batches arrive one at a time rather than as a single static chunk, because
 * composition no longer waits for lifting to finish. A static chunk would mean
 * the main thread could not reprioritise once it knows which functions a module
 * actually needs, and could not rebalance when one worker draws a function that
 * takes minutes.
 *
 * `written` is reported *after* the transaction commits, not after lifting. A
 * scheduler acting on "lifted" would dispatch a module whose dependencies are
 * still sitting in an uncommitted batch.
 */
export type IRFunctionWorkerRequest =
	| {
		type: 'lift';
		spillPath: string;
		functionIds: FunctionId[];
		options?: IRFunctionOptions;
	}
	| { type: 'close' };

export type IRFunctionWorkerMessage =
	| { type: 'progress'; functionId: FunctionId }
	/**
	 * These ids are committed and readable; `failed` are functions this batch
	 * could not lift at all.
	 *
	 * A failure is reported rather than thrown because one unliftable function
	 * must not end a run over 127,282 of them. Composition already degrades
	 * gracefully for a function with no snapshot -- `has` is false, `get` is
	 * undefined, and `cloneNestedFunctionRef` leaves the raw `%CreateClosure`
	 * in place -- so the cost is one un-inlined closure rather than no output.
	 */
	| {
		type: 'written';
		functionIds: FunctionId[];
		failed: {
			functionId: FunctionId;
			message: string;
			/** Our frames from the failure, innermost first. */
			frames: string[];
		}[];
		/**
		 * This worker's heap after the batch.
		 *
		 * Reported because V8 grows to a high-water mark and never returns it,
		 * so a long-lived worker's cost is set by the worst function it ever
		 * drew -- and on a 127k-function bundle that is what a run dies of.
		 * Without this the main thread can only guess at the shape.
		 */
		heapUsed: number;
	}
	| { type: 'closed' }
	| {
		type: 'error';
		functionId?: FunctionId;
		message: string;
		stack?: string;
	};

type WorkerScope = {
	onmessage:
		| ((event: MessageEvent<IRFunctionWorkerRequest>) => void)
		| null;
	postMessage(message: IRFunctionWorkerMessage): void;
};

// Deno truncates stacks at ten frames, and a lift failure surfaces from deep
// inside Babel -- the frames that identify *our* failing pass sit well below
// that cut. Diagnosing one such failure previously required rebuilding the run
// with this raised by hand.
Error.stackTraceLimit = 200;

const workerSelf = globalThis as unknown as WorkerScope;

/**
 * Makes one function unliftable, so the skip-and-continue path can be tested
 * without waiting for a real decompiler bug to turn up.
 *
 * Read once rather than per function: this sits in the innermost loop of the
 * whole pipeline, and the failure path is otherwise only reachable by finding
 * a genuinely broken function in a 127k-function bundle -- which is how it
 * came to ship with its reporting silenced by `--no-progress`.
 */
const FAULT_FUNCTION_ID = Number(
	Deno.env.get('ARES_FAULT_FN') ?? Number.NaN,
);

let store: ColdStore | undefined;
let coldFile: ReturnType<typeof readColdFile>['file'] | undefined;

/**
 * Requests are handled strictly in order.
 *
 * The protocol keeps one batch in flight per worker, so this only matters for a
 * `close` arriving while a batch is still committing -- but releasing a reader
 * out from under an open write transaction is not a failure worth debugging
 * later.
 */
let queue: Promise<void> = Promise.resolve();

workerSelf.onmessage = (event: MessageEvent<IRFunctionWorkerRequest>) => {
	const request = event.data;
	queue = queue
		.then(() => handleRequest(request))
		.catch((error) => {
			workerSelf.postMessage({
				type: 'error',
				message: error instanceof Error ? error.message : String(error),
				stack: error instanceof Error ? error.stack : undefined,
			});
		});
};

async function handleRequest(
	request: IRFunctionWorkerRequest,
): Promise<void> {
	if (request.type === 'close') {
		// Releases this thread's reader; the environment itself belongs to the
		// session on the main thread. Every worker gets this message at once
		// during shutdown, so a `close()` here would have the first one unmap
		// the env and leave the rest -- and `session.release()` after them --
		// working against a dead handle.
		store?.releaseReader();
		store = undefined;
		coldFile = undefined;
		workerSelf.postMessage({ type: 'closed' });
		return;
	}

	const { spillPath, functionIds, options } = request;
	if (!store) {
		store = await openColdStore(spillPath);
		coldFile = readColdFile(store).file;
	}
	const opened = store;
	const file = coldFile!;

	const lifted: [FunctionId, IRFunctionSnapshot][] = [];
	const failed: {
		functionId: FunctionId;
		message: string;
		frames: string[];
	}[] = [];
	for (const id of functionIds) {
		try {
			if (id === FAULT_FUNCTION_ID) {
				throw new TypeError(`injected fault for #${id}`);
			}
			const func = new IRFunction(
				file,
				new SSAFunction(file.functions[id]),
				options,
			);
			// Snapshotted here rather than at the flush below. The snapshot is
			// the only part of a lifted function the store wants, and taking it
			// now lets the rest die with this iteration instead of being held
			// for the whole batch: the SSA form, the handler graph, the CFG
			// analyses, and the Region emission program and source. Block
			// bodies are shared with the snapshot, not copied, so the AST this
			// retains is unchanged.
			const snapshot = func.snapshot();
			// The Region emission program and its source are analysis output;
			// only the recursive CFG output modes, compare mode and the
			// migration audit read them back out of the store. Everything else
			// would pay for them twice -- once in this worker's heap and once
			// per snapshot head, which is where they were 18,300,154 of
			// 18,428,690 head bytes on the v96 main sample.
			if (options?.cfgReducer?.retainArtifacts === false) {
				snapshot.recursiveCFGSummary = compactRecursiveCFGSummary(
					snapshot.recursiveCFGSummary,
				);
			}
			lifted.push([id, snapshot]);
			// Babel's path cache is only *weakly* rooted at the top: child paths
			// hang off `parentPath._store`, a strong Map, so a function's whole
			// NodePath tree is retained until its AST is collected -- and then
			// only once GC actually runs. Outrunning the collector that way is
			// what OOM-killed the first parallel compose attempt.
			//
			// This worker used to get one static chunk and then terminate, which
			// reclaimed everything for free. It now lives for the whole run, so
			// the reclaim has to be explicit. Measured worth is small and not
			// firmly separated from noise -- ~110MB of mean lift-phase peak over
			// three runs per arm, with overlapping ranges -- so this is kept for
			// the structural reason, not the number.
			//
			// Safe here: reduction is complete, and `snapshot()` reads plain
			// nodes and clones them with `t.cloneNode` -- it never asks for a
			// NodePath, so there is none to invalidate.
			traverse.cache.clear();
			workerSelf.postMessage({ type: 'progress', functionId: id });
		} catch (error) {
			// The throwing traversal left its paths behind; clear before
			// moving on, or a failure leaks what a success would not.
			traverse.cache.clear();
			failed.push({
				functionId: id,
				message: error instanceof Error ? error.message : String(error),
				// Only our own frames: two hundred frames of Babel internals
				// per failure is not a diagnostic, it is a haystack. These are
				// what name the pass that broke.
				frames: error instanceof Error
					? (error.stack ?? '').split('\n')
						.filter((line) => line.includes('/lib/ir/'))
						.map((line) =>
							line.trim().replace(/^at\s+/, '').replace(
								/\(?file:\/\/.*?\/(lib\/)/,
								'$1',
							).replace(/\)$/, '')
						)
						.slice(0, 6)
					: [],
			});
			workerSelf.postMessage({ type: 'progress', functionId: id });
		}
	}

	// One transaction per batch: a commit per function would serialise every
	// lift worker on lmdb-js's single writer thread.
	//
	// Encoding each function and releasing its AST immediately was tried, on
	// the theory that holding `batchSize` complete ASTs was the larger cost. It
	// measured no better -- the difference sat inside the run-to-run spread of
	// this box, which is ~10% on peak RSS. What the batch holds is now
	// snapshots rather than lifted functions, so `batchSize` trades queued AST
	// bodies against write-queue depth alone; bodies run from 25KB to 46MB, so
	// the balance is function-size dependent and worth measuring on a real
	// bundle.
	await opened.root.transaction(() => {
		for (const [id, snapshot] of lifted) {
			putColdSnapshot(opened, id, snapshot);
		}
	});
	workerSelf.postMessage({
		type: 'written',
		functionIds: lifted.map(([id]) => id),
		failed,
		heapUsed: Deno.memoryUsage().heapUsed,
	});
}
