import type * as t from '@babel/types';
import { FunctionId } from '../../hbc/disassembly/instruction.ts';
import type { IRFunctionOptions } from '../function/mod.ts';
import { type ColdStore, openColdStore } from '../../coldstore/mod.ts';
import { readColdFile } from '../../coldstore/file.ts';
import { readColdPlan } from '../../coldstore/plan.ts';
import { ColdIRFunctionStore } from '../../coldstore/store.ts';
import { buildCompositionPlan, composeMetroModuleUnits } from '../lift.ts';
import type { EnvironmentIdentityDiagnostics } from '../lift.ts';

export interface ComposeWorkerRequest {
	/** The cold store holding the bundle, the plans and every snapshot. */
	spillPath: string;
	/** The modules to compose: the factory function and its captured env. */
	units: { functionId: FunctionId; envArg: t.Node }[];
	/**
	 * The reference closure of those modules -- everything they may read.
	 *
	 * Sent as ids rather than snapshots. Composition reads more than a unit
	 * owns, because a function referenced from several places is cloned rather
	 * than consumed, so the read set is genuinely wider than the subtree; what
	 * changed is only that the worker now pages those functions out of the
	 * store itself instead of being handed them.
	 */
	readable: FunctionId[];
	globalNames: string[];
	options?: IRFunctionOptions;
}

export type ComposeWorkerMessage =
	| { type: 'progress'; functionId: FunctionId }
	| {
		type: 'result';
		/**
		 * Which factories produced a fragment, and what composing them
		 * consumed. The source text itself goes into the store's `frag`
		 * database rather than back through `postMessage`: a bundle's worth of
		 * composed modules is hundreds of megabytes of string, and the emitter
		 * streams it straight out again.
		 */
		fragments: FunctionId[];
		consumed: FunctionId[];
		environmentIdentity: EnvironmentIdentityDiagnostics;
	}
	| {
		type: 'error';
		functionId?: FunctionId;
		message: string;
		stack?: string;
	};

type WorkerScope = {
	onmessage: ((event: MessageEvent<ComposeWorkerRequest>) => void) | null;
	postMessage(message: ComposeWorkerMessage): void;
};

const workerSelf = globalThis as unknown as WorkerScope;

workerSelf.onmessage = async (event: MessageEvent<ComposeWorkerRequest>) => {
	const { spillPath, units, readable, globalNames, options } = event.data;
	let store: ColdStore | undefined;
	try {
		// The file, the composition plan and every lifted function all come out
		// of the store. This worker used to rebuild the file from bytes and
		// re-derive both plans -- two full scans of every instruction in the
		// bundle, per worker -- which is the work the store exists to do once.
		const opened = await openColdStore(spillPath);
		store = opened;
		const { file } = readColdFile(opened);
		const plan = buildCompositionPlan(readColdPlan(opened));
		const functions = new ColdIRFunctionStore(
			file,
			opened,
			options ?? {},
			new Set(readable),
		);
		const composed = composeMetroModuleUnits(
			file,
			units,
			functions,
			plan,
			new Set(globalNames),
			(functionId: FunctionId) =>
				workerSelf.postMessage({ type: 'progress', functionId }),
		);
		await opened.root.transaction(() => {
			for (const [functionId, code] of composed.fragments) {
				opened.frag.put(functionId, code);
			}
		});
		if (Deno.env.get('ARES_COLDSTORE_STATS')) {
			functions.logStats(`compose batch of ${units.length}`);
		}
		workerSelf.postMessage(
			{
				type: 'result',
				fragments: composed.fragments.map(([functionId]) => functionId),
				consumed: composed.consumed,
				environmentIdentity: composed.environmentIdentity,
			} satisfies ComposeWorkerMessage,
		);
	} catch (error) {
		workerSelf.postMessage(
			{
				type: 'error',
				message: error instanceof Error ? error.message : String(error),
				stack: error instanceof Error ? error.stack : undefined,
			} satisfies ComposeWorkerMessage,
		);
	} finally {
		// Not `close()`: the environment is shared with every other worker in
		// this process, and closing it from here would unmap it under them.
		// Releasing the reader gives back the only thing this thread owns.
		store?.releaseReader();
	}
};
