import type * as t from '@babel/types';
import traverse from '@babel/traverse';
import type { FunctionId } from '../hbc/disassembly/instruction.ts';
import { type ColdStore, openColdStore } from '../coldstore/mod.ts';
import { readColdFile } from '../coldstore/file.ts';
import { readColdPlan } from '../coldstore/plan.ts';
import { putColdSnapshot } from '../coldstore/snapshot.ts';
import { ColdIRFunctionStore } from '../coldstore/store.ts';
import type { HBCFile } from '../parser/file.ts';
import { copyFunctionForSSA, SSAFunction } from '../ssa.ts';
import { compactRecursiveCFGSummary } from './function/cfg/recursiveSummary.ts';
import {
	IRFunction,
	type IRFunctionOptions,
	type IRFunctionSnapshot,
} from './function/mod.ts';
import type { IRFunctionStore } from './function/store.ts';
import {
	buildCompositionPlan,
	composeMetroModuleUnits,
	emptyEnvironmentIdentityDiagnostics,
	type EnvironmentIdentityDiagnostics,
} from './lift.ts';

export interface ParallelComposeUnit {
	functionId: FunctionId;
	envArg: t.Node;
}

export type ParallelWorkerRequest =
	| {
		type: 'lift';
		spillPath: string;
		functionIds: FunctionId[];
		options?: IRFunctionOptions;
	}
	| {
		type: 'compose';
		spillPath: string;
		units: ParallelComposeUnit[];
		readable: FunctionId[];
		globalNames: string[];
		options?: IRFunctionOptions;
	}
	| { type: 'close' };

export type ParallelWorkerMessage =
	| { type: 'progress'; phase: 'lift' | 'compose'; functionId: FunctionId }
	| {
		type: 'written';
		functionIds: FunctionId[];
		failed: {
			functionId: FunctionId;
			message: string;
			frames: string[];
		}[];
		heapUsed: number;
	}
	| {
		type: 'composed';
		fragments: FunctionId[];
		consumed: FunctionId[];
		failed: {
			functionId: FunctionId;
			message: string;
		}[];
		environmentIdentity: EnvironmentIdentityDiagnostics;
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
	onmessage: ((event: MessageEvent<ParallelWorkerRequest>) => void) | null;
	postMessage(message: ParallelWorkerMessage): void;
};

class FreshIRFunctionStore implements IRFunctionStore {
	#functions = new Map<FunctionId, IRFunction>();
	#consumed = new Set<FunctionId>();

	constructor(
		readonly file: HBCFile,
		readonly options: IRFunctionOptions,
		functionIds: readonly FunctionId[],
	) {
		for (const id of functionIds) {
			this.#functions.set(
				id,
				new IRFunction(
					file,
					new SSAFunction(copyFunctionForSSA(file.functions[id])),
					options,
				),
			);
		}
	}

	has(functionId: FunctionId): boolean {
		return this.#functions.has(functionId);
	}

	get(functionId: FunctionId): IRFunction | undefined {
		return this.#functions.get(functionId);
	}

	delete(functionId: FunctionId): boolean {
		if (!this.#functions.has(functionId)) return false;
		this.#consumed.add(functionId);
		return this.#functions.delete(functionId);
	}

	set(functionId: FunctionId, func: IRFunction): void {
		this.#consumed.delete(functionId);
		this.#functions.set(functionId, func);
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

	snapshots(): [FunctionId, IRFunctionSnapshot][] {
		return [...this.#functions].map(([id, func]) => [id, func.snapshot()]);
	}
}

function isDuplicateDeclarationError(error: unknown): boolean {
	return error instanceof Error &&
		/\bDuplicate declaration\b/.test(error.message);
}

function mergeEnvironmentIdentityDiagnostics(
	target: EnvironmentIdentityDiagnostics,
	source: EnvironmentIdentityDiagnostics,
): void {
	for (
		const key of Object.keys(target) as Array<
			keyof EnvironmentIdentityDiagnostics
		>
	) {
		target[key] += source[key];
	}
}

Error.stackTraceLimit = 200;

const workerSelf = globalThis as unknown as WorkerScope;
const FAULT_FUNCTION_ID = Number(
	Deno.env.get('ARES_FAULT_FN') ?? Number.NaN,
);

let store: ColdStore | undefined;
let coldFile: HBCFile | undefined;
let queue: Promise<void> = Promise.resolve();

workerSelf.onmessage = (event: MessageEvent<ParallelWorkerRequest>) => {
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

async function openSession(spillPath: string): Promise<{
	store: ColdStore;
	file: HBCFile;
}> {
	if (!store) {
		store = await openColdStore(spillPath);
		coldFile = readColdFile(store).file;
	}
	return { store, file: coldFile! };
}

async function handleRequest(request: ParallelWorkerRequest): Promise<void> {
	if (request.type === 'close') {
		store?.releaseReader();
		store = undefined;
		coldFile = undefined;
		workerSelf.postMessage({ type: 'closed' });
		return;
	}
	if (request.type === 'lift') {
		await handleLift(request);
		return;
	}
	await handleCompose(request);
}

async function handleLift(
	request: Extract<ParallelWorkerRequest, { type: 'lift' }>,
): Promise<void> {
	const { store: opened, file } = await openSession(request.spillPath);
	const lifted: [FunctionId, IRFunctionSnapshot][] = [];
	const failed: {
		functionId: FunctionId;
		message: string;
		frames: string[];
	}[] = [];
	for (const id of request.functionIds) {
		try {
			if (id === FAULT_FUNCTION_ID) {
				throw new TypeError(`injected fault for #${id}`);
			}
			const func = new IRFunction(
				file,
				new SSAFunction(file.functions[id]),
				request.options,
			);
			const snapshot = func.snapshot();
			if (request.options?.cfgReducer?.retainArtifacts === false) {
				snapshot.recursiveCFGSummary = compactRecursiveCFGSummary(
					snapshot.recursiveCFGSummary,
				);
			}
			lifted.push([id, snapshot]);
			traverse.cache.clear();
			workerSelf.postMessage({
				type: 'progress',
				phase: 'lift',
				functionId: id,
			});
		} catch (error) {
			traverse.cache.clear();
			failed.push({
				functionId: id,
				message: error instanceof Error ? error.message : String(error),
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
			workerSelf.postMessage({
				type: 'progress',
				phase: 'lift',
				functionId: id,
			});
		}
	}

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

async function handleCompose(
	request: Extract<ParallelWorkerRequest, { type: 'compose' }>,
): Promise<void> {
	const { store: opened, file } = await openSession(request.spillPath);
	const plan = buildCompositionPlan(readColdPlan(opened));
	const globalNames = new Set(request.globalNames);
	const compose = (functions: IRFunctionStore, units = request.units) =>
		composeMetroModuleUnits(
			file,
			units,
			functions,
			plan,
			globalNames,
			(functionId: FunctionId) =>
				workerSelf.postMessage({
					type: 'progress',
					phase: 'compose',
					functionId,
				}),
		);
	const coldFunctions = new ColdIRFunctionStore(
		file,
		opened,
		request.options ?? {},
		new Set(request.readable),
	);
	let composed: ReturnType<typeof composeMetroModuleUnits>;
	const failed: { functionId: FunctionId; message: string }[] = [];
	try {
		composed = compose(coldFunctions);
	} catch (error) {
		// A batch can fail even when every unit composes by itself: composition
		// mutates the shared function store as it consumes nested closures. Split
		// only on failure, so the common path keeps one store and one generated
		// fragment transaction.
		composed = {
			fragments: [],
			consumed: [],
			environmentIdentity: emptyEnvironmentIdentityDiagnostics(),
		};
		for (const unit of request.units) {
			try {
				const single = compose(
					new ColdIRFunctionStore(
						file,
						opened,
						request.options ?? {},
						new Set(request.readable),
					),
					[unit],
				);
				composed.fragments.push(...single.fragments);
				composed.consumed.push(...single.consumed);
				mergeEnvironmentIdentityDiagnostics(
					composed.environmentIdentity,
					single.environmentIdentity,
				);
			} catch (singleError) {
				if (!isDuplicateDeclarationError(singleError)) {
					failed.push({
						functionId: unit.functionId,
						message: singleError instanceof Error
							? singleError.message
							: String(singleError),
					});
					continue;
				}
				const fresh = new FreshIRFunctionStore(
					file,
					request.options ?? {},
					request.readable,
				);
				const snapshots = fresh.snapshots();
				await opened.root.transaction(() => {
					for (const [id, snapshot] of snapshots) {
						putColdSnapshot(opened, id, snapshot);
					}
				});
				try {
					const single = compose(fresh, [unit]);
					composed.fragments.push(...single.fragments);
					composed.consumed.push(...single.consumed);
					mergeEnvironmentIdentityDiagnostics(
						composed.environmentIdentity,
						single.environmentIdentity,
					);
				} catch (freshError) {
					failed.push({
						functionId: unit.functionId,
						message: freshError instanceof Error
							? freshError.message
							: String(freshError),
					});
				}
			}
		}
		if (composed.fragments.length === 0 && failed.length === 0) {
			throw error;
		}
	}
	await opened.root.transaction(() => {
		for (const [functionId, code] of composed.fragments) {
			opened.frag.put(functionId, code);
		}
	});
	if (Deno.env.get('ARES_COLDSTORE_STATS')) {
		coldFunctions.logStats(`compose batch of ${request.units.length}`);
	}
	workerSelf.postMessage({
		type: 'composed',
		fragments: composed.fragments.map(([functionId]) => functionId),
		consumed: composed.consumed,
		failed,
		environmentIdentity: composed.environmentIdentity,
		heapUsed: Deno.memoryUsage().heapUsed,
	});
}
