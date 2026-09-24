import { FunctionId } from '../hbc/disassembly/instruction.ts';
import {
	type EnvironmentSiteId,
	environmentSiteKey,
} from '../coldstore/plan.ts';

/**
 * How an inner function's environment operand relates to a wrapper which is
 * removed during composition.
 *
 * `local` preserves the runtime environment created by the wrapper itself.
 * `parent` preserves an explicit GetParentEnvironment walk from the wrapper's
 * captured environment. Keeping this as provenance avoids compensating for a
 * removed wrapper by adjusting every environment depth in the inner body.
 */
export type ElidedWrapperEnvironmentCapture =
	| { kind: 'local' }
	| { kind: 'parent'; depth: number };

export function isEnvironmentSlotName(name: string): boolean {
	return /^_env_\d+(?:_x\d+)?(?:_\d+)+$/.test(name);
}

export class Environment {
	constructor(
		public readonly functionId: FunctionId,
		public readonly parent: Environment | null,
		private readonly namePrefix = `_env_${functionId}`,
		private siteId: EnvironmentSiteId | null = null,
	) {}

	get site(): EnvironmentSiteId | null {
		return this.siteId;
	}

	/** Attach the bytecode creation identity once composition resolves it. */
	claimSite(site: EnvironmentSiteId): void {
		if (this.siteId == null) {
			this.siteId = site;
			return;
		}
		if (environmentSiteKey(this.siteId) !== environmentSiteKey(site)) {
			throw new Error(
				`Environment ${this.functionId} claimed by two creation sites`,
			);
		}
	}

	slotName(slot: number): string {
		return `${this.namePrefix}_${slot}`;
	}
}

/**
 * Build the environment chain.
 *
 * Takes the set of environment-creating functions rather than the file: working
 * that set out means reading every instruction in the bundle, which now happens
 * once in `buildBytecodeDerivedPlan` alongside the three other whole-file scans
 * instead of once here and again per worker.
 *
 * Order matters -- `findParentEnvironment` looks up ancestors in the map being
 * built -- so this walks ids ascending, which is the order the previous
 * `for (let i = 0; i < file.functions.length; i++)` used.
 */
export function buildEnvironmentGraph(
	environmentCreators: ReadonlySet<FunctionId>,
	functionCount: number,
	parentFunctions: Map<FunctionId, FunctionId>,
	environmentCreationSites?: ReadonlyMap<
		FunctionId,
		readonly EnvironmentSiteId[]
	>,
): Map<FunctionId, Environment> {
	const environments = new Map<FunctionId, Environment>();
	for (let i = 0; i < functionCount; i++) {
		if (!environmentCreators.has(i)) continue;
		const parent = findParentEnvironment(i, parentFunctions, environments);
		const primarySite = environmentCreationSites?.get(i)?.find((site) =>
			site.kind === 'CreateFunctionEnvironment' ||
			site.kind === 'CreateTopLevelEnvironment'
		) ?? null;
		environments.set(
			i,
			new Environment(i, parent, `_env_${i}`, primarySite),
		);
	}
	return environments;
}

function findParentEnvironment(
	funcId: FunctionId,
	parentFunctions: Map<FunctionId, FunctionId>,
	environments: Map<FunctionId, Environment>,
): Environment | null {
	let id = parentFunctions.get(funcId);
	while (id != null) {
		const env = environments.get(id);
		if (env != null) return env;
		id = parentFunctions.get(id);
	}
	return null;
}

export function capturedEnvironment(
	funcId: FunctionId,
	depth: number,
	environments: Map<FunctionId, Environment>,
	parentFunctions: Map<FunctionId, FunctionId>,
): Environment | undefined {
	let id = parentFunctions.get(funcId);
	let seen = -1;
	while (id != null) {
		const env = environments.get(id);
		if (env != null && ++seen === depth) return env;
		id = parentFunctions.get(id);
	}
	return undefined;
}
