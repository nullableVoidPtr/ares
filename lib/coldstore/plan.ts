/**
 * The whole-file structures derived from bytecode, computed once.
 *
 * Four separate passes used to walk every instruction in the bundle: the
 * function reference plan, the closure reference graph, the set of functions
 * that create an environment, and the globals declared by the bytecode. On a
 * 127k-function bundle that is 5.9M instructions per pass, and
 * `lib/ir/compose/worker.ts` ran two of them *inside every compose worker*.
 *
 * They are all pure functions of the bytes, so they are folded into a single
 * pass here, stored, and read back by everyone else. That matters twice over:
 * it removes the repeated work, and it removes the only reason anything needed
 * to iterate `file.functions` -- which, against a paged cold file, would drag
 * the entire bundle back into memory and undo the point of paging it.
 */
import { FunctionId, isFunctionRef } from '../hbc/disassembly/instruction.ts';
import type { HBCFile } from '../parser/file.ts';
import type { ColdStore } from './mod.ts';

/**
 * One environment-creating instruction, identified by where it is.
 *
 * Derived here rather than by traversing the composed AST, because that
 * traversal runs once before child functions are inlined and therefore only
 * ever sees the root's creation calls -- and because it keys sites on AST node
 * identity, which a clone does not share. The bytecode has every site, in a
 * fixed order, before any of that. See `BINDING-TODO.md` Phase 1.
 */
export interface EnvironmentSiteId {
	functionId: FunctionId;
	/** Instruction offset within the function, matching `extra.address`. */
	address: number;
	kind:
		| 'CreateFunctionEnvironment'
		| 'CreateTopLevelEnvironment'
		| 'CreateEnvironment';
}

/** A creation site persisted as part of the bytecode-derived plan. */
export interface EnvironmentCreationSite extends EnvironmentSiteId {}

export type EnvironmentCreationKind = EnvironmentCreationSite['kind'];

function isEnvironmentCreationKind(
	instruction: string,
): instruction is EnvironmentCreationKind {
	return instruction === 'CreateFunctionEnvironment' ||
		instruction === 'CreateTopLevelEnvironment' ||
		instruction === 'CreateEnvironment';
}

/** The key a site is identified by everywhere downstream. */
export function environmentCreationSiteKey(
	functionId: FunctionId,
	kind: string,
	address: number,
): string {
	return `${functionId}:${kind}:0x${address.toString(16)}`;
}

/** The structured identity used by alias and environment-slot provenance. */
export function environmentSiteKey(site: EnvironmentSiteId): string {
	return environmentCreationSiteKey(
		site.functionId,
		site.kind,
		site.address,
	);
}

export interface BytecodeDerivedPlan {
	/** For each function, its unique referencing parent, or null if ambiguous. */
	soleFunctionParents: Map<FunctionId, FunctionId | null>;
	/** Functions referenced more than once from a single parent. */
	nonSoleFunctionReferences: Set<FunctionId>;
	/** Which functions each function creates a closure over, in order. */
	closureReferences: Map<FunctionId, FunctionId[]>;
	/** Functions that create an environment chain entry. */
	environmentCreators: Set<FunctionId>;
	/** Every environment creation site, per function, in address order. */
	environmentCreationSites: Map<FunctionId, EnvironmentCreationSite[]>;
	/** Globals named by `TryGetById` / `DeclareGlobalVar` anywhere in the file. */
	bytecodeGlobalNames: Set<string>;
	/** Encoded bytecode bytes per function id, for scheduler weighting. */
	functionBytecodeLengths: number[];
	functionCount: number;
}

/** The stored form: sets and maps as entry arrays. */
interface ColdPlanRecord {
	soleFunctionParents: [FunctionId, FunctionId | null][];
	nonSoleFunctionReferences: FunctionId[];
	closureReferences: [FunctionId, FunctionId[]][];
	environmentCreators: FunctionId[];
	environmentCreationSites: [FunctionId, EnvironmentCreationSite[]][];
	bytecodeGlobalNames: string[];
	functionBytecodeLengths: number[];
	functionCount: number;
}

const PLAN_KEY = 'plan:bytecode';

/**
 * One pass over every instruction, producing all four structures.
 *
 * Only ever called on a file that holds its functions eagerly -- it iterates
 * all of them by definition, so calling it against a paged file would page in
 * the whole bundle.
 */
export function buildBytecodeDerivedPlan(file: HBCFile): BytecodeDerivedPlan {
	const soleFunctionParents = new Map<FunctionId, FunctionId | null>();
	const nonSoleFunctionReferences = new Set<FunctionId>();
	const closureReferences = new Map<FunctionId, FunctionId[]>();
	const environmentCreators = new Set<FunctionId>();
	const environmentCreationSites = new Map<
		FunctionId,
		EnvironmentCreationSite[]
	>();
	const bytecodeGlobalNames = new Set<string>();
	const functionBytecodeLengths: number[] = [];

	for (const func of file.functions) {
		const references = new Map<FunctionId, number>();
		const targets: FunctionId[] = [];
		const creationSites: EnvironmentCreationSite[] = [];
		functionBytecodeLengths[func.id] = func.bytecodeLength ?? 0;
		let createsEnvironment = func.envSize > 0;

		for (const block of func.basicBlocks.values()) {
			for (const instruction of block.instructions) {
				if (
					'function' in instruction &&
					isFunctionRef(instruction.function)
				) {
					const functionId = instruction.function.functionId;
					references.set(
						functionId,
						(references.get(functionId) ?? 0) + 1,
					);
					targets.push(functionId);
				}

				if (isEnvironmentCreationKind(instruction.instruction)) {
					creationSites.push({
						functionId: func.id,
						address: instruction.functionLocalOffset,
						kind: instruction.instruction,
					});
				}

				if (
					!createsEnvironment &&
					(instruction.instruction ===
							'CreateFunctionEnvironment' ||
						instruction.instruction ===
							'CreateTopLevelEnvironment')
				) {
					// For v<97 `envSize` is undefined and implied by the
					// function header. A zero-slot environment is still a real
					// chain entry that `GetParentEnvironment` counts through.
					if (
						instruction.envSize === undefined ||
						instruction.envSize > 0
					) {
						createsEnvironment = true;
					}
				}

				if (instruction.instruction === 'TryGetById') {
					bytecodeGlobalNames.add(
						file.getIdentifier(
							instruction.property.stringTableIndex,
						),
					);
				} else if (instruction.instruction === 'DeclareGlobalVar') {
					bytecodeGlobalNames.add(
						file.getIdentifier(
							instruction.identifier.stringTableIndex,
						),
					);
				}
			}
		}

		if (createsEnvironment) environmentCreators.add(func.id);
		if (targets.length > 0) closureReferences.set(func.id, targets);
		if (creationSites.length > 0) {
			// Blocks are not visited in address order, so sort rather than
			// rely on the walk: the ordering is what assigns namespace
			// indices, and it must not depend on traversal.
			environmentCreationSites.set(
				func.id,
				creationSites.toSorted((left, right) =>
					left.address - right.address
				),
			);
		}

		for (const [functionId, count] of references) {
			if (count !== 1) {
				nonSoleFunctionReferences.add(functionId);
			} else if (!soleFunctionParents.has(functionId)) {
				soleFunctionParents.set(functionId, func.id);
			} else if (soleFunctionParents.get(functionId) !== func.id) {
				soleFunctionParents.set(functionId, null);
			}
		}
	}

	return {
		soleFunctionParents,
		nonSoleFunctionReferences,
		closureReferences,
		environmentCreators,
		environmentCreationSites,
		bytecodeGlobalNames,
		functionBytecodeLengths,
		functionCount: file.functions.length,
	};
}

export async function writeColdPlan(
	store: ColdStore,
	plan: BytecodeDerivedPlan,
): Promise<void> {
	const record: ColdPlanRecord = {
		soleFunctionParents: [...plan.soleFunctionParents],
		nonSoleFunctionReferences: [...plan.nonSoleFunctionReferences],
		closureReferences: [...plan.closureReferences],
		environmentCreators: [...plan.environmentCreators],
		environmentCreationSites: [...plan.environmentCreationSites],
		bytecodeGlobalNames: [...plan.bytecodeGlobalNames],
		functionBytecodeLengths: plan.functionBytecodeLengths,
		functionCount: plan.functionCount,
	};
	await store.plan.put(PLAN_KEY, record);
}

export function readColdPlan(store: ColdStore): BytecodeDerivedPlan {
	const record = store.plan.get(PLAN_KEY) as ColdPlanRecord | undefined;
	if (!record) {
		throw new Error(
			`Cold store at ${store.path} has no bytecode plan; ` +
				'the plan phase did not complete',
		);
	}
	return {
		soleFunctionParents: new Map(record.soleFunctionParents),
		nonSoleFunctionReferences: new Set(record.nonSoleFunctionReferences),
		closureReferences: new Map(record.closureReferences),
		environmentCreators: new Set(record.environmentCreators),
		environmentCreationSites: new Map(
			record.environmentCreationSites ?? [],
		),
		bytecodeGlobalNames: new Set(record.bytecodeGlobalNames),
		functionBytecodeLengths: record.functionBytecodeLengths ?? [],
		functionCount: record.functionCount,
	};
}
