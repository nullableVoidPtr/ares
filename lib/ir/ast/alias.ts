/**
 * Storage locations, named by provenance rather than by their emitted text.
 *
 * Several passes need to answer the same two questions -- which storage
 * location does this expression denote, and can that location change between
 * two program points -- and each grew its own answer. `resolveEnvToEnvironment`
 * walks the operand structurally, `assignedEnvironmentLookupForUse` asks Babel
 * for bindings, `referencesCrossAssignmentToName` compares identifier text, and
 * the lowered generator keeps five alias maps keyed on handle names. Only
 * `chainSharedRegisterAssignmentsInBody` is keyed on provenance, via
 * `extra.sourceRegister`.
 *
 * Parameters are where the textual approach has spread furthest, and where it
 * is least accurate. `IRFunction.getParam` spells parameter *i* as
 * `_param_<fn>_<i-1>_` but spells parameter 0 as `this`, and `LoadParam` past
 * `paramCount` lifts to `arguments[i - 1]` instead. So the `/^_param_\d+_\d+_$/`
 * test repeated across five files matches one of three surface forms, at a
 * shifted index, and silently reports the other two as unknown values.
 *
 * This module gives those forms one identity. A node carries its location in
 * `extra.storageLocation` where lifting knew it; `locationOf` falls back to the
 * `_param_` name shape so untagged trees keep answering exactly as they did
 * before, and a location that cannot be established at all is `null`, which
 * every caller must read as "unknown", never as "no alias".
 */
import * as t from '@babel/types';
import traverse, { type Binding, type NodePath } from '@babel/traverse';
import type { FunctionId } from '../../hbc/disassembly/instruction.ts';
import {
	type EnvironmentSiteId,
	environmentSiteKey,
} from '../../coldstore/plan.ts';
import { type SSARegister, ssaRegisterEquals } from '../../ssa.ts';
import { isEnvironmentSlotName } from '../environment.ts';
import type { LiftedAST } from './mod.ts';

/**
 * Which function instance a register or parameter belongs to.
 *
 * No clone identity: a cloned function is given a synthetic id beyond
 * `file.functions.length` (see `localEnvironmentForCreate` in `lib/ir/lift.ts`),
 * so two clones of one function already differ here and in their emitted
 * `_param_<fn>_<i>_` names.
 */
export interface BindingOwnerId {
	functionId: FunctionId;
}

/**
 * A parameter by provenance.
 *
 * `index` is the Hermes `LoadParam` index, before the shift `getParam` applies
 * when spelling parameter *i* as `_param_<fn>_<i-1>_`. Keeping the unshifted
 * index means `form` and `index` stay independent: index 0 is always `this`,
 * whatever it is spelled as.
 */
export interface ParameterId {
	index: number;
	form: 'this' | 'named' | 'overflow';
}

/** A location that can be read and written. */
export type StorageLocation =
	| { kind: 'register'; owner: BindingOwnerId; register: SSARegister }
	| { kind: 'parameter'; owner: BindingOwnerId; parameter: ParameterId }
	/**
	 * `arguments` itself. Aliases every overflow parameter of its owner in
	 * both directions, so a write to either is a write to the other.
	 */
	| { kind: 'arguments-object'; owner: BindingOwnerId }
	| { kind: 'environment-handle'; environment: EnvironmentSiteId }
	/**
	 * An environment slot, keyed by its creation site rather than by the
	 * `_env_*` spelling. Nothing stamps these yet; the variant exists so
	 * `locationOf` can answer for them once environment tagging lands, and so
	 * that until then it answers `null` rather than guessing from the name.
	 */
	| {
		kind: 'environment-slot';
		environment: EnvironmentSiteId;
		slot: number;
	};

const PARAM_NAME = /^_param_(\d+)_(\d+)_$/;

/** A stable map key for a location. */
export function locationKey(location: StorageLocation): string {
	switch (location.kind) {
		case 'register':
			return `r:${location.owner.functionId}:` +
				`${location.register.index}_${location.register.version}`;
		case 'parameter':
			return `p:${location.owner.functionId}:` +
				`${location.parameter.form}:${location.parameter.index}`;
		case 'arguments-object':
			return `a:${location.owner.functionId}`;
		case 'environment-handle':
			return `h:${environmentSiteKey(location.environment)}`;
		case 'environment-slot':
			return `e:${
				environmentSiteKey(location.environment)
			}:${location.slot}`;
	}
}

export function sameLocation(
	left: StorageLocation | null | undefined,
	right: StorageLocation | null | undefined,
): boolean {
	if (!left || !right || left.kind !== right.kind) return false;
	if (left.kind === 'register' && right.kind === 'register') {
		return left.owner.functionId === right.owner.functionId &&
			ssaRegisterEquals(left.register, right.register);
	}
	return locationKey(left) === locationKey(right);
}

/**
 * Whether two locations may be the same storage at runtime.
 *
 * Distinct from `sameLocation`: `arguments` and an overflow parameter of the
 * same function are different locations that share storage, so a write to
 * either is observable through the other.
 */
export function locationsMayAlias(
	left: StorageLocation | null | undefined,
	right: StorageLocation | null | undefined,
): boolean {
	if (!left || !right) return false;
	if (sameLocation(left, right)) return true;

	const overflowOf = (
		location: StorageLocation,
	): BindingOwnerId | null =>
		location.kind === 'parameter' &&
			location.parameter.form === 'overflow'
			? location.owner
			: null;
	const argumentsOf = (location: StorageLocation): BindingOwnerId | null =>
		location.kind === 'arguments-object' ? location.owner : null;

	const overflow = overflowOf(left) ?? overflowOf(right);
	const args = argumentsOf(left) ?? argumentsOf(right);
	return overflow != null && args != null &&
		overflow.functionId === args.functionId;
}

/** Record the location a node denotes. */
export function tagStorageLocation<N extends t.Node>(
	node: N,
	location: StorageLocation,
): N {
	const lifted = node as LiftedAST<N>;
	lifted.extra = { ...lifted.extra, storageLocation: location };
	return node;
}

/** Copy a location tag onto a node that replaces a tagged one. */
export function carryStorageLocation<N extends t.Node>(
	replacement: N,
	original: t.Node | null | undefined,
): N {
	const location = storedLocation(original);
	return location ? tagStorageLocation(replacement, location) : replacement;
}

function storedLocation(
	node: t.Node | null | undefined,
): StorageLocation | null {
	if (!node) return null;
	return (node as LiftedAST<t.Node>).extra?.storageLocation ?? null;
}

/**
 * The storage location an expression denotes, or `null` for unknown.
 *
 * A stamped tag wins. Failing that, the `_param_<fn>_<i>_` name shape is read
 * as the named parameter it spells, which is what the five call sites this
 * replaces already did -- so an untagged tree answers exactly as before rather
 * than losing the parameter domain entirely.
 */
export function locationOf(
	node: t.Node | null | undefined,
): StorageLocation | null {
	const tagged = storedLocation(node);
	if (tagged) return tagged;
	if (!node) return null;

	if (t.isIdentifier(node)) {
		const extra = (node as LiftedAST<t.Identifier>).extra;
		if (
			extra?.sourceRegister != null &&
			extra.bindingOwnerFunctionId != null
		) {
			return {
				kind: 'register',
				owner: { functionId: extra.bindingOwnerFunctionId },
				register: extra.sourceRegister,
			};
		}
		const match = PARAM_NAME.exec(node.name);
		if (!match) return null;
		// The name spells parameter *i* as `<i - 1>`; undo that so the index
		// means the same thing here as in a stamped tag.
		return {
			kind: 'parameter',
			owner: { functionId: Number(match[1]) },
			parameter: { index: Number(match[2]) + 1, form: 'named' },
		};
	}

	// `this` and `arguments[k]` carry no owner in their spelling, so they are
	// recognised only from a stamped tag. Absence stays unknown.
	return null;
}

/** Whether an expression denotes a parameter, in any of its spellings. */
export function isParameterExpression(
	node: t.Node | null | undefined,
): boolean {
	return locationOf(node)?.kind === 'parameter';
}

/**
 * Whether an expression denotes a value that arrived from outside the body: a
 * parameter in any spelling, or the `arguments` object.
 *
 * `this` and a bare `arguments` identifier carry no owner in their spelling, so
 * an untagged one is recognised by form. That is the same fallback `locationOf`
 * applies to the `_param_` name shape, and between them they cover what the
 * call sites this replaces matched by hand.
 */
export function isIncomingValueExpression(
	node: t.Node | null | undefined,
): boolean {
	const kind = locationOf(node)?.kind;
	if (kind === 'parameter' || kind === 'arguments-object') return true;
	return t.isThisExpression(node) ||
		t.isIdentifier(node, { name: 'arguments' });
}

/**
 * Whether `node` syntactically writes `location` anywhere inside it.
 *
 * Deliberately *not* named `mayWriteBetween`: this sees assignment and update
 * targets and nothing else. It does not model writes through a captured
 * closure, an unknown call, a suspension, or an exception edge, so it is a
 * necessary condition for a rewrite and never a sufficient one on its own.
 */
export function writesLocationWithin(
	node: t.Node,
	location: StorageLocation,
): boolean {
	let writes = false;
	t.traverseFast(node, (child) => {
		if (writes) return t.traverseFast.skip;
		if (
			t.isAssignmentExpression(child) &&
			locationsMayAlias(locationOf(child.left), location)
		) {
			writes = true;
			return;
		}
		if (
			t.isUpdateExpression(child) &&
			locationsMayAlias(locationOf(child.argument), location)
		) {
			writes = true;
		}
	});
	return writes;
}

/**
 * Visit every identifier inside `node` that is in a value position.
 *
 * `t.traverseFast` reaches property keys and label names too, and those are
 * spellings rather than references: `obj.r5_1` and `r5_1` share a name and
 * nothing else. Counting or renaming one of those would corrupt an unrelated
 * member access, which is reachable here because obfuscated bundles do use
 * short generated-looking property names.
 */
function forEachValueIdentifier(
	node: t.Node,
	visit: (identifier: t.Identifier) => void,
): void {
	const walk = (
		current: t.Node,
		key: string | null,
		parent: t.Node | null,
	) => {
		if (t.isIdentifier(current) && !isSpellingPosition(key, parent)) {
			visit(current);
		}
		for (const childKey of t.VISITOR_KEYS[current.type] ?? []) {
			const value = (current as unknown as Record<string, unknown>)[
				childKey
			];
			if (Array.isArray(value)) {
				for (const child of value) {
					if (t.isNode(child)) walk(child, childKey, current);
				}
			} else if (t.isNode(value)) walk(value, childKey, current);
		}
	};
	walk(node, null, null);
}

function isSpellingPosition(
	key: string | null,
	parent: t.Node | null,
): boolean {
	if (!parent || !key) return false;
	if (key === 'property') {
		// `new.target` spells both halves as identifiers too.
		if (t.isMetaProperty(parent)) return true;
		return (t.isMemberExpression(parent) ||
			t.isOptionalMemberExpression(parent)) && !parent.computed;
	}
	if (key === 'meta') return t.isMetaProperty(parent);
	if (key === 'key') {
		return (t.isObjectProperty(parent) || t.isObjectMethod(parent) ||
			t.isClassProperty(parent) || t.isClassMethod(parent) ||
			t.isClassPrivateProperty(parent) ||
			t.isClassPrivateMethod(parent)) &&
			!(parent as { computed?: boolean }).computed;
	}
	if (key === 'label') {
		return t.isLabeledStatement(parent) || t.isBreakStatement(parent) ||
			t.isContinueStatement(parent);
	}
	return false;
}

/** How many expressions inside `node` denote `location`. */
export function countLocationReferences(
	node: t.Node,
	location: StorageLocation,
): number {
	let count = 0;
	// Member expressions can themselves denote a location -- `arguments[k]` --
	// so those are counted directly rather than through their identifiers.
	t.traverseFast(node, (child) => {
		if (
			t.isMemberExpression(child) &&
			sameLocation(locationOf(child), location)
		) count++;
	});
	forEachValueIdentifier(node, (identifier) => {
		if (sameLocation(locationOf(identifier), location)) count++;
	});
	return count;
}

/**
 * Whether a name was minted by lifting rather than recovered from source.
 *
 * Covers `r<reg>_<version>`, `_env_<fn>[_x<n>]_<slot>`, and the materialized
 * lowered-generator slot form `r<fn>_<envName>_<slot>`. A spelling predicate,
 * never an identity test -- it answers "is this name safe to rewrite away",
 * not "which storage does this denote".
 */
export function isGeneratedLocalName(name: string): boolean {
	return /^r\d+_[A-Za-z0-9_$]+$/.test(name) || isEnvironmentSlotName(name);
}

function isGeneratedRestName(name: string): boolean {
	return /^_rest_\d+_\d+_$/.test(name);
}

interface ParameterAliasCandidate {
	statements: t.Statement[];
	index: number;
	local: string;
	parameter: t.Identifier;
	location: StorageLocation;
}

/**
 * Fold `let <local> = <parameter>;` into the parameter itself.
 *
 * Hermes copies a captured parameter into an environment slot in the prologue,
 * and recovery materializes that slot as a local. The result is a second
 * binding for storage that already has one:
 *
 * ```js
 * function* useArgs(_param_3_0_, _param_3_1_) {
 *   let r26_r7_11_0 = _param_3_0_;
 *   yield r26_r7_11_0;
 *   r26_r7_11_0 += 1;
 * }
 * ```
 *
 * `cleanupEnvironmentBody` already performs this fold for slots that kept an
 * `_env_*` spelling, through `replaceEnvAliasIdentifiers`. A materialized slot
 * is spelled `r<fn>_<envName>_<slot>` instead, so the name test there never
 * sees it -- the same rewrite, missed for a different spelling of the same
 * thing.
 *
 * The parameter must have exactly one reference, the initializer, or a read of
 * it elsewhere would observe writes made through the local. Nothing may shadow
 * either name in a nested function, and `this` and `arguments` are excluded:
 * a nested non-arrow function rebinds both, so folding one across a function
 * boundary changes what it denotes.
 *
 * `regions` must include every node that can reference either name, `body`
 * among them.
 */
export function coalesceParameterAliases(
	body: t.Statement[],
	regions: readonly t.Node[],
): string[] {
	const candidates: ParameterAliasCandidate[] = [];
	for (let index = 0; index < body.length; index++) {
		const statement = body[index];
		if (
			!t.isVariableDeclaration(statement) ||
			statement.declarations.length !== 1
		) continue;
		const [declarator] = statement.declarations;
		if (
			!t.isIdentifier(declarator.id) ||
			!isGeneratedLocalName(declarator.id.name) ||
			!t.isIdentifier(declarator.init)
		) continue;
		const location = locationOf(declarator.init);
		if (
			location?.kind !== 'parameter' ||
			location.parameter.form !== 'named'
		) continue;
		candidates.push({
			statements: body,
			index,
			local: declarator.id.name,
			parameter: declarator.init,
			location,
		});
	}
	if (candidates.length === 0) return [];

	const coalesced: string[] = [];
	const claimed = new Set<string>();
	const removed = new Set<t.Statement>();
	for (const candidate of candidates) {
		const key = locationKey(candidate.location);
		// One local per parameter: a second would alias the first's storage.
		if (claimed.has(key)) continue;
		let references = 0;
		let declarations = 0;
		let shadowed = false;
		for (const region of regions) {
			references += countLocationReferences(region, candidate.location);
			declarations += countLocalDeclarations(region, candidate.local);
			shadowed ||= shadowsInNestedFunction(
				region,
				candidate.local,
				candidate.parameter.name,
			);
		}
		if (references !== 1 || declarations !== 1 || shadowed) continue;

		claimed.add(key);
		coalesced.push(candidate.local);
		removed.add(candidate.statements[candidate.index]);
		for (const region of regions) {
			renameIdentifiers(region, candidate.local, candidate.parameter);
		}
	}

	if (removed.size > 0) {
		// Rebuilt in place: callers hold this array, so it must keep its
		// identity rather than be replaced.
		const kept = body.filter((statement) => !removed.has(statement));
		body.length = 0;
		body.push(...kept);
	}
	return coalesced;
}

function destructurablePropertyKey(
	property: t.MemberExpression['property'],
	computed: boolean,
): string | null {
	if (computed) {
		if (t.isStringLiteral(property) || t.isNumericLiteral(property)) {
			return String(property.value);
		}
		return null;
	}
	if (t.isIdentifier(property)) return property.name;
	if (t.isStringLiteral(property) || t.isNumericLiteral(property)) {
		return String(property.value);
	}
	return null;
}

function objectPropertyAliasCapture(
	statement: NodePath<t.Node | null>,
	sourceName: string,
): {
	property: t.Expression | t.PrivateName;
	computed: boolean;
	binding: t.Identifier;
	objectRef: NodePath<t.Identifier>;
	remove: NodePath;
} | null {
	if (statement.isVariableDeclaration({ kind: 'const' })) {
		const declarations = statement.get('declarations');
		if (declarations.length !== 1) return null;
		const id = declarations[0].get('id');
		const init = declarations[0].get('init');
		if (!id.isIdentifier() || !init.isMemberExpression()) return null;
		const object = init.get('object');
		if (!object.isIdentifier({ name: sourceName })) return null;
		const property = init.get('property').node;
		if (destructurablePropertyKey(property, init.node.computed) == null) {
			return null;
		}
		return {
			property,
			computed: init.node.computed,
			binding: id.node,
			objectRef: object,
			remove: statement,
		};
	}
	if (!statement.isExpressionStatement()) return null;
	const expression = statement.get('expression');
	if (!expression.isMemberExpression()) return null;
	const object = expression.get('object');
	if (!object.isIdentifier({ name: sourceName })) return null;
	const property = expression.get('property').node;
	const key = destructurablePropertyKey(property, expression.node.computed);
	if (key == null) return null;
	const binding = t.identifier(sourceName);
	return {
		property,
		computed: expression.node.computed,
		binding,
		objectRef: object,
		remove: statement,
	};
}

export function destructureGeneratedObjectPropertyAliases(
	file: t.File,
): number {
	let changed = 0;
	traverse(file, {
		VariableDeclaration(path) {
			if (!path.isVariableDeclaration({ kind: 'const' })) return;
			const declarations = path.get('declarations');
			if (declarations.length !== 1) return;
			const declarator = declarations[0];
			const id = declarator.get('id');
			const init = declarator.get('init');
			if (
				!id.isIdentifier() || !/^r\d+_\d+$/.test(id.node.name) ||
				!init.node || !t.isExpression(init.node)
			) return;
			const binding = path.scope.getBinding(id.node.name);
			if (
				!binding || binding.path.node !== declarator.node ||
				!binding.constant || binding.constantViolations.length > 0
			) return;
			const captures: Array<{
				property: t.Expression | t.PrivateName;
				computed: boolean;
				binding: t.Identifier;
				objectRef: NodePath<t.Identifier>;
				remove: NodePath;
			}> = [];
			const propertyKeys = new Set<string>();
			const bindingNames = new Set<string>();
			let current: NodePath<t.Node | null> = path;
			while (true) {
				current = current.getNextSibling();
				if (!current.node) break;
				const capture = objectPropertyAliasCapture(
					current,
					id.node.name,
				);
				if (!capture) break;
				const key = destructurablePropertyKey(
					capture.property,
					capture.computed,
				);
				if (
					key == null || propertyKeys.has(key) ||
					bindingNames.has(capture.binding.name)
				) return;
				propertyKeys.add(key);
				bindingNames.add(capture.binding.name);
				captures.push(capture);
			}
			if (captures.length === 0) return;
			const capturedRefs = new Set(
				captures.map((capture) => capture.objectRef),
			);
			if (
				(binding.referencePaths as NodePath<t.Identifier>[]).some(
					(reference) => !capturedRefs.has(reference),
				)
			) return;
			declarator.replaceWith(t.variableDeclarator(
				t.objectPattern(captures.map((capture) =>
					t.objectProperty(
						t.cloneNode(capture.property, true),
						t.cloneNode(capture.binding, true),
						capture.computed,
						false,
					)
				)),
				init.node,
			));
			for (const capture of captures) capture.remove.remove();
			changed++;
		},
	});
	if (changed > 0) traverse.cache.clear();
	return changed;
}

/**
 * Whether `write` is guaranteed to have executed before `use` evaluates.
 *
 * Both are walked up to the statements that share one statement list, and the
 * write's statement must come first. A conditional write still counts: it
 * either ran before `use` or not at all, and neither can put it *between* the
 * alias and its references. A closure reading the location counts as its
 * creation site, which is what makes a slot written in a module factory
 * readable from the closures that factory installs.
 */
function writePrecedesUse(write: NodePath, use: NodePath): boolean {
	const writeAncestors = new Map<t.Node, NodePath>();
	for (
		let path: NodePath | null = write;
		path?.parentPath;
		path = path.parentPath
	) writeAncestors.set(path.parentPath.node, path);

	for (
		let path: NodePath | null = use;
		path?.parentPath;
		path = path.parentPath
	) {
		const sibling = writeAncestors.get(path.parentPath.node);
		if (!sibling || sibling.node === path.node) continue;
		return sibling.listKey != null &&
			sibling.listKey === path.listKey &&
			typeof sibling.key === 'number' &&
			typeof path.key === 'number' &&
			sibling.key < path.key;
	}
	return false;
}

export interface StableStorageAliasResult {
	analysed: number;
	coalesced: number;
	registerAliasesCoalesced: number;
	environmentSlotAliasesCoalesced: number;
	blockedByWrite: number;
	blockedByVisibility: number;
	blockedByLocalMutation: number;
}

function coalesceChainedRegisterEnvironmentSinks(
	file: t.File,
	result: StableStorageAliasResult,
): void {
	const candidates: Array<{
		register: Binding;
		registerDeclaration: NodePath<t.VariableDeclaration>;
		environment: Binding;
		environmentDeclarator: NodePath<t.VariableDeclarator>;
		environmentId: t.Identifier;
		value: t.Expression;
	}> = [];
	traverse(file, {
		VariableDeclarator(path) {
			if (
				!t.isIdentifier(path.node.id) ||
				!/^r\d+_\d+$/.test(path.node.id.name) ||
				!path.parentPath.isVariableDeclaration({ kind: 'const' }) ||
				path.parentPath.node.declarations.length !== 1
			) return;
			const init = path.get('init');
			if (!init.isAssignmentExpression({ operator: '=' })) return;
			const environmentId = init.get('left');
			const value = init.get('right');
			if (!environmentId.isIdentifier() || !value.isExpression()) return;
			const environmentLocation = locationOf(environmentId.node);
			if (environmentLocation?.kind !== 'environment-slot') return;
			result.analysed++;

			const register = path.scope.getBinding(path.node.id.name);
			const environment = environmentId.scope.getBinding(
				environmentId.node.name,
			);
			if (
				!register || register.path.node !== path.node ||
				!register.constant ||
				register.constantViolations.length > 0
			) {
				result.blockedByLocalMutation++;
				return;
			}
			if (
				!environment ||
				!sameLocation(
					locationOf(environment.identifier),
					environmentLocation,
				) ||
				!environment.path.isVariableDeclarator() ||
				environment.path.node.init != null ||
				!environment.path.parentPath.isVariableDeclaration({
					kind: 'var',
				})
			) {
				result.blockedByVisibility++;
				return;
			}
			if (
				environment.constantViolations.length !== 1 ||
				environment.constantViolations[0].node !== init.node
			) {
				result.blockedByWrite++;
				return;
			}
			const registerReferences = register.referencePaths as NodePath<
				t.Identifier
			>[];
			if (
				registerReferences.some((reference) =>
					reference.scope.getBinding(environmentId.node.name) !==
						environment ||
					!writePrecedesUse(path.parentPath, reference)
				)
			) {
				result.blockedByVisibility++;
				return;
			}
			candidates.push({
				register,
				registerDeclaration: path.parentPath,
				environment,
				environmentDeclarator: environment.path,
				environmentId: environmentId.node,
				value: value.node,
			});
		},
	});

	for (const candidate of candidates) {
		if (
			!candidate.registerDeclaration.node ||
			!candidate.environmentDeclarator.node
		) continue;
		const replacement = t.cloneNode(candidate.environmentId, true);
		for (
			const reference of candidate.register
				.referencePaths as NodePath<t.Identifier>[]
		) {
			if (reference.node) {
				reference.replaceWith(t.cloneNode(replacement, true));
			}
		}
		const environmentDeclaration =
			candidate.environmentDeclarator.parentPath;
		candidate.environmentDeclarator.remove();
		if (
			environmentDeclaration.isVariableDeclaration() &&
			environmentDeclaration.node.declarations.length === 0
		) environmentDeclaration.remove();
		candidate.registerDeclaration.replaceWith(
			t.variableDeclaration('var', [
				t.variableDeclarator(
					replacement,
					t.cloneNode(candidate.value, true),
				),
			]),
		);
		result.coalesced++;
		result.environmentSlotAliasesCoalesced++;
	}
	if (candidates.length > 0) traverse.cache.clear();
}

/**
 * Remove generated snapshot aliases of stable parameters/environment slots.
 *
 * Composition often turns
 *
 *     const r7_1 = %expectEnvironment(parent)[4];
 *
 * into `const r7_1 = _env_parent_4`. The IR inliner could not move the
 * intrinsic, but after composition both nodes carry storage provenance. When
 * the source location has no writes anywhere in the composed tree, the local
 * and source are observably equal for the local's entire lifetime and the
 * generated alias can be removed. A write blocks the rewrite globally: that is
 * conservative, but avoids pretending a captured snapshot is a live binding.
 *
 * Register-to-environment sinks canonicalize in the opposite textual
 * direction. The environment cell is the durable captured storage, so both a
 * dominating `const _env = rN` and the chained `const rN = _env = value`
 * promote the register's defining binding to `_env`. This applies equally to
 * ordinary register declarations and register-backed destructured parameter
 * bindings.
 */
export function coalesceStableStorageAliases(
	file: t.File,
): StableStorageAliasResult {
	const result: StableStorageAliasResult = {
		analysed: 0,
		coalesced: 0,
		registerAliasesCoalesced: 0,
		environmentSlotAliasesCoalesced: 0,
		blockedByWrite: 0,
		blockedByVisibility: 0,
		blockedByLocalMutation: 0,
	};
	coalesceChainedRegisterEnvironmentSinks(file, result);
	// Writes are collected as paths, not just as a set of locations, because a
	// location's *own initialization* is a write and blocking on it would rule
	// out every environment slot: a slot is always assigned once before its
	// closures read it. What matters is whether a write can land between an
	// alias and its uses, and that needs to know where the write is.
	const writesByLocation = new Map<string, NodePath[]>();
	const externalEnvironmentWrites = new Set<string>();
	const noteWrite = (path: NodePath, target: t.Node) => {
		const location = locationOf(target);
		if (!location) return;
		const key = locationKey(location);
		const writes = writesByLocation.get(key) ?? [];
		writes.push(path);
		writesByLocation.set(key, writes);
	};
	traverse(file, {
		AssignmentExpression(path) {
			noteWrite(path, path.node.left);
			if (
				t.isIdentifier(path.node.left) &&
				isEnvironmentSlotName(path.node.left.name)
			) {
				externalEnvironmentWrites.add(path.node.left.name);
			}
		},
		UpdateExpression(path) {
			noteWrite(path, path.node.argument);
			if (
				t.isIdentifier(path.node.argument) &&
				isEnvironmentSlotName(path.node.argument.name)
			) {
				externalEnvironmentWrites.add(path.node.argument.name);
			}
		},
	});

	const candidates: Array<{
		path: NodePath<t.VariableDeclarator>;
		declaration: NodePath<t.VariableDeclaration>;
		binding: Binding;
		kind: 'register' | 'environment-slot';
		source: t.Identifier;
		sourceBinding: Binding;
		references: NodePath<t.Identifier>[];
	}> = [];
	traverse(file, {
		VariableDeclarator(path) {
			if (
				!t.isIdentifier(path.node.id) ||
				!t.isIdentifier(path.node.init) ||
				!path.parentPath.isVariableDeclaration()
			) return;
			const localLocation = locationOf(path.node.id);
			const sourceLocation = locationOf(path.node.init);
			if (sourceLocation == null) return;
			const kind = /^r\d+_\d+$/.test(path.node.id.name)
				? 'register' as const
				: localLocation?.kind === 'environment-slot' &&
						(sourceLocation?.kind === 'parameter' ||
							sourceLocation?.kind === 'register')
				? 'environment-slot' as const
				: null;
			if (kind == null) return;
			if (
				kind === 'register' &&
				sourceLocation?.kind !== 'parameter' &&
				sourceLocation?.kind !== 'environment-slot'
			) return;
			result.analysed++;
			const binding = path.scope.getBinding(path.node.id.name);
			if (
				!binding || binding.path.node !== path.node ||
				!binding.constant || binding.constantViolations.length > 0
			) {
				result.blockedByLocalMutation++;
				return;
			}
			const writes = writesByLocation.get(locationKey(sourceLocation)) ??
				[];
			// One write that already happened cannot land between the alias and
			// its uses, so the two stay observably equal for the alias's whole
			// lifetime. More than one write, or one that does not precede the
			// alias, and that guarantee is gone.
			if (
				writes.length > 1 ||
				(writes.length === 1 && !writePrecedesUse(writes[0], path))
			) {
				result.blockedByWrite++;
				return;
			}
			const sourceBinding = path.scope.getBinding(path.node.init.name);
			if (
				!sourceBinding ||
				// The single initializing write shows up here as the source
				// binding's only constant violation; anything beyond that is a
				// mutation this rewrite cannot see through.
				sourceBinding.constantViolations.length > writes.length ||
				!sameLocation(
					locationOf(sourceBinding.identifier),
					sourceLocation,
				)
			) {
				result.blockedByVisibility++;
				return;
			}
			candidates.push({
				path,
				declaration: path.parentPath,
				binding,
				kind,
				source: path.node.init,
				sourceBinding,
				references: binding.referencePaths as NodePath<t.Identifier>[],
			});
		},
	});

	const registerEnvironmentSinks = new Set(
		candidates.filter((candidate) =>
			candidate.kind === 'environment-slot' &&
			locationOf(candidate.source)?.kind === 'register'
		),
	);
	const sinkCountBySource = new Map<Binding, number>();
	for (const candidate of registerEnvironmentSinks) {
		sinkCountBySource.set(
			candidate.sourceBinding,
			(sinkCountBySource.get(candidate.sourceBinding) ?? 0) + 1,
		);
	}
	const multiplyCapturedSinks = new Set(
		[...registerEnvironmentSinks].filter((candidate) =>
			(sinkCountBySource.get(candidate.sourceBinding) ?? 0) > 1
		),
	);
	for (const candidate of multiplyCapturedSinks) {
		registerEnvironmentSinks.delete(candidate);
		result.blockedByVisibility++;
	}
	const candidateByBinding = new Map<Binding, typeof candidates[number]>();
	for (const candidate of candidates) {
		if (multiplyCapturedSinks.has(candidate)) continue;
		candidateByBinding.set(candidate.binding, candidate);
	}
	const finalSource = (candidate: typeof candidates[number]) => {
		let source = candidate.source;
		let binding = candidate.sourceBinding;
		const seen = new Set<Binding>([candidate.binding]);
		while (!seen.has(binding)) {
			seen.add(binding);
			const next = candidateByBinding.get(binding);
			if (!next) break;
			if (registerEnvironmentSinks.has(next)) {
				source = next.path.node.id as t.Identifier;
				binding = next.binding;
				break;
			}
			source = next.source;
			binding = next.sourceBinding;
		}
		return { source, binding };
	};
	const replacements = new Map<
		typeof candidates[number],
		{ source: t.Identifier; binding: Binding }
	>();
	for (const candidate of candidates) {
		if (multiplyCapturedSinks.has(candidate)) continue;
		if (registerEnvironmentSinks.has(candidate)) {
			const localName = (candidate.path.node.id as t.Identifier).name;
			const sourceReferences = candidate.sourceBinding
				.referencePaths as NodePath<t.Identifier>[];
			if (
				sourceReferences.some((reference) =>
					reference.node !== candidate.source &&
					(reference.scope.getBinding(localName) !==
							candidate.binding ||
						!writePrecedesUse(candidate.declaration, reference))
				)
			) {
				registerEnvironmentSinks.delete(candidate);
				result.blockedByVisibility++;
				continue;
			}
			continue;
		}
		const replacement = finalSource(candidate);
		if (
			candidate.references.some((reference) =>
				reference.scope.getBinding(replacement.source.name) !==
					replacement.binding
			)
		) {
			result.blockedByVisibility++;
			continue;
		}
		replacements.set(candidate, replacement);
	}

	// Slot-to-parameter aliases first: their reference set may include a
	// register alias initializer. The register's replacement was resolved to the
	// transitive source above, so removing both never reintroduces the slot name.
	for (
		const candidate of candidates.toSorted((left, right) =>
			left.kind === right.kind
				? 0
				: left.kind === 'environment-slot'
				? -1
				: 1
		)
	) {
		if (!candidate.path.node) continue;
		if (multiplyCapturedSinks.has(candidate)) continue;
		if (registerEnvironmentSinks.has(candidate)) {
			const local = t.cloneNode(
				candidate.path.node.id as t.Identifier,
				true,
			);
			for (
				const reference of candidate.sourceBinding
					.referencePaths as NodePath<t.Identifier>[]
			) {
				if (!reference.node) continue;
				reference.replaceWith(t.cloneNode(local, true));
			}
			candidate.sourceBinding.identifier.name = local.name;
			const localLocation = locationOf(local);
			if (localLocation) {
				tagStorageLocation(
					candidate.sourceBinding.identifier,
					localLocation,
				);
			}
			candidate.path.remove();
			if (
				candidate.declaration.node &&
				candidate.declaration.node.declarations.length === 0
			) candidate.declaration.remove();
			result.coalesced++;
			result.environmentSlotAliasesCoalesced++;
			continue;
		}
		const replacement = replacements.get(candidate);
		if (!replacement) continue;
		for (const reference of candidate.references) {
			if (!reference.node) continue;
			reference.replaceWith(t.cloneNode(replacement.source, true));
		}
		candidate.path.remove();
		if (
			candidate.declaration.node &&
			candidate.declaration.node.declarations.length === 0
		) candidate.declaration.remove();
		result.coalesced++;
		if (candidate.kind === 'register') result.registerAliasesCoalesced++;
		else result.environmentSlotAliasesCoalesced++;
	}

	traverse(file, {
		VariableDeclarator(path) {
			if (
				!t.isIdentifier(path.node.id) ||
				!t.isIdentifier(path.node.init) ||
				!path.parentPath.isVariableDeclaration({ kind: 'const' }) ||
				!/^r\d+_\d+$/.test(path.node.id.name) ||
				(!isEnvironmentSlotName(path.node.init.name) &&
					!isGeneratedRestName(path.node.init.name)) ||
				(isEnvironmentSlotName(path.node.init.name) &&
					(path.scope.getBinding(path.node.init.name) ||
						externalEnvironmentWrites.has(path.node.init.name)))
			) return;
			result.analysed++;
			const binding = path.scope.getBinding(path.node.id.name);
			if (
				!binding || binding.path.node !== path.node ||
				!binding.constant || binding.constantViolations.length > 0
			) {
				result.blockedByLocalMutation++;
				return;
			}
			const sourceName = path.node.init.name;
			const sourceBinding = path.scope.getBinding(sourceName);
			if (
				isGeneratedRestName(sourceName) &&
				(!sourceBinding || !sourceBinding.constant ||
					sourceBinding.constantViolations.length > 0)
			) {
				result.blockedByVisibility++;
				return;
			}
			if (
				binding.referencePaths.some((reference) =>
					reference.scope.getBinding(sourceName) !== sourceBinding
				)
			) {
				result.blockedByVisibility++;
				return;
			}
			const source = t.cloneNode(path.node.init, true);
			for (const reference of binding.referencePaths) {
				if (!reference.node) continue;
				reference.replaceWith(t.cloneNode(source, true));
			}
			path.remove();
			if (
				path.parentPath.node &&
				path.parentPath.isVariableDeclaration() &&
				path.parentPath.node.declarations.length === 0
			) {
				path.parentPath.remove();
			}
			result.coalesced++;
			result.registerAliasesCoalesced++;
		},
	});

	traverse.cache.clear();
	return result;
}

function countLocalDeclarations(node: t.Node, name: string): number {
	let count = 0;
	t.traverseFast(node, (child) => {
		if (!t.isVariableDeclarator(child)) return;
		if (Object.hasOwn(t.getBindingIdentifiers(child.id), name)) count++;
	});
	return count;
}

function shadowsInNestedFunction(
	node: t.Node,
	local: string,
	parameter: string,
): boolean {
	let shadows = false;
	const visit = (current: t.Node, inFunction: boolean) => {
		if (shadows) return;
		const nested = inFunction ||
			(current !== node && t.isFunction(current));
		if (nested && t.isFunction(current)) {
			for (const param of current.params) {
				const names = Object.keys(t.getBindingIdentifiers(param));
				if (names.includes(local) || names.includes(parameter)) {
					shadows = true;
					return;
				}
			}
		}
		for (const key of t.VISITOR_KEYS[current.type] ?? []) {
			const value = (current as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const child of value) {
					if (t.isNode(child)) visit(child, nested);
				}
			} else if (t.isNode(value)) visit(value, nested);
			if (shadows) return;
		}
	};
	visit(node, false);
	return shadows;
}

function renameIdentifiers(
	node: t.Node,
	from: string,
	to: t.Identifier,
): void {
	const location = locationOf(to);
	forEachValueIdentifier(node, (identifier) => {
		if (identifier.name !== from) return;
		identifier.name = to.name;
		if (location) tagStorageLocation(identifier, location);
	});
}
