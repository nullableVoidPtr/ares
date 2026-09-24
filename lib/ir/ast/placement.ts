/**
 * Where a generated binding must be declared for every use to see it.
 *
 * Generated-register cleanup historically accumulated shape-specific repairs
 * for catch visibility, colliding `var` patterns, duplicate declarations,
 * composition, recovered generators, and sibling scopes. Those passes disagreed
 * about scope because each ran where its triggering shape happened to appear.
 *
 * This is the authoritative function-tree placement stage: for each generated
 * binding, it computes the lowest statement list containing every definition
 * and every use, then rewrites declarations and assignments to establish that
 * binding once.
 */
import * as t from '@babel/types';
import { locationOf } from './alias.ts';

export type BindingPlacementReason =
	| 'cross-block'
	| 'out-of-scope-use'
	| 'same-scope-duplicate'
	| 'var-lexical-collision'
	| 'assignment-without-declaration'
	| 'pattern-closure'
	| 'unwritten-ancestor-declaration'
	| 'declaration-closure';

/**
 * A lexical scope, in the only sense this pass needs: a statement list a
 * declaration can be placed in.
 *
 * Loop headers and switch discriminants are *not* scopes here. A binding whose
 * lowest common ancestor is one of those is projected outward to the nearest
 * enclosing statement list, because that is where a declaration can go.
 */
interface PlacementScope {
	id: number;
	parent: PlacementScope | null;
	/** Depth from the function root, for lowest-common-ancestor walks. */
	depth: number;
	/** The statement list a declaration placed here would join. */
	body: t.Statement[];
	/** True for a function body or Program: a `var` stops here. */
	isFunctionScope: boolean;
}

interface BindingRecord {
	name: string;
	/** Scopes holding a declaration of this name. */
	declarations: PlacementScope[];
	/** Declaration scopes whose declarator has no initializer. */
	uninitializedDeclarations: PlacementScope[];
	/** Scopes holding a read, write or update of this name. */
	uses: PlacementScope[];
	/** True when any declaration is a `var`. */
	hasVarDeclaration: boolean;
	/** True when any declaration is `let` or `const`. */
	hasLexicalDeclaration: boolean;
	/** True when any declaration binds it inside a destructuring pattern. */
	inPattern: boolean;
	/**
	 * Names bound by the same destructuring declarator.
	 *
	 * A pattern is rewritten as one assignment, so its members share a fate:
	 * promoting one and leaving another declared would need the declarator to
	 * be both a declaration and an assignment at once.
	 */
	patternSiblings: Set<string>;
	/** Generated names sharing an indivisible loop-header declaration. */
	declarationSiblings: Set<string>;
	/** This name occurs in an indivisible loop-header declaration. */
	inIndivisibleDeclaration: boolean;
	/** The binding shares a pattern/header with a non-generated binding. */
	unsafeMixedSyntacticGroup: boolean;
	/** True when some occurrence is an assignment or update target. */
	assigned: boolean;
	reasons: Set<BindingPlacementReason>;
}

export interface BindingPlacement {
	name: string;
	/** The scope the single declaration belongs in. */
	scope: t.Statement[];
	reasons: BindingPlacementReason[];
}

export interface BindingPlacementResult {
	/** Bindings that must move, keyed by name. */
	placed: Map<string, BindingPlacement>;
	/** Bindings already correctly placed; nothing to do. */
	localized: Set<string>;
	/**
	 * Names used with no declaration and no assignment that could define one.
	 *
	 * Never repaired: a reference with no reaching definition is a definition
	 * the CFG lost, and inventing a declaration would turn a rejected candidate
	 * into wrong output. See the lost-definition rule in `BINDING-TODO.md`.
	 */
	unresolved: Set<string>;
}

export interface BindingPlacementTreeEntry {
	/** Stable preorder function ordinal; root is always `root`. */
	path: string;
	root: t.Program | t.BlockStatement;
	result: BindingPlacementResult;
}

export interface BindingPlacementTreeResult {
	entries: BindingPlacementTreeEntry[];
	placed: number;
	localized: number;
	unresolved: number;
}

// Environment slots deliberately stay out of this pass until they carry a
// structured (creation-site, slot) identity. Two distinct runtime environments
// can have the same emitted `_env_*` spelling, so text is not a binding key.
const isGeneratedBindingName = (name: string) => /^r\d+_\d+$/.test(name);

/**
 * Analyse one function body.
 *
 * `root` is a `Program` or a function body block; nested functions are skipped,
 * since each is analysed on its own.
 */
export function analyseBindingPlacement(
	root: t.Program | t.BlockStatement,
): BindingPlacementResult {
	const records = new Map<string, BindingRecord>();
	let nextScopeId = 0;

	const scopeFor = (
		body: t.Statement[],
		parent: PlacementScope | null,
		isFunctionScope: boolean,
	): PlacementScope => ({
		id: nextScopeId++,
		parent,
		depth: parent == null ? 0 : parent.depth + 1,
		body,
		isFunctionScope,
	});

	const record = (name: string): BindingRecord => {
		let existing = records.get(name);
		if (!existing) {
			existing = {
				name,
				declarations: [],
				uninitializedDeclarations: [],
				uses: [],
				hasVarDeclaration: false,
				hasLexicalDeclaration: false,
				inPattern: false,
				patternSiblings: new Set(),
				declarationSiblings: new Set(),
				inIndivisibleDeclaration: false,
				unsafeMixedSyntacticGroup: false,
				assigned: false,
				reasons: new Set(),
			};
			records.set(name, existing);
		}
		return existing;
	};

	const noteUse = (node: t.Node, scope: PlacementScope) => {
		for (const name of referencedGeneratedNames(node)) {
			record(name).uses.push(scope);
		}
	};

	const visitStatements = (body: t.Statement[], scope: PlacementScope) => {
		for (const statement of body) visitStatement(statement, scope);
	};

	const visitStatement = (
		statement: t.Statement,
		scope: PlacementScope,
	): void => {
		if (t.isFunctionDeclaration(statement)) return;

		if (t.isVariableDeclaration(statement)) {
			for (const declarator of statement.declarations) {
				const allNames = Object.keys(
					t.getBindingIdentifiers(declarator.id),
				);
				const names = allNames.filter(isGeneratedBindingName);
				const pattern = !t.isIdentifier(declarator.id);
				for (const name of names) {
					const entry = record(name);
					if (pattern) {
						for (const sibling of names) {
							if (sibling !== name) {
								entry.patternSiblings.add(sibling);
							}
						}
						entry.unsafeMixedSyntacticGroup ||= allNames.some((
							candidate,
						) => !isGeneratedBindingName(candidate));
					}
					// A `var` binds in the nearest function scope whatever
					// block it is written in, which is what makes it collide
					// with an outer `let` of the same name.
					const declarationScope = statement.kind === 'var'
						? functionScopeOf(scope)
						: scope;
					entry.declarations.push(declarationScope);
					if (!declarator.init) {
						entry.uninitializedDeclarations.push(declarationScope);
					}
					entry.hasVarDeclaration ||= statement.kind === 'var';
					entry.hasLexicalDeclaration ||= statement.kind !== 'var';
					entry.inPattern ||= pattern;
				}
				if (declarator.init) noteUse(declarator.init, scope);
			}
			return;
		}

		if (t.isBlockStatement(statement)) {
			visitStatements(
				statement.body,
				scopeFor(statement.body, scope, false),
			);
			return;
		}

		if (t.isIfStatement(statement)) {
			noteUse(statement.test, scope);
			visitBranch(statement.consequent, scope);
			if (statement.alternate) visitBranch(statement.alternate, scope);
			return;
		}

		if (t.isTryStatement(statement)) {
			visitStatements(
				statement.block.body,
				scopeFor(statement.block.body, scope, false),
			);
			if (statement.handler) {
				const handlerBody = statement.handler.body.body;
				visitStatements(
					handlerBody,
					scopeFor(handlerBody, scope, false),
				);
			}
			if (statement.finalizer) {
				visitStatements(
					statement.finalizer.body,
					scopeFor(statement.finalizer.body, scope, false),
				);
			}
			return;
		}

		if (t.isSwitchStatement(statement)) {
			noteUse(statement.discriminant, scope);
			// One lexical scope spans all cases, but each case's consequent is
			// its own statement list, so a declaration cannot be placed "in the
			// switch". Cases are analysed under a shared scope whose body is
			// the enclosing list -- projecting outward, as the policy requires.
			const caseScope = scopeFor(scope.body, scope, false);
			for (const switchCase of statement.cases) {
				if (switchCase.test) noteUse(switchCase.test, scope);
				visitStatements(switchCase.consequent, caseScope);
			}
			return;
		}

		if (
			t.isForStatement(statement) || t.isForInStatement(statement) ||
			t.isForOfStatement(statement) || t.isWhileStatement(statement) ||
			t.isDoWhileStatement(statement) || t.isLabeledStatement(statement)
		) {
			visitLoop(statement, scope);
			return;
		}

		noteUse(statement, scope);
	};

	const visitBranch = (branch: t.Statement, scope: PlacementScope) => {
		if (t.isBlockStatement(branch)) {
			visitStatements(branch.body, scopeFor(branch.body, scope, false));
			return;
		}
		visitStatement(branch, scope);
	};

	const visitLoop = (statement: t.Statement, scope: PlacementScope) => {
		// A loop header is its own lexical scope -- `for (let x …)` does not
		// bind `x` after the loop -- but it is not a statement list, so a
		// declaration cannot be placed in it. It gets a distinct scope whose
		// body is the enclosing list: uses inside the loop see it, uses after
		// the loop do not, and promoting one lands it where it can go.
		const headerScope = scopeFor(scope.body, scope, false);
		if (t.isForStatement(statement)) {
			if (statement.init) {
				if (t.isVariableDeclaration(statement.init)) {
					visitStatement(statement.init, headerScope);
					linkIndivisibleDeclaration(statement.init);
				} else noteUse(statement.init, headerScope);
			}
			if (statement.test) noteUse(statement.test, headerScope);
			if (statement.update) noteUse(statement.update, headerScope);
		} else if (
			t.isForInStatement(statement) || t.isForOfStatement(statement)
		) {
			if (t.isVariableDeclaration(statement.left)) {
				visitStatement(statement.left, headerScope);
			} else noteUse(statement.left, headerScope);
			noteUse(statement.right, headerScope);
		} else if (
			t.isWhileStatement(statement) || t.isDoWhileStatement(statement)
		) {
			noteUse(statement.test, headerScope);
		}
		const body = (statement as { body: t.Statement }).body;
		if (t.isBlockStatement(body)) {
			visitStatements(body.body, scopeFor(body.body, headerScope, false));
		} else visitStatement(body, headerScope);
	};

	const linkIndivisibleDeclaration = (
		declaration: t.VariableDeclaration,
	) => {
		const allNames = declaration.declarations.flatMap((declarator) =>
			Object.keys(t.getBindingIdentifiers(declarator.id))
		);
		const generated = allNames.filter(isGeneratedBindingName);
		const mixed = allNames.some((name) => !isGeneratedBindingName(name));
		for (const name of generated) {
			const entry = record(name);
			entry.inIndivisibleDeclaration = true;
			for (const sibling of generated) {
				if (sibling !== name) entry.declarationSiblings.add(sibling);
			}
			entry.unsafeMixedSyntacticGroup ||= mixed;
		}
	};

	const rootScope = scopeFor(root.body as t.Statement[], null, true);
	visitStatements(root.body as t.Statement[], rootScope);
	markAssignments(root, records);

	const result = resolvePlacements(records, rootScope);
	for (const name of ambiguousRegisterOwners(root)) {
		result.placed.delete(name);
		result.localized.delete(name);
		result.unresolved.add(name);
	}
	return result;
}

function functionScopeOf(scope: PlacementScope): PlacementScope {
	let current = scope;
	while (!current.isFunctionScope && current.parent) current = current.parent;
	return current;
}

/** Generated names referenced anywhere inside a node, nested functions aside. */
function referencedGeneratedNames(node: t.Node): string[] {
	const names: string[] = [];
	const visit = (
		current: t.Node,
		key: string | null,
		parent: t.Node | null,
	) => {
		if (current !== node && t.isFunction(current)) return;
		if (
			t.isIdentifier(current) && isGeneratedBindingName(current.name) &&
			!isSpelling(key, parent)
		) names.push(current.name);
		for (const childKey of t.VISITOR_KEYS[current.type] ?? []) {
			const value = (current as unknown as Record<string, unknown>)[
				childKey
			];
			if (Array.isArray(value)) {
				for (const child of value) {
					if (t.isNode(child)) visit(child, childKey, current);
				}
			} else if (t.isNode(value)) visit(value, childKey, current);
		}
	};
	visit(node, null, null);
	return names;
}

function isSpelling(key: string | null, parent: t.Node | null): boolean {
	if (!parent || !key) return false;
	if (key === 'property') {
		return (t.isMemberExpression(parent) ||
			t.isOptionalMemberExpression(parent)) && !parent.computed;
	}
	if (key === 'key') {
		return (t.isObjectProperty(parent) || t.isObjectMethod(parent)) &&
			!parent.computed;
	}
	return key === 'label';
}

/** Record which names are ever written, for the assignment-only rule. */
function markAssignments(
	root: t.Node,
	records: Map<string, BindingRecord>,
): void {
	const visit = (node: t.Node): void => {
		if (node !== root && t.isFunction(node)) return;
		const target = t.isAssignmentExpression(node)
			? node.left
			: t.isUpdateExpression(node)
			? node.argument
			: null;
		if (target) {
			const identifiers = t.getBindingIdentifiers(target);
			for (const [name, identifier] of Object.entries(identifiers)) {
				const location = locationOf(identifier);
				// A syntactic assignment is not proof that CFG reduction retained
				// the SSA definition. Only the provenance stamped by lifting is.
				if (
					location?.kind !== 'register' ||
					name !==
						`r${location.register.index}_${location.register.version}`
				) continue;
				const entry = records.get(name);
				if (entry) entry.assigned = true;
			}
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const child of value) if (t.isNode(child)) visit(child);
			} else if (t.isNode(value)) visit(value);
		}
	};
	visit(root);
}

/**
 * Textually equal registers from different inlined function owners are not one
 * binding. Until tree partitioning can place each owner independently, refuse
 * to rewrite that spelling rather than coalescing the two storage locations.
 */
function ambiguousRegisterOwners(
	root: t.Program | t.BlockStatement,
): Set<string> {
	const owners = new Map<string, Set<number>>();
	const visit = (node: t.Node): void => {
		if (node !== root && t.isFunction(node)) return;
		if (t.isIdentifier(node) && isGeneratedBindingName(node.name)) {
			const location = locationOf(node);
			if (location?.kind === 'register') {
				const ids = owners.get(node.name) ?? new Set<number>();
				ids.add(location.owner.functionId);
				owners.set(node.name, ids);
			}
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const child of value) if (t.isNode(child)) visit(child);
			} else if (t.isNode(value)) visit(value);
		}
	};
	visit(root);
	return new Set(
		[...owners].filter(([, ids]) => ids.size > 1).map(([name]) => name),
	);
}

function resolvePlacements(
	records: Map<string, BindingRecord>,
	rootScope: PlacementScope,
): BindingPlacementResult {
	const placed = new Map<string, BindingPlacement>();
	const localized = new Set<string>();
	const unresolved = new Set<string>();

	for (const entry of records.values()) {
		if (entry.declarations.length === 0) {
			// An assignment can stand in for a declaration only when SSA
			// provenance says a definition exists; a bare reference cannot.
			if (entry.assigned) {
				entry.reasons.add('assignment-without-declaration');
				placed.set(entry.name, {
					name: entry.name,
					scope: lowestCommon(entry.uses, rootScope).body,
					reasons: [...entry.reasons],
				});
			} else unresolved.add(entry.name);
			continue;
		}

		// Two declarations only conflict when they land in one scope. Region
		// emission routinely declares the same SSA version in each arm of a
		// branch, and those are independent per-arm bindings: only one ever
		// executes, and consolidating them would discard the localization
		// `preserveDuplicateRegisterScopesInBody` exists to preserve.
		const scopeIds = new Set(
			entry.declarations.map((scope) => scope.id),
		);
		if (scopeIds.size < entry.declarations.length) {
			entry.reasons.add('same-scope-duplicate');
		}
		if (
			entry.uninitializedDeclarations.some((outer) =>
				entry.declarations.some((inner) =>
					inner.id !== outer.id && scopeContains(outer, inner)
				)
			)
		) {
			entry.reasons.add('unwritten-ancestor-declaration');
		}
		// Visible from *some* declaration: a use in the `else` arm is served by
		// the `else` arm's declaration, not by whichever came first.
		const visible = entry.uses.every((use) =>
			entry.declarations.some((declaration) =>
				isVisibleFrom(use, declaration)
			)
		);
		if (!visible) entry.reasons.add('out-of-scope-use');
		// `let r; { var r; }` is a collision whatever the scopes, because the
		// `var` binds in the function scope the `let` already owns.
		if (entry.hasVarDeclaration && entry.hasLexicalDeclaration) {
			entry.reasons.add('var-lexical-collision');
		}
		if (entry.reasons.size === 0) {
			localized.add(entry.name);
			continue;
		}

		const target = lowestCommon(
			[...entry.declarations, ...entry.uses],
			rootScope,
		);
		placed.set(entry.name, {
			name: entry.name,
			scope: target.body,
			reasons: [...entry.reasons],
		});
	}

	// A pattern is rewritten as one assignment, so its members share a fate and
	// a scope: leaving one declared would need the declarator to be both a
	// declaration and an assignment, and splitting them across scopes would
	// need it to be in two places.
	for (
		const { names: group, reason } of syntacticGroups(records)
	) {
		if (!group.some((name) => placed.has(name))) continue;
		if (
			group.some((name) => records.get(name)?.unsafeMixedSyntacticGroup)
		) {
			// A declaration cannot simultaneously declare a user binding and
			// assign a promoted generated binding. Refuse the rewrite instead of
			// inserting an outer binding which the retained declaration shadows.
			for (const name of group) {
				if (!placed.delete(name)) continue;
				localized.delete(name);
				unresolved.add(name);
			}
			continue;
		}
		const scopes: PlacementScope[] = [];
		for (const name of group) {
			const entry = records.get(name);
			if (!entry) continue;
			scopes.push(...entry.declarations, ...entry.uses);
		}
		const target = lowestCommon(scopes, rootScope);
		for (const name of group) {
			const existing = placed.get(name);
			const reasons = new Set(existing?.reasons ?? []);
			reasons.add(reason);
			localized.delete(name);
			unresolved.delete(name);
			placed.set(name, {
				name,
				scope: target.body,
				reasons: [...reasons],
			});
		}
	}

	return { placed, localized, unresolved };
}

/** Names bound by the same destructuring declarator, as connected groups. */
function syntacticGroups(
	records: ReadonlyMap<string, BindingRecord>,
): Array<{
	names: string[];
	reason: 'pattern-closure' | 'declaration-closure';
}> {
	const seen = new Set<string>();
	const groups: Array<{
		names: string[];
		reason: 'pattern-closure' | 'declaration-closure';
	}> = [];
	for (const entry of records.values()) {
		const siblings = new Set([
			...entry.patternSiblings,
			...entry.declarationSiblings,
		]);
		if (
			(siblings.size === 0 && !entry.inPattern &&
				!entry.inIndivisibleDeclaration) || seen.has(entry.name)
		) continue;
		const group: string[] = [];
		const queue = [entry.name];
		let declarationClosure = entry.inIndivisibleDeclaration;
		while (queue.length > 0) {
			const name = queue.pop()!;
			if (seen.has(name)) continue;
			seen.add(name);
			group.push(name);
			const record = records.get(name);
			declarationClosure ||= record?.inIndivisibleDeclaration ?? false;
			for (
				const sibling of [
					...(record?.patternSiblings ?? []),
					...(record?.declarationSiblings ?? []),
				]
			) {
				if (!seen.has(sibling)) queue.push(sibling);
			}
		}
		groups.push({
			names: group,
			reason: declarationClosure
				? 'declaration-closure'
				: 'pattern-closure',
		});
	}
	return groups;
}

function isVisibleFrom(
	use: PlacementScope,
	declaration: PlacementScope,
): boolean {
	for (
		let current: PlacementScope | null = use;
		current;
		current = current.parent
	) {
		if (current.id === declaration.id) return true;
	}
	return false;
}

function lowestCommon(
	scopes: readonly PlacementScope[],
	fallback: PlacementScope,
): PlacementScope {
	let current: PlacementScope | null = scopes[0] ?? fallback;
	for (const scope of scopes.slice(1)) {
		current = commonAncestor(current!, scope);
		if (!current) return fallback;
	}
	return current ?? fallback;
}

function scopeContains(outer: PlacementScope, inner: PlacementScope): boolean {
	let current: PlacementScope | null = inner;
	while (current) {
		if (current.id === outer.id) return true;
		current = current.parent;
	}
	return false;
}

function commonAncestor(
	left: PlacementScope,
	right: PlacementScope,
): PlacementScope | null {
	let a: PlacementScope | null = left;
	let b: PlacementScope | null = right;
	while (a && b && a.depth > b.depth) a = a.parent;
	while (a && b && b.depth > a.depth) b = b.parent;
	while (a && b && a.id !== b.id) {
		a = a.parent;
		b = b.parent;
	}
	return a && b && a.id === b.id ? a : null;
}

/**
 * Whether a tree can possibly need placement repair.
 *
 * One linear scan, on plain nodes, before any scope tree is built, answering
 * the only question that rules repair out entirely: are there any generated
 * bindings at all. The analysis runs per function over bundles with six figures
 * of them, so the cheap answer has to come first.
 *
 * Deliberately not also requiring a nested statement list. Two declarations of
 * one name in a single flat list, and a reference with no declaration anywhere,
 * are both problems that need no nesting -- and the second is the one that must
 * never be missed, since it is what the unbound-register gate rejects on.
 */
export function needsBindingPlacement(
	root: t.Program | t.BlockStatement,
): boolean {
	let hasGenerated = false;
	t.traverseFast(root, (node) => {
		if (hasGenerated) return t.traverseFast.skip;
		if (t.isIdentifier(node) && isGeneratedBindingName(node.name)) {
			hasGenerated = true;
		}
	});
	return hasGenerated;
}

/**
 * Analyse and rewrite: one declaration per binding, in the scope every use can
 * see it from, with the original declaration sites left as assignments.
 *
 * Idempotent. Running it on its own output finds every binding already
 * localized and rewrites nothing.
 */
export function placeGeneratedBindings(
	root: t.Program | t.BlockStatement,
): BindingPlacementResult {
	if (!needsBindingPlacement(root)) {
		return {
			placed: new Map(),
			localized: new Set(),
			unresolved: new Set(),
		};
	}
	const result = analyseBindingPlacement(root);
	if (result.placed.size === 0) return result;

	const placedNames = new Set(result.placed.keys());
	rewriteStatements(root.body as t.Statement[], placedNames);

	// Grouped by target list, so one `let` covers every binding landing there.
	const byScope = new Map<t.Statement[], string[]>();
	for (const placement of result.placed.values()) {
		const names = byScope.get(placement.scope) ?? [];
		names.push(placement.name);
		byScope.set(placement.scope, names);
	}
	for (const [body, names] of byScope) {
		body.splice(
			directivePrologueLength(body),
			0,
			t.variableDeclaration(
				'let',
				names.toSorted().map((name) =>
					t.variableDeclarator(t.identifier(name))
				),
			),
		);
	}
	return result;
}

/**
 * Every independently owned function body in a composed tree.
 *
 * The single-body analyser skips nested functions by design. Composition can
 * inline many complete functions under one Program, so the tree entry point
 * partitions them explicitly instead of merging equal `rN_M` spellings.
 */
export function generatedBindingPlacementRoots(
	root: t.Program | t.BlockStatement,
): Array<{ path: string; root: t.Program | t.BlockStatement }> {
	const roots: Array<{
		path: string;
		root: t.Program | t.BlockStatement;
	}> = [{ path: 'root', root }];
	let nextFunction = 0;
	const visit = (node: t.Node): void => {
		if (t.isFunction(node)) {
			if (t.isBlockStatement(node.body)) {
				roots.push({
					path: `function#${nextFunction++}`,
					root: node.body,
				});
				for (const statement of node.body.body) visit(statement);
			}
			return;
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const child of value) if (t.isNode(child)) visit(child);
			} else if (t.isNode(value)) visit(value);
		}
	};
	for (const statement of root.body as t.Statement[]) visit(statement);
	return roots;
}

export function analyseBindingPlacementInTree(
	root: t.Program | t.BlockStatement,
): BindingPlacementTreeResult {
	const entries = generatedBindingPlacementRoots(root).map((entry) => ({
		...entry,
		result: analyseBindingPlacement(entry.root),
	}));
	return summarizeTreePlacement(entries);
}

export function placeGeneratedBindingsInTree(
	root: t.Program | t.BlockStatement,
): BindingPlacementTreeResult {
	// Bottom-up prevents a parent rewrite from changing the traversal used to
	// discover its children, even though the current scalar rewrites skip them.
	const roots = generatedBindingPlacementRoots(root);
	const results = new Map<
		t.Program | t.BlockStatement,
		BindingPlacementResult
	>();
	for (const entry of roots.toReversed()) {
		results.set(entry.root, placeGeneratedBindings(entry.root));
	}
	return summarizeTreePlacement(roots.map((entry) => ({
		...entry,
		result: results.get(entry.root)!,
	})));
}

function summarizeTreePlacement(
	entries: BindingPlacementTreeEntry[],
): BindingPlacementTreeResult {
	let placed = 0;
	let localized = 0;
	let unresolved = 0;
	for (const entry of entries) {
		placed += entry.result.placed.size;
		localized += entry.result.localized.size;
		unresolved += entry.result.unresolved.size;
	}
	return { entries, placed, localized, unresolved };
}

/** How many leading statements are a directive prologue. */
function directivePrologueLength(body: readonly t.Statement[]): number {
	let count = 0;
	for (const statement of body) {
		if (
			!t.isExpressionStatement(statement) ||
			!t.isStringLiteral(statement.expression)
		) break;
		count++;
	}
	return count;
}

function rewriteStatements(body: t.Statement[], placed: ReadonlySet<string>) {
	const out: t.Statement[] = [];
	for (const statement of body) {
		if (t.isVariableDeclaration(statement)) {
			out.push(...convertDeclaration(statement, placed));
			continue;
		}
		rewriteNested(statement, placed);
		out.push(statement);
	}
	body.length = 0;
	body.push(...out);
}

function rewriteNested(statement: t.Statement, placed: ReadonlySet<string>) {
	if (t.isFunctionDeclaration(statement)) return;
	if (t.isBlockStatement(statement)) {
		rewriteStatements(statement.body, placed);
		return;
	}
	if (t.isIfStatement(statement)) {
		rewriteBranch(statement, 'consequent', placed);
		if (statement.alternate) rewriteBranch(statement, 'alternate', placed);
		return;
	}
	if (t.isTryStatement(statement)) {
		rewriteStatements(statement.block.body, placed);
		if (statement.handler) {
			rewriteStatements(statement.handler.body.body, placed);
		}
		if (statement.finalizer) {
			rewriteStatements(statement.finalizer.body, placed);
		}
		return;
	}
	if (t.isSwitchStatement(statement)) {
		for (const switchCase of statement.cases) {
			rewriteStatements(switchCase.consequent, placed);
		}
		return;
	}
	if (t.isLabeledStatement(statement)) {
		rewriteNested(statement.body, placed);
		return;
	}
	if (t.isForStatement(statement)) {
		rewriteForInit(statement, placed);
		rewriteLoopBody(statement, placed);
		return;
	}
	if (t.isForInStatement(statement) || t.isForOfStatement(statement)) {
		rewriteForTarget(statement, placed);
		rewriteLoopBody(statement, placed);
		return;
	}
	if (t.isWhileStatement(statement) || t.isDoWhileStatement(statement)) {
		rewriteLoopBody(statement, placed);
	}
}

function rewriteBranch(
	statement: t.IfStatement,
	key: 'consequent' | 'alternate',
	placed: ReadonlySet<string>,
) {
	const branch = statement[key];
	if (!branch) return;
	if (t.isBlockStatement(branch)) {
		rewriteStatements(branch.body, placed);
		return;
	}
	if (t.isVariableDeclaration(branch)) {
		// A bare declaration as a branch body has nowhere to split into, so it
		// becomes a block holding whatever it rewrites to.
		statement[key] = t.blockStatement(convertDeclaration(branch, placed));
		return;
	}
	rewriteNested(branch, placed);
}

function rewriteLoopBody(
	statement: { body: t.Statement },
	placed: ReadonlySet<string>,
) {
	if (t.isBlockStatement(statement.body)) {
		rewriteStatements(statement.body.body, placed);
		return;
	}
	if (t.isVariableDeclaration(statement.body)) {
		statement.body = t.blockStatement(
			convertDeclaration(statement.body, placed),
		);
		return;
	}
	rewriteNested(statement.body, placed);
}

/** `for (let r1_0 = 0; …)` becomes `for (r1_0 = 0; …)`. */
function rewriteForInit(
	statement: t.ForStatement,
	placed: ReadonlySet<string>,
) {
	const init = statement.init;
	if (!t.isVariableDeclaration(init)) return;
	const kept: t.VariableDeclarator[] = [];
	const assignments: t.Expression[] = [];
	for (const declarator of init.declarations) {
		if (!declaratorIsPlaced(declarator, placed)) {
			kept.push(declarator);
			continue;
		}
		if (declarator.init) {
			assignments.push(
				t.assignmentExpression(
					'=',
					t.cloneNode(declarator.id, true) as t.LVal,
					declarator.init,
				),
			);
		}
	}
	if (kept.length === init.declarations.length) return;
	if (kept.length > 0) {
		// A partly converted header would need to be a declaration and an
		// expression at once; leaving it alone is the conservative answer and
		// the analysis will still see the binding declared here.
		return;
	}
	statement.init = assignments.length === 0
		? null
		: assignments.length === 1
		? assignments[0]
		: t.sequenceExpression(assignments);
}

/** `for (let r1_0 of xs)` becomes `for (r1_0 of xs)`. */
function rewriteForTarget(
	statement: t.ForInStatement | t.ForOfStatement,
	placed: ReadonlySet<string>,
) {
	const left = statement.left;
	if (!t.isVariableDeclaration(left) || left.declarations.length !== 1) {
		return;
	}
	const [declarator] = left.declarations;
	if (!declaratorIsPlaced(declarator, placed)) return;
	statement.left = t.cloneNode(declarator.id, true) as t.LVal;
}

function declaratorIsPlaced(
	declarator: t.VariableDeclarator,
	placed: ReadonlySet<string>,
): boolean {
	const names = Object.keys(t.getBindingIdentifiers(declarator.id));
	if (names.length === 0) return false;
	// Every name, not any: a declarator is one syntactic unit, and pattern
	// siblings are placed together precisely so this holds.
	return names.every((name) => placed.has(name));
}

/**
 * Split a declaration, converting the placed declarators to assignments.
 *
 * Split rather than rewritten in place so initializers keep their left-to-right
 * order: `const a = f(), b = g()` must still call `f` before `g` once one of
 * the two becomes an assignment.
 */
function convertDeclaration(
	declaration: t.VariableDeclaration,
	placed: ReadonlySet<string>,
): t.Statement[] {
	if (
		!declaration.declarations.some((declarator) =>
			declaratorIsPlaced(declarator, placed)
		)
	) return [declaration];

	const out: t.Statement[] = [];
	for (const declarator of declaration.declarations) {
		if (!declaratorIsPlaced(declarator, placed)) {
			out.push(t.variableDeclaration(declaration.kind, [declarator]));
			continue;
		}
		if (!declarator.init) continue;
		out.push(t.expressionStatement(
			t.assignmentExpression(
				'=',
				// Cloned rather than rebuilt: the id carries the SSA and alias
				// provenance later passes read.
				t.cloneNode(declarator.id, true) as t.LVal,
				declarator.init,
			),
		));
	}
	return out;
}
