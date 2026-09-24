import * as t from '@babel/types';
import { NodePath } from '@babel/traverse';
import { isEnvironmentSlotName } from '../../environment.ts';
import { isUndefinedNode } from '../utils.ts';
import {
	countLocationReferences,
	locationKey,
	locationOf,
	tagStorageLocation,
} from '../alias.ts';

function envAssignment(stmt: NodePath<t.Statement>) {
	if (!stmt.isExpressionStatement()) return;
	const expr = stmt.get('expression');
	if (!expr.isAssignmentExpression({ operator: '=' })) return;
	const left = expr.get('left');
	if (!left.isIdentifier() || !isEnvironmentSlotName(left.node.name)) return;
	const right = expr.get('right');
	if (!right.isExpression()) return;

	return { name: left.node.name, left, right, stmt };
}

function replaceEnvAliasIdentifiers(
	path: NodePath,
	name: string,
	replacement: t.Identifier,
) {
	path.traverse({
		AssignmentExpression(assign) {
			const left = assign.get('left');
			if (left.isIdentifier({ name })) {
				left.replaceWith(t.cloneNode(replacement));
			}
		},
		UpdateExpression(update) {
			const argument = update.get('argument');
			if (argument.isIdentifier({ name })) {
				argument.replaceWith(t.cloneNode(replacement));
			}
		},
		Identifier(id) {
			if (!id.isReferencedIdentifier({ name })) return;
			id.replaceWith(t.cloneNode(replacement));
		},
	});
}

function removeDeclarator(decl: NodePath<t.VariableDeclarator>) {
	const parent = decl.parentPath;
	decl.remove();
	if (
		parent.isVariableDeclaration() && parent.node.declarations.length === 0
	) {
		parent.remove();
	}
}

/** The env slot a statement assigns, read off plain nodes. */
function envAssignmentNode(
	statement: t.Statement,
): {
	name: string;
	left: t.Identifier;
	right: t.Expression;
} | undefined {
	if (!t.isExpressionStatement(statement)) return;
	const expression = statement.expression;
	if (
		!t.isAssignmentExpression(expression, { operator: '=' }) ||
		!t.isIdentifier(expression.left) ||
		!isEnvironmentSlotName(expression.left.name) ||
		!t.isExpression(expression.right)
	) return;
	return {
		name: expression.left.name,
		left: expression.left,
		right: expression.right,
	};
}

/**
 * Whether `name` is *read* anywhere strictly under `node`.
 *
 * Reads only: a write to the slot is not a reason to keep its declaration, and
 * counting one would block the very promotion this pass exists to perform.
 * `t.isReferenced` needs the parent, so this walks with parents rather than
 * using `traverseFast`, and skips the root to match the traversal it replaces.
 */
function referencesIdentifierNode(root: t.Node, name: string): boolean {
	let found = false;
	const visit = (node: t.Node, parent: t.Node, grandparent?: t.Node) => {
		if (found) return;
		if (
			t.isIdentifier(node, { name }) &&
			t.isReferenced(node, parent, grandparent)
		) {
			found = true;
			return;
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const child of value) {
					if (t.isNode(child)) visit(child, node, parent);
					if (found) return;
				}
			} else if (t.isNode(value)) {
				visit(value, node, parent);
				if (found) return;
			}
		}
	};
	for (const key of t.VISITOR_KEYS[root.type] ?? []) {
		const value = (root as unknown as Record<string, unknown>)[key];
		if (Array.isArray(value)) {
			for (const child of value) if (t.isNode(child)) visit(child, root);
		} else if (t.isNode(value)) visit(value, root);
		if (found) return true;
	}
	return found;
}

/**
 * The first `_env_x = …` statement for `name`, and where it lives.
 *
 * Returns the containing array and index so the caller can replace the
 * statement by assignment rather than through a `NodePath`. Document order
 * matters -- "first" is the first one Babel's traversal would have reached --
 * so a node is checked before its children and siblings follow in order.
 * Nested functions are skipped: a slot assigned inside one is not this body's
 * first assignment.
 */
function findFirstEnvAssignmentNode(
	root: t.Node,
	name: string,
): { statements: t.Statement[]; index: number } | undefined {
	let found: { statements: t.Statement[]; index: number } | undefined;
	const isFunctionLike = (node: t.Node) =>
		t.isFunctionExpression(node) || t.isFunctionDeclaration(node) ||
		t.isArrowFunctionExpression(node) || t.isObjectMethod(node) ||
		t.isClassMethod(node);
	const visit = (
		node: t.Node,
		container: t.Statement[] | null,
		index: number,
	): boolean => {
		if (node !== root && isFunctionLike(node)) return false;
		if (
			container != null &&
			envAssignmentNode(node as t.Statement)?.name === name
		) {
			found = { statements: container, index };
			return true;
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (let position = 0; position < value.length; position++) {
					const child = value[position];
					if (!t.isNode(child)) continue;
					const list = t.isStatement(child)
						? value as t.Statement[]
						: null;
					if (visit(child, list, position)) return true;
				}
			} else if (t.isNode(value)) {
				if (visit(value, null, -1)) return true;
			}
		}
		return false;
	};
	visit(root, null, -1);
	return found;
}

/**
 * Whether `name` is written anywhere other than in `assignmentStmt`.
 *
 * Counted at any depth, nested functions included, matching what the binding
 * would see at runtime.
 */
function hasOtherBindingWriteNode(
	node: t.Node,
	name: string,
	assignmentStmt: t.Statement,
): boolean {
	let found = false;
	const walk = (current: t.Node, statement: t.Statement | null) => {
		if (found) return;
		const here = t.isStatement(current) ? current : statement;
		if (here !== assignmentStmt) {
			if (
				(t.isAssignmentExpression(current) &&
					t.isIdentifier(current.left, { name })) ||
				(t.isUpdateExpression(current) &&
					t.isIdentifier(current.argument, { name }))
			) {
				found = true;
				return;
			}
		}
		for (const key of t.VISITOR_KEYS[current.type] ?? []) {
			const value = (current as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const child of value) {
					if (t.isNode(child)) walk(child, here);
				}
			} else if (t.isNode(value)) walk(value, here);
			if (found) return;
		}
	};
	walk(node, null);
	return found;
}

function declarationForEnvironmentAssignment(
	bodyPath: NodePath<t.Program | t.BlockStatement>,
	id: t.Identifier,
	value: t.Expression,
	mutable: boolean,
) {
	if (t.isFunctionExpression(value)) {
		let declarationId = t.cloneNode(id);
		if (value.id && value.id.name !== id.name) {
			// A named function expression's identifier is normally local to the
			// expression. The environment cell is the source-level outer binding;
			// when that name is otherwise free, promote it to the declaration and
			// coalesce every cell access onto it. This also keeps recursive uses of
			// the expression name bound after the FunctionExpression disappears.
			const location = locationOf(id);
			const existing = bodyPath.scope.getBinding(value.id.name);
			if (
				location?.kind !== 'environment-slot' ||
				existing && existing.identifier !== value.id
			) {
				return t.variableDeclaration('var', [
					t.variableDeclarator(t.cloneNode(id), value),
				]);
			}
			declarationId = t.cloneNode(value.id);
			tagStorageLocation(declarationId, location);
			replaceEnvAliasIdentifiers(bodyPath, id.name, declarationId);
		}
		return t.functionDeclaration(
			declarationId,
			value.params,
			value.body,
			value.generator,
			value.async,
		);
	}

	return t.variableDeclaration(mutable ? 'let' : 'const', [
		t.variableDeclarator(t.cloneNode(id), value),
	]);
}

/**
 * Whether a body has anything for `cleanupEnvironmentBody` to do.
 *
 * Answered on plain nodes, because the expensive part of that pass is asking
 * Babel for a `NodePath` per statement, and most bodies carry no environment
 * prologue at all. Every rewrite it performs starts from one of these three
 * shapes, so a body with none of them is left untouched either way.
 */
function bodyNeedsEnvironmentCleanup(
	node: t.Program | t.BlockStatement,
): boolean {
	for (const statement of node.body) {
		if (t.isVariableDeclaration(statement, { kind: 'var' })) {
			// An emptied declaration is swept up at the end of the pass.
			if (statement.declarations.length === 0) return true;
			for (const declarator of statement.declarations) {
				if (
					t.isIdentifier(declarator.id) &&
					isEnvironmentSlotName(declarator.id.name)
				) return true;
			}
			continue;
		}
		if (
			t.isExpressionStatement(statement) &&
			t.isAssignmentExpression(statement.expression, { operator: '=' }) &&
			t.isIdentifier(statement.expression.left) &&
			isEnvironmentSlotName(statement.expression.left.name)
		) return true;
	}
	return false;
}

export function cleanupEnvironmentBody(
	bodyPath: NodePath<t.Program | t.BlockStatement>,
) {
	if (!bodyNeedsEnvironmentCleanup(bodyPath.node)) return;
	const statements = bodyPath.get('body');
	const envDecls = new Map<string, NodePath<t.VariableDeclarator>>();
	for (const stmt of statements) {
		if (!stmt.isVariableDeclaration({ kind: 'var' })) continue;
		for (const decl of stmt.get('declarations')) {
			const id = decl.get('id');
			if (id.isIdentifier() && isEnvironmentSlotName(id.node.name)) {
				envDecls.set(id.node.name, decl);
			}
		}
	}

	const removedPrologueUndefined = new Set<string>();
	/**
	 * Parameters already aliased onto a slot.
	 *
	 * `replaceEnvAliasIdentifiers` rewrites a slot's writes onto the parameter,
	 * so aliasing a second slot onto the same parameter would make the two
	 * slots alias each other: the second slot's stores would land on the
	 * first's storage. One claim per parameter.
	 */
	const claimedParameters = new Set<string>();
	const claimParameterAlias = (node: t.Node | null | undefined) => {
		const location = locationOf(node);
		if (location?.kind !== 'parameter') return false;
		// The prologue copy must be the parameter's only direct reference.
		// Otherwise rewriting later slot writes onto the parameter changes a
		// separately observable binding. Slot/closure references are rewritten
		// together and therefore do not count against this condition.
		if (countLocationReferences(bodyPath.node, location) !== 1) {
			return false;
		}
		const key = locationKey(location);
		if (claimedParameters.has(key)) return false;
		claimedParameters.add(key);
		return true;
	};
	for (let i = 0; i < statements.length; i++) {
		const stmt = statements[i];
		if (stmt.isVariableDeclaration({ kind: 'var' })) {
			for (const decl of stmt.get('declarations')) {
				const id = decl.get('id');
				const init = decl.get('init');
				if (
					!id.isIdentifier() || !isEnvironmentSlotName(id.node.name)
				) {
					continue;
				}

				if (isUndefinedNode(init.node)) {
					removedPrologueUndefined.add(id.node.name);
					removeDeclarator(decl);
					continue;
				}

				const initNode = init.node as t.Expression | null | undefined;
				if (
					t.isIdentifier(initNode) &&
					claimParameterAlias(initNode)
				) {
					replaceEnvAliasIdentifiers(
						bodyPath,
						id.node.name,
						initNode,
					);
					envDecls.delete(id.node.name);
					removeDeclarator(decl);
				}
			}
			continue;
		}
		const assign = envAssignment(stmt);
		if (!assign) break;

		if (isUndefinedNode(assign.right.node)) {
			removedPrologueUndefined.add(assign.name);
			stmt.remove();
			continue;
		}

		const rightNode = assign.right.node as t.Expression;
		if (
			t.isIdentifier(rightNode) &&
			claimParameterAlias(rightNode)
		) {
			replaceEnvAliasIdentifiers(bodyPath, assign.name, rightNode);
			const decl = envDecls.get(assign.name);
			if (decl) removeDeclarator(decl);
			envDecls.delete(assign.name);
			stmt.remove();
			continue;
		}

		break;
	}

	for (const name of removedPrologueUndefined) {
		const decl = envDecls.get(name);
		if (decl && !decl.hasNode()) continue;

		const firstAssignment = findFirstEnvAssignmentNode(bodyPath.node, name);

		if (firstAssignment) {
			const { statements: list, index } = firstAssignment;
			const statement = list[index]!;
			const assign = envAssignmentNode(statement)!;
			if (isUndefinedNode(assign.right)) continue;
			if (
				referencesIdentifierNode(assign.right, name) &&
				!t.isFunctionExpression(assign.right)
			) continue;
			// A declaration inside a conditional/loop/try list would no longer
			// dominate closures or sibling paths which capture the runtime slot.
			// Keep the function-root declaration and the ordered assignment; the
			// environment-slot placement pass has already established that root as
			// the cell's authoritative lexical owner.
			if (list !== bodyPath.node.body) continue;
			list[index] = declarationForEnvironmentAssignment(
				bodyPath,
				assign.left,
				assign.right,
				hasOtherBindingWriteNode(bodyPath.node, name, statement),
			);
			if (decl) removeDeclarator(decl);
			continue;
		}

		if (!referencesIdentifierNode(bodyPath.node, name)) {
			if (decl) removeDeclarator(decl);
		}
	}

	for (const [name, decl] of envDecls) {
		if (!decl.hasNode()) continue;
		if (decl.node.init != null) continue;

		const firstAssignment = findFirstEnvAssignmentNode(bodyPath.node, name);
		if (!firstAssignment) continue;
		const { statements: list, index } = firstAssignment;
		const statement = list[index]!;
		const assign = envAssignmentNode(statement)!;
		if (isUndefinedNode(assign.right)) continue;
		if (
			referencesIdentifierNode(assign.right, name) &&
			!t.isFunctionExpression(assign.right)
		) continue;
		if (list !== bodyPath.node.body) continue;

		list[index] = declarationForEnvironmentAssignment(
			bodyPath,
			assign.left,
			assign.right,
			hasOtherBindingWriteNode(bodyPath.node, name, statement),
		);
		removeDeclarator(decl);
	}

	for (const stmt of bodyPath.get('body')) {
		if (!stmt.isVariableDeclaration({ kind: 'var' })) continue;
		if (stmt.node.declarations.length === 0) stmt.remove();
	}
}
