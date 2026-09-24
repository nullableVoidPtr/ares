import * as t from '@babel/types';
import { Binding, NodePath, Scope } from '@babel/traverse';

function scopeDepth(inner: Scope, outer: Scope) {
	let depth = 0;
	let cursor: Scope | undefined = inner;

	while (cursor) {
		if (cursor === outer) return depth;

		if (cursor.path.isFunction() || cursor.path.isProgram()) depth++;

		cursor = cursor.parent;
	}

	return -1;
}

function isBareAssign(path: NodePath, target: string) {
	if (path.isAssignmentExpression({ operator: '=' })) {
		return path.get('left').isIdentifier({ name: target });
	}

	return false;
}

function getLoopAssign(path: NodePath, target: string) {
	if (
		path.isForOfStatement() &&
		path.get('left').isIdentifier({ name: target })
	) return path.get('left');
	if (
		path.isForInStatement() &&
		path.get('left').isIdentifier({ name: target })
	) return path.get('left');

	return null;
}

function findShallowestAssignment(binding: Binding) {
	let best = null;
	let bestDepth = Infinity;

	for (const refPath of binding.constantViolations) {
		let targetPath = refPath.parentPath;
		let init: t.Expression | undefined;
		if (isBareAssign(refPath, binding.identifier.name)) {
			init = refPath.get('right').node as t.Expression;
			if (!targetPath?.isExpressionStatement()) continue;
		} else {
			const assign = getLoopAssign(refPath, binding.identifier.name);
			if (!assign) continue;
			targetPath = assign;
		}

		const depth = scopeDepth(refPath.scope, binding.scope);

		if (depth < 0) continue;

		if (depth < bestDepth) {
			bestDepth = depth;
			best = { init, targetPath };

			if (depth === 0) break;
		}
	}

	return best;
}

export function unhoistDeclaredGlobals(
	path: NodePath<t.VariableDeclarator>,
): boolean {
	if (!path.parentPath?.isVariableDeclaration({ kind: 'var' })) return false;
	if (!path.node.extra?.isDeclaredGlobal) return false;

	const id = path.get('id');
	if (!id.isIdentifier()) return false;

	path.scope.crawl();
	const binding = path.scope.getBinding(id.node.name);
	if (!binding) return false;

	const assign = findShallowestAssignment(binding);
	if (!assign) return false;

	let declaration: t.Statement = t.variableDeclaration('var', [
		t.variableDeclarator(
			id.node,
			assign.init,
		),
	]);

	if (t.isFunctionExpression(assign.init)) {
		if (assign.init.id && id.node.name == assign.init.id.name) {
			declaration = t.functionDeclaration(
				id.node,
				assign.init.params,
				assign.init.body,
				assign.init.generator,
				assign.init.async,
			);
		}
	} else if (t.isClassExpression(assign.init)) {
		if (assign.init.id && id.node.name == assign.init.id.name) {
			declaration = t.classDeclaration(
				id.node,
				assign.init.superClass,
				assign.init.body,
				assign.init.decorators,
			);
		}
	}

	assign.targetPath.replaceWith(declaration);

	binding.path.remove();
	return true;
}
