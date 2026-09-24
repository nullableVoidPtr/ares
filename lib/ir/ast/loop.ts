import * as t from '@babel/types';
import { NodePath } from '@babel/traverse';

function tryBuildForStatement(
	preLoop: NodePath<t.Statement>,
	loop: NodePath<t.WhileStatement>,
	updateStmt: NodePath<t.Statement>,
) {
	let forInit = preLoop.getPrevSibling();

	let id: NodePath;
	if (
		forInit.isVariableDeclaration() &&
		forInit.node.declarations.length === 1
	) {
		id = forInit.get('declarations.0.id');
	} else if (forInit.isExpressionStatement()) {
		const expr = forInit.get('expression');
		if (!expr.isAssignmentExpression({ operator: '=' })) return;
		forInit = expr;
		id = expr.get('left');
	} else {
		return;
	}

	if (!forInit.isVariableDeclaration() && !forInit.isExpression()) return;
	if (!id.isIdentifier()) return;

	if (!updateStmt.isExpressionStatement()) return;
	const updateExpr = updateStmt.get('expression');

	forInit.scope.crawl();

	const binding = forInit.scope.getBinding(id.node.name);

	if (!binding) return;

	for (const assign of binding?.constantViolations) {
		if (assign != updateExpr && !updateExpr.isAncestor(assign)) continue;

		const replacement = t.forStatement(
			forInit.node,
			loop.node.test,
			updateExpr.node,
			loop.node.body,
		);
		forInit.remove();
		updateStmt.remove();
		return replacement;
	}
}

export function cleanupGuardedNaturalLoops(preLoop: NodePath<t.IfStatement>) {
	if (preLoop.node.alternate) return;
	const enclosing = preLoop.get('consequent');
	if (!enclosing.isBlockStatement() || enclosing.node.body.length !== 1) {
		return;
	}

	const loop = enclosing.get('body.0');
	if (!loop.isWhileStatement()) return;
	const loopTest = loop.get('test');
	if (!loopTest.isBooleanLiteral({ value: true })) return;

	const body = loop.get('body');
	if (!body.isBlockStatement()) return;
	const breakIf = body.get('body').at(-1);
	if (!breakIf?.isIfStatement() || breakIf.node.alternate) return;
	let breakBody = breakIf.get('consequent');
	if (breakBody.isBlockStatement()) {
		if (breakBody.node.body.length !== 1) return;
		breakBody = breakBody.get('body.0');
	}

	if (!breakBody.isBreakStatement()) return;

	const preLoopTest = preLoop.get('test');
	const breakTest = breakIf.get('test');
	if (!breakTest.isUnaryExpression({ operator: '!' })) return;
	const continueTest = breakTest.get('argument');
	if (preLoopTest.toString() != continueTest.toString()) return;

	const updateStmt = breakIf.getPrevSibling();
	if (!updateStmt.isStatement()) return;

	loopTest.replaceWith(continueTest.node);
	breakIf.remove();

	preLoop.replaceWith(
		tryBuildForStatement(preLoop, loop, updateStmt) ?? loop.node,
	);
}
