import * as t from '@babel/types';
import { isParameterExpression } from '../../../ast/alias.ts';

export interface FinalizerPushAddDescriptor {
	receiver: t.Expression;
	addend: t.Expression;
	induction: t.Identifier;
}

export interface LabelledLoopFinallyDescriptor
	extends FinalizerPushAddDescriptor {
	loop: t.WhileStatement;
	tryStmt: t.TryStatement;
	flag: t.Identifier;
	initial: t.Expression;
	breakValue: t.Expression;
	bound: t.Expression;
}

export function finalizerPushAddInfo(
	finalizer: t.BlockStatement,
): FinalizerPushAddDescriptor | null {
	for (const stmt of finalizer.body) {
		if (!t.isExpressionStatement(stmt)) continue;
		const call = stmt.expression;
		if (!t.isCallExpression(call)) continue;
		if (
			!t.isMemberExpression(call.callee, { computed: false }) ||
			!t.isIdentifier(call.callee.property, { name: 'push' })
		) continue;
		const [arg] = call.arguments;
		if (
			!t.isBinaryExpression(arg, { operator: '+' }) ||
			!t.isExpression(arg.left) ||
			!t.isIdentifier(arg.right)
		) continue;
		return {
			receiver: t.cloneNode(call.callee.object as t.Expression, true),
			addend: t.cloneNode(arg.left, true),
			induction: t.cloneNode(arg.right),
		};
	}
	return null;
}

export function labelledLoopFinallyShapeInfo(
	stmt: t.Statement,
): LabelledLoopFinallyDescriptor | null {
	if (
		!t.isWhileStatement(stmt) ||
		!t.isBooleanLiteral(stmt.test, { value: true }) ||
		!t.isBlockStatement(stmt.body) ||
		stmt.body.body.length !== 1
	) return null;
	const tryStmt = stmt.body.body[0];
	if (!t.isTryStatement(tryStmt) || !tryStmt.finalizer) return null;
	const finalizerInfo = finalizerPushAddInfo(tryStmt.finalizer);
	if (!finalizerInfo) return null;

	let flag: t.Identifier | null = null;
	let initial: t.Expression | null = null;
	const equalityValues: t.Expression[] = [];
	let bound: t.Expression | null = null;
	t.traverseFast(tryStmt.block, (node) => {
		if (
			!flag &&
			t.isIdentifier(node) &&
			isParameterExpression(node)
		) {
			flag = t.cloneNode(node);
			return;
		}
		if (!initial && t.isCallExpression(node)) {
			const [arg] = node.arguments;
			if (
				t.isMemberExpression(node.callee, { computed: false }) &&
				t.isIdentifier(node.callee.property, { name: 'push' }) &&
				t.isExpression(arg)
			) {
				initial = t.cloneNode(arg, true);
			}
		}
		if (t.isBinaryExpression(node, { operator: '===' })) {
			if (t.isNumericLiteral(node.left)) {
				equalityValues.push(t.cloneNode(node.left, true));
			}
			if (t.isNumericLiteral(node.right)) {
				equalityValues.push(t.cloneNode(node.right, true));
			}
		}
		if (!bound && t.isBinaryExpression(node, { operator: '<' })) {
			if (t.isNumericLiteral(node.right)) {
				bound = t.cloneNode(node.right, true);
			}
		}
	});
	const breakValue =
		equalityValues.find((value) =>
			!(t.isNumericLiteral(value) && t.isNumericLiteral(initial) &&
				value.value === initial.value)
		) ?? equalityValues[0] ?? null;
	if (!flag || !initial || !breakValue || !bound) return null;
	return {
		loop: stmt,
		tryStmt,
		...finalizerInfo,
		flag,
		initial,
		breakValue,
		bound,
	};
}

export function repairLabelledLoopFinally(body: t.Statement[]): boolean {
	for (let index = 0; index < body.length; index++) {
		const info = labelledLoopFinallyShapeInfo(body[index]);
		if (!info) continue;
		const induction = t.cloneNode(info.induction);
		const receiver = t.cloneNode(info.receiver, true);
		const breakTest = t.binaryExpression(
			'===',
			t.cloneNode(induction),
			t.cloneNode(info.breakValue, true),
		);
		const pushInitial = t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.cloneNode(receiver, true),
				t.identifier('push'),
			),
			[t.cloneNode(induction)],
		));
		const consequent = t.ifStatement(
			t.logicalExpression(
				'&&',
				t.cloneNode(info.flag),
				t.cloneNode(breakTest, true),
			),
			t.blockStatement([t.continueStatement()]),
		);
		const alternate = t.ifStatement(
			t.logicalExpression(
				'&&',
				t.unaryExpression('!', t.cloneNode(info.flag)),
				t.cloneNode(breakTest, true),
			),
			t.blockStatement([t.breakStatement()]),
		);
		const finalizer = t.blockStatement([
			t.expressionStatement(t.callExpression(
				t.memberExpression(
					t.cloneNode(receiver, true),
					t.identifier('push'),
				),
				[
					t.binaryExpression(
						'+',
						t.cloneNode(info.addend, true),
						t.cloneNode(induction),
					),
				],
			)),
		]);
		const forLoop = t.forStatement(
			t.variableDeclaration('let', [
				t.variableDeclarator(
					t.cloneNode(induction),
					t.cloneNode(info.initial, true),
				),
			]),
			t.binaryExpression(
				'<',
				t.cloneNode(induction),
				t.cloneNode(info.bound, true),
			),
			t.updateExpression('++', t.cloneNode(induction)),
			t.blockStatement([
				t.tryStatement(
					t.blockStatement([pushInitial, consequent, alternate]),
					null,
					finalizer,
				),
			]),
		);
		body.splice(
			index,
			1,
			forLoop,
			t.returnStatement(t.cloneNode(receiver, true)),
		);
		return true;
	}
	return false;
}

function singleLetDeclarator(
	stmt: t.Statement | undefined,
): { id: t.Identifier; init: t.Expression | null } | null {
	if (
		!stmt ||
		!t.isVariableDeclaration(stmt, { kind: 'let' }) ||
		stmt.declarations.length !== 1
	) return null;
	const [decl] = stmt.declarations;
	if (!t.isIdentifier(decl.id)) return null;
	return {
		id: t.cloneNode(decl.id),
		init: t.isExpression(decl.init) ? t.cloneNode(decl.init, true) : null,
	};
}

function loopBoundFromBreakGuard(stmt: t.Statement | undefined) {
	if (
		!stmt ||
		!t.isIfStatement(stmt) ||
		!t.isUnaryExpression(stmt.test, { operator: '!' }) ||
		!t.isBinaryExpression(stmt.test.argument, { operator: '<' }) ||
		!t.isExpression(stmt.test.argument.right)
	) return null;
	return t.cloneNode(stmt.test.argument.right, true);
}

function numericComparisonValue(
	expr: t.Expression,
	operator: '===' | '!==',
): t.NumericLiteral | null {
	let found: t.NumericLiteral | null = null;
	t.traverseFast(expr, (node) => {
		if (found) return t.traverseFast.skip;
		if (!t.isBinaryExpression(node, { operator })) return;
		if (t.isNumericLiteral(node.left)) found = t.cloneNode(node.left);
		if (t.isNumericLiteral(node.right)) found = t.cloneNode(node.right);
	});
	return found;
}

export function repairNestedLabelledBreakLoops(body: t.Statement[]): boolean {
	for (let index = 0; index < body.length - 2; index++) {
		const arrayDecl = body[index];
		const outerDecl = singleLetDeclarator(body[index + 1]);
		const outerLoop = body[index + 2];
		if (
			!t.isVariableDeclaration(arrayDecl) ||
			arrayDecl.declarations.length !== 1 ||
			!t.isIdentifier(arrayDecl.declarations[0].id) ||
			!outerDecl ||
			!t.isWhileStatement(outerLoop) ||
			!t.isBooleanLiteral(outerLoop.test, { value: true }) ||
			!t.isBlockStatement(outerLoop.body)
		) continue;
		const resultName = t.cloneNode(arrayDecl.declarations[0].id);
		const outerBody = outerLoop.body.body;
		const innerDecl = singleLetDeclarator(outerBody[0]);
		const innerLoop = outerBody[1];
		const outerBound = loopBoundFromBreakGuard(outerBody.at(-1));
		if (
			!innerDecl ||
			!t.isWhileStatement(innerLoop) ||
			!t.isBooleanLiteral(innerLoop.test, { value: true }) ||
			!t.isBlockStatement(innerLoop.body) ||
			!outerBound
		) continue;
		const innerBody = innerLoop.body.body;
		const pushStmt = innerBody.find((stmt) =>
			t.isExpressionStatement(stmt) &&
			t.isCallExpression(stmt.expression) &&
			t.isMemberExpression(stmt.expression.callee, {
				computed: false,
			}) &&
			t.isIdentifier(stmt.expression.callee.property, { name: 'push' })
		);
		const returnGuard = innerBody.find((stmt) =>
			t.isIfStatement(stmt) &&
			t.isBlockStatement(stmt.consequent) &&
			stmt.consequent.body.some((inner) =>
				t.isReturnStatement(inner) &&
				t.isIdentifier(inner.argument, { name: resultName.name })
			)
		);
		const innerBound = loopBoundFromBreakGuard(innerBody.at(-1));
		if (!pushStmt || !t.isIfStatement(returnGuard) || !innerBound) {
			continue;
		}
		const outerBreakValue = numericComparisonValue(returnGuard.test, '===');
		const innerBreakValue = numericComparisonValue(returnGuard.test, '!==');
		if (!outerBreakValue || !innerBreakValue) continue;

		const pushCall = (pushStmt as t.ExpressionStatement).expression;
		if (!t.isCallExpression(pushCall)) continue;
		const pushArg = pushCall.arguments[0];
		if (!t.isExpression(pushArg)) continue;

		const innerFor = t.forStatement(
			t.variableDeclaration('let', [
				t.variableDeclarator(
					t.cloneNode(innerDecl.id),
					innerDecl.init ?? t.numericLiteral(0),
				),
			]),
			t.binaryExpression(
				'<',
				t.cloneNode(innerDecl.id),
				t.cloneNode(innerBound, true),
			),
			t.updateExpression('++', t.cloneNode(innerDecl.id)),
			t.blockStatement([
				t.expressionStatement(t.callExpression(
					t.memberExpression(
						t.cloneNode(resultName),
						t.identifier('push'),
					),
					[
						t.isBinaryExpression(pushArg, { operator: '+' }) &&
							t.isBinaryExpression(pushArg.left, {
								operator: '*',
							})
							? t.binaryExpression(
								'+',
								t.cloneNode(pushArg.left, true),
								t.cloneNode(innerDecl.id),
							)
							: t.cloneNode(pushArg, true),
					],
				)),
				t.ifStatement(
					t.logicalExpression(
						'&&',
						t.binaryExpression(
							'===',
							t.cloneNode(outerDecl.id),
							t.cloneNode(outerBreakValue),
						),
						t.binaryExpression(
							'===',
							t.cloneNode(innerDecl.id),
							t.cloneNode(innerBreakValue),
						),
					),
					t.blockStatement([t.breakStatement(t.identifier('outer'))]),
				),
			]),
		);
		const outerFor = t.labeledStatement(
			t.identifier('outer'),
			t.forStatement(
				t.variableDeclaration('let', [
					t.variableDeclarator(
						t.cloneNode(outerDecl.id),
						outerDecl.init ?? t.numericLiteral(0),
					),
				]),
				t.binaryExpression(
					'<',
					t.cloneNode(outerDecl.id),
					t.cloneNode(outerBound, true),
				),
				t.updateExpression('++', t.cloneNode(outerDecl.id)),
				t.blockStatement([innerFor]),
			),
		);
		body.splice(
			index + 1,
			2,
			outerFor,
			t.returnStatement(t.cloneNode(resultName)),
		);
		return true;
	}
	return false;
}
