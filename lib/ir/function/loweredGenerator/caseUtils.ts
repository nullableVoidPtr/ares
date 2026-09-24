import * as t from '@babel/types';
import { isUndefinedNode } from '../../ast/utils.ts';
import type { IRFunction } from '../mod.ts';
import type { CaseInfo } from './types.ts';

export function caseBodies(info: CaseInfo) {
	return info.blocks
		? [...info.blocks.values()].map((block) => block.body)
		: [info.body];
}

export function yieldExpressionStatementValue(
	stmt: t.Statement | null | undefined,
) {
	if (t.isVariableDeclaration(stmt) && stmt.declarations.length === 1) {
		const declaration = stmt.declarations[0];
		if (
			t.isVariableDeclarator(declaration) &&
			t.isYieldExpression(declaration.init)
		) return declaration.init;
	}
	if (!t.isExpressionStatement(stmt)) return;
	let expression: t.Expression = stmt.expression;
	while (
		t.isAssignmentExpression(expression, { operator: '=' }) &&
		t.isExpression(expression.right)
	) {
		expression = expression.right;
	}
	if (t.isYieldExpression(expression)) return expression;
}

export function literalValueNode(
	func: IRFunction,
	value: unknown,
): t.Expression | null {
	if (typeof value === 'undefined') return t.identifier('undefined');
	if (
		value && typeof value === 'object' && 'stringTableIndex' in value &&
		typeof (value as { stringTableIndex: unknown }).stringTableIndex ===
			'number'
	) {
		return t.stringLiteral(
			func.file.getString(
				(value as { stringTableIndex: number }).stringTableIndex,
			),
		);
	}
	const node = t.valueToNode(value);
	return t.isExpression(node) ? node : null;
}

export function memberPropertyName(member: t.MemberExpression) {
	if (!member.computed && t.isIdentifier(member.property)) {
		return member.property.name;
	}
	if (t.isStringLiteral(member.property)) {
		return member.property.value;
	}
}

export function objectPropertyExpressionValue(
	object: t.ObjectExpression,
	name: string,
) {
	for (const property of object.properties) {
		if (!t.isObjectProperty(property)) continue;
		const key = t.isIdentifier(property.key)
			? property.key.name
			: t.isStringLiteral(property.key)
			? property.key.value
			: undefined;
		if (key !== name || !t.isExpression(property.value)) continue;
		return property.value;
	}
}

export function iteratorResultTerminalFromBody(body: t.Statement[]) {
	const ret = body.findLast((stmt) => t.isReturnStatement(stmt));
	if (!t.isReturnStatement(ret) || !t.isIdentifier(ret.argument)) return;
	const resultName = ret.argument.name;
	let value: t.Expression | null | undefined;
	let done: t.Expression | null | undefined;

	const isResultScaffolding = (stmt: t.Statement) => {
		if (stmt === ret) return true;
		if (t.isVariableDeclaration(stmt)) {
			const decl = stmt.declarations[0];
			if (
				t.isVariableDeclarator(decl) &&
				t.isIdentifier(decl.id, { name: resultName }) &&
				t.isObjectExpression(decl.init)
			) {
				value = objectPropertyExpressionValue(decl.init, 'value');
				done = objectPropertyExpressionValue(decl.init, 'done');
				return true;
			}
		}
		if (!t.isExpressionStatement(stmt)) return false;
		const expr = stmt.expression;
		if (!t.isAssignmentExpression(expr, { operator: '=' })) return false;
		if (!t.isMemberExpression(expr.left)) return false;
		if (!t.isIdentifier(expr.left.object, { name: resultName })) {
			return false;
		}
		const property = memberPropertyName(expr.left);
		if (property === 'value' && t.isExpression(expr.right)) {
			value = expr.right;
			return true;
		}
		if (property === 'done' && t.isExpression(expr.right)) {
			done = expr.right;
			return true;
		}
		return false;
	};

	const stripped = body.filter((stmt) => !isResultScaffolding(stmt));
	if (t.isBooleanLiteral(done, { value: false })) {
		if (!value) return;
		return {
			terminal: t.expressionStatement(
				t.yieldExpression(t.cloneNode(value, true)),
			),
			body: stripped,
		};
	}
	if (t.isBooleanLiteral(done, { value: true })) {
		if (!value || isUndefinedNode(value) || t.isNullLiteral(value)) {
			return { terminal: t.returnStatement(), body: stripped };
		}
		return {
			terminal: t.returnStatement(t.cloneNode(value, true)),
			body: stripped,
		};
	}
	if (t.isNullLiteral(done)) {
		if (!value || isUndefinedNode(value) || t.isNullLiteral(value)) {
			return { terminal: t.returnStatement(), body: stripped };
		}
		return {
			terminal: t.returnStatement(t.cloneNode(value, true)),
			body: stripped,
		};
	}
}

export function throwTerminalFromBody(body: t.Statement[]) {
	const terminal = body.at(-1);
	if (!t.isThrowStatement(terminal)) return;
	return {
		terminal,
		body: body.slice(0, -1),
	};
}

export function caseEndsControlFlow(stmt: t.Statement) {
	return t.isReturnStatement(stmt) || t.isThrowStatement(stmt);
}

export type CaseContinuation =
	| { kind: 'none'; states: [] }
	| { kind: 'unique'; states: [number]; state: number }
	| { kind: 'multiple'; states: number[] };

/**
 * State-machine continuations reached after this case's terminal blocks.
 *
 * `CaseInfo.nextState` is only a lossless summary for a linear case. A
 * recovered case may instead contain an early return/throw plus one or more
 * yielding exits, each with its own stored state.
 */
export function caseContinuation(info: CaseInfo): CaseContinuation {
	if (!info.blocks) {
		return info.nextState == null || caseEndsControlFlow(info.terminal)
			? { kind: 'none', states: [] }
			: {
				kind: 'unique',
				states: [info.nextState],
				state: info.nextState,
			};
	}

	const states = new Set<number>();
	for (const block of info.blocks.values()) {
		if (!block.terminal || caseEndsControlFlow(block.terminal)) continue;
		const nextState = block.nextState === undefined
			? info.nextState
			: block.nextState;
		if (nextState != null) states.add(nextState);
	}
	const ordered = [...states].toSorted((left, right) => left - right);
	if (ordered.length === 0) return { kind: 'none', states: [] };
	if (ordered.length === 1) {
		return { kind: 'unique', states: [ordered[0]], state: ordered[0] };
	}
	return { kind: 'multiple', states: ordered };
}
