import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import { environmentStoreFromStatement, isEnvMember } from './envAccess.ts';
import { yieldExpressionStatementValue } from './caseUtils.ts';
import { roleStateControlSlots } from './recognition.ts';
import type { StateRoles } from './types.ts';

export function isLoadFromEnvironmentCall(
	expr: t.Expression | null | undefined,
): expr is t.MemberExpression {
	return isEnvMember(expr);
}

export function makeCatchStatement(address: number) {
	return t.variableDeclaration('const', [
		t.variableDeclarator(
			t.identifier(`r_catch_${address}`),
			t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
		),
	]);
}

export function environmentCallSlot(member: t.MemberExpression) {
	return (member.property as t.NumericLiteral).value;
}

export function environmentStoreStatementSlot(stmt: t.Statement) {
	return environmentStoreFromStatement(stmt)?.slot;
}

function isEnvironmentLoadExpressionStatement(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return false;
	return isLoadFromEnvironmentCall(stmt.expression);
}

export function environmentLoadDeclarationSlot(stmt: t.Statement) {
	if (!t.isVariableDeclaration(stmt)) return;
	const decl = stmt.declarations[0];
	if (!t.isVariableDeclarator(decl)) return;
	if (!isLoadFromEnvironmentCall(decl.init)) return;
	return environmentCallSlot(decl.init);
}

function isStateMachineEnvironmentSlot(
	slot: number | undefined,
	roles: StateRoles,
) {
	return slot != null && roleStateControlSlots(roles).has(slot);
}

function isStateMachineEnvironmentLoadDeclaration(
	stmt: t.Statement,
	roles: StateRoles,
) {
	const slot = environmentLoadDeclarationSlot(stmt);
	return isStateMachineEnvironmentSlot(slot, roles) &&
		slot !== roles.caughtExceptionSlot;
}

export function stripLoweredGeneratorEnvironmentScaffolding(
	body: t.Statement[],
	roles: StateRoles,
) {
	const catchAliasForBody = (statements: t.Statement[]) => {
		const first = statements[0];
		if (!t.isVariableDeclaration(first)) return;
		const decl = first.declarations[0];
		if (!t.isVariableDeclarator(decl) || !t.isIdentifier(decl.id)) return;
		if (!decl.id.name.startsWith('r_catch_')) return;
		return decl.id;
	};

	const stripBlock = (
		statements: t.Statement[],
		catchAlias?: t.Identifier,
	) => {
		for (const stmt of statements) {
			if (t.isBlockStatement(stmt)) stmt.body = stripBlock(stmt.body);
			if (t.isTryStatement(stmt)) {
				stmt.block.body = stripBlock(stmt.block.body);
				if (stmt.handler) {
					const alias = catchAliasForBody(stmt.handler.body.body) ??
						(t.isIdentifier(stmt.handler.param)
							? stmt.handler.param
							: undefined);
					stmt.handler.body.body = stripBlock(
						stmt.handler.body.body,
						alias,
					);
				}
				if (stmt.finalizer) {
					stmt.finalizer.body = stripBlock(stmt.finalizer.body);
				}
			}
			if (
				catchAlias &&
				environmentLoadDeclarationSlot(stmt) ===
					roles.caughtExceptionSlot
			) {
				const decl = (stmt as t.VariableDeclaration).declarations[0];
				if (t.isVariableDeclarator(decl)) {
					decl.init = t.cloneNode(catchAlias);
				}
			}
			if (catchAlias) {
				const wrapped = t.file(t.program([stmt]));
				traverse(wrapped, {
					MemberExpression(path: NodePath<t.MemberExpression>) {
						if (!isLoadFromEnvironmentCall(path.node)) return;
						const slot = environmentCallSlot(path.node);
						if (slot !== roles.caughtExceptionSlot) return;
						path.replaceWith(t.cloneNode(catchAlias));
					},
				});
			}
		}
		return statements.filter((stmt) => {
			if (yieldExpressionStatementValue(stmt)) return true;
			if (
				t.isExpressionStatement(stmt) &&
				t.isCallExpression(stmt.expression) &&
				t.isV8IntrinsicIdentifier(stmt.expression.callee, {
					name: 'CreateTopLevelEnvironment',
				})
			) return false;
			return !isStateMachineEnvironmentSlot(
				environmentStoreStatementSlot(stmt),
				roles,
			) &&
				!isEnvironmentLoadExpressionStatement(stmt) &&
				!(catchAlias == null &&
					isStateMachineEnvironmentLoadDeclaration(stmt, roles));
		});
	};
	return stripBlock(body);
}
