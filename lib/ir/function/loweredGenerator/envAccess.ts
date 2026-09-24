import * as t from '@babel/types';

export function isEnvMember(
	expr: t.Expression | null | undefined,
): expr is t.MemberExpression {
	return t.isMemberExpression(expr) &&
		expr.computed &&
		t.isCallExpression(expr.object) &&
		t.isV8IntrinsicIdentifier(expr.object.callee, {
			name: 'expectEnvironment',
		}) &&
		t.isNumericLiteral(expr.property);
}

export function loadEnvironmentCall(expr: t.Expression) {
	if (!isEnvMember(expr)) return;
	const [env] = (expr.object as t.CallExpression).arguments;
	if (!t.isExpression(env)) return;
	return { env, slot: (expr.property as t.NumericLiteral).value };
}

export function storeEnvironmentCall(expr: t.Expression) {
	if (!t.isAssignmentExpression(expr, { operator: '=' })) return;
	if (!isEnvMember(expr.left as t.Expression)) return;
	const lhs = expr.left as t.MemberExpression;
	const [env] = (lhs.object as t.CallExpression).arguments;
	if (!t.isExpression(env) || !t.isExpression(expr.right)) return;
	return {
		env,
		slot: (lhs.property as t.NumericLiteral).value,
		value: expr.right,
	};
}

export function environmentStoreFromStatement(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return;
	return storeEnvironmentCall(stmt.expression);
}
