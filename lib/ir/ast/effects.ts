import * as t from '@babel/types';

export function nodeHasDelegateYield(value: unknown): boolean {
	if (t.isCallExpression(value as t.Node)) {
		const call = value as t.CallExpression;
		if (t.isV8IntrinsicIdentifier(call.callee, { name: 'DelegateYield' })) {
			return true;
		}
	}
	if (Array.isArray(value)) return value.some(nodeHasDelegateYield);
	if (typeof value !== 'object' || value === null) return false;
	return Object.values(value).some(nodeHasDelegateYield);
}

export function nodeMaySuspend(value: unknown): boolean {
	if (t.isYieldExpression(value as t.Node)) return true;
	if (nodeHasDelegateYield(value)) return true;
	if (Array.isArray(value)) return value.some(nodeMaySuspend);
	if (typeof value !== 'object' || value === null) return false;
	return Object.values(value).some(nodeMaySuspend);
}

export function statementsMaySuspend(
	body: readonly t.Statement[],
): boolean {
	return body.some(nodeMaySuspend);
}
