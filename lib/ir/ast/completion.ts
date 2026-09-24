import * as t from '@babel/types';

export function isAbruptStatement(stmt: t.Statement | undefined): boolean {
	return !!stmt && (
		t.isReturnStatement(stmt) ||
		t.isThrowStatement(stmt) ||
		t.isContinueStatement(stmt) ||
		t.isBreakStatement(stmt)
	);
}

export function statementListEndsAbruptly(stmts: t.Statement[]): boolean {
	const last = stmts.at(-1);
	if (!last) return false;
	if (isAbruptStatement(last)) return true;
	if (t.isSwitchStatement(last)) {
		return last.cases.length > 0 &&
			last.cases.every((c) => statementListEndsAbruptly(c.consequent));
	}
	if (t.isIfStatement(last)) {
		const consequent = t.isBlockStatement(last.consequent)
			? last.consequent.body
			: [last.consequent];
		const alternate = last.alternate
			? (t.isBlockStatement(last.alternate)
				? last.alternate.body
				: [last.alternate])
			: [];
		return alternate.length > 0 &&
			statementListEndsAbruptly(consequent) &&
			statementListEndsAbruptly(alternate);
	}
	if (t.isTryStatement(last)) {
		return statementListEndsAbruptly(last.block.body);
	}
	return false;
}
