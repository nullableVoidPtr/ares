import * as t from '@babel/types';

export type StructuredStatementListRewriter = (
	body: t.Statement[],
) => boolean;

/**
 * Rewrite every structured statement list below `body`, followed by `body`
 * itself. Function bodies are scope boundaries and are deliberately skipped.
 */
export function rewriteStructuredStatementLists(
	body: t.Statement[],
	rewrite: StructuredStatementListRewriter,
): boolean {
	let changed = false;
	for (const statement of [...body]) {
		changed = rewriteNestedStatementLists(statement, rewrite) || changed;
	}
	return rewrite(body) || changed;
}

function rewriteNestedStatementLists(
	statement: t.Statement,
	rewrite: StructuredStatementListRewriter,
): boolean {
	if (t.isBlockStatement(statement)) {
		return rewriteStructuredStatementLists(statement.body, rewrite);
	}
	if (t.isIfStatement(statement)) {
		let changed = rewriteNestedStatementLists(
			statement.consequent,
			rewrite,
		);
		if (statement.alternate) {
			changed = rewriteNestedStatementLists(
				statement.alternate,
				rewrite,
			) || changed;
		}
		return changed;
	}
	if (t.isTryStatement(statement)) {
		let changed = rewriteStructuredStatementLists(
			statement.block.body,
			rewrite,
		);
		if (statement.handler) {
			changed = rewriteStructuredStatementLists(
				statement.handler.body.body,
				rewrite,
			) || changed;
		}
		if (statement.finalizer) {
			changed = rewriteStructuredStatementLists(
				statement.finalizer.body,
				rewrite,
			) || changed;
		}
		return changed;
	}
	if (t.isSwitchStatement(statement)) {
		let changed = false;
		for (const switchCase of statement.cases) {
			changed = rewriteStructuredStatementLists(
				switchCase.consequent,
				rewrite,
			) || changed;
		}
		return changed;
	}
	if (
		t.isWhileStatement(statement) || t.isDoWhileStatement(statement) ||
		t.isForStatement(statement) || t.isForInStatement(statement) ||
		t.isForOfStatement(statement) || t.isLabeledStatement(statement) ||
		t.isWithStatement(statement)
	) {
		return rewriteNestedStatementLists(statement.body, rewrite);
	}
	return false;
}
