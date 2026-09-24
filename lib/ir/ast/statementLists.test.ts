import { strict as assert } from 'node:assert';
import * as t from '@babel/types';
import { rewriteStructuredStatementLists } from './statementLists.ts';

Deno.test('structured statement-list rewriting is post-order and skips functions', () => {
	const consequent = [t.emptyStatement()];
	const alternate = [t.emptyStatement()];
	const loopBody = [t.emptyStatement()];
	const tryBody = [t.emptyStatement()];
	const catchBody = [t.emptyStatement()];
	const finalizerBody = [t.emptyStatement()];
	const switchBody = [t.emptyStatement()];
	const functionBody = [t.emptyStatement()];
	const body: t.Statement[] = [
		t.ifStatement(
			t.identifier('condition'),
			t.blockStatement(consequent),
			t.blockStatement(alternate),
		),
		t.doWhileStatement(
			t.identifier('condition'),
			t.blockStatement(loopBody),
		),
		t.tryStatement(
			t.blockStatement(tryBody),
			t.catchClause(null, t.blockStatement(catchBody)),
			t.blockStatement(finalizerBody),
		),
		t.switchStatement(t.identifier('value'), [
			t.switchCase(null, switchBody),
		]),
		t.functionDeclaration(
			t.identifier('nested'),
			[],
			t.blockStatement(functionBody),
		),
	];
	const visited: t.Statement[][] = [];

	const changed = rewriteStructuredStatementLists(body, (statements) => {
		visited.push(statements);
		return false;
	});

	assert.equal(changed, false);
	for (
		const nested of [
			consequent,
			alternate,
			loopBody,
			tryBody,
			catchBody,
			finalizerBody,
			switchBody,
		]
	) {
		assert.ok(visited.includes(nested));
		assert.ok(visited.indexOf(nested) < visited.indexOf(body));
	}
	assert.equal(visited.includes(functionBody), false);
	assert.equal(visited.at(-1), body);
});

Deno.test('structured statement-list rewriting propagates nested changes', () => {
	const nested = [t.emptyStatement()];
	const body = [t.blockStatement(nested)];

	const changed = rewriteStructuredStatementLists(body, (statements) => {
		const filtered = statements.filter((statement) =>
			!t.isEmptyStatement(statement)
		);
		if (filtered.length === statements.length) return false;
		statements.splice(0, statements.length, ...filtered);
		return true;
	});

	assert.equal(changed, true);
	assert.deepEqual(nested, []);
});
