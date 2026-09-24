import { strict as assert } from 'node:assert';
import * as t from '@babel/types';
import {
	statementAlwaysTerminates,
	stripOwnedAdjacentRethrowFinalizerCopies,
	stripOwnedTerminalEnclosingFinalizerCopies,
} from './finalizer.ts';

function marker(value: string): t.ExpressionStatement {
	return t.expressionStatement(t.stringLiteral(value));
}

Deno.test('owned adjacent finalizer cleanup requires HandlerGraph evidence', () => {
	const canonical = t.tryStatement(
		t.blockStatement([marker('inner')]),
		t.catchClause(t.identifier('error'), t.blockStatement([])),
		t.blockStatement([marker('outer')]),
	);
	const owner = t.tryStatement(
		t.blockStatement([]),
		null,
		t.blockStatement([canonical]),
	);
	const rethrowing = t.tryStatement(
		t.blockStatement([
			marker('inner'),
			t.throwStatement(t.identifier('error')),
		]),
		t.catchClause(t.identifier('error'), t.blockStatement([])),
	);
	const copy = t.tryStatement(
		t.blockStatement([rethrowing]),
		null,
		t.blockStatement([marker('outer')]),
	);
	const body: t.Statement[] = [owner, copy];

	assert.equal(stripOwnedAdjacentRethrowFinalizerCopies(body, 0), false);
	assert.equal(body.length, 2);
	assert.equal(stripOwnedAdjacentRethrowFinalizerCopies(body, 1), true);
	assert.deepEqual(body, [owner]);
});

Deno.test('owned terminal finalizer cleanup requires HandlerGraph evidence', () => {
	const copy = t.tryStatement(
		t.blockStatement([
			marker('outer'),
			t.returnStatement(t.numericLiteral(22)),
		]),
		null,
		t.blockStatement([]),
	);
	const owner = t.tryStatement(
		t.blockStatement([copy]),
		null,
		t.blockStatement([
			marker('outer'),
			t.returnStatement(t.numericLiteral(22)),
		]),
	);
	const body: t.Statement[] = [owner];

	assert.equal(stripOwnedTerminalEnclosingFinalizerCopies(body, 0), false);
	assert.equal(owner.block.body.length, 1);
	assert.equal(
		stripOwnedTerminalEnclosingFinalizerCopies(body, 1),
		true,
	);
	assert.equal(owner.block.body.length, 0);
});

Deno.test('terminal analysis covers exhaustive switch fallthrough', () => {
	const statement = t.switchStatement(t.identifier('value'), [
		t.switchCase(t.numericLiteral(0), [t.returnStatement()]),
		t.switchCase(t.numericLiteral(1), []),
		t.switchCase(t.numericLiteral(2), [t.throwStatement(
			t.identifier('error'),
		)]),
		t.switchCase(null, [t.returnStatement()]),
	]);

	assert.equal(statementAlwaysTerminates(statement), true);
	statement.cases[1].consequent.push(t.breakStatement());
	assert.equal(statementAlwaysTerminates(statement), false);
});

Deno.test('terminal analysis covers unbroken infinite loops', () => {
	const loop = t.whileStatement(
		t.booleanLiteral(true),
		t.blockStatement([
			t.ifStatement(
				t.identifier('done'),
				t.returnStatement(),
				t.continueStatement(),
			),
		]),
	);

	assert.equal(statementAlwaysTerminates(loop), true);
	assert.ok(t.isBlockStatement(loop.body));
	loop.body.body.push(t.breakStatement());
	assert.equal(statementAlwaysTerminates(loop), false);
});
