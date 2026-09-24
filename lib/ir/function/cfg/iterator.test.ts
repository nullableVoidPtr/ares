import { strict as assert } from 'node:assert';
import generate from '@babel/generator';
import * as t from '@babel/types';
import {
	cleanupLocalIteratorForOfLoops,
	cleanupLocalPNameForInLoops,
	cleanupLocalSyncIteratorForOfLoops,
} from './iterator.ts';

function intrinsic(name: string, args: t.Expression[] = []) {
	return t.callExpression(t.v8IntrinsicIdentifier(name), args);
}

function declaration(name: string, init: t.Expression) {
	return t.variableDeclaration('const', [
		t.variableDeclarator(t.identifier(name), init),
	]);
}

function multiDeclaration(names: string[], init: t.Expression) {
	return t.variableDeclaration('const', [
		t.variableDeclarator(
			t.arrayPattern(names.map((name) => t.identifier(name))),
			init,
		),
	]);
}

function assignment(name: string, value: t.Expression) {
	return t.expressionStatement(t.assignmentExpression(
		'=',
		t.identifier(name),
		value,
	));
}

function ensureObject(name: string) {
	return t.expressionStatement(t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('ensureObject'),
		),
		[t.identifier(name), t.stringLiteral('expected object')],
	));
}

function awaitIterator(name: string) {
	return t.awaitExpression(t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('awaitAsyncIterator'),
		),
		[t.identifier(name)],
	));
}

Deno.test('local PName recovery consumes lowered generator aliases', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([
				t.identifier('r5_8'),
				t.identifier('r8_3'),
				t.identifier('r9_2'),
			]),
			intrinsic('GetPNameList', [t.identifier('source')]),
		)]),
		t.ifStatement(
			t.binaryExpression(
				'===',
				t.identifier('r5_8'),
				t.identifier('undefined'),
			),
			t.blockStatement([]),
			t.blockStatement([
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier('r11_2')),
					t.variableDeclarator(t.identifier('r14_2')),
				]),
				t.variableDeclaration('let', [t.variableDeclarator(
					t.identifier('r1000004_3'),
					t.identifier('r5_8'),
				)]),
				t.variableDeclaration('let', [t.variableDeclarator(
					t.identifier('r1000003_3'),
					t.identifier('r8_3'),
				)]),
				t.variableDeclaration('let', [t.variableDeclarator(
					t.identifier('r1000002_3'),
					t.identifier('r9_2'),
				)]),
				t.variableDeclaration('let', [t.variableDeclarator(
					t.identifier('r1000001_4'),
					t.identifier('source'),
				)]),
				t.whileStatement(
					t.booleanLiteral(true),
					t.blockStatement([
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.arrayPattern([
								t.identifier('r14_2'),
								t.identifier('r11_2'),
							]),
							intrinsic('GetNextPName', [
								t.identifier('r1000004_3'),
								t.identifier('r1000001_4'),
								t.identifier('r1000003_3'),
							]),
						)),
						t.ifStatement(
							t.binaryExpression(
								'===',
								t.identifier('r14_2'),
								t.identifier('undefined'),
							),
							t.blockStatement([t.breakStatement()]),
						),
						assignment('r1000002_3', t.identifier('r1000002_3')),
						assignment('r1000003_3', t.identifier('r1000003_3')),
						assignment('r1000001_4', t.identifier('r11_2')),
						assignment('r1000004_3', t.identifier('r1000004_3')),
						assignment('prop', t.identifier('r14_2')),
						t.expressionStatement(
							t.yieldExpression(t.memberExpression(
								t.identifier('source'),
								t.identifier('prop'),
								true,
							)),
						),
					]),
				),
			]),
		),
	];

	assert.equal(cleanupLocalPNameForInLoops(body), true);
	const code = generate(t.program(body)).code;
	assert.doesNotMatch(code, /GetPName/);
	assert.match(code, /^for \(const r14_2 in source\) \{/);
	assert.match(code, /prop = r14_2;\n  yield source\[prop\];/);
});

Deno.test('local async iterator recovery preserves a break condition', () => {
	const iterator = 'r18_29';
	const next = 'r18_34';
	const result = 'r0_7';
	const value = 'r19_6';
	const method = 'r19_9';
	const closeResult = 'r0_8';
	const body: t.Statement[] = [
		declaration(
			iterator,
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('makeAsyncIterator'),
				),
				[t.callExpression(t.identifier('source'), [])],
			),
		),
		declaration(
			next,
			t.callExpression(
				t.memberExpression(
					t.identifier(iterator),
					t.identifier('next'),
				),
				[],
			),
		),
		ensureObject(next),
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier(result), awaitIterator(next)),
		]),
		t.whileStatement(
			t.booleanLiteral(true),
			t.blockStatement([
				t.ifStatement(
					t.memberExpression(
						t.identifier(result),
						t.identifier('done'),
					),
					t.blockStatement([t.breakStatement()]),
				),
				declaration(
					value,
					t.memberExpression(
						t.identifier(result),
						t.identifier('value'),
					),
				),
				t.expressionStatement(t.callExpression(
					t.memberExpression(
						t.identifier('results'),
						t.identifier('push'),
					),
					[t.identifier(value)],
				)),
				t.ifStatement(
					t.binaryExpression(
						'!==',
						t.identifier(value),
						t.numericLiteral(3),
					),
					t.blockStatement([
						declaration(
							next,
							t.callExpression(
								t.memberExpression(
									t.identifier(iterator),
									t.identifier('next'),
								),
								[],
							),
						),
						ensureObject(next),
						assignment(result, awaitIterator(next)),
						t.continueStatement(),
					]),
				),
				declaration(
					method,
					t.callExpression(
						t.memberExpression(
							t.identifier('HermesInternal'),
							t.identifier('getMethod'),
						),
						[t.identifier(iterator), t.stringLiteral('return')],
					),
				),
				t.ifStatement(
					t.binaryExpression(
						'!==',
						t.identifier(method),
						t.identifier('undefined'),
					),
					t.blockStatement([
						declaration(
							closeResult,
							t.awaitExpression(t.callExpression(
								t.memberExpression(
									t.identifier('HermesInternal'),
									t.identifier('awaitAsyncIterator'),
								),
								[t.callExpression(
									t.memberExpression(
										t.identifier(method),
										t.identifier('call'),
									),
									[t.identifier(iterator)],
								)],
							)),
						),
						ensureObject(closeResult),
						t.expressionStatement(t.yieldExpression(
							t.identifier('results'),
						)),
						t.returnStatement(),
					]),
				),
			]),
		),
	];

	assert.equal(cleanupLocalIteratorForOfLoops(body), true);
	const code = generate(t.program(body)).code;
	assert.doesNotMatch(code, /HermesInternal|while \(true\)/);
	assert.match(code, /^for await \(const r19_6 of source\(\)\) \{/);
	assert.match(code, /results\.push\(r19_6\);\n  if \(r19_6 === 3\) break;/);
	assert.match(code, /yield results;\nreturn;$/);
});

Deno.test('local sync iterator recovery handles terminal single-step loops', () => {
	const body: t.Statement[] = [
		t.ifStatement(
			t.identifier('condition'),
			t.blockStatement([
				multiDeclaration(
					['iterator', 'state'],
					intrinsic('IteratorBegin', [t.identifier('values')]),
				),
				multiDeclaration(
					['value', 'next'],
					intrinsic('IteratorNext', [
						t.identifier('iterator'),
						t.identifier('state'),
					]),
				),
				t.ifStatement(
					t.binaryExpression(
						'!==',
						t.identifier('next'),
						t.identifier('undefined'),
					),
					t.blockStatement([
						t.tryStatement(
							t.blockStatement([
								t.expressionStatement(t.callExpression(
									t.identifier('consume'),
									[t.identifier('value')],
								)),
								t.returnStatement(t.booleanLiteral(true)),
							]),
							null,
							t.blockStatement([]),
						),
					]),
				),
			]),
		),
	];

	assert.equal(cleanupLocalSyncIteratorForOfLoops(body), true);
	const code = generate(t.program(body)).code;
	assert.doesNotMatch(code, /IteratorBegin|IteratorNext/);
	assert.match(code, /for \(const value of values\) \{/);
	assert.match(code, /consume\(value\);\n    return true;/);
	assert.doesNotMatch(code, /finally/);
});

Deno.test('local sync iterator recovery handles inverted terminal single steps', () => {
	const body: t.Statement[] = [
		multiDeclaration(
			['iterator', 'state'],
			intrinsic('IteratorBegin', [t.identifier('values')]),
		),
		multiDeclaration(
			['value', 'next'],
			intrinsic('IteratorNext', [
				t.identifier('iterator'),
				t.identifier('state'),
			]),
		),
		t.ifStatement(
			t.binaryExpression(
				'===',
				t.identifier('next'),
				t.identifier('undefined'),
			),
			t.blockStatement([
				t.expressionStatement(t.callExpression(
					t.identifier('empty'),
					[],
				)),
			]),
			t.blockStatement([
				t.tryStatement(
					t.blockStatement([
						t.expressionStatement(t.callExpression(
							t.identifier('consume'),
							[t.identifier('value')],
						)),
						t.returnStatement(t.booleanLiteral(true)),
					]),
					null,
					t.blockStatement([]),
				),
			]),
		),
	];

	assert.equal(cleanupLocalSyncIteratorForOfLoops(body), true);
	const code = generate(t.program(body)).code;
	assert.doesNotMatch(code, /IteratorBegin|IteratorNext/);
	assert.match(code, /for \(const value of values\) \{/);
	assert.match(code, /consume\(value\);\n  return true;/);
	assert.match(code, /empty\(\);$/);
	assert.doesNotMatch(code, /finally/);
});

Deno.test('local sync iterator recovery rejects non-terminal single steps', () => {
	const body: t.Statement[] = [
		multiDeclaration(
			['iterator', 'state'],
			intrinsic('IteratorBegin', [t.identifier('values')]),
		),
		multiDeclaration(
			['value', 'next'],
			intrinsic('IteratorNext', [
				t.identifier('iterator'),
				t.identifier('state'),
			]),
		),
		t.ifStatement(
			t.binaryExpression(
				'!==',
				t.identifier('next'),
				t.identifier('undefined'),
			),
			t.blockStatement([
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('value')],
				)),
			]),
		),
	];

	assert.equal(cleanupLocalSyncIteratorForOfLoops(body), false);
	assert.match(
		generate(t.program(body)).code,
		/IteratorBegin[\s\S]*IteratorNext/,
	);
});
