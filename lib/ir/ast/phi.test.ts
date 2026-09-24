import { strict as assert } from 'node:assert';
import generate from '@babel/generator';
import * as t from '@babel/types';
import {
	foldConditionalValuesInBody,
	liftPhiNodesInBody,
	simplifyProvenanceResolvedPhiCalls,
	simplifyScopedPhiAssignments,
	simplifyScopedPhiDeclarations,
} from './phi.ts';
import type { LiftedAST } from './mod.ts';

function assignment(name: string, value: t.Expression): t.Statement {
	return t.expressionStatement(
		t.assignmentExpression('=', t.identifier(name), value),
	);
}

Deno.test('folds hoisted conditional Phi defaults into shortcuts', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r4_8')),
		]),
		assignment('r4_8', t.identifier('isObject')),
		t.ifStatement(
			t.identifier('isObject'),
			t.blockStatement([
				assignment('r4_8', t.identifier('isNotNull')),
			]),
		),
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r5_15')),
		]),
		assignment('r5_15', t.identifier('hasErrorTag')),
		t.ifStatement(
			t.unaryExpression('!', t.identifier('hasErrorTag')),
			t.blockStatement([
				assignment('r5_15', t.identifier('isErrorInstance')),
			]),
		),
	];

	assert.equal(foldConditionalValuesInBody(body), true);
	assert.equal(
		generate(t.program(body)).code,
		'const r4_8 = isObject && isNotNull;\n' +
			'const r5_15 = hasErrorTag || isErrorInstance;',
	);
});

Deno.test('folds complete preserved hoisted conditional values', () => {
	const preservedDecl = t.variableDeclaration('let', [
		t.variableDeclarator(t.identifier('result')),
	]) as LiftedAST<t.VariableDeclaration>;
	preservedDecl.extra = { preserveAcrossBlocks: true };
	const body: t.Statement[] = [
		preservedDecl,
		assignment('result', t.identifier('fallback')),
		t.ifStatement(
			t.binaryExpression('!=', t.nullLiteral(), t.identifier('value')),
			t.blockStatement([
				assignment('result', t.identifier('value')),
			]),
		),
	];

	assert.equal(foldConditionalValuesInBody(body), true);
	assert.equal(
		generate(t.program(body)).code,
		'const result = value ?? fallback;',
	);
});

Deno.test('folds hoisted identifier defaults into ternaries', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('result')),
		]),
		assignment('result', t.identifier('fallback')),
		t.ifStatement(
			t.identifier('condition'),
			t.blockStatement([
				assignment(
					'result',
					t.callExpression(t.identifier('make'), []),
				),
			]),
		),
	];

	assert.equal(foldConditionalValuesInBody(body), true);
	assert.equal(
		generate(t.program(body)).code,
		'const result = condition ? make() : fallback;',
	);
});

Deno.test('falls back to ternary for undefined guarded calls', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('result')),
		]),
		assignment('result', t.identifier('undefined')),
		t.ifStatement(
			t.binaryExpression(
				'!=',
				t.nullLiteral(),
				t.memberExpression(
					t.identifier('source'),
					t.identifier('field'),
				),
			),
			t.blockStatement([
				assignment(
					'result',
					t.callExpression(t.identifier('fromServer'), [
						t.memberExpression(
							t.identifier('source'),
							t.identifier('field'),
						),
					]),
				),
			]),
		),
	];

	assert.equal(foldConditionalValuesInBody(body), true);
	assert.equal(
		generate(t.program(body)).code,
		'const result = null != source.field ? fromServer(source.field) : undefined;',
	);
});

Deno.test('does not relocate an effectful hoisted default', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('result')),
		]),
		assignment(
			'result',
			t.callExpression(t.identifier('defaultValue'), []),
		),
		t.ifStatement(
			t.identifier('condition'),
			t.blockStatement([
				assignment('result', t.identifier('conditionalValue')),
			]),
		),
	];

	assert.equal(foldConditionalValuesInBody(body), false);
	assert.equal(body.length, 3);
});

Deno.test('does not deduplicate an unmarked effectful shortcut guard', () => {
	const check = () => t.callExpression(t.identifier('check'), []);
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('result')),
		]),
		assignment('result', check()),
		t.ifStatement(
			check(),
			t.blockStatement([
				assignment('result', t.identifier('conditionalValue')),
			]),
		),
	];

	assert.equal(foldConditionalValuesInBody(body), false);
	assert.equal(body.length, 3);
});

Deno.test('lifts a branch Phi source across a following protected container', () => {
	const body: t.Statement[] = [
		t.ifStatement(
			t.binaryExpression(
				'===',
				t.identifier('probe'),
				t.identifier('undefined'),
			),
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('fallback'),
						t.callExpression(t.identifier('makeDefault'), []),
					),
				]),
			]),
		),
		t.tryStatement(
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('result'),
						t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
							t.identifier('probe'),
							t.identifier('fallback'),
						]),
					),
				]),
				t.expressionStatement(t.identifier('result')),
			]),
			t.catchClause(t.identifier('error'), t.blockStatement([])),
		),
	];

	assert.equal(liftPhiNodesInBody(body), true);
	assert.equal(
		generate(t.program(body)).code,
		'let result = probe;\n' +
			'if (probe === undefined) {\n' +
			'  result = makeDefault();\n' +
			'}\n' +
			'try {\n' +
			'  result;\n' +
			'} catch (error) {}',
	);
});

Deno.test('simplifies repeated identical scoped Phi sources', () => {
	const phi = () =>
		t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
			t.identifier('source'),
			t.identifier('source'),
			t.identifier('source'),
		]);
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('source')),
		]),
		t.tryStatement(
			t.blockStatement([]),
			t.catchClause(
				t.identifier('error'),
				t.blockStatement([
					t.variableDeclaration('const', [
						t.variableDeclarator(t.identifier('declared'), phi()),
					]),
					assignment('assigned', phi()),
				]),
			),
		),
	];

	assert.equal(simplifyScopedPhiDeclarations(body), true);
	assert.equal(simplifyScopedPhiAssignments(body), true);
	assert.equal(
		generate(t.program(body)).code,
		'let source;\n' +
			'try {} catch (error) {\n' +
			'  const declared = source;\n' +
			'  assigned = source;\n' +
			'}',
	);
});

Deno.test('resolves repeated out-of-scope Phi sources from SSA provenance', () => {
	const body: t.Statement[] = [
		t.tryStatement(
			t.blockStatement([]),
			t.catchClause(
				t.identifier('error'),
				t.blockStatement([
					assignment(
						'result',
						t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
							t.identifier('r1_1'),
							t.identifier('r1_1'),
						]),
					),
				]),
			),
		),
	];

	assert.equal(
		simplifyProvenanceResolvedPhiCalls(
			body,
			(name) => name === 'r1_1' ? t.identifier('undefined') : null,
		),
		true,
	);
	assert.doesNotMatch(generate(t.program(body)).code, /%Phi|r1_1/);
});

Deno.test('folds a cached receiver ladder into an optional method chain', () => {
	const declaration = t.variableDeclaration('let', [
		t.variableDeclarator(t.identifier('result')),
	]) as LiftedAST<t.VariableDeclaration>;
	declaration.extra = { isPotentialConditionalValue: true };
	const setResult = (value: t.Expression) => assignment('result', value);
	const body: t.Statement[] = [
		declaration,
		t.ifStatement(
			t.binaryExpression('==', t.identifier('base'), t.nullLiteral()),
			t.blockStatement([setResult(t.identifier('undefined'))]),
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('cached'),
						t.memberExpression(
							t.identifier('base'),
							t.identifier('child'),
						),
					),
				]),
				t.ifStatement(
					t.binaryExpression(
						'==',
						t.identifier('cached'),
						t.nullLiteral(),
					),
					t.blockStatement([setResult(t.identifier('undefined'))]),
					t.blockStatement([
						t.ifStatement(
							t.binaryExpression(
								'==',
								t.memberExpression(
									t.identifier('cached'),
									t.identifier('method'),
								),
								t.nullLiteral(),
							),
							t.blockStatement([
								setResult(t.identifier('undefined')),
							]),
							t.blockStatement([
								setResult(t.callExpression(
									t.memberExpression(
										t.identifier('cached'),
										t.identifier('method'),
									),
									[],
								)),
							]),
						),
					]),
				),
			]),
		),
	];

	assert.equal(foldConditionalValuesInBody(body), true);
	assert.equal(
		generate(t.program(body)).code,
		'const result = base?.child?.method?.();',
	);
});

Deno.test('folds self-referential cached conditional receiver once', () => {
	const decl = t.variableDeclaration('let', [
		t.variableDeclarator(
			t.identifier('result'),
			t.identifier('fallback'),
		),
	]) as LiftedAST<t.VariableDeclaration>;
	decl.extra = { isPotentialConditionalValue: true };
	const body: t.Statement[] = [
		decl,
		t.ifStatement(
			t.identifier('condition'),
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r0_1'),
						t.memberExpression(
							t.identifier('r0_1'),
							t.identifier('child'),
						),
					),
				]),
				t.ifStatement(
					t.binaryExpression(
						'==',
						t.identifier('r0_1'),
						t.nullLiteral(),
					),
					t.blockStatement([
						assignment('result', t.identifier('undefined')),
					]),
					t.blockStatement([
						assignment(
							'result',
							t.memberExpression(
								t.identifier('r0_1'),
								t.identifier('value'),
							),
						),
					]),
				),
			]),
		),
	];

	assert.equal(foldConditionalValuesInBody(body), true);
	assert.equal(
		generate(t.program(body)).code,
		'const result = condition ? r0_1.child?.value : fallback;',
	);
});

Deno.test('preserves loop Phi destinations used outside a reduced CFG block', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r1_1'),
				t.identifier('initial'),
			),
		]),
		t.whileStatement(
			t.booleanLiteral(true),
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r1_2'),
						t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
							t.identifier('r1_1'),
							t.identifier('r1_3'),
						]),
					),
				]),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r1_3'),
						t.callExpression(t.identifier('next'), [
							t.identifier('r1_2'),
						]),
					),
				]),
			]),
		),
		t.returnStatement(t.identifier('r1_2')),
	];

	assert.equal(liftPhiNodesInBody(body), true);
	assert.equal(
		generate(t.program(body)).code,
		'const r1_1 = initial;\n' +
			'let r1_2 = r1_1;\n' +
			'while (true) {\n' +
			'  r1_2 = next(r1_2);\n' +
			'}\n' +
			'return r1_2;',
	);
});
