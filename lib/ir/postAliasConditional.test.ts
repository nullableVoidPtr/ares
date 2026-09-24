import { strict as assert } from 'node:assert';
import generate from '@babel/generator';
import * as t from '@babel/types';
import { refoldPostAliasConditionalValues } from './lift.ts';

Deno.test('post-alias cleanup restores nullish values without dropping functions', () => {
	const value = t.identifier('value');
	const func = t.functionExpression(
		null,
		[t.cloneNode(value)],
		t.blockStatement([
			t.expressionStatement(t.binaryExpression(
				'==',
				t.nullLiteral(),
				t.cloneNode(value),
			)),
			t.returnStatement(t.conditionalExpression(
				t.binaryExpression(
					'==',
					t.nullLiteral(),
					t.cloneNode(value),
				),
				t.thisExpression(),
				t.cloneNode(value),
			)),
		]),
	);
	const file = t.file(t.program([t.expressionStatement(func)]));

	refoldPostAliasConditionalValues(file);

	assert.equal(
		generate(file).code,
		'(function (value) {\n  return value ?? this;\n});',
	);
});
