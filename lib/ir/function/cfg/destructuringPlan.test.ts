import { strict as assert } from 'node:assert';
import generate from '@babel/generator';
import * as t from '@babel/types';
import {
	containsDestructuringProtocol,
	destructuringSourceDefault,
	destructuringUndefinedAliases,
} from './destructuringPlan.ts';

Deno.test('destructuring source defaults accept inverted undefined aliases', () => {
	const source = t.identifier('_param_7_0_');
	const alias = t.identifier('r1_1');
	const body = t.blockStatement([
		t.variableDeclaration('const', [
			t.variableDeclarator(t.cloneNode(alias), t.identifier('undefined')),
		]),
	]);
	const init = t.conditionalExpression(
		t.unaryExpression(
			'!',
			t.binaryExpression(
				'===',
				t.cloneNode(source),
				t.cloneNode(alias),
			),
		),
		t.cloneNode(source),
		t.callExpression(t.identifier('makeDefault'), []),
	);

	const result = destructuringSourceDefault(
		init,
		source.name,
		destructuringUndefinedAliases(body),
	);
	assert.ok(result);
	assert.equal(generate(result.defaultValue).code, 'makeDefault()');
});

Deno.test('destructuring source defaults reject a parameter in the default arm', () => {
	const source = t.identifier('_param_8_0_');
	const init = t.conditionalExpression(
		t.binaryExpression(
			'===',
			t.cloneNode(source),
			t.identifier('undefined'),
		),
		t.cloneNode(source),
		t.objectExpression([]),
	);
	assert.equal(destructuringSourceDefault(init, source.name), null);
});

Deno.test('destructuring protocol detection covers iterator and object rest', () => {
	const iterator = t.callExpression(
		t.v8IntrinsicIdentifier('IteratorBegin'),
		[t.identifier('input')],
	);
	const objectRest = t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		[
			t.objectExpression([]),
			t.identifier('input'),
			t.identifier('excluded'),
		],
	);
	assert.equal(containsDestructuringProtocol(iterator), true);
	assert.equal(containsDestructuringProtocol(objectRest), true);
	assert.equal(
		containsDestructuringProtocol(
			t.variableDeclarator(
				t.objectPattern([t.objectProperty(
					t.identifier('value'),
					t.identifier('value'),
					false,
					true,
				)]),
				t.identifier('input'),
			),
		),
		false,
	);
});
