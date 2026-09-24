import { strict as assert } from 'node:assert';
import generate from '@babel/generator';
import * as t from '@babel/types';
import type { IRFunction } from '../mod.ts';
import {
	reduceDelegateYieldCFG,
	reduceDelegateYieldStructuredBodies,
} from './delegateYield.ts';

function declaration(name: string, init: t.Expression) {
	return t.variableDeclaration('const', [
		t.variableDeclarator(t.identifier(name), init),
	]);
}

function intrinsic(name: string, args: t.Expression[] = []) {
	return t.callExpression(t.v8IntrinsicIdentifier(name), args);
}

function hermesCall(name: string, args: t.Expression[] = []) {
	return t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier(name),
		),
		args,
	);
}

interface TestBlock {
	address: number;
	body: t.Statement[];
	branch: null;
	consequentAddresses: number[];
}

Deno.test('delegate CFG recovery preserves a reused generator closure and its environment', () => {
	const prelude: TestBlock = {
		address: 0,
		body: [
			declaration('r1_1', intrinsic('CreateFunctionEnvironment')),
			declaration(
				'r13_1',
				intrinsic('CreateGeneratorClosure', [
					intrinsic('getFunctionById', [t.numericLiteral(2)]),
					t.identifier('r1_1'),
				]),
			),
			declaration(
				'r2_1',
				t.callExpression(
					t.memberExpression(
						t.identifier('r13_1'),
						t.identifier('call'),
					),
					[t.identifier('undefined')],
				),
			),
			declaration(
				'r1_5',
				t.memberExpression(
					t.identifier('r2_1'),
					t.memberExpression(
						t.identifier('Symbol'),
						t.identifier('iterator'),
					),
					true,
				),
			),
			declaration(
				'r3_1',
				t.callExpression(
					t.memberExpression(
						t.identifier('r1_5'),
						t.identifier('call'),
					),
					[t.identifier('r2_1')],
				),
			),
		],
		branch: null,
		consequentAddresses: [1],
	};
	const loop: TestBlock = {
		address: 1,
		body: [t.whileStatement(
			t.booleanLiteral(true),
			t.blockStatement([
				declaration(
					'r4_1',
					t.callExpression(
						t.memberExpression(
							t.identifier('r3_1'),
							t.identifier('next'),
						),
						[t.identifier('undefined')],
					),
				),
				t.expressionStatement(t.callExpression(
					t.memberExpression(
						t.identifier('HermesInternal'),
						t.identifier('ensureObject'),
					),
					[t.identifier('r4_1')],
				)),
				t.ifStatement(
					t.memberExpression(
						t.identifier('r4_1'),
						t.identifier('done'),
					),
					t.breakStatement(),
				),
				t.expressionStatement(t.callExpression(
					t.memberExpression(
						t.identifier('HermesInternal'),
						t.identifier('generatorSetDelegated'),
					),
					[],
				)),
				t.expressionStatement(t.yieldExpression(
					t.identifier('r4_1'),
				)),
			]),
		)],
		branch: null,
		consequentAddresses: [],
	};
	const laterUse: TestBlock = {
		address: 2,
		body: [t.expressionStatement(t.callExpression(
			t.identifier('r13_1'),
			[],
		))],
		branch: null,
		consequentAddresses: [],
	};
	const blocks = new Map<number, TestBlock>([
		[0, prelude],
		[1, loop],
		[2, laterUse],
	]);
	const func = {
		blocks,
		exceptions: {
			activeHandlersAtBlock: () => new Set<number>(),
			removeHandlers: () => {},
		},
		predecessorsOf: (address: number) =>
			address === 1 ? new Set([0]) : new Set<number>(),
		markMergedBlocks: () => {},
		deleteBlock: (address: number) => blocks.delete(address),
		isGenerator: false,
	} as unknown as IRFunction;

	assert.equal(reduceDelegateYieldCFG(func), true);
	const code = generate(t.program(prelude.body)).code;
	assert.match(code, /const r1_1 = %CreateFunctionEnvironment\(\)/);
	assert.match(
		code,
		/const r13_1 = %CreateGeneratorClosure\(%getFunctionById\(2\), r1_1\)/,
	);
	assert.match(code, /%DelegateYield\(r13_1\(\)\)/);
	assert.doesNotMatch(code, /const r2_1|const r1_5|const r3_1/);
});

Deno.test('structured delegate loops tolerate cached next method reads', () => {
	const body: t.Statement[] = [
		t.whileStatement(
			t.booleanLiteral(true),
			t.blockStatement([
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier('sent')),
				]),
				declaration(
					'iterator',
					t.callExpression(
						t.memberExpression(
							t.callExpression(t.identifier('values'), []),
							t.memberExpression(
								t.identifier('Symbol'),
								t.identifier('iterator'),
							),
							true,
						),
						[],
					),
				),
				t.expressionStatement(t.callExpression(
					t.memberExpression(
						t.identifier('HermesInternal'),
						t.identifier('ensureObject'),
					),
					[t.identifier('iterator')],
				)),
				declaration(
					'nextMethod',
					t.memberExpression(
						t.identifier('iterator'),
						t.identifier('next'),
					),
				),
				declaration(
					'nextResult',
					t.callExpression(
						t.memberExpression(
							t.identifier('nextMethod'),
							t.identifier('call'),
						),
						[t.identifier('iterator'), t.identifier('undefined')],
					),
				),
				t.expressionStatement(t.callExpression(
					t.memberExpression(
						t.identifier('HermesInternal'),
						t.identifier('ensureObject'),
					),
					[t.identifier('nextResult')],
				)),
				t.ifStatement(
					t.memberExpression(
						t.identifier('nextResult'),
						t.identifier('done'),
					),
					t.blockStatement([t.breakStatement()]),
				),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.identifier('sent'),
					t.yieldExpression(t.identifier('nextResult')),
				)),
			]),
		),
		t.expressionStatement(t.memberExpression(
			t.identifier('nextResult'),
			t.identifier('value'),
		)),
		t.returnStatement(),
	];

	assert.equal(
		reduceDelegateYieldStructuredBodies({
			blocks: new Map([[0, { body }]]),
		} as unknown as IRFunction),
		true,
	);
	const code = generate(t.program(body)).code;
	assert.match(code, /%DelegateYield\(values\(\)\)/);
	assert.doesNotMatch(
		code,
		/HermesInternal\.ensureObject|nextMethod|nextResult\.value/,
	);
});

Deno.test('structured delegate recovery handles protected protocol inside an outer loop', () => {
	const doneBody = t.blockStatement([
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier('completion'),
			t.identifier('result'),
		)),
		declaration(
			'value',
			t.memberExpression(
				t.identifier('completion'),
				t.identifier('value'),
			),
		),
		t.continueStatement(),
	]);
	const loop = t.whileStatement(
		t.booleanLiteral(true),
		t.blockStatement([
			declaration(
				'iterator',
				t.callExpression(
					t.memberExpression(
						t.callExpression(t.identifier('source'), []),
						t.memberExpression(
							t.identifier('Symbol'),
							t.identifier('iterator'),
						),
						true,
					),
					[],
				),
			),
			t.expressionStatement(hermesCall('ensureObject', [
				t.identifier('iterator'),
			])),
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.identifier('sent'),
				t.identifier('undefined'),
			)),
			declaration(
				'result',
				t.callExpression(
					t.memberExpression(
						t.identifier('iterator'),
						t.identifier('next'),
					),
					[t.identifier('sent')],
				),
			),
			t.expressionStatement(hermesCall('ensureObject', [
				t.identifier('result'),
			])),
			t.ifStatement(
				t.memberExpression(
					t.identifier('result'),
					t.identifier('done'),
				),
				doneBody,
			),
			t.variableDeclaration('let', [
				t.variableDeclarator(t.identifier('yielded')),
			]),
			t.tryStatement(
				t.blockStatement([
					t.expressionStatement(hermesCall('generatorSetDelegated')),
					t.expressionStatement(t.assignmentExpression(
						'=',
						t.identifier('yielded'),
						t.yieldExpression(t.identifier('result')),
					)),
				]),
				t.catchClause(
					t.identifier('_e'),
					t.blockStatement([
						t.expressionStatement(hermesCall('getMethod', [
							t.identifier('iterator'),
							t.stringLiteral('throw'),
						])),
					]),
				),
			),
		]),
	);
	const body: t.Statement[] = [loop];

	assert.equal(
		reduceDelegateYieldStructuredBodies({
			blocks: new Map([[0, { body }]]),
		} as unknown as IRFunction),
		true,
	);
	const code = generate(t.program(body)).code;
	assert.match(code, /while \(true\)/);
	assert.match(code, /completion = %DelegateYield\(source\(\)\)/);
	assert.match(code, /const value = completion/);
	assert.doesNotMatch(
		code,
		/HermesInternal\.(ensureObject|generatorSetDelegated|getMethod)/,
	);
});

Deno.test('delegate cleanup removes only unreachable protocol trailers', () => {
	const label = t.identifier('outer');
	const delegateTrailer = () => [
		declaration(
			'returnMethod',
			hermesCall('getMethod', [
				t.identifier('iterator'),
				t.stringLiteral('return'),
			]),
		),
		t.expressionStatement(hermesCall('throwTypeError', [
			t.stringLiteral('yield* delegate must have a .throw() method'),
		])),
		t.throwStatement(t.identifier('undefined')),
	];
	const terminalLoop = t.whileStatement(
		t.booleanLiteral(true),
		t.blockStatement([
			t.expressionStatement(intrinsic('DelegateYield', [
				t.callExpression(t.identifier('source'), []),
			])),
			t.breakStatement(t.cloneNode(label)),
		]),
	);
	const labeledBody = [
		terminalLoop,
		...delegateTrailer(),
	];
	const body: t.Statement[] = [
		t.labeledStatement(label, t.blockStatement(labeledBody)),
	];

	assert.equal(
		reduceDelegateYieldStructuredBodies({
			blocks: new Map([[0, { body }]]),
		} as unknown as IRFunction),
		true,
	);
	assert.equal(labeledBody.length, 1);

	const breakableLoop = t.whileStatement(
		t.booleanLiteral(true),
		t.blockStatement([
			t.ifStatement(
				t.identifier('stop'),
				t.breakStatement(),
			),
		]),
	);
	const reachableTrailer = [
		breakableLoop,
		...delegateTrailer(),
	];
	assert.equal(
		reduceDelegateYieldStructuredBodies({
			blocks: new Map([[0, { body: reachableTrailer }]]),
		} as unknown as IRFunction),
		false,
	);
	assert.equal(reachableTrailer.length, 4);
});
