import { strict as assert } from 'node:assert';
import generate from '@babel/generator';
import * as t from '@babel/types';
import { tagStorageLocation } from '../../ast/alias.ts';
import {
	attachDirectParameterPatterns,
	attachParameterPatternAssignmentDefaults,
	attachPatternBindingDefaults,
	attachProjectedObjectParameterPatterns,
	captureParameterProjections,
	cloneParameterPlan,
	createParameterPlan,
	materializeParameterPlan,
	recoverOverflowParameters,
} from './parameterPlan.ts';

function overflow(functionId: number, jsIndex: number): t.MemberExpression {
	return tagStorageLocation(
		t.memberExpression(
			t.identifier('arguments'),
			t.numericLiteral(jsIndex),
			true,
		),
		{
			kind: 'parameter',
			owner: { functionId },
			parameter: {
				index: jsIndex + 1,
				form: 'overflow',
			},
		},
	);
}

function liftedArgumentsLength(functionId: number): t.MemberExpression {
	const node = t.memberExpression(
		t.identifier('arguments'),
		t.identifier('length'),
	);
	node.extra = {
		instruction: 'GetArgumentsLength',
		parentFunctionId: functionId,
	};
	return node;
}

function liftedArgument(
	functionId: number,
	jsIndex: number,
): t.MemberExpression {
	const node = t.memberExpression(
		t.identifier('arguments'),
		t.numericLiteral(jsIndex),
		true,
	);
	node.extra = {
		instruction: 'GetArgumentsPropByVal',
		parentFunctionId: functionId,
	};
	return node;
}

function signature(plan: ReturnType<typeof createParameterPlan>): string {
	return generate(t.functionExpression(
		null,
		materializeParameterPlan(plan) as t.FunctionParameter[],
		t.blockStatement([]),
	)).code;
}

function copyDataProperties(
	source: t.Expression,
	excludedKeys: readonly string[],
): t.CallExpression {
	return t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		[
			t.objectExpression([]),
			source,
			t.objectExpression([
				t.objectProperty(
					t.identifier('__proto__'),
					t.nullLiteral(),
				),
				...excludedKeys.map((key) =>
					t.objectProperty(t.identifier(key), t.numericLiteral(0))
				),
			]),
		],
	);
}

Deno.test('recovers a default suffix, trailing formals, and raw aliases', () => {
	const functionId = 7;
	const raw = t.identifier('r1_1');
	const selected = t.identifier('r1_3');
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(raw, overflow(functionId, 1)),
		]),
		t.variableDeclaration('let', [
			t.variableDeclarator(selected, t.cloneNode(raw)),
		]),
		t.ifStatement(
			t.binaryExpression(
				'===',
				t.cloneNode(raw),
				t.identifier('undefined'),
			),
			t.blockStatement([
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.cloneNode(selected),
					t.callExpression(t.identifier('value'), []),
				)),
			]),
		),
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r0_1'),
				overflow(functionId, 2),
			),
		]),
		t.returnStatement(t.arrayExpression([
			t.cloneNode(raw),
			t.identifier('r0_1'),
		])),
	];
	const plan = createParameterPlan(functionId, [t.identifier('_param_7_0_')]);

	assert.equal(
		recoverOverflowParameters({
			functionId,
			headerParamCount: 2,
			body,
			plan,
		}),
		true,
	);
	assert.match(
		signature(plan),
		/function \(_param_7_0_, _param_7_1_ = value\(\), _param_7_2_\)/,
	);
	assert.equal(
		generate(t.program(body)).code,
		'return [_param_7_1_, _param_7_2_];',
	);
	assert.equal(plan.telemetry.valueDefaultsRecovered, 1);
	assert.equal(plan.telemetry.trailingFormalsPromoted, 1);
});

Deno.test('rewrites earlier recovered parameters inside later defaults', () => {
	const functionId = 109146;
	const selected = [0, 1, 2, 3].map((index) =>
		t.identifier(`r${index}_selected`)
	);
	const raw = [0, 1, 2, 3].map((index) => t.identifier(`r${index}_raw`));
	const defaultProtocol = (
		jsIndex: number,
		defaultValue: t.Expression,
	): t.Statement[] => [
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.cloneNode(raw[jsIndex]!),
				overflow(functionId, jsIndex),
			),
		]),
		t.variableDeclaration('let', [
			t.variableDeclarator(
				t.cloneNode(selected[jsIndex]!),
				t.cloneNode(raw[jsIndex]!),
			),
		]),
		t.ifStatement(
			t.binaryExpression(
				'===',
				t.cloneNode(raw[jsIndex]!),
				t.identifier('undefined'),
			),
			t.blockStatement([
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.cloneNode(selected[jsIndex]!),
					defaultValue,
				)),
			]),
		),
	];
	const fallback = (jsIndex: number, value: number) =>
		t.conditionalExpression(
			t.binaryExpression(
				'!==',
				t.cloneNode(selected[jsIndex]!),
				t.identifier('undefined'),
			),
			t.cloneNode(selected[jsIndex]!),
			t.numericLiteral(value),
		);
	const body: t.Statement[] = [
		...defaultProtocol(0, t.numericLiteral(34)),
		...defaultProtocol(1, t.numericLiteral(20)),
		...defaultProtocol(2, t.numericLiteral(20)),
		...defaultProtocol(
			3,
			t.binaryExpression(
				'+',
				t.binaryExpression(
					'+',
					t.binaryExpression('+', fallback(0, 34), fallback(1, 20)),
					fallback(2, 20),
				),
				t.numericLiteral(6),
			),
		),
		t.returnStatement(t.arrayExpression(
			selected.map((identifier) => t.cloneNode(identifier)),
		)),
	];
	const plan = createParameterPlan(functionId, []);

	assert.equal(
		recoverOverflowParameters({
			functionId,
			headerParamCount: 1,
			body,
			plan,
		}),
		true,
	);
	assert.equal(
		signature(plan),
		'function (_param_109146_0_ = 34, _param_109146_1_ = 20, ' +
			'_param_109146_2_ = 20, _param_109146_3_ = ' +
			'(_param_109146_0_ !== undefined ? _param_109146_0_ : 34) + ' +
			'(_param_109146_1_ !== undefined ? _param_109146_1_ : 20) + ' +
			'(_param_109146_2_ !== undefined ? _param_109146_2_ : 20) + 6) {}',
	);
	assert.equal(
		generate(t.program(body)).code,
		'return [_param_109146_0_, _param_109146_1_, ' +
			'_param_109146_2_, _param_109146_3_];',
	);
});

Deno.test('infers a sparse first suffix only after a later default proof', () => {
	const functionId = 8;
	const raw = t.identifier('r2_1');
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(raw, overflow(functionId, 2)),
		]),
		t.returnStatement(t.conditionalExpression(
			t.binaryExpression(
				'===',
				t.cloneNode(raw),
				t.identifier('undefined'),
			),
			t.numericLiteral(3),
			t.cloneNode(raw),
		)),
	];
	const plan = createParameterPlan(functionId, [t.identifier('_param_8_0_')]);

	assert.equal(
		recoverOverflowParameters({
			functionId,
			headerParamCount: 2,
			body,
			plan,
		}),
		true,
	);
	assert.match(
		signature(plan),
		/_param_8_1_ = undefined, _param_8_2_ = 3/,
	);
	assert.equal(plan.telemetry.inferredGaps, 1);
	assert.equal(generate(t.program(body)).code, 'return _param_8_2_;');
});

Deno.test('recovers an unused side-effect-only default', () => {
	const functionId = 9;
	const tail = t.returnStatement(t.numericLiteral(1));
	const body: t.Statement[] = [
		t.ifStatement(
			t.unaryExpression(
				'!',
				t.binaryExpression(
					'===',
					overflow(functionId, 0),
					t.identifier('undefined'),
				),
			),
			t.blockStatement([t.cloneNode(tail, true)]),
		),
		t.expressionStatement(t.callExpression(t.identifier('sideEffect'), [])),
		tail,
	];
	const plan = createParameterPlan(functionId, []);

	assert.equal(
		recoverOverflowParameters({
			functionId,
			headerParamCount: 1,
			body,
			plan,
		}),
		true,
	);
	assert.match(signature(plan), /_param_9_0_ = sideEffect\(\)/);
	assert.equal(generate(t.program(body)).code, 'return 1;');
	assert.equal(plan.telemetry.sideEffectOnlyDefaultsRecovered, 1);
});

Deno.test('does not reinterpret a genuine source arguments access', () => {
	const body = [
		t.returnStatement(t.memberExpression(
			t.identifier('arguments'),
			t.numericLiteral(2),
			true,
		)),
	];
	const before = generate(t.program(body)).code;
	const plan = createParameterPlan(10, []);

	assert.equal(
		recoverOverflowParameters({
			functionId: 10,
			headerParamCount: 1,
			body,
			plan,
		}),
		false,
	);
	assert.equal(generate(t.program(body)).code, before);
	assert.deepEqual(plan.slots, []);
});

Deno.test('recovers an argument-length guarded default parameter', () => {
	const functionId = 15;
	const body: t.Statement[] = [
		t.returnStatement(t.conditionalExpression(
			t.binaryExpression(
				'<',
				t.numericLiteral(2),
				liftedArgumentsLength(functionId),
			),
			t.conditionalExpression(
				t.binaryExpression(
					'!==',
					liftedArgument(functionId, 2),
					t.identifier('undefined'),
				),
				liftedArgument(functionId, 2),
				t.nullLiteral(),
			),
			t.nullLiteral(),
		)),
	];
	const plan = createParameterPlan(functionId, [
		t.identifier('_param_15_0_'),
		t.identifier('_param_15_1_'),
	]);

	assert.equal(
		recoverOverflowParameters({
			functionId,
			headerParamCount: 3,
			body,
			plan,
		}),
		true,
	);
	assert.match(signature(plan), /_param_15_2_ = null/);
	assert.equal(generate(t.program(body)).code, 'return _param_15_2_;');
});

Deno.test('recovers a fused missing-or-undefined default guard', () => {
	const functionId = 19;
	const body: t.Statement[] = [
		t.returnStatement(t.conditionalExpression(
			t.logicalExpression(
				'||',
				t.unaryExpression(
					'!',
					t.binaryExpression(
						'>',
						liftedArgumentsLength(functionId),
						t.numericLiteral(1),
					),
				),
				t.binaryExpression(
					'===',
					t.identifier('undefined'),
					liftedArgument(functionId, 1),
				),
			),
			t.objectExpression([]),
			liftedArgument(functionId, 1),
		)),
	];
	const plan = createParameterPlan(functionId, [
		t.identifier('_param_19_0_'),
	]);

	assert.equal(
		recoverOverflowParameters({
			functionId,
			headerParamCount: 2,
			body,
			plan,
		}),
		true,
	);
	assert.match(signature(plan), /_param_19_1_ = \{\}/);
	assert.equal(generate(t.program(body)).code, 'return _param_19_1_;');
});

Deno.test('removes a trailing argument-length guard after a proven default', () => {
	const functionId = 20;
	const body: t.Statement[] = [
		t.expressionStatement(t.conditionalExpression(
			t.binaryExpression(
				'>',
				liftedArgumentsLength(functionId),
				t.numericLiteral(1),
			),
			t.conditionalExpression(
				t.binaryExpression(
					'!==',
					liftedArgument(functionId, 1),
					t.identifier('undefined'),
				),
				liftedArgument(functionId, 1),
				t.numericLiteral(0),
			),
			t.numericLiteral(0),
		)),
		t.returnStatement(t.conditionalExpression(
			t.unaryExpression(
				'!',
				t.binaryExpression(
					'>',
					liftedArgumentsLength(functionId),
					t.numericLiteral(2),
				),
			),
			t.identifier('undefined'),
			liftedArgument(functionId, 2),
		)),
	];
	const plan = createParameterPlan(functionId, [
		t.identifier('_param_20_0_'),
	]);

	assert.equal(
		recoverOverflowParameters({
			functionId,
			headerParamCount: 2,
			body,
			plan,
		}),
		true,
	);
	assert.match(
		signature(plan),
		/_param_20_1_ = 0, _param_20_2_/,
	);
	assert.equal(
		generate(t.program(body)).code,
		'_param_20_1_;\nreturn _param_20_2_;',
	);
});

Deno.test('does not recover an unproven source-level argument-length guard', () => {
	const body: t.Statement[] = [
		t.returnStatement(t.conditionalExpression(
			t.binaryExpression(
				'<',
				t.numericLiteral(2),
				t.memberExpression(
					t.identifier('arguments'),
					t.identifier('length'),
				),
			),
			t.memberExpression(
				t.identifier('arguments'),
				t.numericLiteral(2),
				true,
			),
			t.nullLiteral(),
		)),
	];
	const before = generate(t.program(body)).code;
	const plan = createParameterPlan(16, [
		t.identifier('_param_16_0_'),
		t.identifier('_param_16_1_'),
	]);

	assert.equal(
		recoverOverflowParameters({
			functionId: 16,
			headerParamCount: 3,
			body,
			plan,
		}),
		false,
	);
	assert.equal(generate(t.program(body)).code, before);
});

Deno.test('factors a duplicated suffix and composes a structured default', () => {
	const functionId = 22;
	const raw = t.identifier('r0_1');
	const selected = t.identifier('r0_3');
	const fallback = t.identifier('r1_3');
	const tail = () => t.returnStatement(t.cloneNode(selected));
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			raw,
			overflow(functionId, 0),
		)]),
		t.variableDeclaration('let', [t.variableDeclarator(selected)]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.cloneNode(selected),
			t.cloneNode(raw),
		)),
		t.ifStatement(
			t.binaryExpression(
				'!==',
				t.cloneNode(raw),
				t.identifier('undefined'),
			),
			t.blockStatement([tail()]),
			t.blockStatement([
				t.variableDeclaration('let', [t.variableDeclarator(fallback)]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.cloneNode(fallback),
					t.nullLiteral(),
				)),
				t.ifStatement(
					t.identifier('useNull'),
					t.blockStatement([
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.cloneNode(selected),
							t.cloneNode(fallback),
						)),
					]),
					t.blockStatement([
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.cloneNode(fallback),
							t.callExpression(t.identifier('makeDefault'), []),
						)),
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.cloneNode(selected),
							t.cloneNode(fallback),
						)),
					]),
				),
				tail(),
			]),
		),
	];
	const plan = createParameterPlan(functionId, []);

	assert.equal(
		recoverOverflowParameters({
			functionId,
			headerParamCount: 1,
			body,
			plan,
		}),
		true,
	);
	assert.match(
		signature(plan),
		/_param_22_0_ = useNull \? null : makeDefault\(\)/,
	);
	assert.equal(generate(t.program(body)).code, 'return _param_22_0_;');
});

Deno.test('attaches array destructuring to a later defaulted slot', () => {
	const plan = createParameterPlan(17, [
		t.identifier('_param_17_0_'),
		t.identifier('_param_17_1_'),
	]);
	plan.slots[1].defaultValue = t.arrayExpression([
		t.numericLiteral(1),
		t.numericLiteral(2),
	]);
	const destructuring = t.variableDeclaration('var', [
		t.variableDeclarator(
			t.arrayPattern([
				t.identifier('first'),
				t.identifier('second'),
			]),
			t.identifier('_param_17_1_'),
		),
	]);
	destructuring.extra = { fromDestructuring: true };
	const body: t.Statement[] = [
		destructuring,
		t.returnStatement(t.binaryExpression(
			'+',
			t.identifier('first'),
			t.identifier('second'),
		)),
	];

	assert.equal(attachDirectParameterPatterns(body, plan), 1);
	assert.match(
		signature(plan),
		/function \(_param_17_0_, \[first, second\] = \[1, 2\]\)/,
	);
	assert.equal(generate(t.program(body)).code, 'return first + second;');
	assert.equal(plan.telemetry.parameterPatternsAttached, 1);
});

Deno.test('attaches a pattern after environment parameter bookkeeping', () => {
	const plan = createParameterPlan(21, [
		t.identifier('_param_21_0_'),
		t.identifier('_param_21_1_'),
	]);
	plan.slots[1].defaultValue = t.arrayExpression([]);
	const destructuring = t.variableDeclaration('var', [
		t.variableDeclarator(
			t.arrayPattern([t.identifier('captured')]),
			t.identifier('_param_21_1_'),
		),
	]);
	destructuring.extra = { fromDestructuring: true };
	const environment = t.identifier('environment');
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			environment,
			t.callExpression(
				t.v8IntrinsicIdentifier('CreateFunctionEnvironment'),
				[],
			),
		)]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(
				t.callExpression(t.v8IntrinsicIdentifier('expectEnvironment'), [
					t.cloneNode(environment),
				]),
				t.numericLiteral(0),
				true,
			),
			t.identifier('_param_21_0_'),
		)),
		destructuring,
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(
				t.callExpression(t.v8IntrinsicIdentifier('expectEnvironment'), [
					t.cloneNode(environment),
				]),
				t.numericLiteral(1),
				true,
			),
			t.identifier('captured'),
		)),
	];

	assert.equal(attachDirectParameterPatterns(body, plan), 1);
	assert.match(signature(plan), /\[captured\] = \[\]/);
	assert.equal(body.length, 3);
});

Deno.test('ignores cross-block references when checking direct parameter patterns', () => {
	const plan = createParameterPlan(19, [t.identifier('_param_19_0_')]);
	const destructuring = t.variableDeclaration('var', [
		t.variableDeclarator(
			t.arrayPattern([t.identifier('first')]),
			t.identifier('_param_19_0_'),
		),
	]);
	destructuring.extra = { fromDestructuring: true };
	const entryBody: t.Statement[] = [destructuring];
	const unreachable: t.Statement[] = [
		t.expressionStatement(t.identifier('_param_19_0_')),
	];

	assert.equal(
		attachDirectParameterPatterns(entryBody, plan, [
			entryBody,
			unreachable,
		]),
		0,
	);
	assert.ok(t.isIdentifier(plan.slots[0].binding));
	assert.equal(entryBody.length, 1);
	assert.equal(plan.telemetry.patternsDeclinedSourceEscapes, 1);
});

Deno.test('still attaches direct pattern when source appears only in entry', () => {
	const plan = createParameterPlan(20, [t.identifier('_param_20_0_')]);
	const destructuring = t.variableDeclaration('var', [
		t.variableDeclarator(
			t.arrayPattern([t.identifier('first')]),
			t.identifier('_param_20_0_'),
		),
	]);
	destructuring.extra = { fromDestructuring: true };
	const entryBody: t.Statement[] = [
		destructuring,
		t.returnStatement(t.identifier('first')),
	];
	const nonEscapeBody: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('scratch'),
			t.numericLiteral(0),
		)]),
	];

	assert.equal(
		attachDirectParameterPatterns(entryBody, plan, [
			entryBody,
			nonEscapeBody,
		]),
		1,
	);
	assert.match(signature(plan), /\(\[first\]\)/);
	assert.equal(entryBody.length, 1);
	assert.equal(plan.telemetry.parameterPatternsAttached, 1);
});

Deno.test('moves repeated destructuring defaults into the pattern', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.objectPattern([t.objectProperty(
				t.identifier('x'),
				t.identifier('r1_1'),
			)]),
			t.identifier('_param_11_0_'),
		)]),
		t.returnStatement(t.conditionalExpression(
			t.unaryExpression(
				'!',
				t.binaryExpression(
					'===',
					t.identifier('r1_1'),
					t.identifier('undefined'),
				),
			),
			t.identifier('r1_1'),
			t.numericLiteral(1),
		)),
	];

	assert.equal(attachPatternBindingDefaults(body), 1);
	assert.match(generate(t.program(body)).code, /x: r1_1 = 1/);
	assert.match(generate(t.program(body)).code, /return r1_1/);
});

Deno.test('attaches complete object projections to a defaulted parameter', () => {
	const plan = createParameterPlan(12, []);
	plan.slots.push({
		hermesIndex: 1,
		jsIndex: 0,
		binding: t.identifier('_param_12_0_'),
		defaultValue: t.objectExpression([]),
		provenance: 'overflow-default',
		rawLocations: [],
	});
	plan.projections.push({
		jsIndex: 0,
		path: [{ key: t.identifier('value'), computed: false }],
		binding: t.identifier('r1_2'),
	});
	plan.projections.push({
		jsIndex: 0,
		path: [{ key: t.identifier('unit'), computed: false }],
		binding: t.identifier('r1_3'),
	});
	const body: t.Statement[] = [t.returnStatement(t.arrayExpression([
		t.memberExpression(
			t.identifier('_param_12_0_'),
			t.identifier('value'),
		),
		t.memberExpression(
			t.identifier('_param_12_0_'),
			t.identifier('unit'),
		),
	]))];

	assert.equal(attachProjectedObjectParameterPatterns(12, body, plan), 1);
	assert.match(signature(plan), /\{\s*value: r1_2/);
	assert.equal(
		generate(t.program(body)).code,
		'return [r1_2, r1_3];',
	);
	assert.equal(plan.telemetry.parameterPatternsAttached, 1);
});

Deno.test(
	'projected parameter attachment preserves distinct SSA-version initializers',
	() => {
		const plan = createParameterPlan(55, []);
		plan.slots.push({
			hermesIndex: 3,
			jsIndex: 2,
			binding: t.identifier('_param_55_2_'),
			provenance: 'header',
			rawLocations: [],
		});
		plan.projections.push({
			jsIndex: 2,
			path: [{ key: t.identifier('guild'), computed: false }],
			binding: t.identifier('r6_2'),
		});
		plan.projections.push({
			jsIndex: 2,
			path: [{ key: t.identifier('channel'), computed: false }],
			binding: t.identifier('r6_3'),
		});
		const body: t.Statement[] = [
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r6_2'),
					t.memberExpression(
						t.identifier('_param_55_2_'),
						t.identifier('guild'),
					),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r6_3'),
					t.memberExpression(
						t.identifier('_param_55_2_'),
						t.identifier('channel'),
					),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r3_5'),
					t.identifier('r3_2'),
				),
			]),
			t.variableDeclaration('let', [
				t.variableDeclarator(t.identifier('r4_6')),
			]),
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.identifier('r4_6'),
				t.identifier('r4_4'),
			)),
			t.ifStatement(
				t.identifier('condition'),
				t.blockStatement([
					t.expressionStatement(t.assignmentExpression(
						'=',
						t.identifier('r4_6'),
						t.identifier('selected'),
					)),
				]),
			),
			t.returnStatement(t.identifier('r4_6')),
		];

		assert.equal(
			attachProjectedObjectParameterPatterns(55, body, plan),
			1,
		);
		assert.match(signature(plan), /\{\s*guild: r6_2/);
		const code = generate(t.program(body)).code;
		assert.doesNotMatch(code, /const r6_2 = r6_2/);
		assert.match(code, /const r3_5 = r3_2/);
		assert.match(code, /r4_6 = r4_4/);
	},
);

Deno.test('arguments access does not block object parameter attachment', () => {
	const plan = createParameterPlan(13, []);
	plan.slots.push({
		hermesIndex: 1,
		jsIndex: 0,
		binding: t.identifier('_param_13_0_'),
		defaultValue: t.objectExpression([]),
		provenance: 'overflow-default',
		rawLocations: [],
	});
	plan.projections.push({
		jsIndex: 0,
		path: [{ key: t.identifier('value'), computed: false }],
		binding: t.identifier('r1_2'),
	});
	plan.projections.push({
		jsIndex: 0,
		path: [{ key: t.identifier('unit'), computed: false }],
		binding: t.identifier('r1_3'),
	});
	const body: t.Statement[] = [t.returnStatement(t.arrayExpression([
		t.memberExpression(
			t.identifier('_param_13_0_'),
			t.identifier('value'),
		),
		t.memberExpression(
			t.identifier('_param_13_0_'),
			t.identifier('unit'),
		),
		t.memberExpression(
			t.identifier('arguments'),
			t.numericLiteral(0),
			true,
		),
	]))];

	assert.equal(attachProjectedObjectParameterPatterns(13, body, plan), 1);
	assert.ok(t.isObjectPattern(plan.slots[0].binding));
	assert.equal(
		generate(t.program(body)).code,
		'return [r1_2, r1_3, arguments[0]];',
	);
	assert.equal(plan.telemetry.patternsDeclinedSourceEscapes, 0);
});

Deno.test('object rest copy does not block projected parameter attachment', () => {
	const plan = createParameterPlan(21, [t.identifier('_param_21_0_')]);
	plan.projections.push(
		{
			jsIndex: 0,
			path: [{ key: t.identifier('value'), computed: false }],
			binding: t.identifier('r1_2'),
		},
		{
			jsIndex: 0,
			path: [{ key: t.identifier('other'), computed: false }],
			binding: t.identifier('r2_2'),
		},
	);
	const body: t.Statement[] = [t.returnStatement(t.objectExpression([
		t.spreadElement(copyDataProperties(
			t.identifier('_param_21_0_'),
			['value', 'other'],
		)),
		t.objectProperty(
			t.identifier('value'),
			t.memberExpression(
				t.identifier('_param_21_0_'),
				t.identifier('value'),
			),
		),
		t.objectProperty(
			t.identifier('other'),
			t.memberExpression(
				t.identifier('_param_21_0_'),
				t.identifier('other'),
			),
		),
	]))];

	assert.equal(attachProjectedObjectParameterPatterns(21, body, plan), 1);
	assert.match(
		signature(plan),
		/\{\s*value: r1_2,\s*other: r2_2,\s*\.\.\._rest_21_0_/,
	);
	assert.equal(
		generate(t.program(body)).code,
		'return {\n' +
			'  ..._rest_21_0_,\n' +
			'  value: r1_2,\n' +
			'  other: r2_2\n' +
			'};',
	);
	assert.equal(plan.telemetry.patternsDeclinedSourceEscapes, 0);
});

Deno.test('object rest aliases can feed projected parameter attachment', () => {
	const plan = createParameterPlan(22, [t.identifier('_param_22_0_')]);
	plan.projections.push({
		jsIndex: 0,
		path: [{ key: t.identifier('value'), computed: false }],
		binding: t.identifier('r1_2'),
	});
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r3_1'),
				copyDataProperties(
					t.identifier('_param_22_0_'),
					['value'],
				),
			),
		]),
		t.returnStatement(t.arrayExpression([
			t.identifier('r3_1'),
			t.memberExpression(
				t.identifier('_param_22_0_'),
				t.identifier('value'),
			),
		])),
	];

	assert.equal(attachProjectedObjectParameterPatterns(22, body, plan), 1);
	assert.match(signature(plan), /\{\s*value: r1_2,\s*\.\.\._rest_22_0_/);
	assert.equal(
		generate(t.program(body)).code,
		'const r3_1 = _rest_22_0_;\nreturn [r3_1, r1_2];',
	);
	assert.equal(plan.telemetry.patternsDeclinedSourceEscapes, 0);
});

Deno.test('identifier exclusion map feeds projected parameter attachment', () => {
	const plan = createParameterPlan(24, [t.identifier('_param_24_0_')]);
	plan.projections.push({
		jsIndex: 0,
		path: [{ key: t.identifier('value'), computed: false }],
		binding: t.identifier('r1_2'),
	});
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('excluded'),
			t.callExpression(
				t.memberExpression(
					t.identifier('Object'),
					t.identifier('create'),
				),
				[t.nullLiteral()],
			),
		)]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('excluded'), t.identifier('value')),
			t.numericLiteral(0),
		)),
		t.returnStatement(t.arrayExpression([
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('copyDataProperties'),
				),
				[
					t.objectExpression([]),
					t.identifier('_param_24_0_'),
					t.identifier('excluded'),
				],
			),
			t.memberExpression(
				t.identifier('_param_24_0_'),
				t.identifier('value'),
			),
		])),
	];

	assert.equal(attachProjectedObjectParameterPatterns(24, body, plan), 1);
	assert.match(signature(plan), /\{\s*value: r1_2,\s*\.\.\._rest_24_0_/);
	assert.equal(
		generate(t.program(body)).code,
		'return [_rest_24_0_, r1_2];',
	);
});

Deno.test('v99 parent-buffer exclusion map feeds projected parameter attachment', () => {
	const plan = createParameterPlan(25, [t.identifier('_param_25_0_')]);
	plan.projections.push({
		jsIndex: 0,
		path: [{ key: t.identifier('value'), computed: false }],
		binding: t.identifier('r1_2'),
	});
	const body: t.Statement[] = [t.returnStatement(t.objectExpression([
		t.spreadElement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('copyDataProperties'),
			),
			[
				t.objectExpression([]),
				t.identifier('_param_25_0_'),
				t.callExpression(
					t.memberExpression(
						t.identifier('Object'),
						t.identifier('assign'),
					),
					[
						t.callExpression(
							t.memberExpression(
								t.identifier('Object'),
								t.identifier('create'),
							),
							[t.nullLiteral()],
						),
						t.objectExpression([
							t.objectProperty(
								t.stringLiteral('value'),
								t.numericLiteral(0),
							),
						]),
					],
				),
			],
		)),
		t.objectProperty(
			t.identifier('value'),
			t.memberExpression(
				t.identifier('_param_25_0_'),
				t.identifier('value'),
			),
		),
	]))];

	assert.equal(attachProjectedObjectParameterPatterns(25, body, plan), 1);
	assert.match(signature(plan), /\{\s*value: r1_2,\s*\.\.\._rest_25_0_/);
	assert.equal(
		generate(t.program(body)).code,
		'return {\n' +
			'  ..._rest_25_0_,\n' +
			'  value: r1_2\n' +
			'};',
	);
});

Deno.test('unused excluded property does not block object rest parameter', () => {
	const plan = createParameterPlan(26, [t.identifier('_param_26_0_')]);
	plan.projections.push({
		jsIndex: 0,
		path: [{ key: t.identifier('used'), computed: false }],
		binding: t.identifier('r1_2'),
	});
	const body: t.Statement[] = [
		t.expressionStatement(t.memberExpression(
			t.identifier('_param_26_0_'),
			t.identifier('unused'),
		)),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('rest'),
			copyDataProperties(
				t.identifier('_param_26_0_'),
				['used', 'unused'],
			),
		)]),
		t.returnStatement(t.arrayExpression([
			t.memberExpression(
				t.identifier('_param_26_0_'),
				t.identifier('used'),
			),
			t.identifier('rest'),
		])),
	];

	assert.equal(attachProjectedObjectParameterPatterns(26, body, plan), 1);
	assert.match(
		signature(plan),
		/\{\s*used: r1_2,\s*unused: _unused_26_0_0_,\s*\.\.\._rest_26_0_/,
	);
	assert.equal(
		generate(t.program(body)).code,
		'const rest = _rest_26_0_;\nreturn [r1_2, rest];',
	);
});

Deno.test('object rest with different exclusions still blocks attachment', () => {
	const plan = createParameterPlan(23, [t.identifier('_param_23_0_')]);
	plan.projections.push({
		jsIndex: 0,
		path: [{ key: t.identifier('value'), computed: false }],
		binding: t.identifier('r1_2'),
	});
	const body: t.Statement[] = [t.returnStatement(t.objectExpression([
		t.spreadElement(copyDataProperties(
			t.identifier('_param_23_0_'),
			['other'],
		)),
		t.objectProperty(
			t.identifier('value'),
			t.memberExpression(
				t.identifier('_param_23_0_'),
				t.identifier('value'),
			),
		),
	]))];

	assert.equal(attachProjectedObjectParameterPatterns(23, body, plan), 0);
	assert.ok(t.isIdentifier(plan.slots[0].binding));
	assert.equal(plan.telemetry.patternsDeclinedSourceEscapes, 1);
});

Deno.test('captures chained projected object parameters', () => {
	const plan = createParameterPlan(30, [t.identifier('_param_30_0_')]);
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('windowDimensions'),
			t.memberExpression(
				t.identifier('_param_30_0_'),
				t.identifier('windowDimensions'),
			),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('height'),
			t.memberExpression(
				t.identifier('windowDimensions'),
				t.identifier('height'),
			),
		)]),
		t.returnStatement(t.objectExpression([
			t.spreadElement(copyDataProperties(
				t.identifier('_param_30_0_'),
				['windowDimensions'],
			)),
			t.objectProperty(
				t.identifier('height'),
				t.memberExpression(
					t.memberExpression(
						t.identifier('_param_30_0_'),
						t.identifier('windowDimensions'),
					),
					t.identifier('height'),
				),
			),
		])),
	];

	assert.equal(captureParameterProjections(30, [body], plan), 2);
	body.splice(
		0,
		body.length,
		t.returnStatement(t.objectExpression([
			t.spreadElement(copyDataProperties(
				t.identifier('_param_30_0_'),
				['windowDimensions'],
			)),
			t.objectProperty(
				t.identifier('height'),
				t.memberExpression(
					t.memberExpression(
						t.identifier('_param_30_0_'),
						t.identifier('windowDimensions'),
					),
					t.identifier('height'),
				),
			),
		])),
	);
	assert.equal(attachProjectedObjectParameterPatterns(30, body, plan), 1);
	assert.match(
		signature(plan),
		/\{\s*windowDimensions: \{\s*height: height\s*\},\s*\.\.\._rest_30_0_/,
	);
	assert.equal(
		generate(t.program(body)).code,
		'return {\n' +
			'  ..._rest_30_0_,\n' +
			'  height: height\n' +
			'};',
	);
});

Deno.test('folds destructured parameter assignment defaults', () => {
	const plan = createParameterPlan(31, [t.identifier('_param_31_0_')]);
	plan.slots[0].binding = t.objectPattern([
		t.objectProperty(
			t.identifier('scrollable'),
			t.identifier('scrollable'),
			false,
			true,
		),
	]);
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('selected')),
		]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier('selected'),
			t.identifier('scrollable'),
		)),
		t.ifStatement(
			t.binaryExpression(
				'===',
				t.identifier('scrollable'),
				t.identifier('undefined'),
			),
			t.blockStatement([
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.identifier('selected'),
					t.booleanLiteral(false),
				)),
			]),
		),
		t.returnStatement(t.identifier('selected')),
	];

	assert.equal(attachParameterPatternAssignmentDefaults(body, plan), 1);
	assert.match(signature(plan), /\{\s*scrollable = false\s*\}/);
	assert.equal(generate(t.program(body)).code, 'return scrollable;');
});

Deno.test('parameter plans clone independently', () => {
	const original = createParameterPlan(14, [t.identifier('_param_14_0_')]);
	const clone = cloneParameterPlan(original);
	clone.slots[0].binding = t.objectPattern([]);
	clone.telemetry.declines.push({ reason: 'test' });

	assert.ok(t.isIdentifier(original.slots[0].binding));
	assert.deepEqual(original.telemetry.declines, []);
});

Deno.test('declines a lone object projection', () => {
	const plan = createParameterPlan(23, [t.identifier('_param_23_0_')]);
	plan.projections.push({
		jsIndex: 0,
		path: [{ key: t.identifier('exports'), computed: false }],
		binding: t.identifier('r1_2'),
	});
	const body: t.Statement[] = [t.returnStatement(t.memberExpression(
		t.identifier('_param_23_0_'),
		t.identifier('exports'),
	))];

	assert.equal(attachProjectedObjectParameterPatterns(23, body, plan), 0);
	assert.ok(t.isIdentifier(plan.slots[0].binding));
	assert.equal(
		generate(t.program(body)).code,
		'return _param_23_0_.exports;',
	);
	assert.ok(
		plan.telemetry.declines.some((decline) =>
			decline.reason === 'single-object-parameter-projection'
		),
	);
});

Deno.test('declines projections keyed only by computed numeric literals', () => {
	const plan = createParameterPlan(24, [t.identifier('_param_24_0_')]);
	for (const [index, binding] of [['0', 'r1_2'], ['1', 'r1_3']]) {
		plan.projections.push({
			jsIndex: 0,
			path: [{ key: t.numericLiteral(Number(index)), computed: true }],
			binding: t.identifier(binding),
		});
	}
	const body: t.Statement[] = [t.returnStatement(t.arrayExpression([
		t.memberExpression(
			t.identifier('_param_24_0_'),
			t.numericLiteral(0),
			true,
		),
		t.memberExpression(
			t.identifier('_param_24_0_'),
			t.numericLiteral(1),
			true,
		),
	]))];

	assert.equal(attachProjectedObjectParameterPatterns(24, body, plan), 0);
	assert.ok(t.isIdentifier(plan.slots[0].binding));
	assert.ok(
		plan.telemetry.declines.some((decline) =>
			decline.reason === 'numeric-object-parameter-projection'
		),
	);
});
