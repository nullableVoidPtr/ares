import { strict as assert } from 'node:assert';
import { parse } from '@babel/parser';
import generate from '@babel/generator';
import traverse from '@babel/traverse';
import * as t from '@babel/types';
import {
	assignedEnvironmentLookupForUse,
	collapsePrimedNativeGeneratorWrapper,
	hoistDestructuredFunctionParams,
	hoistInitialIteratorDestructuredFunctionParams,
	hoistPrimedGeneratorArgumentsParams,
	hoistPrimedGeneratorObjectParams,
	liftFileWithAnalysis,
	liftFunctionsIncrementally,
	lowerProgramCompletionReturns,
	mergeRecoveredGeneratorWrapperParams,
	normalizeDuplicateRegisterDeclarations,
	recoverDeclaredGlobalDestructuringAssignments,
	recoverDirectObjectDefaultAliasesInBody,
	recoverEmbeddedObjectRestForFunction,
	removeDeadEnvironmentLookupHandles,
	removeDeadRecoveredProtectedEnvironmentHandles,
	simplifyGeneratedSequenceAssignments,
} from './lift.ts';
import { liftHermesConcatCalls } from './ast/expression.ts';
import { liftSSABlocktoIR } from './ast/lift.ts';
import type { IRFunction } from './function/mod.ts';
import {
	BasicBlock,
	Function,
	FunctionKind,
} from '../hbc/disassembly/function.ts';
import {
	asFunctionRef,
	asRegister,
	asStringRef,
	InstructionLength,
	InstructionStrictness,
	InstructionType,
} from '../hbc/disassembly/instruction.ts';
import type { HBCFile } from '../parser/file.ts';
import type { SSABasicBlock, SSAInstruction, SSARegister } from '../ssa.ts';

Deno.test('program completion return becomes a conditional alternate', () => {
	const program = t.program([
		t.ifStatement(
			t.identifier('done'),
			t.blockStatement([
				t.expressionStatement(
					t.callExpression(t.identifier('finish'), []),
				),
				t.returnStatement(t.callExpression(t.identifier('result'), [])),
			]),
		),
		t.expressionStatement(
			t.callExpression(t.identifier('continueWork'), []),
		),
	]);

	assert.equal(lowerProgramCompletionReturns(program), true);
	assert.equal(
		generate(program).code,
		'if (done) {\n' +
			'  finish();\n' +
			'  result();\n' +
			'} else {\n' +
			'  continueWork();\n' +
			'}',
	);
});

Deno.test('embedded object-rest spreads recover function parameter rest', () => {
	const param = t.identifier('_param_91249_0_');
	const copyDataProperties = t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		[
			t.objectExpression([]),
			t.identifier('_param_91249_0_'),
			t.objectExpression([
				t.objectProperty(t.identifier('__proto__'), t.nullLiteral()),
				t.objectProperty(
					t.stringLiteral('aria-label'),
					t.numericLiteral(0),
				),
				t.objectProperty(t.identifier('size'), t.numericLiteral(0)),
			]),
		],
	);
	const func = t.functionExpression(
		t.identifier('Component'),
		[param],
		t.blockStatement([
			t.returnStatement(t.objectExpression([
				t.objectProperty(
					t.stringLiteral('aria-label'),
					t.memberExpression(
						t.identifier('_param_91249_0_'),
						t.stringLiteral('aria-label'),
						true,
					),
					true,
				),
				t.objectProperty(
					t.identifier('size'),
					t.memberExpression(
						t.identifier('_param_91249_0_'),
						t.identifier('size'),
					),
				),
				t.objectProperty(
					t.identifier('props'),
					t.objectExpression([
						t.spreadElement(copyDataProperties),
					]),
				),
			])),
		]),
	);
	const program = t.program([t.expressionStatement(func)]);
	const file = t.file(program);
	let changed = false;
	traverse(file, {
		Function(path) {
			changed = recoverEmbeddedObjectRestForFunction(path);
			path.stop();
		},
	});

	assert.equal(changed, true);
	assert.doesNotMatch(generate(program).code, /copyDataProperties/);
	assert.match(generate(program).code, /\.\.\._rest_91249_0_/);
});

Deno.test('declared object-rest copy recovers function parameter rest', () => {
	const copyDataProperties = t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		[
			t.objectExpression([]),
			t.identifier('_param_43012_0_'),
			t.objectExpression([
				t.objectProperty(t.identifier('__proto__'), t.nullLiteral()),
				t.objectProperty(
					t.identifier('scrollable'),
					t.numericLiteral(0),
				),
				t.objectProperty(
					t.identifier('bodyStyles'),
					t.numericLiteral(0),
				),
			]),
		],
	);
	const func = t.functionExpression(
		null,
		[t.identifier('_param_43012_0_')],
		t.blockStatement([
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r28_1'),
					t.memberExpression(
						t.identifier('_param_43012_0_'),
						t.identifier('scrollable'),
					),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(t.identifier('r0_2'), copyDataProperties),
			]),
			t.returnStatement(t.memberExpression(
				t.identifier('r0_2'),
				t.identifier('backgroundComponent'),
			)),
		]),
	);
	const program = t.program([t.expressionStatement(func)]);
	const file = t.file(program);
	let changed = false;
	traverse(file, {
		Function(path) {
			changed = recoverEmbeddedObjectRestForFunction(path);
			path.stop();
		},
	});

	const code = generate(program).code;
	assert.equal(changed, true);
	assert.doesNotMatch(code, /copyDataProperties|const r0_2/);
	assert.match(code, /\.\.\._rest_43012_0_/);
	assert.doesNotMatch(code, /const r28_1/);
	assert.match(code, /scrollable: r28_1/);
	assert.match(code, /bodyStyles: _bodyStyles/);
	assert.match(code, /return _rest_43012_0_\.backgroundComponent;/);
});

Deno.test('declared object-rest copy absorbs source destructuring assignment', () => {
	const copyDataProperties = t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		[
			t.objectExpression([]),
			t.identifier('_param_69786_0_'),
			t.objectExpression([
				t.objectProperty(t.identifier('__proto__'), t.nullLiteral()),
				t.objectProperty(
					t.identifier('initialIndex'),
					t.numericLiteral(0),
				),
				t.objectProperty(t.identifier('openAs'), t.numericLiteral(0)),
			]),
		],
	);
	const func = t.functionExpression(
		null,
		[t.identifier('_param_69786_0_')],
		t.blockStatement([
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_1'),
					t.memberExpression(
						t.identifier('_param_69786_0_'),
						t.identifier('initialIndex'),
					),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('_env_69786_0'),
					t.conditionalExpression(
						t.binaryExpression(
							'===',
							t.identifier('r1_1'),
							t.identifier('undefined'),
						),
						t.numericLiteral(0),
						t.identifier('r1_1'),
					),
				),
			]),
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.objectPattern([
					t.objectProperty(
						t.identifier('openAs'),
						t.assignmentPattern(
							t.identifier('_env_69786_5'),
							t.stringLiteral('modal'),
						),
					),
				]),
				t.identifier('_param_69786_0_'),
			)),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('_env_69786_6'),
					copyDataProperties,
				),
			]),
			t.returnStatement(t.objectExpression([
				t.spreadElement(t.identifier('_env_69786_6')),
			])),
		]),
	);
	const program = t.program([t.expressionStatement(func)]);
	const file = t.file(program);
	let changed = false;

	traverse(file, {
		Function(path) {
			changed = recoverEmbeddedObjectRestForFunction(path);
			path.stop();
		},
	});

	const code = generate(program).code;
	assert.equal(changed, true);
	assert.doesNotMatch(code, /copyDataProperties/);
	assert.match(code, /initialIndex: _env_69786_0 = 0/);
	assert.match(code, /openAs: _env_69786_5 = "modal"/);
	assert.match(code, /\.\.\._rest_69786_0_/);
});
Deno.test('declared object-rest copy carries defaults from pattern aliases', () => {
	const copyDataProperties = t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		[
			t.objectExpression([]),
			t.identifier('_param_69786_0_'),
			t.objectExpression([
				t.objectProperty(
					t.identifier('__proto__'),
					t.nullLiteral(),
				),
				t.objectProperty(
					t.identifier('initialIndex'),
					t.numericLiteral(0),
				),
			]),
		],
	);
	const func = t.functionExpression(
		null,
		[t.identifier('_param_69786_0_')],
		t.blockStatement([
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.objectPattern([
						t.objectProperty(
							t.identifier('initialIndex'),
							t.identifier('r1_1'),
						),
					]),
					t.identifier('_param_69786_0_'),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('_env_69786_0'),
					t.conditionalExpression(
						t.binaryExpression(
							'===',
							t.identifier('r1_1'),
							t.identifier('undefined'),
						),
						t.numericLiteral(0),
						t.identifier('r1_1'),
					),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('_env_69786_6'),
					copyDataProperties,
				),
			]),
			t.returnStatement(t.objectExpression([
				t.spreadElement(t.identifier('_env_69786_6')),
			])),
		]),
	);
	const program = t.program([t.expressionStatement(func)]);
	const file = t.file(program);
	let changed = false;
	traverse(file, {
		Function(path) {
			changed = recoverEmbeddedObjectRestForFunction(path);
			path.stop();
		},
	});

	const code = generate(program).code;
	assert.equal(changed, true);
	assert.doesNotMatch(code, /copyDataProperties|r1_1 === undefined/);
	assert.match(code, /initialIndex: _env_69786_0 = 0/);
	assert.match(code, /\.\.\._rest_69786_0_/);
});

Deno.test('declared object-rest copy avoids existing lexical assignment target', () => {
	const copyDataProperties = t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		[
			t.objectExpression([]),
			t.identifier('_param_4384_0_'),
			t.objectExpression([
				t.objectProperty(t.identifier('__proto__'), t.nullLiteral()),
				t.objectProperty(t.identifier('value'), t.numericLiteral(0)),
			]),
		],
	);
	const func = t.functionExpression(
		null,
		[t.identifier('_param_4384_0_')],
		t.blockStatement([
			t.variableDeclaration('let', [
				t.variableDeclarator(t.identifier('r0_1')),
			]),
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.identifier('r0_1'),
				t.memberExpression(
					t.identifier('_param_4384_0_'),
					t.identifier('value'),
				),
			)),
			t.variableDeclaration('const', [
				t.variableDeclarator(t.identifier('r1_1'), copyDataProperties),
			]),
			t.returnStatement(t.memberExpression(
				t.identifier('r1_1'),
				t.identifier('other'),
			)),
		]),
	);
	const program = t.program([t.expressionStatement(func)]);
	const file = t.file(program);
	let changed = false;
	traverse(file, {
		Function(path) {
			changed = recoverEmbeddedObjectRestForFunction(path);
			path.stop();
		},
	});

	const code = generate(program).code;
	assert.equal(changed, true);
	assert.doesNotMatch(code, /value: r0_1/);
	assert.match(code, /let r0_1;/);
	assert.match(code, /r0_1 = _value;/);
	assert.match(code, /return _rest_4384_0_\.other;/);
});

Deno.test('direct object default aliases recover global var destructuring', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r0_4'),
				t.memberExpression(
					t.objectExpression([]),
					t.identifier('abc'),
				),
			),
		]),
		t.variableDeclaration('var', [
			t.variableDeclarator(
				t.identifier('abc'),
				t.conditionalExpression(
					t.binaryExpression(
						'===',
						t.identifier('r0_4'),
						t.identifier('undefined'),
					),
					t.functionExpression(
						t.identifier('abc'),
						[],
						t.blockStatement([]),
					),
					t.identifier('r0_4'),
				),
			),
		]),
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r0_11'),
				t.memberExpression(
					t.objectExpression([]),
					t.identifier('abc'),
				),
			),
		]),
		t.variableDeclaration('var', [
			t.variableDeclarator(
				t.identifier('def'),
				t.conditionalExpression(
					t.binaryExpression(
						'===',
						t.identifier('r0_11'),
						t.identifier('undefined'),
					),
					t.functionExpression(
						t.identifier('def'),
						[],
						t.blockStatement([]),
					),
					t.identifier('r0_11'),
				),
			),
		]),
	];

	assert.equal(recoverDirectObjectDefaultAliasesInBody(body), 2);
	assert.equal(
		generate(t.program(body)).code,
		'var {\n' +
			'  abc = function abc() {}\n' +
			'} = {};\n' +
			'var {\n' +
			'  abc: def = function def() {}\n' +
			'} = {};',
	);
});

Deno.test('declared global array destructuring is placed at assignment', () => {
	const hoist = (name: string) => {
		const declaration = t.variableDeclarator(t.identifier(name));
		declaration.extra = { isDeclaredGlobal: true };
		return t.variableDeclaration('var', [declaration]);
	};
	const destructuring = t.expressionStatement(t.assignmentExpression(
		'=',
		t.arrayPattern([
			t.assignmentPattern(
				t.identifier('foo'),
				t.functionExpression(
					t.identifier('foo'),
					[],
					t.blockStatement([]),
				),
			),
			t.assignmentPattern(
				t.identifier('bar'),
				t.functionExpression(
					t.identifier('bar'),
					[],
					t.blockStatement([]),
				),
			),
		]),
		t.arrayExpression([]),
	));
	destructuring.extra = { fromDestructuring: true };
	const body: t.Statement[] = [
		hoist('foo'),
		hoist('bar'),
		destructuring,
	];

	assert.equal(
		recoverDeclaredGlobalDestructuringAssignments(
			body,
			new Set(['foo', 'bar']),
		),
		1,
	);
	assert.equal(
		generate(t.program(body)).code,
		'var [foo = function foo() {}, bar = function bar() {}] = [];',
	);
});

Deno.test('unbound object destructuring globals are declared in place', () => {
	const body: t.Statement[] = [
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.objectPattern([
				t.objectProperty(
					t.identifier('abc'),
					t.assignmentPattern(
						t.identifier('abc'),
						t.functionExpression(
							t.identifier('abc'),
							[],
							t.blockStatement([]),
						),
					),
					false,
					true,
				),
			]),
			t.objectExpression([]),
		)),
		t.expressionStatement(t.callExpression(
			t.identifier('print'),
			[
				t.memberExpression(
					t.memberExpression(
						t.identifier('global'),
						t.identifier('abc'),
					),
					t.identifier('name'),
				),
			],
		)),
	];

	assert.equal(
		recoverDeclaredGlobalDestructuringAssignments(body, new Set()),
		1,
	);
	assert.equal(
		generate(t.program(body)).code,
		'var {\n' +
			'  abc = function abc() {}\n' +
			'} = {};\n' +
			'print(global.abc.name);',
	);
});

function recoveredEnvironmentLookup(
	statements: t.Statement[],
): t.Expression | undefined {
	const file = t.file(t.program(statements));
	let recovered: t.Expression | undefined;
	traverse(file, {
		CallExpression(path) {
			if (
				!t.isV8IntrinsicIdentifier(path.node.callee, {
					name: 'expectEnvironment',
				})
			) return;
			const [argument] = path.get('arguments');
			if (argument?.isIdentifier()) {
				recovered = assignedEnvironmentLookupForUse(argument);
			}
		},
	});
	return recovered;
}

function parentEnvironmentLookup(depth: number) {
	return t.callExpression(
		t.v8IntrinsicIdentifier('GetParentEnvironment'),
		[t.numericLiteral(depth)],
	);
}

Deno.test('dead environment lookup handles are removed', () => {
	// Resolution rewrites every `%expectEnvironment(h)[slot]` use to an
	// `_env_*` name, which is what leaves the handle unread.
	const program = t.program([
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r2_1'),
				parentEnvironmentLookup(0),
			),
		]),
		t.expressionStatement(t.identifier('_env_7_3')),
	]);
	const file = t.file(program);

	assert.equal(removeDeadEnvironmentLookupHandles(file), 1);
	assert.equal(generate(program).code, '_env_7_3;');
});

Deno.test('dead split environment lookup handles are removed', () => {
	const program = t.program([
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r2_1')),
		]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier('r2_1'),
			parentEnvironmentLookup(0),
		)),
		t.expressionStatement(t.identifier('_env_7_3')),
	]);
	const file = t.file(program);

	assert.equal(removeDeadEnvironmentLookupHandles(file), 2);
	assert.equal(generate(program).code, '_env_7_3;');
});

Deno.test('dead sequence environment lookup handles are removed', () => {
	const program = t.program([
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r2_1')),
		]),
		t.expressionStatement(t.sequenceExpression([
			t.assignmentExpression(
				'=',
				t.identifier('r2_1'),
				parentEnvironmentLookup(0),
			),
			t.identifier('_env_7_3'),
		])),
	]);
	const file = t.file(program);

	assert.equal(removeDeadEnvironmentLookupHandles(file), 2);
	assert.equal(generate(program).code, '_env_7_3;');
});

Deno.test('discarded bare environment lookups are removed', () => {
	const program = t.program([
		t.expressionStatement(t.sequenceExpression([
			parentEnvironmentLookup(0),
			t.callExpression(t.identifier('effect'), []),
		])),
	]);
	const file = t.file(program);

	assert.equal(removeDeadEnvironmentLookupHandles(file), 1);
	assert.equal(generate(program).code, 'effect();');
});

Deno.test('dead environment lookup stores are removed from mixed bindings', () => {
	const program = t.program([
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r3_1')),
		]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier('r3_1'),
			parentEnvironmentLookup(0),
		)),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier('r3_1'),
			t.callExpression(t.identifier('effect'), []),
		)),
	]);
	const file = t.file(program);

	assert.equal(removeDeadEnvironmentLookupHandles(file), 1);
	assert.equal(
		generate(program).code,
		'let r3_1;\nr3_1 = effect();',
	);
});

Deno.test('generated sequence aliases inline without reordering reads', () => {
	const program = t.program([
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r0_1')),
			t.variableDeclarator(t.identifier('r2_1')),
		]),
		t.expressionStatement(t.sequenceExpression([
			t.assignmentExpression(
				'=',
				t.identifier('r0_1'),
				t.identifier('global'),
			),
			t.assignmentExpression(
				'=',
				t.identifier('r2_1'),
				t.memberExpression(
					t.identifier('r0_1'),
					t.identifier('Symbol'),
				),
			),
			t.binaryExpression(
				'!==',
				t.stringLiteral('function'),
				t.unaryExpression('typeof', t.identifier('r2_1')),
			),
		])),
	]);
	const file = t.file(program);

	assert.equal(simplifyGeneratedSequenceAssignments(file), 2);
	assert.equal(
		generate(program).code,
		'"function" !== typeof global.Symbol;',
	);
});

Deno.test('sequence-exposed Hermes concat calls lift after inlining', () => {
	const file = parse(
		`
		function log(guard, logger, value) {
			let r4_3, r3_5, r6_2, r1_12;
			return guard || (
				r4_3 = logger,
				r3_5 = r4_3.info,
				r6_2 = JSON.stringify(value),
				r1_12 = HermesInternal.concat.call("Media sink wants: ", r6_2),
				r3_5.call(r4_3, r1_12)
			);
		}
	`,
		{ sourceType: 'script' },
	);

	simplifyGeneratedSequenceAssignments(file);
	assert.equal(liftHermesConcatCalls(file), 1);
	simplifyGeneratedSequenceAssignments(file);
	assert.equal(
		generate(file).code,
		'function log(guard, logger, value) {\n' +
			'  return guard || logger.info(`Media sink wants: ${JSON.stringify(value)}`);\n' +
			'}',
	);
});

Deno.test('sequence Hermes apply recovers member spread calls', () => {
	const file = parse(
		`
		function append(guard, target, values, done) {
			let r1_1, r2_1, r3_1;
			return guard || (
				r3_1 = target,
				r2_1 = r3_1.push,
				r1_1 = [...values],
				HermesInternal.apply(r2_1, r1_1, r3_1),
				done
			);
		}
		function maximum(guard, values) {
			let r1_1, r2_1, r3_1, r4_1;
			return guard || (
				r4_1 = Math,
				r3_1 = r4_1.max,
				r2_1 = [...values],
				r1_1 = HermesInternal.apply(r3_1, r2_1, r4_1),
				Number.isNaN(r1_1)
			);
		}
	`,
		{ sourceType: 'script' },
	);

	simplifyGeneratedSequenceAssignments(file);

	assert.equal(
		generate(file).code,
		'function append(guard, target, values, done) {\n' +
			'  return guard || (target.push(...values), done);\n' +
			'}\n' +
			'function maximum(guard, values) {\n' +
			'  let r1_1;\n' +
			'  return guard || (r1_1 = Math.max(...values), Number.isNaN(r1_1));\n' +
			'}',
	);
});

Deno.test('immutable split sequence values inline into their selected arm', () => {
	const program = t.program([
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r0_3')),
		]),
		t.returnStatement(t.conditionalExpression(
			t.sequenceExpression([
				t.assignmentExpression(
					'=',
					t.identifier('r0_3'),
					t.stringLiteral('symbol'),
				),
				t.identifier('guard'),
			]),
			t.unaryExpression('typeof', t.identifier('value')),
			t.identifier('r0_3'),
		)),
	]);
	const file = t.file(program);

	assert.equal(simplifyGeneratedSequenceAssignments(file), 1);
	assert.equal(
		generate(program).code,
		'return guard ? typeof value : "symbol";',
	);
});

Deno.test('immutable split replacement covers rewritten sequence branches', () => {
	const file = parse(
		`
		function convert(guard, values) {
			let r1_1, r2_1;
			return guard ||
					(r1_1 = 0, r2_1 = 1, values[r1_1] === values[r2_1]) ||
					!(values[r1_1] === values[r2_1])
				? values.join("")
				: values[r1_1] + values[r2_1];
		}
	`,
		{ sourceType: 'script' },
	);

	assert.equal(simplifyGeneratedSequenceAssignments(file), 2);
	assert.equal(
		generate(file).code,
		'function convert(guard, values) {\n' +
			'  return guard || values[0] === values[1] || !(values[0] === values[1]) ' +
			'? values.join("") : values[0] + values[1];\n' +
			'}',
	);
});

Deno.test('sequence assignment inlining does not cross unrelated effects', () => {
	const program = t.program([
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r1_1')),
		]),
		t.expressionStatement(t.sequenceExpression([
			t.assignmentExpression(
				'=',
				t.identifier('r1_1'),
				t.callExpression(t.identifier('acquire'), []),
			),
			t.callExpression(t.identifier('before'), []),
			t.callExpression(t.identifier('use'), [t.identifier('r1_1')]),
		])),
	]);
	const file = t.file(program);

	assert.equal(simplifyGeneratedSequenceAssignments(file), 0);
	assert.equal(
		generate(program).code,
		'let r1_1;\nr1_1 = acquire(), before(), use(r1_1);',
	);
});

Deno.test('generated sequence arrays inline across ordered setup effects', () => {
	const file = parse(
		`
		function build(guard, first, second) {
			let r1_1, r2_1, r3_1, r4_1, r5_1, r6_1;
			return guard || (
				r4_1 = Object,
				r5_1 = r4_1.keys,
				r6_1 = r5_1.call(r4_1, first),
				r1_1 = [],
				r2_1 = HermesInternal.arraySpread(r1_1, r6_1, 0),
				r3_1 = load(),
				HermesInternal.arraySpread(r1_1, second, r2_1),
				use(r1_1, r3_1)
			);
		}
	`,
		{ sourceType: 'script' },
	);

	simplifyGeneratedSequenceAssignments(file);

	assert.equal(
		generate(file).code,
		'function build(guard, first, second) {\n' +
			'  let r3_1;\n' +
			'  return guard || use([...Object.keys(first), ' +
			'...(r3_1 = load(), second)], r3_1);\n' +
			'}',
	);
});

Deno.test('sequence arrays remain explicit where a catch can observe them', () => {
	const file = parse(
		`
		function build(source) {
			let r1_1;
			try {
				return (
					r1_1 = [],
					HermesInternal.arraySpread(r1_1, source, 0),
					r1_1
				);
			} catch {
				return r1_1;
			}
		}
	`,
		{ sourceType: 'script' },
	);

	simplifyGeneratedSequenceAssignments(file);

	assert.match(
		generate(file).code,
		/HermesInternal\.arraySpread\(r1_1, source, 0\)/,
	);
});

Deno.test('sequence member calls preserve an explicit receiver mismatch', () => {
	const file = parse(
		`
		function invoke(left, right, value) {
			let r1_1;
			return (
				r1_1 = left.method,
				r1_1.call(right, value)
			);
		}
	`,
		{ sourceType: 'script' },
	);

	simplifyGeneratedSequenceAssignments(file);

	assert.equal(
		generate(file).code,
		'function invoke(left, right, value) {\n' +
			'  return left.method.call(right, value);\n' +
			'}',
	);
});

Deno.test('a read environment lookup handle is kept', () => {
	const program = t.program([
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r2_1'),
				parentEnvironmentLookup(0),
			),
		]),
		t.expressionStatement(
			t.callExpression(t.v8IntrinsicIdentifier('expectEnvironment'), [
				t.identifier('r2_1'),
			]),
		),
	]);
	const file = t.file(program);

	assert.equal(removeDeadEnvironmentLookupHandles(file), 0);
});

Deno.test('an unread environment creation is kept', () => {
	// `%CreateFunctionEnvironment` allocates; an unread lookup is a pure read,
	// an unread creation is not obviously unobservable.
	const program = t.program([
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r2_1'),
				t.callExpression(
					t.v8IntrinsicIdentifier('CreateFunctionEnvironment'),
					[],
				),
			),
		]),
	]);
	const file = t.file(program);

	assert.equal(removeDeadEnvironmentLookupHandles(file), 0);
});

Deno.test('a reassigned environment handle is kept', () => {
	const program = t.program([
		t.variableDeclaration('let', [
			t.variableDeclarator(
				t.identifier('r2_1'),
				parentEnvironmentLookup(0),
			),
		]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier('r2_1'),
			parentEnvironmentLookup(1),
		)),
	]);
	const file = t.file(program);

	assert.equal(removeDeadEnvironmentLookupHandles(file), 0);
});

Deno.test(
	'assigned environment lookup recovery spans one switch case',
	() => {
		// Hermes assigns the handle inside the case that uses it. Falling
		// through from an earlier case enters a consequent at the top, never in
		// the middle, so an earlier statement in the list always runs first.
		const environment = () => t.identifier('r7_1');
		const recovered = recoveredEnvironmentLookup([
			t.variableDeclaration('let', [
				t.variableDeclarator(environment()),
			]),
			t.switchStatement(t.identifier('kind'), [
				t.switchCase(t.stringLiteral('string'), [
					t.expressionStatement(t.assignmentExpression(
						'=',
						environment(),
						parentEnvironmentLookup(0),
					)),
					t.expressionStatement(t.callExpression(
						t.v8IntrinsicIdentifier('expectEnvironment'),
						[environment()],
					)),
				]),
			]),
		]);

		assert.ok(recovered, 'expected the lookup to be recovered');
		assert.equal(generate(recovered).code, '%GetParentEnvironment(0)');
	},
);

Deno.test(
	'assigned environment lookup recovery rejects a sibling switch case',
	() => {
		// The write is in a case the use's case is not reached through, so it
		// may never have run.
		const environment = () => t.identifier('r7_1');
		const recovered = recoveredEnvironmentLookup([
			t.variableDeclaration('let', [
				t.variableDeclarator(environment()),
			]),
			t.switchStatement(t.identifier('kind'), [
				t.switchCase(t.stringLiteral('number'), [
					t.expressionStatement(t.assignmentExpression(
						'=',
						environment(),
						parentEnvironmentLookup(0),
					)),
					t.breakStatement(),
				]),
				t.switchCase(t.stringLiteral('string'), [
					t.expressionStatement(t.callExpression(
						t.v8IntrinsicIdentifier('expectEnvironment'),
						[environment()],
					)),
				]),
			]),
		]);

		assert.equal(recovered, undefined);
	},
);

Deno.test(
	'assigned environment lookup recovery requires a dominating equivalent write',
	() => {
		const environment = () => t.identifier('r5_1');
		const use = () =>
			t.expressionStatement(
				t.callExpression(t.v8IntrinsicIdentifier('expectEnvironment'), [
					environment(),
				]),
			);

		const recovered = recoveredEnvironmentLookup([
			t.variableDeclaration('let', [
				t.variableDeclarator(environment()),
			]),
			t.ifStatement(
				t.identifier('ready'),
				t.blockStatement([
					t.expressionStatement(
						t.assignmentExpression(
							'=',
							environment(),
							parentEnvironmentLookup(2),
						),
					),
					use(),
				]),
			),
		]);
		assert.ok(t.isCallExpression(recovered));
		assert.deepEqual(recovered, parentEnvironmentLookup(2));

		const guardedAlternate = recoveredEnvironmentLookup([
			t.variableDeclaration('let', [
				t.variableDeclarator(environment()),
			]),
			t.ifStatement(
				t.logicalExpression(
					'||',
					t.identifier('alreadyDone'),
					t.sequenceExpression([
						t.assignmentExpression(
							'=',
							environment(),
							parentEnvironmentLookup(2),
						),
						t.unaryExpression('!', t.identifier('ready')),
					]),
				),
				t.blockStatement([]),
				t.blockStatement([use()]),
			),
		]);
		assert.deepEqual(guardedAlternate, parentEnvironmentLookup(2));

		const nonDominating = recoveredEnvironmentLookup([
			t.variableDeclaration('let', [
				t.variableDeclarator(environment()),
			]),
			t.ifStatement(
				t.identifier('ready'),
				t.expressionStatement(
					t.assignmentExpression(
						'=',
						environment(),
						parentEnvironmentLookup(2),
					),
				),
			),
			use(),
		]);
		assert.equal(nonDominating, undefined);

		const conflicting = recoveredEnvironmentLookup([
			t.variableDeclaration('let', [
				t.variableDeclarator(environment()),
			]),
			t.expressionStatement(
				t.assignmentExpression(
					'=',
					environment(),
					parentEnvironmentLookup(1),
				),
			),
			t.expressionStatement(
				t.assignmentExpression(
					'=',
					environment(),
					parentEnvironmentLookup(2),
				),
			),
			use(),
		]);
		assert.equal(conflicting, undefined);
	},
);

Deno.test(
	'assigned environment lookup recovery crosses only a non-throwing protected prefix',
	() => {
		const environment = () => t.identifier('r5_1');
		const use = () =>
			t.expressionStatement(
				t.callExpression(
					t.v8IntrinsicIdentifier('expectEnvironment'),
					[environment()],
				),
			);
		const declaration = () =>
			t.variableDeclaration('let', [
				t.variableDeclarator(environment()),
				t.variableDeclarator(t.identifier('r4_1')),
			]);
		const lookupAssignment = () =>
			t.expressionStatement(
				t.assignmentExpression(
					'=',
					environment(),
					parentEnvironmentLookup(2),
				),
			);
		const harmlessInitializer = () =>
			t.expressionStatement(
				t.assignmentExpression(
					'=',
					t.identifier('r4_1'),
					t.identifier('undefined'),
				),
			);

		const caught = recoveredEnvironmentLookup([
			declaration(),
			t.tryStatement(
				t.blockStatement([
					harmlessInitializer(),
					lookupAssignment(),
					t.expressionStatement(
						t.callExpression(t.identifier('mayThrow'), []),
					),
				]),
				t.catchClause(
					t.identifier('error'),
					t.blockStatement([use()]),
				),
			),
		]);
		assert.deepEqual(caught, parentEnvironmentLookup(2));

		const finalized = recoveredEnvironmentLookup([
			declaration(),
			t.tryStatement(
				t.blockStatement([lookupAssignment()]),
				null,
				t.blockStatement([use()]),
			),
		]);
		assert.deepEqual(finalized, parentEnvironmentLookup(2));

		const nestedFinalizer = recoveredEnvironmentLookup([
			declaration(),
			t.tryStatement(
				t.blockStatement([lookupAssignment()]),
				null,
				t.blockStatement([
					t.tryStatement(
						t.blockStatement([
							t.throwStatement(t.identifier('error')),
						]),
						null,
						t.blockStatement([use()]),
					),
				]),
			),
		]);
		assert.deepEqual(nestedFinalizer, parentEnvironmentLookup(2));

		const assignmentAfterCall = recoveredEnvironmentLookup([
			declaration(),
			t.tryStatement(
				t.blockStatement([
					t.expressionStatement(
						t.callExpression(t.identifier('mayThrow'), []),
					),
					lookupAssignment(),
				]),
				t.catchClause(
					t.identifier('error'),
					t.blockStatement([use()]),
				),
			),
		]);
		assert.equal(assignmentAfterCall, undefined);

		const guardedAssignment = recoveredEnvironmentLookup([
			declaration(),
			t.tryStatement(
				t.blockStatement([
					t.ifStatement(
						t.identifier('ready'),
						lookupAssignment(),
					),
				]),
				t.catchClause(
					t.identifier('error'),
					t.blockStatement([use()]),
				),
			),
		]);
		assert.equal(guardedAssignment, undefined);

		const deadLookup = t.assignmentExpression(
			'=',
			environment(),
			parentEnvironmentLookup(2),
		);
		const deadLookupFile = t.file(t.program([
			declaration(),
			t.tryStatement(
				t.blockStatement([
					t.expressionStatement(deadLookup),
					t.expressionStatement(
						t.callExpression(t.identifier('mayThrow'), []),
					),
				]),
				t.catchClause(
					t.identifier('error'),
					t.blockStatement([
						t.expressionStatement(t.identifier('_env_1_0')),
					]),
				),
			),
		]));
		assert.equal(
			removeDeadRecoveredProtectedEnvironmentHandles(
				deadLookupFile,
				new WeakSet([deadLookup]),
			),
			1,
		);
		assert.doesNotMatch(
			generate(deadLookupFile).code,
			/GetParentEnvironment/,
		);
		assert.doesNotMatch(generate(deadLookupFile).code, /r5_1/);
	},
);

Deno.test(
	'destructured parameter promotion carries defaults in nested arrays',
	() => {
		const source = t.identifier('_param_14_0_');
		const func = t.functionExpression(
			null,
			[t.cloneNode(source)],
			t.blockStatement([
				t.variableDeclaration('var', [
					t.variableDeclarator(
						t.objectPattern([
							t.objectProperty(
								t.identifier('outer'),
								t.arrayPattern([t.identifier('value')]),
							),
						]),
						t.cloneNode(source),
					),
				]),
				t.returnStatement(t.conditionalExpression(
					t.binaryExpression(
						'===',
						t.identifier('value'),
						t.identifier('undefined'),
					),
					t.callExpression(t.identifier('innerDefault'), []),
					t.identifier('value'),
				)),
			]),
		);

		hoistDestructuredFunctionParams(func);

		assert.equal(
			generate(func).code,
			'function ({\n' +
				'  outer: [value = innerDefault()]\n' +
				'}) {\n' +
				'  return value;\n' +
				'}',
		);
	},
);

Deno.test(
	'destructured parameter promotion preserves outer and inner defaults',
	() => {
		const source = t.identifier('_param_12_0_');
		const func = t.functionExpression(
			null,
			[t.cloneNode(source)],
			t.blockStatement([
				t.variableDeclaration('var', [
					t.variableDeclarator(
						t.objectPattern([
							t.objectProperty(
								t.identifier('value'),
								t.assignmentPattern(
									t.identifier('value'),
									t.callExpression(
										t.identifier('innerDefault'),
										[],
									),
								),
								false,
								true,
							),
						]),
						t.conditionalExpression(
							t.binaryExpression(
								'===',
								t.cloneNode(source),
								t.identifier('undefined'),
							),
							t.callExpression(t.identifier('outerDefault'), []),
							t.cloneNode(source),
						),
					),
				]),
				t.returnStatement(t.identifier('value')),
			]),
		);

		hoistDestructuredFunctionParams(func);

		assert.equal(
			generate(func).code,
			'function ({\n' +
				'  value = innerDefault()\n' +
				'} = outerDefault()) {\n' +
				'  return value;\n' +
				'}',
		);
	},
);

Deno.test(
	'destructured parameter promotion refuses residual raw parameter uses',
	() => {
		const source = t.identifier('_param_13_0_');
		const func = t.functionExpression(
			null,
			[t.cloneNode(source)],
			t.blockStatement([
				t.variableDeclaration('var', [
					t.variableDeclarator(
						t.arrayPattern([t.identifier('first')]),
						t.conditionalExpression(
							t.binaryExpression(
								'!==',
								t.cloneNode(source),
								t.identifier('undefined'),
							),
							t.cloneNode(source),
							t.arrayExpression([]),
						),
					),
				]),
				t.expressionStatement(t.cloneNode(source)),
			]),
		);

		hoistDestructuredFunctionParams(func);

		assert.ok(t.isIdentifier(func.params[0], { name: source.name }));
		assert.equal(func.body.body.length, 2);
	},
);

Deno.test('member-only object parameter uses become a parameter pattern', () => {
	const source = t.identifier('_param_71691_0_');
	const func = t.functionDeclaration(
		t.identifier('SceneView'),
		[t.cloneNode(source)],
		t.blockStatement([
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('focused'),
					t.memberExpression(
						t.cloneNode(source),
						t.identifier('focused'),
					),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.objectPattern([
						t.objectProperty(
							t.identifier('route'),
							t.identifier('route'),
							false,
							true,
						),
					]),
					t.memberExpression(
						t.cloneNode(source),
						t.identifier('descriptor'),
					),
				),
			]),
			t.returnStatement(t.arrayExpression([
				t.identifier('focused'),
				t.identifier('route'),
				t.memberExpression(t.cloneNode(source), t.identifier('index')),
			])),
		]),
	);

	hoistDestructuredFunctionParams(func);

	assert.equal(
		generate(func).code,
		'function SceneView({\n' +
			'  focused,\n' +
			'  descriptor: {\n' +
			'    route\n' +
			'  },\n' +
			'  index: _index\n' +
			'}) {\n' +
			'  return [focused, route, _index];\n' +
			'}',
	);
});

Deno.test('object member aliases promote repeated pattern defaults', () => {
	const gestureKey = t.identifier('gestureEnabled');
	gestureKey.extra = {
		memberReadDestination: { type: 'register', index: 2, version: 4 },
	};
	const func = t.functionDeclaration(
		t.identifier('SceneView'),
		[t.identifier('_param_71691_0_')],
		t.blockStatement([
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('options'),
					t.memberExpression(
						t.identifier('_param_71691_0_'),
						t.identifier('options'),
					),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('animationTypeForReplace'),
					t.memberExpression(
						t.identifier('options'),
						t.identifier('animationTypeForReplace'),
					),
				),
			]),
			t.expressionStatement(
				t.memberExpression(
					t.identifier('options'),
					gestureKey,
				),
			),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('sheetExpandsWhenScrolledToEdge'),
					t.memberExpression(
						t.identifier('options'),
						t.identifier('sheetExpandsWhenScrolledToEdge'),
					),
				),
			]),
			t.returnStatement(t.objectExpression([
				t.objectProperty(
					t.identifier('replaceAnimation'),
					t.conditionalExpression(
						t.binaryExpression(
							'===',
							t.identifier('undefined'),
							t.identifier('animationTypeForReplace'),
						),
						t.stringLiteral('push'),
						t.identifier('animationTypeForReplace'),
					),
				),
				t.objectProperty(
					t.identifier('sheetExpandsWhenScrolledToEdge'),
					t.conditionalExpression(
						t.binaryExpression(
							'===',
							t.identifier('undefined'),
							t.identifier('sheetExpandsWhenScrolledToEdge'),
						),
						t.binaryExpression(
							'===',
							t.identifier('undefined'),
							t.identifier('sheetExpandsWhenScrolledToEdge'),
						),
						t.identifier('sheetExpandsWhenScrolledToEdge'),
					),
				),
			])),
		]),
	);

	hoistDestructuredFunctionParams(func);

	assert.equal(
		generate(func).code,
		'function SceneView(_param_71691_0_) {\n' +
			'  const options = _param_71691_0_.options;\n' +
			'  const {\n' +
			'    animationTypeForReplace = "push",\n' +
			'    gestureEnabled: r2_4,\n' +
			'    sheetExpandsWhenScrolledToEdge = true\n' +
			'  } = options;\n' +
			'  return {\n' +
			'    replaceAnimation: animationTypeForReplace,\n' +
			'    sheetExpandsWhenScrolledToEdge: sheetExpandsWhenScrolledToEdge\n' +
			'  };\n' +
			'}',
	);
});

Deno.test('pattern defaults stay in the body when they write body bindings', () => {
	const environment = t.identifier('_env_102391_0');
	const selected = t.identifier('r1_1');
	const func = t.functionDeclaration(
		t.identifier('target'),
		[
			t.objectPattern([
				t.objectProperty(
					t.identifier('pending'),
					t.cloneNode(selected),
				),
			]),
		],
		t.blockStatement([
			t.variableDeclaration('var', [
				t.variableDeclarator(t.cloneNode(environment)),
			]),
			t.returnStatement(t.arrayExpression([
				t.conditionalExpression(
					t.binaryExpression(
						'===',
						t.identifier('undefined'),
						t.cloneNode(selected),
					),
					t.assignmentExpression(
						'=',
						t.cloneNode(environment),
						t.callExpression(t.identifier('useSetting'), []),
					),
					t.cloneNode(selected),
				),
				t.arrowFunctionExpression([], t.cloneNode(environment)),
			])),
		]),
	);

	hoistDestructuredFunctionParams(func);

	let calls = 0;
	const instantiate = new globalThis.Function(
		'useSetting',
		`${generate(func).code}\nreturn target;`,
	) as (useSetting: () => string) => (
		value: { pending?: string },
	) => [string, () => string];
	const target = instantiate(() => {
		calls++;
		return 'current';
	});
	const [value, captured] = target({});
	assert.equal(value, 'current');
	assert.equal(captured(), 'current');
	assert.equal(calls, 1);
});

Deno.test('object member aliases fold unreferenced computed registers', () => {
	const func = t.functionDeclaration(
		t.identifier('readIndexed'),
		[t.identifier('source')],
		t.blockStatement([
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r0_1'),
					t.memberExpression(
						t.identifier('source'),
						t.numericLiteral(0),
						true,
					),
				),
			]),
			t.returnStatement(t.nullLiteral()),
		]),
	);

	hoistDestructuredFunctionParams(func);

	assert.equal(
		generate(func).code,
		'function readIndexed(source) {\n' +
			'  const {\n' +
			'    [0]: r0_1\n' +
			'  } = source;\n' +
			'  return null;\n' +
			'}',
	);
});

Deno.test('object member aliases decline a written-through parameter', () => {
	const source = t.identifier('_param_132_4_');
	const func = t.functionDeclaration(
		t.identifier('factory'),
		[t.cloneNode(source)],
		t.blockStatement([
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.memberExpression(
					t.cloneNode(source),
					t.identifier('exports'),
				),
				t.identifier('value'),
			)),
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.memberExpression(
					t.memberExpression(
						t.cloneNode(source),
						t.identifier('exports'),
					),
					t.identifier('__esModule'),
				),
				t.booleanLiteral(true),
			)),
		]),
	);

	hoistDestructuredFunctionParams(func);

	assert.ok(t.isIdentifier(func.params[0], { name: source.name }));
	assert.match(generate(func).code, /_param_132_4_\.exports = value/);
	assert.match(
		generate(func).code,
		/_param_132_4_\.exports\.__esModule = true/,
	);
});

Deno.test('object member aliases decline a read after an observable effect', () => {
	const source = t.identifier('_param_140_0_');
	const func = t.functionDeclaration(
		t.identifier('lateRead'),
		[t.cloneNode(source)],
		t.blockStatement([
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r0_1'),
				t.memberExpression(
					t.cloneNode(source),
					t.identifier('first'),
				),
			)]),
			t.expressionStatement(t.callExpression(
				t.identifier('mutate'),
				[t.identifier('r0_1')],
			)),
			t.returnStatement(t.memberExpression(
				t.cloneNode(source),
				t.identifier('second'),
			)),
		]),
	);

	hoistDestructuredFunctionParams(func);

	assert.ok(t.isIdentifier(func.params[0], { name: source.name }));
	assert.match(generate(func).code, /return _param_140_0_\.second/);
});

Deno.test('object member aliases decline a lone property read', () => {
	const source = t.identifier('_param_141_5_');
	const func = t.functionDeclaration(
		t.identifier('single'),
		[t.cloneNode(source)],
		t.blockStatement([
			t.returnStatement(t.memberExpression(
				t.cloneNode(source),
				t.identifier('exports'),
			)),
		]),
	);

	hoistDestructuredFunctionParams(func);

	assert.equal(
		generate(func).code,
		'function single(_param_141_5_) {\n' +
			'  return _param_141_5_.exports;\n' +
			'}',
	);
});

Deno.test('object member aliases decline computed numeric parameter keys', () => {
	const source = t.identifier('_param_141_6_');
	const func = t.functionDeclaration(
		t.identifier('dependencyMap'),
		[t.cloneNode(source)],
		t.blockStatement([
			t.returnStatement(t.arrayExpression([
				t.memberExpression(
					t.cloneNode(source),
					t.numericLiteral(0),
					true,
				),
				t.memberExpression(
					t.cloneNode(source),
					t.numericLiteral(1),
					true,
				),
			])),
		]),
	);

	hoistDestructuredFunctionParams(func);

	assert.ok(t.isIdentifier(func.params[0], { name: source.name }));
	assert.match(
		generate(func).code,
		/return \[_param_141_6_\[0\], _param_141_6_\[1\]\]/,
	);
});

Deno.test(
	'destructured assignment promotion adopts a composed environment slot',
	() => {
		const source = t.identifier('_param_109726_0_');
		const slot = t.identifier('_env_109726_0');
		const assignment = t.expressionStatement(t.assignmentExpression(
			'=',
			t.arrayPattern([
				t.cloneNode(slot),
				t.objectPattern([
					t.objectProperty(
						t.identifier('headerTitle'),
						t.identifier('r13_1'),
					),
				]),
			]),
			t.cloneNode(source),
		));
		assignment.extra = { fromDestructuring: true };
		const func = t.functionExpression(
			null,
			[t.cloneNode(source)],
			t.blockStatement([
				t.variableDeclaration('var', [
					t.variableDeclarator(t.cloneNode(slot)),
				]),
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier('r13_1')),
				]),
				assignment,
				t.returnStatement(t.arrayExpression([
					t.cloneNode(slot),
					t.identifier('r13_1'),
				])),
			]),
		);

		hoistDestructuredFunctionParams(func);

		assert.equal(
			generate(func).code,
			'function ([_env_109726_0, {\n' +
				'  headerTitle: r13_1\n' +
				'}]) {\n' +
				'  return [_env_109726_0, r13_1];\n' +
				'}',
		);
	},
);

Deno.test(
	'rest parameter alias promotion exposes generator priming yields',
	() => {
		const func = t.functionExpression(
			null,
			[t.restElement(t.identifier('_rest_12_'))],
			t.blockStatement([
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier('pending')),
				]),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r2_1'),
						t.identifier('_rest_12_'),
					),
				]),
				t.expressionStatement(t.yieldExpression(
					t.identifier('undefined'),
				)),
				t.returnStatement(t.identifier('r2_1')),
			]),
			true,
		);

		hoistDestructuredFunctionParams(func);

		assert.equal(
			generate(func).code,
			'function* (...r2_1) {\n' +
				'  let pending;\n' +
				'  yield undefined;\n' +
				'  return r2_1;\n' +
				'}',
		);
	},
);

Deno.test(
	'primed generator property probes become an object parameter',
	() => {
		const source = t.identifier('_param_29644_0_');
		const func = t.functionExpression(
			null,
			[t.cloneNode(source)],
			t.blockStatement([
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier('pending')),
				]),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r11_1'),
						t.memberExpression(
							t.cloneNode(source),
							t.identifier('createPromise'),
						),
					),
				]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.identifier('state'),
					t.identifier('undefined'),
				)),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r12_1'),
						t.memberExpression(
							t.cloneNode(source),
							t.identifier('webpackId'),
						),
					),
				]),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.objectPattern([
							t.objectProperty(
								t.identifier('name'),
								t.assignmentPattern(
									t.identifier('r13_1'),
									t.stringLiteral('unknown'),
								),
							),
						]),
						t.cloneNode(source),
					),
				]),
				t.expressionStatement(t.yieldExpression(
					t.identifier('undefined'),
				)),
				t.returnStatement(t.arrayExpression([
					t.identifier('r11_1'),
					t.identifier('r12_1'),
					t.identifier('r13_1'),
				])),
			]),
			true,
		);

		assert.equal(hoistPrimedGeneratorObjectParams(func), true);
		assert.equal(
			generate(func).code,
			'function* ({\n' +
				'  createPromise: r11_1,\n' +
				'  webpackId: r12_1,\n' +
				'  name: r13_1 = "unknown"\n' +
				'}) {\n' +
				'  let pending;\n' +
				'  state = undefined;\n' +
				'  yield undefined;\n' +
				'  return [r11_1, r12_1, r13_1];\n' +
				'}',
		);
	},
);

Deno.test(
	'late primed wrapper folding accepts defaults and hoisted setup',
	() => {
		const raw = t.identifier('raw');
		const inner = t.functionExpression(
			t.identifier('inner'),
			[],
			t.blockStatement([
				t.variableDeclaration('var', [
					t.variableDeclarator(t.identifier('captured')),
				]),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.cloneNode(raw),
						t.memberExpression(
							t.identifier('arguments'),
							t.numericLiteral(0),
							true,
						),
					),
				]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.identifier('captured'),
					t.identifier('undefined'),
				)),
				t.functionDeclaration(
					t.identifier('helper'),
					[],
					t.blockStatement([]),
				),
				t.expressionStatement(t.yieldExpression(
					t.identifier('undefined'),
				)),
				t.returnStatement(t.conditionalExpression(
					t.binaryExpression(
						'!==',
						t.cloneNode(raw),
						t.identifier('undefined'),
					),
					t.cloneNode(raw),
					t.booleanLiteral(true),
				)),
			]),
			true,
		);
		const generatorName = t.identifier('generator');
		const wrapper = t.functionExpression(
			t.identifier('wrapper'),
			[],
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.cloneNode(generatorName),
						t.callExpression(inner, []),
					),
				]),
				t.expressionStatement(t.callExpression(
					t.memberExpression(
						t.cloneNode(generatorName),
						t.identifier('next'),
					),
					[],
				)),
				t.returnStatement(t.cloneNode(generatorName)),
			]),
		);

		const collapsed = collapsePrimedNativeGeneratorWrapper(wrapper);
		assert.ok(collapsed?.generator);
		assert.ok(t.isAssignmentPattern(collapsed.params[0]));
		assert.equal(generate(collapsed.params[0]).code, 'raw = true');
		const code = generate(collapsed).code;
		assert.doesNotMatch(code, /yield undefined/);
		assert.doesNotMatch(code, /\.next\(\)/);
		assert.match(code, /captured = undefined/);
		assert.match(code, /function helper\(\)/);
		assert.match(code, /return raw;/);
	},
);

Deno.test(
	'primed default recovery descends into a protected generator body',
	() => {
		const raw = t.identifier('raw');
		const effective = t.identifier('effective');
		const inner = t.functionExpression(
			null,
			[],
			t.blockStatement([
				t.tryStatement(
					t.blockStatement([
						t.variableDeclaration('const', [
							t.variableDeclarator(
								t.cloneNode(raw),
								t.memberExpression(
									t.identifier('arguments'),
									t.numericLiteral(0),
									true,
								),
							),
						]),
						t.variableDeclaration('let', [
							t.variableDeclarator(t.cloneNode(effective)),
						]),
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.cloneNode(effective),
							t.cloneNode(raw),
						)),
						t.ifStatement(
							t.binaryExpression(
								'===',
								t.cloneNode(raw),
								t.identifier('undefined'),
							),
							t.blockStatement([
								t.expressionStatement(t.assignmentExpression(
									'=',
									t.cloneNode(effective),
									t.callExpression(
										t.identifier('defaultValue'),
										[],
									),
								)),
							]),
						),
						t.expressionStatement(t.yieldExpression(
							t.identifier('undefined'),
						)),
						t.returnStatement(t.cloneNode(effective)),
					]),
					null,
					t.blockStatement([]),
				),
			]),
			true,
		);
		const generator = t.identifier('generator');
		const wrapper = t.functionExpression(
			null,
			[],
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.cloneNode(generator),
						t.callExpression(inner, []),
					),
				]),
				t.expressionStatement(t.callExpression(
					t.memberExpression(
						t.cloneNode(generator),
						t.identifier('next'),
					),
					[],
				)),
				t.returnStatement(t.cloneNode(generator)),
			]),
		);

		const collapsed = collapsePrimedNativeGeneratorWrapper(wrapper);
		assert.ok(collapsed);
		assert.equal(
			generate(collapsed.params[0]).code,
			'effective = defaultValue()',
		);
		const code = generate(collapsed).code;
		assert.doesNotMatch(code, /yield undefined/);
		assert.doesNotMatch(code, /arguments\[0\]/);
		assert.match(code, /return effective/);
	},
);

Deno.test(
	'primed generator arguments aliases recover optional destructured params',
	() => {
		const raw = t.identifier('r7_1');
		const func = t.functionExpression(
			null,
			[t.identifier('_param_49398_0_')],
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.cloneNode(raw),
						t.memberExpression(
							t.identifier('arguments'),
							t.numericLiteral(1),
							true,
						),
					),
				]),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.objectPattern([
							t.objectProperty(
								t.identifier('forceExternalBrowser'),
								t.identifier('r5_1'),
							),
							t.restElement(t.identifier('r8_1')),
						]),
						t.conditionalExpression(
							t.binaryExpression(
								'!==',
								t.cloneNode(raw),
								t.identifier('undefined'),
							),
							t.cloneNode(raw),
							t.objectExpression([]),
						),
					),
				]),
				t.expressionStatement(t.yieldExpression(
					t.identifier('undefined'),
				)),
				t.returnStatement(t.arrayExpression([
					t.identifier('r5_1'),
					t.identifier('r8_1'),
				])),
			]),
			true,
		);

		assert.equal(hoistPrimedGeneratorArgumentsParams(func), true);
		hoistPrimedGeneratorObjectParams(func);
		hoistDestructuredFunctionParams(func);
		assert.equal(
			generate(func).code,
			'function* (_param_49398_0_, {\n' +
				'  forceExternalBrowser: r5_1,\n' +
				'  ...r8_1\n' +
				'} = {}) {\n' +
				'  yield undefined;\n' +
				'  return [r5_1, r8_1];\n' +
				'}',
		);
	},
);

Deno.test(
	'primed generator object promotion refuses residual parameter uses',
	() => {
		const source = t.identifier('_param_1_0_');
		const func = t.functionExpression(
			null,
			[t.cloneNode(source)],
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('value'),
						t.memberExpression(
							t.cloneNode(source),
							t.identifier('value'),
						),
					),
				]),
				t.expressionStatement(t.yieldExpression(
					t.identifier('undefined'),
				)),
				t.returnStatement(t.cloneNode(source)),
			]),
			true,
		);

		assert.equal(hoistPrimedGeneratorObjectParams(func), false);
		assert.ok(t.isIdentifier(func.params[0], { name: source.name }));
	},
);

Deno.test(
	'generator wrapper merge preserves recovered body bindings',
	() => {
		const merged = mergeRecoveredGeneratorWrapperParams(
			[
				t.arrayPattern([t.identifier('r2_4')]),
				t.identifier('r3_4'),
				t.restElement(t.identifier('r4_4')),
				t.identifier('_param_11_3_'),
			],
			[
				t.identifier('_param_9_0_'),
				t.assignmentPattern(
					t.identifier('_param_9_1_'),
					t.callExpression(t.identifier('value'), []),
				),
				t.restElement(t.identifier('_rest_9_')),
				t.identifier('_param_9_3_'),
			],
		);

		assert.equal(
			merged.map((param) => generate(param).code).join(', '),
			'[r2_4], r3_4 = value(), ...r4_4, _param_11_3_',
		);
	},
);

Deno.test(
	'generator wrapper merge adopts plain wrapper parameter names',
	() => {
		const merged = mergeRecoveredGeneratorWrapperParams(
			[
				t.identifier('_param_26_0_'),
				t.identifier('_param_26_1_'),
			],
			[
				t.identifier('_param_3_0_'),
				t.identifier('_param_3_1_'),
			],
			t.functionExpression(
				null,
				[
					t.identifier('_param_26_0_'),
					t.identifier('_param_26_1_'),
				],
				t.blockStatement([
					t.expressionStatement(t.identifier('_param_3_0_')),
					t.expressionStatement(t.identifier('_param_3_1_')),
				]),
				true,
			),
		);
		assert.equal(
			merged.map((param) => generate(param).code).join(', '),
			'_param_3_0_, _param_3_1_',
		);
	},
);

Deno.test(
	'generator wrapper merge retains a recovered default',
	() => {
		const merged = mergeRecoveredGeneratorWrapperParams(
			[
				t.assignmentPattern(
					t.objectPattern([
						t.objectProperty(
							t.identifier('x'),
							t.identifier('r2_4'),
						),
					]),
					t.objectExpression([]),
				),
			],
			[
				t.assignmentPattern(
					t.identifier('_param_9_0_'),
					t.identifier('fallback'),
				),
			],
		);

		assert.equal(generate(merged[0]).code, '{\n  x: r2_4\n} = {}');
	},
);

Deno.test(
	'primed iterator destructuring adopts the wrapper parameter',
	() => {
		const source = t.identifier('_param_7_0_');
		const target = t.identifier('r11_r10_1_0');
		const iterator = t.identifier('r11_1');
		const state = t.identifier('r7_8');
		const value = t.identifier('r9_3');
		const done = t.identifier('r7_10');
		const func = t.functionExpression(
			null,
			[
				t.assignmentPattern(
					t.cloneNode(source),
					t.callExpression(t.identifier('fallback'), []),
				),
			],
			t.blockStatement([
				t.variableDeclaration('let', [
					t.variableDeclarator(
						t.cloneNode(target),
						t.identifier('undefined'),
					),
				]),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.arrayPattern([
							t.cloneNode(iterator),
							t.cloneNode(state),
						]),
						t.callExpression(
							t.v8IntrinsicIdentifier('IteratorBegin'),
							[t.cloneNode(source)],
						),
					),
				]),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.arrayPattern([
							t.cloneNode(value),
							t.cloneNode(done),
						]),
						t.callExpression(
							t.v8IntrinsicIdentifier('IteratorNext'),
							[t.cloneNode(iterator), t.cloneNode(state)],
						),
					),
				]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.cloneNode(target),
					t.cloneNode(value),
				)),
				t.ifStatement(
					t.binaryExpression(
						'!==',
						t.cloneNode(done),
						t.identifier('undefined'),
					),
					t.blockStatement([
						t.expressionStatement(t.callExpression(
							t.v8IntrinsicIdentifier('IteratorClose'),
							[t.cloneNode(done), t.booleanLiteral(false)],
						)),
					]),
				),
				t.expressionStatement(t.yieldExpression(
					t.identifier('undefined'),
				)),
				t.returnStatement(t.cloneNode(target)),
			]),
			true,
		);

		hoistInitialIteratorDestructuredFunctionParams(func);

		assert.equal(
			generate(func).code,
			'function* ([r11_r10_1_0] = fallback()) {\n' +
				'  yield undefined;\n' +
				'  return r11_r10_1_0;\n' +
				'}',
		);
	},
);

Deno.test(
	'duplicate SSA declaration reuses destructured function parameter',
	() => {
		const func = t.functionExpression(
			null,
			[t.arrayPattern([t.identifier('r2_5')])],
			t.blockStatement([
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier('r2_5')),
				]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.identifier('r2_5'),
					t.numericLiteral(1),
				)),
				t.returnStatement(t.identifier('r2_5')),
			]),
		);
		const wrapped = t.file(t.program([
			t.expressionStatement(func),
		]));

		normalizeDuplicateRegisterDeclarations(wrapped);

		traverse(wrapped, {});
		assert.equal(
			generate(wrapped).code,
			'(function ([r2_5]) {\n  r2_5 = 1;\n  return r2_5;\n});',
		);
	},
);

Deno.test(
	'duplicate SSA binding in declaration pattern reuses function parameter',
	() => {
		const func = t.functionExpression(
			null,
			[t.arrayPattern([t.identifier('r2_6')])],
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.arrayPattern([
							t.identifier('r1_1'),
							t.identifier('r2_6'),
						]),
						t.identifier('source'),
					),
				]),
				t.returnStatement(t.identifier('r2_6')),
			]),
		);
		const wrapped = t.file(t.program([
			t.expressionStatement(func),
		]));

		normalizeDuplicateRegisterDeclarations(wrapped);

		traverse(wrapped, {});
		assert.equal(
			generate(wrapped).code,
			'(function ([r2_6]) {\n  let r1_1;\n  [r1_1, r2_6] = source;\n  return r2_6;\n});',
		);
	},
);

Deno.test(
	'duplicate SSA bindings in a multi-declaration reuse function parameters',
	() => {
		const func = t.functionExpression(
			null,
			[
				t.arrayPattern([t.identifier('r2_6')]),
				t.arrayPattern([t.identifier('r3_4')]),
			],
			t.blockStatement([
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier('r2_6')),
					t.variableDeclarator(t.identifier('r3_4')),
				]),
				t.returnStatement(t.binaryExpression(
					'+',
					t.identifier('r2_6'),
					t.identifier('r3_4'),
				)),
			]),
		);
		const wrapped = t.file(t.program([
			t.expressionStatement(func),
		]));

		normalizeDuplicateRegisterDeclarations(wrapped);

		traverse(wrapped, {});
		assert.equal(
			generate(wrapped).code,
			'(function ([r2_6], [r3_4]) {\n  return r2_6 + r3_4;\n});',
		);
	},
);

function standaloneTestFunction(id: number): Function {
	const block: BasicBlock = {
		address: 0,
		instructions: [
			{
				instruction: 'LoadConst',
				functionLocalOffset: 0,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(0),
				value: id,
			},
			{
				instruction: 'Ret',
				functionLocalOffset: 1,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				argument: asRegister(0),
			},
		],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		id,
		offset: id * 2,
		name: `function_${id}`,
		paramCount: 1,
		frameSize: 1,
		envSize: id,
		loopDepth: 0,
		numberRegCount: 0,
		nonPtrRegCount: 0,
		highestReadCacheIndex: 0,
		highestWriteCacheIndex: 0,
		readCacheSize: 0,
		writeCacheSize: 0,
		privateNameCacheSize: 0,
		strict: false,
		prohibitInvoke: 2,
		functionKind: FunctionKind.NormalFunction,
		exceptionHandlers: [],
		basicBlocks: new Map([[0, block]]),
		trampolines: new Map(),
	};
}

function nestedTestFunction(
	id: number,
	childId?: number,
): Function {
	const instructions = childId == null
		? [
			{
				instruction: 'LoadConst' as const,
				functionLocalOffset: 0,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(0),
				value: id,
			},
		]
		: [
			{
				instruction: 'LoadConst' as const,
				functionLocalOffset: 0,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(0),
				value: undefined,
			},
			{
				instruction: 'CreateClosure' as const,
				functionLocalOffset: 1,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(1),
				environment: asRegister(0),
				function: asFunctionRef(childId),
			},
		];
	const result = childId == null ? asRegister(0) : asRegister(1);
	const block: BasicBlock = {
		address: 0,
		instructions: [
			...instructions,
			{
				instruction: 'Ret',
				functionLocalOffset: instructions.length,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				argument: result,
			},
		],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		...standaloneTestFunction(id),
		frameSize: 2,
		basicBlocks: new Map([[0, block]]),
	};
}

function environmentCaptureChildTestFunction(
	id: number,
	slotIndex: number,
	levelIndex = 0,
) {
	const block: BasicBlock = {
		address: 0,
		instructions: [{
			instruction: 'GetParentEnvironment',
			functionLocalOffset: 0,
			length: InstructionLength.NORMAL,
			type: InstructionType.NORMAL,
			strict: InstructionStrictness.NORMAL,
			destination: asRegister(0),
			levelIndex,
		}, {
			instruction: 'LoadFromEnvironment',
			functionLocalOffset: 1,
			length: InstructionLength.NORMAL,
			type: InstructionType.NORMAL,
			strict: InstructionStrictness.NORMAL,
			destination: asRegister(1),
			environment: asRegister(0),
			slotIndex,
		}, {
			instruction: 'Ret',
			functionLocalOffset: 2,
			length: InstructionLength.NORMAL,
			type: InstructionType.NORMAL,
			strict: InstructionStrictness.NORMAL,
			argument: asRegister(1),
		}],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		...standaloneTestFunction(id),
		frameSize: 2,
		envSize: 0,
		basicBlocks: new Map([[0, block]]),
	};
}

function environmentCreatingClosureTestFunction(
	id: number,
	childId: number,
): Function {
	const block: BasicBlock = {
		address: 0,
		instructions: [{
			instruction: 'CreateFunctionEnvironment',
			functionLocalOffset: 0,
			length: InstructionLength.NORMAL,
			type: InstructionType.NORMAL,
			strict: InstructionStrictness.NORMAL,
			destination: asRegister(0),
			envSize: 0,
		}, {
			instruction: 'CreateClosure',
			functionLocalOffset: 1,
			length: InstructionLength.NORMAL,
			type: InstructionType.NORMAL,
			strict: InstructionStrictness.NORMAL,
			destination: asRegister(1),
			environment: asRegister(0),
			function: asFunctionRef(childId),
		}, {
			instruction: 'Ret',
			functionLocalOffset: 2,
			length: InstructionLength.NORMAL,
			type: InstructionType.NORMAL,
			strict: InstructionStrictness.NORMAL,
			argument: asRegister(1),
		}],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		...standaloneTestFunction(id),
		frameSize: 2,
		envSize: 0,
		basicBlocks: new Map([[0, block]]),
	};
}

function environmentCreatingClosureWithValueTestFunction(
	id: number,
	childId: number,
	value: number,
	generatorClosure = false,
): Function {
	const metadata = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const block: BasicBlock = {
		address: 0,
		instructions: [{
			instruction: 'CreateFunctionEnvironment',
			...metadata(0),
			destination: asRegister(0),
			envSize: 1,
		}, {
			instruction: 'LoadConst',
			...metadata(1),
			destination: asRegister(1),
			value,
		}, {
			instruction: 'StoreToEnvironment',
			...metadata(2),
			environment: asRegister(0),
			slotIndex: 0,
			value: asRegister(1),
		}, {
			instruction: generatorClosure
				? 'CreateGeneratorClosure'
				: 'CreateClosure',
			...metadata(3),
			destination: asRegister(2),
			environment: asRegister(0),
			function: asFunctionRef(childId),
		}, {
			instruction: 'Ret',
			...metadata(4),
			argument: asRegister(2),
		}],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		...standaloneTestFunction(id),
		frameSize: 3,
		envSize: 1,
		basicBlocks: new Map([[0, block]]),
	};
}

function repeatedEnvironmentClosureRootTestFunction(): Function {
	const metadata = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const block: BasicBlock = {
		address: 0,
		instructions: [{
			instruction: 'CreateFunctionEnvironment',
			...metadata(0),
			destination: asRegister(0),
			envSize: 1,
		}, {
			instruction: 'LoadConst',
			...metadata(1),
			destination: asRegister(1),
			value: 101,
		}, {
			instruction: 'StoreToEnvironment',
			...metadata(2),
			environment: asRegister(0),
			slotIndex: 0,
			value: asRegister(1),
		}, {
			instruction: 'CreateClosure',
			...metadata(3),
			destination: asRegister(2),
			environment: asRegister(0),
			function: asFunctionRef(1),
		}, {
			instruction: 'CreateClosure',
			...metadata(4),
			destination: asRegister(3),
			environment: asRegister(0),
			function: asFunctionRef(1),
		}, {
			instruction: 'Call',
			...metadata(5),
			destination: asRegister(4),
			closure: asRegister(2),
			arguments: [asRegister(2)],
		}, {
			instruction: 'Ret',
			...metadata(6),
			argument: asRegister(3),
		}],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		...standaloneTestFunction(0),
		frameSize: 5,
		envSize: 0,
		basicBlocks: new Map([[0, block]]),
	};
}

function mixedEnvironmentCreationTestFunction(): Function {
	const metadata = (
		functionLocalOffset: number,
	) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const block: BasicBlock = {
		address: 0,
		instructions: [{
			instruction: 'CreateFunctionEnvironment',
			...metadata(0),
			destination: asRegister(0),
			envSize: 1,
		}, {
			instruction: 'LoadConst',
			...metadata(1),
			destination: asRegister(1),
			value: 101,
		}, {
			instruction: 'StoreToEnvironment',
			...metadata(2),
			environment: asRegister(0),
			slotIndex: 0,
			value: asRegister(1),
		}, {
			instruction: 'CreateTopLevelEnvironment',
			...metadata(3),
			destination: asRegister(2),
			envSize: 2,
		}, {
			instruction: 'CreateClosure',
			...metadata(4),
			destination: asRegister(3),
			environment: asRegister(0),
			function: asFunctionRef(1),
		}, {
			instruction: 'StoreToEnvironment',
			...metadata(5),
			environment: asRegister(2),
			slotIndex: 0,
			value: asRegister(3),
		}, {
			instruction: 'LoadConst',
			...metadata(6),
			destination: asRegister(4),
			value: 202,
		}, {
			instruction: 'StoreToEnvironment',
			...metadata(7),
			environment: asRegister(2),
			slotIndex: 1,
			value: asRegister(4),
		}, {
			instruction: 'CreateClosure',
			...metadata(8),
			destination: asRegister(5),
			environment: asRegister(2),
			function: asFunctionRef(2),
		}, {
			instruction: 'Ret',
			...metadata(9),
			argument: asRegister(5),
		}],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		...standaloneTestFunction(0),
		frameSize: 6,
		envSize: 0,
		basicBlocks: new Map([[0, block]]),
	};
}

function generatorObjectTestFunction(
	id: number,
	childId: number,
): Function {
	const block: BasicBlock = {
		address: 0,
		instructions: [
			{
				instruction: 'LoadConst',
				functionLocalOffset: 0,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(0),
				value: undefined,
			},
			{
				instruction: 'CreateGenerator',
				functionLocalOffset: 1,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(1),
				environment: asRegister(0),
				function: asFunctionRef(childId),
			},
			{
				instruction: 'Ret',
				functionLocalOffset: 2,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				argument: asRegister(1),
			},
		],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		...standaloneTestFunction(id),
		frameSize: 2,
		basicBlocks: new Map([[0, block]]),
	};
}

function parentEnvironmentGeneratorObjectTestFunction(
	id: number,
	childId: number,
) {
	const wrapper = generatorObjectTestFunction(id, childId);
	wrapper.basicBlocks.get(0)!.instructions[0] = {
		instruction: 'GetParentEnvironment',
		functionLocalOffset: 0,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
		destination: asRegister(0),
		levelIndex: 0,
	};
	return wrapper;
}

function localEnvironmentGeneratorObjectTestFunction(
	id: number,
	childId: number,
) {
	const wrapper = generatorObjectTestFunction(id, childId);
	wrapper.basicBlocks.get(0)!.instructions[0] = {
		instruction: 'CreateFunctionEnvironment',
		functionLocalOffset: 0,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
		destination: asRegister(0),
		envSize: 0,
	};
	return wrapper;
}

function generatorClosureTestFunction(
	id: number,
	childId: number,
): Function {
	const block: BasicBlock = {
		address: 0,
		instructions: [
			{
				instruction: 'LoadConst',
				functionLocalOffset: 0,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(0),
				value: undefined,
			},
			{
				instruction: 'CreateGeneratorClosure',
				functionLocalOffset: 1,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(1),
				environment: asRegister(0),
				function: asFunctionRef(childId),
			},
			{
				instruction: 'Ret',
				functionLocalOffset: 2,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				argument: asRegister(1),
			},
		],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		...standaloneTestFunction(id),
		frameSize: 2,
		basicBlocks: new Map([[0, block]]),
	};
}

function primedGeneratorObjectTestFunction(
	id: number,
	childId: number,
): Function {
	const block: BasicBlock = {
		address: 0,
		instructions: [
			{
				instruction: 'LoadConst',
				functionLocalOffset: 0,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(0),
				value: undefined,
			},
			{
				instruction: 'CreateGenerator',
				functionLocalOffset: 1,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(1),
				environment: asRegister(0),
				function: asFunctionRef(childId),
			},
			{
				instruction: 'GetById',
				functionLocalOffset: 2,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(2),
				object: asRegister(1),
				cacheIndex: 0,
				property: asStringRef(0),
			},
			{
				instruction: 'Call',
				functionLocalOffset: 3,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				destination: asRegister(2),
				closure: asRegister(2),
				arguments: [asRegister(1)],
			},
			{
				instruction: 'Ret',
				functionLocalOffset: 4,
				length: InstructionLength.NORMAL,
				type: InstructionType.NORMAL,
				strict: InstructionStrictness.NORMAL,
				argument: asRegister(1),
			},
		],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		...standaloneTestFunction(id),
		frameSize: 3,
		basicBlocks: new Map([[0, block]]),
	};
}

function nativeGeneratorBodyTestFunction(id: number): Function {
	const metadata = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	return {
		...standaloneTestFunction(id),
		frameSize: 3,
		basicBlocks: new Map([
			[0, {
				address: 0,
				instructions: [{
					instruction: 'StartGenerator',
					...metadata(0),
				}],
				consequentAddresses: [1],
				predicate: null,
			}],
			[1, {
				address: 1,
				instructions: [{
					instruction: 'ResumeGenerator',
					...metadata(1),
					destination: asRegister(0),
					isReturn: asRegister(1),
				}, {
					instruction: 'LoadConst',
					...metadata(2),
					destination: asRegister(2),
					value: undefined,
				}, {
					instruction: 'JmpTrue',
					...metadata(3),
					predicate: asRegister(1),
					relativeTarget: 17,
				}],
				consequentAddresses: [10, 20],
				predicate: null,
			}],
			[10, {
				address: 10,
				instructions: [{
					instruction: 'CompleteGenerator',
					...metadata(10),
				}, {
					instruction: 'Ret',
					...metadata(11),
					argument: asRegister(0),
				}],
				consequentAddresses: [],
				predicate: null,
			}],
			[20, {
				address: 20,
				instructions: [{
					instruction: 'LoadConst',
					...metadata(20),
					destination: asRegister(0),
					value: id,
				}],
				consequentAddresses: [22],
				predicate: null,
			}],
			[22, {
				address: 22,
				instructions: [{
					instruction: 'CompleteGenerator',
					...metadata(22),
				}, {
					instruction: 'Ret',
					...metadata(23),
					argument: asRegister(0),
				}],
				consequentAddresses: [],
				predicate: null,
			}],
		]),
	};
}

function environmentReadingNativeGeneratorBodyTestFunction(
	id: number,
	depth: number,
	slot: number,
): Function {
	const func = environmentCaptureChildTestFunction(id, slot, depth);
	func.functionKind = FunctionKind.GeneratorFunction;
	return func;
}

Deno.test('whole-file composition lowers a nested chain bottom-up', () => {
	const file = {
		version: 96,
		loweredGeneratorWrapperSlotAliases: new Map(),
		functions: [
			nestedTestFunction(0, 1),
			nestedTestFunction(1, 2),
			nestedTestFunction(2),
		],
	} as HBCFile;
	const lifted: number[] = [];
	const originalError = console.error;
	console.error = (...args: unknown[]) => {
		const match = /^currently lifting function #(\d+)$/.exec(
			String(args[0]),
		);
		if (match) lifted.push(Number(match[1]));
	};
	try {
		const result = liftFileWithAnalysis(file, {
			retainRecursiveCFGSummaries: false,
		});
		assert.deepEqual(lifted, [0, 1, 2]);
		assert.match(result.code, /function function_1/);
		assert.match(result.code, /function function_2/);
		assert.doesNotMatch(result.code, /%CreateClosure/);
		assert.ok(
			result.code.indexOf('function function_1') <
				result.code.indexOf('function function_2'),
		);
	} finally {
		console.error = originalError;
	}
});

Deno.test('composing from root 0 matches whole-file composition', () => {
	// The whole-file path is `composeRoots` with the one root that is a program
	// rather than a function expression, so the two must agree exactly.
	const build = () =>
		({
			version: 99,
			loweredGeneratorWrapperSlotAliases: new Map(),
			functions: [
				mixedEnvironmentCreationTestFunction(),
				environmentCaptureChildTestFunction(1, 0),
				environmentCaptureChildTestFunction(2, 1),
			],
		}) as HBCFile;

	const whole = liftFileWithAnalysis(build(), {
		retainRecursiveCFGSummaries: false,
	});
	const partial = liftFileWithAnalysis(build(), {
		retainRecursiveCFGSummaries: false,
		composeRoots: [0],
	});

	assert.equal(
		partial.code.replace(
			/^\/\* Function #0 composed with its descendants \*\/\n/,
			'',
		),
		whole.code,
	);
});

Deno.test('composing from a child root inlines its own descendants', () => {
	const file = {
		version: 99,
		loweredGeneratorWrapperSlotAliases: new Map(),
		functions: [
			mixedEnvironmentCreationTestFunction(),
			environmentCaptureChildTestFunction(1, 0),
			environmentCaptureChildTestFunction(2, 1),
		],
	} as HBCFile;

	const result = liftFileWithAnalysis(file, {
		retainRecursiveCFGSummaries: false,
		composeRoots: [1],
	});

	// Only the requested root is emitted, and it is composed rather than
	// printed as raw blocks.
	assert.match(result.code, /Function #1 composed with its descendants/);
	assert.doesNotMatch(result.code, /Function #0 composed/);
	assert.doesNotMatch(result.code, /%expectEnvironment/);
});

Deno.test(
	'distinct local environment creation sites retain their closure captures',
	() => {
		const file = {
			version: 99,
			loweredGeneratorWrapperSlotAliases: new Map(),
			functions: [
				mixedEnvironmentCreationTestFunction(),
				environmentCaptureChildTestFunction(1, 0),
				environmentCaptureChildTestFunction(2, 1),
			],
		} as HBCFile;

		const result = liftFileWithAnalysis(file, {
			retainRecursiveCFGSummaries: false,
		});
		assert.match(result.code, /_env_0_0 = 101/);
		assert.match(result.code, /_env_0_x0_1 = 202/);
		assert.match(
			result.code,
			/function \w+\(\) \{\s+return _env_0_0;/,
		);
		assert.match(
			result.code,
			/function function_2\(\) \{\s+return _env_0_x0_1;/,
		);
		assert.doesNotMatch(
			result.code,
			/_env_0_0 = 202/,
		);
		assert.ok((result.environmentIdentity?.resolvedHandles ?? 0) > 0);
		assert.ok((result.environmentIdentity?.resolvedSlots ?? 0) > 0);
		assert.equal(result.environmentIdentity?.ambiguousHandles, 0);
		assert.equal(result.environmentIdentity?.unresolvedSlots, 0);
	},
);

Deno.test(
	'multiply created closure clones retain their creation-site parent chain',
	() => {
		const file = {
			version: 99,
			loweredGeneratorWrapperSlotAliases: new Map(),
			functions: [
				repeatedEnvironmentClosureRootTestFunction(),
				environmentCreatingClosureTestFunction(1, 2),
				environmentCaptureChildTestFunction(2, 0, 1),
			],
		} as HBCFile;

		const result = liftFileWithAnalysis(file, {
			retainRecursiveCFGSummaries: false,
		});
		assert.equal(
			result.code.match(/return _env_0_0;/g)?.length,
			2,
		);
		assert.doesNotMatch(result.code, /%expectEnvironment/);
		assert.doesNotMatch(result.code, /%GetParentEnvironment/);
	},
);

Deno.test(
	'native generator composition preserves its elided wrapper environment',
	() => {
		const file = {
			version: 96,
			loweredGeneratorWrapperSlotAliases: new Map(),
			functions: [
				environmentCreatingClosureWithValueTestFunction(0, 1, 100),
				environmentCreatingClosureWithValueTestFunction(1, 2, 200),
				environmentCreatingClosureWithValueTestFunction(
					2,
					3,
					300,
					true,
				),
				localEnvironmentGeneratorObjectTestFunction(3, 4),
				environmentReadingNativeGeneratorBodyTestFunction(4, 2, 0),
			],
		} as HBCFile;

		const result = liftFileWithAnalysis(file, {
			retainRecursiveCFGSummaries: false,
		});
		assert.match(result.code, /return _env_1_0;/);
		assert.doesNotMatch(
			result.code,
			/function\* function_3[^]*return _env_0_0;/,
		);
		assert.doesNotMatch(result.code, /%GetParentEnvironment/);
		assert.doesNotMatch(result.code, /%expectEnvironment/);
	},
);

Deno.test(
	'cloned generator wrappers preserve their elided environment depth',
	() => {
		const creator = environmentCreatingClosureWithValueTestFunction(
			2,
			3,
			300,
			true,
		);
		creator.frameSize = 5;
		creator.basicBlocks.get(0)!.instructions.splice(4, 0, {
			instruction: 'CreateGeneratorClosure',
			functionLocalOffset: 4,
			length: InstructionLength.NORMAL,
			type: InstructionType.NORMAL,
			strict: InstructionStrictness.NORMAL,
			destination: asRegister(3),
			environment: asRegister(0),
			function: asFunctionRef(3),
		}, {
			instruction: 'Call',
			functionLocalOffset: 5,
			length: InstructionLength.NORMAL,
			type: InstructionType.NORMAL,
			strict: InstructionStrictness.NORMAL,
			destination: asRegister(4),
			closure: asRegister(3),
			arguments: [asRegister(3)],
		});
		const file = {
			version: 96,
			loweredGeneratorWrapperSlotAliases: new Map(),
			functions: [
				environmentCreatingClosureWithValueTestFunction(0, 1, 100),
				environmentCreatingClosureWithValueTestFunction(1, 2, 200),
				creator,
				localEnvironmentGeneratorObjectTestFunction(3, 4),
				environmentReadingNativeGeneratorBodyTestFunction(4, 2, 0),
			],
		} as HBCFile;

		const result = liftFileWithAnalysis(file, {
			retainRecursiveCFGSummaries: false,
		});
		assert.equal(
			result.code.match(/return _env_1_0;/g)?.length,
			2,
		);
		assert.doesNotMatch(result.code, /%GetParentEnvironment/);
		assert.doesNotMatch(result.code, /%expectEnvironment/);
	},
);

Deno.test('bottom-up composition visits nested CreateGenerator calls', () => {
	const file = {
		version: 96,
		loweredGeneratorWrapperSlotAliases: new Map(),
		functions: [
			nestedTestFunction(0, 1),
			generatorObjectTestFunction(1, 2),
			standaloneTestFunction(2),
		],
	} as HBCFile;

	const result = liftFileWithAnalysis(file, {
		retainRecursiveCFGSummaries: false,
	});
	assert.doesNotMatch(result.code, /%CreateGenerator/);
	assert.doesNotMatch(result.code, /%getFunctionById/);
	assert.match(result.code, /function function_2/);
});

Deno.test('bottom-up composition revisits generator-wrapper fallbacks', () => {
	const file = {
		version: 96,
		loweredGeneratorWrapperSlotAliases: new Map(),
		getIdentifier: () => 'next',
		functions: [
			nestedTestFunction(0, 1),
			generatorClosureTestFunction(1, 2),
			primedGeneratorObjectTestFunction(2, 3),
			standaloneTestFunction(3),
		],
	} as unknown as HBCFile;

	const result = liftFileWithAnalysis(file, {
		retainRecursiveCFGSummaries: false,
	});
	assert.doesNotMatch(result.code, /%CreateGenerator/);
	assert.doesNotMatch(result.code, /%getFunctionById/);
	assert.match(result.code, /function function_3/);
});

Deno.test('bottom-up composition clones multiply created generator wrappers', () => {
	const root = generatorClosureTestFunction(0, 1);
	root.frameSize = 3;
	root.basicBlocks.get(0)!.instructions.splice(2, 0, {
		instruction: 'CreateGeneratorClosure',
		functionLocalOffset: 2,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
		destination: asRegister(2),
		environment: asRegister(0),
		function: asFunctionRef(1),
	});
	const file = {
		version: 96,
		loweredGeneratorWrapperSlotAliases: new Map(),
		getIdentifier: () => 'next',
		functions: [
			root,
			parentEnvironmentGeneratorObjectTestFunction(1, 2),
			standaloneTestFunction(2),
		],
	} as unknown as HBCFile;

	const result = liftFileWithAnalysis(file, {
		retainRecursiveCFGSummaries: false,
	});
	assert.doesNotMatch(result.code, /%CreateGeneratorClosure/);
	assert.doesNotMatch(result.code, /%CreateGenerator/);
	assert.doesNotMatch(result.code, /%getFunctionById/);
	assert.match(result.code, /function function_1/);
});

Deno.test('bottom-up composition relifts repeated ordinary generator wrappers', () => {
	const file = {
		version: 96,
		loweredGeneratorWrapperSlotAliases: new Map(),
		getIdentifier: () => 'next',
		functions: [
			repeatedEnvironmentClosureRootTestFunction(),
			primedGeneratorObjectTestFunction(1, 2),
			nativeGeneratorBodyTestFunction(2),
		],
	} as unknown as HBCFile;

	const result = liftFileWithAnalysis(file, {
		retainRecursiveCFGSummaries: false,
	});
	assert.doesNotMatch(result.code, /%CreateClosure/);
	assert.doesNotMatch(result.code, /%CreateGenerator/);
	assert.doesNotMatch(result.code, /%getFunctionById/);
	assert.equal(result.code.match(/function\*/g)?.length, 2);
	assert.doesNotMatch(result.code, /yield undefined/);
	assert.doesNotMatch(result.code, /\.next\(\)/);
});

Deno.test('bottom-up composition clones a shared generator body', () => {
	const root = generatorClosureTestFunction(0, 1);
	root.frameSize = 3;
	root.basicBlocks.get(0)!.instructions.splice(2, 0, {
		instruction: 'CreateGeneratorClosure',
		functionLocalOffset: 2,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
		destination: asRegister(2),
		environment: asRegister(0),
		function: asFunctionRef(2),
	});
	const file = {
		version: 96,
		loweredGeneratorWrapperSlotAliases: new Map(),
		getIdentifier: () => 'next',
		functions: [
			root,
			parentEnvironmentGeneratorObjectTestFunction(1, 3),
			parentEnvironmentGeneratorObjectTestFunction(2, 3),
			standaloneTestFunction(3),
		],
	} as unknown as HBCFile;

	const result = liftFileWithAnalysis(file, {
		retainRecursiveCFGSummaries: false,
	});
	assert.doesNotMatch(result.code, /%CreateGeneratorClosure/);
	assert.doesNotMatch(result.code, /%CreateGenerator/);
	assert.doesNotMatch(result.code, /%getFunctionById/);
	assert.match(result.code, /function function_[12]/);
});

Deno.test('bottom-up composition clones multiply created generators', () => {
	const root = generatorObjectTestFunction(0, 1);
	root.frameSize = 3;
	root.basicBlocks.get(0)!.instructions.splice(2, 0, {
		instruction: 'CreateGenerator',
		functionLocalOffset: 2,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
		destination: asRegister(2),
		environment: asRegister(0),
		function: asFunctionRef(1),
	});
	const file = {
		version: 96,
		loweredGeneratorWrapperSlotAliases: new Map(),
		functions: [root, standaloneTestFunction(1)],
	} as HBCFile;

	const result = liftFileWithAnalysis(file, {
		retainRecursiveCFGSummaries: false,
	});
	assert.doesNotMatch(result.code, /%CreateGenerator/);
	assert.doesNotMatch(result.code, /%getFunctionById/);
	assert.equal(result.code.match(/function function_1/g)?.length, 2);
});

Deno.test('bottom-up composition caches multiply referenced functions', () => {
	const root = nestedTestFunction(0, 1);
	const block = root.basicBlocks.get(0)!;
	block.instructions.splice(2, 0, {
		instruction: 'CreateClosure',
		functionLocalOffset: 2,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
		destination: asRegister(0),
		environment: asRegister(0),
		function: asFunctionRef(1),
	});
	const file = {
		version: 96,
		functions: [root, nestedTestFunction(1)],
	} as HBCFile;
	const lifted: number[] = [];
	const originalError = console.error;
	console.error = (...args: unknown[]) => {
		const match = /^currently lifting function #(\d+)$/.exec(
			String(args[0]),
		);
		if (match) lifted.push(Number(match[1]));
	};
	try {
		const result = liftFileWithAnalysis(file, {
			retainRecursiveCFGSummaries: false,
		});
		assert.deepEqual(lifted, [0, 1]);
		assert.match(result.code, /function function_1/);
		assert.doesNotMatch(result.code, /%CreateClosure/);
	} finally {
		console.error = originalError;
	}
});

Deno.test('selected and incremental lifting avoid whole-file composition', () => {
	const file = {
		version: 96,
		functions: [
			standaloneTestFunction(0),
			standaloneTestFunction(1),
			standaloneTestFunction(2),
		],
	} as HBCFile;

	const artifacts: Array<{ id: number; code: string; env: number }> = [];
	const summaries = liftFunctionsIncrementally(
		file,
		{ functionIds: [2, 0] },
		(artifact) => {
			artifacts.push({
				id: artifact.summary.functionId,
				code: artifact.code,
				env: artifact.summary.environmentSize,
			});
		},
	);

	assert.deepEqual(
		artifacts.map((artifact) => artifact.id),
		[2, 0],
	);
	assert.deepEqual(
		summaries.map((summary) => summary.functionId),
		[2, 0],
	);
	assert.equal(artifacts[0].env, 2);
	assert.match(artifacts[0].code, /function function_2/);

	const discardedSummaries = liftFunctionsIncrementally(
		file,
		{ functionIds: [1], retainSummaries: false },
		() => {},
	);
	assert.deepEqual(discardedSummaries, []);

	const selected = liftFileWithAnalysis(file, {
		functionIds: [1],
		compose: false,
	});
	assert.match(selected.code, /function function_1/);
	assert.doesNotMatch(selected.code, /function function_0/);
	assert.doesNotMatch(selected.code, /function function_2/);
});

function globalVarTestFunction(): Function {
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const block: BasicBlock = {
		address: 0,
		instructions: [{
			instruction: 'DeclareGlobalVar',
			...meta(0),
			identifier: asStringRef(0),
		}, {
			instruction: 'DeclareGlobalVar',
			...meta(1),
			identifier: asStringRef(1),
		}, {
			instruction: 'GetGlobalObject',
			...meta(2),
			destination: asRegister(0),
		}, {
			instruction: 'LoadConst',
			...meta(3),
			destination: asRegister(1),
			value: 1,
		}, {
			instruction: 'PutById',
			...meta(4),
			object: asRegister(0),
			value: asRegister(1),
			cacheIndex: 0,
			property: asStringRef(0),
		}, {
			instruction: 'LoadConst',
			...meta(5),
			destination: asRegister(2),
			value: 2,
		}, {
			instruction: 'PutById',
			...meta(6),
			object: asRegister(0),
			value: asRegister(2),
			cacheIndex: 1,
			property: asStringRef(1),
		}, {
			instruction: 'GetById',
			...meta(7),
			destination: asRegister(3),
			object: asRegister(0),
			cacheIndex: 2,
			property: asStringRef(1),
		}, {
			instruction: 'Ret',
			...meta(8),
			argument: asRegister(3),
		}],
		consequentAddresses: [],
		predicate: null,
	};
	return {
		...standaloneTestFunction(0),
		frameSize: 4,
		envSize: 0,
		basicBlocks: new Map([[0, block]]),
	};
}

Deno.test('a write-only declared global stays a top-level var', () => {
	// `writeOnly` is assigned through the global object and never read, so the
	// emitter's write-only elimination used to drop its `DeclareGlobalVar`
	// declaration -- and with it the provenance composition needs to unqualify
	// `global.writeOnly = 1` back into the `var writeOnly = 1` of the source.
	const names = ['writeOnly', 'readWrite'];
	const file = {
		version: 96,
		loweredGeneratorWrapperSlotAliases: new Map(),
		getIdentifier: (index: number) => names[index],
		functions: [globalVarTestFunction()],
	} as unknown as HBCFile;

	const result = liftFileWithAnalysis(file, {
		retainRecursiveCFGSummaries: false,
		cfgReducer: { mode: 'recursive', materialize: true },
	});
	assert.match(result.code, /^var writeOnly = 1;$/m);
	assert.match(result.code, /^var readWrite = 2;$/m);
	assert.doesNotMatch(result.code, /global\./);
});

function ssaLiteralSliceRegister(index: number): SSARegister {
	return { ...asRegister(index), version: 0 };
}

Deno.test('large single-use object construction lifts directly into terminal write', () => {
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const root = ssaLiteralSliceRegister(1);
	const param = ssaLiteralSliceRegister(2);
	const rootWriteAlias = ssaLiteralSliceRegister(3);
	const instructions: SSAInstruction[] = [{
		instruction: 'NewObject',
		...meta(0),
		destination: asRegister(1),
		defs: { destination: root },
		uses: {},
	} as SSAInstruction, {
		instruction: 'Mov',
		...meta(1),
		destination: asRegister(3),
		source: asRegister(1),
		defs: { destination: rootWriteAlias },
		uses: { source: root },
	} as SSAInstruction];
	for (let i = 0; i < 130; i++) {
		const value = ssaLiteralSliceRegister(10 + i);
		const stored = i % 17 === 0 ? ssaLiteralSliceRegister(200 + i) : value;
		instructions.push({
			instruction: 'LoadConst',
			...meta(i * 3 + 1),
			destination: asRegister(10 + i),
			value: i,
			defs: { destination: value },
			uses: {},
		} as SSAInstruction);
		if (stored !== value) {
			instructions.push({
				instruction: 'Mov',
				...meta(i * 3 + 2),
				destination: asRegister(stored.index),
				source: asRegister(value.index),
				defs: { destination: stored },
				uses: { source: value },
			} as SSAInstruction);
		}
		instructions.push({
			instruction: 'PutNewOwnById',
			...meta(i * 3 + 3),
			object: asRegister(rootWriteAlias.index),
			value: asRegister(stored.index),
			property: asStringRef(i + 2),
			defs: {},
			uses: { object: rootWriteAlias, value: stored },
		} as SSAInstruction);
	}
	instructions.push({
		instruction: 'LoadParam',
		...meta(270),
		destination: asRegister(2),
		parameterIndex: 5,
		defs: { destination: param },
		uses: {},
	} as SSAInstruction);
	instructions.push({
		instruction: 'PutById',
		...meta(271),
		object: asRegister(2),
		value: asRegister(1),
		cacheIndex: 0,
		property: asStringRef(1),
		defs: {},
		uses: { object: param, value: root },
	} as SSAInstruction);
	const block: SSABasicBlock = {
		address: 0,
		instructions: [],
		ssaInstructions: instructions,
		consequentAddresses: [],
		predicate: null,
	};
	const names = ['exports', 'payload'];
	for (let i = 0; i < 130; i++) names.push(`p${i}`);
	const func = {
		id: 42,
		paramCount: 8,
		objectShapeKeysByRegister: new Map(),
		file: {
			getObjectBufferElements: () => ({ keys: [], values: [] }),
			getArrayBufferElements: () => [],
		},
		fromIdentifierRef: (ref: { stringTableIndex: number }) =>
			t.identifier(names[ref.stringTableIndex]),
		getParam: (index: number) => t.identifier(`param${index}`),
		ssa: {
			_func: {
				basicBlocks: new Map([[
					0,
					{
						instructions,
						consequentAddresses: [],
					},
				]]),
				exceptionHandlers: [],
			},
		},
	} as unknown as IRFunction;

	const ir = liftSSABlocktoIR(func, block);
	const code = generate(t.program(ir.body as t.Statement[])).code;

	assert.equal(ir.body.length, 1);
	assert.match(code, /^param5\.payload = \{/);
	assert.match(code, /p129: 129/);
	assert.doesNotMatch(code, /r1_0|r3_0|r10_0/);
	assert.doesNotMatch(code, /r200_0/);
});

// `new Ctor(arg)` as Hermes emits it: the callee's own `.prototype` feeds
// `CreateThis`, the receiver reaches `Construct` through a call-frame `Mov`,
// and `SelectObject` picks the constructor's return over the receiver.
function constructionIdiomInstructions(
	options: {
		prototypeOwner?: number;
		extraReceiverUse?: boolean;
		// v97+ folds the prototype lookup into the instruction itself.
		createThisForNew?: boolean;
	} = {},
): SSAInstruction[] {
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const constructorRef = ssaLiteralSliceRegister(1);
	const prototype = ssaLiteralSliceRegister(2);
	const receiver = ssaLiteralSliceRegister(3);
	const receiverSlot = ssaLiteralSliceRegister(4);
	const argument = ssaLiteralSliceRegister(5);
	const constructed = ssaLiteralSliceRegister(6);
	const selected = ssaLiteralSliceRegister(7);
	const prototypeOwner = options.prototypeOwner ?? constructorRef.index;
	const receiverSetup: SSAInstruction[] = options.createThisForNew
		? [{
			instruction: 'CreateThisForNew',
			...meta(1),
			destination: asRegister(receiver.index),
			closure: asRegister(constructorRef.index),
			prototypeCacheIndex: 0,
			defs: { destination: receiver },
			uses: { closure: constructorRef },
		} as SSAInstruction]
		: [{
			instruction: 'GetById',
			...meta(0),
			destination: asRegister(prototype.index),
			object: asRegister(prototypeOwner),
			cacheIndex: 0,
			property: asStringRef(0),
			defs: { destination: prototype },
			uses: { object: ssaLiteralSliceRegister(prototypeOwner) },
		} as SSAInstruction, {
			instruction: 'CreateThis',
			...meta(1),
			destination: asRegister(receiver.index),
			prototype: asRegister(prototype.index),
			constructorRef: asRegister(constructorRef.index),
			defs: { destination: receiver },
			uses: { prototype, constructorRef },
		} as SSAInstruction];
	const instructions: SSAInstruction[] = [...receiverSetup, {
		instruction: 'Mov',
		...meta(2),
		destination: asRegister(receiverSlot.index),
		source: asRegister(receiver.index),
		defs: { destination: receiverSlot },
		uses: { source: receiver },
	} as SSAInstruction, {
		instruction: 'LoadConst',
		...meta(3),
		destination: asRegister(argument.index),
		value: 42,
		defs: { destination: argument },
		uses: {},
	} as SSAInstruction, {
		instruction: 'Construct',
		...meta(4),
		destination: asRegister(constructed.index),
		closure: asRegister(constructorRef.index),
		argumentCount: 2,
		arguments: [asRegister(receiverSlot.index), asRegister(argument.index)],
		defs: { destination: constructed },
		uses: {
			closure: constructorRef,
			arguments: [receiverSlot, argument],
		},
	} as SSAInstruction, {
		instruction: 'SelectObject',
		...meta(5),
		destination: asRegister(selected.index),
		thisObject: asRegister(receiver.index),
		constructorReturnValue: asRegister(constructed.index),
		defs: { destination: selected },
		uses: { thisObject: receiver, constructorReturnValue: constructed },
	} as SSAInstruction];
	if (options.extraReceiverUse) {
		instructions.push({
			instruction: 'PutById',
			...meta(6),
			object: asRegister(selected.index),
			value: asRegister(receiver.index),
			cacheIndex: 0,
			property: asStringRef(1),
			defs: {},
			uses: { object: selected, value: receiver },
		} as SSAInstruction);
	}
	return instructions;
}

function liftInstructions(
	instructions: SSAInstruction[],
): string {
	const block: SSABasicBlock = {
		address: 0,
		instructions: [],
		ssaInstructions: instructions,
		consequentAddresses: [],
		predicate: null,
	};
	const names = ['prototype', 'self', 'count'];
	const func = {
		id: 7,
		paramCount: 1,
		objectShapeKeysByRegister: new Map(),
		file: {
			getIdentifier: (index: number) => names[index],
			getObjectBufferElements: () => ({ keys: [], values: [] }),
			getArrayBufferElements: () => [],
		},
		fromIdentifierRef: (ref: { stringTableIndex: number }) =>
			t.identifier(names[ref.stringTableIndex]),
		getParam: (index: number) => t.identifier(`param${index}`),
		ssa: {
			basicBlocks: new Map([[0, block]]),
			exceptionHandlers: [],
			_func: {
				basicBlocks: new Map([[
					0,
					{ instructions, consequentAddresses: [] },
				]]),
				exceptionHandlers: [],
			},
		},
	} as unknown as IRFunction;

	return generate(
		t.program(liftSSABlocktoIR(func, block).body as t.Statement[]),
	).code;
}

Deno.test('a consecutive construction idiom lifts straight to a new expression', () => {
	const code = liftInstructions(constructionIdiomInstructions());
	assert.match(code, /^const r7_0 = new r1_0\(r5_0\);$/m);
	assert.doesNotMatch(code, /%CreateThis|%Construct|%SelectObject/);
	// The `.prototype` read only existed to feed `CreateThis`.
	assert.doesNotMatch(code, /\.prototype/);
});

Deno.test('a v97+ construction idiom lifts straight to a new expression', () => {
	const code = liftInstructions(
		constructionIdiomInstructions({ createThisForNew: true }),
	);
	assert.match(code, /^const r7_0 = new r1_0\(r5_0\);$/m);
	assert.doesNotMatch(code, /%CreateThisForNew|%Construct|%SelectObject/);
});

Deno.test('a construction idiom with a foreign prototype keeps its intrinsics', () => {
	// `new.target` differs from the callee -- `Reflect.construct` and derived
	// constructors -- so the receiver is not an instance of the callee and
	// `new callee(…)` would be wrong.
	const code = liftInstructions(
		constructionIdiomInstructions({ prototypeOwner: 9 }),
	);
	assert.match(code, /%CreateThis\(r2_0, r1_0\)/);
	assert.match(code, /%SelectObject\(r3_0, r6_0\)/);
	assert.doesNotMatch(code, /new /);
});

Deno.test('a construction idiom with a surviving receiver read keeps its intrinsics', () => {
	// Folding would delete the `CreateThis` definition the later read needs.
	const code = liftInstructions(
		constructionIdiomInstructions({ extraReceiverUse: true }),
	);
	assert.match(code, /%CreateThis\(r2_0, r1_0\)/);
	assert.match(code, /r7_0\.self = r3_0/);
	assert.doesNotMatch(code, /new /);
});

// `x++` / `++x` as Hermes emits it (`genUpdateExpr`): read the l-reference,
// coerce the old value when the expression yields it and the operand is not
// statically numeric, add or subtract one, write the result straight back.
function updateIdiomInstructions(
	options: {
		operator?: 'Inc' | 'Dec';
		storage?: 'environment' | 'property' | 'computed' | 'global';
		/** Emit the postfix coercion of the old value. */
		coerce?: boolean;
		/** Insert an allocator copy between the coercion and update. */
		copyCoercion?: boolean;
		/** Consume the old value, as a postfix expression does. */
		readOld?: boolean;
		/** Consume the new value, as a prefix expression does. */
		readNew?: boolean;
		/** Write back to a slot other than the one that was read. */
		storeSlot?: number;
	} = {},
): SSAInstruction[] {
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const holder = ssaLiteralSliceRegister(1);
	const old = ssaLiteralSliceRegister(2);
	const value = ssaLiteralSliceRegister(3);
	const next = ssaLiteralSliceRegister(4);
	const keyRegister = ssaLiteralSliceRegister(5);
	const coercedCopy = ssaLiteralSliceRegister(6);
	const operator = options.operator ?? 'Inc';
	const storage = options.storage ?? 'environment';
	const privateCoercedCopy = ssaLiteralSliceRegister(7);
	const instructions: SSAInstruction[] = [];
	if (storage === 'global') {
		instructions.push({
			instruction: 'GetGlobalObject',
			...meta(0),
			destination: asRegister(holder.index),
			defs: { destination: holder },
			uses: {},
		} as SSAInstruction);
	}
	if (storage === 'computed') {
		instructions.push({
			instruction: 'GetByVal',
			...meta(1),
			destination: asRegister(old.index),
			object: asRegister(holder.index),
			property: asRegister(keyRegister.index),
			defs: { destination: old },
			uses: { object: holder, property: keyRegister },
		} as SSAInstruction);
	} else if (storage === 'environment') {
		instructions.push({
			instruction: 'LoadFromEnvironment',
			...meta(1),
			destination: asRegister(old.index),
			environment: asRegister(holder.index),
			slotIndex: 3,
			defs: { destination: old },
			uses: { environment: holder },
		} as SSAInstruction);
	} else {
		instructions.push({
			instruction: storage === 'global' ? 'TryGetById' : 'GetById',
			...meta(1),
			destination: asRegister(old.index),
			object: asRegister(holder.index),
			cacheIndex: 0,
			property: asStringRef(2),
			defs: { destination: old },
			uses: { object: holder },
		} as SSAInstruction);
	}
	// Without a coercion the update reads the loaded value directly.
	const updateArgument = options.copyCoercion ? privateCoercedCopy : (
		options.coerce ? value : old
	);
	if (options.coerce) {
		instructions.push({
			instruction: 'ToNumeric',
			...meta(2),
			destination: asRegister(value.index),
			argument: asRegister(old.index),
			defs: { destination: value },
			uses: { argument: old },
		} as SSAInstruction);
	}
	if (options.copyCoercion) {
		instructions.push({
			instruction: 'Mov',
			...meta(3),
			destination: asRegister(coercedCopy.index),
			source: asRegister(value.index),
			defs: { destination: coercedCopy },
			uses: { source: value },
		} as SSAInstruction);
		instructions.push({
			instruction: 'Mov',
			...meta(3),
			destination: asRegister(privateCoercedCopy.index),
			source: asRegister(coercedCopy.index),
			defs: { destination: privateCoercedCopy },
			uses: { source: coercedCopy },
		} as SSAInstruction);
	}
	instructions.push({
		instruction: operator,
		...meta(3),
		destination: asRegister(next.index),
		argument: asRegister(updateArgument.index),
		defs: { destination: next },
		uses: { argument: updateArgument },
	} as SSAInstruction);
	if (storage === 'global') {
		// Hermes reloads the global object before storing back to it.
		instructions.push({
			instruction: 'GetGlobalObject',
			...meta(4),
			destination: asRegister(keyRegister.index),
			defs: { destination: keyRegister },
			uses: {},
		} as SSAInstruction);
	}
	if (storage === 'computed') {
		instructions.push({
			instruction: 'PutByVal',
			...meta(5),
			object: asRegister(holder.index),
			property: asRegister(keyRegister.index),
			value: asRegister(next.index),
			defs: {},
			uses: { object: holder, property: keyRegister, value: next },
		} as SSAInstruction);
	} else if (storage === 'environment') {
		instructions.push({
			instruction: 'StoreToEnvironment',
			...meta(5),
			environment: asRegister(holder.index),
			slotIndex: options.storeSlot ?? 3,
			value: asRegister(next.index),
			defs: {},
			uses: { environment: holder, value: next },
		} as SSAInstruction);
	} else {
		instructions.push({
			instruction: 'PutById',
			...meta(5),
			object: asRegister(
				storage === 'global' ? keyRegister.index : holder.index,
			),
			value: asRegister(next.index),
			cacheIndex: 0,
			property: asStringRef(2),
			defs: {},
			uses: {
				object: storage === 'global' ? keyRegister : holder,
				value: next,
			},
		} as SSAInstruction);
	}
	if (options.readOld) {
		const result = options.copyCoercion
			? coercedCopy
			: options.coerce
			? value
			: old;
		instructions.push({
			instruction: 'Throw',
			...meta(6),
			exception: asRegister(result.index),
			defs: {},
			uses: { exception: result },
		} as SSAInstruction);
	}
	if (options.readNew) {
		instructions.push({
			instruction: 'Throw',
			...meta(7),
			exception: asRegister(next.index),
			defs: {},
			uses: { exception: next },
		} as SSAInstruction);
	}
	return instructions;
}

Deno.test('an environment slot update lifts to a postfix increment', () => {
	const code = liftInstructions(
		updateIdiomInstructions({ coerce: true, readOld: true }),
	);
	assert.match(code, /^const r3_0 = %expectEnvironment\(r1_0\)\[3\]\+\+;$/m);
	assert.doesNotMatch(code, /%ToNumeric/);
	// The read and the write-back are both subsumed by the update.
	assert.equal(code.split('\n').length, 2);
});

Deno.test('an update whose new value is read lifts to a prefix increment', () => {
	const code = liftInstructions(updateIdiomInstructions({ readNew: true }));
	assert.match(code, /^const r4_0 = \+\+%expectEnvironment\(r1_0\)\[3\];$/m);
});

Deno.test('an unread update lifts to a bare update statement', () => {
	const code = liftInstructions(
		updateIdiomInstructions({ operator: 'Dec', storage: 'property' }),
	);
	assert.equal(code, 'r1_0.count--;');
});

Deno.test('a computed member update lifts to an update on the same key', () => {
	const code = liftInstructions(
		updateIdiomInstructions({ storage: 'computed', readOld: true }),
	);
	assert.match(code, /^const r2_0 = r1_0\[r5_0\]\+\+;$/m);
});

Deno.test('a global update tolerates the reloaded global object', () => {
	// The store reaches the global through a second `GetGlobalObject`, so the
	// receiver registers of the load and the store differ.
	const code = liftInstructions(
		updateIdiomInstructions({ storage: 'global', readOld: true }),
	);
	assert.match(code, /^const r2_0 = r1_0\.count\+\+;$/m);
	assert.doesNotMatch(code, /= r4_0/);
});

Deno.test('an update writing a different slot keeps its instructions', () => {
	const code = liftInstructions(
		updateIdiomInstructions({ coerce: true, readOld: true, storeSlot: 9 }),
	);
	// The increment runs on a copy of what was loaded, not on the slot.
	assert.match(code, /let r4_0 = r2_0;\s*const r3_0 = r4_0\+\+;/);
	assert.match(code, /%expectEnvironment\(r1_0\)\[9\] = r4_0/);
	// The slot that was read is never the one updated in place.
	assert.doesNotMatch(code, /\[3\]\+\+/);
});

Deno.test('an update whose old and new value are both read is declined', () => {
	// Neither `x++` nor `++x` yields both halves, so the arithmetic stays.
	const code = liftInstructions(
		updateIdiomInstructions({ readOld: true, readNew: true }),
	);
	// The increment survives on a copy, not on the l-reference.
	assert.match(code, /let r4_0 = r2_0;\s*r4_0\+\+;/);
	assert.doesNotMatch(code, /\[3\]\+\+/);
});

/**
 * A loop counter the allocator keeps in a register: a header Phi joins the
 * entry value with the latch's `Dec`, and no store instruction exists.
 *
 * Returns the lifted latch block and the Phi, so a caller can check both the
 * emitted update and whether the back edge was retargeted.
 */
function liftLoopCounterLatch(
	options: {
		readAfterUpdate?: boolean;
		consumeOld?: boolean;
		readBeforeUpdate?: boolean;
		/** Schedule a consumer of the coerced value above the `Dec`. */
		gap?: 'reads-coerced' | 'reads-counter';
	} = {},
) {
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const entry = ssaLiteralSliceRegister(1);
	const counter = ssaLiteralSliceRegister(2);
	const coerced = ssaLiteralSliceRegister(3);
	const next = ssaLiteralSliceRegister(4);
	const holder = ssaLiteralSliceRegister(5);
	const arr = ssaLiteralSliceRegister(6);
	const phi = {
		instruction: 'Phi',
		destination: counter,
		sources: new Map([[0, entry], [2, next]]),
	} as unknown as SSAInstruction;
	const header: SSABasicBlock = {
		address: 1,
		instructions: [],
		ssaInstructions: [phi],
		consequentAddresses: [2],
		predicate: null,
	};
	const latch: SSABasicBlock = {
		address: 2,
		instructions: [],
		ssaInstructions: [
			...(options.readBeforeUpdate
				? [{
					instruction: 'Throw',
					...meta(4),
					exception: asRegister(counter.index),
					defs: {},
					uses: { exception: counter },
				} as SSAInstruction]
				: []),
			...(options.consumeOld === false ? [] : [{
				instruction: 'ToNumeric',
				...meta(0),
				destination: asRegister(coerced.index),
				argument: asRegister(counter.index),
				defs: { destination: coerced },
				uses: { argument: counter },
			} as SSAInstruction]),
			// Hermes hoists consumers of the coerced value above the update.
			...(options.gap
				? [{
					instruction: 'GetByVal',
					...meta(5),
					destination: asRegister(holder.index),
					object: asRegister(arr.index),
					property: asRegister(
						options.gap === 'reads-counter'
							? counter.index
							: coerced.index,
					),
					defs: { destination: holder },
					uses: {
						object: arr,
						property: options.gap === 'reads-counter'
							? counter
							: coerced,
					},
				} as SSAInstruction]
				: []),
			{
				instruction: 'Dec',
				...meta(1),
				destination: asRegister(next.index),
				argument: asRegister(
					options.consumeOld === false
						? counter.index
						: coerced.index,
				),
				defs: { destination: next },
				uses: {
					argument: options.consumeOld === false ? counter : coerced,
				},
			} as SSAInstruction,
			// The loop test consumes the pre-update value.
			...(options.consumeOld === false ? [] : [{
				instruction: 'Throw',
				...meta(2),
				exception: asRegister(coerced.index),
				defs: {},
				uses: { exception: coerced },
			} as SSAInstruction]),
			...(options.readAfterUpdate
				? [{
					instruction: 'Throw',
					...meta(3),
					exception: asRegister(counter.index),
					defs: {},
					uses: { exception: counter },
				} as SSAInstruction]
				: []),
		],
		consequentAddresses: [1],
		predicate: null,
	};
	const func = {
		id: 7,
		paramCount: 0,
		objectShapeKeysByRegister: new Map(),
		file: {
			getIdentifier: () => 'count',
			getObjectBufferElements: () => ({ keys: [], values: [] }),
			getArrayBufferElements: () => [],
		},
		fromIdentifierRef: () => t.identifier('count'),
		getParam: (index: number) => t.identifier(`param${index}`),
		ssa: {
			basicBlocks: new Map([[1, header], [2, latch]]),
			exceptionHandlers: [],
			_func: {
				basicBlocks: new Map([
					[1, { instructions: [], consequentAddresses: [2] }],
					[2, { instructions: [], consequentAddresses: [1] }],
				]),
				exceptionHandlers: [],
			},
		},
	} as unknown as IRFunction;
	const code = generate(
		t.program(liftSSABlocktoIR(func, latch).body as t.Statement[]),
	).code;
	return {
		code,
		phi: phi as unknown as { sources: Map<number, SSARegister> },
	};
}

Deno.test('a loop counter with no store lifts to an update on its register', () => {
	const { code, phi } = liftLoopCounterLatch();
	assert.match(code, /^const r3_0 = r2_0--;$/m);
	assert.doesNotMatch(code, /%ToNumeric/);
	// The update wrote the Phi's destination in place, so the back edge must
	// stop copying a register the update no longer produces.
	assert.equal(phi.sources.get(2)?.index, 2);
});

Deno.test('a loop counter read after its update keeps its instructions', () => {
	// The trailing read names the pre-update value, which an in-place update
	// has already destroyed.
	const { code, phi } = liftLoopCounterLatch({ readAfterUpdate: true });
	// The decrement runs on a copy, so the counter itself is untouched.
	assert.match(code, /let r4_0 = r2_0;\s*const r3_0 = r4_0--;/);
	// The counter itself is never updated in place.
	assert.doesNotMatch(code, /r2_0--/);
	assert.equal(phi.sources.get(2)?.index, 4);
});

Deno.test('an unconsumed loop counter update lifts to a bare statement', () => {
	// Nothing reads either half, so the counter needs no coercion and the
	// update is the whole statement.
	const { code, phi } = liftLoopCounterLatch({ consumeOld: false });
	assert.equal(code, 'r2_0--;');
	assert.equal(phi.sources.get(2)?.index, 2);
});

Deno.test('an uncoerced loop counter whose old value is read is declined', () => {
	// The pre-update value lives in the target's own register, so naming it
	// would emit `r = r++` and discard the update.
	const { code, phi } = liftLoopCounterLatch({
		consumeOld: false,
		readBeforeUpdate: true,
	});
	// The counter itself is never updated in place.
	assert.doesNotMatch(code, /r2_0--/);
	assert.equal(phi.sources.get(2)?.index, 4);
});

Deno.test('a consumer scheduled above the update still closes the window', () => {
	// Hermes emits `a[i--]` as <ToNumeric; GetByVal; Dec>: the postfix value's
	// consumer sits between the read and the update.
	const { code, phi } = liftLoopCounterLatch({ gap: 'reads-coerced' });
	assert.match(code, /^const r3_0 = r2_0--;$/m);
	assert.doesNotMatch(code, /%ToNumeric/);
	// The update must precede the consumer that reads its value.
	assert.match(code, /r3_0 = r2_0--;[\s\S]*r6_0\[r3_0\]/);
	assert.equal(phi.sources.get(2)?.index, 2);
});

Deno.test('a gap that reads the counter keeps the window open', () => {
	// Emitting the update where the coercion sat would move the write ahead of
	// this read, which observes the pre-update value.
	const { code, phi } = liftLoopCounterLatch({ gap: 'reads-counter' });
	// The decrement runs on a copy, so the gap's read of the counter still
	// sees the value it saw before.
	assert.match(code, /let r4_0 = r2_0;\s*const r3_0 = r4_0--;/);
	assert.match(code, /r6_0\[r2_0\]/);
	// The counter itself is never updated in place.
	assert.doesNotMatch(code, /r2_0--/);
	assert.equal(phi.sources.get(2)?.index, 4);
});

/**
 * Two updates of one register in a row, as `p[i++] + p[i++]` emits them: only
 * the second result reaches the loop-header Phi, so neither window closes on
 * its own.
 */
function liftChainedCounterLatch(options: { tailEscapes?: boolean } = {}) {
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const entry = ssaLiteralSliceRegister(1);
	const counter = ssaLiteralSliceRegister(2);
	const firstOld = ssaLiteralSliceRegister(3);
	const firstNew = ssaLiteralSliceRegister(4);
	const secondOld = ssaLiteralSliceRegister(5);
	const secondNew = ssaLiteralSliceRegister(6);
	const arr = ssaLiteralSliceRegister(7);
	const readA = ssaLiteralSliceRegister(8);
	const readB = ssaLiteralSliceRegister(9);
	const phi = {
		instruction: 'Phi',
		destination: counter,
		sources: new Map([[0, entry], [2, secondNew]]),
	} as unknown as SSAInstruction;
	const coerce = (
		offset: number,
		destination: SSARegister,
		argument: SSARegister,
	) => ({
		instruction: 'ToNumeric',
		...meta(offset),
		destination: asRegister(destination.index),
		argument: asRegister(argument.index),
		defs: { destination },
		uses: { argument },
	} as SSAInstruction);
	const inc = (
		offset: number,
		destination: SSARegister,
		argument: SSARegister,
	) => ({
		instruction: 'Inc',
		...meta(offset),
		destination: asRegister(destination.index),
		argument: asRegister(argument.index),
		defs: { destination },
		uses: { argument },
	} as SSAInstruction);
	const index = (
		offset: number,
		destination: SSARegister,
		property: SSARegister,
	) => ({
		instruction: 'GetByVal',
		...meta(offset),
		destination: asRegister(destination.index),
		object: asRegister(arr.index),
		property: asRegister(property.index),
		defs: { destination },
		uses: { object: arr, property },
	} as SSAInstruction);
	const latch: SSABasicBlock = {
		address: 2,
		instructions: [],
		ssaInstructions: [
			coerce(0, firstOld, counter),
			index(1, readA, firstOld),
			inc(2, firstNew, firstOld),
			coerce(3, secondOld, firstNew),
			index(4, readB, secondOld),
			inc(5, secondNew, secondOld),
			...(options.tailEscapes
				? [{
					instruction: 'Throw',
					...meta(6),
					exception: asRegister(counter.index),
					defs: {},
					uses: { exception: counter },
				} as SSAInstruction]
				: []),
		],
		consequentAddresses: [1],
		predicate: null,
	};
	const func = {
		id: 7,
		paramCount: 0,
		objectShapeKeysByRegister: new Map(),
		file: {
			getIdentifier: () => 'count',
			getObjectBufferElements: () => ({ keys: [], values: [] }),
			getArrayBufferElements: () => [],
		},
		fromIdentifierRef: () => t.identifier('count'),
		getParam: (i: number) => t.identifier(`param${i}`),
		ssa: {
			basicBlocks: new Map([[1, {
				address: 1,
				instructions: [],
				ssaInstructions: [phi],
				consequentAddresses: [2],
				predicate: null,
			}], [2, latch]]),
			exceptionHandlers: [],
			_func: {
				basicBlocks: new Map([
					[1, { instructions: [], consequentAddresses: [2] }],
					[2, { instructions: [], consequentAddresses: [1] }],
				]),
				exceptionHandlers: [],
			},
		},
	} as unknown as IRFunction;
	const code = generate(
		t.program(liftSSABlocktoIR(func, latch).body as t.Statement[]),
	).code;
	return {
		code,
		phi: phi as unknown as { sources: Map<number, SSARegister> },
	};
}

Deno.test('two updates in a row share one l-reference', () => {
	const { code, phi } = liftChainedCounterLatch();
	assert.doesNotMatch(code, /%ToNumeric/);
	// Both windows name the same register, in bytecode order.
	assert.match(code, /r3_0 = r2_0\+\+;[\s\S]*r5_0 = r2_0\+\+;/);
	assert.match(code, /r7_0\[r3_0\]/);
	assert.match(code, /r7_0\[r5_0\]/);
	// Only the run's last result is what the back edge carried.
	assert.equal(phi.sources.get(2)?.index, 2);
});

Deno.test('a destination-only chain preserves an escaped variable', () => {
	const { code, phi } = liftChainedCounterLatch({ tailEscapes: true });
	assert.doesNotMatch(code, /%ToNumeric/);
	// The tail destination is the private mutable target. The escaped counter
	// keeps its pre-update value, while both expression results stay ordered.
	assert.match(
		code,
		/let r6_0 = r2_0;[\s\S]*r3_0 = r6_0\+\+;[\s\S]*r5_0 = r6_0\+\+;/,
	);
	assert.match(code, /throw r2_0;/);
	assert.equal(phi.sources.get(2)?.index, 6);
});

/**
 * `out[i++] = x` inside a conditional arm: the operand comes from the Phi that
 * dominates the block, and the result is written into the Phi at the join. The
 * two Phis are the same variable only because the `Inc` links them.
 */
function liftJoinCounterArm(options: { escapes?: boolean } = {}) {
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const entry = ssaLiteralSliceRegister(1);
	const counter = ssaLiteralSliceRegister(2);
	const old = ssaLiteralSliceRegister(3);
	const next = ssaLiteralSliceRegister(4);
	const joined = ssaLiteralSliceRegister(5);
	const arr = ssaLiteralSliceRegister(6);
	const other = ssaLiteralSliceRegister(7);
	// Block 1 dominates; block 2 is the arm; block 3 joins.
	const headerPhi = {
		instruction: 'Phi',
		destination: counter,
		sources: new Map([[0, entry]]),
	} as unknown as SSAInstruction;
	const joinPhi = {
		instruction: 'Phi',
		destination: joined,
		sources: new Map([[1, counter], [2, next]]),
	} as unknown as SSAInstruction;
	const arm: SSABasicBlock = {
		address: 2,
		instructions: [],
		ssaInstructions: [
			{
				instruction: 'ToNumeric',
				...meta(0),
				destination: asRegister(old.index),
				argument: asRegister(counter.index),
				defs: { destination: old },
				uses: { argument: counter },
			} as SSAInstruction,
			{
				instruction: 'PutByVal',
				...meta(1),
				object: asRegister(arr.index),
				property: asRegister(old.index),
				value: asRegister(other.index),
				defs: {},
				uses: { object: arr, property: old, value: other },
			} as SSAInstruction,
			{
				instruction: 'Inc',
				...meta(2),
				destination: asRegister(next.index),
				argument: asRegister(old.index),
				defs: { destination: next },
				uses: { argument: old },
			} as SSAInstruction,
		],
		consequentAddresses: [3],
		predicate: null,
	};
	const join: SSABasicBlock = {
		address: 3,
		instructions: [],
		ssaInstructions: [
			joinPhi,
			...(options.escapes
				? [{
					instruction: 'Throw',
					...meta(3),
					exception: asRegister(counter.index),
					defs: {},
					uses: { exception: counter },
				} as SSAInstruction]
				: []),
		],
		consequentAddresses: [],
		predicate: null,
	};
	const func = {
		id: 7,
		paramCount: 0,
		objectShapeKeysByRegister: new Map(),
		file: {
			getIdentifier: () => 'count',
			getObjectBufferElements: () => ({ keys: [], values: [] }),
			getArrayBufferElements: () => [],
		},
		fromIdentifierRef: () => t.identifier('count'),
		getParam: (i: number) => t.identifier(`param${i}`),
		ssa: {
			basicBlocks: new Map([
				[1, {
					address: 1,
					instructions: [],
					ssaInstructions: [headerPhi],
					consequentAddresses: [2, 3],
					predicate: null,
				}],
				[2, arm],
				[3, join],
			]),
			exceptionHandlers: [],
			_func: {
				basicBlocks: new Map([
					[1, { instructions: [], consequentAddresses: [2, 3] }],
					[2, { instructions: [], consequentAddresses: [3] }],
					[3, { instructions: [], consequentAddresses: [] }],
				]),
				exceptionHandlers: [],
			},
		},
	} as unknown as IRFunction;
	const code = generate(
		t.program(liftSSABlocktoIR(func, arm).body as t.Statement[]),
	).code;
	return {
		code,
		joinPhi: joinPhi as unknown as { sources: Map<number, SSARegister> },
	};
}

Deno.test('an update written back at a join names the register it read', () => {
	const { code, joinPhi } = liftJoinCounterArm();
	assert.doesNotMatch(code, /%ToNumeric/);
	assert.match(code, /const r3_0 = r2_0\+\+;\s*r6_0\[r3_0\] = r7_0;/);
	// The join edge now carries the register the update wrote, not a copy of
	// a result the fused update no longer produces.
	assert.equal(joinPhi.sources.get(2)?.index, 2);
});

Deno.test('a join update whose variable is read past the join is declined', () => {
	const { code, joinPhi } = liftJoinCounterArm({ escapes: true });
	// The increment runs on a copy, so the join still carries its own value.
	assert.match(code, /let r4_0 = r2_0;\s*const r3_0 = r4_0\+\+;/);
	// The counter itself is never updated in place.
	assert.doesNotMatch(code, /r2_0\+\+/);
	assert.equal(joinPhi.sources.get(2)?.index, 4);
});

/**
 * `var n = arguments.length; while (n--)` peels its first update above the
 * loop. That window has no Phi to read from -- the binding the iterations
 * share is only created by the Phi its result feeds.
 */
function liftPeeledFirstUpdate(
	options: {
		operandShared?: boolean;
		/** Read the length through a property load, as `a.length` does. */
		loadShaped?: boolean;
		/** Schedule a consumer of the coerced value above the update. */
		gap?: boolean;
		/** Read the operand again before the update, where it is harmless. */
		operandReadEarly?: boolean;
	} = {},
) {
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const source = ssaLiteralSliceRegister(1);
	const old = ssaLiteralSliceRegister(2);
	const first = ssaLiteralSliceRegister(3);
	const holder = ssaLiteralSliceRegister(6);
	const spare = ssaLiteralSliceRegister(7);
	const carried = ssaLiteralSliceRegister(4);
	const looped = ssaLiteralSliceRegister(5);
	const phi = {
		instruction: 'Phi',
		destination: carried,
		sources: new Map([[0, first], [1, looped]]),
	} as unknown as SSAInstruction;
	const preheader: SSABasicBlock = {
		address: 0,
		instructions: [],
		ssaInstructions: [
			options.loadShaped
				? {
					instruction: 'GetById',
					...meta(0),
					destination: asRegister(source.index),
					object: asRegister(holder.index),
					cacheIndex: 0,
					property: asStringRef(2),
					defs: { destination: source },
					uses: { object: holder },
				} as SSAInstruction
				: {
					instruction: 'GetArgumentsLength',
					...meta(0),
					destination: asRegister(source.index),
					defs: { destination: source },
					uses: {},
				} as SSAInstruction,
			...(options.operandReadEarly
				? [{
					instruction: 'GetByVal',
					...meta(7),
					destination: asRegister(spare.index),
					object: asRegister(holder.index),
					property: asRegister(source.index),
					defs: { destination: spare },
					uses: { object: holder, property: source },
				} as SSAInstruction]
				: []),
			{
				instruction: 'ToNumeric',
				...meta(1),
				destination: asRegister(old.index),
				argument: asRegister(source.index),
				defs: { destination: old },
				uses: { argument: source },
			} as SSAInstruction,
			...(options.gap
				? [{
					instruction: 'GetByVal',
					...meta(6),
					destination: asRegister(spare.index),
					object: asRegister(holder.index),
					property: asRegister(old.index),
					defs: { destination: spare },
					uses: { object: holder, property: old },
				} as SSAInstruction]
				: []),
			{
				instruction: 'Dec',
				...meta(2),
				destination: asRegister(first.index),
				argument: asRegister(old.index),
				defs: { destination: first },
				uses: { argument: old },
			} as SSAInstruction,
			// The loop-entry test reads the pre-update value.
			{
				instruction: 'Throw',
				...meta(3),
				exception: asRegister(old.index),
				defs: {},
				uses: { exception: old },
			} as SSAInstruction,
			...(options.operandShared
				? [{
					instruction: 'Throw',
					...meta(4),
					exception: asRegister(source.index),
					defs: {},
					uses: { exception: source },
				} as SSAInstruction]
				: []),
		],
		consequentAddresses: [1],
		predicate: null,
	};
	const header: SSABasicBlock = {
		address: 1,
		instructions: [],
		ssaInstructions: [
			phi,
			{
				instruction: 'Dec',
				...meta(5),
				destination: asRegister(looped.index),
				argument: asRegister(carried.index),
				defs: { destination: looped },
				uses: { argument: carried },
			} as SSAInstruction,
		],
		consequentAddresses: [1],
		predicate: null,
	};
	const func = {
		id: 7,
		paramCount: 0,
		objectShapeKeysByRegister: new Map(),
		file: {
			getIdentifier: () => 'count',
			getObjectBufferElements: () => ({ keys: [], values: [] }),
			getArrayBufferElements: () => [],
		},
		fromIdentifierRef: () => t.identifier('count'),
		getParam: (i: number) => t.identifier(`param${i}`),
		ssa: {
			basicBlocks: new Map([[0, preheader], [1, header]]),
			exceptionHandlers: [],
			_func: {
				basicBlocks: new Map([
					[0, { instructions: [], consequentAddresses: [1] }],
					[1, { instructions: [], consequentAddresses: [1] }],
				]),
				exceptionHandlers: [],
			},
		},
	} as unknown as IRFunction;
	const code = generate(
		t.program(liftSSABlocktoIR(func, preheader).body as t.Statement[]),
	).code;
	return {
		code,
		phi: phi as unknown as { sources: Map<number, SSARegister> },
	};
}

Deno.test('a peeled first update materialises the loop binding and updates it', () => {
	const { code, phi } = liftPeeledFirstUpdate();
	assert.doesNotMatch(code, /%ToNumeric/);
	// The value has to reach the shared binding before the update names it.
	assert.match(code, /r4_0 = r1_0;\s*const r2_0 = r4_0--;/);
	// The entry edge now carries that binding rather than a result the fused
	// update no longer produces.
	assert.equal(phi.sources.get(0)?.index, 4);
});

Deno.test('a peeled update read again after it is declined', () => {
	// The operand keeps its own register, so another reader is harmless on its
	// own -- this one sits after the update, where it would observe the write
	// the rewrite moved ahead of it.
	const { code, phi } = liftPeeledFirstUpdate({ operandShared: true });
	// The decrement runs on a copy, leaving the read value intact.
	assert.match(code, /let r3_0 = r1_0;\s*const r2_0 = r3_0--;/);
	// The shared binding is never the thing updated.
	assert.doesNotMatch(code, /r4_0--/);
	assert.equal(phi.sources.get(0)?.index, 3);
});

Deno.test('a property read with no store is not treated as an l-reference', () => {
	// `var n = a.length; while (n--)` puts a load in front of the coercion,
	// but nothing ever stores back through it -- so there is no store whose
	// move a consumer scheduled in between could observe.
	const { code, phi } = liftPeeledFirstUpdate({
		loadShaped: true,
		gap: true,
	});
	assert.doesNotMatch(code, /%ToNumeric/);
	// The load keeps its own value; the binding is materialised from it.
	assert.match(code, /const r1_0 = r6_0\.count;\s*r4_0 = r1_0;/);
	assert.match(code, /const r2_0 = r4_0--;\s*const r7_0 = r6_0\[r2_0\]/);
	assert.equal(phi.sources.get(0)?.index, 4);
});

Deno.test('a peel whose operand is read before the update still closes', () => {
	// The operand keeps its own register and this read precedes the update, so
	// it sees the same value either way.
	const { code, phi } = liftPeeledFirstUpdate({ operandReadEarly: true });
	assert.doesNotMatch(code, /%ToNumeric/);
	assert.match(code, /r4_0 = r1_0;\s*const r2_0 = r4_0--;/);
	assert.equal(phi.sources.get(0)?.index, 4);
});

Deno.test('an unfoldable increment keeps the coercion its operand needs', () => {
	// `Inc` coerces, so `x + 1` on a property read would concatenate where the
	// instruction counts. The update expression on a copy says it exactly.
	const code = liftInstructions(
		updateIdiomInstructions({ readOld: true, readNew: true }),
	);
	assert.match(code, /let r4_0 = r2_0;\s*r4_0\+\+;/);
	assert.doesNotMatch(code, /r2_0 \+ 1/);
});

Deno.test('an increment of a provably numeric value stays plain arithmetic', () => {
	// A counter seeded by a numeric constant is a Number however many times it
	// goes round the loop, so the coercion is a no-op and `+ 1` reads better.
	const zero = ssaLiteralSliceRegister(1);
	const counter = ssaLiteralSliceRegister(2);
	const next = ssaLiteralSliceRegister(3);
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const code = liftInstructions([
		{
			instruction: 'LoadConst',
			...meta(0),
			destination: asRegister(zero.index),
			value: 0,
			defs: { destination: zero },
			uses: {},
		} as SSAInstruction,
		{
			instruction: 'Mov',
			...meta(1),
			destination: asRegister(counter.index),
			source: asRegister(zero.index),
			defs: { destination: counter },
			uses: { source: zero },
		} as SSAInstruction,
		{
			instruction: 'Inc',
			...meta(2),
			destination: asRegister(next.index),
			argument: asRegister(counter.index),
			defs: { destination: next },
			uses: { argument: counter },
		} as SSAInstruction,
		{
			instruction: 'Throw',
			...meta(3),
			exception: asRegister(next.index),
			defs: {},
			uses: { exception: next },
		} as SSAInstruction,
	]);
	assert.match(code, /r3_0 = r2_0 \+ 1;/);
	assert.doesNotMatch(code, /\+\+/);
});

Deno.test('a window with no write-back still needs no intrinsic', () => {
	// Nothing names the variable -- both halves are read, so neither `x++` nor
	// `++x` on it would do. The coercion is what `--` performs, so running it
	// on the update's own destination reproduces the pair exactly: the
	// destination holds the new value, the coercion's register the old.
	const code = liftInstructions(
		updateIdiomInstructions({
			coerce: true,
			readOld: true,
			readNew: true,
			storeSlot: 9,
		}),
	);
	assert.doesNotMatch(code, /%ToNumeric/);
	assert.match(code, /let r4_0 = r2_0;\s*const r3_0 = r4_0\+\+;/);
	// The slot that was read is not updated in place.
	assert.doesNotMatch(code, /\[3\]\+\+/);
});

Deno.test('allocator copies preserve a public postfix result', () => {
	const code = liftInstructions(
		updateIdiomInstructions({
			coerce: true,
			copyCoercion: true,
			readOld: true,
		}),
	);
	assert.doesNotMatch(code, /%ToNumeric/);
	assert.doesNotMatch(code, /r3_0|r7_0/);
	assert.match(code, /const r6_0 = %expectEnvironment\(r1_0\)\[3\]\+\+;/);
});

Deno.test('a destination-only update chain shares its mutable register', () => {
	const source = ssaLiteralSliceRegister(1);
	const firstOld = ssaLiteralSliceRegister(2);
	const firstNew = ssaLiteralSliceRegister(3);
	const secondOld = ssaLiteralSliceRegister(4);
	const secondNew = ssaLiteralSliceRegister(5);
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const instructions: SSAInstruction[] = [
		{
			instruction: 'ToNumeric',
			...meta(0),
			destination: asRegister(firstOld.index),
			argument: asRegister(source.index),
			defs: { destination: firstOld },
			uses: { argument: source },
		} as SSAInstruction,
		{
			instruction: 'Inc',
			...meta(1),
			destination: asRegister(firstNew.index),
			argument: asRegister(firstOld.index),
			defs: { destination: firstNew },
			uses: { argument: firstOld },
		} as SSAInstruction,
		{
			instruction: 'ToNumeric',
			...meta(2),
			destination: asRegister(secondOld.index),
			argument: asRegister(firstNew.index),
			defs: { destination: secondOld },
			uses: { argument: firstNew },
		} as SSAInstruction,
		{
			instruction: 'Inc',
			...meta(3),
			destination: asRegister(secondNew.index),
			argument: asRegister(secondOld.index),
			defs: { destination: secondNew },
			uses: { argument: secondOld },
		} as SSAInstruction,
	];
	for (
		const [offset, exception] of [firstOld, secondOld, secondNew].entries()
	) {
		instructions.push({
			instruction: 'Throw',
			...meta(offset + 4),
			exception: asRegister(exception.index),
			defs: {},
			uses: { exception },
		} as SSAInstruction);
	}
	const code = liftInstructions(instructions);
	assert.doesNotMatch(code, /%ToNumeric/);
	assert.match(
		code,
		/let r5_0 = r1_0;\s*const r2_0 = r5_0\+\+;\s*const r4_0 = r5_0\+\+;/,
	);
});

Deno.test('ToNumeric after an increment is an identity', () => {
	const source = ssaLiteralSliceRegister(1);
	const updated = ssaLiteralSliceRegister(2);
	const coerced = ssaLiteralSliceRegister(3);
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const code = liftInstructions([
		{
			instruction: 'Inc',
			...meta(0),
			destination: asRegister(updated.index),
			argument: asRegister(source.index),
			defs: { destination: updated },
			uses: { argument: source },
		} as SSAInstruction,
		{
			instruction: 'ToNumeric',
			...meta(1),
			destination: asRegister(coerced.index),
			argument: asRegister(updated.index),
			defs: { destination: coerced },
			uses: { argument: updated },
		} as SSAInstruction,
		{
			instruction: 'Throw',
			...meta(2),
			exception: asRegister(coerced.index),
			defs: {},
			uses: { exception: coerced },
		} as SSAInstruction,
	]);
	assert.doesNotMatch(code, /%ToNumeric/);
	assert.match(code, /const r3_0 = r2_0;/);
});

Deno.test('ToNumeric of a proven Number is an identity', () => {
	const number = ssaLiteralSliceRegister(1);
	const coerced = ssaLiteralSliceRegister(2);
	const meta = (functionLocalOffset: number) => ({
		functionLocalOffset,
		length: InstructionLength.NORMAL,
		type: InstructionType.NORMAL,
		strict: InstructionStrictness.NORMAL,
	});
	const code = liftInstructions([
		{
			instruction: 'LoadConst',
			...meta(0),
			destination: asRegister(number.index),
			value: 4,
			defs: { destination: number },
			uses: {},
		} as SSAInstruction,
		{
			instruction: 'ToNumeric',
			...meta(1),
			destination: asRegister(coerced.index),
			argument: asRegister(number.index),
			defs: { destination: coerced },
			uses: { argument: number },
		} as SSAInstruction,
		{
			instruction: 'Throw',
			...meta(2),
			exception: asRegister(coerced.index),
			defs: {},
			uses: { exception: coerced },
		} as SSAInstruction,
	]);
	assert.doesNotMatch(code, /%ToNumeric/);
	assert.match(code, /const r2_0 = r1_0;/);
});
