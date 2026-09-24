import { strict as assert } from 'node:assert';
import { parse } from '@babel/parser';
import generate from '@babel/generator';
import traverse, { NodePath } from '@babel/traverse';
import * as t from '@babel/types';
import {
	flattenElseIfBlock,
	inlineBranchArrayConstructionsToFixpoint,
	inlineNullPrototypeObjectLiteral,
	inlineObjectConstruction,
	inlineObjectConstructionsToFixpoint,
	invertTest,
	liftHermesApplyCalls,
	liftHermesConcatCalls,
	lowerResidualArraySpreadCalls,
	rewriteTwoArgumentCopyDataProperties,
	rotateTerminatingGuardIntoElseIf,
	toCompoundAssignment,
} from './expression.ts';
import type { LiftedAST } from './mod.ts';
import { foldConditionalValuesInBody } from './phi.ts';

Deno.test('invertTest applies De Morgan to logical conditions', () => {
	const condition = t.logicalExpression(
		'&&',
		t.binaryExpression(
			'!=',
			t.identifier('value'),
			t.nullLiteral(),
		),
		t.callExpression(t.identifier('matches'), []),
	);

	assert.equal(
		generate(invertTest(condition)).code,
		'value == null || !matches()',
	);
});

Deno.test('late Hermes concat calls become template literals', () => {
	const program = t.program([
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('concat'),
				),
				t.identifier('call'),
			),
			[
				t.stringLiteral('Media sink wants: '),
				t.callExpression(
					t.memberExpression(
						t.identifier('JSON'),
						t.identifier('stringify'),
					),
					[t.identifier('value')],
				),
			],
		)),
	]);
	const file = t.file(program);

	assert.equal(liftHermesConcatCalls(file), 1);
	assert.equal(
		generate(program).code,
		'`Media sink wants: ${JSON.stringify(value)}`;',
	);
});

Deno.test('late Hermes apply-family calls become standard JavaScript', () => {
	const newTarget = t.metaProperty(
		t.identifier('new'),
		t.identifier('target'),
	);
	const program = t.program([
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('apply'),
			),
			[
				t.identifier('Widget'),
				t.arrayExpression([
					t.identifier('one'),
					t.spreadElement(t.identifier('rest')),
				]),
			],
		)),
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('method'),
				t.memberExpression(
					t.identifier('receiver'),
					t.identifier('run'),
				),
			),
		]),
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('apply'),
			),
			[
				t.identifier('method'),
				t.arrayExpression([t.identifier('one')]),
				t.identifier('receiver'),
			],
		)),
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('applyArguments'),
			),
			[t.identifier('fn'), t.identifier('receiver')],
		)),
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('applyWithArguments'),
			),
			[t.identifier('fn'), t.identifier('undefined')],
		)),
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('applyWithNewTarget'),
			),
			[
				t.identifier('Base'),
				t.identifier('args'),
				t.callExpression(
					t.v8IntrinsicIdentifier('CreateThisForSuper'),
					[
						t.identifier('Base'),
						t.cloneNode(newTarget),
					],
				),
				newTarget,
			],
		)),
	]);
	const file = t.file(program);

	assert.equal(liftHermesApplyCalls(file), 5);
	assert.equal(
		generate(program).code,
		'new Widget(one, ...rest);\n' +
			'const method = receiver.run;\n' +
			'method.call(receiver, one);\n' +
			'fn.call(receiver, ...arguments);\n' +
			'fn(...arguments);\n' +
			'Reflect.construct(Base, args, new.target);',
	);
});

Deno.test('single-if alternate blocks flatten to else-if', () => {
	const nested = t.ifStatement(
		t.identifier('inner'),
		t.blockStatement([]),
	);
	const outer = t.ifStatement(
		t.identifier('outer'),
		t.blockStatement([]),
		t.blockStatement([nested]),
	);

	assert.equal(flattenElseIfBlock(outer), true);
	assert.equal(outer.alternate, nested);
	assert.equal(
		generate(outer).code,
		'if (outer) {} else if (inner) {}',
	);
});

Deno.test('compound assignment requires the exact generated register', () => {
	const unrelated = t.assignmentExpression(
		'=',
		t.identifier('r0_4'),
		t.binaryExpression('-', t.identifier('r2_2'), t.numericLiteral(1)),
	);
	assert.equal(toCompoundAssignment(unrelated), undefined);

	const selfUpdate = t.assignmentExpression(
		'=',
		t.identifier('r0_4'),
		t.binaryExpression('-', t.identifier('r0_4'), t.numericLiteral(1)),
	);
	assert.equal(generate(toCompoundAssignment(selfUpdate)!).code, 'r0_4 -= 1');
});

Deno.test('terminating negative guards rotate into else-if chains', () => {
	const statement = t.ifStatement(
		t.unaryExpression('!', t.identifier('first')),
		t.blockStatement([
			t.ifStatement(
				t.unaryExpression('!', t.identifier('second')),
				t.blockStatement([t.returnStatement()]),
			),
			t.expressionStatement(
				t.callExpression(t.identifier('secondArm'), []),
			),
		]),
		t.blockStatement([
			t.expressionStatement(
				t.callExpression(t.identifier('firstArm'), []),
			),
		]),
	);

	const rotated = rotateTerminatingGuardIntoElseIf(statement);
	assert(rotated);
	assert.equal(
		generate(rotated).code,
		'if (first) {\n  firstArm();\n} else if (second) {\n  secondArm();\n} else {\n  return;\n}',
	);
});

Deno.test('resumes a partially folded NewObject after a temporary blocker', () => {
	const accumulator = t.objectExpression([]) as LiftedAST<t.ObjectExpression>;
	accumulator.extra = { instruction: 'NewObject' };
	const accumulatorDeclaration = t.variableDeclaration('const', [
		t.variableDeclarator(t.identifier('object'), accumulator),
	]) as LiftedAST<t.VariableDeclaration>;
	// Lifted construction metadata is retained on both the declaration and its
	// initializer, as it is for NewObjectWithBuffer.
	accumulatorDeclaration.extra = { instruction: 'NewObject' };
	const body: t.Statement[] = [
		accumulatorDeclaration,
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('object'), t.identifier('key')),
			t.stringLiteral('entry'),
		)),
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('temporary'),
				t.callExpression(t.identifier('makeTemporary'), []),
			),
		]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('object'), t.identifier('value')),
			t.callExpression(t.identifier('makeValue'), []),
		)),
		t.expressionStatement(
			t.callExpression(t.identifier('consume'), [t.identifier('object')]),
		),
	];
	const program = t.program(body);
	const file = t.file(program);

	let declaration: NodePath<t.VariableDeclaration> | null = null;
	traverse(file, {
		VariableDeclaration(path) {
			if (
				path.get('declarations.0.id').isIdentifier({ name: 'object' })
			) {
				declaration = path;
			}
		},
	});
	assert(declaration);
	const partialDeclaration = declaration as NodePath<t.VariableDeclaration>;
	assert.equal(inlineObjectConstruction(partialDeclaration), true);
	assert.equal(
		(partialDeclaration.get('declarations.0.init').node as LiftedAST<
			t.Node
		>)
			.extra?.instruction,
		'NewObject',
	);

	// Simulate the ordinary cleanup pass eliminating the temporary which stopped
	// the first construction scan, then rebuild bindings for the next fixpoint.
	program.body.splice(1, 1);
	declaration = null;
	traverse.cache.clearScope();
	traverse(file, {
		VariableDeclaration(path) {
			if (
				path.get('declarations.0.id').isIdentifier({ name: 'object' })
			) {
				declaration = path;
			}
		},
	});
	assert(declaration);
	assert.equal(
		inlineObjectConstruction(
			declaration as NodePath<t.VariableDeclaration>,
		),
		true,
	);
	assert.equal(
		generate(program).code,
		'consume({\n' +
			'  key: "entry",\n' +
			'  value: makeValue()\n' +
			'});',
	);
});

Deno.test('folds object writes across movable register aliases', () => {
	const accumulator = t.objectExpression([]) as LiftedAST<t.ObjectExpression>;
	accumulator.extra = { instruction: 'NewObject' };
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(t.identifier('object'), accumulator),
		]) as LiftedAST<t.VariableDeclaration>,
		t.variableDeclaration('const', [
			t.variableDeclarator(t.identifier('radius'), t.identifier('outer')),
		]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('object'), t.identifier('left')),
			t.identifier('radius'),
		)),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('object'), t.identifier('right')),
			t.identifier('radius'),
		)),
		t.returnStatement(t.identifier('object')),
	];
	const program = t.program(body);
	const file = t.file(program);

	traverse(file, {
		VariableDeclaration(path) {
			if (
				path.get('declarations.0.id').isIdentifier({ name: 'object' })
			) inlineObjectConstruction(path);
		},
	});

	assert.equal(
		generate(program).code,
		'return {\n  left: outer,\n  right: outer\n};',
	);
});

Deno.test('folds object spreads after setup temporaries', () => {
	const accumulator = t.objectExpression([]) as LiftedAST<t.ObjectExpression>;
	accumulator.extra = { instruction: 'NewObject' };
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(t.identifier('object'), accumulator),
		]) as LiftedAST<t.VariableDeclaration>,
		t.variableDeclaration('const', [
			t.variableDeclarator(t.identifier('receiver'), t.thisExpression()),
		]),
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('source'),
				t.callExpression(t.identifier('loadSource'), []),
			),
		]),
		t.expressionStatement(t.callExpression(
			t.memberExpression(t.identifier('Object'), t.identifier('assign')),
			[t.identifier('object'), t.identifier('source')],
		)),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(
				t.identifier('object'),
				t.stringLiteral('value'),
				true,
			),
			t.conditionalExpression(
				t.identifier('condition'),
				t.callExpression(t.identifier('makeValue'), []),
				t.nullLiteral(),
			),
		)),
		t.returnStatement(t.identifier('object')),
	];
	const program = t.program(body);
	const file = t.file(program);

	assert.equal(inlineObjectConstructionsToFixpoint(file), 1);
	assert.equal(
		generate(program).code,
		'const receiver = this;\n' +
			'const source = loadSource();\n' +
			'return {\n' +
			'  ...source,\n' +
			'  value: condition ? makeValue() : null\n' +
			'};',
	);
});

Deno.test('folds array writes across movable register aliases', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('items'),
				t.arrayExpression([t.identifier('first'), null]),
			),
		]),
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('second'),
				t.logicalExpression(
					'&&',
					t.binaryExpression(
						'!=',
						t.identifier('value'),
						t.nullLiteral(),
					),
					t.memberExpression(
						t.identifier('styles'),
						t.identifier('wrapperWithBorder'),
					),
				),
			),
		]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(
				t.identifier('items'),
				t.numericLiteral(1),
				true,
			),
			t.identifier('second'),
		)),
		t.returnStatement(t.identifier('items')),
	];
	const program = t.program(body);
	const file = t.file(program);

	traverse(file, {
		VariableDeclaration(path) {
			if (
				path.get('declarations.0.id').isIdentifier({ name: 'items' })
			) inlineObjectConstruction(path);
		},
	});

	assert.equal(
		generate(program).code,
		'return [first, value != null && styles.wrapperWithBorder];',
	);
});

Deno.test('does not fold a captured array-spread offset that still escapes', () => {
	const file = t.file(t.program([
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('items'),
			t.newExpression(t.identifier('Array'), [t.numericLiteral(1)]),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('offset'),
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('arraySpread'),
				),
				[
					t.identifier('items'),
					t.identifier('source'),
					t.numericLiteral(0),
				],
			),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('value'),
			t.callExpression(t.identifier('makeValue'), []),
		)]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(
				t.identifier('items'),
				t.identifier('offset'),
				true,
			),
			t.identifier('value'),
		)),
		t.returnStatement(t.identifier('offset')),
	]));

	assert.equal(inlineObjectConstructionsToFixpoint(file), 0);
	assert.match(
		generate(file).code,
		/const offset = HermesInternal\.arraySpread\(items, source, 0\);/,
	);
	assert.match(generate(file).code, /items\[offset\] = value;/);
});

Deno.test('construction fixpoint recrawls bindings after late declaration normalization', () => {
	const file = parse(`
		function build(extra) {
			let items;
			items = [first];
			HermesInternal.arraySpread(items, extra, 1);
			return items;
		}
	`);
	traverse(file, {
		Program(path) {
			path.scope.crawl();
			path.stop();
		},
	});

	const fn = file.program.body[0];
	if (!t.isFunctionDeclaration(fn)) throw new Error('missing test function');
	fn.body.body.splice(
		0,
		2,
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('items'),
				t.arrayExpression([t.identifier('first')]),
			),
		]),
	);

	assert.equal(inlineObjectConstructionsToFixpoint(file), 1);
	assert.equal(
		generate(file).code,
		'function build(extra) {\n  return [first, ...extra];\n}',
	);
});

Deno.test('folds a spread iterable alias at its original evaluation point', () => {
	const file = parse(`
		function build() {
			const items = [first()];
			const extra = loadExtra();
			HermesInternal.arraySpread(items, extra, 1);
			return consume(items);
		}
	`);

	assert.equal(inlineObjectConstructionsToFixpoint(file), 1);
	assert.equal(
		generate(file).code,
		'function build() {\n' +
			'  return consume([first(), ...loadExtra()]);\n' +
			'}',
	);
});

Deno.test('moves an empty accumulator past one spread setup declaration', () => {
	const file = parse(`
		function build(useAvatar) {
			const items = [];
			const r14_1 = getManager();
			HermesInternal.arraySpread(
				items,
				useAvatar ? [r14_1.avatar] : [r14_1.camera],
				0,
			);
			return consume(items);
		}
	`);

	assert.equal(inlineObjectConstructionsToFixpoint(file), 1);
	assert.equal(
		generate(file).code,
		'function build(useAvatar) {\n' +
			'  const r14_1 = getManager();\n' +
			'  return consume([...(useAvatar ? [r14_1.avatar] : [r14_1.camera])]);\n' +
			'}',
	);
});

Deno.test('folds left-associated writes after a captured spread offset', () => {
	const file = parse(`
		function build(source) {
			const items = new Array(3);
			const offset = HermesInternal.arraySpread(items, source, 0);
			items[offset] = first;
			items[offset + 1] = second;
			items[offset + 1 + 1] = third;
			return items;
		}
	`);

	assert.equal(inlineObjectConstructionsToFixpoint(file), 1);
	assert.equal(
		generate(file).code,
		'function build(source) {\n' +
			'  return [...source, first, second, third];\n' +
			'}',
	);
});

Deno.test('lowers a residual spread after intervening setup effects', () => {
	const file = parse(`
		function build() {
			const items = [first()];
			const helper = createHelper();
			helper.prepare();
			HermesInternal.arraySpread(items, helper.values(), 1);
			return consume(items);
		}
	`);

	assert.equal(lowerResidualArraySpreadCalls(file), 1);
	assert.equal(
		generate(file).code,
		'function build() {\n' +
			'  let items = [first()];\n' +
			'  const helper = createHelper();\n' +
			'  helper.prepare();\n' +
			'  items = [items[0], ...helper.values()];\n' +
			'  return consume(items);\n' +
			'}',
	);
});

Deno.test('preserves a captured residual spread offset', () => {
	const file = parse(`
		function build(source) {
			const items = new Array(2);
			const offset = HermesInternal.arraySpread(items, source, 0);
			const values = loadValues();
			items[offset] = values[0];
			items[offset + 1] = values[1];
			return items;
		}
	`);

	assert.equal(lowerResidualArraySpreadCalls(file), 1);
	assert.equal(
		generate(file).code,
		'function build(source) {\n' +
			'  let items = new Array(2);\n' +
			'  items = [...source];\n' +
			'  const offset = items.length;\n' +
			'  const values = loadValues();\n' +
			'  items[offset] = values[0];\n' +
			'  items[offset + 1] = values[1];\n' +
			'  return items;\n' +
			'}',
	);
});

Deno.test('folds reversed branch-local array spreads into a conditional value', () => {
	const file = parse(`
		const r7_6 = [];
		let r5_25;
		if (before) {
			HermesInternal.arraySpread(
				r7_6,
				incoming,
				HermesInternal.arraySpread(r7_6, current, 0),
			);
			r5_25 = r7_6;
		} else {
			HermesInternal.arraySpread(
				r7_6,
				current,
				HermesInternal.arraySpread(r7_6, incoming, 0),
			);
			r5_25 = r7_6;
		}
		consume(r5_25);
	`);

	assert.equal(inlineBranchArrayConstructionsToFixpoint(file), 1);
	assert.equal(foldConditionalValuesInBody(file.program.body), true);
	assert.equal(
		generate(file).code,
		'const r5_25 = before ? [...current, ...incoming] : [...incoming, ...current];\n' +
			'consume(r5_25);',
	);
});

Deno.test('folds a conditional spread source through its slice consumer', () => {
	const file = parse(`
		const r9_8 = [];
		let r14_5;
		if (hasBlocked) {
			HermesInternal.arraySpread(r9_8, blockedIds, 0);
			r14_5 = r9_8.slice(0, 2);
		} else {
			HermesInternal.arraySpread(r9_8, ignoredIds, 0);
			r14_5 = r9_8.slice(0, 2);
		}
		use(r14_5);
	`);

	assert.equal(inlineBranchArrayConstructionsToFixpoint(file), 1);
	assert.equal(foldConditionalValuesInBody(file.program.body), true);
	assert.equal(
		generate(file).code,
		'const r14_5 = hasBlocked ? [...blockedIds].slice(0, 2) : [...ignoredIds].slice(0, 2);\n' +
			'use(r14_5);',
	);
});

Deno.test('folds duplicated array construction in a terminating guard', () => {
	const file = parse(
		`
		let r1_6;
		r1_6 = new Array(1);
		if (matches) {
			r1_6[0] = current;
			HermesInternal.arraySpread(r1_6, parents, 1);
			return r1_6;
		}
		r1_6[0] = current;
		HermesInternal.arraySpread(r1_6, parents, 1);
		result = search(items, r1_6);
	`,
		{ allowReturnOutsideFunction: true },
	);

	assert.equal(inlineBranchArrayConstructionsToFixpoint(file), 1);
	assert.equal(
		generate(file).code,
		'if (matches) {\n' +
			'  return [current, ...parents];\n' +
			'}\n' +
			'result = search(items, [current, ...parents]);',
	);
});

Deno.test('keeps branch array construction when substitution reorders effects', () => {
	const file = parse(
		`
		let r1_6;
		r1_6 = [];
		if (matches) {
			HermesInternal.arraySpread(r1_6, values, 0);
			return r1_6;
		}
		HermesInternal.arraySpread(r1_6, values, 0);
		result = search(loadItems(), r1_6);
	`,
		{ allowReturnOutsideFunction: true },
	);

	assert.equal(inlineBranchArrayConstructionsToFixpoint(file), 0);
	assert.equal(
		(generate(file).code.match(/HermesInternal\.arraySpread/g) ?? [])
			.length,
		2,
	);
});

Deno.test('folds an adjacent silent null-prototype operation into its literal', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('dictionary'),
			t.objectExpression([
				t.objectProperty(t.identifier('key'), t.booleanLiteral(true)),
			]),
		)]),
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('silentSetPrototypeOf'),
			),
			[t.identifier('dictionary'), t.nullLiteral()],
		)),
		t.returnStatement(t.identifier('dictionary')),
	];
	const program = t.program(body);
	const file = t.file(program);
	traverse(file, {
		ExpressionStatement(path) {
			inlineNullPrototypeObjectLiteral(path);
		},
	});

	assert.equal(
		generate(program).code,
		'const dictionary = {\n' +
			'  __proto__: null,\n' +
			'  key: true\n' +
			'};\nreturn dictionary;',
	);
});

Deno.test('does not discard a materialized copyDataProperties exclusion map', () => {
	const copy = t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		[
			t.objectExpression([]),
			t.identifier('source'),
			t.objectExpression([
				t.objectProperty(t.identifier('excluded'), t.numericLiteral(0)),
			]),
		],
	);
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(t.identifier('rest'), copy),
		]),
		t.returnStatement(t.identifier('rest')),
	];
	const program = t.program(body);
	const file = t.file(program);
	let declaration: NodePath<t.VariableDeclaration> | null = null;
	traverse(file, {
		VariableDeclaration(path) {
			declaration = path;
		},
	});
	assert(declaration);
	assert.equal(
		inlineObjectConstruction(
			declaration as NodePath<t.VariableDeclaration>,
		),
		undefined,
	);
	assert.match(generate(program).code, /copyDataProperties/);
});

Deno.test('rewrites residual two-argument copyDataProperties helpers', () => {
	const program = t.program([
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('copyDataProperties'),
			),
			[t.identifier('target'), t.identifier('_rest_1_0_')],
		)),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('kept'),
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('copyDataProperties'),
				),
				[
					t.objectExpression([]),
					t.identifier('source'),
					t.identifier('excluded'),
				],
			),
		)]),
	]);

	assert.equal(rewriteTwoArgumentCopyDataProperties(program), 1);
	assert.equal(
		generate(program).code,
		'Object.assign(target, _rest_1_0_);\n' +
			'const kept = HermesInternal.copyDataProperties({}, source, excluded);',
	);
});

Deno.test('object construction fixpoint revisits a consumer unblocked by its source', () => {
	const helper = t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		[
			t.identifier('r1_1'),
			t.memberExpression(
				t.identifier('r3_1'),
				t.identifier('size'),
				true,
			),
		],
	);
	const file = t.file(t.program([
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			t.objectExpression([]),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r3_1'),
			t.objectExpression([]),
		)]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('r3_1'), t.identifier('md')),
			t.identifier('medium'),
		)),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('r3_1'), t.identifier('lg')),
			t.identifier('large'),
		)),
		t.expressionStatement(helper),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('r1_1'), t.identifier('color')),
			t.identifier('color'),
		)),
		t.returnStatement(t.identifier('r1_1')),
	]));

	assert.equal(inlineObjectConstructionsToFixpoint(file), 2);
	assert.equal(
		generate(file).code,
		'return {\n' +
			'  ...{\n' +
			'    md: medium,\n' +
			'    lg: large\n' +
			'  }[size],\n' +
			'  color: color\n' +
			'};',
	);
});

Deno.test('object construction fixpoint recrawls moved nested references', () => {
	const file = t.file(t.program([
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r0_1'),
			t.objectExpression([]),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			t.objectExpression([]),
		)]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('r1_1'), t.identifier('name')),
			t.identifier('name'),
		)),
		t.expressionStatement(t.callExpression(
			t.memberExpression(t.identifier('Object'), t.identifier('assign')),
			[t.identifier('r1_1'), t.identifier('source')],
		)),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(
				t.identifier('r0_1'),
				t.identifier('debugTrackedData'),
			),
			t.identifier('r1_1'),
		)),
		t.returnStatement(t.identifier('r0_1')),
	]));

	assert.equal(inlineObjectConstructionsToFixpoint(file), 2);
	assert.equal(
		generate(file).code,
		'return {\n' +
			'  debugTrackedData: {\n' +
			'    name: name,\n' +
			'    ...source\n' +
			'  }\n' +
			'};',
	);
});

Deno.test('recrawls a nested object moved past a captured copy alias', () => {
	const file = parse(`
		(function build(name, source) {
			const r0_1 = {};
			const r1_1 = {};
			r1_1.name = name;
			const r5_1 = r1_1;
			const r2_2 = HermesInternal.copyDataProperties(
				r5_1,
				source,
			);
			r0_1.debugTrackedData = r1_1;
			return r0_1;
		});
	`);

	assert.equal(inlineObjectConstructionsToFixpoint(file), 2);
	const transformed = generate(file).code;
	const build = new Function(
		'HermesInternal',
		`return ${transformed}`,
	)({
		copyDataProperties: Object.assign,
	});
	assert.deepEqual(
		build('tracked', { active: true }),
		{
			debugTrackedData: {
				name: 'tracked',
				active: true,
			},
		},
	);
});

Deno.test('folds named computed methods through ToPropertyKey temporaries', () => {
	const accumulator = t.objectExpression([]) as LiftedAST<t.ObjectExpression>;
	accumulator.extra = { instruction: 'NewObject' };
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(t.identifier('object'), accumulator),
		]) as LiftedAST<t.VariableDeclaration>,
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('key'),
				t.callExpression(t.v8IntrinsicIdentifier('ToPropertyKey'), [
					t.memberExpression(
						t.identifier('Symbol'),
						t.identifier('iterator'),
					),
				]),
			),
		]),
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('method'),
				t.functionExpression(
					null,
					[],
					t.blockStatement([
						t.returnStatement(t.identifier('iterator')),
					]),
				),
			),
		]),
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('setFunctionName'),
			),
			[
				t.identifier('method'),
				t.identifier('key'),
				t.numericLiteral(0),
			],
		)),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(
				t.identifier('object'),
				t.identifier('key'),
				true,
			),
			t.identifier('method'),
		)),
		t.returnStatement(t.identifier('object')),
	];
	const program = t.program(body);
	const file = t.file(program);

	assert.equal(inlineObjectConstructionsToFixpoint(file), 1);
	assert.equal(
		generate(program).code,
		'return {\n' +
			'  [Symbol.iterator]: %asNamedObjectMethod(function () {\n' +
			'    return iterator;\n' +
			'  })\n' +
			'};',
	);
});

Deno.test('folds residual named computed method object literals', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('method'),
				t.functionExpression(
					null,
					[],
					t.blockStatement([
						t.returnStatement(t.identifier('iterator')),
					]),
				),
			),
		]),
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('setFunctionName'),
			),
			[
				t.identifier('method'),
				t.callExpression(t.v8IntrinsicIdentifier('ToPropertyKey'), [
					t.memberExpression(
						t.identifier('Symbol'),
						t.identifier('iterator'),
					),
				]),
				t.numericLiteral(0),
			],
		)),
		t.variableDeclaration('var', [
			t.variableDeclarator(
				t.identifier('iter'),
				t.objectExpression([
					t.objectProperty(
						t.callExpression(
							t.v8IntrinsicIdentifier('ToPropertyKey'),
							[
								t.memberExpression(
									t.identifier('Symbol'),
									t.identifier('iterator'),
								),
							],
						),
						t.identifier('method'),
						true,
					),
				]),
			),
		]),
	];
	const program = t.program(body);
	const file = t.file(program);

	assert.equal(inlineObjectConstructionsToFixpoint(file), 1);
	assert.equal(
		generate(program).code,
		'var iter = {\n' +
			'  [Symbol.iterator]() {\n' +
			'    return iterator;\n' +
			'  }\n' +
			'};',
	);
});
