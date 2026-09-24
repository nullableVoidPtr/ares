import { strict as assert } from 'node:assert';
import generate from '@babel/generator';
import * as t from '@babel/types';
import { tagStorageLocation } from '../../ast/alias.ts';
import type { IRBlock } from '../../ast/mod.ts';
import type { IRFunction } from '../mod.ts';
import {
	capturePlainObjectProjectionSources,
	cleanupComposedObjectRestInBody,
	cleanupSequentialArrayDestructuring,
	cleanupSequentialObjectDestructuring,
	objectRestProtocolBindingNames,
	recordResidualObjectRestTelemetry,
	recoverGuardedObjectDestructuring,
	reduceNestedRecoveredDestructuring,
	reduceProtectedArrayDestructuring,
} from './destructuring.ts';

function environmentSlot(name: string, slot = 0) {
	return tagStorageLocation(t.identifier(name), {
		kind: 'environment-slot',
		environment: {
			functionId: 3,
			kind: 'CreateFunctionEnvironment',
			address: 10,
		},
		slot,
	});
}

function assign(name: string, value: t.Expression): t.Statement {
	return t.expressionStatement(t.assignmentExpression(
		'=',
		t.identifier(name),
		value,
	));
}

function getById(source: string, property: string): t.MemberExpression {
	const member = t.memberExpression(
		t.identifier(source),
		t.identifier(property),
	);
	member.extra = { instruction: 'GetById' };
	return member;
}

function singleBlockFunction(body: t.Statement[]): IRFunction {
	return {
		blocks: new Map([[0, { body } as unknown as IRBlock]]),
		recordBindingCleanupObservation() {},
	} as unknown as IRFunction;
}

function done(state: string): t.Expression {
	return t.binaryExpression(
		'===',
		t.identifier(state),
		t.identifier('undefined'),
	);
}

function intrinsicArrayDeclaration(
	name: 'IteratorBegin' | 'IteratorNext',
	ids: string[],
	args: t.Expression[],
): t.VariableDeclaration {
	return t.variableDeclaration('const', [t.variableDeclarator(
		t.arrayPattern(ids.map((id) => t.identifier(id))),
		t.callExpression(t.v8IntrinsicIdentifier(name), args),
	)]);
}

function intrinsicStatement(
	name: 'Catch' | 'IteratorClose',
	args: t.Expression[],
): t.ExpressionStatement {
	return t.expressionStatement(t.callExpression(
		t.v8IntrinsicIdentifier(name),
		args,
	));
}

function emptyObjectDestructuringThrow(
	source: string,
	message = "Cannot destructure 'undefined' or 'null'.",
): t.Statement[] {
	return [
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('throwTypeError'),
			),
			[t.identifier(source), t.stringLiteral(message)],
		)),
		t.throwStatement(t.identifier('undefined')),
	];
}

Deno.test('recovers an empty object destructuring guard', () => {
	const body: t.Statement[] = [
		t.ifStatement(
			t.binaryExpression(
				'!=',
				t.identifier('source'),
				t.nullLiteral(),
			),
			t.blockStatement([t.returnStatement(t.numericLiteral(1))]),
		),
		...emptyObjectDestructuringThrow('source'),
	];

	assert.equal(recoverGuardedObjectDestructuring(body, 7), true);
	assert.equal(generate(t.program(body)).code, 'var {} = source;\nreturn 1;');
	assert.equal(body[0].extra?.fromDestructuring, true);
});

Deno.test('recovers a forward empty object destructuring guard', () => {
	const body: t.Statement[] = [
		t.ifStatement(
			t.binaryExpression(
				'==',
				t.identifier('source'),
				t.nullLiteral(),
			),
			t.blockStatement(emptyObjectDestructuringThrow('source')),
		),
		t.expressionStatement(t.callExpression(t.identifier('use'), [
			t.identifier('source'),
		])),
	];

	assert.equal(recoverGuardedObjectDestructuring(body, 8), true);
	assert.equal(
		generate(t.program(body)).code,
		'var {} = source;\nuse(source);',
	);
});

Deno.test('recovers rest-only object destructuring after inlining', () => {
	const copy = t.objectExpression([
		t.spreadElement(t.identifier('source')),
	]);
	copy.extra = { copyDataPropertiesSpread: true };
	const body: t.Statement[] = [
		t.ifStatement(
			t.binaryExpression(
				'!=',
				t.identifier('source'),
				t.nullLiteral(),
			),
			t.blockStatement([
				t.returnStatement(
					t.callExpression(t.identifier('use'), [copy]),
				),
			]),
		),
		...emptyObjectDestructuringThrow('source'),
	];

	assert.equal(recoverGuardedObjectDestructuring(body, 9), true);
	const code = generate(t.program(body)).code;
	assert.match(code, /var \{\s*\.\.\._rest_9_source_\s*\} = source/);
	assert.match(code, /return use\(_rest_9_source_\)/);
	assert.doesNotMatch(code, /throwTypeError/);
});

Deno.test('preserves non-destructuring throwTypeError control flow', () => {
	const body: t.Statement[] = [
		t.ifStatement(
			t.binaryExpression(
				'!=',
				t.identifier('source'),
				t.nullLiteral(),
			),
			t.blockStatement([t.returnStatement(t.numericLiteral(1))]),
		),
		...emptyObjectDestructuringThrow('source', 'unrelated type error'),
	];
	const before = generate(t.program(body)).code;

	assert.equal(recoverGuardedObjectDestructuring(body, 10), false);
	assert.equal(generate(t.program(body)).code, before);
});

Deno.test('recovers three consequential plain GetById object projections', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('source'),
			t.callExpression(t.identifier('load'), []),
		)]),
		...['first', 'second', 'third'].map((property, index) =>
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier(`r${index}_1`),
				getById('source', property),
			)])
		),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('r1_1'),
			t.identifier('r2_1'),
		])),
	];

	assert.equal(
		cleanupSequentialObjectDestructuring(singleBlockFunction(body)),
		true,
	);
	const code = generate(t.program(body)).code;
	assert.match(code, /const \{[\s\S]*first: r0_1/);
	assert.match(code, /second: r1_1/);
	assert.match(code, /third: r2_1[\s\S]*\} = source/);
});

Deno.test('recovers a complete run of plain GetById assignments', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r0_1')),
			t.variableDeclarator(t.identifier('r1_1')),
			t.variableDeclarator(t.identifier('r2_1')),
		]),
		assign('r0_1', getById('source', 'first')),
		assign('r1_1', getById('source', 'second')),
		assign('r2_1', getById('source', 'third')),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('r1_1'),
			t.identifier('r2_1'),
		])),
	];

	assert.equal(
		cleanupSequentialObjectDestructuring(singleBlockFunction(body)),
		true,
	);
	assert.match(
		generate(t.program(body)).code,
		/\(\{[\s\S]*first: r0_1[\s\S]*third: r2_1[\s\S]*\} = source\)/,
	);
});

Deno.test(
	'carries GetById proof into mixed local and environment projection sinks',
	() => {
		const rawBody: t.Statement[] = [
			...['seenRequests', 'first', 'second', 'third'].map(
				(property, index) => {
					const declaration = t.variableDeclaration('const', [
						t.variableDeclarator(
							t.identifier(`r${index}_1`),
							t.memberExpression(
								t.identifier('r0_10'),
								t.identifier(property),
							),
						),
					]);
					declaration.extra = { instruction: 'GetById' };
					return declaration;
				},
			),
		];
		const func = singleBlockFunction(rawBody);
		func.plainObjectProjectionSources = new Set();
		assert.equal(capturePlainObjectProjectionSources(func), 1);
		assert.deepEqual([...func.plainObjectProjectionSources], ['r0_10']);

		const environmentSink = (slot: number) =>
			t.memberExpression(
				t.callExpression(
					t.v8IntrinsicIdentifier('expectEnvironment'),
					[t.identifier('r8_1')],
				),
				t.numericLiteral(slot),
				true,
			);
		const projection = (property: string) =>
			t.memberExpression(
				t.identifier('r0_10'),
				t.identifier(property),
			);
		const body: t.Statement[] = [
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r10_1'),
				projection('seenRequests'),
			)]),
			...['first', 'second', 'third'].map((property, index) =>
				t.expressionStatement(t.assignmentExpression(
					'=',
					environmentSink(index + 1),
					projection(property),
				))
			),
			t.returnStatement(t.identifier('r10_1')),
		];
		const block = func.blocks.get(0)!;
		block.body = body;

		assert.equal(cleanupSequentialObjectDestructuring(func), true);
		const code = generate(t.program(body)).code;
		assert.match(code, /let r10_1/);
		assert.match(code, /seenRequests: r10_1/);
		assert.match(code, /first: %expectEnvironment\(r8_1\)\[1\]/);
		assert.match(code, /third: %expectEnvironment\(r8_1\)\[3\]/);
	},
);

Deno.test('plain GetById recovery requires more than two assignments', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r0_1'),
			getById('source', 'first'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			getById('source', 'second'),
		)]),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('r1_1'),
		])),
	];

	assert.equal(
		cleanupSequentialObjectDestructuring(singleBlockFunction(body)),
		false,
	);
});

Deno.test('plain GetById recovery requires complete source references', () => {
	const body: t.Statement[] = [
		...['first', 'second', 'third'].map((property, index) =>
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier(`r${index}_1`),
				getById('source', property),
			)])
		),
		t.expressionStatement(t.callExpression(t.identifier('observe'), [
			t.identifier('source'),
		])),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('r1_1'),
			t.identifier('r2_1'),
		])),
	];

	assert.equal(
		cleanupSequentialObjectDestructuring(singleBlockFunction(body)),
		false,
	);
});

Deno.test('plain GetById recovery requires consequential targets', () => {
	const body: t.Statement[] = [
		...['first', 'second', 'third'].map((property, index) =>
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier(`r${index}_1`),
				getById('source', property),
			)])
		),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('r1_1'),
		])),
	];

	assert.equal(
		cleanupSequentialObjectDestructuring(singleBlockFunction(body)),
		false,
	);
});

Deno.test('plain GetById recovery tolerates branch-local generated bindings', () => {
	const body: t.Statement[] = [
		...['first', 'second', 'third'].map((property, index) =>
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier(`r${index}_1`),
				getById('source', property),
			)])
		),
		t.switchStatement(t.identifier('tag'), [
			t.switchCase(t.identifier('left'), [
				t.blockStatement([
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('r37_16'),
						t.memberExpression(
							t.identifier('node'),
							t.identifier('callback'),
						),
					)]),
				]),
			]),
			t.switchCase(t.identifier('right'), [
				t.blockStatement([
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('r37_16'),
						t.memberExpression(
							t.identifier('node'),
							t.identifier('callback'),
						),
					)]),
				]),
			]),
		]),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('r1_1'),
			t.identifier('r2_1'),
		])),
	];

	assert.equal(
		cleanupSequentialObjectDestructuring(singleBlockFunction(body)),
		true,
	);
	assert.match(generate(t.program(body)).code, /const \{[\s\S]*third: r2_1/);
});

Deno.test('plain GetById recovery excludes parameter-derived sources', () => {
	const body: t.Statement[] = [
		...['first', 'second', 'third'].map((property, index) =>
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier(`r${index}_1`),
				getById('_param_9_0_', property),
			)])
		),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('r1_1'),
			t.identifier('r2_1'),
		])),
	];

	assert.equal(
		cleanupSequentialObjectDestructuring(singleBlockFunction(body)),
		false,
	);
});

Deno.test('plain object projection recovery requires GetById provenance', () => {
	const body: t.Statement[] = [
		...['first', 'second', 'third'].map((property, index) =>
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier(`r${index}_1`),
				t.memberExpression(
					t.identifier('source'),
					t.identifier(property),
				),
			)])
		),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('r1_1'),
			t.identifier('r2_1'),
		])),
	];

	assert.equal(
		cleanupSequentialObjectDestructuring(singleBlockFunction(body)),
		false,
	);
});

Deno.test('plain GetById recovery does not cross an intervening effect', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r0_1'),
			getById('source', 'first'),
		)]),
		t.expressionStatement(t.callExpression(t.identifier('observe'), [])),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			getById('source', 'second'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r2_1'),
			getById('source', 'third'),
		)]),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('r1_1'),
			t.identifier('r2_1'),
		])),
	];

	assert.equal(
		cleanupSequentialObjectDestructuring(singleBlockFunction(body)),
		false,
	);
});

Deno.test('CFG reducer recovers an arbitrary number of protected array elements', () => {
	const block = (
		body: t.Statement[],
		consequentAddresses: number[],
		branch?: t.Expression,
	) => ({ body, consequentAddresses, branch }) as unknown as IRBlock;
	const phi = (name: string, ...values: t.Expression[]) =>
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier(name),
			t.callExpression(t.v8IntrinsicIdentifier('Phi'), values),
		)]);
	const target = (name: string, value: string) =>
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier(name),
			t.identifier(value),
		));
	const blocks = new Map<number, IRBlock>([
		[
			0,
			block([
				intrinsicArrayDeclaration('IteratorBegin', ['r1_1', 'r1_2'], [
					t.identifier('input'),
				]),
				intrinsicArrayDeclaration('IteratorNext', ['r2_1', 'r2_2'], [
					t.identifier('r1_1'),
					t.identifier('r1_2'),
				]),
				phi('r3_1', t.identifier('r2_1'), t.numericLiteral(1)),
			], [10]),
		],
		[10, block([target('a', 'r3_1')], [20])],
		[
			20,
			block([
				intrinsicArrayDeclaration('IteratorNext', ['r4_1', 'r4_2'], [
					t.identifier('r2_2'),
					t.identifier('r1_2'),
				]),
				phi('r5_1', t.identifier('r4_1'), t.stringLiteral('two')),
			], [30]),
		],
		[30, block([target('b', 'r5_1')], [40])],
		[
			40,
			block([
				intrinsicArrayDeclaration('IteratorNext', ['r6_1', 'r6_2'], [
					t.identifier('r4_2'),
					t.identifier('r1_2'),
				]),
				phi('r7_1', t.identifier('r6_1'), t.booleanLiteral(true)),
			], [50]),
		],
		[50, block([target('c', 'r7_1')], [60])],
		[60, block([], [70, 80], t.identifier('r6_2'))],
		[
			70,
			block([
				intrinsicStatement('IteratorClose', [
					t.identifier('r6_2'),
					t.booleanLiteral(false),
				]),
			], [80]),
		],
		[
			80,
			block([t.returnStatement(t.arrayExpression([
				t.identifier('a'),
				t.identifier('b'),
				t.identifier('c'),
			]))], []),
		],
		...[100, 110, 120].map((address, index) =>
			[
				address,
				block([
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier(`r8_${index + 1}`),
						t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
					)]),
				], [130]),
			] as [number, IRBlock]
		),
		[
			130,
			block(
				[
					phi(
						'r9_1',
						t.identifier('r8_1'),
						t.identifier('r8_2'),
						t.identifier('r8_3'),
					),
				],
				[140, 150],
				t.identifier('r6_2'),
			),
		],
		[
			140,
			block([
				intrinsicStatement('IteratorClose', [
					t.identifier('r6_2'),
					t.booleanLiteral(true),
				]),
			], [150]),
		],
		[150, block([t.throwStatement(t.identifier('r9_1'))], [])],
	]);
	const protectedByHandler = new Map([
		[100, new Set([10])],
		[110, new Set([30])],
		[120, new Set([50])],
	]);
	let predecessors = new Map<number, Set<number>>();
	const rebuildPredecessors = () => {
		predecessors = new Map();
		for (const [address, current] of blocks) {
			for (const successor of current.consequentAddresses) {
				const incoming = predecessors.get(successor) ?? new Set();
				incoming.add(address);
				predecessors.set(successor, incoming);
			}
		}
		for (const [handler, protectedBlocks] of protectedByHandler) {
			for (const address of protectedBlocks) {
				const incoming = predecessors.get(handler) ?? new Set();
				incoming.add(address);
				predecessors.set(handler, incoming);
			}
		}
	};
	rebuildPredecessors();
	const records = new Map(
		[...protectedByHandler].map(([address, protectedBlocks]) => [
			address,
			{ protectedBlocks },
		]),
	);
	const func = {
		blocks,
		exceptions: {
			records,
			removeHandlers(addresses: Iterable<number>) {
				for (const address of addresses) {
					records.delete(address);
					protectedByHandler.delete(address);
				}
				rebuildPredecessors();
			},
		},
		predecessorsOf(address: number) {
			return predecessors.get(address) ?? new Set<number>();
		},
		setSuccessors(address: number, successors: number[]) {
			blocks.get(address)!.consequentAddresses = successors;
			rebuildPredecessors();
		},
		markMergedBlocks(_parent: number, child: number) {
			blocks.delete(child);
			rebuildPredecessors();
		},
	} as unknown as IRFunction;

	assert.equal(reduceProtectedArrayDestructuring(func), true);
	assert.deepEqual([...blocks.keys()], [0, 80]);
	assert.equal(
		generate(t.program(blocks.get(0)!.body as t.Statement[])).code,
		'var [a = 1, b = "two", c = true] = input;',
	);
});

Deno.test('CFG reducer recovers protected parameter array property leaves', () => {
	const block = (
		body: t.Statement[],
		consequentAddresses: number[],
		branch?: t.Expression,
	) => ({ body, consequentAddresses, branch }) as unknown as IRBlock;
	const phi = (name: string, ...values: t.Expression[]) =>
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier(name),
			t.callExpression(t.v8IntrinsicIdentifier('Phi'), values),
		)]);
	const blocks = new Map<number, IRBlock>([
		[
			0,
			block(
				[
					intrinsicArrayDeclaration(
						'IteratorBegin',
						['r1_1', 'r6_2'],
						[
							t.identifier('input'),
						],
					),
					intrinsicArrayDeclaration(
						'IteratorNext',
						['r7_1', 'r1_2'],
						[
							t.identifier('r1_1'),
							t.identifier('r6_2'),
						],
					),
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('r5_1'),
						t.identifier('undefined'),
					)]),
				],
				[10, 20],
				t.identifier('firstDone'),
			),
		],
		[
			10,
			block([
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r5_2'),
					t.identifier('r7_1'),
				)]),
			], [20]),
		],
		[
			20,
			block(
				[
					phi('r5_3', t.identifier('r5_1'), t.identifier('r5_2')),
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('r3_1'),
						t.identifier('r5_3'),
					)]),
				],
				[30, 40],
				t.identifier('firstDone'),
			),
		],
		[
			30,
			block(
				[
					intrinsicArrayDeclaration(
						'IteratorNext',
						['r6_3', 'r1_3'],
						[
							t.identifier('r1_2'),
							t.identifier('r6_2'),
						],
					),
				],
				[35, 40],
				t.identifier('secondDone'),
			),
		],
		[
			35,
			block([
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r5_5'),
					t.identifier('r6_3'),
				)]),
			], [40]),
		],
		[
			40,
			block([
				phi(
					'r5_6',
					t.identifier('r5_1'),
					t.identifier('r5_1'),
					t.identifier('r5_5'),
				),
				phi(
					'r2_4',
					t.identifier('firstDone'),
					t.identifier('secondDone'),
				),
				phi('r1_4', t.identifier('r1_2'), t.identifier('r1_3')),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r4_1'),
					t.memberExpression(
						t.identifier('r5_6'),
						t.identifier('time'),
					),
				)]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.memberExpression(
						t.callExpression(
							t.v8IntrinsicIdentifier('expectEnvironment'),
							[t.identifier('env')],
						),
						t.numericLiteral(0),
						true,
					),
					t.identifier('r3_1'),
				)),
			], [50]),
		],
		[50, block([], [55, 60], t.identifier('r2_4'))],
		[
			55,
			block([
				intrinsicStatement('IteratorClose', [
					t.identifier('r1_4'),
					t.booleanLiteral(false),
				]),
			], [60]),
		],
		[
			60,
			block(
				[t.returnStatement(t.identifier('r4_1'))],
				[],
				t.identifier('r3_1'),
			),
		],
		[
			100,
			block([
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
			], [110]),
		],
		[
			110,
			block(
				[
					phi('r0_2', t.identifier('r0_1')),
				],
				[120, 130],
				t.identifier('r2_4'),
			),
		],
		[
			120,
			block([
				intrinsicStatement('IteratorClose', [
					t.identifier('r1_4'),
					t.booleanLiteral(true),
				]),
			], [130]),
		],
		[130, block([t.throwStatement(t.identifier('r0_2'))], [])],
	]);
	const protectedByHandler = new Map([[100, new Set([40])]]);
	let predecessors = new Map<number, Set<number>>();
	const rebuildPredecessors = () => {
		predecessors = new Map();
		for (const [address, current] of blocks) {
			for (const successor of current.consequentAddresses) {
				const incoming = predecessors.get(successor) ?? new Set();
				incoming.add(address);
				predecessors.set(successor, incoming);
			}
		}
		for (const [handler, protectedBlocks] of protectedByHandler) {
			for (const address of protectedBlocks) {
				const incoming = predecessors.get(handler) ?? new Set();
				incoming.add(address);
				predecessors.set(handler, incoming);
			}
		}
	};
	rebuildPredecessors();
	const records = new Map([[100, { protectedBlocks: new Set([40]) }]]);
	const func = {
		id: 7,
		blocks,
		exceptions: {
			records,
			removeHandlers(addresses: Iterable<number>) {
				for (const address of addresses) {
					records.delete(address);
					protectedByHandler.delete(address);
				}
				rebuildPredecessors();
			},
		},
		predecessorsOf(address: number) {
			return predecessors.get(address) ?? new Set<number>();
		},
		setSuccessors(address: number, successors: number[]) {
			blocks.get(address)!.consequentAddresses = successors;
			rebuildPredecessors();
		},
		markMergedBlocks(_parent: number, child: number) {
			blocks.delete(child);
			rebuildPredecessors();
		},
	} as unknown as IRFunction;

	assert.equal(reduceProtectedArrayDestructuring(func), true);
	assert.deepEqual([...blocks.keys()], [0, 60]);
	const code = generate(t.program(blocks.get(0)!.body as t.Statement[])).code;
	assert.match(code, /let r4_1;/);
	assert.match(
		code,
		/\[%expectEnvironment\(env\)\[0\], \{\s*time: r4_1\s*\}\] = input/,
	);
	const continuation = generate(t.program(
		blocks.get(60)!.body as t.Statement[],
	)).code;
	assert.doesNotMatch(continuation, /r3_1/);
	const continuationBranch = generate(
		blocks.get(60)!.branch as t.Expression,
	).code;
	assert.match(continuationBranch, /%expectEnvironment\(env\)\[0\]/);
	assert.doesNotMatch(continuationBranch, /r3_1/);
});

Deno.test('recovers an elided terminal array parameter protocol', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('value')),
			t.variableDeclarator(t.identifier('state')),
			t.variableDeclarator(t.identifier('isDone')),
		]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([
				t.identifier('iterator'),
				t.identifier('record'),
			]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorBegin'), [
				t.identifier('input'),
			]),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([
				t.identifier('first'),
				t.identifier('firstState'),
			]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
				t.identifier('iterator'),
				t.identifier('record'),
			]),
		)]),
		t.ifStatement(
			done('firstState'),
			t.blockStatement([
				assign('isDone', done('firstState')),
				assign('value', t.identifier('undefined')),
				assign('state', t.identifier('firstState')),
			]),
			t.blockStatement([
				t.variableDeclaration('const', [t.variableDeclarator(
					t.arrayPattern([
						t.identifier('second'),
						t.identifier('secondState'),
					]),
					t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
						t.identifier('firstState'),
						t.identifier('record'),
					]),
				)]),
				t.ifStatement(
					done('secondState'),
					t.blockStatement([
						assign('isDone', done('secondState')),
						assign('value', t.identifier('undefined')),
						assign('state', t.identifier('secondState')),
					]),
					t.blockStatement([
						assign('isDone', done('secondState')),
						assign('value', t.identifier('second')),
						assign('state', t.identifier('secondState')),
					]),
				),
			]),
		),
		t.ifStatement(
			t.unaryExpression('!', t.identifier('isDone')),
			t.blockStatement([t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('IteratorClose'),
				[t.identifier('state'), t.booleanLiteral(false)],
			))]),
		),
		t.returnStatement(t.identifier('value')),
	];
	const block = { body } as unknown as IRBlock;
	const func = { blocks: new Map([[0, block]]) } as unknown as IRFunction;

	assert.equal(cleanupSequentialArrayDestructuring(func, block, body), true);
	assert.equal(
		generate(t.program(body)).code,
		'var [, value] = input;\nreturn value;',
	);
});

Deno.test('recovers a two-slot carried array parameter protocol', () => {
	const terminal = () =>
		t.returnStatement(t.arrayExpression([
			t.identifier('firstValue'),
			t.identifier('secondValue'),
		]));
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('isDone')),
			t.variableDeclarator(t.identifier('state')),
			t.variableDeclarator(t.identifier('firstValue')),
			t.variableDeclarator(t.identifier('secondValue')),
		]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([
				t.identifier('iterator'),
				t.identifier('record'),
			]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorBegin'), [
				t.identifier('input'),
			]),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([
				t.identifier('first'),
				t.identifier('firstState'),
			]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
				t.identifier('iterator'),
				t.identifier('record'),
			]),
		)]),
		t.ifStatement(
			done('firstState'),
			t.blockStatement([
				assign('firstValue', t.identifier('undefined')),
			]),
			t.blockStatement([
				assign('firstValue', t.identifier('first')),
			]),
		),
		t.ifStatement(
			done('firstState'),
			t.blockStatement([
				assign('secondValue', t.identifier('undefined')),
				assign('isDone', done('firstState')),
				assign('state', t.identifier('firstState')),
			]),
			t.blockStatement([
				t.variableDeclaration('const', [t.variableDeclarator(
					t.arrayPattern([
						t.identifier('second'),
						t.identifier('secondState'),
					]),
					t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
						t.identifier('firstState'),
						t.identifier('record'),
					]),
				)]),
				t.ifStatement(
					done('secondState'),
					t.blockStatement([
						assign('secondValue', t.identifier('undefined')),
						assign('isDone', done('secondState')),
						assign('state', t.identifier('secondState')),
					]),
					t.blockStatement([
						assign('secondValue', t.identifier('second')),
						assign('isDone', done('secondState')),
						assign('state', t.identifier('secondState')),
					]),
				),
			]),
		),
		t.ifStatement(
			t.unaryExpression('!', t.identifier('isDone')),
			t.blockStatement([t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('IteratorClose'),
				[t.identifier('state'), t.booleanLiteral(false)],
			))]),
		),
		terminal(),
	];
	const block = { body } as unknown as IRBlock;
	const func = { blocks: new Map([[0, block]]) } as unknown as IRFunction;

	assert.equal(cleanupSequentialArrayDestructuring(func, block, body), true);
	assert.equal(
		generate(t.program(body)).code,
		'var [firstValue, secondValue] = input;\nreturn [firstValue, secondValue];',
	);
});

Deno.test('recovers carried array destructuring before non-terminal continuation', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('isDone')),
			t.variableDeclarator(t.identifier('state')),
			t.variableDeclarator(t.identifier('firstValue')),
			t.variableDeclarator(t.identifier('secondValue')),
		]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('env'),
			t.callExpression(
				t.v8IntrinsicIdentifier('CreateFunctionEnvironment'),
				[],
			),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([
				t.identifier('iterator'),
				t.identifier('record'),
			]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorBegin'), [
				t.identifier('input'),
			]),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([
				t.identifier('first'),
				t.identifier('firstState'),
			]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
				t.identifier('iterator'),
				t.identifier('record'),
			]),
		)]),
		t.ifStatement(
			done('firstState'),
			t.blockStatement([
				assign('firstValue', t.identifier('undefined')),
			]),
			t.blockStatement([
				assign('firstValue', t.identifier('first')),
			]),
		),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(
				t.callExpression(t.v8IntrinsicIdentifier('expectEnvironment'), [
					t.identifier('env'),
				]),
				t.numericLiteral(0),
				true,
			),
			t.identifier('firstValue'),
		)),
		t.ifStatement(
			done('firstState'),
			t.blockStatement([
				assign('isDone', done('firstState')),
				assign('secondValue', t.identifier('undefined')),
				assign('state', t.identifier('firstState')),
			]),
			t.blockStatement([
				t.variableDeclaration('const', [t.variableDeclarator(
					t.arrayPattern([
						t.identifier('second'),
						t.identifier('secondState'),
					]),
					t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
						t.identifier('firstState'),
						t.identifier('record'),
					]),
				)]),
				t.ifStatement(
					done('secondState'),
					t.blockStatement([
						assign('isDone', done('secondState')),
						assign('secondValue', t.identifier('undefined')),
						assign('state', t.identifier('secondState')),
					]),
					t.blockStatement([
						assign('isDone', done('secondState')),
						assign('secondValue', t.identifier('second')),
						assign('state', t.identifier('secondState')),
					]),
				),
			]),
		),
		t.ifStatement(
			t.unaryExpression('!', t.identifier('isDone')),
			t.blockStatement([t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('IteratorClose'),
				[t.identifier('state'), t.booleanLiteral(false)],
			))]),
		),
		t.ifStatement(
			t.binaryExpression(
				'!==',
				t.identifier('firstValue'),
				t.stringLiteral('_errors'),
			),
			t.blockStatement([t.returnStatement(t.identifier('secondValue'))]),
		),
	];
	const block = { body } as unknown as IRBlock;
	const func = { blocks: new Map([[0, block]]) } as unknown as IRFunction;

	assert.equal(cleanupSequentialArrayDestructuring(func, block, body), true);
	assert.equal(
		generate(t.program(body)).code,
		'var [firstValue, secondValue] = input;\n' +
			'const env = %CreateFunctionEnvironment();\n' +
			'%expectEnvironment(env)[0] = firstValue;\n' +
			'if (firstValue !== "_errors") {\n' +
			'  return secondValue;\n' +
			'}',
	);
});

Deno.test('recovers a leading elision with Phi-carried register spellings', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([t.identifier('r1_1'), t.identifier('r6_2')]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorBegin'), [
				t.identifier('input'),
			]),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([t.identifier('r7_1'), t.identifier('r1_2')]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
				t.identifier('r1_1'),
				t.identifier('r6_2'),
			]),
		)]),
		t.ifStatement(
			t.unaryExpression('!', done('r1_2')),
			t.blockStatement([]),
		),
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r3_6')),
			t.variableDeclarator(t.identifier('r2_4')),
			t.variableDeclarator(t.identifier('r1_4')),
		]),
		assign('r3_6', t.identifier('undefined')),
		assign('r2_4', done('r1_2')),
		assign('r1_4', t.identifier('r1_2')),
		t.ifStatement(
			t.unaryExpression('!', done('r1_2')),
			t.blockStatement([
				t.variableDeclaration('const', [t.variableDeclarator(
					t.arrayPattern([
						t.identifier('r7_3'),
						t.identifier('r1_3'),
					]),
					t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
						t.identifier('r1_2'),
						t.identifier('r6_2'),
					]),
				)]),
				assign('r3_6', t.identifier('r3_4')),
				assign('r2_4', done('r1_3')),
				assign('r1_4', t.identifier('r1_3')),
				t.ifStatement(
					t.unaryExpression('!', done('r1_3')),
					t.blockStatement([
						assign('r3_6', t.identifier('r7_3')),
						assign('r2_4', t.identifier('r2_3')),
						assign('r1_4', t.identifier('r1_3')),
					]),
				),
			]),
		),
		t.ifStatement(
			t.unaryExpression('!', t.identifier('r2_4')),
			t.blockStatement([t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('IteratorClose'),
				[t.identifier('r1_4'), t.booleanLiteral(false)],
			))]),
		),
		t.returnStatement(t.identifier('r3_6')),
	];
	const block = { body } as unknown as IRBlock;
	const func = { blocks: new Map([[0, block]]) } as unknown as IRFunction;

	assert.equal(cleanupSequentialArrayDestructuring(func, block, body), true);
	assert.equal(
		generate(t.program(body)).code,
		'var [, r3_6] = input;\nreturn r3_6;',
	);
});

Deno.test('recovers a single terminal array parameter protocol', () => {
	const terminal = () =>
		t.returnStatement(t.binaryExpression(
			'===',
			t.identifier('value'),
			t.identifier('expected'),
		));
	const body: t.Statement[] = [
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('value')),
		]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([
				t.identifier('iterator'),
				t.identifier('record'),
			]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorBegin'), [
				t.identifier('input'),
			]),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern([
				t.identifier('first'),
				t.identifier('state'),
			]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
				t.identifier('iterator'),
				t.identifier('record'),
			]),
		)]),
		t.ifStatement(
			done('state'),
			t.blockStatement([
				assign('value', t.identifier('undefined')),
			]),
			t.blockStatement([
				assign('value', t.identifier('first')),
			]),
		),
		t.ifStatement(
			t.unaryExpression('!', done('state')),
			t.blockStatement([
				t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('IteratorClose'),
					[t.identifier('state'), t.booleanLiteral(false)],
				)),
				terminal(),
			]),
		),
		terminal(),
	];
	const block = { body } as unknown as IRBlock;
	const func = { blocks: new Map([[0, block]]) } as unknown as IRFunction;

	assert.equal(cleanupSequentialArrayDestructuring(func, block, body), true);
	assert.equal(
		generate(t.program(body)).code,
		'var [value] = input;\nreturn value === expected;',
	);
});

Deno.test('closed object rest preserves support values used by its branch', () => {
	const copyDataProperties = (
		target: t.Expression,
		source: t.Expression,
		excluded?: t.Expression,
	) => t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		excluded ? [target, source, excluded] : [target, source],
	);
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r2_1'),
			t.identifier('input'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r3_1'),
			t.memberExpression(t.identifier('r2_1'), t.identifier('sku_id')),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r0_1'),
			t.nullLiteral(),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			t.callExpression(
				t.memberExpression(
					t.identifier('Object'),
					t.identifier('create'),
				),
				[t.identifier('r0_1')],
			),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r0_2'),
			t.numericLiteral(0),
		)]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('r1_1'), t.identifier('sku_id')),
			t.identifier('r0_2'),
		)),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r6_1'),
			t.objectExpression([]),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r5_1'),
			t.identifier('r2_1'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r4_1'),
			t.identifier('r1_1'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r5_2'),
			copyDataProperties(
				t.identifier('r6_1'),
				t.identifier('r5_1'),
				t.identifier('r4_1'),
			),
		)]),
		t.returnStatement(t.arrayExpression([
			t.identifier('r3_1'),
			t.identifier('r5_2'),
		])),
	];
	const block = {
		address: 0,
		body,
		branch: t.binaryExpression(
			'===',
			t.identifier('r0_1'),
			t.identifier('r0_2'),
		),
	} as unknown as IRBlock;
	const func = {
		blocks: new Map([[0, block]]),
		recordBindingCleanupObservation() {},
	} as unknown as IRFunction;

	assert.equal(cleanupSequentialObjectDestructuring(func), true);
	assert.equal(
		generate(t.program(body)).code,
		'const {\n' +
			'  sku_id: r3_1,\n' +
			'  ...r5_2\n' +
			'} = input;\n' +
			'const r0_1 = null;\n' +
			'const r0_2 = 0;\n' +
			'return [r3_1, r5_2];',
	);
});

Deno.test('recovers object rest with Phi defaults and a literal exclusion map', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			t.memberExpression(t.identifier('input'), t.identifier('style')),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r2_1'),
			t.memberExpression(t.identifier('input'), t.identifier('color')),
		)]),
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r2_3')),
		]),
		assign('r2_3', t.identifier('r2_1')),
		t.ifStatement(
			t.binaryExpression(
				'===',
				t.identifier('r2_1'),
				t.identifier('undefined'),
			),
			t.blockStatement([
				assign(
					'r2_3',
					t.callExpression(t.identifier('defaultColor'), []),
				),
			]),
		),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r3_1'),
			t.objectExpression([
				t.objectProperty(t.identifier('style'), t.numericLiteral(0)),
				t.objectProperty(t.identifier('color'), t.numericLiteral(0)),
			]),
		)]),
		t.expressionStatement(t.callExpression(
			t.memberExpression(
				t.identifier('HermesInternal'),
				t.identifier('silentSetPrototypeOf'),
			),
			[t.identifier('r3_1'), t.nullLiteral()],
		)),
		// Register inlining can substitute this helper target into the call while
		// leaving its dead declaration for the next cleanup iteration.
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r5_1'),
			t.objectExpression([]),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r4_1'),
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('copyDataProperties'),
				),
				[
					t.objectExpression([]),
					t.identifier('input'),
					t.identifier('r3_1'),
				],
			),
		)]),
		t.returnStatement(t.arrayExpression([
			t.identifier('r1_1'),
			// Recursive materialisation can retain the pre-Phi SSA version here.
			t.identifier('r2_1'),
			t.identifier('r4_1'),
		])),
	];
	const block = { body } as unknown as IRBlock;
	const func = {
		blocks: new Map([[0, block]]),
		recordBindingCleanupObservation() {},
	} as unknown as IRFunction;

	assert.equal(cleanupSequentialObjectDestructuring(func), true);
	assert.equal(
		generate(t.program(body)).code,
		'const {\n' +
			'  style: r1_1,\n' +
			'  color: r2_3 = defaultColor(),\n' +
			'  ...r4_1\n' +
			'} = input;\nreturn [r1_1, r2_3, r4_1];',
	);
});

Deno.test('uses an immutable environment slot as a composed object-rest binding', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r0_1'),
			t.memberExpression(t.identifier('input'), t.identifier('onPress')),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			environmentSlot('_env_3_0'),
			t.identifier('r0_1'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r5_1'),
			t.memberExpression(t.identifier('input'), t.identifier('loading')),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r2_1'),
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
			t.memberExpression(t.identifier('r2_1'), t.identifier('onPress')),
			t.numericLiteral(0),
		)),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('r2_1'), t.identifier('loading')),
			t.numericLiteral(0),
		)),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r8_1'),
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('copyDataProperties'),
				),
				[
					t.objectExpression([]),
					t.identifier('input'),
					t.identifier('r2_1'),
				],
			),
		)]),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('_env_3_0'),
			t.identifier('r5_1'),
			t.identifier('r8_1'),
		])),
	];
	assert.equal(cleanupComposedObjectRestInBody(body), 1);
	assert.equal(
		generate(t.program(body)).code,
		'const {\n' +
			'  onPress: _env_3_0,\n' +
			'  loading: r5_1,\n' +
			'  ...r8_1\n' +
			'} = input;\n' +
			'return [_env_3_0, _env_3_0, r5_1, r8_1];',
	);
});

Deno.test('keeps a pre-materialized environment store after object-rest recovery', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('env'),
			t.callExpression(
				t.v8IntrinsicIdentifier('CreateFunctionEnvironment'),
				[t.numericLiteral(1)],
			),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r0_1'),
			t.memberExpression(t.identifier('input'), t.identifier('onChange')),
		)]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(
				t.callExpression(t.v8IntrinsicIdentifier('expectEnvironment'), [
					t.identifier('env'),
				]),
				t.numericLiteral(0),
				true,
			),
			t.identifier('r0_1'),
		)),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r5_1'),
			t.memberExpression(t.identifier('input'), t.identifier('style')),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r8_1'),
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('copyDataProperties'),
				),
				[
					t.objectExpression([]),
					t.identifier('input'),
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
									t.stringLiteral('onChange'),
									t.numericLiteral(0),
								),
								t.objectProperty(
									t.stringLiteral('style'),
									t.numericLiteral(0),
								),
							]),
						],
					),
				],
			),
		)]),
		t.returnStatement(t.arrayExpression([
			t.identifier('r0_1'),
			t.identifier('r5_1'),
			t.identifier('r8_1'),
		])),
	];

	assert.equal(cleanupComposedObjectRestInBody(body), 1);
	assert.equal(
		generate(t.program(body)).code,
		'const env = %CreateFunctionEnvironment(1);\n' +
			'const {\n' +
			'  onChange: r0_1,\n' +
			'  style: r5_1,\n' +
			'  ...r8_1\n' +
			'} = input;\n' +
			'%expectEnvironment(env)[0] = r0_1;\n' +
			'return [r0_1, r5_1, r8_1];',
	);
});

Deno.test('recovers an embedded object-rest spread with direct member uses', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r6_1'),
			t.memberExpression(t.identifier('input'), t.identifier('color')),
		)]),
		t.returnStatement(t.callExpression(t.identifier('render'), [
			t.objectExpression([
				t.objectProperty(
					t.identifier('color'),
					t.conditionalExpression(
						t.binaryExpression(
							'!==',
							t.identifier('r6_1'),
							t.identifier('undefined'),
						),
						t.identifier('r6_1'),
						t.stringLiteral('default'),
					),
				),
				t.spreadElement(t.callExpression(
					t.memberExpression(
						t.identifier('HermesInternal'),
						t.identifier('copyDataProperties'),
					),
					[
						t.objectExpression([]),
						t.identifier('input'),
						t.objectExpression([
							t.objectProperty(
								t.identifier('__proto__'),
								t.nullLiteral(),
							),
							t.objectProperty(
								t.identifier('children'),
								t.numericLiteral(0),
							),
							t.objectProperty(
								t.identifier('color'),
								t.numericLiteral(0),
							),
						]),
					],
				)),
				t.objectProperty(
					t.identifier('children'),
					t.memberExpression(
						t.identifier('input'),
						t.identifier('children'),
					),
				),
			]),
		])),
	];

	assert.equal(cleanupComposedObjectRestInBody(body), 1);
	assert.equal(
		generate(t.program(body)).code,
		'const {\n' +
			'  children: _children,\n' +
			'  color: r6_1,\n' +
			'  ..._rest\n' +
			'} = input;\n' +
			'return render({\n' +
			'  color: r6_1 !== undefined ? r6_1 : "default",\n' +
			'  ..._rest,\n' +
			'  children: _children\n' +
			'});',
	);
});

Deno.test('carries a composed default into an environment-slot binding', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			t.memberExpression(t.identifier('input'), t.identifier('label')),
		)]),
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r1_3')),
		]),
		assign('r1_3', t.identifier('r1_1')),
		t.ifStatement(
			t.binaryExpression(
				'===',
				t.identifier('r1_1'),
				t.identifier('undefined'),
			),
			t.blockStatement([
				assign(
					'r1_3',
					t.callExpression(t.identifier('defaultLabel'), []),
				),
			]),
		),
		t.variableDeclaration('const', [t.variableDeclarator(
			environmentSlot('_env_3_0'),
			t.identifier('r1_3'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r4_1'),
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('copyDataProperties'),
				),
				[
					t.objectExpression([]),
					t.identifier('input'),
					t.objectExpression([
						t.objectProperty(
							t.identifier('__proto__'),
							t.nullLiteral(),
						),
						t.objectProperty(
							t.identifier('label'),
							t.numericLiteral(0),
						),
					]),
				],
			),
		)]),
		t.returnStatement(t.arrayExpression([
			t.identifier('r1_3'),
			t.identifier('_env_3_0'),
			t.identifier('r4_1'),
		])),
	];

	assert.equal(cleanupComposedObjectRestInBody(body), 1);
	assert.equal(
		generate(t.program(body)).code,
		'const {\n' +
			'  label: _env_3_0 = defaultLabel(),\n' +
			'  ...r4_1\n' +
			'} = input;\n' +
			'return [_env_3_0, _env_3_0, r4_1];',
	);
});

Deno.test('carries a conditional alias default into an environment-slot binding', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			t.memberExpression(t.identifier('input'), t.identifier('label')),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_2'),
			t.identifier('r1_1'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			environmentSlot('_env_3_0'),
			t.conditionalExpression(
				t.binaryExpression(
					'===',
					t.identifier('r1_2'),
					t.identifier('undefined'),
				),
				t.callExpression(t.identifier('defaultLabel'), []),
				t.identifier('r1_2'),
			),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r4_1'),
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('copyDataProperties'),
				),
				[
					t.objectExpression([]),
					t.identifier('input'),
					t.objectExpression([
						t.objectProperty(
							t.identifier('__proto__'),
							t.nullLiteral(),
						),
						t.objectProperty(
							t.identifier('label'),
							t.numericLiteral(0),
						),
					]),
				],
			),
		)]),
		t.returnStatement(t.arrayExpression([
			t.identifier('_env_3_0'),
			t.identifier('r4_1'),
		])),
	];

	assert.equal(cleanupComposedObjectRestInBody(body), 1);
	assert.equal(
		generate(t.program(body)).code,
		'const {\n' +
			'  label: _env_3_0 = defaultLabel(),\n' +
			'  ...r4_1\n' +
			'} = input;\n' +
			'return [_env_3_0, r4_1];',
	);
});

Deno.test('does not infer an untagged environment-looking rest binding', () => {
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r0_1'),
			t.memberExpression(t.identifier('input'), t.identifier('key')),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('_env_3_0'),
			t.identifier('r0_1'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r2_1'),
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('copyDataProperties'),
				),
				[
					t.objectExpression([]),
					t.identifier('input'),
					t.objectExpression([
						t.objectProperty(
							t.identifier('__proto__'),
							t.nullLiteral(),
						),
						t.objectProperty(
							t.identifier('key'),
							t.numericLiteral(0),
						),
					]),
				],
			),
		)]),
	];

	assert.equal(cleanupComposedObjectRestInBody(body), 0);
	assert.match(generate(t.program(body)).code, /copyDataProperties/);
});

Deno.test('object-rest recovery does not cross a genuine declaration', () => {
	const telemetry = new Map<string, number>();
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r3_1'),
			t.memberExpression(t.identifier('input'), t.identifier('key')),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('userValue'),
			t.callExpression(t.identifier('observe'), []),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
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
			t.memberExpression(t.identifier('r1_1'), t.identifier('key')),
			t.numericLiteral(0),
		)),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r5_2'),
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('copyDataProperties'),
				),
				[
					t.objectExpression([]),
					t.identifier('input'),
					t.identifier('r1_1'),
				],
			),
		)]),
		t.returnStatement(t.arrayExpression([
			t.identifier('r3_1'),
			t.identifier('userValue'),
			t.identifier('r5_2'),
		])),
	];
	const block = { body } as unknown as IRBlock;
	const func = {
		blocks: new Map([[0, block]]),
		recordBindingCleanupObservation(reason: string) {
			telemetry.set(reason, (telemetry.get(reason) ?? 0) + 1);
		},
	} as unknown as IRFunction;

	assert.equal(cleanupSequentialObjectDestructuring(func), false);
	assert.match(generate(t.program(body)).code, /copyDataProperties/);
	assert.equal(telemetry.get('object-rest-intervening-declaration'), 1);
});

Deno.test('categorizes residual embedded object-rest helpers', () => {
	const telemetry = new Map<string, number>();
	const func = {
		recordBindingCleanupObservation(reason: string) {
			telemetry.set(reason, (telemetry.get(reason) ?? 0) + 1);
		},
	} as unknown as IRFunction;
	const helper = t.callExpression(
		t.memberExpression(
			t.identifier('HermesInternal'),
			t.identifier('copyDataProperties'),
		),
		[
			t.objectExpression([]),
			t.identifier('input'),
			t.objectExpression([
				t.objectProperty(t.identifier('key'), t.numericLiteral(0)),
			]),
		],
	);
	const program = t.program([t.returnStatement(t.objectExpression([
		t.spreadElement(helper),
	]))]);

	recordResidualObjectRestTelemetry(func, program);
	assert.equal(telemetry.get('object-rest-residual'), 1);
	assert.equal(
		telemetry.get('object-rest-residual-embedded-spread'),
		1,
	);
	assert.equal(
		telemetry.get('object-rest-residual-static-exclusion'),
		1,
	);
});

Deno.test('retains split object-rest probes and result until CFG joining', () => {
	const entryBody: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r2_1'),
			t.identifier('input'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r5_1'),
			t.memberExpression(t.identifier('r2_1'), t.identifier('style')),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r6_1'),
			t.memberExpression(t.identifier('r2_1'), t.identifier('color')),
		)]),
	];
	const helperBody: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
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
			t.memberExpression(t.identifier('r1_1'), t.identifier('style')),
			t.numericLiteral(0),
		)),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.memberExpression(t.identifier('r1_1'), t.identifier('color')),
			t.numericLiteral(0),
		)),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r11_1'),
			t.identifier('r2_1'),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r11_2'),
			t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('copyDataProperties'),
				),
				[
					t.objectExpression([]),
					t.identifier('r11_1'),
					t.identifier('r1_1'),
				],
			),
		)]),
	];
	const func = {
		blocks: new Map([
			[0, { body: entryBody } as unknown as IRBlock],
			[1, { body: helperBody } as unknown as IRBlock],
		]),
	} as unknown as IRFunction;

	assert.deepEqual(
		[...objectRestProtocolBindingNames(func)].sort(),
		['r11_2', 'r5_1', 'r6_1'],
	);
});

function recoveredPattern(
	pattern: t.ArrayPattern | t.ObjectPattern,
	source: t.Expression,
): t.VariableDeclaration {
	const statement = t.variableDeclaration('var', [
		t.variableDeclarator(pattern, source),
	]);
	statement.extra = { fromDestructuring: true };
	return statement;
}

Deno.test('folds a recovered destructuring into the pattern that bound it', () => {
	const body: t.Statement[] = [
		recoveredPattern(
			t.arrayPattern([t.identifier('r4_1'), t.identifier('r9_3')]),
			t.identifier('_param_7_1_'),
		),
		recoveredPattern(
			t.arrayPattern([t.identifier('r6_1')]),
			t.identifier('r9_3'),
		),
		t.returnStatement(t.identifier('r6_1')),
	];
	const func = singleBlockFunction(body);

	assert.equal(reduceNestedRecoveredDestructuring(func), true);
	assert.equal(reduceNestedRecoveredDestructuring(func), false);
	assert.equal(body.length, 2);
	assert.equal(
		generate(body[0] as t.Node).code,
		'var [r4_1, [r6_1]] = _param_7_1_;',
	);
	assert.equal(body[0].extra?.fromDestructuring, true);
});

Deno.test('folds a recovered destructuring into an object pattern property', () => {
	const body: t.Statement[] = [
		recoveredPattern(
			t.objectPattern([t.objectProperty(
				t.identifier('pair'),
				t.identifier('r2_1'),
			)]),
			t.identifier('_param_7_0_'),
		),
		recoveredPattern(
			t.arrayPattern([t.identifier('r3_1'), t.identifier('r4_1')]),
			t.identifier('r2_1'),
		),
		t.returnStatement(t.identifier('r3_1')),
	];

	assert.equal(
		reduceNestedRecoveredDestructuring(singleBlockFunction(body)),
		true,
	);
	assert.equal(
		generate(body[0] as t.Node).code,
		'var {\n  pair: [r3_1, r4_1]\n} = _param_7_0_;',
	);
});

Deno.test('declines to fold when the bound temporary is read elsewhere', () => {
	const body: t.Statement[] = [
		recoveredPattern(
			t.arrayPattern([t.identifier('r4_1'), t.identifier('r9_3')]),
			t.identifier('_param_7_1_'),
		),
		recoveredPattern(
			t.arrayPattern([t.identifier('r6_1')]),
			t.identifier('r9_3'),
		),
		t.returnStatement(t.identifier('r9_3')),
	];

	assert.equal(
		reduceNestedRecoveredDestructuring(singleBlockFunction(body)),
		false,
	);
	assert.equal(body.length, 3);
});

Deno.test('declines to fold across an intervening statement', () => {
	const body: t.Statement[] = [
		recoveredPattern(
			t.arrayPattern([t.identifier('r4_1'), t.identifier('r9_3')]),
			t.identifier('_param_7_1_'),
		),
		t.expressionStatement(t.callExpression(t.identifier('effect'), [])),
		recoveredPattern(
			t.arrayPattern([t.identifier('r6_1')]),
			t.identifier('r9_3'),
		),
	];

	assert.equal(
		reduceNestedRecoveredDestructuring(singleBlockFunction(body)),
		false,
	);
	assert.equal(body.length, 3);
});

Deno.test('declines to fold a pattern with no destructuring provenance', () => {
	const child = t.variableDeclaration('var', [t.variableDeclarator(
		t.arrayPattern([t.identifier('r6_1')]),
		t.identifier('r9_3'),
	)]);
	const body: t.Statement[] = [
		recoveredPattern(
			t.arrayPattern([t.identifier('r4_1'), t.identifier('r9_3')]),
			t.identifier('_param_7_1_'),
		),
		child,
	];

	assert.equal(
		reduceNestedRecoveredDestructuring(singleBlockFunction(body)),
		false,
	);
	assert.equal(body.length, 2);
});
