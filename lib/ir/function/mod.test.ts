import { strict as assert } from 'node:assert';
import generate from '@babel/generator';
import * as t from '@babel/types';
import {
	BasicBlock,
	Function,
	FunctionKind,
} from '../../hbc/disassembly/function.ts';
import {
	asRegister,
	Instruction,
	InstructionLength,
	InstructionStrictness,
	InstructionType,
} from '../../hbc/disassembly/instruction.ts';
import { HBCFile } from '../../parser/file.ts';
import { SSAFunction } from '../../ssa.ts';
import type { PhiInst, SSARegister } from '../../ssa.ts';
import { AddressGraph } from '../../utils/graph.ts';
import { AddressMap } from '../../utils/map.ts';
import { AddressSet } from '../../utils/set.ts';
import type { IRBlock } from '../ast/mod.ts';
import { foldConditionalValuesInBody, liftPhiNodesInBody } from '../ast/phi.ts';
import {
	reduceInlineTerminal,
	reduceMergedGuardPhiTerminal,
	reduceNaturalLoop,
	reduceOrChain,
	reducePredicateGuardChains,
	reduceSequence,
	reduceSharedLeadingPhi,
	reduceSharedSequenceEdge,
	reduceSharedTerminalPhi,
	reduceSimpleIf,
	reduceSwitch,
} from './cfg/mod.ts';
import { cloneBodyForPredecessor } from './cfg/linear.ts';
import { tryBuildForInOrOfStatement } from './cfg/iterator.ts';
import { HandlerGraph } from './except/mod.ts';
import {
	IRFunction,
	reduceHermesInternalConditionalMemberAccesses,
} from './mod.ts';

const base = {
	length: InstructionLength.NORMAL,
	type: InstructionType.NORMAL,
	strict: InstructionStrictness.NORMAL,
};

function block(
	address: number,
	instructions: Instruction[],
	consequentAddresses: number[],
): BasicBlock {
	return { address, instructions, consequentAddresses, predicate: null };
}

function phiRegister(index: number, version: number): SSARegister {
	return { type: 'register', index, version };
}

function phiInstruction(
	index: number,
	destinationVersion: number,
	sources: Array<[number, number]>,
): PhiInst {
	return {
		instruction: 'Phi',
		destination: phiRegister(index, destinationVersion),
		sources: new AddressMap(
			sources.map(([address, version]) => [
				address,
				phiRegister(index, version),
			]),
		),
	};
}

function phiCloneTestFunction(
	body: t.Statement[],
	phis: PhiInst[],
	predecessorSources: number[] = [0],
): IRFunction {
	const blocks = new AddressMap<IRBlock>([[4, {
		address: 4,
		body,
		consequentAddresses: [],
		kind: 'normal',
	}]]);
	return {
		blocks,
		mergedBlocks: new AddressGraph<number, number>([
			[0, new AddressSet(predecessorSources)],
			[4, new AddressSet([4])],
		]),
		ssa: {
			basicBlocks: new AddressMap([[4, { ssaInstructions: phis }]]),
		},
	} as unknown as IRFunction;
}

Deno.test('CFG migration telemetry is opt-in and traces changed passes', () => {
	const plainSample = new URL(
		'../../../samples/v99/switch.hbc',
		import.meta.url,
	)
		.pathname;
	const plainFile = HBCFile.fromFile(plainSample);
	const plain = new IRFunction(
		plainFile,
		new SSAFunction(plainFile.functions[3]),
		{ cfgReducer: { mode: 'recursive', materialize: false } },
	);
	assert.equal(plain.recursiveCFGSummary?.migrationAudit, undefined);
	assert.equal(plain.recursiveCFGSummary?.normalization.enabled, true);

	const auditSample = new URL(
		'../../../samples/v99/destructuring-init.hbc',
		import.meta.url,
	).pathname;
	const auditedFile = HBCFile.fromFile(auditSample);
	const audited = new IRFunction(
		auditedFile,
		new SSAFunction(auditedFile.functions[0]),
		{
			cfgReducer: {
				mode: 'recursive',
				materialize: false,
				migrationAudit: 'observe',
			},
		},
	);
	const audit = audited.recursiveCFGSummary?.migrationAudit;
	assert.ok(audit);
	assert.equal(audit.mode, 'observe');
	assert.equal(audit.normalization.enabled, true);
	assert.equal(audit.normalization.idempotent, true);
	assert.deepEqual(audit.normalization.invariantIssues, []);
	assert.deepEqual(audit.initial.misses, []);
	assert.equal(audit.passTrace.length, 0);
	assert.ok(
		audit.compatibilityPaths.some((event) =>
			event.path === 'single-top-level-loop' &&
			event.phase === 'raw-region' && event.attempts > 0
		),
	);
	assert.equal(audit.legacyPhiRescue.shadowOnly, true);
	assert.equal(audit.legacyPhiRescue.attempted, false);
	assert.equal(audit.legacyPhiRescue.wouldImprove, false);
	assert.equal(audit.legacyPhiRescue.adopted, false);
	assert.equal(audit.destructuringLegacyRescue.shadowOnly, true);
	assert.equal(audit.destructuringLegacyRescue.attempted, false);
	assert.equal(audit.destructuringLegacyRescue.wouldImprove, false);
	assert.equal(audit.destructuringLegacyRescue.adopted, false);
	assert.deepEqual(
		audit.final?.duplicatedSSABlockCounts,
		audited.recursiveCFGSummary?.duplicatedSSABlockCounts,
	);
});

Deno.test('migration audit rejects generated registers without writes', () => {
	const sample = new URL(
		'../../../samples/v99/switch.hbc',
		import.meta.url,
	).pathname;
	const file = HBCFile.fromFile(sample);
	const func = new IRFunction(
		file,
		new SSAFunction(file.functions[3]),
		{
			cfgReducer: {
				mode: 'recursive',
				materialize: false,
				migrationAudit: 'observe',
			},
		},
	);
	const summary = func.recursiveCFGSummary;
	const selected = summary?.selectedEmission;
	assert.ok(summary?.migrationAudit);
	assert.ok(selected?.program);
	selected.program.body.unshift(
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r999_1')),
		]),
		t.expressionStatement(t.identifier('r999_1')),
	);

	func.finalizeMigrationAudit();

	const rejection = summary.migrationAudit.candidateRejections.find(
		(candidate) => candidate.candidate === selected.source,
	);
	assert.ok(rejection);
	assert.ok(
		rejection.reasons.includes('generated registers are never written'),
	);
});
Deno.test('migration audit applies unified binding placement', () => {
	const sample = new URL(
		'../../../samples/v99/switch.hbc',
		import.meta.url,
	).pathname;
	const file = HBCFile.fromFile(sample);
	const func = new IRFunction(
		file,
		new SSAFunction(file.functions[3]),
		{
			cfgReducer: {
				mode: 'recursive',
				materialize: false,
				migrationAudit: 'observe',
			},
		},
	);
	const restored = IRFunction.fromSnapshot(file, func.snapshot());
	assert.equal(restored.options.cfgReducer, undefined);
	const summary = restored.recursiveCFGSummary;
	const selected = summary?.selectedEmission;
	const audit = summary?.migrationAudit;
	assert.ok(selected?.program);
	assert.ok(audit);
	selected.program.body.unshift(
		t.tryStatement(
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r999_2'),
						t.identifier('source'),
					),
				]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r999_2')],
				)),
			]),
			t.catchClause(
				t.identifier('error'),
				t.blockStatement([
					t.expressionStatement(t.callExpression(
						t.identifier('consume'),
						[t.identifier('r999_2')],
					)),
				]),
			),
		),
	);

	restored.finalizeMigrationAudit();

	assert.equal(audit.bindingPlacement?.placed, 1);
	const code = generate(selected.program).code;
	assert.equal(code.match(/let r999_2;/g)?.length, 1);
	assert.match(code, /r999_2 = source;/);
	assert.doesNotMatch(code, /const r999_2/);
	assert.equal(
		audit.candidateRejections.some((rejection) =>
			rejection.reasons.some((reason) =>
				reason.startsWith('generated registers')
			)
		),
		false,
	);
});

Deno.test('migration audit treats loop declarations as writes', () => {
	const sample = new URL(
		'../../../samples/v96/forOf.hbc',
		import.meta.url,
	).pathname;
	const file = HBCFile.fromFile(sample);
	const func = new IRFunction(
		file,
		new SSAFunction(file.functions[1]),
		{
			cfgReducer: {
				mode: 'recursive',
				materialize: false,
				migrationAudit: 'observe',
			},
		},
	);
	const audit = func.recursiveCFGSummary?.migrationAudit;
	assert.ok(audit);
	assert.equal(
		audit.candidateRejections.some((rejection) =>
			rejection.reasons.includes('generated registers are never written')
		),
		false,
	);
});

Deno.test('recursive emission normalizes SSA global-object TryGetById uses', () => {
	const sample = new URL(
		'../../../samples/v96/tryCatch.test.hbc',
		import.meta.url,
	).pathname;
	const file = HBCFile.fromFile(sample);
	const func = new IRFunction(file, new SSAFunction(file.functions[2]), {
		cfgReducer: { mode: 'recursive', materialize: false },
	});
	const code = func.recursiveCFGSummary?.emittedCode ?? '';

	assert.match(code, /console\.log\("inner0\.try"\)/);
	assert.doesNotMatch(code, /%TryGetById/);
});

Deno.test('worker-restored functions support async-generator analysis', () => {
	const func = Object.create(IRFunction.prototype) as IRFunction;
	func.file = { version: 99 } as HBCFile;
	func.entryAddress = 0;
	func.blocks = new AddressMap([
		[0, {
			address: 0,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	assert.doesNotThrow(() => func.analyseAsyncGeneratorClosure());
});

Deno.test('handler activity follows source blocks merged into a parent', () => {
	const sourceBlocks = new Map([
		[0, { consequentAddresses: [], ssaInstructions: [] }],
		[10, { consequentAddresses: [], ssaInstructions: [] }],
		[30, { consequentAddresses: [], ssaInstructions: [] }],
	]);
	const func = {
		_exceptionHandlers: [{
			tryStart: 10,
			tryEnd: 20,
			catchOffset: 30,
		}],
		blocks: new Map(),
		ssa: { basicBlocks: sourceBlocks },
		mergedBlocks: new AddressGraph([
			[0, new AddressSet([0, 10])],
		]),
	} as unknown as IRFunction;
	const handlers = new HandlerGraph(func);

	assert.deepEqual([...handlers.activeHandlersAtBlock(0)], [30]);
});

Deno.test('split value-only catch pads alias their enclosing handler', () => {
	const caughtInner = phiRegister(1, 1);
	const caughtOuter = phiRegister(1, 2);
	const innerValue = phiRegister(0, 3);
	const outerValue = phiRegister(0, 4);
	const result = phiRegister(0, 5);
	const sourceBlocks = new Map([
		[20, { consequentAddresses: [40], ssaInstructions: [] }],
		[40, { consequentAddresses: [90], ssaInstructions: [] }],
		[60, {
			consequentAddresses: [65],
			ssaInstructions: [{
				instruction: 'Catch',
				defs: { destination: caughtInner },
				uses: {},
			}],
		}],
		[65, {
			consequentAddresses: [90],
			ssaInstructions: [{
				instruction: 'LoadConst',
				defs: { destination: innerValue },
				uses: {},
				value: true,
			}, {
				instruction: 'Jmp',
				defs: {},
				uses: {},
			}],
		}],
		[80, {
			consequentAddresses: [90],
			ssaInstructions: [{
				instruction: 'Catch',
				defs: { destination: caughtOuter },
				uses: {},
			}, {
				instruction: 'LoadConst',
				defs: { destination: outerValue },
				uses: {},
				value: true,
			}],
		}],
		[90, {
			consequentAddresses: [],
			ssaInstructions: [{
				instruction: 'Ret',
				defs: {},
				uses: { argument: result },
			}],
		}],
	]);
	const func = {
		_exceptionHandlers: [{
			tryStart: 40,
			tryEnd: 50,
			catchOffset: 60,
		}, {
			tryStart: 20,
			tryEnd: 70,
			catchOffset: 80,
		}],
		blocks: new Map(),
		ssa: { basicBlocks: sourceBlocks },
		mergedBlocks: new AddressGraph(),
	} as unknown as IRFunction;

	const aliases = new HandlerGraph(func).equivalentCatchHandlerAliases();

	assert.deepEqual([...aliases], [[60, 80]]);
});

Deno.test('finalizer copies keep unconditional jumps significant', () => {
	const sourceBlocks = new Map([
		[20, {
			consequentAddresses: [60],
			ssaInstructions: [],
		}],
		[40, {
			consequentAddresses: [],
			ssaInstructions: [{
				instruction: 'Catch',
				defs: { destination: phiRegister(0, 1) },
				uses: {},
			}, {
				instruction: 'Jmp',
				defs: {},
				uses: {},
			}],
		}],
		[60, {
			consequentAddresses: [],
			ssaInstructions: [],
		}],
	]);
	const func = {
		_exceptionHandlers: [],
		blocks: new AddressMap([
			[20, {
				address: 20,
				body: [],
				consequentAddresses: [60],
				kind: 'normal',
			}],
			[40, {
				address: 40,
				body: [],
				consequentAddresses: [],
				kind: 'normal',
			}],
			[60, {
				address: 60,
				body: [],
				consequentAddresses: [],
				kind: 'normal',
			}],
		]),
		ssa: { basicBlocks: sourceBlocks },
		mergedBlocks: new AddressGraph(),
	} as unknown as IRFunction;
	const handlers = HandlerGraph.fromSnapshot(func, {
		records: [[40, {
			catchAddress: 40,
			innerTryRecords: [],
			ranges: [],
			directProtectedBlocks: [20],
			catchBody: null,
			canonicalFinallyAddress: null,
		}]],
		protectedEntries: [20],
		finallyRecords: [[40, {
			canonicalFinallyAddress: 40,
			catchTrailer: null,
			copyRoots: [],
			bodyBlocks: [40],
			bodyBlockStatementLimits: [],
			isReturnOverride: false,
		}]],
	});

	const descriptor = handlers.structuredRegionDescriptors()[0];

	assert.equal(descriptor.kind, 'finally');
	assert.deepEqual(descriptor.finallyCopies, []);
});

Deno.test(
	'a rethrowing catch without duplicated cleanup is not a finalizer',
	() => {
		const caught = phiRegister(0, 1);
		const cleanupValue = phiRegister(1, 1);
		const sourceBlocks = new Map([
			[10, {
				consequentAddresses: [20],
				ssaInstructions: [],
			}],
			[20, {
				// The inner try and catch share an ordinary continuation.
				consequentAddresses: [50],
				ssaInstructions: [],
			}],
			[40, {
				consequentAddresses: [50],
				ssaInstructions: [{
					instruction: 'Catch',
					defs: { destination: phiRegister(2, 1) },
					uses: {},
				}],
			}],
			[50, {
				// The protected exit performs the same call with a different
				// argument; it is ordinary sibling work, not a cleanup copy.
				consequentAddresses: [],
				ssaInstructions: [{
					instruction: 'LoadConst',
					defs: { destination: phiRegister(1, 2) },
					uses: {},
					value: 'success',
				}, {
					instruction: 'Call',
					defs: { destination: phiRegister(5, 1) },
					uses: {
						closure: phiRegister(4, 1),
						arguments: [
							phiRegister(6, 1),
							phiRegister(1, 2),
						],
					},
				}, {
					instruction: 'Ret',
					defs: {},
					uses: { argument: phiRegister(3, 1) },
				}],
			}],
			[90, {
				consequentAddresses: [],
				ssaInstructions: [{
					instruction: 'Catch',
					defs: { destination: caught },
					uses: {},
				}, {
					instruction: 'LoadConst',
					defs: { destination: cleanupValue },
					uses: {},
					value: 'failure',
				}, {
					instruction: 'Call',
					defs: { destination: phiRegister(5, 2) },
					uses: {
						closure: phiRegister(4, 2),
						arguments: [
							phiRegister(6, 2),
							cleanupValue,
						],
					},
				}, {
					instruction: 'Throw',
					defs: {},
					uses: { exception: caught },
				}],
			}],
		]);
		const func = {
			_exceptionHandlers: [{
				tryStart: 20,
				tryEnd: 30,
				catchOffset: 40,
			}, {
				tryStart: 10,
				tryEnd: 50,
				catchOffset: 90,
			}],
			blocks: new Map(),
			ssa: { basicBlocks: sourceBlocks },
			mergedBlocks: new AddressGraph(),
		} as unknown as IRFunction;

		const handlers = new HandlerGraph(func);
		const descriptors = handlers.structuredRegionDescriptors();
		const inner = descriptors.find(({ handler }) => handler === 40);
		const outer = descriptors.find(({ handler }) => handler === 90);

		assert.ok(inner);
		assert.equal(inner.canonicalFinallyAddress, null);
		assert.equal(inner.catchBody, null);
		assert.ok(outer);
		assert.equal(outer.kind, 'catch');
		assert.equal(handlers.finallyRecords.has(90), false);
	},
);

Deno.test(
	'exception-only iterator close is an intrinsic finalizer',
	() => {
		const caught = phiRegister(0, 1);
		const iterator = phiRegister(1, 1);
		const sourceBlocks = new Map([
			[20, {
				consequentAddresses: [50],
				ssaInstructions: [],
			}],
			[40, {
				consequentAddresses: [],
				ssaInstructions: [{
					instruction: 'Catch',
					defs: { destination: caught },
					uses: {},
				}, {
					instruction: 'IteratorClose',
					defs: {},
					uses: { iterator },
					ignoreException: 1,
				}, {
					instruction: 'Throw',
					defs: {},
					uses: { exception: caught },
				}],
			}],
			[50, {
				consequentAddresses: [],
				ssaInstructions: [{
					instruction: 'Ret',
					defs: {},
					uses: { argument: phiRegister(2, 1) },
				}],
			}],
		]);
		const func = {
			_exceptionHandlers: [{
				tryStart: 20,
				tryEnd: 30,
				catchOffset: 40,
			}],
			blocks: new Map(),
			ssa: { basicBlocks: sourceBlocks },
			mergedBlocks: new AddressGraph(),
		} as unknown as IRFunction;

		const handlers = new HandlerGraph(func);
		const descriptor = handlers.structuredRegionDescriptors().find(
			({ handler }) => handler === 40,
		);

		assert.ok(descriptor);
		assert.equal(descriptor.kind, 'finally');
		assert.deepEqual([...descriptor.finallyCopyRoots], []);
	},
);

Deno.test(
	'finalizer copy matching tolerates exceptional-path value setup',
	() => {
		const caught = phiRegister(0, 1);
		const sourceBlocks = new Map([
			[20, {
				consequentAddresses: [35],
				ssaInstructions: [],
			}],
			[35, {
				consequentAddresses: [],
				ssaInstructions: [{
					instruction: 'TryGetById',
					defs: { destination: phiRegister(1, 1) },
					uses: { object: phiRegister(2, 1) },
					property: 'print',
				}, {
					instruction: 'LoadConst',
					defs: { destination: phiRegister(3, 1) },
					uses: {},
					value: 'finally',
				}, {
					instruction: 'Call',
					defs: { destination: phiRegister(4, 1) },
					uses: {
						closure: phiRegister(1, 1),
						arguments: [
							phiRegister(5, 1),
							phiRegister(3, 1),
						],
					},
				}, {
					instruction: 'Ret',
					defs: {},
					uses: { argument: phiRegister(6, 1) },
				}],
			}],
			[40, {
				consequentAddresses: [],
				ssaInstructions: [{
					instruction: 'Catch',
					defs: { destination: caught },
					uses: {},
				}, {
					instruction: 'GetGlobalObject',
					defs: { destination: phiRegister(2, 2) },
					uses: {},
				}, {
					instruction: 'TryGetById',
					defs: { destination: phiRegister(1, 2) },
					uses: { object: phiRegister(2, 2) },
					property: 'print',
				}, {
					instruction: 'LoadConst',
					defs: { destination: phiRegister(5, 2) },
					uses: {},
				}, {
					instruction: 'LoadConst',
					defs: { destination: phiRegister(3, 2) },
					uses: {},
					value: 'finally',
				}, {
					instruction: 'Call',
					defs: { destination: phiRegister(4, 2) },
					uses: {
						closure: phiRegister(1, 2),
						arguments: [
							phiRegister(5, 2),
							phiRegister(3, 2),
						],
					},
				}, {
					instruction: 'Throw',
					defs: {},
					uses: { exception: caught },
				}],
			}],
		]);
		const func = {
			_exceptionHandlers: [{
				tryStart: 20,
				tryEnd: 35,
				catchOffset: 40,
			}],
			blocks: new Map(),
			ssa: { basicBlocks: sourceBlocks },
			mergedBlocks: new AddressGraph(),
		} as unknown as IRFunction;

		const handlers = new HandlerGraph(func);
		const descriptor = handlers.structuredRegionDescriptors().find(
			({ handler }) => handler === 40,
		);

		assert.ok(descriptor);
		assert.equal(descriptor.kind, 'finally');
		assert.deepEqual([...descriptor.finallyCopyRoots], [35]);
	},
);

Deno.test(
	'shared terminal suffix recovers a merged equality branch and value',
	() => {
		const blocks = new Map<number, IRBlock>([
			[0, {
				address: 0,
				body: [t.ifStatement(
					t.identifier('outer'),
					t.blockStatement([
						t.returnStatement(t.booleanLiteral(false)),
					]),
					t.blockStatement([
						t.expressionStatement(t.identifier('offer')),
						t.expressionStatement(t.identifier('override')),
					]),
				)],
				consequentAddresses: [1, 2],
				kind: 'normal',
			}],
			[1, {
				address: 1,
				body: [
					t.variableDeclaration('const', [
						t.variableDeclarator(
							t.identifier('selected'),
							t.identifier('fallback'),
						),
					]),
					t.expressionStatement(t.callExpression(
						t.identifier('use'),
						[t.identifier('selected')],
					)),
					t.returnStatement(t.booleanLiteral(true)),
				],
				consequentAddresses: [],
				kind: 'normal',
			}],
			[2, {
				address: 2,
				body: [
					t.expressionStatement(t.callExpression(
						t.identifier('use'),
						[t.identifier('selected')],
					)),
					t.returnStatement(t.booleanLiteral(true)),
				],
				consequentAddresses: [],
				kind: 'normal',
			}],
		]);
		const mergedBlocks = new AddressGraph<number, number>([
			[0, new AddressSet([0, 10])],
			[1, new AddressSet()],
			[2, new AddressSet()],
		]);
		const func = {
			id: 1,
			blocks,
			mergedBlocks,
			ssa: {
				basicBlocks: new Map([
					[10, {
						predicate: {
							not: true,
							left: { index: 0 },
							operation: '===',
							right: { index: 1 },
						},
						consequentAddresses: [1, 2],
						ssaInstructions: [{
							instruction: 'JStrictNotEqual',
						}],
					}],
				]),
			},
			exceptions: {
				activeHandlersEqual: () => true,
			},
			predecessorsOf(target: number) {
				return new AddressSet(
					[...blocks].filter(([, candidate]) =>
						candidate.consequentAddresses.includes(target)
					).map(([address]) => address),
				);
			},
			markMergedBlocks(parent: number, child: number) {
				blocks.delete(child);
				mergedBlocks.set(
					parent,
					new AddressSet([
						parent,
						child,
						...mergedBlocks.get(parent) ?? [],
						...mergedBlocks.get(child) ?? [],
					]),
				);
				mergedBlocks.delete(child);
			},
		} as unknown as IRFunction;

		assert.equal(reducePredicateGuardChains(func), true);
		assert.equal(blocks.size, 1);
		assert.deepEqual(blocks.get(0)?.consequentAddresses, []);
		const code =
			generate(t.program(blocks.get(0)!.body as t.Statement[])).code;
		assert.match(code, /let selected;/);
		assert.match(code, /if \(offer === override\)/);
		assert.match(code, /selected = fallback/);
		assert.match(code, /selected = override/);
		assert.match(code, /use\(selected\)/);
	},
);

Deno.test('shared terminal phi accepts equivalent merged Mov sources', () => {
	const phi = t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
		t.identifier('r5_1'),
		t.identifier('r5_2'),
		t.identifier('r5_3'),
	]);
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('condition'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.variableDeclaration('const', [
					t.variableDeclarator(t.identifier('r5_10'), phi),
				]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r5_10')],
				)),
				t.returnStatement(),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const register = (index: number, version: number) => ({ index, version });
	const mov = (version: number) => ({
		instruction: 'Mov',
		defs: { destination: register(5, version) },
		uses: { source: register(8, 1) },
	});
	const ssaBlocks = new Map([
		[1, { ssaInstructions: [mov(1)] }],
		[2, { ssaInstructions: [] }],
		[3, { ssaInstructions: [mov(2)] }],
		[4, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: register(5, 10),
				sources: new Map([
					[1, register(5, 1)],
					[3, register(5, 2)],
					[2, register(5, 3)],
				]),
			}],
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>([
		[0, new AddressSet([0])],
		[1, new AddressSet([1, 3])],
		[2, new AddressSet([2])],
		[4, new AddressSet([4])],
	]);
	const func = {
		blocks,
		mergedBlocks,
		ssa: { basicBlocks: ssaBlocks },
		exceptions: {
			records: new Map(),
			activeHandlersEqual: () => true,
		},
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
	} as unknown as IRFunction;

	assert.equal(reduceSharedTerminalPhi(func), true);
	const rootCode = generate(t.program(blocks.get(0)!.body as t.Statement[]))
		.code;
	const leftCode = generate(t.program(blocks.get(1)!.body as t.Statement[]))
		.code;
	const rightCode = generate(t.program(blocks.get(2)!.body as t.Statement[]))
		.code;
	assert.match(rootCode, /let r5_10/);
	assert.match(leftCode, /r5_10 = r8_1/);
	assert.match(rightCode, /r5_10 = r5_3/);
	assert.doesNotMatch(
		generate(t.program(blocks.get(4)!.body as t.Statement[])).code,
		/%Phi/,
	);
});

Deno.test('merged guard phi appends a shared terminal exactly once', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('condition'),
			consequentAddresses: [4, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r5_10'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('r5_1'),
						t.identifier('r5_2'),
					]),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('effect'),
					[t.identifier('r5_10')],
				)),
				t.returnStatement(),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const register = (index: number, version: number) => ({ index, version });
	const loadParam = (index: number) => ({
		instruction: 'LoadParam',
		defs: { destination: register(index, 1) },
		uses: {},
	});
	const mov = (version: number, sourceIndex: number) => ({
		instruction: 'Mov',
		defs: { destination: register(5, version) },
		uses: { source: register(sourceIndex, 1) },
	});
	const ssaBlocks = new Map([
		[0, { ssaInstructions: [loadParam(8), loadParam(3)] }],
		[1, { ssaInstructions: [mov(1, 8)] }],
		[2, { ssaInstructions: [mov(2, 3)] }],
		[4, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: register(5, 10),
				sources: new Map([
					[1, register(5, 1)],
					[2, register(5, 2)],
				]),
			}],
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>([
		[0, new AddressSet([0, 1])],
		[2, new AddressSet([2, 4])],
	]);
	const func = {
		blocks,
		mergedBlocks,
		ssa: { basicBlocks: ssaBlocks },
		exceptions: { activeHandlersEqual: () => true },
		markMergedBlocks(parent: number, child: number) {
			blocks.delete(child);
			mergedBlocks.set(
				parent,
				new AddressSet([
					parent,
					child,
					...mergedBlocks.get(parent) ?? [],
					...mergedBlocks.get(child) ?? [],
				]),
			);
			mergedBlocks.delete(child);
		},
	} as unknown as IRFunction;

	assert.equal(reduceMergedGuardPhiTerminal(func), true);
	assert.equal(blocks.size, 1);
	const code = generate(t.program(blocks.get(0)!.body as t.Statement[])).code;
	assert.match(code, /if \(condition\)/);
	assert.match(code, /r5_10 = r3_1/);
	assert.match(code, /r5_10 = r8_1/);
	assert.equal(code.match(/effect\(r5_10\)/g)?.length, 1);
	assert.doesNotMatch(code, /%Phi/);
});

Deno.test(
	'predecessor cloning keeps a Phi accumulator already lowered from the AST',
	() => {
		const func = phiCloneTestFunction(
			[
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r1_3')],
				)),
				t.returnStatement(),
			],
			[phiInstruction(1, 3, [[0, 1], [2, 2]])],
		);

		const body = cloneBodyForPredecessor(func, 4, 0);
		const code = generate(t.program(body)).code;
		assert.match(code, /consume\(r1_3\)/);
		assert.doesNotMatch(code, /consume\(r1_1\)/);
	},
);

Deno.test(
	'predecessor cloning specializes only Phis still present in the AST',
	() => {
		const currentPhi = t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
			t.identifier('r2_1'),
			t.identifier('r2_2'),
		]);
		const func = phiCloneTestFunction(
			[
				t.variableDeclaration('const', [
					t.variableDeclarator(t.identifier('r2_3'), currentPhi),
				]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r1_3'), t.identifier('r2_3')],
				)),
				t.returnStatement(),
			],
			[
				phiInstruction(1, 3, [[0, 1], [2, 2]]),
				phiInstruction(2, 3, [[0, 1], [2, 2]]),
			],
		);

		const body = cloneBodyForPredecessor(func, 4, 0);
		const code = generate(t.program(body)).code;
		assert.match(code, /consume\(r1_3, r2_1\)/);
		assert.doesNotMatch(code, /r1_1|r2_3|%Phi/);
	},
);

Deno.test(
	'predecessor cloning resolves an embedded Phi by its current operands',
	() => {
		const inlinePhi = t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
			t.identifier('r2_1'),
			t.identifier('r2_2'),
		]);
		const func = phiCloneTestFunction(
			[
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r1_3')],
				)),
				t.returnStatement(inlinePhi),
			],
			[
				phiInstruction(1, 3, [[0, 1], [2, 2]]),
				phiInstruction(2, 3, [[0, 1], [2, 2]]),
			],
		);

		const body = cloneBodyForPredecessor(func, 4, 0);
		const code = generate(t.program(body)).code;
		assert.match(code, /consume\(r1_3\)/);
		assert.match(code, /return r2_1/);
		assert.doesNotMatch(code, /%Phi|return r1_1/);
	},
);

Deno.test(
	'predecessor cloning retains conflicting merged Phi sources transactionally',
	() => {
		const phi = t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
			t.identifier('r1_1'),
			t.identifier('r1_2'),
		]);
		const func = phiCloneTestFunction(
			[
				t.variableDeclaration('const', [
					t.variableDeclarator(t.identifier('r1_3'), phi),
				]),
				t.returnStatement(t.identifier('r1_3')),
			],
			[phiInstruction(1, 3, [[0, 1], [2, 2]])],
			[0, 2],
		);

		const body = cloneBodyForPredecessor(func, 4, 0);
		const code = generate(t.program(body)).code;
		assert.match(code, /const r1_3 = %Phi\(r1_1, r1_2\)/);
		assert.match(code, /return r1_3/);
	},
);

Deno.test(
	'inline terminal keeps a lowered SSA Phi join shared',
	() => {
		const terminal = (address: number): IRBlock => ({
			address,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		});
		const blocks = new AddressMap<IRBlock>([
			[0, {
				address: 0,
				body: [],
				branch: t.identifier('left'),
				consequentAddresses: [1, 4],
				kind: 'normal',
			}],
			[1, terminal(1)],
			[2, {
				address: 2,
				body: [],
				branch: t.identifier('right'),
				consequentAddresses: [3, 4],
				kind: 'normal',
			}],
			[3, terminal(3)],
			[4, {
				address: 4,
				body: [
					t.expressionStatement(t.callExpression(
						t.identifier('sharedEffect'),
						[t.identifier('r1_3')],
					)),
					t.returnStatement(),
				],
				consequentAddresses: [],
				kind: 'normal',
			}],
		]);
		const register = (version: number) => ({ index: 1, version });
		const mergedBlocks = new AddressGraph<number, number>(
			[...blocks.keys()].map((address) => [
				address,
				new AddressSet([address]),
			]),
		);
		const func = {
			blocks,
			mergedBlocks,
			ssa: {
				basicBlocks: new Map([[4, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: register(3),
						sources: new Map([
							[0, register(1)],
							[2, register(2)],
						]),
					}],
				}]]),
			},
			exceptions: {
				records: new Map(),
				activeHandlersEqual: () => true,
				isCatchTarget: () => false,
			},
			predecessorsOf(target: number) {
				return new AddressSet(
					[...blocks].filter(([, candidate]) =>
						candidate.consequentAddresses.includes(target)
					).map(([address]) => address),
				);
			},
			markMergedBlocks(_parent: number, child: number) {
				blocks.delete(child);
			},
		} as unknown as IRFunction;

		// The unique early-return arm can be folded, but the shared Phi join must
		// remain a single continuation on subsequent passes.
		assert.equal(reduceInlineTerminal(func), true);
		assert.equal(reduceInlineTerminal(func), false);
		assert.deepEqual(blocks.get(0)?.consequentAddresses, [4]);
		assert.deepEqual(blocks.get(2)?.consequentAddresses, [4]);
		assert.equal(
			[...blocks.values()].filter((block) =>
				generate(t.program(block.body as t.Statement[])).code.includes(
					'sharedEffect',
				)
			).length,
			1,
		);
	},
);

Deno.test('inline terminal recognizes a shared natural-loop break', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('leftExit'),
			consequentAddresses: [1, -5],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('rightExit'),
			consequentAddresses: [3, -5],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[-5, {
			address: -5,
			body: [t.breakStatement()],
			consequentAddresses: [],
			kind: 'synthetic',
			terminalKind: 'break',
			syntheticReason: 'natural-loop-break',
		}],
	]);
	const func = {
		blocks,
		mergedBlocks: new AddressGraph<number, number>(
			[...blocks.keys()].map((address) => [
				address,
				new AddressSet([address]),
			]),
		),
		ssa: { basicBlocks: new Map() },
		exceptions: {
			records: new Map(),
			activeHandlersEqual: () => true,
			isCatchTarget: () => false,
		},
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
	} as unknown as IRFunction;

	assert.equal(reduceInlineTerminal(func), true);
	const inlined = [0, 2].map((address) => blocks.get(address)!).filter(
		(candidate) => candidate.branch === undefined,
	);
	assert.equal(inlined.length, 1);
	assert.equal(inlined[0].consequentAddresses.length, 1);
	assert.match(
		generate(t.program(inlined[0].body as t.Statement[])).code,
		/if \(.*Exit\) \{\n {2}break;/,
	);
});

Deno.test('loop-header Phi coalescing renames destination uses', () => {
	const phi = t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
		t.identifier('r1_1'),
		t.identifier('r1_3'),
	]);
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			t.identifier('initial'),
		)]),
		t.whileStatement(
			t.booleanLiteral(true),
			t.blockStatement([
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_2'),
					phi,
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r1_2')],
				)),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_3'),
					t.callExpression(t.identifier('next'), [
						t.identifier('r1_2'),
					]),
				)]),
			]),
		),
	];

	assert.equal(liftPhiNodesInBody(body), true);
	const code = generate(t.program(body)).code;
	assert.match(code, /let r1_1 = initial/);
	assert.match(code, /consume\(r1_1\)/);
	assert.match(code, /r1_1 = next\(r1_1\)/);
	assert.doesNotMatch(code, /%Phi|r1_2|r1_3/);
});

Deno.test('loop-header Phi coalescing renames aliases used after loop exit', () => {
	const phi = t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
		t.identifier('r1_1'),
		t.identifier('r1_3'),
	]);
	const body: t.Statement[] = [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			t.identifier('initial'),
		)]),
		t.whileStatement(
			t.booleanLiteral(true),
			t.blockStatement([
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_2'),
					phi,
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r2_1'),
					t.identifier('r1_2'),
				)]),
				t.ifStatement(
					t.callExpression(t.identifier('done'), [
						t.identifier('r2_1'),
					]),
					t.blockStatement([t.breakStatement()]),
				),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_3'),
					t.callExpression(t.identifier('next'), [
						t.identifier('r2_1'),
					]),
				)]),
			]),
		),
		t.returnStatement(t.memberExpression(
			t.identifier('r2_1'),
			t.identifier('value'),
		)),
	];

	assert.equal(liftPhiNodesInBody(body), true);
	const code = generate(t.program(body)).code;
	assert.match(code, /return r1_1\.value/);
	assert.doesNotMatch(code, /%Phi|return r2_1\.value/);
});

Deno.test('compare switch lowers every leading Phi before structuring', () => {
	const phi = (destination: number, sources: number[]) => ({
		instruction: 'Phi' as const,
		destination: { index: destination, version: 4 },
		sources: new Map(sources.map((source, index) => [
			index === 0 ? 1 : index + 1,
			{ index: destination, version: source },
		])),
	});
	const sourceDeclarations = (
		leftVersion: number,
		rightVersion: number,
		leftValue: string,
		rightValue: string,
	) => [
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier(`r10_${leftVersion}`),
			t.stringLiteral(leftValue),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier(`r11_${rightVersion}`),
			t.stringLiteral(rightValue),
		)]),
	];
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('caseA'),
				t.stringLiteral('A'),
			)])],
			branch: t.binaryExpression(
				'===',
				t.identifier('caseA'),
				t.identifier('kind'),
			),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [
				...sourceDeclarations(1, 1, 'default-left', 'default-right'),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('caseB'),
					t.stringLiteral('B'),
				)]),
			],
			branch: t.binaryExpression(
				'===',
				t.identifier('caseB'),
				t.identifier('kind'),
			),
			consequentAddresses: [4, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: sourceDeclarations(2, 2, 'a-left', 'a-right'),
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: sourceDeclarations(3, 3, 'b-left', 'b-right'),
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r10_4'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('r10_1'),
						t.identifier('r10_2'),
						t.identifier('r10_3'),
					]),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r11_4'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('r11_1'),
						t.identifier('r11_2'),
						t.identifier('r11_3'),
					]),
				)]),
				t.returnStatement(t.arrayExpression([
					t.identifier('r10_4'),
					t.identifier('r11_4'),
				])),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>(
		[...blocks.keys()].map((address) => [
			address,
			new AddressSet([address]),
		]),
	);
	const func = {
		blocks,
		mergedBlocks,
		ssa: {
			basicBlocks: new Map([[4, {
				ssaInstructions: [phi(10, [1, 2, 3]), phi(11, [1, 2, 3])],
			}]]),
		},
		exceptions: { activeHandlersEqual: () => true },
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
	} as unknown as IRFunction;

	assert.equal(reduceSwitch(func), true);
	const rootCode = generate(t.program(blocks.get(0)!.body as t.Statement[]))
		.code;
	const joinCode = generate(t.program(blocks.get(4)!.body as t.Statement[]))
		.code;
	assert.match(rootCode, /let r10_4, r11_4/);
	for (const address of [1, 2, 3]) {
		const code = generate(t.program(
			blocks.get(address)!.body as t.Statement[],
		)).code;
		assert.match(code, /r10_4 =/);
		assert.match(code, /r11_4 =/);
	}
	assert.doesNotMatch(joinCode, /%Phi/);
});

Deno.test('recovered conditional Phi uses transformed edge expressions', () => {
	const directSource = t.binaryExpression(
		'!==',
		t.nullLiteral(),
		t.identifier('r10_2'),
	);
	const guardedSource = t.binaryExpression(
		'!==',
		t.numericLiteral(4294967295),
		t.memberExpression(
			t.identifier('root'),
			t.identifier('timeoutHandle'),
		),
	);
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.cloneNode(directSource, true),
			consequentAddresses: [5, 6],
			kind: 'generatorCase',
		}],
		[5, {
			address: 5,
			body: [],
			consequentAddresses: [6],
			kind: 'generatorCase',
		}],
		[6, {
			address: 6,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r3_3'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.cloneNode(directSource, true),
						t.cloneNode(guardedSource, true),
					]),
				)]),
				t.returnStatement(t.identifier('r3_3')),
			],
			consequentAddresses: [],
			kind: 'generatorCase',
		}],
	]);
	const register = (version: number) => ({ index: 3, version });
	const rawHeader = 0x6a;
	const rawGuarded = 0x79;
	const rawJoin = 0x89;
	const mergedBlocks = new AddressGraph<number, number>([
		[0, new AddressSet([rawHeader])],
		[5, new AddressSet([rawGuarded])],
		[6, new AddressSet([rawJoin])],
	]);
	const func = {
		blocks,
		guardedPhiMode: 'enabled',
		mergedBlocks,
		ssa: {
			_func: { basicBlocks: new Map(), exceptionHandlers: [] },
			basicBlocks: new Map([[rawJoin, {
				ssaInstructions: [{
					instruction: 'Phi',
					destination: register(3),
					sources: new Map([
						[rawHeader, register(1)],
						[rawGuarded, register(2)],
					]),
				}],
			}]]),
		},
		exceptions: {
			activeHandlersAtBlock: () => [],
			activeHandlersParent: () => true,
		},
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
		markMergedBlocks(target: number, source: number) {
			const targetSources = mergedBlocks.get(target) ??
				new AddressSet<number>();
			for (const address of mergedBlocks.get(source) ?? []) {
				targetSources.add(address);
			}
			mergedBlocks.set(target, targetSources);
			mergedBlocks.delete(source);
			blocks.delete(source);
		},
	} as unknown as IRFunction;

	assert.equal(reduceSimpleIf(func), true);
	const root = blocks.get(0)!;
	assert.equal(foldConditionalValuesInBody(root.body as t.Statement[]), true);
	const code = generate(t.program(root.body as t.Statement[])).code;
	assert.match(
		code,
		/null !== r10_2 \|\| 4294967295 !== root\.timeoutHandle/,
	);
	assert.doesNotMatch(code, /%Phi/);
});

Deno.test('recursive prepass preserves successor Phi edge copies', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('cond'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_1'),
					t.stringLiteral('left'),
				)]),
			],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_2'),
					t.stringLiteral('right'),
				)]),
			],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_3'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('r1_1'),
						t.identifier('r1_2'),
					]),
				)]),
			],
			branch: t.identifier('r1_3'),
			consequentAddresses: [4, 5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>(
		[...blocks.keys()].map((address) => [
			address,
			new AddressSet([address]),
		]),
	);
	const func = {
		blocks,
		guardedPhiMode: 'disabled',
		mergedBlocks,
		ssa: {
			_func: { basicBlocks: new Map(), exceptionHandlers: [] },
			basicBlocks: new Map([[3, {
				ssaInstructions: [{
					instruction: 'Phi',
					destination: { index: 1, version: 3 },
					sources: new Map([
						[1, { index: 1, version: 1 }],
						[2, { index: 1, version: 2 }],
					]),
				}],
			}]]),
		},
		exceptions: {
			activeHandlersAtBlock: () => [],
			activeHandlersParent: () => true,
		},
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
		markMergedBlocks(target: number, source: number) {
			const targetSources = mergedBlocks.get(target) ??
				new AddressSet<number>();
			for (const address of mergedBlocks.get(source) ?? []) {
				targetSources.add(address);
			}
			targetSources.add(source);
			mergedBlocks.set(target, targetSources);
			mergedBlocks.delete(source);
			blocks.delete(source);
		},
	} as unknown as IRFunction;

	assert.equal(
		reduceSimpleIf(func, { preserveSuccessorPhis: true }),
		true,
	);
	const rootCode = generate(t.program(blocks.get(0)!.body as t.Statement[]))
		.code;
	const successorCode =
		generate(t.program(blocks.get(3)!.body as t.Statement[]))
			.code;
	assert.match(rootCode, /let r1_3/);
	assert.match(rootCode, /r1_3 = "left"/);
	assert.match(rootCode, /r1_3 = "right"/);
	assert.doesNotMatch(successorCode, /%Phi/);
	assert.equal(blocks.get(0)!.consequentAddresses[0], 3);
});

Deno.test('sequence keeps an unresolved phi join with multiple live owners', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('r1_1'),
						t.identifier('r1_2'),
					])],
				)),
				t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('CreateClosure'),
					[t.identifier('closure'), t.identifier('environment')],
				)),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const register = (version: number) => ({ index: 1, version });
	const mergedBlocks = new AddressGraph<number, number>([
		[0, new AddressSet([0])],
		[2, new AddressSet([2])],
		[3, new AddressSet([3])],
	]);
	const func = {
		blocks,
		mergedBlocks,
		ssa: {
			basicBlocks: new Map([[3, {
				ssaInstructions: [{
					instruction: 'Phi',
					destination: register(3),
					sources: new Map([
						[0, register(1)],
						[2, register(2)],
					]),
				}],
			}]]),
		},
		exceptions: {
			finallyRecords: new Map(),
			records: new Map(),
			isCatchTarget: () => false,
			activeHandlersEqual: () => true,
			activeHandlersAtBlock: () => new AddressSet(),
		},
		reachableBlocksFromEntry: () => new AddressSet([0, 3]),
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
	} as unknown as IRFunction;

	assert.equal(reduceSequence(func), false);
	assert.equal(blocks.size, 3);
});

Deno.test('shared sequence edge declines a structurally large single statement', () => {
	const largeContinuation = t.expressionStatement(t.arrayExpression(
		Array.from({ length: 600 }, (_, value) => t.numericLiteral(value)),
	));
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('condition'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [largeContinuation],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = {
		id: 1,
		blocks,
		exceptions: {
			records: new AddressMap(),
			isCatchTarget: () => false,
			activeHandlersAtBlock: () => new AddressSet(),
			activeHandlersEqual: () => true,
		},
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
		setBlock() {
			throw new Error('oversized continuation must not be cloned');
		},
		rebuildPredecessorMap() {},
	} as unknown as IRFunction;

	assert.equal(reduceSharedSequenceEdge(func), false);
	assert.deepEqual(blocks.get(0)!.consequentAddresses, [1, 3]);
	assert.equal(blocks.get(3)!.body[0], largeContinuation);
});

Deno.test('linear reducers preserve a protected successor boundary', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.identifier('_param_1_0_'),
			)])],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('protectedWork'),
				[],
			))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const activeHandlersAtBlock = (address: number) =>
		new AddressSet(address === 1 ? [9] : []);
	const func = {
		id: 1,
		isNativeGenerator: false,
		isLoweredGenerator: false,
		guardedPhiMode: 'disabled',
		blocks,
		mergedBlocks: AddressGraph.fromBasicBlocks(blocks),
		ssa: {
			basicBlocks: new Map([
				[0, { consequentAddresses: [1], ssaInstructions: [] }],
				[1, { consequentAddresses: [2], ssaInstructions: [] }],
				[2, { consequentAddresses: [], ssaInstructions: [] }],
			]),
		},
		exceptions: {
			finallyRecords: new Map(),
			records: new Map(),
			isCatchTarget: () => false,
			activeHandlersAtBlock,
			activeHandlersEqual: (left: number, right: number) =>
				activeHandlersAtBlock(left).equals(
					activeHandlersAtBlock(right),
				),
		},
		reachableBlocksFromEntry: () => new AddressSet([0, 1, 2]),
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
		markMergedBlocks(_parent: number, child: number) {
			blocks.delete(child);
		},
	} as unknown as IRFunction;

	reduceSequence(func);
	assert.ok(blocks.has(0));
	assert.ok(blocks.has(1));
	assert.doesNotMatch(
		generate(t.program(blocks.get(0)!.body as t.Statement[])).code,
		/protectedWork/,
	);

	// Once a terminal arm has been inlined, reduceInlineTerminal must not move
	// the protected continuation into its `else` branch. Doing so gives one IR
	// block mixed handler ownership and leaves reduceTryCatch unable to isolate
	// the try body.
	const terminalGuard = t.ifStatement(
		t.identifier('done'),
		t.blockStatement([t.returnStatement(t.booleanLiteral(false))]),
	);
	blocks.get(0)!.body = [terminalGuard];
	assert.equal(reduceInlineTerminal(func), false);
	assert.equal(terminalGuard.alternate, null);
	assert.ok(blocks.has(1));
});

Deno.test('short-circuit collapse preserves a protected success arm', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('firstGuard'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('secondGuard'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('protectedWork'),
				[],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const activeHandlersAtBlock = (address: number) =>
		new AddressSet(address === 2 ? [9] : []);
	const rawBlocks = new Map(
		[...blocks].map(([address, block]) => [address, {
			consequentAddresses: [...block.consequentAddresses],
			instructions: [],
		}]),
	);
	const func = {
		blocks,
		ssa: {
			_func: { basicBlocks: rawBlocks, exceptionHandlers: [] },
			basicBlocks: new Map(),
		},
		exceptions: {
			activeHandlersAtBlock,
			activeHandlersEqual: (left: number, right: number) =>
				activeHandlersAtBlock(left).equals(
					activeHandlersAtBlock(right),
				),
		},
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
		markMergedBlocks(_parent: number, child: number) {
			blocks.delete(child);
		},
	} as unknown as IRFunction;

	assert.equal(reduceOrChain(func), false);
	assert.deepEqual([...blocks.keys()], [0, 1, 2, 3]);
});

Deno.test('shared leading phi consumes local source initializers', () => {
	const phi = t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
		t.identifier('r1_1'),
		t.identifier('r1_2'),
	]);
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('condition'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.stringLiteral('left'),
			)])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_2'),
				t.stringLiteral('right'),
			)])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_3'),
					phi,
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r1_3')],
				)),
			],
			branch: t.identifier('next'),
			consequentAddresses: [4, 5],
			kind: 'normal',
		}],
		[4, { address: 4, body: [], consequentAddresses: [], kind: 'normal' }],
		[5, { address: 5, body: [], consequentAddresses: [], kind: 'normal' }],
	]);
	const register = (version: number) => ({ index: 1, version });
	const mergedBlocks = new AddressGraph<number, number>(
		[...blocks.keys()].map((
			address,
		) => [address, new AddressSet([address])]),
	);
	const func = {
		blocks,
		mergedBlocks,
		ssa: {
			basicBlocks: new Map([[3, {
				ssaInstructions: [{
					instruction: 'Phi',
					destination: register(3),
					sources: new Map([
						[1, register(1)],
						[2, register(2)],
					]),
				}],
			}]]),
		},
		exceptions: { activeHandlersEqual: () => true },
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
	} as unknown as IRFunction;

	assert.equal(
		reduceSharedLeadingPhi(func, {
			nonTerminalOnly: true,
			skipClosureSources: true,
		}),
		true,
	);
	const rootDeclaration = blocks.get(0)!.body.at(-1)!;
	assert.equal(rootDeclaration.extra?.preserveAcrossBlocks, true);
	assert.match(
		generate(t.program(blocks.get(1)!.body as t.Statement[])).code,
		/r1_3 = "left"/,
	);
	assert.match(
		generate(t.program(blocks.get(2)!.body as t.Statement[])).code,
		/r1_3 = "right"/,
	);
	assert.doesNotMatch(
		generate(t.program(blocks.get(3)!.body as t.Statement[])).code,
		/%Phi/,
	);
});

Deno.test('shared leading phi supports a bounded high-fan-in join', () => {
	const predecessorCount = 17;
	const joinAddress = predecessorCount + 1;
	const sources = Array.from(
		{ length: predecessorCount },
		(_, index) => {
			const address = index + 1;
			const version = index + 1;
			return { address, version };
		},
	);
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('dispatch'),
			consequentAddresses: sources.map(({ address }) => address),
			kind: 'normal',
		}],
		...sources.map(({ address, version }): [number, IRBlock] => [
			address,
			{
				address,
				body: [t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier(`r1_${version}`),
					t.numericLiteral(version),
				)])],
				consequentAddresses: [joinAddress],
				kind: 'normal',
			},
		]),
		[joinAddress, {
			address: joinAddress,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_18'),
					t.callExpression(
						t.v8IntrinsicIdentifier('Phi'),
						sources.map(
							({ version }) => t.identifier(`r1_${version}`),
						),
					),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r1_18')],
				)),
			],
			branch: t.identifier('next'),
			consequentAddresses: [joinAddress + 1, joinAddress + 2],
			kind: 'normal',
		}],
		[joinAddress + 1, {
			address: joinAddress + 1,
			body: [],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[joinAddress + 2, {
			address: joinAddress + 2,
			body: [],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const register = (version: number) => ({ index: 1, version });
	const func = {
		blocks,
		mergedBlocks: new AddressGraph<number, number>(
			[...blocks.keys()].map((address) => [
				address,
				new AddressSet([address]),
			]),
		),
		ssa: {
			basicBlocks: new AddressMap([[joinAddress, {
				ssaInstructions: [{
					instruction: 'Phi',
					destination: register(18),
					sources: new AddressMap(
						sources.map(({ address, version }) => [
							address,
							register(version),
						]),
					),
				}],
			}]]),
		},
		exceptions: { activeHandlersEqual: () => true },
		predecessorsOf(target: number) {
			return new AddressSet(
				[...blocks].filter(([, candidate]) =>
					candidate.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		},
	} as unknown as IRFunction;

	assert.equal(
		reduceSharedLeadingPhi(func, { maxPredecessors: 16 }),
		false,
	);
	let applied:
		| { address: number; phiCount: number; predecessorCount: number }
		| undefined;
	assert.equal(
		reduceSharedLeadingPhi(func, {
			maxPredecessors: 64,
			onApplied: (info) => {
				applied = info;
			},
		}),
		true,
	);
	assert.deepEqual(applied, {
		address: joinAddress,
		phiCount: 1,
		predecessorCount,
	});
	assert.doesNotMatch(
		generate(t.program(blocks.get(joinAddress)!.body as t.Statement[]))
			.code,
		/%Phi/,
	);
});

Deno.test('recursive leading phi rollback disables widened pre-region rewrite', () => {
	type LeadingPhiHarness = {
		appliedWideLeadingPhi: boolean;
		blocks: AddressMap<IRBlock>;
		exceptions: { activeHandlersEqual: () => boolean };
		mergedBlocks: AddressGraph<number, number>;
		normalizeLeadingPhisForRegions(): boolean;
		predecessorsOf(target: number): AddressSet<number>;
		skipWideLeadingPhi: boolean;
		ssa: {
			basicBlocks: AddressMap<{
				ssaInstructions: unknown[];
			}>;
		};
	};
	const makeFunction = () => {
		const predecessorCount = 17;
		const joinAddress = predecessorCount + 1;
		const sources = Array.from(
			{ length: predecessorCount },
			(_, index) => {
				const address = index + 1;
				const version = index + 1;
				return { address, version };
			},
		);
		const blocks = new AddressMap<IRBlock>([
			[0, {
				address: 0,
				body: [],
				branch: t.identifier('dispatch'),
				consequentAddresses: sources.map(({ address }) => address),
				kind: 'normal',
			}],
			...sources.map(({ address, version }): [number, IRBlock] => [
				address,
				{
					address,
					body: [t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier(`r1_${version}`),
						t.numericLiteral(version),
					)])],
					consequentAddresses: [joinAddress],
					kind: 'normal',
				},
			]),
			[joinAddress, {
				address: joinAddress,
				body: [
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('r1_18'),
						t.callExpression(
							t.v8IntrinsicIdentifier('Phi'),
							sources.map(
								({ version }) => t.identifier(`r1_${version}`),
							),
						),
					)]),
					t.expressionStatement(t.callExpression(
						t.identifier('consume'),
						[t.identifier('r1_18')],
					)),
				],
				branch: t.identifier('next'),
				consequentAddresses: [joinAddress + 1, joinAddress + 2],
				kind: 'normal',
			}],
			[joinAddress + 1, {
				address: joinAddress + 1,
				body: [],
				consequentAddresses: [],
				kind: 'normal',
			}],
			[joinAddress + 2, {
				address: joinAddress + 2,
				body: [],
				consequentAddresses: [],
				kind: 'normal',
			}],
		]);
		const register = (version: number) => ({ index: 1, version });
		const func = Object.assign(Object.create(IRFunction.prototype), {
			appliedWideLeadingPhi: false,
			blocks,
			exceptions: { activeHandlersEqual: () => true },
			mergedBlocks: new AddressGraph<number, number>(
				[...blocks.keys()].map((address) => [
					address,
					new AddressSet([address]),
				]),
			),
			predecessorsOf(target: number) {
				return new AddressSet(
					[...blocks].filter(([, candidate]) =>
						candidate.consequentAddresses.includes(target)
					).map(([address]) => address),
				);
			},
			skipWideLeadingPhi: false,
			ssa: {
				basicBlocks: new AddressMap([[joinAddress, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: register(18),
						sources: new AddressMap(
							sources.map(({ address, version }) => [
								address,
								register(version),
							]),
						),
					}],
				}]]),
			},
		}) as LeadingPhiHarness;
		return { blocks, func, joinAddress };
	};

	const skipped = makeFunction();
	skipped.func.skipWideLeadingPhi = true;
	assert.equal(skipped.func.normalizeLeadingPhisForRegions(), false);
	assert.equal(skipped.func.appliedWideLeadingPhi, false);
	assert.match(
		generate(
			t.program(
				skipped.blocks.get(skipped.joinAddress)!.body as t.Statement[],
			),
		).code,
		/%Phi/,
	);

	const applied = makeFunction();
	assert.equal(applied.func.normalizeLeadingPhisForRegions(), true);
	assert.equal(applied.func.appliedWideLeadingPhi, true);
	assert.doesNotMatch(
		generate(
			t.program(
				applied.blocks.get(applied.joinAddress)!.body as t.Statement[],
			),
		).code,
		/%Phi/,
	);
});

function hermesAliasHarness(
	body: t.Statement[],
	register: SSARegister,
	successorUses: [number, number],
): IRFunction {
	const rawRegister = asRegister(register.index);
	const successorBlocks = successorUses.map((count, index) => {
		const address = index + 1;
		const instructions = Array.from({ length: count }, (_, useIndex) => ({
			...base,
			functionLocalOffset: address * 10 + useIndex,
			instruction: 'Mov',
			destination: asRegister(useIndex),
			source: rawRegister,
		} as Instruction));
		return [address, {
			address,
			instructions,
			ssaInstructions: instructions.map((instruction, useIndex) => ({
				...instruction,
				defs: {
					destination: phiRegister(useIndex, 1),
				},
				uses: {
					source: register,
				},
			})),
			consequentAddresses: [],
			predicate: null,
		}];
	}) as Array<[number, unknown]>;
	return {
		blocks: new AddressMap([[0, {
			address: 0,
			body,
			consequentAddresses: [],
			kind: 'normal',
		}]]),
		ssa: {
			_func: {
				basicBlocks: new AddressMap([
					[0, {
						address: 0,
						instructions: [],
						ssaInstructions: [],
						consequentAddresses: [1, 2],
						predicate: null,
					}],
					...successorBlocks,
				]),
				exceptionHandlers: [],
			},
			basicBlocks: new AddressMap([
				[0, {
					address: 0,
					instructions: [],
					ssaInstructions: [],
					consequentAddresses: [1, 2],
					predicate: null,
				}],
				...successorBlocks,
			]),
		},
	} as unknown as IRFunction;
}

Deno.test('HermesInternal branch alias deoptimizer inlines balanced ternary arms', () => {
	const register = phiRegister(9, 10);
	const alias = t.identifier('r9_10');
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.cloneNode(alias),
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('concat'),
				),
			),
		]),
		t.returnStatement(t.conditionalExpression(
			t.callExpression(t.identifier('test'), []),
			t.callExpression(
				t.memberExpression(t.cloneNode(alias), t.identifier('call')),
				[t.stringLiteral('[HTMLElement: '), t.identifier('name')],
			),
			t.callExpression(
				t.memberExpression(t.cloneNode(alias), t.identifier('call')),
				[t.stringLiteral('[object '), t.identifier('name')],
			),
		)),
	];
	const func = hermesAliasHarness(body, register, [1, 1]);

	assert.equal(reduceHermesInternalConditionalMemberAccesses(func), true);
	assert.equal(
		generate(t.program(func.blocks.get(0)!.body as t.Statement[])).code,
		'return test() ? HermesInternal.concat.call("[HTMLElement: ", name) : HermesInternal.concat.call("[object ", name);',
	);
});

Deno.test('HermesInternal branch alias deoptimizer rejects path-skewed uses', () => {
	const register = phiRegister(9, 10);
	const alias = t.identifier('r9_10');
	alias.extra = { sourceRegister: register };
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.cloneNode(alias),
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('concat'),
				),
			),
		]),
		t.returnStatement(t.conditionalExpression(
			t.callExpression(t.identifier('test'), []),
			t.logicalExpression(
				'&&',
				t.identifier('enabled'),
				t.callExpression(
					t.memberExpression(
						t.cloneNode(alias),
						t.identifier('call'),
					),
					[t.stringLiteral('[HTMLElement: '), t.identifier('name')],
				),
			),
			t.callExpression(
				t.memberExpression(t.cloneNode(alias), t.identifier('call')),
				[t.stringLiteral('[object '), t.identifier('name')],
			),
		)),
	];
	const func = hermesAliasHarness(body, register, [1, 1]);

	assert.equal(reduceHermesInternalConditionalMemberAccesses(func), false);
	assert.match(
		generate(t.program(func.blocks.get(0)!.body as t.Statement[])).code,
		/const r9_10 = HermesInternal\.concat/,
	);
});

Deno.test('HermesInternal branch alias deoptimizer requires branch liveness', () => {
	const register = phiRegister(9, 10);
	const alias = t.identifier('r9_10');
	alias.extra = { sourceRegister: register };
	const body: t.Statement[] = [
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.cloneNode(alias),
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('concat'),
				),
			),
		]),
		t.returnStatement(t.conditionalExpression(
			t.callExpression(t.identifier('test'), []),
			t.callExpression(
				t.memberExpression(t.cloneNode(alias), t.identifier('call')),
				[t.stringLiteral('[HTMLElement: '), t.identifier('name')],
			),
			t.callExpression(
				t.memberExpression(t.cloneNode(alias), t.identifier('call')),
				[t.stringLiteral('[object '), t.identifier('name')],
			),
		)),
	];
	const func = hermesAliasHarness(body, register, [1, 2]);

	assert.equal(reduceHermesInternalConditionalMemberAccesses(func), false);
	assert.match(
		generate(t.program(func.blocks.get(0)!.body as t.Statement[])).code,
		/const r9_10 = HermesInternal\.concat/,
	);
});

function cleanupLiftedBlocksForTest(
	blocks: AddressMap<IRBlock>,
	options: Parameters<IRFunction['cleanupLiftedBlocks']>[0] = {},
): void {
	const func = Object.assign(Object.create(IRFunction.prototype), {
		blocks,
		entryAddress: 0,
		exceptions: {
			finalizerCleanupPlan: () => ({
				removeRanges: [],
				replaceWithReturnRanges: [],
				embeddedCatchActions: [],
				enclosingEdgeActionCount: 0,
			}),
		},
		id: 0,
		options: {},
		referencedFunctionIds: new Map<number, number>(),
		ssa: { basicBlocks: new AddressMap() },
		yieldRetBlocks: new AddressMap(),
	}) as IRFunction;

	func.cleanupLiftedBlocks({
		hoistDestructuredParams: false,
		...options,
	});
}

function cleanupLiftedBodyCode(
	body: t.Statement[],
	options: Parameters<IRFunction['cleanupLiftedBlocks']>[0] = {},
): string {
	const blocks = new AddressMap<IRBlock>([[0, {
		address: 0,
		body,
		consequentAddresses: [],
		kind: 'normal',
	}]]);
	cleanupLiftedBlocksForTest(blocks, options);
	return generate(t.program(blocks.get(0)!.body as t.Statement[])).code;
}

Deno.test('structured exceptions drop unused bindings but keep effects', () => {
	const generatedDeclaration = (name: string, callee: string) => {
		const declaration = t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier(name),
				t.callExpression(t.identifier(callee), []),
			),
		]);
		declaration.extra = { preserveAcrossBlocks: true };
		return declaration;
	};
	assert.equal(
		cleanupLiftedBodyCode([
			t.tryStatement(
				t.blockStatement([
					generatedDeclaration('r1_1', 'effect'),
					t.returnStatement(t.numericLiteral(1)),
				]),
				null,
				t.blockStatement([
					generatedDeclaration('r2_1', 'cleanup'),
				]),
			),
		], { removeUnusedStructuredBindings: true }),
		'try {\n' +
			'  effect();\n' +
			'  return 1;\n' +
			'} finally {\n' +
			'  cleanup();\n' +
			'}',
	);
});

Deno.test('conditional cleanup preserves a value used by a successor block', () => {
	const declaration = t.variableDeclaration('let', [
		t.variableDeclarator(t.identifier('r11_9')),
	]);
	declaration.extra = { preserveAcrossBlocks: true };
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [
				declaration,
				t.ifStatement(
					t.identifier('condition'),
					t.blockStatement([
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.identifier('r11_9'),
							t.callExpression(t.identifier('fromProtected'), []),
						)),
					]),
					t.blockStatement([
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.identifier('r11_9'),
							t.identifier('fallback'),
						)),
					]),
				),
			],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.returnStatement(t.identifier('r11_9'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	cleanupLiftedBlocksForTest(blocks);

	assert.equal(
		generate(t.program(blocks.get(0)!.body as t.Statement[])).code,
		'const r11_9 = condition ? fromProtected() : fallback;',
	);
	assert.equal(
		generate(t.program(blocks.get(1)!.body as t.Statement[])).code,
		'return r11_9;',
	);
});

Deno.test('cleanup keeps effectful Phi sources before conditional selection', () => {
	const sourceRegister: SSARegister = {
		type: 'register',
		index: 2,
		version: 5,
	};
	const source = () => {
		const identifier = t.identifier('r2_5');
		identifier.extra = {
			sourceRegister,
			bindingOwnerFunctionId: 0,
		};
		return identifier;
	};
	const code = cleanupLiftedBodyCode([
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('_env_0_0')),
		]),
		t.variableDeclaration('const', [t.variableDeclarator(
			source(),
			t.callExpression(t.identifier('effect'), []),
		)]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier('_env_0_0'),
			source(),
		)),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r5_3'),
			source(),
		)]),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r5_5'),
			t.conditionalExpression(
				t.identifier('condition'),
				t.identifier('r5_3'),
				t.identifier('fallback'),
			),
		)]),
		t.returnStatement(t.identifier('r5_5')),
	]);

	const effects: string[] = [];
	const execute = new globalThis.Function(
		'effect',
		'condition',
		'fallback',
		code,
	) as (
		effect: () => string,
		condition: boolean,
		fallback: string,
	) => string;
	assert.equal(
		execute(
			() => {
				effects.push('effect');
				return 'current';
			},
			false,
			'pending',
		),
		'pending',
	);
	assert.deepEqual(effects, ['effect']);
});

Deno.test('object construction recrawls bindings before temp cleanup', () => {
	assert.equal(
		cleanupLiftedBodyCode([
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_2'),
					t.objectExpression([]),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r5_5'),
					t.callExpression(t.identifier('makeSessionId'), []),
				),
			]),
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.memberExpression(
					t.identifier('r1_2'),
					t.identifier('sessionId'),
				),
				t.identifier('r5_5'),
			)),
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.memberExpression(
					t.identifier('r1_2'),
					t.identifier('searchQueryId'),
				),
				t.nullLiteral(),
			)),
			t.expressionStatement(t.callExpression(
				t.memberExpression(
					t.thisExpression(),
					t.identifier('setSession'),
				),
				[t.identifier('ctx'), t.identifier('r1_2')],
			)),
		]),
		'this.setSession(ctx, {\n' +
			'  sessionId: makeSessionId(),\n' +
			'  searchQueryId: null\n' +
			'});',
	);
});

Deno.test('object construction keeps dependencies used by later properties', () => {
	assert.equal(
		cleanupLiftedBodyCode([
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r0_1'),
				t.objectExpression([]),
			)]),
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.identifier('input'),
			)]),
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r2_1'),
				t.numericLiteral(2),
			)]),
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r3_1'),
				t.binaryExpression(
					'+',
					t.identifier('r1_1'),
					t.identifier('r2_1'),
				),
			)]),
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.memberExpression(t.identifier('r0_1'), t.identifier('width')),
				t.identifier('r3_1'),
			)),
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r4_1'),
				t.binaryExpression(
					'*',
					t.numericLiteral(1.4),
					t.identifier('r3_1'),
				),
			)]),
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.memberExpression(
					t.identifier('r0_1'),
					t.identifier('height'),
				),
				t.identifier('r4_1'),
			)),
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r5_1'),
				t.binaryExpression(
					'/',
					t.identifier('r3_1'),
					t.numericLiteral(4),
				),
			)]),
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.memberExpression(
					t.identifier('r0_1'),
					t.identifier('cornerRadius'),
				),
				t.identifier('r5_1'),
			)),
			t.returnStatement(t.identifier('r0_1')),
		]),
		'return {\n' +
			'  width: input + 2,\n' +
			'  height: 1.4 * (input + 2),\n' +
			'  cornerRadius: (input + 2) / 4\n' +
			'};',
	);
});

Deno.test('HermesInternal.apply preserves call and construct semantics', () => {
	assert.equal(
		cleanupLiftedBodyCode([
			t.expressionStatement(t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('apply'),
				),
				[
					t.memberExpression(
						t.thisExpression(),
						t.identifier('waitFor'),
					),
					t.arrayExpression([t.spreadElement(t.identifier('args'))]),
					t.thisExpression(),
				],
			)),
		]),
		'this.waitFor(...args);',
	);
	assert.equal(
		cleanupLiftedBodyCode([
			t.returnStatement(t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('apply'),
				),
				[
					t.identifier('Widget'),
					t.arrayExpression([
						t.identifier('first'),
						t.spreadElement(t.identifier('rest')),
					]),
				],
			)),
		]),
		'return new Widget(first, ...rest);',
	);
	assert.equal(
		cleanupLiftedBodyCode([
			t.expressionStatement(t.callExpression(
				t.memberExpression(
					t.identifier('HermesInternal'),
					t.identifier('apply'),
				),
				[
					t.memberExpression(
						t.thisExpression(),
						t.identifier('waitFor'),
					),
					t.arrayExpression([]),
					t.identifier('other'),
				],
			)),
		]),
		'HermesInternal.apply(this.waitFor, [], other);',
	);
});

Deno.test({
	name:
		'native generator handles resume initializers and two-instruction cleanup',
	async fn() {
		const { IRFunction } = await import('./mod.ts');
		const func: Function = {
			id: 1,
			offset: 0,
			name: 'generatorWithCleanup',
			paramCount: 1,
			frameSize: 3,
			envSize: 0,
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
			basicBlocks: new Map([
				[
					0,
					block(0, [{
						...base,
						functionLocalOffset: 0,
						instruction: 'StartGenerator',
					}], [1]),
				],
				[
					1,
					block(1, [
						{
							...base,
							functionLocalOffset: 1,
							instruction: 'ResumeGenerator',
							destination: asRegister(0),
							isReturn: asRegister(1),
						},
						{
							...base,
							functionLocalOffset: 2,
							instruction: 'LoadConst',
							destination: asRegister(2),
							value: undefined,
						},
						{
							...base,
							functionLocalOffset: 3,
							instruction: 'JmpTrue',
							predicate: asRegister(1),
							relativeTarget: 18,
						},
					], [10, 20]),
				],
				[
					10,
					block(10, [
						{
							...base,
							functionLocalOffset: 10,
							instruction: 'CompleteGenerator',
						},
						{
							...base,
							functionLocalOffset: 11,
							instruction: 'Ret',
							argument: asRegister(0),
						},
					], []),
				],
				[
					20,
					block(20, [
						{
							...base,
							functionLocalOffset: 20,
							instruction: 'Mov',
							destination: asRegister(2),
							source: asRegister(0),
						},
						{
							...base,
							functionLocalOffset: 21,
							instruction: 'Mov',
							destination: asRegister(0),
							source: asRegister(2),
						},
					], [22]),
				],
				[
					22,
					block(22, [
						{
							...base,
							functionLocalOffset: 22,
							instruction: 'CompleteGenerator',
						},
						{
							...base,
							functionLocalOffset: 23,
							instruction: 'Ret',
							argument: asRegister(0),
						},
					], []),
				],
			]),
			trampolines: new Map(),
		};

		const ir = new IRFunction(
			{} as HBCFile,
			new SSAFunction(func),
		);

		assert.equal(ir.isNativeGenerator, true);
		assert.equal(ir.yieldEndBlocks.get(1)?.return, 20);
	},
});

Deno.test('read-only environment SSA handles propagate across blocks', () => {
	const func: Function = {
		id: 0,
		offset: 0,
		name: 'crossBlockEnvironment',
		paramCount: 1,
		frameSize: 4,
		envSize: 0,
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
		basicBlocks: new Map([
			[
				0,
				block(0, [
					{
						...base,
						functionLocalOffset: 0,
						instruction: 'GetParentEnvironment',
						destination: asRegister(1),
						levelIndex: 0,
					},
					{
						...base,
						functionLocalOffset: 1,
						instruction: 'LoadFromEnvironment',
						destination: asRegister(2),
						environment: asRegister(1),
						slotIndex: 27,
					},
					{
						...base,
						functionLocalOffset: 2,
						instruction: 'JmpTrue',
						predicate: asRegister(2),
						relativeTarget: 4,
					},
				], [3, 6]),
			],
			[
				3,
				block(3, [
					{
						...base,
						functionLocalOffset: 3,
						instruction: 'LoadFromEnvironment',
						destination: asRegister(3),
						environment: asRegister(1),
						slotIndex: 27,
					},
					{
						...base,
						functionLocalOffset: 4,
						instruction: 'Ret',
						argument: asRegister(3),
					},
				], []),
			],
			[
				6,
				block(6, [
					{
						...base,
						functionLocalOffset: 6,
						instruction: 'LoadConst',
						destination: asRegister(3),
						value: undefined,
					},
					{
						...base,
						functionLocalOffset: 7,
						instruction: 'Ret',
						argument: asRegister(3),
					},
				], []),
			],
		]),
		trampolines: new Map(),
	};

	const ir = new IRFunction(
		{ functions: [func] } as HBCFile,
		new SSAFunction(func),
		{ cfgReducer: { mode: 'recursive', materialize: false } },
	);
	const emitted = [...ir.blocks.values()].flatMap((block) => [
		...(block.body as t.Statement[]).map((statement) =>
			generate(statement).code
		),
		...(block.branch ? [generate(block.branch as t.Expression).code] : []),
	]).join('\n');

	assert.doesNotMatch(emitted, /\br1_\d+\b/);
	assert.equal(
		(emitted.match(/%GetParentEnvironment\(0\)/g) ?? []).length,
		2,
	);
});

Deno.test(
	'latch-tested natural loop preserves its terminalized header',
	() => {
		const header = 0x34;
		const latch = 0x41;
		const exit = 0x68;
		const blocks = new AddressMap<IRBlock>([
			[0, {
				address: 0,
				body: [],
				branch: t.identifier('enter'),
				consequentAddresses: [header, exit],
			}],
			[header, {
				address: header,
				body: [
					t.expressionStatement(
						t.callExpression(t.identifier('work'), []),
					),
				],
				branch: t.identifier('finish'),
				consequentAddresses: [0x4b, 0x60],
			}],
			[latch, {
				address: latch,
				body: [
					t.expressionStatement(
						t.updateExpression('++', t.identifier('i')),
					),
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('r1_9'),
						t.memberExpression(
							t.identifier('source'),
							t.identifier('colorStops'),
						),
					)]),
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('r1_10'),
						t.memberExpression(
							t.identifier('r1_9'),
							t.identifier('length'),
						),
					)]),
				],
				branch: t.binaryExpression(
					'<',
					t.identifier('i'),
					t.identifier('r1_10'),
				),
				consequentAddresses: [exit, header],
			}],
			[0x4b, {
				address: 0x4b,
				body: [t.expressionStatement(
					t.callExpression(t.identifier('guardOne'), []),
				)],
				branch: t.identifier('secondGuard'),
				consequentAddresses: [0x52, 0x58],
			}],
			[0x52, {
				address: 0x52,
				body: [t.expressionStatement(
					t.callExpression(t.identifier('guardTwo'), []),
				)],
				branch: t.identifier('thirdGuard'),
				consequentAddresses: [latch, 0x58],
			}],
			[0x58, {
				address: 0x58,
				body: [t.expressionStatement(
					t.callExpression(t.identifier('filterWork'), []),
				)],
				branch: t.identifier('accept'),
				consequentAddresses: [latch, 0x60],
			}],
			[0x60, {
				address: 0x60,
				body: [t.expressionStatement(
					t.callExpression(t.identifier('side'), []),
				)],
				consequentAddresses: [latch],
			}],
			[exit, {
				address: exit,
				body: [t.returnStatement(t.identifier('done'))],
				consequentAddresses: [],
			}],
		]);
		const predecessorsOf = (target: number) =>
			new AddressSet(
				[...blocks].filter(([, block]) =>
					block.consequentAddresses.includes(target)
				).map(([address]) => address),
			);
		const mergedBlocks = new AddressGraph<number, number>(
			[...blocks.keys()].map((address) => [
				address,
				new AddressSet([address]),
			]),
		);
		const basicBlocks = new Map(
			[...blocks].map(([address, block]) => [
				address,
				{
					consequentAddresses: [...block.consequentAddresses],
					instructions: [],
					ssaInstructions: [],
				},
			]),
		);
		const func = {
			id: 1,
			entryAddress: 0,
			blocks,
			mergedBlocks,
			ssa: {
				basicBlocks,
				_func: { basicBlocks, exceptionHandlers: [] },
			},
			file: { version: 98 },
			options: { cfgReducer: { mode: 'recursive' } },
			exceptions: {
				records: new Map(),
				finallyRecords: new Map(),
				activeHandlersEqual: () => true,
				activeHandlersAtBlock: () => new AddressSet(),
				isCatchTarget: () => false,
				activeHandlersParent: () => true,
				liveHandlers: () => new AddressSet(),
				notifyBlocksMerged: () => {},
				catchMapForBlocks: () => new AddressMap(),
			},
			reachableBlocksFromEntry() {
				const reachable = new AddressSet<number>();
				const pending = [0];
				while (pending.length > 0) {
					const address = pending.pop()!;
					if (reachable.has(address)) continue;
					reachable.add(address);
					pending.push(
						...(blocks.get(address)?.consequentAddresses ?? []),
					);
				}
				return reachable;
			},
			predecessorsOf,
			markMergedBlocks(parent: number, child: number) {
				blocks.delete(child);
				mergedBlocks.set(
					parent,
					new AddressSet([
						...(mergedBlocks.get(parent) ?? []),
						...(mergedBlocks.get(child) ?? []),
						child,
					]),
				);
				mergedBlocks.delete(child);
			},
			setBlock(address: number, block: IRBlock) {
				blocks.set(address, block);
				if (!mergedBlocks.has(address)) {
					mergedBlocks.set(address, new AddressSet([address]));
				}
			},
			rebuildPredecessorMap() {},
			deleteBlock(address: number) {
				mergedBlocks.delete(address);
				return blocks.delete(address);
			},
		} as unknown as IRFunction;

		assert.equal(reduceNaturalLoop(func), true);
		assert.ok(blocks.has(header));
		const loop = blocks.get(header)?.body[0] as t.Statement | undefined;
		assert.ok(t.isWhileStatement(loop));
		assert.ok(t.isBlockStatement(loop.body));
		const loopCode = generate(loop).code;
		for (
			const call of ['work', 'guardOne', 'guardTwo', 'filterWork', 'side']
		) {
			assert.equal(
				(loopCode.match(new RegExp(`${call}\\(\\)`, 'g')) ?? []).length,
				1,
				loopCode,
			);
		}
		assert.equal((loopCode.match(/source\.colorStops/g) ?? []).length, 1);
		assert.equal((loopCode.match(/\.length/g) ?? []).length, 1);
		assert.equal((loopCode.match(/i\+\+/g) ?? []).length, 1);
	},
);

Deno.test('for-of recovery preserves a phi-lowered exhaustion carry', () => {
	const tuple = (
		names: string[],
		intrinsic: string,
		args: t.Expression[],
	) => t.variableDeclaration('const', [t.variableDeclarator(
		t.arrayPattern(names.map((name) => t.identifier(name))),
		t.callExpression(t.v8IntrinsicIdentifier(intrinsic), args),
	)]);
	const preheader = {
		address: 0,
		body: [tuple(
			['r19_7', 'r18_18'],
			'IteratorBegin',
			[t.identifier('items')],
		)],
		consequentAddresses: [1],
	} as IRBlock;
	const loopStatements: t.Statement[] = [
		tuple(
			['r20_4', 'r19_9'],
			'IteratorNext',
			[t.identifier('r19_8'), t.identifier('r18_18')],
		),
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r21_3'),
			t.identifier('r19_9'),
		)]),
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier('r17_13'),
			t.identifier('r2_2'),
		)),
		t.ifStatement(
			t.binaryExpression(
				'===',
				t.identifier('r21_3'),
				t.identifier('undefined'),
			),
			t.blockStatement([t.breakStatement()]),
		),
		t.expressionStatement(t.callExpression(
			t.identifier('consume'),
			[t.identifier('r20_4')],
		)),
	];
	const blocks = new AddressMap<IRBlock>([
		[0, preheader],
		[1, {
			address: 1,
			body: loopStatements,
			consequentAddresses: [1, 2],
		}],
		[2, {
			address: 2,
			body: [t.returnStatement()],
			consequentAddresses: [],
		}],
	]);
	const func = {
		blocks,
		predecessorsOf(address: number) {
			return address === 1
				? new AddressSet([0, 1])
				: address === 2
				? new AddressSet([1])
				: new AddressSet();
		},
		ssa: {
			_func: {
				basicBlocks: new AddressMap(),
				exceptionHandlers: [],
			},
		},
	} as unknown as IRFunction;

	const result = tryBuildForInOrOfStatement(
		func,
		1,
		new AddressSet([1]),
		loopStatements,
		2,
	);
	assert.ok(result);
	assert.match(generate(result.loop).code, /for \(const r20_4 of items\)/);
	assert.equal(
		generate(t.program(result.exitStatements)).code,
		'r17_13 = r2_2;',
	);
	assert.equal(preheader.body.length, 0);
});

Deno.test('a mutating init is not inlined across a read of what it mutates', () => {
	// `const old = i--` substituted into its use would move the decrement past
	// the read of `i` in the statement before it, so the pair `[i, old]` would
	// report the post-update value for both halves.
	const blocks = new AddressMap<IRBlock>([[0, {
		address: 0,
		body: [
			t.variableDeclaration('let', [t.variableDeclarator(
				t.identifier('r2_1'),
				t.memberExpression(t.identifier('o'), t.identifier('count')),
			)]),
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.updateExpression('--', t.identifier('r2_1'), false),
			)]),
			t.returnStatement(
				t.arrayExpression([t.identifier('r2_1'), t.identifier('r1_1')]),
			),
		],
		consequentAddresses: [],
		kind: 'normal',
	}]]);
	cleanupLiftedBlocksForTest(blocks);
	const code = generate(
		t.program(blocks.get(0)!.body as t.Statement[]),
	).code;
	assert.match(code, /const r1_1 = r2_1--;/);
	assert.doesNotMatch(code, /r2_1--\s*\]/);
});
