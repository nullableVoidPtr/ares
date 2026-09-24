import { strict as assert } from 'node:assert';
import generate from '@babel/generator';
import traverse from '@babel/traverse';
import * as t from '@babel/types';
import type { IRBlock } from '../../../ast/mod.ts';
import type { IRFunction } from '../../mod.ts';
import type { SSARegister } from '../../../../ssa.ts';
import { AddressGraph } from '../../../../utils/graph.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import { recoverDescriptors } from '../descriptors/mod.ts';
import { ImmutableCFG } from '../immutableCFG.ts';
import type { Region } from '../regions/region.ts';
import {
	emitRegionToAST,
	foldGuardedLoopExitTests,
	simplifyForwardExitLabels,
} from './emitRegion.ts';

function register(index: number, version: number): SSARegister {
	return { type: 'register', index, version };
}

function conditionalPhiFixture(options: {
	test: t.Expression;
	consequent: SSARegister;
	alternate: SSARegister;
	headerBody?: t.Statement[];
	consequentBody?: t.Statement[];
	alternateBody?: t.Statement[];
}) {
	const target = register(0, 1);
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: options.headerBody ?? [],
			branch: options.test,
			consequentAddresses: [2, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: options.consequentBody ?? [],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: options.alternateBody ?? [],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r0_1'),
						t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
					),
				]),
				t.returnStatement(t.identifier('r0_1')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[3, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: target,
						sources: new AddressMap([
							[1, options.consequent],
							[2, options.alternate],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const conditionalRegion: Region = {
		kind: 'if',
		header: 0,
		test: t.cloneNode(options.test, true),
		consequent: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([1]),
		},
		alternate: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		join: 3,
		conditionalValue: {
			kind: 'conditionalPhi',
			branch: 0,
			consequentEntry: 1,
			alternateEntry: 2,
			join: 3,
			forms: ['shortcut', 'ternary'],
		},
		sourceBlocks: new AddressSet([0, 1, 2]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [conditionalRegion, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([3]),
		}],
		sourceBlocks: new AddressSet([0, 1, 2, 3]),
	};
	return emitRegionToAST(region, cfg, recoverDescriptors(cfg));
}

function emittedCode(result: ReturnType<typeof conditionalPhiFixture>): string {
	assert.deepEqual(result.diagnostics, []);
	return generate(result.program).code;
}

Deno.test('switch case emission gives each case a lexical block', () => {
	const declaration = (value: string) =>
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r37_16'),
				t.stringLiteral(value),
			),
		]);
	const blocks = new AddressMap<IRBlock>([
		[1, {
			address: 1,
			body: [declaration('case')],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [declaration('default')],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 1,
		mergedBlocks,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const region: Region = {
		kind: 'switch',
		header: 0,
		discriminant: t.identifier('tag'),
		cases: [{
			test: t.stringLiteral('case'),
			target: 1,
			body: {
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([1]),
			},
		}],
		defaultTarget: 2,
		defaultBody: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([0, 1, 2]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	traverse(t.file(result.program), {});
	const code = generate(result.program).code;
	assert.match(code, /case "case":\s*\{\s*const r37_16 = "case";\s*\}/);
	assert.match(code, /default:\s*\{\s*const r37_16 = "default";\s*\}/);
});

Deno.test('catch Phis track state before each protected exception point', () => {
	const phi = (
		destination: SSARegister,
		sources: Array<[number, SSARegister]>,
	) => ({
		instruction: 'Phi' as const,
		destination,
		sources: new AddressMap(sources),
	});
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r0_1'),
					t.identifier('initial'),
				),
			])],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r0_2'),
					t.callExpression(t.identifier('risky'), []),
				),
			])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_3'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('r0_1'),
					]),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('caught'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
			],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_4'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('r0_2'),
						t.identifier('r0_3'),
					]),
				)]),
				t.returnStatement(t.identifier('r0_4')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		id: 1,
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[2, {
					ssaInstructions: [phi(register(0, 3), [[
						1,
						register(0, 1),
					]])],
				}],
				[3, {
					ssaInstructions: [phi(register(0, 4), [
						[1, register(0, 2)],
						[2, register(0, 3)],
					])],
				}],
			]),
		},
		exceptions: {
			records: new AddressMap([
				[2, { protectedBlocks: new AddressSet([1]) }],
			]),
		},
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const region: Region = {
		kind: 'sequence',
		regions: [
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([0]) },
			{
				kind: 'tryCatch',
				body: {
					kind: 'basic',
					body: [],
					sourceBlocks: new AddressSet([1]),
				},
				handler: {
					kind: 'basic',
					body: [],
					sourceBlocks: new AddressSet([2]),
				},
				handlerAddress: 2,
				protectedBlocks: new AddressSet([1]),
				sourceBlocks: new AddressSet([1, 2]),
			},
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([3]) },
		],
		sourceBlocks: new AddressSet([0, 1, 2, 3]),
	};
	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.doesNotMatch(code, /%Phi/);
	assert.doesNotMatch(code, /r0_3/);
	assert.match(code, /catch \(_e\) \{[\s\S]*r0_4 = r0_1;/);
});

Deno.test('catch Phi provenance survives merged CFG block addresses', () => {
	const source = register(0, 1);
	const target = register(0, 3);
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [10],
			kind: 'normal',
			sourceAddresses: new AddressSet([0]),
		}],
		[10, {
			address: 10,
			body: [t.expressionStatement(
				t.callExpression(t.identifier('risky'), []),
			)],
			consequentAddresses: [30],
			kind: 'normal',
			sourceAddresses: new AddressSet([1]),
		}],
		[20, {
			address: 20,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_3'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('r0_1'),
					]),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('caught'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
			],
			consequentAddresses: [30],
			kind: 'normal',
			sourceAddresses: new AddressSet([2]),
		}],
		[30, {
			address: 30,
			body: [t.returnStatement(t.identifier('r0_3'))],
			consequentAddresses: [],
			kind: 'normal',
			sourceAddresses: new AddressSet([3]),
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>([
		[0, new AddressSet([0])],
		[10, new AddressSet([1])],
		[20, new AddressSet([2])],
		[30, new AddressSet([3])],
	]);
	const func = {
		id: 1,
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[0, {
					ssaInstructions: [{
						instruction: 'LoadConst',
						destination: source,
						value: undefined,
						defs: { destination: source },
						uses: {},
					}],
				}],
				[2, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: target,
						sources: new AddressMap([[1, source]]),
					}],
				}],
			]),
		},
		exceptions: {
			records: new AddressMap([
				[2, { protectedBlocks: new AddressSet([1]) }],
			]),
		},
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	assert.deepEqual([...cfg.ownersOfSource(1)], [10]);
	assert.equal(cfg.blocks.get(20)?.ssaInstructions.length, 1);
	assert.deepEqual(cfg.exceptionalEdges(), [{
		from: 10,
		to: 20,
		kind: 'exceptional',
	}]);
	const region: Region = {
		kind: 'sequence',
		regions: [
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([0]) },
			{
				kind: 'tryCatch',
				body: {
					kind: 'basic',
					body: [],
					sourceBlocks: new AddressSet([10]),
				},
				handler: {
					kind: 'basic',
					body: [],
					sourceBlocks: new AddressSet([20]),
				},
				handlerAddress: 20,
				protectedBlocks: new AddressSet([10]),
				sourceBlocks: new AddressSet([10, 20]),
			},
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([30]) },
		],
		sourceBlocks: new AddressSet([0, 10, 20, 30]),
	};
	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.doesNotMatch(code, /%Phi|r0_1/);
	assert.ok(code.indexOf('r0_3 = undefined') < code.indexOf('risky()'));
});

Deno.test('fallback finalizer candidates do not re-emit covered Phis', () => {
	const source = register(0, 1);
	const exceptionalSource = register(0, 2);
	const target = register(0, 3);
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r0_1'),
				t.identifier('normalValue'),
			)])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_3'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('r0_1'),
						t.identifier('r0_2'),
					]),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('track'),
					[t.identifier('r0_3')],
				)),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		id: 1,
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[3, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: target,
						sources: new AddressMap([
							[0, source],
							[2, exceptionalSource],
						]),
					}],
				}],
			]),
		},
		exceptions: {
			records: new AddressMap([
				[2, { protectedBlocks: new AddressSet([0]) }],
			]),
		},
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const region: Region = {
		kind: 'tryFinally',
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([0]),
		},
		finalizer: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		handlerAddress: 2,
		protectedBlocks: new AddressSet([0]),
		normalExit: 3,
		normalExitCandidates: [3],
		sourceBlocks: new AddressSet([0, 2]),
	};
	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.doesNotMatch(code, /%Phi|const r0_3/);
	assert.match(code, /let r0_3;/);
	assert.match(code, /r0_3 = r0_1;/);
	assert.equal((code.match(/track\(r0_3\)/g) ?? []).length, 1);
});

Deno.test('canonical finalizer Phi state feeds the represented copy target', () => {
	const initial = register(0, 1);
	const caught = register(0, 2);
	const copyTarget = register(0, 3);
	const canonicalTarget = register(0, 4);
	const phi = (name: string) =>
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier(name),
			t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
		)]);
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r0_1'),
				t.identifier('initialTask'),
			)])],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('risky'),
				[],
			))],
			consequentAddresses: [30],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [
				phi('r0_2'),
				t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('Catch'),
					[],
				)),
				t.expressionStatement(t.callExpression(
					t.identifier('riskyCatch'),
					[],
				)),
			],
			consequentAddresses: [30],
			kind: 'normal',
		}],
		[20, {
			address: 20,
			body: [phi('r0_4'), t.throwStatement(t.identifier('error'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[30, {
			address: 30,
			body: [
				phi('r0_3'),
				t.expressionStatement(t.callExpression(
					t.identifier('endTask'),
					[t.identifier('r0_3')],
				)),
			],
			consequentAddresses: [40],
			kind: 'normal',
		}],
		[40, {
			address: 40,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		id: 1,
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[10, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: caught,
						sources: new AddressMap([[1, initial]]),
					}],
				}],
				[20, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: canonicalTarget,
						sources: new AddressMap([
							[1, initial],
							[10, caught],
						]),
					}],
				}],
				[30, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: copyTarget,
						sources: new AddressMap([
							[1, initial],
							[10, caught],
						]),
					}],
				}],
			]),
		},
		exceptions: {
			records: new AddressMap([
				[10, { protectedBlocks: new AddressSet([1]) }],
				[20, { protectedBlocks: new AddressSet([1, 10]) }],
			]),
		},
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const tryCatch: Region = {
		kind: 'tryCatch',
		body: { kind: 'basic', body: [], sourceBlocks: new AddressSet([1]) },
		handler: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([10]),
		},
		handlerAddress: 10,
		protectedBlocks: new AddressSet([1]),
		sourceBlocks: new AddressSet([1, 10]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [{
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([0]),
		}, {
			kind: 'tryFinally',
			body: tryCatch,
			finalizer: {
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([30]),
			},
			handlerAddress: 20,
			protectedBlocks: new AddressSet([1, 10]),
			normalExit: 40,
			normalExitCandidates: [40],
			sourceBlocks: new AddressSet([1, 10, 30]),
		}, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([40]),
		}],
		sourceBlocks: new AddressSet([0, 1, 10, 30, 40]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.doesNotMatch(code, /%Phi|r0_4/);
	assert.ok(code.indexOf('r0_3 = r0_1') < code.indexOf('risky()'));
	assert.ok(code.indexOf('r0_3 = r0_2') < code.indexOf('riskyCatch()'));
	assert.equal((code.match(/endTask\(r0_3\)/g) ?? []).length, 1);
});

Deno.test('finalizer copy suppression retains escaping definition chains', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('work'),
				[],
			))],
			consequentAddresses: [10],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r4_26'),
					t.identifier('completionRecord'),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r4_27'),
					t.identifier('r4_26'),
				)]),
			],
			branch: t.identifier('takeTrue'),
			consequentAddresses: [11, 12],
			kind: 'normal',
		}],
		[11, {
			address: 11,
			body: [t.returnStatement(t.identifier('r4_27'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[12, {
			address: 12,
			body: [t.returnStatement(t.booleanLiteral(false))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[20, {
			address: 20,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r4_29'),
				t.identifier('completionRecord'),
			)])],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const descriptors = recoverDescriptors(cfg);
	const descriptor = {
		handler: 20,
		kind: 'finally' as const,
		protectedBlocks: new AddressSet([0]),
		protectedEntries: new AddressSet([0]),
		catchBody: null,
		canonicalFinallyAddress: 20,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet([10]),
		finallyBodyBlocks: [20],
		boundedFinallyBodyBlocks: [20],
		finallyCopies: [{
			canonical: 20,
			copyRoot: 10,
			next: null,
			kind: 'abruptExit' as const,
			skipRanges: [{ block: 10, start: 0, end: 2 }],
		}],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	descriptors.exceptions.handlers = [descriptor];
	descriptors.exceptions.handlerByAddress = new Map([[20, descriptor]]);
	const region: Region = {
		kind: 'sequence',
		regions: [{
			kind: 'tryFinally',
			body: {
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([0]),
			},
			finalizer: {
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([20]),
			},
			handlerAddress: 20,
			protectedBlocks: new AddressSet([0]),
			normalExit: 10,
			finallyCopyKinds: ['abruptExit:0xa'],
			sourceBlocks: new AddressSet([0, 20]),
		}, {
			kind: 'if',
			header: 10,
			test: t.identifier('takeTrue'),
			consequent: {
				kind: 'terminalReference',
				entry: 11,
				sourceBlocks: new AddressSet(),
			},
			alternate: {
				kind: 'terminalReference',
				entry: 12,
				sourceBlocks: new AddressSet(),
			},
			sourceBlocks: new AddressSet([10]),
		}],
		sourceBlocks: new AddressSet([0, 10, 11, 12, 20]),
	};

	const result = emitRegionToAST(region, cfg, descriptors);
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(
		code,
		/const r4_26 = completionRecord;\s*const r4_27 = r4_26;\s*if \(takeTrue\)/,
	);
});

Deno.test('forward-exit labels become nested guard conditions', () => {
	const statements = simplifyForwardExitLabels([
		t.labeledStatement(
			t.identifier('cfg_exit'),
			t.blockStatement([
				t.expressionStatement(
					t.callExpression(t.identifier('setup'), []),
				),
				t.ifStatement(
					t.identifier('first'),
					t.breakStatement(t.identifier('cfg_exit')),
				),
				t.ifStatement(
					t.identifier('second'),
					t.breakStatement(t.identifier('cfg_exit')),
				),
				t.expressionStatement(
					t.callExpression(t.identifier('tail'), []),
				),
			]),
		),
	]);

	const code = generate(t.program(statements)).code;
	assert.doesNotMatch(code, /cfg_exit/);
	assert.equal(
		code,
		'setup();\nif (!first) {\n  if (!second) {\n    tail();\n  }\n}',
	);
});

Deno.test('nested forward labels expose exits to their parent scope', () => {
	const statements = simplifyForwardExitLabels([
		t.labeledStatement(
			t.identifier('outer'),
			t.blockStatement([
				t.labeledStatement(
					t.identifier('inner'),
					t.blockStatement([
						t.ifStatement(
							t.identifier('leaveOuter'),
							t.breakStatement(t.identifier('outer')),
						),
						t.ifStatement(
							t.identifier('leaveInner'),
							t.breakStatement(t.identifier('inner')),
						),
						t.expressionStatement(
							t.callExpression(t.identifier('innerTail'), []),
						),
					]),
				),
				t.expressionStatement(
					t.callExpression(t.identifier('outerTail'), []),
				),
			]),
		),
	]);

	const code = generate(t.program(statements)).code;
	assert.doesNotMatch(code, /outer:|inner:|break outer|break inner/);
	assert.match(code, /if \(!leaveOuter\)/);
	assert.match(code, /if \(!leaveInner\)/);
	assert.match(code, /outerTail\(\)/);
});

Deno.test('forward-label continuations preserve colliding register scopes', () => {
	const registerDeclaration = (value: string) =>
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r13_4'),
				t.stringLiteral(value),
			),
		]);
	const statements = simplifyForwardExitLabels([
		t.labeledStatement(
			t.identifier('exit'),
			t.blockStatement([
				t.ifStatement(
					t.identifier('branch'),
					t.blockStatement([
						registerDeclaration('arm'),
						t.ifStatement(
							t.identifier('leave'),
							t.breakStatement(t.identifier('exit')),
						),
					]),
				),
				registerDeclaration('continuation'),
			]),
		),
	]);

	const code = generate(t.program(statements)).code;
	assert.doesNotMatch(code, /exit:|break exit/);
	assert.match(
		code,
		/const r13_4 = "arm";[\s\S]*\{\s*const r13_4 = "continuation";/,
	);
});

Deno.test('shared loop-terminal values do not invent function boundaries', () => {
	const statements = simplifyForwardExitLabels([
		t.labeledStatement(
			t.identifier('loop_body_exit'),
			t.blockStatement([
				t.whileStatement(
					t.callExpression(t.identifier('next'), []),
					t.blockStatement([
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.identifier('result'),
							t.identifier('early'),
						)),
						t.breakStatement(t.identifier('loop_body_exit')),
					]),
				),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.identifier('result'),
					t.identifier('sharedTerminal'),
				)),
			]),
		),
	]);

	const code = generate(t.program(statements)).code;
	assert.match(code, /loop_body_exit:/);
	assert.match(code, /break loop_body_exit/);
	assert.match(code, /result = sharedTerminal/);
	assert.doesNotMatch(code, /=>/);
});

Deno.test('recursive Region emission reconstructs shortcut Phis', () => {
	const result = conditionalPhiFixture({
		test: t.identifier('r0_2'),
		consequent: register(1, 2),
		alternate: register(0, 2),
	});
	assert.equal(
		emittedCode(result),
		'const r0_1 = r0_2 && r1_2;\nreturn r0_1;',
	);
});

Deno.test('recursive Region emission reconstructs ternary Phis', () => {
	const result = conditionalPhiFixture({
		test: t.identifier('condition'),
		consequent: register(1, 2),
		alternate: register(2, 2),
	});
	assert.equal(
		emittedCode(result),
		'const r0_1 = condition ? r1_2 : r2_2;\nreturn r0_1;',
	);
});

Deno.test('recursive Region emission reconstructs optional-access Phis', () => {
	const receiver = t.identifier('r3_0');
	const result = conditionalPhiFixture({
		test: t.binaryExpression(
			'!=',
			t.cloneNode(receiver),
			t.nullLiteral(),
		),
		consequent: register(1, 2),
		alternate: register(2, 2),
		consequentBody: [
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_2'),
					t.memberExpression(
						t.cloneNode(receiver),
						t.identifier('value'),
					),
				),
			]),
		],
		alternateBody: [
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r2_2'),
					t.identifier('undefined'),
				),
			]),
		],
	});
	assert.equal(
		emittedCode(result),
		'const r0_1 = r3_0?.value;\nreturn r0_1;',
	);
});

Deno.test('recursive conditional Phi synthesis defers pattern bindings', () => {
	const result = conditionalPhiFixture({
		test: t.identifier('r0_0'),
		consequent: register(1, 2),
		alternate: register(2, 2),
		headerBody: [
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.arrayPattern([t.identifier('r0_0')]),
					t.identifier('input'),
				),
			]),
		],
	});
	const code = emittedCode(result);
	assert.match(code, /let r0_1;/);
	assert.match(code, /if \(r0_0\)/);
	assert.doesNotMatch(code, /const r0_1 = r0_0 \?/);
});

Deno.test('recursive conditional Phis retain provenance across arm cleanup', () => {
	const result = conditionalPhiFixture({
		test: t.identifier('condition'),
		consequent: register(1, 2),
		alternate: register(2, 2),
		headerBody: [
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('condition'),
					t.memberExpression(
						t.identifier('globalThis'),
						t.identifier('nativePerformanceNow'),
					),
				),
			]),
		],
		consequentBody: [
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('callee'),
					t.identifier('nativePerformanceNow'),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('receiver'),
					t.identifier('undefined'),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_2'),
					t.callExpression(
						t.memberExpression(
							t.identifier('callee'),
							t.identifier('call'),
						),
						[t.identifier('receiver')],
					),
				),
			]),
		],
		alternateBody: [
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('date'),
					t.identifier('Date'),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('now'),
					t.memberExpression(
						t.identifier('date'),
						t.identifier('now'),
					),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r2_2'),
					t.callExpression(
						t.memberExpression(
							t.identifier('now'),
							t.identifier('call'),
						),
						[t.identifier('date')],
					),
				),
			]),
		],
	});
	const ifIndex = result.program.body.findIndex((statement) =>
		t.isIfStatement(statement)
	);
	assert.notEqual(ifIndex, -1);
	const declaration = result.program.body[ifIndex - 1];
	assert.equal(
		(declaration as { extra?: { isPotentialConditionalValue?: boolean } })
			.extra?.isPotentialConditionalValue,
		true,
	);
	assert.equal(
		t.isVariableDeclaration(declaration) &&
			t.isIdentifier(declaration.declarations[0]?.id)
			? declaration.declarations[0].id.name
			: null,
		'r0_1',
	);
});

Deno.test('recursive if arms consume Phi actions on their entry edge', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('condition'),
			consequentAddresses: [2, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r0_1'),
						t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
					),
				]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r0_1')],
				)),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[1, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: register(0, 1),
						sources: new AddressMap([
							[0, register(1, 1)],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const region: Region = {
		kind: 'if',
		header: 0,
		test: t.identifier('condition'),
		consequent: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([1]),
		},
		alternate: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		join: 0,
		sourceBlocks: new AddressSet([0, 1, 2]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(code, /r0_1 = r1_1;/);
	assert.ok(code.indexOf('r0_1 = r1_1;') < code.indexOf('consume\(r0_1\)'));
});

Deno.test('folded guard chains discard equivalent shared-arm Phi copies', () => {
	const target = register(0, 1);
	const sharedValue = register(1, 1);
	const otherValue = register(2, 1);
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('first'),
			consequentAddresses: [2, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('second'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r0_1'),
						t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
					),
				]),
				t.returnStatement(t.identifier('r0_1')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			consequentAddresses: [2],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[2, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: target,
						sources: new AddressMap([
							[0, sharedValue],
							[1, sharedValue],
							[3, otherValue],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const conditional: Region = {
		kind: 'if',
		header: 0,
		predicateBlocks: new AddressSet([0, 1]),
		branchEdges: {
			consequent: { from: 1, to: 3, kind: 'normal' },
			alternate: { from: 0, to: 2, kind: 'normal' },
		},
		test: t.logicalExpression(
			'&&',
			t.identifier('first'),
			t.identifier('second'),
		),
		consequent: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([3]),
		},
		alternate: {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		},
		join: 2,
		sourceBlocks: new AddressSet([0, 1, 3]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [conditional, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		}],
		sourceBlocks: new AddressSet([0, 1, 2, 3]),
	};
	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(
		code,
		/const r0_1 = first && second \? r2_1 : r1_1;/,
	);
});

Deno.test('folded loop exits preserve shared condition dependencies', () => {
	const statements = [
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r1_1'),
				t.callExpression(
					t.v8IntrinsicIdentifier('CreateEnvironment'),
					[],
				),
			),
		]),
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r2_7'),
				t.callExpression(t.v8IntrinsicIdentifier('CreateClosure'), [
					t.callExpression(
						t.v8IntrinsicIdentifier('getFunctionById'),
						[
							t.numericLiteral(1),
						],
					),
					t.identifier('r1_1'),
				]),
			),
		]),
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier('r1_2'),
				t.callExpression(
					t.memberExpression(
						t.identifier('r2_7'),
						t.identifier('call'),
					),
					[t.identifier('undefined')],
				),
			),
		]),
		t.ifStatement(
			t.unaryExpression('!', t.identifier('r1_2')),
			t.blockStatement([
				t.whileStatement(
					t.booleanLiteral(true),
					t.blockStatement([
						t.variableDeclaration('const', [
							t.variableDeclarator(
								t.identifier('r1_4'),
								t.callExpression(
									t.memberExpression(
										t.identifier('r2_7'),
										t.identifier('call'),
									),
									[t.identifier('undefined')],
								),
							),
						]),
						t.ifStatement(
							t.identifier('r1_4'),
							t.blockStatement([t.breakStatement()]),
						),
					]),
				),
			]),
		),
		t.returnStatement(t.identifier('result')),
	];

	const folded = foldGuardedLoopExitTests(statements);
	const code = generate(t.program(folded)).code;
	assert.match(code, /const r2_7 = %CreateClosure/);
	assert.match(code, /while \(!r2_7\.call\(undefined\)\) \{\}/);
	assert.doesNotMatch(code, /while[\\s\\S]*r2_7\\.call\\(undefined\\);/);
});

Deno.test('generic loop headers emit same-value Phi assignments', () => {
	const target = register(0, 1);
	const value = register(1, 1);
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r0_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				),
			])],
			branch: t.identifier('done'),
			consequentAddresses: [3, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('consume'),
				[t.identifier('r0_1')],
			))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[1, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: target,
						sources: new AddressMap([
							[0, value],
							[2, value],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [2],
		loopBlocks: new AddressSet([1, 2]),
		continuation: 3,
		exits: [{ from: 1, to: 3, kind: 'break' }],
		children: [],
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [
			{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([0]),
			},
			loop,
			{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([3]),
			},
		],
		sourceBlocks: new AddressSet([0, 1, 2, 3]),
	};
	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	assert.match(generate(result.program).code, /r0_1 = r1_1;/);
});

Deno.test('a loop header Phi updated in place keeps its entry copy outside the loop', () => {
	const target = register(0, 1);
	const entry = register(1, 1);
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r0_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				),
			])],
			branch: t.identifier('done'),
			consequentAddresses: [3, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(
				t.updateExpression('--', t.identifier('r0_1'), false),
			)],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement(t.identifier('r0_1'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[1, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: target,
						// The back edge carries the Phi's own destination: the
						// update in block 2 already wrote the register in place.
						sources: new AddressMap([
							[0, entry],
							[2, target],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [2],
		loopBlocks: new AddressSet([1, 2]),
		continuation: 3,
		exits: [{ from: 1, to: 3, kind: 'break' }],
		children: [],
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [
			{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([0]),
			},
			loop,
			{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([3]),
			},
		],
		sourceBlocks: new AddressSet([0, 1, 2, 3]),
	};
	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	// Re-running the entry copy on every iteration discards the update.
	assert.match(code, /r0_1 = r1_1;\s*while \(true\)/);
});

Deno.test('redundant for-in guards retain the guarded loop', () => {
	const preheader = t.variableDeclaration('const', [
		t.variableDeclarator(
			t.arrayPattern([
				t.identifier('propertyList'),
				t.identifier('beginIndex'),
				t.identifier('endIndex'),
			]),
			t.callExpression(t.v8IntrinsicIdentifier('GetPNameList'), [
				t.identifier('object'),
			]),
		),
	]);
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [preheader],
			branch: t.binaryExpression(
				'===',
				t.identifier('propertyList'),
				t.identifier('undefined'),
			),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r0_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				),
			])],
			branch: t.binaryExpression(
				'===',
				t.identifier('key'),
				t.identifier('undefined'),
			),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[t.identifier('key')],
			))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[1, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: register(0, 1),
						sources: new AddressMap([
							[0, register(0, 0)],
							[2, register(0, 2)],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [2],
		loopBlocks: new AddressSet([1, 2]),
		exits: [{ from: 1, to: 3, kind: 'break' }],
		children: [],
		syntax: {
			kind: 'forIn',
			header: 1,
			preheader: { block: 0, statement: 0 },
			source: t.identifier('object'),
			value: t.identifier('key'),
		},
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2]),
	};
	const empty: Region = {
		kind: 'sequence',
		regions: [],
		sourceBlocks: new AddressSet(),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [{
			kind: 'if',
			header: 0,
			test: t.binaryExpression(
				'===',
				t.identifier('propertyList'),
				t.identifier('undefined'),
			),
			consequent: empty,
			alternate: loop,
			join: 3,
			sourceBlocks: new AddressSet([0, 1, 2]),
		}, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([3]),
		}],
		sourceBlocks: new AddressSet([0, 1, 2, 3]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(code, /for \(const key in object\)/);
	assert.match(code, /visit\(key\)/);
	assert.doesNotMatch(code, /%Phi/);
});

Deno.test('iterator break trailers emit nested loop Phi actions', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('outerDone'),
			consequentAddresses: [6, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r0_2'),
					t.numericLiteral(0),
				),
			])],
			branch: t.identifier('leaveOuter'),
			consequentAddresses: [4, 3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r0_1'),
						t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
					),
				]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r0_1')],
				)),
			],
			branch: t.identifier('innerDone'),
			consequentAddresses: [6, 5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_1'),
					t.callExpression(t.identifier('next'), [
						t.identifier('r0_1'),
					]),
				),
			])],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[4, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: register(0, 1),
						sources: new AddressMap([
							[2, register(0, 2)],
							[5, register(1, 1)],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const innerLoop: Extract<Region, { kind: 'loop' }> = {
		kind: 'loop',
		id: 1,
		header: 4,
		latches: [5],
		loopBlocks: new AddressSet([4, 5]),
		exits: [{ from: 4, to: 6, kind: 'break' }],
		children: [],
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([5]),
		},
		sourceBlocks: new AddressSet([4, 5]),
	};
	const empty: Region = {
		kind: 'sequence',
		regions: [],
		sourceBlocks: new AddressSet(),
	};
	const outerLoop: Extract<Region, { kind: 'loop' }> = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [3],
		loopBlocks: new AddressSet([1, 2, 3]),
		exits: [{
			from: 1,
			to: 6,
			kind: 'break',
		}, {
			from: 2,
			to: 4,
			kind: 'break',
			trailer: innerLoop,
			continuation: 6,
		}],
		children: [],
		syntax: {
			kind: 'forIn',
			header: 1,
			source: t.identifier('object'),
			value: t.identifier('key'),
		},
		body: {
			kind: 'if',
			header: 2,
			test: t.identifier('leaveOuter'),
			consequent: empty,
			alternate: {
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([3]),
			},
			branchEdges: {
				consequent: { from: 2, to: 4, kind: 'normal' },
				alternate: { from: 2, to: 3, kind: 'normal' },
			},
			sourceBlocks: new AddressSet([2, 3]),
		},
		sourceBlocks: new AddressSet([1, 2, 3]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [
			{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([0]),
			},
			outerLoop,
			{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([6]),
			},
		],
		sourceBlocks: new AddressSet([0, 1, 2, 3, 4, 5, 6]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(code, /for \(const key in object\)/);
	assert.match(code, /r0_1 = r0_2;/);
	assert.match(code, /r0_1 = r1_1;/);
	assert.match(code, /consume\(r0_1\)/);
	assert.doesNotMatch(code, /%Phi/);
});

Deno.test('nested loop exits inherit enclosing ordered trailers', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('leaveAll'),
			consequentAddresses: [3, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('advance'),
				[],
			))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('makeResult'),
				[],
			))],
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
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap(
				[...blocks.keys()].map((address) => [
					address,
					{ ssaInstructions: [] },
				]),
			),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const trailer: Region = {
		kind: 'basic',
		body: [],
		sourceBlocks: new AddressSet([3]),
	};
	const innerLoop: Extract<Region, { kind: 'loop' }> = {
		kind: 'loop',
		id: 1,
		label: 'inner',
		header: 1,
		latches: [2],
		loopBlocks: new AddressSet([1, 2]),
		exits: [{
			from: 1,
			to: 3,
			kind: 'labelledBreak',
			targetLoop: 0,
			label: 'outer',
		}],
		children: [],
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2]),
	};
	const outerLoop: Extract<Region, { kind: 'loop' }> = {
		kind: 'loop',
		id: 0,
		label: 'outer',
		header: 0,
		latches: [2],
		loopBlocks: new AddressSet([0, 1, 2]),
		exits: [{
			from: 1,
			to: 3,
			kind: 'break',
			trailer,
			continuation: 4,
		}],
		children: [1],
		body: innerLoop,
		sourceBlocks: new AddressSet([0, 1, 2, 3]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [
			outerLoop,
			{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([4]),
			},
		],
		sourceBlocks: new AddressSet([0, 1, 2, 3, 4]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(code, /if \(!leaveAll\) \{\s*makeResult\(\);\s*return;/);
});

Deno.test('body-owned loop trailers emit their completion Phi edge', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r0_0'),
				t.identifier('emptyValue'),
			)])],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('done'),
			consequentAddresses: [4, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('found'),
			consequentAddresses: [3, 1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.identifier('foundValue'),
			)])],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)]),
				t.returnStatement(t.identifier('r0_1')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[4, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: register(0, 1),
						sources: new AddressMap([
							[1, register(0, 0)],
							[3, register(1, 1)],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const trailer: Region = {
		kind: 'basic',
		body: [],
		sourceBlocks: new AddressSet([3]),
	};
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [2],
		loopBlocks: new AddressSet([1, 2, 3]),
		continuation: 4,
		exits: [{ from: 1, to: 4, kind: 'break' }],
		bodyOwnedExits: [{
			from: 2,
			to: 3,
			kind: 'break',
			trailer,
			continuation: 4,
		}],
		children: [],
		body: {
			kind: 'if',
			header: 2,
			test: t.identifier('found'),
			consequent: {
				kind: 'deferredExit',
				exit: {
					kind: 'loopExit',
					edge: { from: 3, to: 3, kind: 'normal' },
					target: 3,
					actions: [],
				},
				sourceBlocks: new AddressSet([3]),
			},
			alternate: {
				kind: 'continue',
				target: 1,
				sourceBlocks: new AddressSet(),
			},
			branchEdges: {
				consequent: { from: 2, to: 3, kind: 'normal' },
				alternate: { from: 2, to: 1, kind: 'normal' },
			},
			sourceBlocks: new AddressSet([2, 3]),
		},
		sourceBlocks: new AddressSet([1, 2, 3]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [
			{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([0]),
			},
			loop,
			{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([4]),
			},
		],
		sourceBlocks: new AddressSet([0, 1, 2, 3, 4]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(
		code,
		/r1_1 = foundValue;\s*r0_1 = r1_1;\s*break;/,
	);
	assert.doesNotMatch(code, /%Phi/);
});

Deno.test('redundant for-in guards retain bypass and loop-exit Phis', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_2'),
					t.booleanLiteral(false),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.arrayPattern([
						t.identifier('propertyList'),
						t.identifier('beginIndex'),
						t.identifier('endIndex'),
					]),
					t.callExpression(t.v8IntrinsicIdentifier('GetPNameList'), [
						t.identifier('object'),
					]),
				)]),
			],
			branch: t.binaryExpression(
				'===',
				t.identifier('propertyList'),
				t.identifier('undefined'),
			),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r2_1'),
				t.booleanLiteral(true),
			)])],
			branch: t.binaryExpression(
				'===',
				t.identifier('key'),
				t.identifier('undefined'),
			),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[t.identifier('key')],
			))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r1_1')],
				)),
				t.returnStatement(),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[3, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: register(1, 1),
						sources: new AddressMap([
							[0, register(1, 2)],
							[1, register(2, 1)],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [2],
		loopBlocks: new AddressSet([1, 2]),
		exits: [{ from: 1, to: 3, kind: 'break' }],
		children: [],
		syntax: {
			kind: 'forIn',
			header: 1,
			preheader: { block: 0, statement: 1 },
			source: t.identifier('object'),
			value: t.identifier('key'),
		},
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2]),
	};
	const empty: Region = {
		kind: 'sequence',
		regions: [],
		sourceBlocks: new AddressSet(),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [{
			kind: 'if',
			header: 0,
			test: t.binaryExpression(
				'===',
				t.identifier('propertyList'),
				t.identifier('undefined'),
			),
			consequent: empty,
			alternate: loop,
			join: 3,
			sourceBlocks: new AddressSet([0, 1, 2]),
		}, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([3]),
		}],
		sourceBlocks: new AddressSet([0, 1, 2, 3]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(code, /r1_1 = r1_2/);
	assert.match(code, /for \(const key in object\)/);
	assert.match(code, /r1_1 = r2_1/);
	assert.ok(code.indexOf('r1_1 = r1_2') < code.indexOf('for (const key'));
	assert.ok(code.indexOf('for (const key') < code.indexOf('r1_1 = r2_1'));
	assert.doesNotMatch(code, /GetPNameList|propertyList|%Phi/);
});

Deno.test('an ordinary conditional above a for-in keeps its empty arm', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_2'),
				t.booleanLiteral(false),
			)])],
			branch: t.identifier('enabled'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.arrayPattern([
					t.identifier('propertyList'),
					t.identifier('beginIndex'),
					t.identifier('endIndex'),
				]),
				t.callExpression(t.v8IntrinsicIdentifier('GetPNameList'), [
					t.identifier('object'),
				]),
			)])],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r2_1'),
				t.booleanLiteral(true),
			)])],
			branch: t.binaryExpression(
				'===',
				t.identifier('key'),
				t.identifier('undefined'),
			),
			consequentAddresses: [4, 3],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[t.identifier('key')],
			))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r1_1')],
				)),
				t.returnStatement(),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[3, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: register(1, 1),
						sources: new AddressMap([
							[0, register(1, 2)],
							[2, register(2, 1)],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 2,
		latches: [4],
		loopBlocks: new AddressSet([2, 4]),
		exits: [{ from: 2, to: 3, kind: 'break' }],
		children: [],
		syntax: {
			kind: 'forIn',
			header: 2,
			preheader: { block: 1, statement: 0 },
			source: t.identifier('object'),
			value: t.identifier('key'),
		},
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([4]),
		},
		sourceBlocks: new AddressSet([2, 4]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [{
			kind: 'if',
			header: 0,
			test: t.identifier('enabled'),
			consequent: {
				kind: 'sequence',
				regions: [{
					kind: 'basic',
					body: [],
					sourceBlocks: new AddressSet([1]),
				}, loop],
				sourceBlocks: new AddressSet([1, 2, 4]),
			},
			alternate: {
				kind: 'sequence',
				regions: [],
				sourceBlocks: new AddressSet(),
			},
			join: 3,
			sourceBlocks: new AddressSet([0, 1, 2, 4]),
		}, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([3]),
		}],
		sourceBlocks: new AddressSet([0, 1, 2, 3, 4]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	// The conditional is not the loop's zero-trip guard, so it survives and
	// its empty arm still carries the continuation Phi copy.
	assert.match(code, /if \(enabled\)/);
	assert.match(code, /for \(const key in object\)/);
	assert.match(code, /r1_1 = r1_2/);
	assert.doesNotMatch(code, /GetPNameList|%Phi/);
});

Deno.test('an elided for-in guard block places its bypass Phi copy', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_2'),
					t.booleanLiteral(false),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.arrayPattern([
						t.identifier('propertyList'),
						t.identifier('beginIndex'),
						t.identifier('endIndex'),
					]),
					t.callExpression(t.v8IntrinsicIdentifier('GetPNameList'), [
						t.identifier('object'),
					]),
				)]),
			],
			branch: t.binaryExpression(
				'===',
				t.identifier('propertyList'),
				t.identifier('undefined'),
			),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r2_1'),
				t.booleanLiteral(true),
			)])],
			branch: t.binaryExpression(
				'===',
				t.identifier('key'),
				t.identifier('undefined'),
			),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[t.identifier('key')],
			))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r1_1')],
				)),
				t.returnStatement(),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[3, {
					ssaInstructions: [{
						instruction: 'Phi',
						destination: register(1, 1),
						sources: new AddressMap([
							[0, register(1, 2)],
							[1, register(2, 1)],
						]),
					}],
				}],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	// The guard branch is dropped by structuring: block 0 is a Basic Region
	// beside the loop, so no If Region is left to carry the bypass edge.
	const region: Region = {
		kind: 'sequence',
		regions: [{
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([0]),
		}, {
			kind: 'loop',
			id: 0,
			header: 1,
			latches: [2],
			loopBlocks: new AddressSet([1, 2]),
			continuation: 3,
			exits: [{ from: 1, to: 3, kind: 'break' }],
			children: [],
			syntax: {
				kind: 'forIn',
				header: 1,
				preheader: { block: 0, statement: 1 },
				source: t.identifier('object'),
				value: t.identifier('key'),
			},
			body: {
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([2]),
			},
			sourceBlocks: new AddressSet([1, 2]),
		}, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([3]),
		}],
		sourceBlocks: new AddressSet([0, 1, 2, 3]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(code, /r1_1 = r1_2/);
	assert.match(code, /for \(const key in object\)/);
	assert.match(code, /r1_1 = r2_1/);
	assert.ok(code.indexOf('r1_1 = r1_2') < code.indexOf('for (const key'));
	assert.ok(code.indexOf('for (const key') < code.indexOf('r1_1 = r2_1'));
	assert.doesNotMatch(code, /GetPNameList|propertyList|%Phi/);
});

Deno.test('nested for-in guards may bypass through an enclosing continue', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.arrayPattern([
					t.identifier('propertyList'),
					t.identifier('beginIndex'),
					t.identifier('endIndex'),
				]),
				t.callExpression(t.v8IntrinsicIdentifier('GetPNameList'), [
					t.identifier('object'),
				]),
			)])],
			branch: t.binaryExpression(
				'===',
				t.identifier('propertyList'),
				t.identifier('undefined'),
			),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.identifier('key'),
				t.identifier('undefined'),
			),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[t.identifier('key')],
			))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const empty: Region = {
		kind: 'sequence',
		regions: [],
		sourceBlocks: new AddressSet(),
	};
	const loop: Region = {
		kind: 'loop',
		id: 1,
		label: 'loop_1',
		header: 1,
		latches: [2],
		loopBlocks: new AddressSet([1, 2]),
		exits: [{
			from: 1,
			to: 3,
			kind: 'labelledContinue',
			label: 'loop_0',
		}],
		children: [],
		syntax: {
			kind: 'forIn',
			header: 1,
			preheader: { block: 0, statement: 0 },
			source: t.identifier('object'),
			value: t.identifier('key'),
		},
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [{
			kind: 'if',
			header: 0,
			test: t.binaryExpression(
				'===',
				t.identifier('propertyList'),
				t.identifier('undefined'),
			),
			consequent: {
				kind: 'labelContinue',
				label: 'loop_0',
				target: 3,
				sourceBlocks: new AddressSet(),
			},
			alternate: empty,
			join: 1,
			sourceBlocks: new AddressSet([0]),
		}, loop],
		sourceBlocks: new AddressSet([0, 1, 2]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(code, /for \(const key in object\)/);
	assert.match(code, /visit\(key\)/);
	assert.doesNotMatch(code, /GetPNameList|propertyList|if \(/);
	assert.doesNotMatch(code, /loop_1:/);

	const loopWithTargetedLabel: Region = {
		...loop,
		body: {
			kind: 'labelBreak',
			label: 'loop_1',
			target: 3,
			sourceBlocks: new AddressSet(),
		},
	};
	const targetedResult = emitRegionToAST(
		loopWithTargetedLabel,
		cfg,
		recoverDescriptors(cfg),
	);
	const targetedCode = generate(targetedResult.program).code;
	assert.match(targetedCode, /loop_1: for \(const key in object\)/);
	assert.match(targetedCode, /break loop_1/);
});

Deno.test('write-only cleanup keeps destructuring provenance on the statement', () => {
	const destructuring = t.variableDeclaration('var', [t.variableDeclarator(
		t.arrayPattern([t.identifier('r1_1'), t.identifier('r2_1')]),
		t.identifier('_param_9_0_'),
	)]);
	destructuring.extra = { fromDestructuring: true };
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [
				destructuring,
				// Declared here, written, never read: the write-only cleanup
				// rebuilds the statements it walks, and used to drop every
				// statement's `extra` while doing so.
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier('r3_1')),
				]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.identifier('r3_1'),
					t.numericLiteral(0),
				)),
				t.returnStatement(t.identifier('r1_1')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	mergedBlocks.set(0, new AddressSet([0]));
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const result = emitRegionToAST(
		{
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([0]),
		},
		cfg,
		recoverDescriptors(cfg),
	);

	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.doesNotMatch(code, /r3_1/);
	const emitted = result.program.body.find((statement) =>
		t.isVariableDeclaration(statement) &&
		t.isArrayPattern(statement.declarations[0]?.id)
	);
	assert.ok(emitted);
	assert.equal(emitted.extra?.fromDestructuring, true);
});

Deno.test('an exhausted iterator breaks past the body break destination', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('items'),
				t.callExpression(t.identifier('getItems'), []),
			)])],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('done'),
			consequentAddresses: [2, 4],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[t.identifier('item')],
			))],
			branch: t.identifier('stop'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.expressionStatement(t.callExpression(
					t.identifier('afterBreak'),
					[],
				)),
				t.returnStatement(),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('afterExhaustion'),
				[],
			))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const headerExit = {
		from: 1,
		to: 4,
		kind: 'break' as const,
		sequenceExit: { target: 4, label: 'scope_4' },
	};
	const bodyExit = { from: 2, to: 3, kind: 'break' as const };
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [2],
		loopBlocks: new AddressSet([1, 2]),
		exits: [headerExit, bodyExit],
		children: [],
		syntax: {
			kind: 'forOf',
			header: 1,
			source: t.identifier('items'),
			value: t.identifier('item'),
		},
		body: {
			kind: 'if',
			header: 2,
			test: t.identifier('stop'),
			consequent: {
				kind: 'break',
				target: 3,
				exit: bodyExit,
				sourceBlocks: new AddressSet(),
			},
			alternate: {
				kind: 'continue',
				target: 1,
				sourceBlocks: new AddressSet(),
			},
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([0]) },
			{
				kind: 'sequence',
				exitLabel: 'scope_4',
				regions: [
					loop,
					{
						kind: 'basic',
						body: [],
						sourceBlocks: new AddressSet([3]),
					},
				],
				sourceBlocks: new AddressSet([1, 2, 3]),
			},
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([4]) },
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([5]) },
		],
		sourceBlocks: new AddressSet([0, 1, 2, 3, 4, 5]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	// Exhaustion leaves the labelled span; the body break's destination is what
	// lexically follows the loop, so it must not be preceded by the
	// exhaustion destination's statements.
	assert.ok(code.indexOf('afterBreak()') < code.indexOf('afterExhaustion()'));
	assert.match(code, /for \(const item of items\)/);
});

Deno.test('iterator loops emit conditional latch exits', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('items'),
				t.callExpression(t.identifier('getItems'), []),
			)])],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('done'),
			consequentAddresses: [2, 4],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[t.identifier('item')],
			))],
			branch: t.identifier('stop'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.expressionStatement(t.callExpression(
					t.identifier('found'),
					[],
				)),
				t.returnStatement(),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.expressionStatement(t.callExpression(
					t.identifier('exhausted'),
					[],
				)),
				t.returnStatement(),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [2],
		loopBlocks: new AddressSet([1, 2]),
		exits: [
			{ from: 1, to: 4, kind: 'break' },
			{ from: 2, to: 3, kind: 'break' },
		],
		children: [],
		syntax: {
			kind: 'forOf',
			header: 1,
			source: t.identifier('items'),
			value: t.identifier('item'),
		},
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([0]) },
			loop,
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([4]) },
		],
		sourceBlocks: new AddressSet([0, 1, 2, 3, 4]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(code, /if \(stop\) \{\s*found\(\);\s*return;/);
	assert.equal(code.match(/found\(\)/g)?.length, 1);
	assert.equal(code.match(/exhausted\(\)/g)?.length, 1);
});

Deno.test('try-finally reuses a nested sequence exit label', () => {
	const blocks = new AddressMap<IRBlock>([
		[1, {
			address: 1,
			body: [],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('protectedBody'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.expressionStatement(t.identifier('afterProtectedBody'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.expressionStatement(t.identifier('cleanup'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 1,
		mergedBlocks,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const exit = {
		from: 2,
		to: 6,
		kind: 'break' as const,
		sequenceExit: { target: 6, label: 'scope_6' },
	};
	const body: Region = {
		kind: 'sequence',
		exitLabel: 'scope_6',
		regions: [{
			kind: 'loop',
			id: 0,
			header: 1,
			latches: [2],
			loopBlocks: new AddressSet([1, 2]),
			exits: [exit],
			children: [],
			syntax: {
				kind: 'forOf',
				header: 1,
				source: t.identifier('items'),
				value: t.identifier('item'),
			},
			body: {
				kind: 'labelBreak',
				label: 'scope_6',
				target: 6,
				exit,
				sourceBlocks: new AddressSet([2]),
			},
			sourceBlocks: new AddressSet([1, 2]),
		}, {
			kind: 'basic',
			body: [t.expressionStatement(t.identifier('protectedBody'))],
			sourceBlocks: new AddressSet([5]),
		}],
		sourceBlocks: new AddressSet([1, 2, 5]),
	};
	const region: Region = {
		kind: 'tryFinally',
		body,
		finalizer: {
			kind: 'basic',
			body: [t.expressionStatement(t.identifier('cleanup'))],
			sourceBlocks: new AddressSet([9]),
		},
		handlerAddress: 9,
		protectedBlocks: new AddressSet([1, 2, 5]),
		sourceBlocks: new AddressSet([1, 2, 5, 9]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	const labels = code.match(/^\s*scope_6: \{/gm) ?? [];
	assert.equal(labels.length, 1, code);
	assert.match(code, /break scope_6;/);
	assert.match(code, /finally \{\s*cleanup;/);
});

Deno.test('shared deferred loop exits use their ordered sequence label', () => {
	const blocks = new AddressMap<IRBlock>([
		[1, {
			address: 1,
			body: [],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('ordinaryTail'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 1,
		mergedBlocks,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const sequenceExit = { target: 6, label: 'scope_6' };
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [3],
		loopBlocks: new AddressSet([1, 2, 3]),
		continuation: 5,
		exits: [
			{ from: 1, to: 5, kind: 'break' },
			{ from: 2, to: 6, kind: 'break', sequenceExit },
			{ from: 3, to: 6, kind: 'break', sequenceExit },
		],
		children: [],
		syntax: {
			kind: 'forOf',
			header: 1,
			source: t.identifier('items'),
			value: t.identifier('item'),
		},
		body: {
			kind: 'deferredExit',
			exit: {
				kind: 'loopExit',
				edge: { from: 6, to: 6, kind: 'normal' },
				target: 6,
				actions: [],
			},
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2, 3]),
	};
	const scoped: Region = {
		kind: 'sequence',
		exitLabel: 'scope_6',
		regions: [loop, {
			kind: 'basic',
			body: [t.expressionStatement(t.identifier('ordinaryTail'))],
			sourceBlocks: new AddressSet([5]),
		}],
		sourceBlocks: new AddressSet([1, 2, 3, 5]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [scoped, {
			kind: 'basic',
			body: [t.returnStatement()],
			sourceBlocks: new AddressSet([6]),
		}],
		sourceBlocks: new AddressSet([1, 2, 3, 5, 6]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.match(code, /break scope_6;/);
	assert.ok(code.indexOf('break scope_6;') < code.indexOf('ordinaryTail;'));
});

Deno.test('a Phi merged by folded control is assigned on the folded arm', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r3_4'),
					t.callExpression(t.identifier('parse'), []),
				)]),
				t.ifStatement(
					t.identifier('invalid'),
					t.blockStatement([
						t.variableDeclaration('const', [t.variableDeclarator(
							t.identifier('r3_5'),
							t.callExpression(t.identifier('fallback'), []),
						)]),
					]),
				),
			],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r3_6'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('r3_4'),
						t.identifier('r3_5'),
					]),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r3_6')],
				)),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const region: Region = {
		kind: 'sequence',
		regions: [
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([0]) },
			{ kind: 'basic', body: [], sourceBlocks: new AddressSet([1]) },
		],
		sourceBlocks: new AddressSet([0, 1]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	// The join has one CFG predecessor once the branch is folded into the
	// block, so no edge carries the copy: the arm defining the source has to.
	assert.doesNotMatch(code, /%Phi/);
	assert.match(code, /let r3_6 = r3_4;/);
	assert.match(code, /if \(invalid\) \{[^}]*r3_6 = r3_5;\s*\}/);
	assert.match(code, /consume\(r3_6\)/);
});

Deno.test('header-latch loops emit the latch body before the backedge', () => {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('runBody'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('body'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r8_8'),
					t.identifier('latchValue'),
				),
			])],
			consequentAddresses: [0],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	const func = {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	const cfg = ImmutableCFG.fromIRFunction(func);
	const region: Region = {
		kind: 'loop',
		id: 0,
		header: 0,
		latches: [2],
		loopBlocks: new AddressSet([0, 1, 2]),
		exits: [],
		children: [],
		headerLatchBranch: { bodyEntry: 1, latch: 2 },
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([1]),
		},
		sourceBlocks: new AddressSet([0, 1, 2]),
	};

	const result = emitRegionToAST(region, cfg, recoverDescriptors(cfg));
	assert.deepEqual(result.diagnostics, []);
	const code = generate(result.program).code;
	assert.equal((code.match(/const r8_8 = latchValue/g) ?? []).length, 1);
});

Deno.test('repeated entry and latch guards become one loop condition', () => {
	const guardedLoop = (body: t.Statement[]) =>
		t.ifStatement(
			t.identifier('withinRetryLimit'),
			t.blockStatement([
				t.ifStatement(
					t.identifier('notAborted'),
					t.blockStatement([
						t.whileStatement(
							t.booleanLiteral(true),
							t.blockStatement([
								...body,
								t.ifStatement(
									t.unaryExpression(
										'!',
										t.identifier('withinRetryLimit'),
									),
									t.blockStatement([t.breakStatement()]),
								),
								t.ifStatement(
									t.unaryExpression(
										'!',
										t.identifier('notAborted'),
									),
									t.blockStatement([t.breakStatement()]),
									t.blockStatement([t.continueStatement()]),
								),
							]),
						),
					]),
				),
			]),
		);
	const failure = t.throwStatement(t.identifier('failure'));
	const folded = foldGuardedLoopExitTests([
		guardedLoop([t.expressionStatement(t.identifier('work'))]),
		failure,
	]);
	const code = generate(t.program(folded)).code;

	assert.match(
		code,
		/while \(withinRetryLimit && notAborted\) \{\s*work;/,
	);
	assert.equal((code.match(/throw failure/g) ?? []).length, 1);
	assert.doesNotMatch(code, /if \(withinRetryLimit\)/);
	assert.doesNotMatch(code, /break;/);

	const continueBeforeLatch = foldGuardedLoopExitTests([
		guardedLoop([t.continueStatement()]),
		failure,
	]);
	assert.ok(t.isIfStatement(continueBeforeLatch[0]));
});

Deno.test('loop-carried result guards become one iterator loop', () => {
	const assign = (target: string, value: string) =>
		t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier(target),
			t.identifier(value),
		));
	const resultCall = () => t.callExpression(t.identifier('nextResult'), []);
	const doneTest = (name: string) =>
		t.unaryExpression(
			'!',
			t.memberExpression(t.identifier(name), t.identifier('done')),
		);
	const folded = foldGuardedLoopExitTests([
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier('r4_14')),
		]),
		t.variableDeclaration('const', [
			t.variableDeclarator(t.identifier('r4_13'), resultCall()),
		]),
		t.ifStatement(
			doneTest('r4_13'),
			t.blockStatement([
				assign('r4_14', 'r4_13'),
				t.whileStatement(
					t.booleanLiteral(true),
					t.blockStatement([
						t.expressionStatement(t.callExpression(
							t.identifier('consume'),
							[
								t.memberExpression(
									t.identifier('r4_14'),
									t.identifier('value'),
								),
							],
						)),
						t.variableDeclaration('const', [
							t.variableDeclarator(
								t.identifier('r12_16'),
								resultCall(),
							),
						]),
						t.ifStatement(
							doneTest('r12_16'),
							t.blockStatement([
								assign('r4_14', 'r12_16'),
								t.continueStatement(),
							]),
							t.blockStatement([t.breakStatement()]),
						),
					]),
				),
			]),
		),
	]);
	const code = generate(t.program(folded)).code;

	assert.match(code, /r4_14 = nextResult\(\);/);
	assert.match(code, /while \(!r4_14\.done\)/);
	assert.match(code, /consume\(r4_14\.value\)/);
	assert.equal((code.match(/nextResult\(\)/g) ?? []).length, 2);
	assert.doesNotMatch(code, /r4_13|r12_16|while \(true\)|break|continue/);
});
