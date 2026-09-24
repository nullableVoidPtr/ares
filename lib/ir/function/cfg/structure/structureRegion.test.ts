import { strict as assert } from 'node:assert';
import * as t from '@babel/types';
import type { IRBlock } from '../../../ast/mod.ts';
import type { IRFunction } from '../../mod.ts';
import { AddressGraph } from '../../../../utils/graph.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import {
	labelPendingLoopSequenceExits,
	structureCFG,
	structureRegionAt,
} from './structureRegion.ts';
import {
	tryStructureBoundedContinuationForest,
	tryStructureBoundedScopeForest,
} from './loopForest.ts';
import {
	contractedExceptionBlocks,
	openableProtectedEntries,
	tryStructureExceptionRegion,
} from './exceptionRegion.ts';
import { recoverDescriptors } from '../descriptors/mod.ts';
import { tryStructureLoopRegion } from './loopRegion.ts';
import {
	regionTextLooksLinearizedAcyclicCFG,
	summarizeRecursiveCFG,
} from '../recursiveSummary.ts';
import { computeNaturalLoops } from '../algorithms/naturalLoops.ts';
import { ImmutableCFG } from '../immutableCFG.ts';
import {
	loopRegionCoverageIssues,
	type Region,
	regionCoveredBlocks,
	regionDuplicateOwnership,
	sequenceRegion,
	visitRegions,
} from '../regions/region.ts';
import { printRegion } from '../regions/printer.ts';

function fakeFunction(
	blocks: Map<number, IRBlock>,
	exceptionalEdges: Array<{
		handler: number;
		protectedBlocks: number[];
	}> = [],
): IRFunction {
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	return {
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: { basicBlocks: new Map() },
		exceptions: {
			records: new Map(exceptionalEdges.map((edge) => [
				edge.handler,
				{ protectedBlocks: new AddressSet(edge.protectedBlocks) },
			])),
			structuredRegionDescriptors: () => [],
			finalizerEdgeActions: () => [],
			equivalentCatchHandlerAliases: () => new AddressMap(),
			structuredRegionForest: () => ({
				roots: [],
				nodeByHandler: new Map(),
				parentByHandler: new Map(),
			}),
		},
	} as unknown as IRFunction;
}

Deno.test('duplicate block ownership is reported', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('test'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('left'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('right'))],
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
	const cfg = structureCFG(fakeFunction(blocks)).cfg;
	const shared: Region = {
		kind: 'basic',
		body: [],
		sourceBlocks: new AddressSet([3]),
	};
	// Both arms claim the shared continuation. The emitter keeps the statements
	// at whichever arm runs first, so the other one silently loses them.
	const cloned: Region = {
		kind: 'if',
		header: 0,
		test: t.identifier('test'),
		consequent: {
			kind: 'sequence',
			regions: [{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([1]),
			}, shared],
			sourceBlocks: new AddressSet([1, 3]),
		},
		alternate: {
			kind: 'sequence',
			regions: [{
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([2]),
			}, shared],
			sourceBlocks: new AddressSet([2, 3]),
		},
		join: 3,
		sourceBlocks: new AddressSet([0, 1, 2, 3]),
	};

	assert.deepEqual(regionDuplicateOwnership(cloned, cfg), [3]);
	assert.deepEqual(
		regionDuplicateOwnership(
			structureCFG(fakeFunction(blocks)).region!,
			cfg,
		),
		[],
	);
});

Deno.test('summary counts duplicated SSA ownership outside finalizers', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('test'),
			consequentAddresses: [10, 20],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.returnStatement(t.numericLiteral(1))],
			consequentAddresses: [],
			kind: 'normal',
			sourceAddresses: new AddressSet([3]),
		}],
		[20, {
			address: 20,
			body: [t.returnStatement(t.numericLiteral(2))],
			consequentAddresses: [],
			kind: 'normal',
			sourceAddresses: new AddressSet([3]),
		}],
	]);
	const result = structureCFG(fakeFunction(blocks));
	const region: Region = {
		kind: 'if',
		header: 0,
		test: t.identifier('test'),
		consequent: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([10]),
		},
		alternate: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([20]),
		},
		sourceBlocks: new AddressSet([0, 10, 20]),
	};

	// Distinct compatibility blocks hide the overlap at the live CFG layer.
	assert.deepEqual(regionDuplicateOwnership(region, result.cfg), []);
	const summary = summarizeRecursiveCFG(1, { ...result, region });
	assert.deepEqual(summary.duplicatedSSABlockCounts, { '0x3': 2 });
	assert.equal(
		summary.diagnostics.find((diagnostic) =>
			diagnostic.kind === 'duplicateBlockOwnership'
		)?.message,
		'blocks 0x3 (2 claims) are claimed by more than one Region',
	);

	const finalizer = {
		handler: 10,
		kind: 'finally' as const,
		protectedBlocks: new AddressSet([0]),
		protectedEntries: new AddressSet([0]),
		catchBody: null,
		canonicalFinallyAddress: 10,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: [10],
		boundedFinallyBodyBlocks: [10],
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const finalizerSummary = summarizeRecursiveCFG(1, {
		...result,
		region,
		descriptors: {
			...result.descriptors,
			exceptions: {
				...result.descriptors.exceptions,
				handlers: [finalizer],
			},
		},
	});
	assert.deepEqual(finalizerSummary.duplicatedSSABlockCounts, {});
	assert.equal(
		finalizerSummary.diagnostics.some((diagnostic) =>
			diagnostic.kind === 'duplicateBlockOwnership'
		),
		false,
	);
});

Deno.test('natural loops with equal bodies are siblings not parents', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			consequentAddresses: [0],
			kind: 'normal',
		}],
	]);
	const cfg = ImmutableCFG.fromIRFunction(fakeFunction(blocks));
	const loops = computeNaturalLoops(cfg, {
		idom: new AddressMap([[0, null], [1, null]]),
		children: new AddressMap([[0, []], [1, []]]),
		dominates: (a, b) =>
			a === b || (a === 0 && b === 1) ||
			(a === 1 && b === 0),
		nearestCommonDominator: () => 0,
	}).loops;

	assert.equal(loops.length, 2);
	assert.deepEqual(
		loops.map((loop) => loop.parent),
		[undefined, undefined],
	);
});

Deno.test('loop coverage rejects claimed but unrepresented body blocks', () => {
	const claimedLoop: Region = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [3],
		loopBlocks: new AddressSet([1, 2, 3]),
		exits: [],
		children: [],
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2, 3]),
	};

	assert.deepEqual(loopRegionCoverageIssues(claimedLoop), [{
		header: 1,
		missingBodyBlocks: [3],
		unexpectedBodyBlocks: [],
		missingTrailerBlocks: [],
		unexpectedTrailerBlocks: [],
		overlappingTrailerBlocks: [],
	}]);
	const result = structureCFG(fakeFunction(
		new Map([[0, {
			address: 0,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}]]),
	));
	result.region = claimedLoop;
	const summary = summarizeRecursiveCFG(0, result);
	assert.equal(summary.misses.includes('loops-not-structured'), true);
	assert.deepEqual(summary.loopCoverageIssues[0]?.missingBodyBlocks, [3]);
});

Deno.test('suppressed finalizer copies are covered loop body blocks', () => {
	const claimedLoop = (suppressed?: AddressSet<number>): Region => ({
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [3],
		loopBlocks: new AddressSet([1, 2, 3]),
		exits: [],
		children: [],
		suppressedBodyBlocks: suppressed,
		body: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([1, 2, 3]),
	});

	// Block 3 is a finalizer copy of a `finally` the body itself represents: the
	// clause emits those statements once, so the body emits nothing for it.
	assert.deepEqual(
		loopRegionCoverageIssues(claimedLoop(new AddressSet([3]))),
		[],
	);
	assert.deepEqual(
		loopRegionCoverageIssues(claimedLoop()).map((issue) =>
			issue.missingBodyBlocks
		),
		[[3]],
	);
});

Deno.test('subsumed nested iterator handlers cover loop bodies', () => {
	const nested: Region = {
		kind: 'loop',
		id: 1,
		header: 2,
		latches: [2],
		loopBlocks: new AddressSet([2, 3]),
		exits: [],
		children: [],
		subsumedHandlers: new AddressSet([3]),
		body: {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		},
		sourceBlocks: new AddressSet([2, 3]),
	};
	const outer: Region = {
		kind: 'loop',
		id: 0,
		header: 1,
		latches: [2],
		loopBlocks: new AddressSet([1, 2, 3]),
		exits: [],
		children: [1],
		body: nested,
		sourceBlocks: new AddressSet([1, 2, 3]),
	};

	assert.deepEqual(loopRegionCoverageIssues(outer), []);
});

Deno.test('a protected range opening at a loop header composes the body', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.identifier('prelude'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('header'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('again'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('step'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('handle'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
	]);
	// The `try` opens exactly at the loop header and the back edge re-enters it
	// from inside the protected range: contracting the loop first would leave
	// the handler with nowhere to open.
	const result = structureCFG(fakeFunction(blocks, [{
		handler: 5,
		protectedBlocks: [1, 2, 3],
	}]));
	const summary = summarizeRecursiveCFG(0, result);

	assert.deepEqual(summary.misses, []);
	assert.deepEqual(summary.unhandledExceptionHandlers, []);
	const loop = findLoopRegion(result.region);
	assert.equal(loop?.bodyOwnsHeader, true);
	assert.equal(loop?.body.kind, 'tryCatch');
	// The header's statements belong to the `try`, and the loop must not repeat
	// them once the body owns the header.
	assert.equal(
		(summary.emittedCode?.match(/header;/g) ?? []).length,
		1,
	);
});

Deno.test('nested catches sharing a cyclic protected entry remain nested', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.identifier('start'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			branch: t.identifier('again'),
			consequentAddresses: [2, 1],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.returnStatement(t.identifier('done'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('innerCatch'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.identifier('outerCatch'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		0,
		structureCFG(fakeFunction(blocks, [
			{ handler: 4, protectedBlocks: [0, 1] },
			{ handler: 5, protectedBlocks: [0, 1, 4] },
		])),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.unhandledExceptionHandlers, []);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.equal((summary.emittedCode?.match(/try \{/g) ?? []).length, 2);
	assert.match(summary.emittedCode ?? '', /innerCatch/);
	assert.match(summary.emittedCode ?? '', /outerCatch/);
});

Deno.test('nested catch branches exclude their enclosing handler', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('risky'),
				[],
			))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.returnStatement(t.identifier('ok'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('error'),
				t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
			)])],
			branch: t.identifier('hasCode'),
			consequentAddresses: [5, 6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('recordCode'),
				[t.identifier('error')],
			))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.throwStatement(t.identifier('error'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.returnStatement(t.identifier('outerFallback'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		0,
		structureCFG(fakeFunction(blocks, [
			{ handler: 4, protectedBlocks: [0] },
			{ handler: 9, protectedBlocks: [0, 4, 5, 6] },
		])),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.regionText ?? '', /fallback/);
	assert.equal((summary.emittedCode?.match(/try \{/g) ?? []).length, 2);
	assert.equal(
		(summary.emittedCode?.match(/outerFallback/g) ?? []).length,
		1,
	);
});

Deno.test('a protected loop entry owns its terminal exit and handler', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('hasNext'),
			consequentAddresses: [1, 10],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[],
			))],
			branch: t.identifier('succeeded'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.returnStatement(t.booleanLiteral(true))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('advance'))],
			consequentAddresses: [0],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('caught'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.returnStatement(t.booleanLiteral(false)),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.returnStatement(t.booleanLiteral(false))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const result = structureCFG(fakeFunction(blocks, [{
		handler: 4,
		protectedBlocks: [1],
	}]));
	const summary = summarizeRecursiveCFG(0, result);

	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	const loop = findLoopRegion(result.region);
	assert.ok(loop?.sourceBlocks.has(2));
	assert.ok(loop?.sourceBlocks.has(4));
	assert.match(summary.emittedCode ?? '', /try \{/);
	assert.match(summary.emittedCode ?? '', /catch \(/);
});

function findLoopRegion(
	region: Region | undefined,
): Extract<Region, { kind: 'loop' }> | null {
	if (!region) return null;
	let found: Extract<Region, { kind: 'loop' }> | null = null;
	visitRegions(region, (candidate) => {
		if (found == null && candidate.kind === 'loop') found = candidate;
	});
	return found;
}

Deno.test('unstructured branch inventory identifies protected boundaries', () => {
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
			body: [],
			branch: t.identifier('cycle'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.throwStatement(t.identifier('error'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const summary = summarizeRecursiveCFG(
		0,
		structureCFG(fakeFunction(blocks, [{
			handler: 5,
			protectedBlocks: [1],
		}])),
	);
	assert.equal(
		summary.unstructuredBranches.find((branch) => branch.block === 3)
			?.shapes.includes('protected-region-boundary'),
		true,
	);
});

Deno.test('unstructured branch inventory identifies irreducible SCCs', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('entry'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
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
			body: [],
			branch: t.identifier('cycle'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
	]);
	const summary = summarizeRecursiveCFG(
		0,
		structureCFG(fakeFunction(blocks)),
	);
	assert.equal(
		summary.unstructuredBranches.some((branch) =>
			branch.shapes.includes('irreducible-subgraph')
		),
		true,
	);
});

Deno.test('large overlapping terminal-if arms avoid recursive expansion', () => {
	// Every branch reaches both terminal blocks through a Fibonacci-shaped DAG.
	// It has no common postdominator, but its arms are not disjoint and therefore
	// cannot be represented as a terminal-if ladder. Recursing before proving that
	// fact expands an exponential number of overlapping suffixes.
	const terminal = 120;
	const blocks = new Map<number, IRBlock>();
	for (let address = 0; address < terminal; address++) {
		blocks.set(address, {
			address,
			body: [],
			branch: t.identifier(`condition_${address}`),
			consequentAddresses: [address + 1, address + 2],
			kind: 'normal',
		});
	}
	for (const address of [terminal, terminal + 1]) {
		blocks.set(address, {
			address,
			body: [t.returnStatement(t.numericLiteral(address))],
			consequentAddresses: [],
			kind: 'normal',
		});
	}

	const result = structureCFG(fakeFunction(blocks));
	assert.equal(
		result.diagnostics.items.some((item) =>
			item.kind === 'unstructuredRegion'
		),
		false,
	);
	// The arms cannot be a terminal-if ladder, so the bounded control skeleton
	// owns the DAG instead: every block once, and no branch left to a Basic
	// Region. Recursing before proving that would expand an exponential number
	// of overlapping suffixes, so completing at all is part of the assertion.
	const summary = summarizeRecursiveCFG(0, result);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.unstructuredBranches, [], summary.regionText);
});

Deno.test('large linearized acyclic Regions are explicit misses', () => {
	// `cloned` is a block a second leaf claims as well: the copy that makes a
	// Region larger than the graph it represents.
	const groups = (cloned: boolean) =>
		Array.from({ length: 16 }, (_, index) => {
			const start = index * 4;
			const suffix = Array.from(
				{ length: 40 },
				(_unused, offset) => `0x${(start + offset).toString(16)}`,
			).join(',');
			return [
				`  sequence blocks=${suffix}`,
				`    if join=0x${(start + 3).toString(16)} header=0x${
					start.toString(16)
				} value=shortcut|ternary blocks=0x${start.toString(16)},0x${
					(start + 1).toString(16)
				},0x${(start + 2).toString(16)}`,
				'      then sequence blocks=',
				`      else basic blocks=0x${
					(cloned ? 1 : start + 1).toString(16)
				}`,
			].join('\n');
		}).join('\n');

	assert.equal(
		regionTextLooksLinearizedAcyclicCFG(groups(true), {
			blockCount: 80,
			sccCount: 80,
			loopCount: 0,
		}),
		true,
	);
	assert.equal(
		regionTextLooksLinearizedAcyclicCFG(groups(true), {
			blockCount: 80,
			sccCount: 79,
			loopCount: 0,
		}),
		false,
	);
	// A deep nest names a long suffix at every level because a sequence lists
	// its descendants. With every leaf owning its own block there is no copy,
	// so the same shape is exactly the nest the source had.
	assert.equal(
		regionTextLooksLinearizedAcyclicCFG(groups(false), {
			blockCount: 80,
			sccCount: 80,
			loopCount: 0,
		}),
		false,
	);
});

Deno.test('acyclic value-if ladders are not linearized misses', () => {
	const ladder = (groups: number) =>
		Array.from({ length: groups }, (_, index) => {
			const start = index * 3;
			return [
				`  if join=0x${(start + 2).toString(16)} header=0x${
					start.toString(16)
				} value=shortcut|ternary blocks=0x${start.toString(16)},0x${
					(start + 1).toString(16)
				},0x${(start + 2).toString(16)}`,
				'    then sequence blocks=',
				`    else basic blocks=0x${(start + 1).toString(16)}`,
			].join('\n');
		}).join('\n');
	const regionText = ladder(11);

	// A folded short-circuit chain and a conditional-Phi arm each leave one
	// `if` node with one empty arm, so a guard-heavy function crosses those
	// thresholds while its Region is exactly the nest the source had.
	assert.equal(
		regionTextLooksLinearizedAcyclicCFG(regionText, {
			blockCount: 33,
			sccCount: 33,
			loopCount: 0,
		}),
		false,
	);
	// More branch nodes than blocks: the arms were cloned under several
	// parents, so the Region is larger than the graph it represents.
	assert.equal(
		regionTextLooksLinearizedAcyclicCFG(ladder(30), {
			blockCount: 29,
			sccCount: 29,
			loopCount: 0,
		}),
		true,
	);
	assert.equal(
		regionTextLooksLinearizedAcyclicCFG(ladder(30), {
			blockCount: 29,
			sccCount: 29,
			loopCount: 1,
		}),
		false,
	);
});

Deno.test('labelled control forests are not linearized misses', () => {
	const regionText = Array.from({ length: 11 }, (_, index) => {
		const start = index * 3;
		return [
			`  sequence label=cfg_cont_0_${start.toString(16)} blocks=0x${
				start.toString(16)
			},0x${(start + 1).toString(16)},0x${(start + 2).toString(16)}`,
			`    if join=0x${(start + 2).toString(16)} header=0x${
				start.toString(16)
			} blocks=0x${start.toString(16)},0x${(start + 1).toString(16)}`,
			'      then sequence blocks=',
			`      else basic blocks=0x${(start + 1).toString(16)}`,
		].join('\n');
	}).join('\n');

	assert.equal(
		regionTextLooksLinearizedAcyclicCFG(regionText, {
			blockCount: 33,
			sccCount: 33,
			loopCount: 0,
		}),
		false,
	);
});

Deno.test('nested branches fill their enclosing weak-SESE arm', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outer'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('inner'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('alternate'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('left'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('right'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('afterInner'))],
			branch: t.identifier('rejoin'),
			consequentAddresses: [6, 7],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const result = structureCFG(fakeFunction(blocks));
	const conditional = result.region?.kind === 'sequence'
		? result.region.regions[0]
		: result.region;
	assert.equal(conditional?.kind, 'if');
	if (conditional?.kind === 'if') {
		assert.deepEqual(
			conditional.conditionalValue?.forms,
			['shortcut', 'ternary'],
		);
	}
	assert.deepEqual(
		[...result.region?.sourceBlocks ?? []].toSorted((left, right) =>
			left - right
		),
		[0, 1, 2, 3, 4, 5, 6],
	);
	assert.equal(result.region?.kind, 'sequence');
	assert.equal(result.diagnostics.hasErrors, false);
});

Deno.test('mixed-polarity guard chains recover one structured if', () => {
	// Hermes lowers `window && location && reload()` as two tests that jump to
	// the common failure arm followed by a final test whose polarity is reversed:
	// success jumps to the reload arm. Treating only a uniform two-block prefix
	// as a shortcut leaves overlapping arms and sends this shape to cfg_dag labels.
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('missingWindow'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_1'),
					t.identifier('missingLocation'),
				),
			])],
			branch: t.identifier('r1_1'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r2_1'),
					t.identifier('reloadIsFunction'),
				),
			])],
			branch: t.identifier('r2_1'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('fallback'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('reload'))],
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

	const result = structureCFG(fakeFunction(blocks));
	const summary = summarizeRecursiveCFG(1, result);
	const outer = result.region?.kind === 'sequence'
		? result.region.regions.find((region) => region.kind === 'if')
		: result.region;
	assert.equal(outer?.kind, 'if');
	if (outer?.kind === 'if') {
		assert.deepEqual([...outer.predicateBlocks ?? []], [0, 1, 2]);
		assert.deepEqual(outer.branchEdges, {
			consequent: { from: 0, to: 3, kind: 'normal' },
			alternate: { from: 2, to: 4, kind: 'normal' },
		});
	}
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.regionText ?? '', /cfg_dag_/);
	assert.doesNotMatch(summary.emittedCode ?? '', /cfg_dag_/);
	assert.match(
		summary.emittedCode ?? '',
		/missingWindow \|\| missingLocation \|\| !reloadIsFunction/,
	);
	assert.equal(
		(summary.emittedCode?.match(/fallback/g) ?? []).length,
		1,
	);
	assert.equal(
		(summary.emittedCode?.match(/reload;/g) ?? []).length,
		1,
	);
	assert.deepEqual(
		[...result.region?.sourceBlocks ?? []].toSorted((left, right) =>
			left - right
		),
		[0, 1, 2, 3, 4, 5],
	);
});

Deno.test('terminal shared-target guard chains keep the continuation join', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('a'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('b'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('after'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /cfg_(?:cont|forest)_/);
	assert.match(summary.emittedCode ?? '', /if \(!a && !b\) \{/);
	assert.equal(
		(summary.emittedCode?.match(/after;/g) ?? []).length,
		1,
	);
});

Deno.test('terminal guard chains prefer their live continuation', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('a'),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('b'),
			consequentAddresses: [2, 4],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('after'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('cleanup'))],
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

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /cfg_(?:cont|forest)_/);
	assert.match(summary.emittedCode ?? '', /if \(a \|\| b\) \{/);
	assert.equal(
		(summary.emittedCode?.match(/after;/g) ?? []).length,
		1,
	);
	assert.equal(
		(summary.emittedCode?.match(/cleanup;/g) ?? []).length,
		1,
	);
});

Deno.test('guard chains retain temporaries used by later predicates', () => {
	// The middle block computes a value consumed by the final guard. Absorbing
	// the chain must keep that computation conditional and evaluate it once; the
	// old forest represented each edge to the common failure arm with a forward
	// label.
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('missingFirst'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_1'),
					t.callExpression(t.identifier('probe'), []),
				),
			])],
			branch: t.identifier('r1_1'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r2_1'),
					t.memberExpression(
						t.identifier('r1_1'),
						t.identifier('accepted'),
					),
				),
			])],
			branch: t.identifier('r2_1'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('fallback'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('accepted'))],
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

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /cfg_(?:cont|forest)_/);
	assert.doesNotMatch(summary.emittedCode ?? '', /=>/);
	assert.match(summary.emittedCode ?? '', /let r1_1;/);
	assert.match(
		summary.emittedCode ?? '',
		/\(r1_1 = probe\(\), r1_1\)/,
	);
	assert.equal(
		(summary.emittedCode?.match(/probe\(\)/g) ?? []).length,
		1,
	);
});

Deno.test('guard chains inline private values around escaped assignments', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('missing'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_1'),
					t.callExpression(t.identifier('acquire'), []),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r2_1'),
					t.memberExpression(
						t.identifier('r1_1'),
						t.identifier('accepted'),
					),
				)]),
			],
			branch: t.identifier('r2_1'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('use'),
				[t.identifier('r1_1')],
			))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('fallback'))],
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

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.emittedCode ?? '', /let r1_1;/);
	assert.match(
		summary.emittedCode ?? '',
		/\(r1_1 = acquire\(\), r1_1\.accepted\)/,
	);
	assert.doesNotMatch(summary.emittedCode ?? '', /r2_1 =/);
	assert.equal(
		(summary.emittedCode?.match(/acquire\(\)/g) ?? []).length,
		1,
	);
});

Deno.test('guard predicate inlining preserves independent effect order', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('missing'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_1'),
					t.callExpression(t.identifier('first'), []),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r2_1'),
					t.callExpression(t.identifier('second'), []),
				)]),
			],
			branch: t.callExpression(t.identifier('accepts'), [
				t.identifier('r2_1'),
				t.identifier('r1_1'),
			]),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('accepted'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('fallback'))],
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

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(
		summary.emittedCode ?? '',
		/\(r1_1 = first\(\), r2_1 = second\(\), accepts\(r2_1, r1_1\)\)/,
	);
	assert.doesNotMatch(
		summary.emittedCode ?? '',
		/accepts\(second\(\), first\(\)\)/,
	);
});

Deno.test('conditional Phi arms do not duplicate their terminal join', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_1'),
					t.binaryExpression(
						'!=',
						t.identifier('value'),
						t.nullLiteral(),
					),
				),
			])],
			branch: t.unaryExpression('!', t.identifier('r1_1')),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_2'),
					t.callExpression(t.identifier('some'), []),
				),
			])],
			consequentAddresses: [2],
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
				t.returnStatement(t.unaryExpression(
					'!',
					t.identifier('r0_1'),
				)),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks);
	func.ssa.basicBlocks = new AddressMap([
		[2, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 1 },
				sources: new AddressMap([
					[0, { type: 'register', index: 1, version: 1 }],
					[1, { type: 'register', index: 1, version: 2 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(1, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /\bif\s*\(/);
	assert.match(summary.emittedCode ?? '', /r1_1 && some\(\)/);
	assert.equal(
		(summary.emittedCode?.match(/\breturn\b/g) ?? []).length,
		1,
	);
});

Deno.test('asymmetric successor join structures nested terminal arms', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outer'),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('middle'),
			consequentAddresses: [2, 4],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('terminalGuard'),
			consequentAddresses: [4, 3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.throwStatement(t.identifier('error'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement(t.identifier('value'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const result = structureCFG(fakeFunction(blocks));
	const summary = summarizeRecursiveCFG(0, result);
	assert.deepEqual(
		[...result.region?.sourceBlocks ?? []].toSorted((left, right) =>
			left - right
		),
		[0, 1, 2, 3, 4],
	);
	assert.equal(
		summary.misses.includes(
			'basic-branch-not-structured',
		),
		false,
	);
	assert.match(
		summary.emittedCode ?? '',
		/!outer\s*&&\s*!middle\s*&&\s*terminalGuard/,
	);
	assert.doesNotMatch(summary.emittedCode ?? '', /cfg_forest_/);
});

Deno.test('asymmetric successor join admits loop-bearing arms', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('skipWork'),
			consequentAddresses: [5, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('enterWork'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('done'),
			consequentAddresses: [5, 3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			branch: t.identifier('failed'),
			consequentAddresses: [6, 4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('body'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.identifier('result'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement(t.identifier('early'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		0,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.unstructuredBranches, [], summary.regionText);
	assert.match(summary.emittedCode ?? '', /if \(skipWork\)/);
	assert.match(summary.emittedCode ?? '', /while \(true\)/);
	assert.match(summary.emittedCode ?? '', /return early/);
	assert.match(summary.emittedCode ?? '', /return result/);
});

Deno.test('shared terminal references retain incoming Phi edge actions', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outer'),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('inner'),
			consequentAddresses: [4, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_0'),
					t.stringLiteral('early'),
				),
			])],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r2_0'),
					t.stringLiteral('continued'),
				),
			])],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
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
	const func = fakeFunction(blocks);
	func.ssa.basicBlocks = new AddressMap([
		[5, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 1 },
				sources: new AddressMap([
					[2, { type: 'register', index: 1, version: 0 }],
					[4, { type: 'register', index: 2, version: 0 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const result = structureCFG(func);
	const summary = summarizeRecursiveCFG(0, result);
	assert.deepEqual(summary.misses, []);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.match(summary.emittedCode ?? '', /return r0_1/);
});

Deno.test('catch paths leave a shared terminal Phi outside the try body', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('leaveEarly'),
			consequentAddresses: [1, 5],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.identifier('normalValue'),
			)])],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_2'),
				t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
			)])],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
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
	const func = fakeFunction(blocks, [{
		handler: 4,
		protectedBlocks: [0, 1],
	}]);
	const descriptor = {
		handler: 4,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([0, 1]),
		protectedEntries: new AddressSet([0]),
		catchBody: new AddressSet([4, 5]),
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[4, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});
	func.ssa.basicBlocks = new AddressMap([
		[5, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 1 },
				sources: new AddressMap([
					[0, { type: 'register', index: 1, version: 0 }],
					[1, { type: 'register', index: 1, version: 1 }],
					[4, { type: 'register', index: 1, version: 2 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(1, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.equal(
		(summary.emittedCode?.match(/\breturn\b/g) ?? []).length,
		1,
	);
	assert.match(
		summary.regionText ?? '',
		/tryCatch[\s\S]*catch[\s\S]*basic blocks=0x5/,
	);
});

Deno.test('scoped catch retains exception-only branch and exit Phi', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.identifier('normalValue'),
			)])],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_4'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)]),
				t.returnStatement(t.identifier('r1_4')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('caught'),
				t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
			)])],
			branch: t.identifier('shouldLog'),
			consequentAddresses: [11, 12],
			kind: 'normal',
		}],
		[11, {
			address: 11,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('log'),
				[t.identifier('caught')],
			))],
			consequentAddresses: [12],
			kind: 'normal',
		}],
		[12, {
			address: 12,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_3'),
				t.callExpression(t.identifier('fallback'), []),
			)])],
			consequentAddresses: [4],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{
		handler: 10,
		protectedBlocks: [0],
	}]);
	const descriptor = {
		handler: 10,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([0]),
		protectedEntries: new AddressSet([0]),
		catchBody: null,
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[10, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});
	func.ssa.basicBlocks = new AddressMap([
		[4, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 1, version: 4 },
				sources: new AddressMap([
					[0, { type: 'register', index: 1, version: 1 }],
					[12, { type: 'register', index: 1, version: 3 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const result = structureCFG(func);
	const scoped = tryStructureExceptionRegion(
		result.cfg,
		result.descriptors,
		undefined,
		new AddressSet([0, 10]),
		undefined,
		result.analyses,
	);
	assert.ok(scoped, 'expected the scoped exception to structure');
	assert.equal(scoped.kind, 'tryCatch');
	if (scoped.kind !== 'tryCatch') {
		throw new Error('expected try/catch Region');
	}
	assert.deepEqual(
		[...scoped.handler.sourceBlocks].sort((left, right) => left - right),
		[10, 11, 12],
	);

	const boundedScope = new AddressSet([0, 10]);
	const bounded = tryStructureExceptionRegion(
		result.cfg,
		result.descriptors,
		undefined,
		boundedScope,
		new AddressSet(),
		result.analyses,
		{ exactScope: true },
	);
	assert.ok(bounded, 'expected the bounded exception to structure');
	assert.equal(bounded.kind, 'tryCatch');
	if (bounded.kind !== 'tryCatch') {
		throw new Error('expected bounded try/catch Region');
	}
	assert.deepEqual([...bounded.handler.sourceBlocks], [10]);
	assert.equal(bounded.sourceBlocks.isSubsetOf(boundedScope), true);
	const recursivelyBounded = structureRegionAt(
		0,
		result.cfg,
		result.analyses,
		result.descriptors,
		boundedScope,
	);
	assert.equal(
		recursivelyBounded.sourceBlocks.isSubsetOf(boundedScope),
		true,
	);

	const region = sequenceRegion([
		scoped,
		{
			kind: 'basic',
			body: [...result.cfg.blocks.get(4)!.body],
			sourceBlocks: new AddressSet([4]),
		},
	]);
	const summary = summarizeRecursiveCFG(2, { ...result, region });
	assert.deepEqual(summary.uncoveredBlocks, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.match(
		summary.emittedCode ?? '',
		/catch \(\w+\) \{[\s\S]*if \(!?shouldLog\)[\s\S]*log\([\s\S]*fallback\(\)[\s\S]*r1_4 = r1_3[\s\S]*return r1_4/,
	);
});

Deno.test('protected guard chain joins after its fallback assignment', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('first'),
			consequentAddresses: [1, 3],
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
			body: [],
			branch: t.identifier('third'),
			consequentAddresses: [4, 3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_3'),
				t.stringLiteral('fallback'),
			)])],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_4'),
				t.stringLiteral('transformed'),
			)])],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_5'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)]),
				t.returnStatement(t.identifier('r1_5')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('caught'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.returnStatement(t.stringLiteral('caught')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const protectedBlocks = [0, 1, 2, 3, 4, 5];
	const func = fakeFunction(blocks, [{ handler: 10, protectedBlocks }]);
	const descriptor = {
		handler: 10,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet(protectedBlocks),
		protectedEntries: new AddressSet([0]),
		catchBody: null,
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[10, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});
	func.ssa.basicBlocks = new AddressMap([
		[5, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 1, version: 5 },
				sources: new AddressMap([
					[3, { type: 'register', index: 1, version: 3 }],
					[4, { type: 'register', index: 1, version: 4 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(3, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	const run = new Function(
		'first',
		'second',
		'third',
		summary.emittedCode ?? '',
	) as (first: boolean, second: boolean, third: boolean) => string;
	const outcomes = new Set<string>();
	for (const first of [false, true]) {
		for (const second of [false, true]) {
			for (const third of [false, true]) {
				outcomes.add(run(first, second, third));
			}
		}
	}
	assert.deepEqual(
		[...outcomes].sort(),
		['fallback', 'transformed'],
		`${summary.regionText}\n${summary.emittedCode}`,
	);
});

Deno.test('protected branches leave a shared terminal Phi after try/catch', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('first'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_2'),
				t.identifier('normalValue'),
			)])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.identifier('alternateValue'),
			)])],
			branch: t.identifier('second'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
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
		[4, {
			address: 4,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r2_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.returnStatement(t.identifier('fallbackValue')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{
		handler: 4,
		protectedBlocks: [0, 1, 2],
	}]);
	const descriptor = {
		handler: 4,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([0, 1, 2]),
		protectedEntries: new AddressSet([0]),
		catchBody: null,
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[4, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});
	func.ssa.basicBlocks = new AddressMap([
		[3, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 1 },
				sources: new AddressMap([
					[1, { type: 'register', index: 1, version: 2 }],
					[2, { type: 'register', index: 1, version: 1 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(2, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.equal(
		(summary.emittedCode?.match(/return r0_1/g) ?? []).length,
		1,
	);
	assert.match(
		summary.emittedCode ?? '',
		/try[\s\S]*catch[\s\S]*return r0_1/,
	);
});

Deno.test('large protected branches reference one inert shared return', () => {
	const blocks = new Map<number, IRBlock>();
	blocks.set(0, {
		address: 0,
		body: [t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_1'),
			t.identifier('earlyValue'),
		)])],
		branch: t.identifier('leaveEarly'),
		consequentAddresses: [1, 10],
		kind: 'normal',
	});
	for (let address = 1; address < 9; address++) {
		blocks.set(address, {
			address,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('step'),
				[t.numericLiteral(address)],
			))],
			consequentAddresses: [address + 1],
			kind: 'normal',
		});
	}
	blocks.set(9, {
		address: 9,
		body: [t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier('r1_2'),
			t.identifier('lateValue'),
		)])],
		consequentAddresses: [10],
		kind: 'normal',
	});
	blocks.set(10, {
		address: 10,
		body: [
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r0_1'),
				t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
			)]),
			t.returnStatement(t.identifier('r0_1')),
		],
		consequentAddresses: [],
		kind: 'normal',
	});
	blocks.set(20, {
		address: 20,
		body: [
			t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r2_1'),
				t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
			)]),
			t.returnStatement(t.identifier('fallbackValue')),
		],
		consequentAddresses: [],
		kind: 'normal',
	});
	const protectedBlocks = Array.from({ length: 10 }, (_, address) => address);
	const func = fakeFunction(blocks, [{ handler: 20, protectedBlocks }]);
	const descriptor = {
		handler: 20,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet(protectedBlocks),
		protectedEntries: new AddressSet([0]),
		catchBody: null,
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[20, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});
	func.ssa.basicBlocks = new AddressMap([
		[10, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 1 },
				sources: new AddressMap([
					[0, { type: 'register', index: 1, version: 1 }],
					[9, { type: 'register', index: 1, version: 2 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(3, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.equal(
		(summary.emittedCode?.match(/return r0_1/g) ?? []).length,
		1,
		summary.emittedCode,
	);
	assert.equal(
		(summary.emittedCode?.match(/step\(/g) ?? []).length,
		8,
		summary.emittedCode,
	);
});

Deno.test('contracted catch arms route distinct shared continuations', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('useSharedPath'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('directPath'),
				[],
			))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('sharedPath'),
				[],
			))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement(t.identifier('result'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('caught'),
				t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
			)])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{
		handler: 5,
		protectedBlocks: [1, 2],
	}]);
	const descriptor = {
		handler: 5,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([1, 2]),
		protectedEntries: new AddressSet([1]),
		catchBody: null,
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[5, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});

	const summary = summarizeRecursiveCFG(4, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.deepEqual(summary.unhandledExceptionHandlers, []);
	assert.equal(
		(summary.emittedCode?.match(/directPath\(\)/g) ?? []).length,
		1,
		summary.emittedCode,
	);
	assert.equal(
		(summary.emittedCode?.match(/sharedPath\(\)/g) ?? []).length,
		1,
		summary.emittedCode,
	);
	assert.equal(
		(summary.emittedCode?.match(/return result/g) ?? []).length,
		1,
		summary.emittedCode,
	);
});

Deno.test('contracted finalizers route distinct normal continuations', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('bodyContinuation'),
				[],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('finalizerContinuation'),
				[],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement(t.identifier('result'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [],
			consequentAddresses: [2],
			kind: 'normal',
		}],
	]);
	const result = structureCFG(fakeFunction(blocks, [{
		handler: 5,
		protectedBlocks: [0],
	}]));
	const basic = (address: number): Region => ({
		kind: 'basic',
		body: [],
		sourceBlocks: new AddressSet([address]),
	});
	const exceptionRegion: Region = {
		kind: 'tryFinally',
		body: basic(0),
		finalizer: basic(5),
		handlerAddress: 5,
		protectedBlocks: new AddressSet([0]),
		sourceBlocks: new AddressSet([0, 5]),
	};
	const copiedFinalizerRegion: Region = {
		...exceptionRegion,
		finalizer: basic(2),
		sourceBlocks: new AddressSet([0, 2]),
	};
	assert.deepEqual(
		[...regionCoveredBlocks(copiedFinalizerRegion)].toSorted(
			(left, right) => left - right,
		),
		[0, 2, 5],
	);

	const region = tryStructureBoundedContinuationForest(
		result.cfg,
		result.analyses,
		() => null,
		{
			entries: new AddressSet([0]),
			protectedBlocks: new AddressSet([0]),
			exceptionAt: (entry) => entry === 0 ? exceptionRegion : null,
		},
	);

	assert.ok(region, 'expected the finalizer continuations to compose');
	assert.deepEqual(
		[...region.sourceBlocks].sort((left, right) => left - right),
		[0, 1, 2, 3, 5],
	);
	assert.deepEqual(regionDuplicateOwnership(region, result.cfg), []);
});

Deno.test('Phi-only protected exit bridges stay before a shared catch join', () => {
	const phiDeclaration = (name: string) =>
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier(name),
			t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
		)]);
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('choose'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r6_1'),
				t.identifier('leftValue'),
			)])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r6_2'),
				t.identifier('rightValue'),
			)])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				phiDeclaration('r6_3'),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_1'),
					t.identifier('r6_3'),
				)]),
			],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('Catch'),
					[],
				)),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_2'),
					t.identifier('fallbackValue'),
				)]),
			],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [
				phiDeclaration('r0_3'),
				t.returnStatement(t.identifier('r0_3')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{
		handler: 4,
		protectedBlocks: [0, 1, 2],
	}]);
	const descriptor = {
		handler: 4,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([0, 1, 2]),
		protectedEntries: new AddressSet([0]),
		catchBody: null,
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		boundedFinallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[4, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});
	func.ssa.basicBlocks = new AddressMap([
		[3, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 6, version: 3 },
				sources: new AddressMap([
					[1, { type: 'register', index: 6, version: 1 }],
					[2, { type: 'register', index: 6, version: 2 }],
				]),
			}],
		}],
		[5, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 3 },
				sources: new AddressMap([
					[3, { type: 'register', index: 0, version: 1 }],
					[4, { type: 'register', index: 0, version: 2 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(5, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.equal((summary.emittedCode?.match(/\breturn\b/g) ?? []).length, 1);
	assert.match(summary.emittedCode ?? '', /try[\s\S]*catch[\s\S]*return/);
});

Deno.test('split protected ranges retain copy bridges and private terminals', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('hasWrapped'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('continueWork'),
				[],
			))],
			branch: t.identifier('chooseResult'),
			consequentAddresses: [8, 9],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.assignmentExpression(
				'=',
				t.identifier('r2_1'),
				t.identifier('wrapped'),
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			branch: t.identifier('isCallable'),
			consequentAddresses: [4, 5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.identifier('r2_1'),
			)])],
			consequentAddresses: [7],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_2'),
				t.identifier('original'),
			)])],
			consequentAddresses: [7],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [
				t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('Catch'),
					[],
				)),
				t.returnStatement(t.identifier('caught')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_3'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)]),
				t.returnStatement(t.identifier('r1_3')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.returnStatement(t.identifier('firstResult'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.returnStatement(t.identifier('secondResult'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{
		handler: 6,
		protectedBlocks: [0, 3, 4, 5],
	}]);
	const descriptor = {
		handler: 6,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([0, 3, 4, 5]),
		protectedEntries: new AddressSet([0, 3]),
		catchBody: new AddressSet([6]),
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		boundedFinallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[6, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});
	func.ssa.basicBlocks = new AddressMap([
		[7, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 1, version: 3 },
				sources: new AddressMap([
					[4, { type: 'register', index: 1, version: 1 }],
					[5, { type: 'register', index: 1, version: 2 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(5, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.match(summary.emittedCode ?? '', /try[\s\S]*return r1_3/);
	const catchEnd = summary.emittedCode?.indexOf('catch') ?? -1;
	const continuation = summary.emittedCode?.indexOf('continueWork') ?? -1;
	assert.ok(catchEnd >= 0 && continuation > catchEnd, summary.emittedCode);
});

Deno.test('normal finalizer copies remain protected fallthroughs', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [7],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('protectedWork'),
				[],
			))],
			consequentAddresses: [24],
			kind: 'normal',
		}],
		[24, {
			address: 24,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('finallyWork'),
				[],
			))],
			consequentAddresses: [73],
			kind: 'normal',
		}],
		[73, {
			address: 73,
			body: [t.returnStatement(t.identifier('result'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[75, {
			address: 75,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('caught'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('finallyWork'),
					[],
				)),
				t.throwStatement(t.identifier('caught')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{
		handler: 75,
		protectedBlocks: [7],
	}]);
	const descriptor = {
		handler: 75,
		kind: 'finally' as const,
		protectedBlocks: new AddressSet([7]),
		protectedEntries: new AddressSet([7]),
		catchBody: null,
		canonicalFinallyAddress: 75,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet([24]),
		finallyBodyBlocks: [75],
		boundedFinallyBodyBlocks: [75],
		finallyCopies: [{
			canonical: 75,
			copyRoot: 24,
			next: 73,
			kind: 'normalExit' as const,
			copyBlocks: [24],
		}],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[75, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});

	const summary = summarizeRecursiveCFG(1, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.emittedCode ?? '', /try[\s\S]*finally/);
	assert.doesNotMatch(summary.emittedCode ?? '', /\bbreak\b/);
	assert.equal(
		(summary.emittedCode?.match(/finallyWork\(\)/g) ?? []).length,
		1,
		summary.emittedCode,
	);
});

Deno.test('branching finalizer copies retain protected return completions', () => {
	const cleanup = () =>
		t.expressionStatement(t.callExpression(t.identifier('cleanup'), []));
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('normalResult'),
				t.callExpression(t.identifier('normalValue'), []),
			)])],
			consequentAddresses: [10],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('caught'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('catchResult'),
					t.callExpression(t.identifier('fallbackValue'), []),
				)]),
			],
			consequentAddresses: [20],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [cleanup()],
			branch: t.identifier('normalCleanupDone'),
			consequentAddresses: [11, 13],
			kind: 'normal',
		}],
		[11, {
			address: 11,
			body: [],
			consequentAddresses: [10],
			kind: 'normal',
		}],
		[13, {
			address: 13,
			body: [t.returnStatement(t.identifier('normalResult'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[20, {
			address: 20,
			body: [cleanup()],
			branch: t.identifier('catchCleanupDone'),
			consequentAddresses: [21, 23],
			kind: 'normal',
		}],
		[21, {
			address: 21,
			body: [],
			consequentAddresses: [20],
			kind: 'normal',
		}],
		[23, {
			address: 23,
			body: [t.returnStatement(t.identifier('catchResult'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[30, {
			address: 30,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('pendingException'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				cleanup(),
				t.throwStatement(t.identifier('pendingException')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{
		handler: 5,
		protectedBlocks: [1],
	}, {
		handler: 30,
		protectedBlocks: [1, 5],
	}]);
	const catchDescriptor = {
		handler: 5,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([1]),
		protectedEntries: new AddressSet([1]),
		catchBody: new AddressSet([5]),
		canonicalFinallyAddress: 30,
		canonicalFinallyOwnership: {
			finallyAddress: 30,
			protectsCatch: true,
			missingProtectedBlocks: new AddressSet<number>(),
			valid: true,
		},
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		boundedFinallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const finallyDescriptor = {
		handler: 30,
		kind: 'finally' as const,
		protectedBlocks: new AddressSet([1, 5]),
		protectedEntries: new AddressSet([1]),
		catchBody: null,
		canonicalFinallyAddress: 30,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet([10, 20]),
		finallyBodyBlocks: [30],
		boundedFinallyBodyBlocks: [30],
		finallyCopies: [{
			canonical: 30,
			copyRoot: 10,
			next: null,
			kind: 'abruptExit' as const,
		}, {
			canonical: 30,
			copyRoot: 20,
			next: null,
			kind: 'catchTrailer' as const,
		}],
		finallyCopySuffixes: [{
			canonical: 30,
			copyRoot: 10,
			ownerBlock: 30,
			next: null,
			kind: 'abruptExitTrailer' as const,
			statements: [cleanup()],
			skipRanges: [{ block: 10, start: 0, end: 1 }],
		}, {
			canonical: 30,
			copyRoot: 20,
			ownerBlock: 30,
			next: null,
			kind: 'catchTrailer' as const,
			statements: [cleanup()],
			skipRanges: [{ block: 20, start: 0, end: 1 }],
		}],
		enclosingFinallyCopyRoots: [],
	};
	const catchNode = { descriptor: catchDescriptor, children: [] };
	const finallyNode = {
		descriptor: finallyDescriptor,
		children: [catchNode],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		finalizerEdgeActions: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [
		catchDescriptor,
		finallyDescriptor,
	];
	exceptionModel.finalizerEdgeActions = () => [{
		handler: 30,
		edge: { from: 30, to: 10, kind: 'normal' },
		canonical: 30,
		copyRoot: 10,
		ownerBlock: 30,
		next: null,
		kind: 'abrupt-copy',
		completion: 'break-or-continue',
		statements: [cleanup()],
		skipRanges: [{ block: 10, start: 0, end: 1 }],
		depth: 0,
	}, {
		handler: 30,
		edge: { from: 30, to: 20, kind: 'normal' },
		canonical: 30,
		copyRoot: 20,
		ownerBlock: 30,
		next: null,
		kind: 'catch-copy',
		completion: 'break-or-continue',
		statements: [cleanup()],
		skipRanges: [{ block: 20, start: 0, end: 1 }],
		depth: 0,
	}];
	exceptionModel.structuredRegionForest = () => ({
		roots: [finallyNode],
		nodeByHandler: new Map<number, unknown>([
			[5, catchNode],
			[30, finallyNode],
		]),
		parentByHandler: new Map([[5, 30]]),
	});

	const summary = summarizeRecursiveCFG(1, structureCFG(func));
	const code = summary.emittedCode ?? '';
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(
		code,
		/try \{[\s\S]*return normalResult;[\s\S]*catch[\s\S]*return catchResult;[\s\S]*finally/,
	);
	assert.equal((code.match(/cleanup\(\)/g) ?? []).length, 1, code);
});

Deno.test('protected for-in guards remain inside their catch region', () => {
	const intrinsicTuple = (
		names: string[],
		intrinsic: string,
		args: t.Expression[],
	) => t.variableDeclaration('const', [t.variableDeclarator(
		t.arrayPattern(names.map((name) => t.identifier(name))),
		t.callExpression(t.v8IntrinsicIdentifier(intrinsic), args),
	)]);
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [intrinsicTuple(
				['r3_1', 'r2_1', 'r1_1'],
				'GetPNameList',
				[t.identifier('source')],
			)],
			branch: t.binaryExpression(
				'===',
				t.identifier('r3_1'),
				t.identifier('undefined'),
			),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [intrinsicTuple(
				['r4_1', 'r2_2'],
				'GetNextPName',
				[
					t.identifier('r3_1'),
					t.identifier('source'),
					t.identifier('r2_1'),
				],
			)],
			branch: t.binaryExpression(
				'===',
				t.identifier('r4_1'),
				t.identifier('undefined'),
			),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[t.identifier('r4_1')],
			))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement(t.identifier('result'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('Catch'),
				[],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{
		handler: 4,
		protectedBlocks: [0, 1, 2],
	}]);
	const descriptor = {
		handler: 4,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([0, 1, 2]),
		protectedEntries: new AddressSet([0]),
		catchBody: new AddressSet([4]),
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		boundedFinallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[4, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});

	const summary = summarizeRecursiveCFG(5, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /tryCatch[\s\S]*syntax=forIn/);
	assert.match(
		summary.emittedCode ?? '',
		/try \{[\s\S]*for \(const r4_1 in source\)/,
	);
	assert.doesNotMatch(summary.emittedCode ?? '', /GetPNameList|GetNextPName/);
});

Deno.test('catch backedges form exception-driven retry loops', () => {
	const phiDeclaration = (name: string) =>
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier(name),
			t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
		)]);
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_0'),
				t.booleanLiteral(false),
			)])],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [phiDeclaration('r1_1')],
			branch: t.identifier('chooseLeft'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r0_1'),
				t.stringLiteral('left'),
			)])],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r0_2'),
				t.stringLiteral('right'),
			)])],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				phiDeclaration('r1_2'),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r2_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('handleThrow'),
					[t.identifier('r2_1')],
				)),
			],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [
				phiDeclaration('r0_3'),
				t.returnStatement(t.identifier('r0_3')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{
		handler: 4,
		protectedBlocks: [1, 2, 3],
	}]);
	const descriptor = {
		handler: 4,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([1, 2, 3]),
		protectedEntries: new AddressSet([1]),
		catchBody: null,
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		boundedFinallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[4, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});
	func.ssa.basicBlocks = new AddressMap([
		[1, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 1, version: 1 },
				sources: new AddressMap([
					[0, { type: 'register', index: 1, version: 0 }],
					[4, { type: 'register', index: 1, version: 2 }],
				]),
			}],
		}],
		[4, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 1, version: 2 },
				sources: new AddressMap([
					[1, { type: 'register', index: 1, version: 1 }],
					[2, { type: 'register', index: 1, version: 1 }],
					[3, { type: 'register', index: 1, version: 1 }],
				]),
			}],
		}],
		[5, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 3 },
				sources: new AddressMap([
					[2, { type: 'register', index: 0, version: 1 }],
					[3, { type: 'register', index: 0, version: 2 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const result = structureCFG(func);
	const summary = summarizeRecursiveCFG(2, result);
	assert.equal(
		result.analyses.naturalLoops.loops.length,
		0,
		'catch-to-protected retry edges belong to the exception descriptor',
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /retry=0x1->0x5/);
	assert.match(
		summary.emittedCode ?? '',
		/while \(true\) \{\s*try \{[\s\S]*break;[\s\S]*catch/,
	);
	assert.match(summary.emittedCode ?? '', /handleThrow\(r2_1\)/);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
});

Deno.test('exceptional predecessors retain an enclosing natural loop', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.identifier('initialize'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('done'),
			consequentAddresses: [2, 6],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('work'),
				[],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('advance'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('error'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('handle'),
					[t.identifier('error')],
				)),
			],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{ handler: 4, protectedBlocks: [2] }]);
	const descriptor = {
		handler: 4,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([2]),
		protectedEntries: new AddressSet([2]),
		catchBody: new AddressSet([4]),
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		boundedFinallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[4, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});

	const result = structureCFG(func);
	const summary = summarizeRecursiveCFG(2, result);
	assert.deepEqual(
		result.analyses.naturalLoops.loops.map((loop) => loop.header),
		[1],
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.loopCoverageIssues, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.emittedCode ?? '', /while \(true\)/);
	assert.match(summary.emittedCode ?? '', /if \(done\)/);
	assert.match(summary.emittedCode ?? '', /try \{/);
	assert.match(summary.emittedCode ?? '', /catch/);
});

Deno.test('conditional catch trailers form exception retry loops', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.identifier('initialize'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('prepareAttempt'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('work'),
				[],
			))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('error'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('handle'),
					[t.identifier('error')],
				)),
				t.expressionStatement(t.identifier('advanceAttempt')),
			],
			branch: t.identifier('retry'),
			consequentAddresses: [5, 1],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.identifier('result'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{ handler: 4, protectedBlocks: [2] }]);
	const descriptor = {
		handler: 4,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([2]),
		protectedEntries: new AddressSet([2]),
		catchBody: new AddressSet([4]),
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		boundedFinallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[4, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});

	const summary = summarizeRecursiveCFG(3, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /retry=0x1->0x5/);
	assert.match(summary.emittedCode ?? '', /while \(true\)/);
	assert.match(summary.emittedCode ?? '', /if \(!retry\) \{\s*break;/);
	assert.match(summary.emittedCode ?? '', /initialize;[\s\S]*while/);
	assert.equal(
		(summary.emittedCode?.match(/prepareAttempt/g) ?? []).length,
		1,
	);
});

Deno.test('rethrow guards on the way back form exception retry loops', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.identifier('prepareAttempt'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('work'),
				[],
			))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.returnStatement(t.identifier('result'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('error'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.expressionStatement(t.identifier('advanceAttempt')),
			],
			branch: t.identifier('exhausted'),
			consequentAddresses: [5, 6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('logRetry'))],
			consequentAddresses: [7],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.throwStatement(t.identifier('error'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [],
			branch: t.identifier('retryable'),
			consequentAddresses: [8, 0],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.throwStatement(t.identifier('error'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{ handler: 4, protectedBlocks: [1] }]);
	const descriptor = {
		handler: 4,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([1]),
		protectedEntries: new AddressSet([1]),
		catchBody: new AddressSet([4, 5, 6, 7, 8]),
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		boundedFinallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[4, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});

	const summary = summarizeRecursiveCFG(4, structureCFG(func));
	// The trailer tests twice before it reaches the backedge, and each rejecting
	// arm rethrows instead of leaving the loop, so the retry is the catch's own
	// fallthrough rather than a conditional `break`.
	assert.match(summary.regionText ?? '', /retry=0x0->0x2/);
	assert.match(summary.emittedCode ?? '', /while \(true\)/);
	assert.equal(
		(summary.emittedCode?.match(/prepareAttempt/g) ?? []).length,
		1,
		summary.emittedCode,
	);
	assert.equal(
		(summary.emittedCode?.match(/work\(\)/g) ?? []).length,
		1,
		summary.emittedCode,
	);
	assert.equal(
		(summary.emittedCode?.match(/throw error/g) ?? []).length,
		2,
		summary.emittedCode,
	);
});

Deno.test('protected shared DAGs retain an outside Phi join', () => {
	const phi = t.variableDeclaration('const', [t.variableDeclarator(
		t.identifier('r0_3'),
		t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
	)]);
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outer'),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('inner'),
			consequentAddresses: [2, 4],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r0_1'),
				t.stringLiteral('left'),
			)])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r0_2'),
				t.stringLiteral('shared'),
			)])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [phi, t.returnStatement(t.identifier('r0_3'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [
				t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('Catch'),
					[],
				)),
				t.returnStatement(t.stringLiteral('caught')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [{
		handler: 5,
		protectedBlocks: [0, 1, 2, 4],
	}]);
	const descriptor = {
		handler: 5,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet([0, 1, 2, 4]),
		protectedEntries: new AddressSet([0]),
		catchBody: new AddressSet([5]),
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		boundedFinallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[5, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});
	func.ssa.basicBlocks = new AddressMap([
		[3, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 3 },
				sources: new AddressMap([
					[2, { type: 'register', index: 0, version: 1 }],
					[4, { type: 'register', index: 0, version: 2 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(4, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.match(summary.emittedCode ?? '', /"left"/);
	assert.match(summary.emittedCode ?? '', /"shared"/);
});

Deno.test('terminal ladders may share a terminal leaf', () => {
	const terminal = (address: number, value: string): IRBlock => ({
		address,
		body: [t.returnStatement(t.stringLiteral(value))],
		consequentAddresses: [],
		kind: 'normal',
	});
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outer'),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('left'),
			consequentAddresses: [2, 5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [],
			branch: t.identifier('right'),
			consequentAddresses: [5, 6],
			kind: 'normal',
		}],
		[2, terminal(2, 'left')],
		[5, terminal(5, 'shared')],
		[6, terminal(6, 'right')],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, []);
	assert.deepEqual(summary.emitDiagnostics, []);
	// The shared leaf used to be reached by referencing it from both ladders,
	// which emitted its statements twice. Recovering the join by arm ownership
	// makes 0x5 the join of both ladders and the trailer of the enclosing
	// sequence instead, so it is emitted once and every path still falls into
	// it: `outer && right` and `!outer && !left` leave both Ifs through an
	// empty arm.
	assert.match(summary.regionText ?? '', /if join=0x5 header=0x0/);
	assert.match(summary.regionText ?? '', /basic blocks=0x5/);
	assert.equal(
		(summary.emittedCode?.match(/return "shared"/g) ?? []).length,
		1,
	);
});

Deno.test('bounded continuations retain shared nonterminal subtrees once', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outer'),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('leftGuard'),
			consequentAddresses: [3, 5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [],
			branch: t.identifier('rightGuard'),
			consequentAddresses: [3, 6],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			branch: t.identifier('sharedBranch'),
			consequentAddresses: [7, 8],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.stringLiteral('left'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement(t.stringLiteral('right'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.returnStatement(t.stringLiteral('shared-left'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.returnStatement(t.stringLiteral('shared-right'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	// The shared subtree is the branch's trailer, owned once by the enclosing
	// Sequence. It used to need a `cfg_cont` label because the arms return and
	// so have no common postdominator to prove that ownership with.
	assert.match(summary.regionText ?? '', /if join=0x3 header=0x0/);
	assert.doesNotMatch(summary.regionText ?? '', /label=cfg_cont_0_/);
	assert.equal(
		(summary.emittedCode?.match(/sharedBranch/g) ?? []).length,
		1,
		summary.emittedCode,
	);
	assert.equal(
		(summary.emittedCode?.match(/return "shared-left"/g) ?? []).length,
		1,
	);
	assert.equal(
		(summary.emittedCode?.match(/return "shared-right"/g) ?? []).length,
		1,
	);
});

Deno.test('nested guard ladders fill an enclosing weak-SESE arm', () => {
	const terminal = (address: number, value: string): IRBlock => ({
		address,
		body: [t.returnStatement(t.stringLiteral(value))],
		consequentAddresses: [],
		kind: 'normal',
	});
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outer'),
			consequentAddresses: [2, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('continuationBranch'),
			consequentAddresses: [9, 10],
			kind: 'normal',
		}],
		[9, terminal(9, 'continuation-left')],
		[10, terminal(10, 'continuation-right')],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('guardA'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			branch: t.identifier('guardB'),
			consequentAddresses: [4, 1],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [],
			branch: t.identifier('guardC'),
			consequentAddresses: [5, 1],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [],
			branch: t.identifier('guardD'),
			consequentAddresses: [1, 6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [],
			branch: t.identifier('inner'),
			consequentAddresses: [7, 8],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.expressionStatement(t.identifier('innerBody'))],
			consequentAddresses: [8],
			kind: 'normal',
		}],
		[8, terminal(8, 'innerContinuation')],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /label=cfg_exit_1/);
	// The region still owns the labelled exit -- asserted above -- but emission
	// now folds the single guard into its negation, so the label never reaches
	// the output.
	assert.match(summary.emittedCode ?? '', /if \(guardA \|\| !guardB\)/);
	assert.doesNotMatch(summary.emittedCode ?? '', /cfg_exit_1/);
});

Deno.test('nested terminal guards retain loop ownership inside an arm', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outerGuard'),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('loopGuard'),
			consequentAddresses: [2, 4],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [4, 2],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.equal(
		(summary.emittedCode?.match(/return;/g) ?? []).length,
		1,
		summary.emittedCode,
	);
});

Deno.test('distinct terminal guards retain their loop continuation', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('done'),
			consequentAddresses: [1, 6],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('invalid'),
			consequentAddresses: [2, 5],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('beforeLoop'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [4, 3],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('afterLoop'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.throwStatement(t.identifier('failure'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.emittedCode ?? '', /while \(true\)/);
	assert.match(summary.emittedCode ?? '', /return;/);
	assert.doesNotMatch(summary.emittedCode ?? '', /cfg_(?:cont|forest)_/);
	assert.equal(
		(summary.emittedCode?.match(/beforeLoop;/g) ?? []).length,
		1,
	);
	assert.equal(
		(summary.emittedCode?.match(/afterLoop;/g) ?? []).length,
		1,
	);
	assert.match(summary.emittedCode ?? '', /throw failure/);
});

Deno.test('optional loops retain a nonterminal continuation', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outerGuard'),
			consequentAddresses: [1, 5],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('enterLoop'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [3, 2],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('afterLoop'))],
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

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.emittedCode ?? '', /afterLoop/);
});

Deno.test('optional loops compose before a later catch region', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('enterLoop'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [2, 1],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('protectedBody'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement(t.identifier('done'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('handle'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(
			fakeFunction(blocks, [{ handler: 4, protectedBlocks: [2] }]),
		),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.emittedCode ?? '', /while \(true\)/);
	assert.match(summary.emittedCode ?? '', /try \{/);
	assert.match(summary.emittedCode ?? '', /catch/);
});

Deno.test('optional loop arms retain a structured suffix before their join', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('enterLoop'),
			consequentAddresses: [1, 5],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [3, 1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('loopSuffix'))],
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

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.emittedCode ?? '', /loopBody/);
	assert.match(summary.emittedCode ?? '', /loopSuffix/);
});

Deno.test('loop branches retain ordered shared terminal completions', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('finishEarly'),
			consequentAddresses: [1, 9],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('exhausted'),
			consequentAddresses: [2, 9],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('visitValue'))],
			branch: t.identifier('valid'),
			consequentAddresses: [8, 1],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.returnStatement(t.booleanLiteral(false))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.returnStatement(t.booleanLiteral(true))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /return:0x1->0x9/);
	assert.match(summary.regionText ?? '', /return:0x2->0x8/);
	assert.match(summary.regionText ?? '', /terminalReference entry=0x8/);
	assert.match(summary.emittedCode ?? '', /return false/);
	assert.match(summary.emittedCode ?? '', /return true/);
});

Deno.test('bounded scope forest accepts outside terminal completion with unrelated exceptions', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('chooseLeft'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('left'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('right'))],
			branch: t.identifier('skipShared'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('shared'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('afterShared'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.identifier('done'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.expressionStatement(t.identifier('unrelatedProtected'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.throwStatement(t.identifier('unrelatedError'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const result = structureCFG(
		fakeFunction(blocks, [{ handler: 9, protectedBlocks: [8] }]),
	);

	const region = tryStructureBoundedScopeForest(
		result.cfg,
		result.analyses,
		() => null,
		{
			entry: 0,
			allowed: new AddressSet([0, 1, 2, 3, 4]),
			labelPrefix: 'test_scope',
			completion: (_from, to) =>
				to === 5
					? {
						kind: 'return',
						argument: t.identifier('done'),
						sourceBlocks: new AddressSet([5]),
					}
					: null,
		},
	);

	assert.ok(region, 'expected bounded forest to compose partial shared DAG');
	assert.deepEqual([...region.sourceBlocks].sort((a, b) => a - b), [
		0,
		1,
		2,
		3,
		4,
		5,
	]);
	assert.deepEqual(regionDuplicateOwnership(region, result.cfg), []);
});

Deno.test('bounded scope forest accepts enclosing exception boundaries', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('chooseLeft'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('left'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('right'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.throwStatement(t.identifier('caught'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const result = structureCFG(
		fakeFunction(blocks, [{ handler: 9, protectedBlocks: [0, 1, 2] }]),
	);
	const allowed = new AddressSet([0, 1, 2]);

	const terminalCompletion = (from: number, to: number): Region | null =>
		to === 3
			? {
				kind: 'terminalReference',
				entry: 3,
				edge: { from, to, kind: 'normal' },
				sourceBlocks: new AddressSet<number>(),
			}
			: null;

	assert.equal(
		tryStructureBoundedScopeForest(
			result.cfg,
			result.analyses,
			() => null,
			{
				entry: 0,
				allowed,
				labelPrefix: 'test_scope',
				completion: terminalCompletion,
			},
		),
		null,
	);
	const region = tryStructureBoundedScopeForest(
		result.cfg,
		result.analyses,
		() => null,
		{
			entry: 0,
			allowed,
			labelPrefix: 'test_scope',
			completion: terminalCompletion,
			exceptionBoundary: (from, to) => allowed.has(from) && to === 9,
		},
	);

	assert.ok(region, 'expected enclosing exceptional transfer as boundary');
	assert.deepEqual([...region.sourceBlocks].sort((a, b) => a - b), [0, 1, 2]);
	assert.deepEqual(regionDuplicateOwnership(region, result.cfg), []);
});

Deno.test('bounded arm sequencing retains optional loop ownership', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outerGuard'),
			consequentAddresses: [1, 6],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('prelude'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('enterLoop'),
			consequentAddresses: [3, 5],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [5, 3],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('afterLoop'))],
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

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.emittedCode ?? '', /prelude/);
	assert.match(summary.emittedCode ?? '', /loopBody/);
	assert.match(summary.emittedCode ?? '', /afterLoop/);
});

Deno.test('nonterminal arms own a loop forest before their shared join', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('finishEarly'),
			consequentAddresses: [1, 10],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('useDefault'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('selectDefault'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.arrayPattern([
					t.identifier('iteratorState'),
					t.identifier('iteratorSource'),
				]),
				t.callExpression(t.v8IntrinsicIdentifier('IteratorBegin'), [
					t.identifier('values'),
				]),
			)])],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.arrayPattern([
					t.identifier('value'),
					t.identifier('nextState'),
				]),
				t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
					t.identifier('iteratorState'),
					t.identifier('iteratorSource'),
				]),
			)])],
			branch: t.identifier('loopDone'),
			consequentAddresses: [5, 6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [],
			branch: t.identifier('addSuffix'),
			consequentAddresses: [7, 8],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [],
			branch: t.identifier('nestedSuffix'),
			consequentAddresses: [8, 9],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.expressionStatement(t.identifier('suffixArm'))],
			consequentAddresses: [9],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.expressionStatement(t.identifier('afterLoop'))],
			consequentAddresses: [10],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.emittedCode ?? '', /selectDefault/);
	assert.match(summary.emittedCode ?? '', /for \(const value of values\)/);
	assert.match(summary.emittedCode ?? '', /afterLoop/);
	assert.match(
		summary.emittedCode ?? '',
		/if \(addSuffix \|\| !nestedSuffix\)/,
	);
	assert.doesNotMatch(summary.emittedCode ?? '', /cfg_exit_9/);
	assert.equal(
		summary.emittedCode?.match(/afterLoop/g)?.length,
		1,
		summary.emittedCode,
	);
	assert.match(summary.emittedCode ?? '', /}\nreturn;$/);
});

Deno.test('for-of break paths retain private exit trailers', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.arrayPattern([
					t.identifier('iteratorState'),
					t.identifier('iteratorSource'),
				]),
				t.callExpression(t.v8IntrinsicIdentifier('IteratorBegin'), [
					t.identifier('values'),
				]),
			)])],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.arrayPattern([
					t.identifier('value'),
					t.identifier('nextState'),
				]),
				t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
					t.identifier('iteratorState'),
					t.identifier('iteratorSource'),
				]),
			)])],
			branch: t.identifier('done'),
			consequentAddresses: [2, 5],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('found'),
			consequentAddresses: [3, 4],
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
			body: [t.expressionStatement(t.assignmentExpression(
				'=',
				t.identifier('foundValue'),
				t.booleanLiteral(true),
			))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.assignmentExpression(
				'=',
				t.identifier('foundValue'),
				t.booleanLiteral(false),
			))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement(t.identifier('foundValue'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.emittedCode ?? '', /for \(const value of values\)/);
	assert.match(
		summary.emittedCode ?? '',
		/if \(found\) \{\s*foundValue = true;\s*_cfg_loop_1_completed = false;\s*break;/,
	);
	assert.match(
		summary.emittedCode ?? '',
		/if \(_cfg_loop_1_completed\) \{\s*foundValue = false;/,
	);
	assert.doesNotMatch(
		summary.emittedCode ?? '',
		/IteratorBegin|IteratorNext/,
	);
});

Deno.test(
	'protected for-of shared exit Phis cross an iterator-close trailer',
	() => {
		const close = (exceptional: boolean) =>
			t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('IteratorClose'),
				[
					t.identifier('nextState'),
					t.booleanLiteral(exceptional),
				],
			));
		const blocks = new Map<number, IRBlock>([
			[0, {
				address: 0,
				body: [
					t.variableDeclaration('const', [
						t.variableDeclarator(
							t.identifier('r10_2'),
							t.booleanLiteral(false),
						),
					]),
					t.variableDeclaration('const', [t.variableDeclarator(
						t.arrayPattern([
							t.identifier('iteratorState'),
							t.identifier('iteratorSource'),
						]),
						t.callExpression(
							t.v8IntrinsicIdentifier('IteratorBegin'),
							[t.identifier('values')],
						),
					)]),
				],
				consequentAddresses: [1],
				kind: 'normal',
			}],
			[1, {
				address: 1,
				body: [t.variableDeclaration('const', [t.variableDeclarator(
					t.arrayPattern([
						t.identifier('value'),
						t.identifier('nextState'),
					]),
					t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
						t.identifier('iteratorState'),
						t.identifier('iteratorSource'),
					]),
				)])],
				branch: t.identifier('done'),
				consequentAddresses: [2, 6],
				kind: 'normal',
			}],
			[2, {
				address: 2,
				body: [],
				branch: t.identifier('found'),
				consequentAddresses: [3, 4],
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
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('r10_3'),
						t.booleanLiteral(true),
					)]),
				],
				consequentAddresses: [5],
				kind: 'normal',
			}],
			[5, {
				address: 5,
				body: [close(false)],
				consequentAddresses: [6],
				kind: 'normal',
			}],
			[6, {
				address: 6,
				body: [t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r10_4'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)])],
				consequentAddresses: [7],
				kind: 'normal',
			}],
			[7, {
				address: 7,
				body: [t.returnStatement(t.identifier('r10_4'))],
				consequentAddresses: [],
				kind: 'normal',
			}],
			[8, {
				address: 8,
				body: [
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('caught'),
						t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
					)]),
					close(true),
					t.throwStatement(t.identifier('caught')),
				],
				consequentAddresses: [],
				kind: 'normal',
			}],
		]);

		const func = fakeFunction(blocks, [{
			handler: 8,
			protectedBlocks: [2, 4],
		}]);
		func.ssa.basicBlocks = new AddressMap([
			[6, {
				ssaInstructions: [{
					instruction: 'Phi',
					destination: { type: 'register', index: 10, version: 4 },
					sources: new AddressMap([
						[1, { type: 'register', index: 10, version: 2 }],
						[5, { type: 'register', index: 10, version: 3 }],
					]),
				}],
			}],
		]) as typeof func.ssa.basicBlocks;
		const descriptor = {
			handler: 8,
			kind: 'finally' as const,
			protectedEntries: new AddressSet([2]),
			protectedBlocks: new AddressSet([2, 4]),
			catchBody: null,
			canonicalFinallyAddress: 8,
			canonicalFinallyOwnership: null,
			finallyCopyRoots: new AddressSet<number>(),
			finallyBodyBlocks: [8],
			boundedFinallyBodyBlocks: [8],
			finallyCopies: [],
			finallyCopySuffixes: [],
			enclosingFinallyCopyRoots: [],
		};
		const exceptions = func.exceptions as unknown as {
			structuredRegionDescriptors: () => unknown[];
			structuredRegionForest: () => unknown;
		};
		exceptions.structuredRegionDescriptors = () => [descriptor];
		exceptions.structuredRegionForest = () => ({
			roots: [{
				descriptor,
				children: [],
			}],
			nodeByHandler: new Map([[8, {
				descriptor,
				children: [],
			}]]),
			parentByHandler: new Map(),
		});

		const summary = summarizeRecursiveCFG(1, structureCFG(func));
		assert.deepEqual(summary.misses, [], summary.regionText);
		assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
		assert.match(
			summary.emittedCode ?? '',
			/for \(const value of values\)/,
		);
		assert.match(
			summary.emittedCode ?? '',
			/r10_4 = r10_3;\s*_cfg_loop_1_completed = false;\s*break;/,
		);
		assert.match(
			summary.emittedCode ?? '',
			/if \(_cfg_loop_1_completed\) \{\s*r10_4 = r10_2;/,
		);
		assert.doesNotMatch(
			summary.emittedCode ?? '',
			/IteratorBegin|IteratorNext|%Phi/,
		);
	},
);

Deno.test(
	'for-of exhaustion and protected body breaks retain distinct returns',
	() => {
		const tuple = (
			names: string[],
			intrinsic: string,
			args: t.Expression[],
		) => t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern(names.map((name) => t.identifier(name))),
			t.callExpression(t.v8IntrinsicIdentifier(intrinsic), args),
		)]);
		const close = (iterator: string, exceptional: boolean) =>
			t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('IteratorClose'),
				[t.identifier(iterator), t.booleanLiteral(exceptional)],
			));
		const blocks = new Map<number, IRBlock>([
			[0, {
				address: 0,
				body: [tuple(
					['outerValue', 'outerState'],
					'IteratorNext',
					[t.identifier('outerIterator'), t.identifier('outerNext')],
				)],
				consequentAddresses: [1],
				kind: 'normal',
			}],
			[1, {
				address: 1,
				body: [tuple(
					['innerState', 'innerSource'],
					'IteratorBegin',
					[t.identifier('innerValues')],
				)],
				consequentAddresses: [2],
				kind: 'normal',
			}],
			[2, {
				address: 2,
				body: [tuple(
					['innerValue', 'nextInnerState'],
					'IteratorNext',
					[
						t.identifier('innerState'),
						t.identifier('innerSource'),
					],
				)],
				branch: t.identifier('innerDone'),
				consequentAddresses: [3, 6],
				kind: 'normal',
			}],
			[3, {
				address: 3,
				body: [],
				branch: t.identifier('matches'),
				consequentAddresses: [2, 5],
				kind: 'normal',
			}],
			[5, {
				address: 5,
				body: [close('nextInnerState', false)],
				consequentAddresses: [7],
				kind: 'normal',
			}],
			[6, {
				address: 6,
				body: [
					close('outerState', false),
					t.returnStatement(t.booleanLiteral(true)),
				],
				consequentAddresses: [],
				kind: 'normal',
			}],
			[7, {
				address: 7,
				body: [
					close('outerState', false),
					t.returnStatement(t.booleanLiteral(false)),
				],
				consequentAddresses: [],
				kind: 'normal',
			}],
			[8, {
				address: 8,
				body: [
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('caught'),
						t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
					)]),
					close('outerState', true),
					t.throwStatement(t.identifier('caught')),
				],
				consequentAddresses: [],
				kind: 'normal',
			}],
		]);
		const func = fakeFunction(blocks, [{
			handler: 8,
			protectedBlocks: [1, 2, 3, 5],
		}]);
		const descriptor = {
			handler: 8,
			kind: 'finally' as const,
			protectedBlocks: new AddressSet([1, 2, 3, 5]),
			protectedEntries: new AddressSet([1]),
			catchBody: null,
			canonicalFinallyAddress: 8,
			canonicalFinallyOwnership: null,
			finallyCopyRoots: new AddressSet<number>(),
			finallyBodyBlocks: [8],
			boundedFinallyBodyBlocks: [8],
			finallyCopies: [],
			finallyCopySuffixes: [],
			enclosingFinallyCopyRoots: [],
		};
		const exceptionModel = func.exceptions as unknown as {
			structuredRegionDescriptors: () => unknown[];
			structuredRegionForest: () => unknown;
		};
		exceptionModel.structuredRegionDescriptors = () => [descriptor];
		exceptionModel.structuredRegionForest = () => ({
			roots: [{ descriptor, children: [] }],
			nodeByHandler: new Map([[8, { descriptor, children: [] }]]),
			parentByHandler: new Map(),
		});

		const summary = summarizeRecursiveCFG(1, structureCFG(func));
		const code = summary.emittedCode ?? '';

		assert.deepEqual(summary.misses, [], summary.regionText);
		assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
		assert.match(code, /let _cfg_loop_2_completed = true;/);
		assert.match(
			code,
			/_cfg_loop_2_completed = false;\s*break;/,
		);
		assert.match(
			code,
			/if \(_cfg_loop_2_completed\) \{[\s\S]*?return true;\s*\}[\s\S]*?return false;/,
		);
		assert.doesNotMatch(code, /return true;\s*break;/);
	},
);

Deno.test('conditional sibling loops compose as one loop forest', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('useLeftLoop'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('leftLoop'))],
			branch: t.identifier('leftDone'),
			consequentAddresses: [5, 1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('rightLoop'))],
			branch: t.identifier('rightDone'),
			consequentAddresses: [5, 3],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('afterLoops'))],
			branch: t.identifier('returnLeft'),
			consequentAddresses: [6, 7],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.returnStatement(t.numericLiteral(1))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		2,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.equal(summary.regionText?.match(/loop id=/g)?.length, 2);
	assert.match(summary.regionText ?? '', /if join=0x5 header=0x0/);
	assert.match(summary.emittedCode ?? '', /leftLoop/);
	assert.match(summary.emittedCode ?? '', /rightLoop/);
	assert.doesNotMatch(
		summary.emittedCode ?? '',
		/break cfg_forest_0_5/,
	);
	assert.equal(
		(summary.emittedCode?.match(/afterLoops/g) ?? []).length,
		1,
	);
});

Deno.test('short-circuit loop arms hand their shared trailer to the sequence', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('first'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.identifier('second'),
			)])],
			branch: t.identifier('r1_1'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('alternateLoop'))],
			branch: t.identifier('alternateDone'),
			consequentAddresses: [5, 2],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('consequentLoop'))],
			branch: t.identifier('consequentDone'),
			consequentAddresses: [5, 3],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('sharedTrailer'))],
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

	const summary = summarizeRecursiveCFG(
		2,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.emittedCode ?? '', /first\s*\|\|\s*second/);
	assert.doesNotMatch(summary.emittedCode ?? '', /cfg_forest_0_5/);
	assert.equal(
		(summary.emittedCode?.match(/sharedTrailer/g) ?? []).length,
		1,
		summary.emittedCode,
	);
});

Deno.test('conditional forests retain sibling self-loop arms', () => {
	const conditional = (
		address: number,
		fallthrough: number,
		taken: number,
	): IRBlock => ({
		address,
		body: [],
		branch: t.identifier(`test_${address}`),
		consequentAddresses: [fallthrough, taken],
		kind: 'normal',
	});
	const jump = (address: number, target: number): IRBlock => ({
		address,
		body: [t.expressionStatement(t.identifier(`body_${address}`))],
		consequentAddresses: [target],
		kind: 'normal',
	});
	const blocks = new Map<number, IRBlock>([
		[0, conditional(0, 1, 20)],
		[1, conditional(1, 2, 3)],
		[2, jump(2, 4)],
		[3, jump(3, 4)],
		[4, conditional(4, 5, 8)],
		[5, conditional(5, 6, 8)],
		[6, jump(6, 8)],
		[8, conditional(8, 9, 18)],
		[9, conditional(9, 10, 18)],
		[10, conditional(10, 11, 14)],
		[11, conditional(11, 14, 30)],
		[14, conditional(14, 15, 16)],
		[15, jump(15, 16)],
		[16, conditional(16, 17, 30)],
		[17, conditional(17, 30, 17)],
		[18, jump(18, 30)],
		[20, conditional(20, 21, 22)],
		[21, jump(21, 22)],
		[22, conditional(22, 23, 30)],
		[23, conditional(23, 30, 23)],
		[30, {
			address: 30,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.equal(
		summary.regionText?.match(/loop id=/g)?.length,
		2,
		summary.regionText,
	);
	const labels = summary.emittedCode?.match(/^\s*cfg_exit_[\da-f]+: \{/gm) ??
		[];
	assert.equal(
		new Set(labels.map((label) => label.trim())).size,
		labels.length,
	);
});

Deno.test('shared alternate guards retain a loop in their shared arm', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('enterArm'),
			consequentAddresses: [1, 20],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('useShared'),
			consequentAddresses: [2, 4],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('bypassShared'),
			consequentAddresses: [4, 20],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [],
			branch: t.identifier('hasValues'),
			consequentAddresses: [5, 20],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('copyValue'))],
			branch: t.identifier('hasMore'),
			consequentAddresses: [20, 5],
			kind: 'normal',
		}],
		[20, {
			address: 20,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.equal(
		summary.emittedCode?.match(/copyValue/g)?.length,
		1,
		summary.emittedCode,
	);
});

Deno.test('shared alternate guards preserve non-empty guard branches', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('headerSkipsToSharedTail'),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('enterShared'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('prepareGuard'))],
			branch: t.identifier('guardRejects'),
			consequentAddresses: [3, 9],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('sharedStart'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('sharedTail'))],
			consequentAddresses: [9],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.expressionStatement(t.identifier('latch'))],
			branch: t.identifier('hasMore'),
			consequentAddresses: [20, 0],
			kind: 'normal',
		}],
		[20, {
			address: 20,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.unstructuredBranches, [], summary.regionText);
	assert.equal(
		summary.emittedCode?.match(/prepareGuard/g)?.length,
		1,
		summary.emittedCode,
	);
	assert.equal(
		summary.emittedCode?.match(/sharedStart/g)?.length,
		1,
		summary.emittedCode,
	);
});

Deno.test('protected divergent loop exits are classified within one handler state', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('hasNext'),
			consequentAddresses: [1, 10],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[],
			))],
			branch: t.identifier('stopNow'),
			consequentAddresses: [0, 5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.identifier('earlyResult'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('afterLoop'),
				[],
			))],
			consequentAddresses: [11],
			kind: 'normal',
		}],
		[11, {
			address: 11,
			body: [t.returnStatement(t.identifier('ordinaryResult'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[20, {
			address: 20,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('caught'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.returnStatement(t.identifier('fallbackResult')),
			],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const protectedBlocks = [0, 1, 5, 10, 11];
	const func = fakeFunction(blocks, [{ handler: 20, protectedBlocks }]);
	const descriptor = {
		handler: 20,
		kind: 'catch' as const,
		protectedBlocks: new AddressSet(protectedBlocks),
		protectedEntries: new AddressSet([0]),
		catchBody: null,
		canonicalFinallyAddress: null,
		canonicalFinallyOwnership: null,
		finallyCopyRoots: new AddressSet<number>(),
		finallyBodyBlocks: null,
		finallyCopies: [],
		finallyCopySuffixes: [],
		enclosingFinallyCopyRoots: [],
	};
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => [descriptor];
	exceptionModel.structuredRegionForest = () => ({
		roots: [{ descriptor, children: [] }],
		nodeByHandler: new Map([[20, { descriptor, children: [] }]]),
		parentByHandler: new Map(),
	});

	const result = structureCFG(func);
	const loop = tryStructureLoopRegion(
		result.cfg,
		result.analyses,
		result.descriptors,
	);
	assert.ok(loop, 'expected the protected natural loop to be recognized');
	assert.equal(loop.kind, 'loop');
	if (loop.kind !== 'loop') throw new Error('expected loop Region');
	assert.equal(loop.exits.find((exit) => exit.to === 5)?.kind, 'return');
	assert.equal(loop.exits.find((exit) => exit.to === 10)?.kind, 'break');

	const crossingBlocks = [0, 1, 10, 11];
	const crossingFunc = fakeFunction(blocks, [{
		handler: 20,
		protectedBlocks: crossingBlocks,
	}]);
	const crossingDescriptor = {
		...descriptor,
		protectedBlocks: new AddressSet(crossingBlocks),
	};
	const crossingModel = crossingFunc.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	crossingModel.structuredRegionDescriptors = () => [crossingDescriptor];
	crossingModel.structuredRegionForest = () => ({
		roots: [{ descriptor: crossingDescriptor, children: [] }],
		nodeByHandler: new Map([[
			20,
			{ descriptor: crossingDescriptor, children: [] },
		]]),
		parentByHandler: new Map(),
	});
	const crossingResult = structureCFG(crossingFunc);
	const crossingLoop = tryStructureLoopRegion(
		crossingResult.cfg,
		crossingResult.analyses,
		crossingResult.descriptors,
	);
	assert.equal(crossingLoop?.kind, 'loop');
	if (crossingLoop?.kind !== 'loop') throw new Error('expected loop Region');
	assert.equal(
		crossingLoop.exits.find((exit) => exit.to === 5)?.kind,
		'break',
	);
});

Deno.test('loop exits keep an entry-shared return as their continuation', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('initialDone'),
			consequentAddresses: [4, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[],
			))],
			branch: t.identifier('nextDone'),
			consequentAddresses: [4, 1],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.match(
		summary.regionText ?? '',
		/exits=break:0x1->0x4/,
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.equal(
		(summary.emittedCode?.match(/return;/g) ?? []).length,
		1,
		summary.emittedCode,
	);
});

Deno.test('loop exits retain ordered trailers and join Phi actions', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r1_1'),
					t.stringLiteral('bypass'),
				),
			])],
			branch: t.identifier('enterLoop'),
			consequentAddresses: [1, 5],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('runBody'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r2_1'),
					t.stringLiteral('direct'),
				),
			])],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [5, 1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.expressionStatement(t.callExpression(
					t.identifier('exitTrailer'),
					[],
				)),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r3_1'),
						t.stringLiteral('trailer'),
					),
				]),
			],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
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
	const func = fakeFunction(blocks);
	func.ssa.basicBlocks = new AddressMap([
		[5, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 1 },
				sources: new AddressMap([
					[0, { type: 'register', index: 1, version: 1 }],
					[2, { type: 'register', index: 2, version: 1 }],
					[3, { type: 'register', index: 3, version: 1 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(0, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /continuation=0x5/);
	assert.match(summary.regionText ?? '', /exit\[0\] basic blocks=0x3/);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.match(
		summary.emittedCode ?? '',
		/exitTrailer\(\);[\s\S]*r0_1 = r3_1;[\s\S]*break;/,
	);
});

Deno.test('guarded loops retain ordinary and bypass continuations', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('enterDirectly'),
			consequentAddresses: [1, 10],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('guardPrelude'))],
			branch: t.identifier('enterAfterPrelude'),
			consequentAddresses: [50, 10],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [],
			branch: t.identifier('finishNormallyAtHeader'),
			consequentAddresses: [11, 50],
			kind: 'normal',
		}],
		[11, {
			address: 11,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			branch: t.identifier('leaveOuterSequence'),
			consequentAddresses: [12, 20],
			kind: 'normal',
		}],
		[12, {
			address: 12,
			body: [t.expressionStatement(t.identifier('latchBody'))],
			branch: t.identifier('continueLoop'),
			consequentAddresses: [50, 10],
			kind: 'normal',
		}],
		[20, {
			address: 20,
			body: [t.expressionStatement(t.identifier('bypassTrailer'))],
			consequentAddresses: [60],
			kind: 'normal',
		}],
		[50, {
			address: 50,
			body: [t.expressionStatement(t.identifier('ordinarySuffix'))],
			consequentAddresses: [60],
			kind: 'normal',
		}],
		[60, {
			address: 60,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		0,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.regionText ?? '', /label=cfg_exit_32/);
	assert.match(summary.regionText ?? '', /label=cfg_exit_3c/);
	assert.match(summary.emittedCode ?? '', /guardPrelude/);
	assert.match(summary.emittedCode ?? '', /bypassTrailer/);
	assert.match(summary.emittedCode ?? '', /ordinarySuffix/);
	assert.match(
		summary.emittedCode ?? '',
		/bypassTrailer;[\s\S]*break cfg_exit_3c;/,
	);
});

Deno.test('nested loop breaks keep trailers beside labelled exits', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('outerHeader'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('leaveAll'),
			consequentAddresses: [9, 3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			branch: t.identifier('takeFirstTrailer'),
			consequentAddresses: [4, 5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('firstTrailer'))],
			consequentAddresses: [8],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [],
			branch: t.identifier('takeSecondTrailer'),
			consequentAddresses: [6, 7],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.expressionStatement(t.identifier('secondTrailer'))],
			consequentAddresses: [8],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.expressionStatement(t.identifier('innerLatch'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.expressionStatement(t.identifier('outerLatch'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		0,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.loopCoverageIssues, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /return:loop_1:0x2->0x9/);
	assert.match(summary.emittedCode ?? '', /firstTrailer/);
	assert.match(summary.emittedCode ?? '', /secondTrailer/);
});

Deno.test('loop break with continuation Phi routes both trailers', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('enterLoop'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_0'),
				t.identifier('directValue'),
			)])],
			branch: t.identifier('skipTrailer'),
			consequentAddresses: [4, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			branch: t.identifier('takeTrailer'),
			consequentAddresses: [3, 1],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_1'),
					t.identifier('trailerValue'),
				)]),
				t.expressionStatement(t.identifier('sharedTrailer')),
			],
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
				t.expressionStatement(t.callExpression(
					t.identifier('afterSharedTrailer'),
					[t.identifier('r0_1')],
				)),
			],
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

	const func = fakeFunction(blocks);
	func.ssa.basicBlocks = new AddressMap([
		[4, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 1 },
				sources: new AddressMap([
					[1, { type: 'register', index: 1, version: 0 }],
					[3, { type: 'register', index: 1, version: 1 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(0, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /break:0x1->0x4\[seq:/);
	assert.match(summary.regionText ?? '', /break:0x2->0x3/);
	assert.match(summary.emittedCode ?? '', /break cfg_/);
	assert.match(summary.emittedCode ?? '', /sharedTrailer/);
});

Deno.test('loops behind an arm prelude retain loop ownership', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outerGuard'),
			consequentAddresses: [1, 5],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('prelude'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [4, 3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('loopBody'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('loopTrailer'))],
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

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.emittedCode ?? '', /prelude/);
	assert.match(summary.emittedCode ?? '', /loopBody/);
	assert.match(summary.emittedCode ?? '', /loopTrailer/);
});

Deno.test('loop bodies recursively structure internal diamond branches', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [5, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('chooseArm'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('leftArm'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('rightArm'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [],
			consequentAddresses: [0],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.regionText ?? '', /if join=0x4/);
	assert.match(summary.emittedCode ?? '', /leftArm/);
	assert.match(summary.emittedCode ?? '', /rightArm/);
});

Deno.test('loop bodies compose an unrecognized residual subgraph', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.identifier('prologue'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('outerHeader'))],
			branch: t.identifier('enterChild'),
			consequentAddresses: [2, 5],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('childHeader'))],
			branch: t.identifier('childBranch'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('childBody'))],
			branch: t.identifier('childAgain'),
			consequentAddresses: [4, 2],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('childExit'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('outerTail'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.expressionStatement(t.identifier('outerLatch'))],
			branch: t.identifier('repeat'),
			consequentAddresses: [1, 7],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	// The outer header enters a child loop whose two exits share one trailer, so
	// no single branch builder recognizes the body. Before the loop-local control
	// skeleton owned that residual, the body kept block 0x2 as a Basic Region and
	// dropped the whole child loop below it.
	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.loopCoverageIssues, [], summary.regionText);
	assert.equal(
		(summary.regionText ?? '').match(/loop id=/g)?.length,
		2,
		summary.regionText,
	);
	assert.match(summary.emittedCode ?? '', /childBody/);
	assert.match(summary.emittedCode ?? '', /childExit/);
	assert.match(summary.emittedCode ?? '', /outerTail/);
});

Deno.test('wide guard ladders in an arm retain every guard and its suffix', () => {
	const branch = (
		address: number,
		name: string,
		targets: number[],
	): [number, IRBlock] => [address, {
		address,
		body: [t.expressionStatement(t.identifier(name))],
		branch: t.identifier(`${name}Test`),
		consequentAddresses: targets,
		kind: 'normal',
	}];
	// A guard ladder reached through one arm of the entry branch. Every guard
	// leaves for the same shared suffix and the ladder ends at the enclosing
	// join, so the arm must own each guard exactly once.
	const ladder = 30;
	const shared = 900;
	const sharedTail = 901;
	const join = 910;
	const blocks = new Map<number, IRBlock>([
		branch(0, 'entry', [1, join]),
		...Array.from(
			{ length: ladder },
			(_, index) =>
				branch(index + 1, `guard${index}`, [
					index + 2 > ladder ? join : index + 2,
					shared,
				]),
		),
		[shared, {
			address: shared,
			body: [t.expressionStatement(t.identifier('sharedSuffix'))],
			consequentAddresses: [sharedTail],
			kind: 'normal',
		}],
		[sharedTail, {
			address: sharedTail,
			body: [t.returnStatement(t.identifier('early'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[join, {
			address: join,
			body: [t.returnStatement(t.identifier('joined'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		2,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.unstructuredBranches, [], summary.regionText);
	assert.match(summary.emittedCode ?? '', /guard0/);
	assert.match(summary.emittedCode ?? '', /guard29/);
	assert.match(summary.emittedCode ?? '', /return early/);
	assert.match(summary.emittedCode ?? '', /return joined/);
});

Deno.test('dispatch terminators are owned as skeleton nodes', () => {
	const dispatch = (
		address: number,
		targets: number[],
	): [number, IRBlock] => [
		address,
		{
			address,
			body: [
				t.expressionStatement(t.identifier('dispatchPrelude')),
				t.expressionStatement(
					t.callExpression(t.v8IntrinsicIdentifier('UIntSwitchImm'), [
						t.identifier('selector'),
						t.numericLiteral(0),
						t.numericLiteral(1),
					]),
				),
			],
			consequentAddresses: targets,
			kind: 'normal',
		},
	];
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.identifier('preheader'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		// A switch-terminated loop header: the ordinary builders cannot split the
		// dispatch from its cases, so the body composes the header itself.
		dispatch(1, [4, 2, 3]),
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('firstCase'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('secondCase'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('defaultCase'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('latch'))],
			branch: t.identifier('again'),
			consequentAddresses: [1, 6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		3,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.loopCoverageIssues, [], summary.regionText);
	assert.match(summary.regionText ?? '', /switch cases=2 header=0x1/);
	assert.match(summary.emittedCode ?? '', /switch \(selector\)/);
	assert.match(summary.emittedCode ?? '', /firstCase/);
	assert.match(summary.emittedCode ?? '', /secondCase/);
	assert.match(summary.emittedCode ?? '', /defaultCase/);
	assert.doesNotMatch(summary.emittedCode ?? '', /UIntSwitchImm/);
});

Deno.test('a switch case owns the handler of a try it contains', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [
				t.expressionStatement(t.identifier('dispatchPrelude')),
				t.expressionStatement(
					t.callExpression(t.v8IntrinsicIdentifier('UIntSwitchImm'), [
						t.identifier('selector'),
						t.numericLiteral(0),
						t.numericLiteral(1),
					]),
				),
			],
			consequentAddresses: [4, 1, 2],
			kind: 'normal',
		}],
		// The protected block of a try that lives wholly inside this case.
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('risky'),
				[],
			))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('secondCase'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('caught'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('recover'),
					[t.identifier('caught')],
				)),
			],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('defaultCase'))],
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

	const summary = summarizeRecursiveCFG(
		5,
		structureCFG(
			fakeFunction(blocks, [{ handler: 3, protectedBlocks: [1] }]),
		),
	);
	// Nothing branches to a handler, so the case body has to admit it before
	// the recursion can open the exception Region inside the case.
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(
		summary.unhandledExceptionHandlers,
		[],
		summary.regionText,
	);
	assert.match(summary.regionText ?? '', /switch cases=2/);
	assert.match(summary.regionText ?? '', /tryCatch handler=0x3/);
	assert.match(summary.emittedCode ?? '', /try \{\s*risky\(\)/);
	assert.match(summary.emittedCode ?? '', /catch \(\w+\) \{[\s\S]*recover/);
});

Deno.test('a switch marker embedded in AST is never a complete Region', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.whileStatement(
				t.booleanLiteral(true),
				t.blockStatement([
					t.expressionStatement(t.callExpression(
						t.v8IntrinsicIdentifier('UIntSwitchImm'),
						[
							t.identifier('tag'),
							t.numericLiteral(0),
							t.numericLiteral(27),
						],
					)),
					t.breakStatement(),
				]),
			)],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		3,
		structureCFG(fakeFunction(blocks)),
	);
	assert.ok(summary.misses.includes('switches-not-structured'));
	assert.match(summary.emittedCode ?? '', /%UIntSwitchImm/);
});

Deno.test('loop headers retain direct latch Phi edges and escaping values', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.callExpression(t.identifier('headerValue'), []),
			)])],
			branch: t.identifier('skipBody'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r2_1'),
				t.callExpression(t.identifier('bodyValue'), []),
			)])],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r3_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r4_1'),
					t.callExpression(t.identifier('consume'), [
						t.identifier('r3_1'),
					]),
				)]),
			],
			branch: t.identifier('repeat'),
			consequentAddresses: [4, 0],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement(t.identifier('r4_1'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks);
	func.ssa.basicBlocks = new AddressMap([
		[3, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 3, version: 1 },
				sources: new AddressMap([
					[0, { type: 'register', index: 1, version: 1 }],
					[1, { type: 'register', index: 2, version: 1 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(0, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /headerLatch=0x3 bodyEntry=0x1/);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.match(
		summary.emittedCode ?? '',
		/let r4_1;[\s\S]*while \(true\)[\s\S]*if \(skipBody\)[\s\S]*r3_1 = r1_1;[\s\S]*else[\s\S]*r3_1 = r2_1;/,
	);
	assert.match(summary.emittedCode ?? '', /r4_1 = consume\(r3_1\)/);
	assert.match(summary.emittedCode ?? '', /return r4_1/);
});

Deno.test('header-latch loops can contain a nested for-in', () => {
	const intrinsicTuple = (
		names: string[],
		intrinsic: string,
		args: t.Expression[],
	) => t.variableDeclaration('const', [t.variableDeclarator(
		t.arrayPattern(names.map((name) => t.identifier(name))),
		t.callExpression(t.v8IntrinsicIdentifier(intrinsic), args),
	)]);
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('skipOuterBody'),
			consequentAddresses: [1, 9],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('outerBody'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [intrinsicTuple(
				['propertyList', 'beginIndex', 'endIndex'],
				'GetPNameList',
				[t.identifier('object')],
			)],
			branch: t.binaryExpression(
				'===',
				t.identifier('propertyList'),
				t.identifier('undefined'),
			),
			consequentAddresses: [3, 8],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [intrinsicTuple(
				['key', 'nextIndex'],
				'GetNextPName',
				[
					t.identifier('propertyList'),
					t.identifier('object'),
					t.identifier('beginIndex'),
				],
			)],
			branch: t.binaryExpression(
				'===',
				t.identifier('key'),
				t.identifier('undefined'),
			),
			consequentAddresses: [4, 8],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[t.identifier('key')],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.expressionStatement(t.identifier('outerSuffix'))],
			consequentAddresses: [9],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.expressionStatement(t.identifier('outerLatch'))],
			branch: t.identifier('repeatOuter'),
			consequentAddresses: [10, 0],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		0,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /headerLatch=0x9 bodyEntry=0x1/);
	assert.match(summary.regionText ?? '', /syntax=forIn/);
	assert.match(summary.emittedCode ?? '', /for \(const key in object\)/);
	assert.doesNotMatch(
		summary.emittedCode ?? '',
		/GetPNameList|GetNextPName|unsupported fallback/,
	);
});

Deno.test('header-latch loops retain an early body exit', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_1'),
				t.callExpression(t.identifier('headerValue'), []),
			)])],
			branch: t.identifier('skipBody'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r2_1'),
				t.callExpression(t.identifier('bodyValue'), []),
			)])],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('leaveEarly'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r3_1'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('consume'),
					[t.identifier('r3_1')],
				)),
			],
			branch: t.identifier('repeat'),
			consequentAddresses: [4, 0],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks);
	func.ssa.basicBlocks = new AddressMap([
		[3, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 3, version: 1 },
				sources: new AddressMap([
					[0, { type: 'register', index: 1, version: 1 }],
					[2, { type: 'register', index: 2, version: 1 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(0, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /headerLatch=0x3 bodyEntry=0x1/);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Phi/);
	assert.match(summary.emittedCode ?? '', /r3_1 = r1_1/);
	assert.match(summary.emittedCode ?? '', /r3_1 = r2_1/);
	assert.match(summary.emittedCode ?? '', /if \(leaveEarly\)/);
});

Deno.test('bounded parent loops retain optional child loops with branched exit trailers', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('skipOuterBody'),
			consequentAddresses: [1, 9],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('enterChild'),
			consequentAddresses: [2, 6],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('childHeader'))],
			branch: t.identifier('leaveThroughTrailer'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('childBody'))],
			branch: t.identifier('repeatChild'),
			consequentAddresses: [6, 2],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('trailerHeader'))],
			branch: t.identifier('takeTrailerArm'),
			consequentAddresses: [6, 5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('trailerArm'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.expressionStatement(t.identifier('outerSuffix'))],
			consequentAddresses: [9],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.expressionStatement(t.identifier('outerLatch'))],
			branch: t.identifier('repeatOuter'),
			consequentAddresses: [10, 0],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		0,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /headerLatch=0x9 bodyEntry=0x1/);
	assert.match(summary.regionText ?? '', /exit\[0\].*blocks=0x4,0x5/);
	assert.match(summary.emittedCode ?? '', /if \(!enterChild\)/);
	assert.match(summary.emittedCode ?? '', /trailerHeader/);
	assert.match(summary.emittedCode ?? '', /trailerArm/);
});

Deno.test('loop-local DAGs retain alternate backedge arms', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [9, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('restartEarly'),
			consequentAddresses: [3, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('earlyBackedge'))],
			consequentAddresses: [0],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			branch: t.identifier('chooseArm'),
			consequentAddresses: [5, 4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('leftArm'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('latch'))],
			consequentAddresses: [0],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.loopCoverageIssues, [], summary.regionText);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /if join=0x3/);
	assert.match(summary.emittedCode ?? '', /earlyBackedge;[\s\S]*continue;/);
	assert.match(summary.emittedCode ?? '', /leftArm/);
	assert.match(summary.emittedCode ?? '', /latch/);
});

Deno.test('loop-local joins do not consume a shared downstream latch', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [9, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('outerChoice'),
			consequentAddresses: [3, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('bypassEarlyJoin'),
			consequentAddresses: [5, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('rightArm'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('earlyJoin'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('bypass'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.expressionStatement(t.identifier('sharedLatch'))],
			branch: t.identifier('continueLoop'),
			consequentAddresses: [9, 0],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.rawEmission.diagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /if join=0x6/);
	assert.equal(
		(summary.emittedCode?.match(/sharedLatch;/g) ?? []).length,
		1,
	);
	assert.match(summary.emittedCode ?? '', /sharedLatch/);
});

Deno.test('nested optional loops remain nested', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('chooseOuterArm'),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('outerLeftArm'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('innerPrelude'))],
			branch: t.identifier('enterInner'),
			consequentAddresses: [5, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('innerBody'))],
			branch: t.identifier('keepInner'),
			consequentAddresses: [5, 2],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.identifier('outerLatch'))],
			branch: t.identifier('keepOuter'),
			consequentAddresses: [6, 0],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.equal((summary.regionText?.match(/loop id=/g) ?? []).length, 2);
	assert.match(summary.emittedCode ?? '', /innerPrelude/);
	assert.match(summary.emittedCode ?? '', /innerBody/);
});

Deno.test(
	'native-generator for-of cleanup protection does not truncate a nested body branch',
	() => {
		const tuple = (
			names: string[],
			intrinsic: string,
			args: t.Expression[],
		) => t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern(names.map((name) => t.identifier(name))),
			t.callExpression(t.v8IntrinsicIdentifier(intrinsic), args),
		)]);
		const blocks = new Map<number, IRBlock>([
			[0, {
				address: 0,
				body: [tuple(
					['iteratorState', 'iteratorSource'],
					'IteratorBegin',
					[t.identifier('values')],
				)],
				consequentAddresses: [1],
				kind: 'normal',
			}],
			[1, {
				address: 1,
				body: [tuple(
					['value', 'nextState'],
					'IteratorNext',
					[
						t.identifier('iteratorState'),
						t.identifier('iteratorSource'),
					],
				)],
				branch: t.binaryExpression(
					'===',
					t.identifier('value'),
					t.identifier('undefined'),
				),
				consequentAddresses: [2, 6],
				kind: 'normal',
			}],
			[2, {
				address: 2,
				body: [t.expressionStatement(t.identifier('bodyPrelude'))],
				branch: t.identifier('chooseLeft'),
				consequentAddresses: [3, 4],
				kind: 'normal',
			}],
			[3, {
				address: 3,
				body: [t.expressionStatement(t.identifier('leftBody'))],
				consequentAddresses: [5],
				kind: 'normal',
			}],
			[4, {
				address: 4,
				body: [t.expressionStatement(t.identifier('rightBody'))],
				consequentAddresses: [5],
				kind: 'normal',
			}],
			[5, {
				address: 5,
				body: [t.expressionStatement(t.identifier('latchBody'))],
				consequentAddresses: [1],
				kind: 'normal',
			}],
			[6, {
				address: 6,
				body: [t.returnStatement()],
				consequentAddresses: [],
				kind: 'normal',
			}],
			[7, {
				address: 7,
				body: [
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('caught'),
						t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
					)]),
					t.expressionStatement(t.callExpression(
						t.v8IntrinsicIdentifier('IteratorClose'),
						[t.identifier('iteratorState'), t.booleanLiteral(true)],
					)),
					t.throwStatement(t.identifier('caught')),
				],
				consequentAddresses: [],
				kind: 'normal',
			}],
		]);
		const func = fakeFunction(blocks, [{
			handler: 7,
			protectedBlocks: [2, 3, 4, 5],
		}]);
		Object.assign(func, {
			isAsync: false,
			isGenerator: true,
			isNativeGenerator: true,
			isLoweredGenerator: false,
		});
		const descriptor = {
			handler: 7,
			kind: 'finally' as const,
			protectedBlocks: new AddressSet([2, 3, 4, 5]),
			protectedEntries: new AddressSet([2]),
			catchBody: null,
			canonicalFinallyAddress: 7,
			canonicalFinallyOwnership: null,
			finallyCopyRoots: new AddressSet<number>(),
			finallyBodyBlocks: [7],
			boundedFinallyBodyBlocks: [7],
			finallyCopies: [],
			finallyCopySuffixes: [],
			enclosingFinallyCopyRoots: [],
		};
		const exceptionModel = func.exceptions as unknown as {
			structuredRegionDescriptors: () => unknown[];
			structuredRegionForest: () => unknown;
		};
		exceptionModel.structuredRegionDescriptors = () => [descriptor];
		exceptionModel.structuredRegionForest = () => ({
			roots: [{ descriptor, children: [] }],
			nodeByHandler: new Map([[7, { descriptor, children: [] }]]),
			parentByHandler: new Map(),
		});

		const summary = summarizeRecursiveCFG(1, structureCFG(func));
		assert.deepEqual(summary.misses, [], summary.regionText);
		assert.deepEqual(summary.loopCoverageIssues, [], summary.regionText);
		assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
		assert.match(summary.regionText ?? '', /syntax=forOf/);
		assert.match(summary.emittedCode ?? '', /if \(chooseLeft\)/);
		assert.match(summary.emittedCode ?? '', /leftBody/);
		assert.match(summary.emittedCode ?? '', /rightBody/);
		assert.doesNotMatch(
			summary.emittedCode ?? '',
			/IteratorBegin|IteratorNext|IteratorClose/,
		);
		const spanningDescriptor = {
			...descriptor,
			protectedBlocks: new AddressSet([5, 6]),
			protectedEntries: new AddressSet([5]),
		};
		exceptionModel.structuredRegionDescriptors = () => [spanningDescriptor];
		exceptionModel.structuredRegionForest = () => ({
			roots: [{ descriptor: spanningDescriptor, children: [] }],
			nodeByHandler: new Map([[
				7,
				{ descriptor: spanningDescriptor, children: [] },
			]]),
			parentByHandler: new Map(),
		});
		const spanningResult = structureCFG(func);
		assert.deepEqual(
			[
				...spanningResult.descriptors.exceptions
					.elidedIteratorCleanupHandlers,
			],
			[7],
		);
	},
);

Deno.test(
	'for-of cleanup boundary structures branched protected body',
	() => {
		const tuple = (
			names: string[],
			intrinsic: string,
			args: t.Expression[],
		) => t.variableDeclaration('const', [t.variableDeclarator(
			t.arrayPattern(names.map((name) => t.identifier(name))),
			t.callExpression(t.v8IntrinsicIdentifier(intrinsic), args),
		)]);
		const blocks = new Map<number, IRBlock>([
			[0, {
				address: 0,
				body: [tuple(
					['iteratorState', 'iteratorSource'],
					'IteratorBegin',
					[t.identifier('values')],
				)],
				consequentAddresses: [1],
				kind: 'normal',
			}],
			[1, {
				address: 1,
				body: [tuple(
					['value', 'nextState'],
					'IteratorNext',
					[
						t.identifier('iteratorState'),
						t.identifier('iteratorSource'),
					],
				)],
				branch: t.binaryExpression(
					'===',
					t.identifier('value'),
					t.identifier('undefined'),
				),
				consequentAddresses: [2, 7],
				kind: 'normal',
			}],
			[2, {
				address: 2,
				body: [],
				branch: t.identifier('chooseLeft'),
				consequentAddresses: [3, 4],
				kind: 'normal',
			}],
			[3, {
				address: 3,
				body: [t.expressionStatement(t.identifier('leftBody'))],
				consequentAddresses: [5],
				kind: 'normal',
			}],
			[4, {
				address: 4,
				body: [t.expressionStatement(t.identifier('rightBody'))],
				consequentAddresses: [6],
				kind: 'normal',
			}],
			[5, {
				address: 5,
				body: [t.expressionStatement(t.identifier('leftLatch'))],
				consequentAddresses: [1],
				kind: 'normal',
			}],
			[6, {
				address: 6,
				body: [t.expressionStatement(t.identifier('rightLatch'))],
				consequentAddresses: [1],
				kind: 'normal',
			}],
			[7, {
				address: 7,
				body: [t.returnStatement()],
				consequentAddresses: [],
				kind: 'normal',
			}],
			[8, {
				address: 8,
				body: [
					t.variableDeclaration('const', [t.variableDeclarator(
						t.identifier('caught'),
						t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
					)]),
					t.expressionStatement(t.callExpression(
						t.v8IntrinsicIdentifier('IteratorClose'),
						[t.identifier('iteratorState'), t.booleanLiteral(true)],
					)),
					t.throwStatement(t.identifier('caught')),
				],
				consequentAddresses: [],
				kind: 'normal',
			}],
		]);
		const func = fakeFunction(blocks, [{
			handler: 8,
			protectedBlocks: [2, 3, 4, 5, 6],
		}]);
		const descriptor = {
			handler: 8,
			kind: 'finally' as const,
			protectedBlocks: new AddressSet([2, 3, 4, 5, 6]),
			protectedEntries: new AddressSet([2]),
			catchBody: null,
			canonicalFinallyAddress: 8,
			canonicalFinallyOwnership: null,
			finallyCopyRoots: new AddressSet<number>(),
			finallyBodyBlocks: [8],
			boundedFinallyBodyBlocks: [8],
			finallyCopies: [],
			finallyCopySuffixes: [],
			enclosingFinallyCopyRoots: [],
		};
		const exceptionModel = func.exceptions as unknown as {
			structuredRegionDescriptors: () => unknown[];
			structuredRegionForest: () => unknown;
		};
		exceptionModel.structuredRegionDescriptors = () => [descriptor];
		exceptionModel.structuredRegionForest = () => ({
			roots: [{ descriptor, children: [] }],
			nodeByHandler: new Map([[8, { descriptor, children: [] }]]),
			parentByHandler: new Map(),
		});

		const summary = summarizeRecursiveCFG(1, structureCFG(func));
		assert.deepEqual(summary.misses, [], summary.regionText);
		assert.deepEqual(summary.loopCoverageIssues, [], summary.regionText);
		assert.match(summary.regionText ?? '', /syntax=forOf/);
		assert.match(summary.regionText ?? '', /tryFinally handler=0x8/);
		assert.match(summary.emittedCode ?? '', /if \(chooseLeft\)/);
		assert.match(summary.emittedCode ?? '', /leftLatch/);
		assert.match(summary.emittedCode ?? '', /rightLatch/);
		assert.doesNotMatch(
			summary.emittedCode ?? '',
			/IteratorBegin|IteratorNext|IteratorClose/,
		);
	},
);

Deno.test('nested iterator guards retain a switch and abrupt case exits', () => {
	const intrinsicTuple = (
		names: string[],
		intrinsic: string,
		args: t.Expression[],
	) => t.variableDeclaration('const', [t.variableDeclarator(
		t.arrayPattern(names.map((name) => t.identifier(name))),
		t.callExpression(t.v8IntrinsicIdentifier(intrinsic), args),
	)]);
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [intrinsicTuple(
				['r2_0', 'r9_0'],
				'IteratorBegin',
				[t.identifier('items')],
			)],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [intrinsicTuple(
				['r17_0', 'r9_1'],
				'IteratorNext',
				[t.identifier('r2_0'), t.identifier('r9_0')],
			)],
			branch: t.binaryExpression(
				'===',
				t.identifier('r17_0'),
				t.identifier('undefined'),
			),
			consequentAddresses: [2, 9],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [intrinsicTuple(
				['r21_0', 'r19_0', 'r18_0'],
				'GetPNameList',
				[t.identifier('r17_0')],
			)],
			branch: t.binaryExpression(
				'===',
				t.identifier('r21_0'),
				t.identifier('undefined'),
			),
			consequentAddresses: [3, 8],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [intrinsicTuple(
				['r17_1', 'r19_1'],
				'GetNextPName',
				[
					t.identifier('r21_0'),
					t.identifier('r17_0'),
					t.identifier('r19_0'),
				],
			)],
			branch: t.binaryExpression(
				'===',
				t.identifier('r17_1'),
				t.identifier('undefined'),
			),
			consequentAddresses: [4, 8],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('UIntSwitchImm'),
				[
					t.identifier('r17_1'),
					t.numericLiteral(0),
					t.numericLiteral(1),
				],
			))],
			consequentAddresses: [3, 6, 7],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visitFirst'),
				[t.identifier('r17_1')],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visitSecond'),
				[t.identifier('r17_1')],
			))],
			branch: t.identifier('invalid'),
			consequentAddresses: [3, 10],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.expressionStatement(t.identifier('finishItem'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [t.returnStatement(t.identifier('result'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.returnStatement(t.arrayExpression([]))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.equal((summary.regionText?.match(/loop id=/g) ?? []).length, 2);
	assert.match(summary.regionText ?? '', /syntax=forOf/);
	assert.match(summary.regionText ?? '', /syntax=forIn/);
	assert.match(summary.regionText ?? '', /body\s+switch cases=2/);
	assert.match(summary.emittedCode ?? '', /for \(const r17_0 of items\)/);
	assert.match(summary.emittedCode ?? '', /for \(const r17_1 in r17_0\)/);
	assert.match(summary.emittedCode ?? '', /switch \(r17_1\)/);
	assert.match(summary.emittedCode ?? '', /if \(invalid\) \{\s*return \[\];/);
	assert.doesNotMatch(
		summary.emittedCode ?? '',
		/GetPNameList|GetNextPName|IteratorBegin|IteratorNext|unsupported fallback/,
	);
});

Deno.test('optional parent loops retain nested child loops', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outerGuard'),
			consequentAddresses: [1, 7],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('enterOuter'),
			consequentAddresses: [2, 6],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('outerBody'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('innerBody'))],
			branch: t.identifier('keepInner'),
			consequentAddresses: [4, 3],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('outerLatch'))],
			branch: t.identifier('keepOuter'),
			consequentAddresses: [6, 2],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.expressionStatement(t.identifier('afterOuter'))],
			consequentAddresses: [7],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.equal((summary.regionText?.match(/loop id=/g) ?? []).length, 2);
	assert.match(summary.emittedCode ?? '', /outerBody/);
	assert.match(summary.emittedCode ?? '', /innerBody/);
	assert.match(summary.emittedCode ?? '', /afterOuter/);
});

Deno.test('loop body guards retain optional child self-loops', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.identifier('outerHeader'))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('enterInner'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('innerBody'))],
			branch: t.identifier('keepInner'),
			consequentAddresses: [3, 2],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('outerLatch'))],
			branch: t.identifier('keepOuter'),
			consequentAddresses: [4, 0],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.deepEqual(summary.loopCoverageIssues, [], summary.regionText);
	assert.equal((summary.regionText?.match(/loop id=/g) ?? []).length, 2);
	assert.equal(
		(summary.emittedCode?.match(/innerBody;/g) ?? []).length,
		1,
	);
});

Deno.test('switch joins retain a following optional loop', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('UIntSwitchImm'),
				[t.identifier('tag'), t.numericLiteral(0), t.numericLiteral(2)],
			))],
			consequentAddresses: [4, 1, 2, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('sharedCase'),
				[],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('otherCase'),
				[],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('defaultCase'),
				[],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			branch: t.identifier('enterLoop'),
			consequentAddresses: [5, 7],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('loopBody'),
				[],
			))],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [7, 5],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /switch .* join=0x3/);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(
		summary.emittedCode ?? '',
		/case 0:\s*case 2:\s*(?:\{\s*)?sharedCase\(\);\s*break;/,
	);
	assert.match(
		summary.emittedCode ?? '',
		/case 1:\s*(?:\{\s*)?otherCase\(\);\s*break;/,
	);
	assert.equal(
		(summary.emittedCode?.match(/sharedCase\(\)/g) ?? []).length,
		1,
	);
});

Deno.test('switch joins do not claim incompletely structured cases', () => {
	const terminal = 121;
	const join = 200;
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('UIntSwitchImm'),
				[t.identifier('tag'), t.numericLiteral(0), t.numericLiteral(1)],
			))],
			consequentAddresses: [131, 1, 130],
			kind: 'normal',
		}],
		[130, {
			address: 130,
			body: [t.expressionStatement(t.identifier('otherCase'))],
			consequentAddresses: [join],
			kind: 'normal',
		}],
		[131, {
			address: 131,
			body: [t.expressionStatement(t.identifier('defaultCase'))],
			consequentAddresses: [join],
			kind: 'normal',
		}],
		[join, {
			address: join,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	for (let address = 1; address < terminal - 1; address++) {
		blocks.set(address, {
			address,
			body: [],
			branch: t.identifier(`branch${address}`),
			consequentAddresses: [address + 1, address + 2],
			kind: 'normal',
		});
	}
	for (const address of [terminal - 1, terminal]) {
		blocks.set(address, {
			address,
			body: [t.expressionStatement(t.identifier(`terminal${address}`))],
			consequentAddresses: [join],
			kind: 'normal',
		});
	}

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.match(summary.regionText ?? '', /switch /);
	// The join may be retained only because the wide case is now completely
	// structured; an incompletely structured case must never hide behind it.
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.unstructuredBranches, [], summary.regionText);
});

Deno.test('switch loop headers retain every case body', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('enterLoop'),
			consequentAddresses: [1, 7],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('UIntSwitchImm'),
				[t.identifier('tag'), t.numericLiteral(0), t.numericLiteral(1)],
			))],
			consequentAddresses: [4, 2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('firstCase'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('secondCase'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('defaultCase'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [7, 1],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.regionText ?? '', /body\s+switch .* join=0x6/);
	assert.match(summary.emittedCode ?? '', /switch \(tag\)/);
	assert.match(summary.emittedCode ?? '', /firstCase/);
	assert.match(summary.emittedCode ?? '', /secondCase/);
	assert.match(summary.emittedCode ?? '', /defaultCase/);
	assert.doesNotMatch(summary.emittedCode ?? '', /%UIntSwitchImm/);
});

Deno.test('switch loop headers leave shared latch outside cases', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('UIntSwitchImm'),
				[t.identifier('tag'), t.numericLiteral(0), t.numericLiteral(1)],
			))],
			consequentAddresses: [4, 2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('firstCase'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('secondCase'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.assignmentExpression(
				'=',
				t.identifier('cursor'),
				t.identifier('nextCursor'),
			))],
			branch: t.identifier('done'),
			consequentAddresses: [5, 1],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /body\s+switch .* join=0x4/);
	assert.doesNotMatch(summary.regionText ?? '', /fallback/);
	assert.match(summary.emittedCode ?? '', /cursor = nextCursor/);
	assert.match(summary.emittedCode ?? '', /if \(done\)/);
});

Deno.test('wide string switches retain shared case targets', () => {
	const labels = [
		'to top',
		'to right',
		'to bottom',
		'to left',
		'to top right',
		'to right top',
		'to bottom right',
		'to right bottom',
	];
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.callExpression(
				t.v8IntrinsicIdentifier('StringSwitchImm'),
				[
					t.identifier('direction'),
					t.arrayExpression(
						labels.map((label) => t.stringLiteral(label)),
					),
				],
			))],
			consequentAddresses: [9, 1, 2, 3, 4, 5, 5, 6, 6],
			kind: 'normal',
		}],
		...[1, 2, 3, 4, 5, 6, 9].map((address): [number, IRBlock] => [
			address,
			{
				address,
				body: [t.expressionStatement(t.identifier(`body${address}`))],
				consequentAddresses: [10],
				kind: 'normal',
			},
		]),
		[10, {
			address: 10,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.emittedCode ?? '', /switch \(direction\)/);
	assert.match(
		summary.emittedCode ?? '',
		/case "to top right":\s*case "to right top":\s*(?:\{\s*)?body5;/,
	);
	assert.match(
		summary.emittedCode ?? '',
		/case "to bottom right":\s*case "to right bottom":\s*(?:\{\s*)?body6;/,
	);
	assert.doesNotMatch(summary.emittedCode ?? '', /%StringSwitchImm/);
});

Deno.test('switch emission uses its explicit dispatch header', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [10],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [
				t.expressionStatement(t.identifier('dispatchPrelude')),
				t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('UIntSwitchImm'),
					[
						t.identifier('tag'),
						t.numericLiteral(0),
						t.numericLiteral(1),
					],
				)),
			],
			consequentAddresses: [3, 1, 2],
			kind: 'normal',
		}],
		...[1, 2, 3].map((address): [number, IRBlock] => [
			address,
			{
				address,
				body: [t.returnStatement(t.numericLiteral(address))],
				consequentAddresses: [],
				kind: 'normal',
			},
		]),
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /switch .* header=0xa/);
	assert.match(summary.emittedCode ?? '', /dispatchPrelude;/);
	assert.match(summary.emittedCode ?? '', /switch \(tag\)/);
	assert.doesNotMatch(summary.emittedCode ?? '', /%UIntSwitchImm/);
});

Deno.test('dynamic equality guards are not recovered as eager switches', () => {
	const guarded = t.memberExpression(
		t.identifier('value'),
		t.identifier('guarded'),
	);
	const fallback = t.memberExpression(
		t.identifier('value'),
		t.identifier('fallback'),
	);
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.identifier('value'),
				t.nullLiteral(),
			),
			consequentAddresses: [1, 6],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.binaryExpression(
				'===',
				guarded,
				t.nullLiteral(),
			),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.unaryExpression('typeof', t.cloneNode(guarded)),
				t.stringLiteral('number'),
			),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.unaryExpression('typeof', t.cloneNode(fallback)),
				t.stringLiteral('number'),
			),
			consequentAddresses: [5, 7],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement(t.cloneNode(guarded))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.nullLiteral())],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement(t.nullLiteral())],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.returnStatement(t.cloneNode(fallback))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.doesNotMatch(summary.regionText ?? '', /switch /);
	assert.doesNotMatch(summary.emittedCode ?? '', /switch \(/);
	assert.match(
		summary.emittedCode ?? '',
		/value\.guarded !== null && typeof value\.guarded/,
	);
});

Deno.test('literal equality chains remain recovered switches', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.stringLiteral('fulfilled'),
				t.identifier('status'),
			),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.stringLiteral('rejected'),
				t.identifier('status'),
			),
			consequentAddresses: [2, 5],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.returnStatement(t.stringLiteral('pending'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement(t.stringLiteral('yes'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.stringLiteral('no'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /switch cases=2/);
	assert.match(summary.emittedCode ?? '', /switch \(status\)/);
});

Deno.test('compare chains folded into guards do not require switch emission', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.binaryExpression(
				'==',
				t.nullLiteral(),
				t.identifier('value'),
			),
			consequentAddresses: [4, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('objectLiteral'),
					t.stringLiteral('object'),
				),
			])],
			branch: t.binaryExpression(
				'===',
				t.identifier('objectLiteral'),
				t.identifier('kind'),
			),
			consequentAddresses: [4, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('functionLiteral'),
					t.stringLiteral('function'),
				),
			])],
			branch: t.unaryExpression(
				'!',
				t.binaryExpression(
					'===',
					t.identifier('functionLiteral'),
					t.identifier('kind'),
				),
			),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.throwStatement(t.identifier('typeError'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement(t.identifier('ok'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const result = structureCFG(fakeFunction(blocks));
	const descriptor = {
		dispatchBlock: 1,
		discriminant: t.identifier('kind'),
		cases: [
			{ test: t.stringLiteral('object'), target: 4, source: 1 },
			{ test: t.stringLiteral('function'), target: 4, source: 2 },
		],
		defaultTarget: 3,
		defaultSource: 2,
		coveredBlocks: new AddressSet([1, 2]),
		kind: 'compareChain' as const,
	};
	result.descriptors.switches.switches.push(descriptor);
	result.descriptors.switches.switchByDispatch.set(1, descriptor);
	const summary = summarizeRecursiveCFG(1, result);
	assert.equal(summary.switchCount, 1);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.doesNotMatch(summary.emittedCode ?? '', /%Switch/);
	assert.match(summary.emittedCode ?? '', /throw typeError/);
});

Deno.test('dispatch-only switch aliases retain exact forest routing', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('firstMatch'),
			consequentAddresses: [3, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('secondMatch'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('caseWork'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('defaultWork'))],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.stringLiteral('case'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement(t.stringLiteral('default'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const structured = structureCFG(fakeFunction(blocks));
	const empty = (): Region => ({
		kind: 'sequence',
		regions: [],
		sourceBlocks: new AddressSet(),
	});
	const recoveredSwitch: Region = {
		kind: 'switch',
		header: 1,
		discriminant: t.identifier('kind'),
		cases: [{
			test: t.stringLiteral('first'),
			aliases: [t.stringLiteral('second')],
			target: 3,
			source: 1,
			body: empty(),
		}],
		defaultTarget: 4,
		defaultSource: 2,
		defaultBody: empty(),
		sourceBlocks: new AddressSet([1, 2]),
	};
	const exact = tryStructureBoundedContinuationForest(
		structured.cfg,
		structured.analyses,
		() => null,
		undefined,
		{
			dispatches: new AddressSet([1]),
			switchAt: () => recoveredSwitch,
		},
	);
	assert.ok(exact);
	assert.deepEqual(
		[...regionCoveredBlocks(exact)].toSorted((left, right) => left - right),
		[0, 1, 2, 3, 4, 5, 6],
	);
	assert.equal((printRegion(exact).match(/switch cases=1/g) ?? []).length, 1);
});

Deno.test('terminal arms share one switch continuation', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('choosePath'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('failEarly'),
			consequentAddresses: [4, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('alternatePrelude'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.throwStatement(t.identifier('earlyError'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.stringLiteral('fulfilled'),
				t.identifier('status'),
			),
			consequentAddresses: [5, 7],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.stringLiteral('rejected'),
				t.identifier('status'),
			),
			consequentAddresses: [6, 8],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement(t.stringLiteral('pending'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [t.returnStatement(t.stringLiteral('yes'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.returnStatement(t.stringLiteral('no'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /if join=0x4/);
	assert.equal(
		(summary.regionText?.match(/switch cases=2/g) ?? []).length,
		1,
	);
	assert.equal(
		(summary.emittedCode?.match(/switch \(status\)/g) ?? []).length,
		1,
	);
	assert.match(summary.emittedCode ?? '', /throw earlyError/);
});

Deno.test('shared acyclic branch DAGs retain one copy of each join block', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [t.expressionStatement(t.identifier('prepareOuter'))],
			branch: t.identifier('outer'),
			consequentAddresses: [1, 3],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('prepareLeft'))],
			branch: t.identifier('left'),
			consequentAddresses: [2, 4],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('prepareMiddle'))],
			branch: t.identifier('middle'),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('prepareShared'))],
			branch: t.identifier('skipShared'),
			consequentAddresses: [4, 5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('sharedWork'))],
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

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /label=cfg_dag_0_/);
	assert.equal(
		(summary.emittedCode?.match(/sharedWork/g) ?? []).length,
		1,
	);
});

Deno.test('guarded terminal switches retain a shared continuation once', () => {
	const firstCase = t.identifier('r1_1');
	const discriminant = t.identifier('r10_1');
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outer'),
			consequentAddresses: [1, 10],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('useTerminalSwitch'),
			consequentAddresses: [10, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.cloneNode(discriminant),
					t.memberExpression(
						t.identifier('subject'),
						t.identifier('kind'),
					),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.cloneNode(firstCase),
					t.stringLiteral('first'),
				)]),
			],
			branch: t.binaryExpression(
				'===',
				t.cloneNode(firstCase),
				t.cloneNode(discriminant),
			),
			consequentAddresses: [3, 4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('r1_2'),
				t.stringLiteral('second'),
			)])],
			branch: t.binaryExpression(
				'===',
				t.identifier('r1_2'),
				t.cloneNode(discriminant),
			),
			consequentAddresses: [6, 5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.returnStatement(t.callExpression(
				t.identifier('consume'),
				[t.cloneNode(firstCase)],
			))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.stringLiteral('second'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.returnStatement(t.stringLiteral('default'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.expressionStatement(t.identifier('sharedContinuation'))],
			consequentAddresses: [11],
			kind: 'normal',
		}],
		[11, {
			address: 11,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.emittedCode ?? '', /switch \(r10_1\)/);
	assert.equal(
		(summary.emittedCode?.match(/subject\.kind/g) ?? []).length,
		1,
	);
	assert.match(summary.emittedCode ?? '', /const r1_1 = "first"/);
	assert.match(summary.emittedCode ?? '', /consume\(r1_1\)/);
	assert.equal(
		(summary.emittedCode?.match(/sharedContinuation/g) ?? []).length,
		1,
	);
});

Deno.test('mixed abrupt loops retain a terminal switch suffix', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('hasNext'),
			consequentAddresses: [10, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('visitItem'))],
			branch: t.identifier('validItem'),
			consequentAddresses: [5, 0],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.throwStatement(t.identifier('badItem'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.numericLiteral(1),
				t.identifier('kind'),
			),
			consequentAddresses: [11, 20],
			kind: 'normal',
		}],
		[11, {
			address: 11,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.numericLiteral(2),
				t.identifier('kind'),
			),
			consequentAddresses: [30, 40],
			kind: 'normal',
		}],
		[20, {
			address: 20,
			body: [t.expressionStatement(t.identifier('caseOne'))],
			consequentAddresses: [40],
			kind: 'normal',
		}],
		[30, {
			address: 30,
			body: [t.throwStatement(t.identifier('badKind'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[40, {
			address: 40,
			body: [t.returnStatement(t.identifier('result'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=.*continuation=0xa/);
	assert.match(summary.regionText ?? '', /switch cases=2.*join=0x28/);
	assert.match(summary.emittedCode ?? '', /throw badItem/);
	assert.match(summary.emittedCode ?? '', /switch \(kind\)/);
	assert.equal(
		(summary.emittedCode?.match(/return result/g) ?? []).length,
		1,
	);
});

Deno.test('loop-local branch paths retain nested switches', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('hasWork'),
			consequentAddresses: [50, 1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('useSwitch'),
			consequentAddresses: [3, 2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.numericLiteral(1),
				t.identifier('kind'),
			),
			consequentAddresses: [4, 10],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('directArm'))],
			consequentAddresses: [40],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [],
			branch: t.binaryExpression(
				'===',
				t.numericLiteral(2),
				t.identifier('kind'),
			),
			consequentAddresses: [30, 20],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.expressionStatement(t.identifier('case_10'))],
			consequentAddresses: [40],
			kind: 'normal',
		}],
		[20, {
			address: 20,
			body: [t.expressionStatement(t.identifier('case_20'))],
			consequentAddresses: [40],
			kind: 'normal',
		}],
		[30, {
			address: 30,
			body: [t.expressionStatement(t.identifier('case_30'))],
			consequentAddresses: [40],
			kind: 'normal',
		}],
		[40, {
			address: 40,
			body: [t.expressionStatement(t.identifier('latch'))],
			consequentAddresses: [0],
			kind: 'normal',
		}],
		[50, {
			address: 50,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.regionText ?? '', /switch cases=2.*join=0x28/);
	assert.match(summary.emittedCode ?? '', /switch \(kind\)/);
});

Deno.test('loop headers retain internal diamond branches', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('enterLoop'),
			consequentAddresses: [1, 5],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('chooseArm'),
			consequentAddresses: [2, 3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('leftArm'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('rightArm'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('latchBody'),
				[],
			))],
			branch: t.identifier('keepGoing'),
			consequentAddresses: [5, 1],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /loop id=/);
	assert.match(summary.emittedCode ?? '', /leftArm/);
	assert.match(summary.emittedCode ?? '', /rightArm/);
	assert.match(summary.emittedCode ?? '', /latchBody\(\)/);
});

Deno.test('script completion is not emitted as a terminal reference', () => {
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
			body: [t.expressionStatement(t.identifier('sideEffect'))],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.returnStatement(t.identifier('completion'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks);
	func.id = 0;

	const summary = summarizeRecursiveCFG(0, structureCFG(func));
	assert.doesNotMatch(summary.regionText ?? '', /terminalReference/);
});

Deno.test('a loop returning from its body keeps its ordinary continuation', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('more'),
			consequentAddresses: [2, 4],
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
			body: [t.returnStatement(t.booleanLiteral(true))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('after'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.booleanLiteral(false))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const result = structureCFG(fakeFunction(blocks));
	const summary = summarizeRecursiveCFG(0, result);
	assert.deepEqual(summary.misses, [], summary.regionText);
	// `break` leaves a loop at one place. Lowering the body's exit to the
	// terminal block as a second break would emit that block after the loop,
	// where exhaustion runs it too — returning `true` on every completion.
	assert.match(
		summary.regionText ?? '',
		/exits=break:0x1->0x4,return:0x2->0x3/,
	);
});

Deno.test('an unlabelled ordered loop exit is named by its enclosing scope', () => {
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 2,
		latches: [3],
		loopBlocks: new AddressSet([2, 3]),
		continuation: 5,
		exits: [
			{ from: 2, to: 5, kind: 'break' },
			{ from: 3, to: 6, kind: 'break', sequenceExit: { target: 6 } },
		],
		children: [],
		body: {
			kind: 'break',
			target: 6,
			exit: {
				from: 3,
				to: 6,
				kind: 'break',
				sequenceExit: { target: 6 },
			},
			sourceBlocks: new AddressSet([3]),
		},
		sourceBlocks: new AddressSet([2, 3]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [loop, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([5]),
		}, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([6]),
		}],
		sourceBlocks: new AddressSet([2, 3, 5, 6]),
	};

	const labelled = labelPendingLoopSequenceExits(region);
	assert.equal(labelled.kind, 'sequence');
	const [scoped, tail] = (labelled as Extract<Region, { kind: 'sequence' }>)
		.regions;
	// The loop and the block it skips share a labelled scope, so the exit can
	// leave both instead of falling into 0x5 alongside the ordinary completion.
	assert.equal(
		(scoped as Extract<Region, { kind: 'sequence' }>).exitLabel,
		'cfg_exit_6',
	);
	assert.deepEqual([...tail!.sourceBlocks], [6]);
	const scopedLoop = (scoped as Extract<Region, { kind: 'sequence' }>)
		.regions[0] as Extract<Region, { kind: 'loop' }>;
	assert.equal(scopedLoop.exits[1]!.sequenceExit?.label, 'cfg_exit_6');
	assert.equal(
		(scopedLoop.body as Extract<Region, { kind: 'labelBreak' }>).label,
		'cfg_exit_6',
	);
});

Deno.test('multiple ordered loop exits receive nested lexical labels', () => {
	const exits = [
		{ from: 3, to: 6, kind: 'break' as const, sequenceExit: { target: 6 } },
		{ from: 4, to: 7, kind: 'break' as const, sequenceExit: { target: 7 } },
	];
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 2,
		latches: [4],
		loopBlocks: new AddressSet([2, 3, 4]),
		continuation: 5,
		exits: [{ from: 2, to: 5, kind: 'break' }, ...exits],
		children: [],
		body: {
			kind: 'if',
			header: 2,
			test: t.identifier('leaveLater'),
			consequent: {
				kind: 'break',
				target: 6,
				exit: exits[0],
				sourceBlocks: new AddressSet([3]),
			},
			alternate: {
				kind: 'break',
				target: 7,
				exit: exits[1],
				sourceBlocks: new AddressSet([4]),
			},
			sourceBlocks: new AddressSet([2, 3, 4]),
		},
		sourceBlocks: new AddressSet([2, 3, 4]),
	};
	const tail = (address: number): Region => ({
		kind: 'basic',
		body: [],
		sourceBlocks: new AddressSet([address]),
	});
	const labelled = labelPendingLoopSequenceExits({
		kind: 'sequence',
		regions: [loop, tail(5), tail(6), tail(7)],
		sourceBlocks: new AddressSet([2, 3, 4, 5, 6, 7]),
	});
	const text = printRegion(labelled);
	assert.match(text, /sequence label=cfg_exit_6/);
	assert.match(text, /sequence label=cfg_exit_7/);
	assert.match(text, /labelBreak label=cfg_exit_6 target=0x6/);
	assert.match(text, /labelBreak label=cfg_exit_7 target=0x7/);
});

Deno.test('continuation forests route nonempty switch arms independently', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('kind'),
			consequentAddresses: [1, 2],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('caseA'))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.identifier('caseB'))],
			consequentAddresses: [4],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.expressionStatement(t.identifier('tailA'))],
			consequentAddresses: [5],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.identifier('tailB'))],
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
	const result = structureCFG(fakeFunction(blocks));
	const switchRegion: Region = {
		kind: 'switch',
		header: 0,
		discriminant: t.identifier('kind'),
		cases: [{
			test: t.numericLiteral(1),
			target: 1,
			source: 0,
			body: {
				kind: 'basic',
				body: [t.expressionStatement(t.identifier('caseA'))],
				sourceBlocks: new AddressSet([1]),
			},
		}],
		defaultTarget: 2,
		defaultSource: 0,
		defaultBody: {
			kind: 'basic',
			body: [t.expressionStatement(t.identifier('caseB'))],
			sourceBlocks: new AddressSet([2]),
		},
		sourceBlocks: new AddressSet([0, 1, 2]),
	};
	const forest = tryStructureBoundedContinuationForest(
		result.cfg,
		result.analyses,
		() => null,
		undefined,
		{
			dispatches: new AddressSet([0]),
			switchAt: () => switchRegion,
		},
	);

	assert.ok(forest);
	assert.deepEqual(
		[...forest.sourceBlocks].toSorted((left, right) => left - right),
		[0, 1, 2, 3, 4, 5],
	);
	const text = printRegion(forest);
	assert.match(text, /case 0x1 basic/);
	assert.match(text, /default 0x2 sequence/);
	assert.match(text, /labelBreak label=cfg_cont_/);
});

Deno.test('ordered loop exit labels propagate through protected regions', () => {
	const exit = {
		from: 3,
		to: 6,
		kind: 'break' as const,
		sequenceExit: { target: 6 },
	};
	const loop: Region = {
		kind: 'loop',
		id: 0,
		header: 2,
		latches: [3],
		loopBlocks: new AddressSet([2, 3]),
		continuation: 5,
		exits: [{ from: 2, to: 5, kind: 'break' }, exit],
		children: [],
		body: {
			kind: 'break',
			target: 6,
			exit,
			sourceBlocks: new AddressSet([3]),
		},
		sourceBlocks: new AddressSet([2, 3]),
	};
	const protectedLoop: Region = {
		kind: 'tryCatch',
		body: loop,
		handler: {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([4]),
		},
		handlerAddress: 4,
		protectedBlocks: new AddressSet([2, 3]),
		sourceBlocks: new AddressSet([2, 3, 4]),
	};
	const region: Region = {
		kind: 'sequence',
		regions: [protectedLoop, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([5]),
		}, {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([6]),
		}],
		sourceBlocks: new AddressSet([2, 3, 4, 5, 6]),
	};

	const labelled = labelPendingLoopSequenceExits(region);
	assert.equal(labelled.kind, 'sequence');
	const scoped = (labelled as Extract<Region, { kind: 'sequence' }>)
		.regions[0] as Extract<Region, { kind: 'sequence' }>;
	assert.equal(scoped.exitLabel, 'cfg_exit_6');
	const nestedTry = scoped.regions[0] as Extract<
		Region,
		{ kind: 'tryCatch' }
	>;
	const nestedLoop = nestedTry.body as Extract<Region, { kind: 'loop' }>;
	assert.equal(nestedLoop.exits[1]!.sequenceExit?.label, 'cfg_exit_6');
	assert.equal(
		(nestedLoop.body as Extract<Region, { kind: 'labelBreak' }>).label,
		'cfg_exit_6',
	);
});

Deno.test('a contracted catch range stops at its continuation', () => {
	const catchBinding = (name: string) =>
		t.variableDeclaration('const', [t.variableDeclarator(
			t.identifier(name),
			t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
		)]);
	const assign = (target: string, value: t.Expression) =>
		t.expressionStatement(
			t.assignmentExpression('=', t.identifier(target), value),
		);
	const blocks = new Map<number, IRBlock>();
	// Two `try { probe(); try { probe2() } catch {} isX() } catch {}` groups in
	// a row, as a type-probe helper compiles to. Both handlers and the group's
	// non-throwing tail join at the group's continuation, which is the entry of
	// the next group.
	const probeGroup = (base: number, target: string, join: number) => {
		blocks.set(base, {
			address: base,
			body: [t.expressionStatement(t.callExpression(
				t.identifier(`probeOuter${base}`),
				[],
			))],
			consequentAddresses: [base + 1],
			kind: 'normal',
		} as IRBlock);
		blocks.set(base + 1, {
			address: base + 1,
			body: [t.expressionStatement(t.callExpression(
				t.identifier(`probeInner${base}`),
				[],
			))],
			consequentAddresses: [base + 2],
			kind: 'normal',
		} as IRBlock);
		blocks.set(base + 2, {
			address: base + 2,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier(`probed${base}`),
				t.binaryExpression(
					'instanceof',
					t.identifier('value'),
					t.identifier('Map'),
				),
			)])],
			consequentAddresses: [base + 3],
			kind: 'normal',
		} as IRBlock);
		// The non-throwing tail of the `try`: outside every protected range, so
		// the join is not a successor of any protected block.
		blocks.set(base + 3, {
			address: base + 3,
			body: [assign(target, t.identifier(`probed${base}`))],
			consequentAddresses: [join],
			kind: 'normal',
		} as IRBlock);
		blocks.set(base + 4, {
			address: base + 4,
			body: [
				catchBinding(`inner${base}`),
				assign(target, t.booleanLiteral(true)),
			],
			consequentAddresses: [join],
			kind: 'normal',
		} as IRBlock);
		blocks.set(base + 5, {
			address: base + 5,
			body: [
				catchBinding(`outer${base}`),
				assign(target, t.booleanLiteral(false)),
			],
			consequentAddresses: [join],
			kind: 'normal',
		} as IRBlock);
		const innerDescriptor = {
			handler: base + 4,
			kind: 'catch' as const,
			protectedBlocks: new AddressSet([base + 1]),
			protectedEntries: new AddressSet([base + 1]),
			catchBody: null,
			canonicalFinallyAddress: null,
			canonicalFinallyOwnership: null,
			finallyCopyRoots: new AddressSet<number>(),
			finallyBodyBlocks: null,
			boundedFinallyBodyBlocks: null,
			finallyCopies: [],
			finallyCopySuffixes: [],
			enclosingFinallyCopyRoots: [],
		};
		// Hermes splits the outer range around the nested handler, so that
		// handler block is one of the outer range's entries even though only an
		// exceptional edge reaches it.
		const outerDescriptor = {
			...innerDescriptor,
			handler: base + 5,
			protectedBlocks: new AddressSet([
				base,
				base + 1,
				base + 2,
				base + 4,
			]),
			protectedEntries: new AddressSet([base, base + 4]),
		};
		return { innerDescriptor, outerDescriptor };
	};
	blocks.set(0, {
		address: 0,
		body: [assign('foundMap', t.booleanLiteral(false))],
		consequentAddresses: [1],
		kind: 'normal',
	} as IRBlock);
	const first = probeGroup(1, 'foundMap', 10);
	blocks.set(10, {
		address: 10,
		body: [assign('foundSet', t.booleanLiteral(false))],
		consequentAddresses: [11],
		kind: 'normal',
	} as IRBlock);
	const second = probeGroup(11, 'foundSet', 20);
	blocks.set(20, {
		address: 20,
		body: [t.returnStatement(t.logicalExpression(
			'||',
			t.identifier('foundMap'),
			t.identifier('foundSet'),
		))],
		consequentAddresses: [],
		kind: 'normal',
	} as IRBlock);

	const descriptors = [
		first.outerDescriptor,
		first.innerDescriptor,
		second.outerDescriptor,
		second.innerDescriptor,
	];
	const func = fakeFunction(
		blocks,
		descriptors.map((descriptor) => ({
			handler: descriptor.handler,
			protectedBlocks: [...descriptor.protectedBlocks],
		})),
	);
	const exceptionModel = func.exceptions as unknown as {
		structuredRegionDescriptors: () => unknown[];
		structuredRegionForest: () => unknown;
	};
	exceptionModel.structuredRegionDescriptors = () => descriptors;
	const nodeOf = (
		outer: typeof first.outerDescriptor,
		inner: typeof first.innerDescriptor,
	) => {
		const innerNode = { descriptor: inner, children: [] };
		return {
			outerNode: { descriptor: outer, children: [innerNode] },
			innerNode,
		};
	};
	const firstNodes = nodeOf(first.outerDescriptor, first.innerDescriptor);
	const secondNodes = nodeOf(second.outerDescriptor, second.innerDescriptor);
	exceptionModel.structuredRegionForest = () => ({
		roots: [firstNodes.outerNode, secondNodes.outerNode],
		nodeByHandler: new Map([
			[first.outerDescriptor.handler, firstNodes.outerNode],
			[first.innerDescriptor.handler, firstNodes.innerNode],
			[second.outerDescriptor.handler, secondNodes.outerNode],
			[second.innerDescriptor.handler, secondNodes.innerNode],
		]),
		parentByHandler: new Map([
			[first.innerDescriptor.handler, first.outerDescriptor.handler],
			[second.innerDescriptor.handler, second.outerDescriptor.handler],
		]),
	});

	const cfg = ImmutableCFG.fromIRFunction(func);
	const recovered = recoverDescriptors(cfg, func);
	const outer = recovered.exceptions.handlers.find((descriptor) =>
		descriptor.handler === first.outerDescriptor.handler
	)!;

	// The nested handler is an entry of the enclosing range, but only an
	// exceptional edge reaches it, so a Region may not be opened there.
	assert.deepEqual(
		[...openableProtectedEntries(cfg, outer)],
		[1],
		[...outer.protectedEntries].join(','),
	);

	// A contracted node covers its own range and stops at the continuation: the
	// tail of the try joins the handlers at 0xa, and everything from there on —
	// including the second probe — belongs to the enclosing skeleton.
	const contracted = contractedExceptionBlocks(cfg, outer, recovered);
	assert.equal(contracted.has(1), true);
	assert.equal(contracted.has(first.innerDescriptor.handler), true);
	for (const outside of [10, 20, ...second.outerDescriptor.protectedBlocks]) {
		assert.equal(
			contracted.has(outside),
			false,
			`0x${outside.toString(16)} in ${
				[...contracted].map((block) => `0x${block.toString(16)}`).join(
					',',
				)
			}`,
		);
	}
});

Deno.test('a for-in whose body always returns needs no backedge', () => {
	const blocks = new Map<number, IRBlock>([
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
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.arrayPattern([
					t.identifier('key'),
					t.identifier('nextIndex'),
				]),
				t.callExpression(t.v8IntrinsicIdentifier('GetNextPName'), [
					t.identifier('propertyList'),
					t.identifier('object'),
					t.identifier('beginIndex'),
				]),
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
			body: [t.returnStatement(t.booleanLiteral(false))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement(t.booleanLiteral(true))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	// One iteration is all the graph admits, and the loop owns it: no latch.
	assert.match(summary.regionText ?? '', /syntax=forIn/);
	assert.match(summary.regionText ?? '', /latches= /);
	assert.match(
		summary.emittedCode ?? '',
		/for \(const key in object\) \{\s*return false;\s*\}\s*return true;/,
	);
	assert.doesNotMatch(
		summary.emittedCode ?? '',
		/GetPNameList|GetNextPName|propertyList/,
	);
});

Deno.test('a single-iteration for-in body leaves by break', () => {
	const blocks = new Map<number, IRBlock>([
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
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.arrayPattern([
					t.identifier('key'),
					t.identifier('nextIndex'),
				]),
				t.callExpression(t.v8IntrinsicIdentifier('GetNextPName'), [
					t.identifier('propertyList'),
					t.identifier('object'),
					t.identifier('beginIndex'),
				]),
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
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [t.returnStatement(t.identifier('result'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		1,
		structureCFG(fakeFunction(blocks)),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.match(summary.regionText ?? '', /syntax=forIn/);
	// Falling out of the body resumes after the loop, and without a backedge
	// that is exactly what `break` does.
	assert.match(
		summary.emittedCode ?? '',
		/for \(const key in object\) \{\s*visit\(key\);\s*break;\s*\}\s*return result;/,
	);
	assert.doesNotMatch(
		summary.emittedCode ?? '',
		/GetPNameList|GetNextPName|propertyList/,
	);
});

Deno.test('inlined IIFE catch copies collapse after optional for-in probes', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('outerGuard'),
			consequentAddresses: [11, 9],
			kind: 'normal',
		}],
		[11, {
			address: 11,
			body: [],
			branch: t.identifier('innerGuard'),
			consequentAddresses: [12, 9],
			kind: 'normal',
		}],
		[12, {
			address: 12,
			body: [
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
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r0_2'),
						t.booleanLiteral(false),
					),
				]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.arrayPattern([
						t.identifier('key'),
						t.identifier('nextIndex'),
					]),
					t.callExpression(t.v8IntrinsicIdentifier('GetNextPName'), [
						t.identifier('propertyList'),
						t.identifier('object'),
						t.identifier('beginIndex'),
					]),
				)]),
			],
			branch: t.binaryExpression(
				'===',
				t.identifier('key'),
				t.identifier('undefined'),
			),
			consequentAddresses: [2, 9],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('visit'),
				[t.identifier('key')],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			branch: t.identifier('skipRisky'),
			consequentAddresses: [1, 4],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('risky'),
				[t.identifier('key')],
			))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('innerError'),
				t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
			)])],
			consequentAddresses: [6],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r0_3'),
					t.booleanLiteral(true),
				),
			])],
			consequentAddresses: [9],
			kind: 'normal',
		}],
		[7, {
			address: 7,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('outerError'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r0_4'),
						t.booleanLiteral(true),
					),
				]),
			],
			consequentAddresses: [9],
			kind: 'normal',
		}],
		[9, {
			address: 9,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_5'),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.identifier('after'),
					[t.identifier('r0_5')],
				)),
			],
			consequentAddresses: [10],
			kind: 'normal',
		}],
		[10, {
			address: 10,
			body: [t.returnStatement(t.identifier('r0_5'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const func = fakeFunction(blocks, [
		{ handler: 7, protectedBlocks: [2, 3, 4, 5] },
		{ handler: 5, protectedBlocks: [4] },
	]);
	func.exceptions.equivalentCatchHandlerAliases = () =>
		new AddressMap([[5, 7]]);
	func.ssa.basicBlocks = new AddressMap([
		[9, {
			ssaInstructions: [{
				instruction: 'Phi',
				destination: { type: 'register', index: 0, version: 5 },
				sources: new AddressMap([
					[1, { type: 'register', index: 0, version: 2 }],
					[6, { type: 'register', index: 0, version: 3 }],
					[7, { type: 'register', index: 0, version: 4 }],
				]),
			}],
		}],
	]) as typeof func.ssa.basicBlocks;

	const summary = summarizeRecursiveCFG(0, structureCFG(func));
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.unhandledExceptionHandlers, []);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(summary.regionText ?? '', /syntax=forIn/);
	assert.match(summary.regionText ?? '', /tryCatch handler=0x7/);
	assert.doesNotMatch(summary.regionText ?? '', /tryCatch handler=0x5/);
	assert.match(summary.regionText ?? '', /subsumed=0x5,0x6/);
	assert.match(
		summary.regionText ?? '',
		/exits=break:0x1->0x9,break:0x6->0x9,break:0x7->0x9/,
	);
	const code = summary.emittedCode ?? '';
	assert.match(code, /let _cfg_loop_1_completed = true;/);
	assert.equal(
		(code.match(/_cfg_loop_1_completed = false;/g) ?? []).length,
		1,
	);
	assert.equal((code.match(/\bcatch\b/g) ?? []).length, 1);
	assert.doesNotMatch(code, /continue;\s*r0_5 = true;/);
	assert.match(
		code,
		/if \(_cfg_loop_1_completed\) \{\s*r0_5 = r0_2;\s*\}/,
	);
	assert.match(code, /after\(r0_5\);\s*return r0_5;/);
	assert.doesNotMatch(code, /%Phi/);
});

Deno.test('a loop owns its private terminal catch subtree', () => {
	const blocks = new Map<number, IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [],
			branch: t.identifier('runBody'),
			consequentAddresses: [2, 8],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('upload'),
				[],
			))],
			consequentAddresses: [3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [],
			branch: t.identifier('again'),
			consequentAddresses: [1, 8],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [t.variableDeclaration('const', [t.variableDeclarator(
				t.identifier('caught'),
				t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
			)])],
			branch: t.memberExpression(
				t.identifier('caught'),
				t.identifier('retryable'),
			),
			consequentAddresses: [5, 6],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.throwStatement(t.identifier('uploadError'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[6, {
			address: 6,
			body: [t.throwStatement(t.identifier('progressError'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
		[8, {
			address: 8,
			body: [t.returnStatement()],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);

	const summary = summarizeRecursiveCFG(
		0,
		structureCFG(fakeFunction(blocks, [{
			handler: 4,
			protectedBlocks: [2],
		}])),
	);
	assert.deepEqual(summary.misses, [], summary.regionText);
	assert.deepEqual(summary.uncoveredBlocks, []);
	assert.deepEqual(summary.unhandledExceptionHandlers, []);
	assert.deepEqual(summary.emitDiagnostics, [], summary.regionText);
	assert.match(
		summary.regionText ?? '',
		/tryCatch handler=0x4 protected=0x2 blocks=0x2,0x4,0x5,0x6/,
	);
	assert.match(
		summary.emittedCode ?? '',
		/catch \(_e\) \{[\s\S]*if \(caught\.retryable\)[\s\S]*throw progressError;[\s\S]*throw uploadError;/,
	);
});
