import { strict as assert } from 'node:assert';
import * as t from '@babel/types';
import { AddressGraph } from '../../../utils/graph.ts';
import { AddressSet } from '../../../utils/set.ts';
import type { IRBlock } from '../../ast/mod.ts';
import type { IRFunction } from '../mod.ts';
import { CFGAnalyses } from './algorithms/mod.ts';
import { recoverDescriptors } from './descriptors/mod.ts';
import { ImmutableCFG } from './immutableCFG.ts';
import {
	cfgFingerprint,
	normalizeCFGForRegions,
	validateNormalizedCFG,
} from './normalization.ts';

function fakeFunction(
	blocks: Map<number, IRBlock>,
	exceptionalEdges: Array<{ handler: number; protectedBlocks: number[] }> =
		[],
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
		},
	} as unknown as IRFunction;
}

function block(
	address: number,
	successors: number[],
	body: t.Statement[] = [],
): IRBlock {
	return {
		address,
		body,
		consequentAddresses: successors,
		kind: 'normal',
		sourceAddresses: new AddressSet([address, address + 100]),
	};
}

Deno.test('Region descriptors distinguish semantic destructuring from protocol', () => {
	const semantic = t.variableDeclaration('var', [
		t.variableDeclarator(
			t.objectPattern([t.objectProperty(
				t.identifier('value'),
				t.assignmentPattern(
					t.identifier('value'),
					t.numericLiteral(1),
				),
				false,
				true,
			)]),
			t.identifier('input'),
		),
	]);
	const protocol = t.variableDeclaration('const', [
		t.variableDeclarator(
			t.arrayPattern([t.identifier('iterator'), t.identifier('state')]),
			t.callExpression(t.v8IntrinsicIdentifier('IteratorBegin'), [
				t.identifier('items'),
			]),
		),
	]);
	const cfg = ImmutableCFG.fromIRFunction(fakeFunction(
		new Map([
			[0, block(0, [], [semantic, protocol, t.returnStatement()])],
		]),
	));
	const descriptors = recoverDescriptors(cfg);

	assert.equal(descriptors.destructuring.descriptors.length, 1);
	assert.equal(descriptors.destructuring.descriptors[0].kind, 'object');
	assert.equal(descriptors.destructuring.descriptors[0].entry, 0);
	assert.deepEqual(
		descriptors.destructuring.protocolCandidates.map((candidate) =>
			candidate.kind
		),
		['iterator'],
	);
});

Deno.test('Region CFG normalization prunes detached blocks idempotently', () => {
	const blocks = new Map<number, IRBlock>([
		[0, block(0, [1], [t.expressionStatement(t.identifier('entry'))])],
		[1, block(1, [], [t.returnStatement()])],
		[10, block(10, [10], [t.expressionStatement(t.identifier('dead'))])],
	]);
	blocks.get(1)!.sourceAddresses = new AddressSet();
	const input = ImmutableCFG.fromIRFunction(fakeFunction(blocks));
	const result = normalizeCFGForRegions(input, {
		enabled: true,
		validate: true,
	});

	assert.deepEqual([...result.cfg.blocks.keys()], [0, 1]);
	assert.deepEqual(result.summary.passes, [{
		name: 'prune-unreachable',
		changed: true,
		blocksBefore: 3,
		blocksAfter: 2,
		removedBlocks: [10],
	}]);
	assert.equal(result.summary.idempotent, true);
	assert.deepEqual(result.summary.invariantIssues, []);
	assert.deepEqual(
		[...result.cfg.blocks.get(1)!.sourceAddresses],
		[1],
	);

	const second = normalizeCFGForRegions(result.cfg, {
		enabled: true,
		validate: true,
	});
	assert.equal(second.summary.changed, false);
	assert.equal(cfgFingerprint(second.cfg), cfgFingerprint(result.cfg));
	assert.deepEqual(validateNormalizedCFG(second.cfg), []);
	const firstDescriptors = recoverDescriptors(
		result.cfg,
		undefined,
		new CFGAnalyses(result.cfg),
	);
	const secondDescriptors = recoverDescriptors(
		second.cfg,
		undefined,
		new CFGAnalyses(second.cfg),
	);
	assert.deepEqual(
		{
			phis: firstDescriptors.phis.phis.length,
			switches: firstDescriptors.switches.switches.length,
			handlers: firstDescriptors.exceptions.handlers.length,
			delegates: firstDescriptors.delegateYields.delegates.length,
			destructuring: firstDescriptors.destructuring.descriptors.length,
			destructuringProtocols:
				firstDescriptors.destructuring.protocolCandidates.length,
		},
		{
			phis: secondDescriptors.phis.phis.length,
			switches: secondDescriptors.switches.switches.length,
			handlers: secondDescriptors.exceptions.handlers.length,
			delegates: secondDescriptors.delegateYields.delegates.length,
			destructuring: secondDescriptors.destructuring.descriptors.length,
			destructuringProtocols:
				secondDescriptors.destructuring.protocolCandidates.length,
		},
	);
	assert.equal(result.cfg.blocks.get(0), input.blocks.get(0));
	assert.equal(
		result.cfg.blocks.get(0)?.ssaInstructions,
		input.blocks.get(0)?.ssaInstructions,
	);
});

Deno.test('Region CFG normalization retains explicit live handler flow', () => {
	const blocks = new Map<number, IRBlock>([
		[0, block(0, [1])],
		[1, block(1, [], [t.returnStatement()])],
		[5, block(5, [], [t.throwStatement(t.identifier('error'))])],
	]);
	const input = ImmutableCFG.fromIRFunction(fakeFunction(blocks, [{
		handler: 5,
		protectedBlocks: [0],
	}]));
	const result = normalizeCFGForRegions(input, {
		enabled: true,
		validate: true,
	});

	assert.deepEqual([...result.cfg.blocks.keys()], [0, 1, 5]);
	assert.equal(result.cfg.exceptionalSuccessors.get(0)?.has(5), true);
	assert.equal(result.cfg.exceptionalPredecessors.get(5)?.has(0), true);
	assert.equal(result.summary.protectedRegionPolicy, 'no-edge-rewrites');
	assert.deepEqual(result.summary.invariantIssues, []);
	const firstDescriptors = recoverDescriptors(
		result.cfg,
		undefined,
		new CFGAnalyses(result.cfg),
	);
	const second = normalizeCFGForRegions(result.cfg, {
		enabled: true,
		validate: true,
	});
	const secondDescriptors = recoverDescriptors(
		second.cfg,
		undefined,
		new CFGAnalyses(second.cfg),
	);
	const handlerShape = (
		descriptors: ReturnType<typeof recoverDescriptors>,
	) => descriptors.exceptions.handlers.map((handler) => ({
		handler: handler.handler,
		protectedBlocks: [...handler.protectedBlocks],
		protectedEntries: [...handler.protectedEntries],
	}));
	assert.deepEqual(
		handlerShape(secondDescriptors),
		handlerShape(firstDescriptors),
	);
});
