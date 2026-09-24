import { strict as assert } from 'node:assert';
import * as t from '@babel/types';
import type { IRBlock } from '../../../ast/mod.ts';
import type { IRFunction } from '../../mod.ts';
import { AddressGraph } from '../../../../utils/graph.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import { CFGAnalyses } from '../algorithms/mod.ts';
import { ImmutableCFG } from '../immutableCFG.ts';
import { recoverDelegateYieldDescriptors } from './delegateYield.ts';

const declare = (name: string, init: t.Expression) =>
	t.variableDeclaration('const', [
		t.variableDeclarator(t.identifier(name), init),
	]);
const call = (
	callee: t.Expression | t.V8IntrinsicIdentifier,
	args: t.Expression[] = [],
) => t.callExpression(callee, args);
const member = (object: string, property: string) =>
	t.memberExpression(t.identifier(object), t.identifier(property));

/**
 * A lowered `yield* makeGen()` inside `while (step.done === false)`.
 *
 * Block 1 is both the enclosing loop's header and the delegate's prelude: the
 * acquisition sits in the header's tail. Block 4 is both the delegate's
 * completion block and the enclosing loop's latch, so it ends in a branch.
 */
function delegateInsideLoop(): IRFunction {
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [declare('step0', call(t.identifier('outerNext')))],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [
				declare(
					'step',
					call(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('step0'),
						t.identifier('step1'),
					]),
				),
				t.expressionStatement(t.callExpression(
					t.identifier('observe'),
					[member('step', 'value')],
				)),
				declare('source', call(t.identifier('makeGen'))),
				declare(
					'symbolObject',
					call(t.v8IntrinsicIdentifier('TryGetById'), [
						t.identifier('global'),
						t.stringLiteral('Symbol'),
					]),
				),
				declare('symbolIterator', member('symbolObject', 'iterator')),
				declare(
					'method',
					t.memberExpression(
						t.identifier('source'),
						t.identifier('symbolIterator'),
						true,
					),
				),
				declare(
					'iterator',
					call(member('method', 'call'), [t.identifier('source')]),
				),
				t.expressionStatement(call(
					t.memberExpression(
						t.identifier('HermesInternal'),
						t.identifier('ensureObject'),
					),
					[
						t.identifier('iterator'),
						t.stringLiteral('not an object'),
					],
				)),
				declare('next', member('iterator', 'next')),
				declare('sent0', t.identifier('undefined')),
			],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[2, {
			address: 2,
			body: [
				declare(
					'sent',
					call(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('sent0'),
						t.identifier('resumed'),
					]),
				),
				declare(
					'result',
					call(member('next', 'call'), [
						t.identifier('iterator'),
						t.identifier('sent'),
					]),
				),
				t.expressionStatement(call(
					t.memberExpression(
						t.identifier('HermesInternal'),
						t.identifier('ensureObject'),
					),
					[t.identifier('result'), t.stringLiteral('not an object')],
				)),
				declare('resultDone', member('result', 'done')),
			],
			branch: t.identifier('resultDone'),
			consequentAddresses: [4, 3],
			kind: 'normal',
		}],
		[3, {
			address: 3,
			body: [
				t.expressionStatement(call(
					t.memberExpression(
						t.identifier('HermesInternal'),
						t.identifier('generatorSetDelegated'),
					),
				)),
				declare('resumed', t.yieldExpression(t.identifier('result'))),
			],
			consequentAddresses: [2],
			kind: 'normal',
		}],
		[4, {
			address: 4,
			body: [
				declare(
					'completion',
					call(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier('result'),
					]),
				),
				declare('completionValue', member('completion', 'value')),
				declare('step1', call(t.identifier('outerNext'))),
				declare('stepDone', member('step1', 'done')),
			],
			branch: t.identifier('stepDone'),
			consequentAddresses: [5, 1],
			kind: 'normal',
		}],
		[5, {
			address: 5,
			body: [t.returnStatement(t.identifier('undefined'))],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>();
	for (const address of blocks.keys()) {
		mergedBlocks.set(address, new AddressSet([address]));
	}
	return {
		id: 1,
		blocks,
		entryAddress: 0,
		mergedBlocks,
		isGenerator: true,
		ssa: { basicBlocks: new AddressMap() },
		exceptions: {
			records: new AddressMap(),
			structuredRegionDescriptors: () => [],
			finalizerEdgeActions: () => [],
			structuredRegionForest: () => ({
				roots: [],
				nodeByHandler: new Map(),
				parentByHandler: new Map(),
			}),
		},
	} as unknown as IRFunction;
}

Deno.test('a delegate sharing its prelude and completion blocks is recovered', () => {
	const cfg = ImmutableCFG.fromIRFunction(delegateInsideLoop());
	const analyses = new CFGAnalyses(cfg);
	const info = recoverDelegateYieldDescriptors(cfg, analyses);
	assert.equal(info.delegates.length, 1, 'delegate not recovered');
	const [descriptor] = info.delegates;
	assert.equal(descriptor.prelude, 1);
	assert.equal(descriptor.header, 2);
	assert.equal(descriptor.normalExit, 4);

	// The enclosing loop owns the prelude block and the completion block, so the
	// delegate owns neither and suppresses only the statements it represents.
	assert.equal(descriptor.sourceBlocks.has(1), false);
	assert.equal(descriptor.sourceBlocks.has(4), false);
	assert.deepEqual([...descriptor.sourceBlocks].toSorted(), [2, 3]);
	assert.equal(info.delegateByPrelude.size, 0);
	assert.equal(info.delegateByHeader.get(2), descriptor);
	assert.deepEqual(descriptor.completionSkip, {
		block: 4,
		start: 0,
		end: 2,
	});
	// `observe(step.value)` is the loop header's own statement and stays there;
	// the acquisition statements after it are the delegate's.
	assert.deepEqual(descriptor.preludeSkip?.block, 1);
	assert.deepEqual(descriptor.preludeSkip?.statements, [
		2,
		3,
		4,
		5,
		6,
		7,
		8,
		9,
	]);
});
