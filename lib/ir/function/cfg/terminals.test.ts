import { strict as assert } from 'node:assert';
import * as t from '@babel/types';
import type { IRBlock } from '../../ast/mod.ts';
import type { IRFunction } from '../mod.ts';
import { AddressGraph } from '../../../utils/graph.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import {
	isHeaderTestedProtectedBodyLoop,
	reduceInlineTerminal,
} from './terminals.ts';

Deno.test('terminal inlining preserves a terminal shared by entry and loop exits', () => {
	const terminal = 4;
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			branch: t.identifier('enterLoop'),
			consequentAddresses: [terminal, 1],
		}],
		[1, {
			address: 1,
			body: [t.expressionStatement(t.identifier('work'))],
			consequentAddresses: [2],
		}],
		[2, {
			address: 2,
			body: [],
			branch: t.identifier('repeat'),
			consequentAddresses: [terminal, 1],
		}],
		[terminal, {
			address: terminal,
			body: [t.throwStatement(t.identifier('failure'))],
			consequentAddresses: [],
		}],
	]);
	const predecessorsOf = (address: number) =>
		new AddressSet(
			[...blocks]
				.filter(([, block]) =>
					block.consequentAddresses.includes(address)
				)
				.map(([predecessor]) => predecessor),
		);
	const func = {
		id: 1,
		blocks,
		predecessorsOf,
		exceptions: {
			activeHandlersEqual: () => true,
			isCatchTarget: () => false,
			records: new Map(),
		},
		markMergedBlocks: () => {},
	} as unknown as IRFunction;

	assert.equal(reduceInlineTerminal(func), false);
	assert.deepEqual([...predecessorsOf(terminal)].sort(), [0, 2]);
	assert.equal(blocks.get(terminal)?.body.length, 1);
	assert.equal(blocks.get(0)?.body.length, 0);
	assert.equal(blocks.get(2)?.body.length, 0);
});

Deno.test('iterator cleanup protection admits its enclosing natural loop', () => {
	const header = 1;
	const bodyEntry = 2;
	const latch = 3;
	const exit = 4;
	const handler = 10;
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [header],
		}],
		[header, {
			address: header,
			body: [],
			branch: t.identifier('done'),
			consequentAddresses: [exit, bodyEntry],
		}],
		[bodyEntry, {
			address: bodyEntry,
			body: [t.expressionStatement(t.callExpression(
				t.identifier('work'),
				[],
			))],
			consequentAddresses: [latch],
		}],
		[latch, {
			address: latch,
			body: [],
			consequentAddresses: [header],
		}],
		[exit, {
			address: exit,
			body: [t.returnStatement()],
			consequentAddresses: [],
		}],
		[handler, {
			address: handler,
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('caught'),
					t.callExpression(t.v8IntrinsicIdentifier('Catch'), []),
				)]),
				t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('IteratorClose'),
					[t.identifier('iterator'), t.booleanLiteral(true)],
				)),
				t.throwStatement(t.identifier('caught')),
			],
			consequentAddresses: [],
		}],
	]);
	const predecessorsOf = (address: number) =>
		new AddressSet(
			[...blocks]
				.filter(([, block]) =>
					block.consequentAddresses.includes(address)
				)
				.map(([predecessor]) => predecessor),
		);
	const activeHandlersAtBlock = (address: number) =>
		new AddressSet(
			address === bodyEntry || address === latch ? [handler] : [],
		);
	const func = {
		blocks,
		mergedBlocks: new AddressGraph<number, number>(
			[...blocks.keys()].map((address) => [
				address,
				new AddressSet([address]),
			]),
		),
		predecessorsOf,
		exceptions: {
			records: new Map([
				[handler, {
					protectedBlocks: new AddressSet([bodyEntry, latch]),
				}],
			]),
			activeHandlersAtBlock,
			activeHandlersEqual(
				left: number,
				right: number,
				options?: { exclude?: ReadonlySet<number> },
			) {
				const exclude = options?.exclude ?? new Set<number>();
				const visible = (address: number) =>
					new AddressSet(
						[...activeHandlersAtBlock(address)].filter((
							candidate,
						) => !exclude.has(candidate)),
					);
				return visible(left).equals(visible(right));
			},
		},
	} as unknown as IRFunction;

	assert.equal(
		isHeaderTestedProtectedBodyLoop(func, header, latch),
		true,
	);
});
