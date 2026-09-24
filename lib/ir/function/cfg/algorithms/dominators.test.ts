import { strict as assert } from 'node:assert';
import { AddressGraph } from '../../../../utils/graph.ts';
import { AddressMap } from '../../../../utils/map.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import { computeDominanceFrontier, computeDominators } from './dominators.ts';

function cfg(
	addresses: number[],
	edges: Array<readonly [number, number]>,
): ImmutableCFG {
	const blocks = new AddressMap(addresses.map((address) => [address, {}]));
	const normalPredecessors = AddressGraph.fromBasicBlocks(blocks);
	for (const [from, to] of edges) normalPredecessors.addEdge(to, from);
	return {
		entry: 0,
		blocks,
		normalPredecessors,
	} as unknown as ImmutableCFG;
}

Deno.test('immediate dominators select the deepest strict dominator', () => {
	const graph = cfg(
		[0, 1, 2, 3, 4],
		[
			[0, 1],
			[0, 2],
			[1, 3],
			[2, 3],
			[3, 4],
		],
	);
	const dominators = computeDominators(graph);

	assert.deepEqual([...dominators.idom], [
		[0, null],
		[1, 0],
		[2, 0],
		[3, 0],
		[4, 3],
	]);
	assert.deepEqual([...dominators.children.get(0)!], [1, 2, 3]);
	assert.deepEqual([...dominators.children.get(3)!], [4]);
});

Deno.test('dominance frontier identifies a diamond join', () => {
	const graph = cfg(
		[0, 1, 2, 3, 4],
		[
			[0, 1],
			[0, 2],
			[1, 3],
			[2, 3],
			[3, 4],
		],
	);
	const dominators = computeDominators(graph);
	const frontier = computeDominanceFrontier(graph, dominators);

	assert.deepEqual([...frontier.frontierOf(1)], [3]);
	assert.deepEqual([...frontier.frontierOf(2)], [3]);
	assert.deepEqual([...frontier.frontierOf(3)], []);
});
