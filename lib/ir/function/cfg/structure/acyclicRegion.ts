import * as t from '@babel/types';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../../utils/set.ts';
import { type CFGAnalyses, findSESE } from '../algorithms/mod.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import { emptyRegion, type Region, sequenceRegion } from '../regions/region.ts';

const MAX_SHARED_ACYCLIC_BLOCKS = 24;

/**
 * Structure a bounded acyclic SESE graph whose branch arms share internal
 * nodes. A topological order makes every edge forward; nested labelled
 * sequences then represent non-adjacent edges without cloning a shared tail.
 */
export function tryStructureSharedAcyclicRegion(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	blockedHeaders: ReadonlySet<BlockAddr>,
	allowed?: AddressSet<BlockAddr>,
): { region: Region; join: BlockAddr } | null {
	const entry = cfg.blocks.get(cfg.entry);
	if (!entry || entry.terminator.kind !== 'if') return null;
	const join = analyses.postdominators.nearestCommonPostdominator(
		entry.terminator.fallthrough,
		entry.terminator.taken,
	);
	if (join == null || join === cfg.entry) return null;
	const sese = findSESE(cfg.entry, join, {
		cfg,
		dominators: analyses.dominators,
		postdominators: analyses.postdominators,
	});
	if (
		!sese || sese.body.size < 3 ||
		sese.body.size > MAX_SHARED_ACYCLIC_BLOCKS ||
		(allowed && !sese.body.isSubsetOf(allowed)) ||
		[...sese.body].some((address) => blockedHeaders.has(address))
	) return null;
	// A bounded call from an enclosing Try Region owns only normal control inside
	// its protected set. Its exceptional edges all lead to the handler already
	// owned by that Try, so they must not disable normal-DAG composition here.
	// Unrestricted composition may claim nothing an exception Region owns, and
	// that is decidable per block: a protected block has an exceptional
	// successor and a handler has an exceptional predecessor.
	if (
		!allowed && cfg.hasExceptionRegions &&
		[...sese.body].some((address) =>
			(cfg.exceptionalSuccessors.get(address)?.size ?? 0) > 0 ||
			(cfg.exceptionalPredecessors.get(address)?.size ?? 0) > 0
		)
	) return null;
	// A Phi at the join is lowered per incoming edge. Keep such a join with the
	// ordinary conditional reducers whenever an edge into it starts outside this
	// DAG: two Regions can then claim that edge, and moving the join out of its
	// original conditional scope decides which one owns it. When every
	// predecessor is inside the body the DAG owns all of them — a forward jump
	// carries its exact edge on a deferred exit, and the topologically last node
	// falls out into the join — so no enclosing Region is affected.
	if (
		cfg.blocks.get(join)?.ssaInstructions.some((instruction) =>
			instruction.instruction === 'Phi'
		) && (!allowed || allowed.has(join)) &&
		[
			...(cfg.normalPredecessors.get(join) ?? []),
			...(cfg.exceptionalPredecessors.get(join) ?? []),
		].some((address) => !sese.body.has(address))
	) return null;

	let hasSharedNode = false;
	for (const address of sese.body) {
		const block = cfg.blocks.get(address);
		if (
			!block ||
			(block.terminator.kind !== 'goto' &&
				block.terminator.kind !== 'if')
		) return null;
		const internalPredecessors = [
			...(cfg.normalPredecessors.get(address) ?? []),
		].filter((predecessor) => sese.body.has(predecessor));
		hasSharedNode ||= internalPredecessors.length > 1;
	}
	if (!hasSharedNode) return null;

	const order = topologicalOrder(sese.body, cfg);
	if (!order) return null;
	const labels = forwardEdgeLabels(order, join, cfg);
	let regions: Region[] = [];
	for (let index = 0; index < order.length; index++) {
		const address = order[index]!;
		const label = labels.get(address);
		if (label && regions.length > 0) {
			regions = [sequenceRegion(regions, label)];
		}
		regions.push(regionForNode(
			address,
			order[index + 1] ?? join,
			join,
			labels,
			cfg,
		));
	}
	const region = sequenceRegion(regions, labels.get(join));
	return { region, join };
}

function topologicalOrder(
	body: AddressSet<BlockAddr>,
	cfg: ImmutableCFG,
): BlockAddr[] | null {
	const indegree = new Map<BlockAddr, number>();
	for (const address of body) indegree.set(address, 0);
	for (const address of body) {
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (body.has(successor)) {
				indegree.set(successor, (indegree.get(successor) ?? 0) + 1);
			}
		}
	}
	const ready = [...body].filter((address) => indegree.get(address) === 0)
		.toSorted((left, right) => left - right);
	const order: BlockAddr[] = [];
	while (ready.length > 0) {
		const address = ready.shift()!;
		order.push(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (!body.has(successor)) continue;
			const next = (indegree.get(successor) ?? 0) - 1;
			indegree.set(successor, next);
			if (next === 0) {
				ready.push(successor);
				ready.sort((left, right) => left - right);
			}
		}
	}
	return order.length === body.size ? order : null;
}

function forwardEdgeLabels(
	order: readonly BlockAddr[],
	join: BlockAddr,
	cfg: ImmutableCFG,
): Map<BlockAddr, string> {
	const labels = new Map<BlockAddr, string>();
	for (let index = 0; index < order.length; index++) {
		const address = order[index]!;
		const next = order[index + 1] ?? join;
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (successor === next) continue;
			labels.set(
				successor,
				`cfg_dag_${formatAddress(order[0]!)}_${
					formatAddress(successor)
				}`,
			);
		}
	}
	return labels;
}

function regionForNode(
	address: BlockAddr,
	next: BlockAddr,
	join: BlockAddr,
	labels: ReadonlyMap<BlockAddr, string>,
	cfg: ImmutableCFG,
): Region {
	const block = cfg.blocks.get(address)!;
	if (block.terminator.kind === 'goto') {
		const basic: Region = {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([address]),
		};
		if (block.terminator.target === next) return basic;
		return sequenceRegion([
			basic,
			forwardJump(address, block.terminator.target, labels),
		]);
	}
	if (block.terminator.kind !== 'if') {
		throw new Error('shared acyclic Region contains a non-branch node');
	}
	const arm = (target: BlockAddr): Region =>
		target === next ? emptyRegion() : forwardJump(address, target, labels);
	return {
		kind: 'if',
		header: address,
		test: t.cloneNode(block.terminator.test, true),
		consequent: arm(block.terminator.taken),
		alternate: arm(block.terminator.fallthrough),
		join,
		sourceBlocks: new AddressSet([address]),
	};
}

function forwardJump(
	from: BlockAddr,
	target: BlockAddr,
	labels: ReadonlyMap<BlockAddr, string>,
): Region {
	const label = labels.get(target);
	if (!label) {
		throw new Error(
			`missing forward label for 0x${target.toString(16)}`,
		);
	}
	return sequenceRegion([
		{
			kind: 'deferredExit',
			exit: {
				kind: 'toJoin',
				edge: { from, to: target, kind: 'normal' },
				target,
				actions: [],
			},
			sourceBlocks: new AddressSet(),
		},
		{
			kind: 'labelBreak',
			label,
			target,
			sourceBlocks: new AddressSet(),
		},
	]);
}

function formatAddress(address: BlockAddr): string {
	return address < 0
		? `n${Math.abs(address).toString(16)}`
		: address.toString(16);
}
