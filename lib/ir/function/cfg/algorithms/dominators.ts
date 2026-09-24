import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressGraph } from '../../../../utils/graph.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';

export interface DominatorInfo {
	idom: AddressMap<BlockAddr | null>;
	children: AddressMap<BlockAddr[]>;
	dominates(a: BlockAddr, b: BlockAddr): boolean;
	nearestCommonDominator(
		a: BlockAddr,
		b: BlockAddr,
	): BlockAddr | null;
}

export function computeDominators(cfg: ImmutableCFG): DominatorInfo {
	return computeDominatorsFromPredecessors(
		cfg,
		(addr) =>
			cfg.normalPredecessors.get(addr) ?? new AddressSet<BlockAddr>(),
	);
}

/**
 * Dominance used only to discover normal loops in an exception CFG.
 *
 * A handler is another control-flow entry. Treating it as a root poisons the
 * dominance of every normal continuation it rejoins, while omitting the
 * exceptional edge loses ordinary source loops containing a try/catch. The
 * combined graph supplies that missing path without changing the normal-only
 * dominance relation used by Region ownership and reducibility.
 */
export function computeLoopDominators(cfg: ImmutableCFG): DominatorInfo {
	return computeDominatorsFromPredecessors(
		cfg,
		(addr) =>
			new AddressSet<BlockAddr>([
				...(cfg.normalPredecessors.get(addr) ?? []),
				...(cfg.exceptionalPredecessors.get(addr) ?? []),
			]),
	);
}

function computeDominatorsFromPredecessors(
	cfg: ImmutableCFG,
	predecessorsAt: (addr: BlockAddr) => AddressSet<BlockAddr>,
): DominatorInfo {
	const dominators = new AddressMap<AddressSet<BlockAddr>>();
	const allBlocks = new AddressSet(cfg.blocks.keys());
	for (const addr of cfg.blocks.keys()) {
		dominators.set(
			addr,
			addr === cfg.entry
				? new AddressSet([addr])
				: new AddressSet(allBlocks),
		);
	}

	let changed = true;
	while (changed) {
		changed = false;
		for (const addr of cfg.blocks.keys()) {
			if (addr === cfg.entry) continue;
			const predecessors = predecessorsAt(addr);
			let next = new AddressSet<BlockAddr>(allBlocks);
			if (predecessors.size === 0) {
				next = new AddressSet<BlockAddr>();
			}
			for (const pred of predecessors) {
				next = next.intersection(dominators.get(pred)!);
			}
			next.add(addr);
			if (!next.equals(dominators.get(addr)!)) {
				dominators.set(addr, next);
				changed = true;
			}
		}
	}

	const idom = computeImmediateDominators(cfg, dominators);
	const children = new AddressMap<BlockAddr[]>();
	for (const addr of cfg.blocks.keys()) children.set(addr, []);
	for (const [addr, parent] of idom) {
		if (parent == null) continue;
		children.get(parent)?.push(addr);
	}

	const dominates = (a: BlockAddr, b: BlockAddr) =>
		dominators.get(b)?.has(a) ?? false;

	return {
		idom,
		children,
		dominates,
		nearestCommonDominator(a, b) {
			const aDominators = dominators.get(a);
			const bDominators = dominators.get(b);
			if (!aDominators || !bDominators) return null;
			let best: BlockAddr | null = null;
			for (const candidate of aDominators.intersection(bDominators)) {
				if (best == null || dominates(best, candidate)) {
					best = candidate;
				}
			}
			return best;
		},
	};
}

export interface DominanceFrontierInfo {
	frontiers: AddressGraph;
	frontierOf(block: BlockAddr): AddressSet<BlockAddr>;
}

export function computeDominanceFrontier(
	cfg: ImmutableCFG,
	dominators: DominatorInfo,
): DominanceFrontierInfo {
	const frontiers = AddressGraph.fromBasicBlocks(cfg.blocks);
	for (const [block, predecessors] of cfg.normalPredecessors) {
		if (predecessors.size < 2) continue;
		for (const pred of predecessors) {
			let runner: BlockAddr | null = pred;
			while (
				runner != null && runner !== dominators.idom.get(block)
			) {
				frontiers.addEdge(runner, block);
				runner = dominators.idom.get(runner) ?? null;
			}
		}
	}
	return {
		frontiers,
		frontierOf(block: BlockAddr) {
			return new AddressSet(frontiers.get(block) ?? []);
		},
	};
}

function computeImmediateDominators(
	cfg: ImmutableCFG,
	dominators: AddressMap<AddressSet<BlockAddr>>,
) {
	const idom = new AddressMap<BlockAddr | null>();
	for (const addr of cfg.blocks.keys()) {
		if (addr === cfg.entry) {
			idom.set(addr, null);
			continue;
		}
		const strict = new AddressSet(dominators.get(addr)!);
		strict.delete(addr);
		let immediate: BlockAddr | null = null;
		for (const candidate of strict) {
			const dominatesOther = [...strict].some((other) =>
				other !== candidate && dominators.get(other)?.has(candidate)
			);
			if (!dominatesOther) {
				immediate = candidate;
				break;
			}
		}
		idom.set(addr, immediate);
	}
	return idom;
}
