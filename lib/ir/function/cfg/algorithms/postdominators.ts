import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';

export interface PostDominatorInfo {
	ipdom: AddressMap<BlockAddr | null>;
	children: AddressMap<BlockAddr[]>;
	postdominates(a: BlockAddr, b: BlockAddr): boolean;
	nearestCommonPostdominator(
		a: BlockAddr,
		b: BlockAddr,
	): BlockAddr | null;
}

export function computePostDominators(cfg: ImmutableCFG): PostDominatorInfo {
	const allBlocks = new AddressSet(cfg.blocks.keys());
	const exits = [...cfg.blocks.keys()].filter((addr) =>
		(cfg.normalSuccessors.get(addr)?.size ?? 0) === 0
	);
	const postdominators = new AddressMap<AddressSet<BlockAddr>>();
	for (const addr of cfg.blocks.keys()) {
		postdominators.set(
			addr,
			exits.includes(addr)
				? new AddressSet([addr])
				: new AddressSet(allBlocks),
		);
	}

	let changed = true;
	while (changed) {
		changed = false;
		for (const addr of cfg.blocks.keys()) {
			if (exits.includes(addr)) continue;
			const successors = cfg.normalSuccessors.get(addr) ??
				new AddressSet<BlockAddr>();
			let next = new AddressSet<BlockAddr>(allBlocks);
			if (successors.size === 0) next = new AddressSet<BlockAddr>();
			for (const succ of successors) {
				next = next.intersection(postdominators.get(succ)!);
			}
			next.add(addr);
			if (!next.equals(postdominators.get(addr)!)) {
				postdominators.set(addr, next);
				changed = true;
			}
		}
	}

	const ipdom = computeImmediatePostDominators(cfg, postdominators);
	const children = new AddressMap<BlockAddr[]>();
	for (const addr of cfg.blocks.keys()) children.set(addr, []);
	for (const [addr, parent] of ipdom) {
		if (parent == null) continue;
		children.get(parent)?.push(addr);
	}
	const postdominates = (a: BlockAddr, b: BlockAddr) =>
		postdominators.get(b)?.has(a) ?? false;

	return {
		ipdom,
		children,
		postdominates,
		nearestCommonPostdominator(a, b) {
			const left = postdominators.get(a);
			const right = postdominators.get(b);
			if (!left || !right) return null;
			let best: BlockAddr | null = null;
			for (const candidate of left.intersection(right)) {
				if (best == null || postdominates(best, candidate)) {
					best = candidate;
				}
			}
			return best;
		},
	};
}

function computeImmediatePostDominators(
	cfg: ImmutableCFG,
	postdominators: AddressMap<AddressSet<BlockAddr>>,
) {
	const ipdom = new AddressMap<BlockAddr | null>();
	for (const addr of cfg.blocks.keys()) {
		const strict = new AddressSet(postdominators.get(addr)!);
		strict.delete(addr);
		let immediate: BlockAddr | null = null;
		for (const candidate of strict) {
			const postdominatedByOther = [...strict].some((other) =>
				other !== candidate && postdominators.get(candidate)?.has(other)
			);
			if (!postdominatedByOther) {
				immediate = candidate;
				break;
			}
		}
		ipdom.set(addr, immediate);
	}
	return ipdom;
}
