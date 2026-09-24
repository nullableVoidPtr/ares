import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';

export interface ReachabilityInfo {
	normalReachable: AddressSet<BlockAddr>;
	exceptionalReachable: AddressSet<BlockAddr>;
	allReachable: AddressSet<BlockAddr>;
}

export interface TraversalInfo {
	preorder: BlockAddr[];
	postorder: BlockAddr[];
	reversePostorder: BlockAddr[];
}

export function computeReachability(cfg: ImmutableCFG): ReachabilityInfo {
	const normalReachable = walk(
		cfg.entry,
		(addr) => cfg.normalSuccessors.get(addr) ?? new AddressSet(),
	);
	const allReachable = walk(cfg.entry, (addr) =>
		new AddressSet([
			...(cfg.normalSuccessors.get(addr) ?? []),
			...(cfg.exceptionalSuccessors.get(addr) ?? []),
		]));
	return {
		normalReachable,
		exceptionalReachable: allReachable.difference(normalReachable),
		allReachable,
	};
}

export function computeTraversal(cfg: ImmutableCFG): TraversalInfo {
	const seen = new AddressSet<BlockAddr>();
	const preorder: BlockAddr[] = [];
	const postorder: BlockAddr[] = [];

	const visit = (addr: BlockAddr) => {
		if (seen.has(addr) || !cfg.blocks.has(addr)) return;
		seen.add(addr);
		preorder.push(addr);
		const successors = [...(cfg.normalSuccessors.get(addr) ?? [])].sort(
			(
				left,
				right,
			) => left - right,
		);
		for (const succ of successors) visit(succ);
		postorder.push(addr);
	};

	visit(cfg.entry);
	return {
		preorder,
		postorder,
		reversePostorder: postorder.toReversed(),
	};
}

function walk(
	entry: BlockAddr,
	successorsOf: (addr: BlockAddr) => Iterable<BlockAddr>,
) {
	const seen = new AddressSet<BlockAddr>();
	const stack = [entry];
	while (stack.length > 0) {
		const addr = stack.pop()!;
		if (seen.has(addr)) continue;
		seen.add(addr);
		for (const succ of successorsOf(addr)) {
			if (!seen.has(succ)) stack.push(succ);
		}
	}
	return seen;
}
