import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { DominatorInfo } from './dominators.ts';
import type { CFGEdge, ImmutableCFG } from '../immutableCFG.ts';

export interface NaturalLoop {
	id: number;
	header: BlockAddr;
	latches: BlockAddr[];
	body: AddressSet<BlockAddr>;
	backedges: CFGEdge[];
	exits: CFGEdge[];
	parent?: number;
	children: number[];
}

export interface NaturalLoopInfo {
	loops: NaturalLoop[];
	loopByHeader: AddressMap<NaturalLoop>;
	loopOfBlock: AddressMap<number[]>;
}

export function computeNaturalLoops(
	cfg: ImmutableCFG,
	dominators: DominatorInfo,
	normalReachable?: AddressSet<BlockAddr>,
): NaturalLoopInfo {
	const backedges = cfg.normalEdges().filter((edge) =>
		dominators.dominates(edge.to, edge.from) &&
		// A catch trailer may jump back to the protected entry. Combined
		// exceptional dominance makes that edge look like a natural backedge, but
		// it is already owned by the exception retry descriptor. Keep genuine
		// loops wholly inside a catch; only exclude a handler-only source crossing
		// back into the function-entry normal component.
		!normalReachableCrossEntry(edge, normalReachable)
	);
	const byHeader = new AddressMap<CFGEdge[]>();
	for (const edge of backedges) {
		byHeader.getWithDefault(edge.to, () => []).push(edge);
	}

	const loops: NaturalLoop[] = [];
	const loopByHeader = new AddressMap<NaturalLoop>();
	for (const [header, edges] of byHeader) {
		const body = new AddressSet<BlockAddr>([header]);
		const stack = edges.map((edge) => edge.from);
		while (stack.length > 0) {
			const addr = stack.pop()!;
			if (body.has(addr)) continue;
			body.add(addr);
			for (const pred of cfg.normalPredecessors.get(addr) ?? []) {
				stack.push(pred);
			}
		}
		const exits: CFGEdge[] = [];
		for (const from of body) {
			for (const to of cfg.normalSuccessors.get(from) ?? []) {
				if (!body.has(to)) exits.push({ from, to, kind: 'normal' });
			}
		}
		const loop = {
			id: loops.length,
			header,
			latches: edges.map((edge) => edge.from),
			body,
			backedges: edges,
			exits,
			children: [],
		};
		loops.push(loop);
		loopByHeader.set(header, loop);
	}

	for (const loop of loops) {
		const parents = loops.filter((candidate) =>
			candidate !== loop &&
			candidate.body.size > loop.body.size &&
			loop.body.isSubsetOf(candidate.body)
		).toSorted((left, right) => left.body.size - right.body.size);
		const parent = parents[0];
		if (parent) {
			loop.parent = parent.id;
			parent.children.push(loop.id);
		}
	}

	const loopOfBlock = new AddressMap<number[]>();
	for (
		const loop of loops.toSorted((left, right) =>
			left.body.size - right.body.size
		)
	) {
		for (const block of loop.body) {
			loopOfBlock.getWithDefault(block, () => []).push(loop.id);
		}
	}

	return { loops, loopByHeader, loopOfBlock };
}

function normalReachableCrossEntry(
	edge: CFGEdge,
	normalReachable?: AddressSet<BlockAddr>,
): boolean {
	return normalReachable != null &&
		!normalReachable.has(edge.from) &&
		normalReachable.has(edge.to);
}
