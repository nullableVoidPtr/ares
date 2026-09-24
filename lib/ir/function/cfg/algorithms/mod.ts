import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import {
	computeDominanceFrontier,
	computeDominators,
	computeLoopDominators,
	type DominanceFrontierInfo,
	type DominatorInfo,
} from './dominators.ts';
import { computeNaturalLoops, type NaturalLoopInfo } from './naturalLoops.ts';
import {
	computePostDominators,
	type PostDominatorInfo,
} from './postdominators.ts';
import { computeReducibility, type ReducibilityInfo } from './reducibility.ts';
import { computeSCCs, type SCCInfo } from './tarjanSCC.ts';
import {
	computeReachability,
	computeTraversal,
	type ReachabilityInfo,
	type TraversalInfo,
} from './traversal.ts';

export interface ControlDependenceInfo {
	controllersOf(block: BlockAddr): AddressSet<BlockAddr>;
	controlledBy(block: BlockAddr): AddressSet<BlockAddr>;
}

/**
 * The CFG's derived analyses, each computed when first asked for and kept.
 *
 * All nine used to be computed in the constructor, so every caller paid for
 * all of them. Three -- `traversal`, `dominanceFrontier` and
 * `controlDependence` -- have no readers at all, and `controlDependence` is
 * the dearest of the set: two sets per block before it starts, then a walk up
 * the immediate-postdominator chain for every normal edge. It also pulled
 * `postdominators` in behind it for functions that never wanted either.
 *
 * Kept without any invalidation because `cfg` is an `ImmutableCFG`. The input
 * an analysis was derived from cannot change under it, so a stored result
 * stays true for as long as the object lives -- the reason this one is safe
 * where a cache over a mutating CFG would not be.
 */
export class CFGAnalyses {
	private cachedReachability?: ReachabilityInfo;
	private cachedTraversal?: TraversalInfo;
	private cachedSCCs?: SCCInfo;
	private cachedDominators?: DominatorInfo;
	private cachedLoopDominators?: DominatorInfo;
	private cachedPostdominators?: PostDominatorInfo;
	private cachedDominanceFrontier?: DominanceFrontierInfo;
	private cachedNaturalLoops?: NaturalLoopInfo;
	private cachedReducibility?: ReducibilityInfo;
	private cachedControlDependence?: ControlDependenceInfo;

	constructor(readonly cfg: ImmutableCFG) {}

	get reachability(): ReachabilityInfo {
		return this.cachedReachability ??= computeReachability(this.cfg);
	}

	get traversal(): TraversalInfo {
		return this.cachedTraversal ??= computeTraversal(this.cfg);
	}

	get sccs(): SCCInfo {
		return this.cachedSCCs ??= computeSCCs(this.cfg);
	}

	get dominators(): DominatorInfo {
		return this.cachedDominators ??= computeDominators(this.cfg);
	}

	get postdominators(): PostDominatorInfo {
		return this.cachedPostdominators ??= computePostDominators(this.cfg);
	}

	get loopDominators(): DominatorInfo {
		return this.cachedLoopDominators ??= this.cfg.hasExceptionRegions
			? computeLoopDominators(this.cfg)
			: this.dominators;
	}

	get dominanceFrontier(): DominanceFrontierInfo {
		return this.cachedDominanceFrontier ??= computeDominanceFrontier(
			this.cfg,
			this.dominators,
		);
	}

	get naturalLoops(): NaturalLoopInfo {
		return this.cachedNaturalLoops ??= computeNaturalLoops(
			this.cfg,
			this.loopDominators,
			this.reachability.normalReachable,
		);
	}

	get reducibility(): ReducibilityInfo {
		return this.cachedReducibility ??= computeReducibility(
			this.cfg,
			this.sccs,
			this.dominators,
			this.reachability.normalReachable,
		);
	}

	get controlDependence(): ControlDependenceInfo {
		return this.cachedControlDependence ??= computeControlDependence(
			this.cfg,
			this.postdominators,
		);
	}
}

function computeControlDependence(
	cfg: ImmutableCFG,
	postdominators: PostDominatorInfo,
): ControlDependenceInfo {
	const controllers = new AddressMap<AddressSet<BlockAddr>>();
	const controlled = new AddressMap<AddressSet<BlockAddr>>();
	for (const addr of cfg.blocks.keys()) {
		controllers.set(addr, new AddressSet());
		controlled.set(addr, new AddressSet());
	}
	for (const edge of cfg.normalEdges()) {
		if (postdominators.postdominates(edge.to, edge.from)) continue;
		let runner: BlockAddr | null = edge.to;
		const stop = postdominators.ipdom.get(edge.from) ?? null;
		while (runner != null && runner !== stop) {
			controllers.get(runner)?.add(edge.from);
			controlled.get(edge.from)?.add(runner);
			runner = postdominators.ipdom.get(runner) ?? null;
		}
	}
	return {
		controllersOf(block: BlockAddr) {
			return new AddressSet(controllers.get(block) ?? []);
		},
		controlledBy(block: BlockAddr) {
			return new AddressSet(controlled.get(block) ?? []);
		},
	};
}

export * from './dominators.ts';
export * from './naturalLoops.ts';
export * from './postdominators.ts';
export * from './reducibility.ts';
export * from './sese.ts';
export * from './tarjanSCC.ts';
export * from './traversal.ts';
