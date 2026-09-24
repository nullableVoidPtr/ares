import * as t from '@babel/types';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { CFGAnalyses, NaturalLoop } from '../algorithms/mod.ts';
import type { CFGEdge, ImmutableCFG } from '../immutableCFG.ts';
import {
	emptyRegion,
	hasPrestructuredControl,
	isEmptyRegion,
	loopRegionCoverageIssues,
	type LoopRegionExit,
	type Region,
	regionCoveredBlocks,
	sequenceRegion,
	type SwitchRegionCase,
} from '../regions/region.ts';
import type { Terminator } from '../terminator.ts';
import { shortCircuitBranch } from './ifRegion.ts';
import {
	exclusiveArmPartition,
	reachableBefore,
	reachableNodes,
	successorsWithin,
	topologicalOrder,
} from './armPartition.ts';

/**
 * Skeleton size bound. The composition itself is linear, so this bounds the
 * recursive structuring of the children it contracts and the size of the
 * labelled output it produces. 1024 covers the largest remaining Metro
 * function after ownership contraction without making the fallback effectively
 * unbounded.
 */
const MAX_LOOP_FOREST_NODES = 1024;

type LoopRegion = Extract<Region, { kind: 'loop' }>;

/**
 * A bounded sub-scope for control-forest composition.
 *
 * The forest owns every block reachable from `entry` inside `allowed` and
 * every edge between them. An edge leaving that residual is not ownership: the
 * caller decides what completes it — a loop `continue`, one of its ordered
 * loop exits, or an enclosing deferred join — and the forest declines whenever
 * a leaving edge has no such completion.
 *
 * `entry` is itself a boundary target: an edge back to it leaves the scope. A
 * loop header can therefore be composed together with its body while its own
 * backedges remain the caller's `continue` completions.
 */
export interface ControlForestScope {
	entry: BlockAddr;
	allowed: AddressSet<BlockAddr>;
	labelPrefix: string;
	completion: (from: BlockAddr, to: BlockAddr) => Region | null;
	/**
	 * Exceptional edges consumed by an enclosing protected Region. They are
	 * lexical scope boundaries, not control-skeleton edges: the surrounding
	 * `try` owns their transfer to the handler.
	 */
	exceptionBoundary?: (from: BlockAddr, to: BlockAddr) => boolean;
}

/**
 * Build the Switch Region for a recovered comparison chain so the skeleton can
 * contract it. Returning null declines the whole composition: emitting the
 * chain as ordinary branches would undo the recovery.
 */
export type SwitchAt = (dispatch: BlockAddr) => Region | null;

/** Recovered comparison chains a composition may contract, with their builder. */
export interface RecoveredSwitches {
	dispatches: AddressSet<BlockAddr>;
	switchAt: SwitchAt;
}

/**
 * Build the try/catch Region for a protected range so the skeleton can contract
 * it. Returning null declines the whole composition: the surrounding graph would
 * otherwise still carry the exceptional edges this contraction exists to hide.
 */
export type ExceptionAt = (entry: BlockAddr) => Region | null;

/** Protected ranges a composition may contract, with their builder. */
export interface ContractibleExceptions {
	entries: AddressSet<BlockAddr>;
	protectedBlocks: AddressSet<BlockAddr>;
	exceptionAt: ExceptionAt;
}

interface ControlForestBounds {
	minimumLoopRoots: number;
	labelPrefix: string;
	scope?: ControlForestScope;
	switchAt?: SwitchAt;
	compareChainDispatches?: AddressSet<BlockAddr>;
	exceptionAt?: ExceptionAt;
	protectedEntries?: AddressSet<BlockAddr>;
	protectedBlocks?: AddressSet<BlockAddr>;
}

/**
 * Compose multiple top-level natural-loop trees through their acyclic control
 * skeleton. Loop bodies are opaque nodes in that skeleton; nested loops remain
 * owned by the corresponding outer Loop Region.
 *
 * This is deliberately exact and bounded. It declines graphs with switches,
 * exceptional ownership, incomplete Loop Regions, cross-entry loop edges, or a
 * cyclic graph after loop contraction. Those shapes need their dedicated Region
 * owner rather than an address-ordered loop append.
 */
export function tryStructureBoundedLoopForest(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	loopAt: (loop: NaturalLoop) => LoopRegion | null,
	allowed?: AddressSet<BlockAddr>,
): Region | null {
	// A bounded arm may have intentional edges to its enclosing join. Without an
	// explicit scope the forest owns a whole reachable function suffix, so leave
	// arm boundaries to weak-SESE composition.
	if (allowed) return null;
	return tryStructureBoundedControlForest(cfg, analyses, loopAt, {
		minimumLoopRoots: 2,
		labelPrefix: 'cfg_forest',
	});
}

/**
 * Last-resort exact composition for a whole acyclic continuation skeleton.
 * Unlike the multi-loop entry point above, this also accepts an entirely
 * acyclic CFG or a graph with one top-level loop. Callers must prefer the
 * ordinary structured candidate whenever it already owns every branch: this
 * representation deliberately trades prettier nesting for exact single-copy
 * ownership of every reachable block and edge.
 */
export function tryStructureBoundedContinuationForest(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	loopAt: (loop: NaturalLoop) => LoopRegion | null,
	contractibleExceptions?: ContractibleExceptions,
	recoveredSwitches?: RecoveredSwitches,
): Region | null {
	return tryStructureBoundedControlForest(cfg, analyses, loopAt, {
		minimumLoopRoots: 0,
		labelPrefix: 'cfg_cont',
		switchAt: recoveredSwitches?.switchAt,
		compareChainDispatches: recoveredSwitches?.dispatches,
		exceptionAt: contractibleExceptions?.exceptionAt,
		protectedEntries: contractibleExceptions?.entries,
		protectedBlocks: contractibleExceptions?.protectedBlocks,
	});
}

/**
 * Exact composition of one bounded residual subgraph, such as the remainder of
 * a loop body that no single branch builder recognized. Blocks and edges inside
 * the scope are owned exactly once; edges leaving it become the completions the
 * caller supplied.
 */
export function tryStructureBoundedScopeForest(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	loopAt: (loop: NaturalLoop) => LoopRegion | null,
	scope: ControlForestScope,
	recoveredSwitches?: RecoveredSwitches,
	contractibleExceptions?: ContractibleExceptions,
): Region | null {
	return tryStructureBoundedControlForest(cfg, analyses, loopAt, {
		minimumLoopRoots: 0,
		labelPrefix: scope.labelPrefix,
		scope,
		switchAt: recoveredSwitches?.switchAt,
		compareChainDispatches: recoveredSwitches?.dispatches,
		exceptionAt: contractibleExceptions?.exceptionAt,
		protectedEntries: contractibleExceptions?.entries,
		protectedBlocks: contractibleExceptions?.protectedBlocks,
	});
}

function tryStructureBoundedControlForest(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	loopAt: (loop: NaturalLoop) => LoopRegion | null,
	bounds: ControlForestBounds,
): Region | null {
	const { minimumLoopRoots, labelPrefix, scope } = bounds;
	if (
		hasPrestructuredControl(
			scope?.allowed == null ? cfg : cfg.restrictTo(scope.allowed),
		)
	) return null;
	const entry = scope?.entry ?? cfg.entry;
	const decline = (_reason: string): null => null;
	const reachable = normalReachable(entry, cfg, scope?.allowed);
	const completionSources = new AddressSet<BlockAddr>();
	// A handler is entered only by an exceptional edge, so the normal walk never
	// reaches it. Contraction owns handler blocks, so they have to be part of the
	// reachable set the composition validates against — otherwise every
	// contracted range is rejected for owning blocks "outside" the graph.
	// A contracted loop may own the handler of a try inside its body even when
	// this composition contracts no protected range of its own.
	if (bounds.exceptionAt != null || cfg.hasExceptionRegions) {
		for (let changed = true; changed;) {
			changed = false;
			for (const from of [...reachable]) {
				for (const to of cfg.exceptionalSuccessors.get(from) ?? []) {
					if (scope?.exceptionBoundary?.(from, to)) continue;
					if (reachable.has(to)) continue;
					if (scope?.allowed && !scope.allowed.has(to)) continue;
					reachable.add(to);
					changed = true;
				}
			}
			for (const from of [...reachable]) {
				for (const to of cfg.normalSuccessors.get(from) ?? []) {
					if (reachable.has(to)) continue;
					if (scope?.allowed && !scope.allowed.has(to)) continue;
					reachable.add(to);
					changed = true;
				}
			}
		}
	}
	// The scope entry is a boundary: a loop rooted there is completed by the
	// caller rather than contracted into the skeleton it heads.
	const leavesScope = (to: BlockAddr) =>
		!reachable.has(to) || (scope != null && to === entry);
	const roots = analyses.naturalLoops.loops.filter((loop) =>
		reachable.has(loop.header) &&
		!bounds.protectedBlocks?.has(loop.header) &&
		(scope == null || loop.header !== entry) &&
		isTopLevelWithin(
			loop,
			analyses,
			reachable,
			scope ? entry : undefined,
		) &&
		loop.body.isSubsetOf(reachable)
	);
	if (roots.length < minimumLoopRoots) return decline('too few loop roots');

	// Contract each loop Region by everything it owns, which includes the ordered
	// exit trailers it emits on its own exit edges.
	const loopRegions = new AddressMap<LoopRegion>();
	const ownerByBlock = new AddressMap<BlockAddr>();
	for (const loop of roots) {
		const region = loopAt(loop);
		const issues = region?.kind === 'loop'
			? loopRegionCoverageIssues(region)
			: ['not a loop'];
		if (
			!region || !region.sourceBlocks.isSubsetOf(reachable) ||
			!loop.body.isSubsetOf(region.sourceBlocks) ||
			!loop.body.difference(
				region.suppressedBodyBlocks ?? new AddressSet<BlockAddr>(),
			).isSubsetOf(regionCoveredBlocks(region)) ||
			issues.length > 0 ||
			!hasExactTerminalExits(region, cfg)
		) {
			return decline(
				`loop 0x${loop.header.toString(16)} is inexact ` +
					`region=${region != null} sourceReachable=${
						region?.sourceBlocks.isSubsetOf(reachable) ?? false
					} bodySource=${
						region
							? loop.body.isSubsetOf(region.sourceBlocks)
							: false
					} issues=${JSON.stringify(issues)}`,
			);
		}
		loopRegions.set(loop.header, region);
		for (const address of region.sourceBlocks) {
			if (ownerByBlock.has(address)) return decline('overlapping loops');
			ownerByBlock.set(address, loop.header);
		}
	}
	// Natural loops have a single dominating header. Refuse an irreducible or
	// malformed external edge into the middle of an otherwise natural loop, or
	// into a trailer it owns.
	for (const loop of roots) {
		const owned = loopRegions.get(loop.header)!.sourceBlocks;
		for (const address of owned) {
			for (
				const predecessor of cfg.normalPredecessors.get(address) ?? []
			) {
				if (
					!owned.has(predecessor) && address !== loop.header &&
					reachable.has(predecessor)
				) {
					return decline(
						`secondary loop entry 0x${address.toString(16)}`,
					);
				}
			}
		}
	}

	// A recovered comparison chain is contracted the same way: its Switch Region
	// owns the dispatch and every case block, and the skeleton sees one node.
	// Dispatches inside a contractible protected range are owned by that
	// exception node; contracting them here would overlap the enclosing try/catch.
	const switchRegions = new AddressMap<Region>();
	const switchCandidates = [...bounds.compareChainDispatches ?? []]
		.filter((dispatch) =>
			reachable.has(dispatch) && !bounds.protectedBlocks?.has(dispatch)
		)
		.map((dispatch) => ({
			dispatch,
			region: bounds.switchAt?.(dispatch) ?? null,
		}))
		.toSorted((left, right) =>
			(right.region?.sourceBlocks.size ?? 0) -
				(left.region?.sourceBlocks.size ?? 0) ||
			left.dispatch - right.dispatch
		);
	for (const { dispatch, region } of switchCandidates) {
		// A dispatch a contracted loop or an outer recovered switch already owns
		// is represented inside that Region and needs no second skeleton node.
		if (ownerByBlock.has(dispatch)) continue;
		if (!region || !region.sourceBlocks.isSubsetOf(reachable)) {
			return decline('inexact switch contraction');
		}
		const hasSecondaryEntry = [...region.sourceBlocks].some((address) =>
			address !== dispatch &&
			[...(cfg.normalPredecessors.get(address) ?? [])].some(
				(predecessor) =>
					reachable.has(predecessor) &&
					!region.sourceBlocks.has(predecessor),
			)
		);
		if (hasSecondaryEntry) continue;
		// A recovered switch can lexically contain a natural loop. Prefer that
		// outer owner and remove the loop's separate skeleton node; the Switch
		// Region already contains the exact Loop Region.
		for (const [header, loopRegion] of [...loopRegions]) {
			if (!region.sourceBlocks.has(header)) continue;
			if (!loopRegion.sourceBlocks.isSubsetOf(region.sourceBlocks)) {
				return decline('partially overlapping switch loop');
			}
			loopRegions.delete(header);
			for (const address of loopRegion.sourceBlocks) {
				ownerByBlock.delete(address);
			}
		}
		switchRegions.set(dispatch, region);
		for (const address of region.sourceBlocks) {
			if (ownerByBlock.has(address)) {
				return decline(
					`overlapping switch 0x${dispatch.toString(16)} at 0x${
						address.toString(16)
					}`,
				);
			}
			ownerByBlock.set(address, dispatch);
		}
	}
	for (const [dispatch, region] of switchRegions) {
		for (const address of region.sourceBlocks) {
			for (
				const predecessor of cfg.normalPredecessors.get(address) ?? []
			) {
				if (
					!region.sourceBlocks.has(predecessor) &&
					address !== dispatch && reachable.has(predecessor)
				) {
					return decline(
						`secondary switch entry 0x${predecessor.toString(16)}` +
							`->0x${address.toString(16)} for 0x${
								dispatch.toString(16)
							}`,
					);
				}
			}
		}
	}

	// A protected range is contracted the same way, and for the same reason the
	// other composites are: its try/catch Region owns the protected body and the
	// handler, so every exceptional edge becomes internal to one skeleton node
	// and the normal-graph analyses around it are correct again.
	const exceptionRegions = new AddressMap<Region>();
	for (const protectedEntry of bounds.protectedEntries ?? []) {
		if (!reachable.has(protectedEntry)) continue;
		if (ownerByBlock.has(protectedEntry)) continue;
		const region = bounds.exceptionAt?.(protectedEntry) ?? null;
		if (!region || !region.sourceBlocks.isSubsetOf(reachable)) {
			return decline('inexact exception contraction');
		}
		if (!region.sourceBlocks.isSubsetOf(regionCoveredBlocks(region))) {
			return decline('exception contraction has uncovered sources');
		}
		exceptionRegions.set(protectedEntry, region);
		for (const address of region.sourceBlocks) {
			if (ownerByBlock.has(address)) {
				return decline(
					`overlapping exception 0x${protectedEntry.toString(16)} ` +
						`at 0x${address.toString(16)} with 0x${
							ownerByBlock.get(address)!.toString(16)
						} sources=${
							[...region.sourceBlocks]
								.toSorted((left, right) => left - right)
								.slice(0, 24)
								.map((source) => `0x${source.toString(16)}`)
								.join(',')
						}`,
				);
			}
			ownerByBlock.set(address, protectedEntry);
		}
	}
	for (const [protectedEntry, region] of exceptionRegions) {
		for (const address of region.sourceBlocks) {
			// Resume-split protected ranges can have several descriptor entries.
			// They are aliases of this same contracted exception node; no other
			// block may have a normal predecessor outside the Region.
			for (
				const predecessor of cfg.normalPredecessors.get(address) ?? []
			) {
				if (
					!region.sourceBlocks.has(predecessor) &&
					address !== protectedEntry &&
					!(bounds.protectedEntries?.has(address) &&
						ownerByBlock.get(address) === protectedEntry) &&
					reachable.has(predecessor)
				) {
					return decline(
						`secondary exception entry 0x${
							address.toString(16)
						} from 0x${predecessor.toString(16)} owner=0x${
							protectedEntry.toString(16)
						} entries=${
							[...(bounds.protectedEntries ?? [])].map((entry) =>
								`0x${entry.toString(16)}`
							).join(',')
						}`,
					);
				}
			}
		}
	}
	// The contraction is only sound if it hides every exceptional edge. One
	// leaving a contracted node — an inner range escaping to an outer handler —
	// would still be invisible to the skeleton's normal-graph reasoning.
	if (cfg.hasExceptionRegions) {
		for (const from of reachable) {
			for (const to of cfg.exceptionalSuccessors.get(from) ?? []) {
				if (scope?.exceptionBoundary?.(from, to)) continue;
				const owner = ownerByBlock.get(from);
				if (owner == null || ownerByBlock.get(to) !== owner) {
					return decline(
						`unowned exceptional edge 0x${from.toString(16)}->0x${
							to.toString(16)
						} ` +
							`owners=${owner?.toString(16) ?? '-'},${
								ownerByBlock.get(to)?.toString(16) ?? '-'
							}`,
					);
				}
			}
		}
	}

	const nodeFor = (address: BlockAddr) =>
		ownerByBlock.get(address) ?? address;
	const nodes = new AddressSet<BlockAddr>(
		[...reachable].map((address) => nodeFor(address)),
	);
	if (nodes.size > MAX_LOOP_FOREST_NODES) return decline('too many nodes');

	const successors = new AddressMap<AddressSet<BlockAddr>>();
	for (const node of nodes) successors.set(node, new AddressSet());
	for (const from of reachable) {
		const fromNode = nodeFor(from);
		for (const to of cfg.normalSuccessors.get(from) ?? []) {
			if (leavesScope(to)) continue;
			const toNode = nodeFor(to);
			if (fromNode !== toNode) successors.get(fromNode)?.add(toNode);
		}
	}
	/**
	 * Compose one closed subset of the contracted DAG. `fallthrough` is a lexical
	 * boundary owned by the caller: an edge to it ends this Region normally and
	 * therefore needs neither a forward label nor a scope completion.
	 *
	 * Before falling back to the exact labelled order, split an entry branch at a
	 * proven common postdominating node. Its two disjoint arms become an If Region
	 * and the shared node becomes the following Sequence trailer. Besides being
	 * more readable, this is the important ownership distinction for Phi-bearing
	 * value joins: the trailer is caller-side control, not a value returned by a
	 * synthetic function.
	 */
	const composeNodes = (
		subEntry: BlockAddr,
		subNodes: AddressSet<BlockAddr>,
		fallthrough?: BlockAddr,
		outerExit?: ArmExit,
	): Region | null => {
		const subSuccessors = successorsWithin(subNodes, successors);
		const order = topologicalOrder(subEntry, subNodes, subSuccessors);
		if (!order) {
			return decline(
				`cyclic contracted skeleton at 0x${subEntry.toString(16)}`,
			);
		}

		const block = ownerByBlock.has(subEntry)
			? undefined
			: cfg.blocks.get(subEntry);
		// The partitions below can only start at a branch, so a subset that opens
		// with straight-line blocks would fall to the labelled order even when
		// everything after that prefix is an ordinary conditional. Peel the
		// single-successor head and compose the remainder, which owns its own
		// entry because nothing else in the subset reaches it.
		if (block?.terminator.kind === 'goto' && subNodes.size > 1) {
			const next = nodeFor(block.terminator.target);
			const predecessors = [...subNodes].filter((node) =>
				subSuccessors.get(node)?.has(next)
			);
			if (
				next !== subEntry && subNodes.has(next) &&
				predecessors.length === 1 && predecessors[0] === subEntry
			) {
				const rest = new AddressSet(subNodes);
				rest.delete(subEntry);
				const tail = composeNodes(next, rest, fallthrough, outerExit);
				if (tail) {
					return sequenceRegion([{
						kind: 'basic',
						body: [],
						sourceBlocks: new AddressSet([subEntry]),
					}, tail]);
				}
			}
		}
		if (block?.terminator.kind === 'if') {
			const subBlocks = new AddressSet<BlockAddr>(
				[...reachable].filter((address) =>
					subNodes.has(nodeFor(address))
				),
			);
			const folded = shortCircuitBranch(cfg, subBlocks, subEntry);
			const taken = folded?.taken ?? block.terminator.taken;
			const fallthroughTarget = folded?.fallthrough ??
				block.terminator.fallthrough;
			const consequentEntry = nodeFor(taken);
			const alternateEntry = nodeFor(fallthroughTarget);
			const branchNodes = new AddressSet(subNodes);
			for (const absorbed of folded?.absorbed ?? []) {
				branchNodes.delete(nodeFor(absorbed));
			}
			const analysisNodes = new AddressSet(branchNodes);
			if (fallthrough != null) analysisNodes.add(fallthrough);
			const branchSuccessors = successorsWithin(
				analysisNodes,
				successors,
			);
			if (folded) {
				branchSuccessors.set(
					subEntry,
					new AddressSet([consequentEntry, alternateEntry]),
				);
			}
			const branchOrder = topologicalOrder(
				subEntry,
				analysisNodes,
				branchSuccessors,
			);
			const join = branchOrder == null ? null : sharedPostdominatingJoin(
				consequentEntry,
				alternateEntry,
				analysisNodes,
				branchSuccessors,
				branchOrder,
			);
			const terminator = block.terminator;
			/** The If Region for this branch, with arms already composed. */
			const branchRegion = (
				branchJoin: BlockAddr | undefined,
				consequent: Region,
				alternate: Region,
			): Region => ({
				kind: 'if',
				header: subEntry,
				branchEdges: {
					consequent: {
						from: folded?.takenSource ?? subEntry,
						to: taken,
						kind: 'normal',
					},
					alternate: {
						from: folded?.fallthroughSource ?? subEntry,
						to: fallthroughTarget,
						kind: 'normal',
					},
				},
				test: folded?.test ?? t.cloneNode(terminator.test, true),
				consequent,
				alternate,
				join: branchJoin,
				predicateBlocks: folded
					? new AddressSet([subEntry, ...folded.absorbed])
					: undefined,
				predicateBindings: folded?.bindings.length
					? folded.bindings
					: undefined,
				conditionalValue: branchJoin == null ? undefined : {
					kind: 'conditionalPhi',
					branch: subEntry,
					consequentEntry: taken,
					alternateEntry: fallthroughTarget,
					join: branchJoin,
					forms: ['shortcut', 'ternary'],
				},
				sourceBlocks: new AddressSet([
					subEntry,
					...folded?.absorbed ?? [],
					...consequent.sourceBlocks,
					...alternate.sourceBlocks,
				]),
			});
			if (join != null) {
				const consequentNodes = reachableBefore(
					consequentEntry,
					join,
					analysisNodes,
					branchSuccessors,
				);
				const alternateNodes = reachableBefore(
					alternateEntry,
					join,
					branchNodes,
					branchSuccessors,
				);
				const trailerNodes = join === fallthrough
					? new AddressSet<BlockAddr>()
					: reachableNodes(
						join,
						branchNodes,
						branchSuccessors,
					);
				const partition = new AddressSet<BlockAddr>([
					subEntry,
					...consequentNodes,
					...alternateNodes,
					...trailerNodes,
				]);
				if (
					consequentNodes.intersection(alternateNodes).size === 0 &&
					partition.equals(branchNodes)
				) {
					const joinExit = armExits(
						subEntry,
						fallthrough,
						join,
						labelPrefix,
						nodeFor,
						outerExit,
					);
					const consequent = consequentEntry === join
						? emptyRegion()
						: composeNodes(
							consequentEntry,
							consequentNodes,
							join,
							joinExit.exit,
						);
					const alternate = alternateEntry === join
						? emptyRegion()
						: composeNodes(
							alternateEntry,
							alternateNodes,
							join,
							joinExit.exit,
						);
					const trailer = join === fallthrough
						? emptyRegion()
						: composeNodes(
							join,
							trailerNodes,
							fallthrough,
							outerExit,
						);
					if (consequent && alternate && trailer) {
						return joinExit.wrap(sequenceRegion([
							branchRegion(join, consequent, alternate),
							trailer,
						]));
					}
				}
			}

			// The postdominator proof above declines a dispatch whose arms never
			// meet — each one returns, throws, or leaves the scope — and one whose
			// shared node is reached on some paths but bypassed on others. Both
			// are ordinary branches; owning them by arm reachability keeps the
			// `if` and leaves the skeleton nothing to label.
			// Identical arm entries are the degenerate branch the postdominator
			// path above already owns; the colouring below would hand the same
			// nodes to both arms.
			const partition = consequentEntry === alternateEntry
				? null
				: exclusiveArmPartition(
					subEntry,
					[consequentEntry, alternateEntry],
					branchNodes,
					branchSuccessors,
				);
			if (partition) {
				const { trailerRoot } = partition;
				const armBoundary = trailerRoot ?? fallthrough;
				const exit = armExits(
					subEntry,
					fallthrough,
					armBoundary,
					labelPrefix,
					nodeFor,
					outerExit,
				);
				const compose = (
					entry: BlockAddr,
					owned: AddressSet<BlockAddr>,
				) => composeNodes(entry, owned, armBoundary, exit.exit);
				const consequent = exit.arm(
					consequentEntry,
					partition.armNodes.get(consequentEntry),
					folded?.takenSource ?? subEntry,
					taken,
					compose,
				);
				const alternate = exit.arm(
					alternateEntry,
					partition.armNodes.get(alternateEntry),
					folded?.fallthroughSource ?? subEntry,
					fallthroughTarget,
					compose,
				);
				const trailer = trailerRoot == null ? null : composeNodes(
					trailerRoot,
					partition.trailerNodes,
					fallthrough,
					outerExit,
				);
				if (
					consequent && alternate &&
					(trailer != null || trailerRoot == null)
				) {
					const branch = branchRegion(
						trailerRoot ?? undefined,
						consequent,
						alternate,
					);
					return exit.wrap(
						trailer ? sequenceRegion([branch, trailer]) : branch,
					);
				}
			}
		}

		// A dispatch terminator is otherwise emitted as one skeleton node whose
		// every case jumps to a labelled rung holding the real case body.
		// Partitioning the subset by arm gives the switch its own cases and hands
		// the shared suffix to the enclosing Sequence.
		if (block?.terminator.kind === 'switch') {
			const terminator = block.terminator;
			const caseTargets = terminator.cases.filter((edge) =>
				edge.target !== terminator.defaultTarget
			);
			const armEntries = new AddressSet([
				...caseTargets.map((edge) => nodeFor(edge.target)),
				nodeFor(terminator.defaultTarget),
			]);
			const partition = exclusiveArmPartition(
				subEntry,
				[...armEntries],
				subNodes,
				subSuccessors,
			);
			if (partition) {
				const armBoundary = partition.trailerRoot ?? fallthrough;
				const exit = armExits(
					subEntry,
					fallthrough,
					armBoundary,
					labelPrefix,
					nodeFor,
					outerExit,
				);
				// The original target an arm entry stands for, so a completion
				// carries the edge the dispatch actually took.
				const targetByEntry = new AddressMap<BlockAddr>();
				for (const edge of terminator.cases) {
					const entry = nodeFor(edge.target);
					if (!targetByEntry.has(entry)) {
						targetByEntry.set(entry, edge.target);
					}
				}
				const defaultEntry = nodeFor(terminator.defaultTarget);
				if (!targetByEntry.has(defaultEntry)) {
					targetByEntry.set(defaultEntry, terminator.defaultTarget);
				}
				const bodies = new AddressMap<Region>();
				let owned = true;
				for (const entry of armEntries) {
					const body = exit.arm(
						entry,
						partition.armNodes.get(entry),
						subEntry,
						targetByEntry.get(entry) ?? entry,
						(armEntry, armNodes) =>
							composeNodes(
								armEntry,
								armNodes,
								armBoundary,
								exit.exit,
							),
					);
					if (!body) {
						owned = false;
						break;
					}
					bodies.set(entry, body);
				}
				const trailer = !owned || partition.trailerRoot == null
					? null
					: composeNodes(
						partition.trailerRoot,
						partition.trailerNodes,
						fallthrough,
						outerExit,
					);
				if (
					owned && (trailer != null || partition.trailerRoot == null)
				) {
					const cases: SwitchRegionCase[] = [];
					const caseByEntry = new AddressMap<SwitchRegionCase>();
					for (const edge of caseTargets) {
						const test = edge.test
							? t.cloneNode(edge.test, true)
							: null;
						// Several labels selecting one arm are aliases of a single
						// case, not a repetition of its body.
						const existing = caseByEntry.get(nodeFor(edge.target));
						if (existing) {
							if (test) (existing.aliases ??= []).push(test);
							continue;
						}
						const body = bodies.get(nodeFor(edge.target))!;
						const switchCase: SwitchRegionCase = {
							test,
							target: edge.target,
							source: subEntry,
							body,
							completion: caseCompletesAtJoin(body, cfg)
								? 'break'
								: undefined,
						};
						cases.push(switchCase);
						caseByEntry.set(nodeFor(edge.target), switchCase);
					}
					const defaultBody = bodies.get(
						nodeFor(terminator.defaultTarget),
					)!;
					const region: Region = {
						kind: 'switch',
						header: subEntry,
						discriminant: t.cloneNode(
							terminator.discriminant,
							true,
						),
						join: partition.trailerRoot ?? undefined,
						cases,
						defaultTarget: terminator.defaultTarget,
						defaultSource: subEntry,
						defaultBody,
						sourceBlocks: new AddressSet([
							subEntry,
							...cases.flatMap((switchCase) => [
								...switchCase.body.sourceBlocks,
							]),
							...defaultBody.sourceBlocks,
						]),
					};
					return exit.wrap(
						trailer ? sequenceRegion([region, trailer]) : region,
					);
				}
			}
		}

		const labels = forwardEdgeLabels(order, subSuccessors, labelPrefix);
		if (fallthrough != null) {
			for (let index = 0; index < order.length; index++) {
				const node = order[index]!;
				const next: BlockAddr | undefined = order[index + 1] ??
					fallthrough;
				if (
					next !== fallthrough &&
					successors.get(node)?.has(fallthrough)
				) {
					labels.set(
						fallthrough,
						`${labelPrefix}_${formatAddress(subEntry)}_${
							formatAddress(fallthrough)
						}`,
					);
					break;
				}
			}
		}
		const localLeavesScope = (to: BlockAddr) => {
			const target = nodeFor(to);
			return target !== fallthrough &&
				((scope != null && to === scope.entry) ||
					!subNodes.has(target));
		};
		const localScope: ControlForestScope = {
			entry: subEntry,
			allowed: new AddressSet(),
			labelPrefix,
			completion: (from, to) => {
				const completion = outerExit?.(from, to) ??
					scope?.completion(from, to) ?? null;
				if (completion) {
					for (const source of completion.sourceBlocks) {
						completionSources.add(source);
					}
				}
				return completion;
			},
		};
		/** The transfer carried by one edge in this lexical subset. */
		const edgeRegion = (
			from: BlockAddr,
			to: BlockAddr,
			next: BlockAddr | undefined,
		): Region | null => {
			const target = nodeFor(to);
			if (target === next) return emptyRegion();
			if (localLeavesScope(to)) return localScope.completion(from, to);
			const label = labels.get(target);
			return label ? forwardJump(from, to, target, label) : null;
		};
		let regions: Region[] = [];
		for (let index = 0; index < order.length; index++) {
			const node = order[index]!;
			const label = labels.get(node);
			if (label && regions.length > 0) {
				regions = [sequenceRegion(regions, label)];
			}
			const next = order[index + 1] ?? fallthrough;
			const loopRegion = loopRegions.get(node);
			const nodeRegion = loopRegion
				? routeLoopExits(
					loopRegion,
					next,
					nodeFor,
					labels,
					localLeavesScope,
					localScope,
				)
				: exceptionRegions.has(node)
				? routeExceptionExits(
					exceptionRegions.get(node)!,
					next,
					nodeFor,
					edgeRegion,
					cfg,
				)
				: switchRegions.has(node)
				? routeSwitchExits(
					switchRegions.get(node)!,
					next,
					nodeFor,
					edgeRegion,
					cfg,
				)
				: regionForBlock(
					node,
					edgeRegion,
					next,
					nodeFor,
					loopRegions,
					cfg,
				);
			if (!nodeRegion) {
				return decline(
					`could not route node 0x${node.toString(16)}`,
				);
			}
			regions.push(nodeRegion);
		}
		return sequenceRegion(
			regions,
			fallthrough == null ? undefined : labels.get(fallthrough),
		);
	};

	const region = composeNodes(nodeFor(entry), nodes);
	if (!region) return decline('node composition failed');
	if (!reachable.isSubsetOf(regionCoveredBlocks(region))) {
		return decline('composed region did not cover reachable graph');
	}
	const allowedSources = reachable.union(completionSources);
	if (!region.sourceBlocks.isSubsetOf(allowedSources)) {
		return decline(
			`composed region escaped reachable graph: ${
				[...region.sourceBlocks.difference(allowedSources)].map((
					address,
				) => `0x${address.toString(16)}`).join(',')
			}`,
		);
	}
	return region;
}

/**
 * A contracted node leaves through one edge. When that edge does not fall
 * through to the next skeleton node it needs the same transfer any other node
 * would use.
 */
function routeContractedExit(
	region: Region,
	node: BlockAddr,
	next: BlockAddr | undefined,
	edgeRegion: (
		from: BlockAddr,
		to: BlockAddr,
		next: BlockAddr | undefined,
	) => Region | null,
	cfg: ImmutableCFG,
): Region | null {
	const exits = new AddressMap<BlockAddr>();
	for (const address of region.sourceBlocks) {
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (region.sourceBlocks.has(successor)) continue;
			exits.set(successor, address);
		}
	}
	if (exits.size === 0) return region;
	if (exits.size > 1) return null;
	const [[target, from]] = [...exits];
	const transfer = edgeRegion(from, target, next);
	if (!transfer) return null;
	return isEmptyRegion(transfer)
		? region
		: sequenceRegion([region, transfer]);
}

function hasExactTerminalExits(
	loop: LoopRegion,
	cfg: ImmutableCFG,
): boolean {
	return loop.exits.every((exit) => {
		if (exit.kind !== 'return' && exit.kind !== 'throw') return true;
		if (exit.trailer && exit.trailer.sourceBlocks.has(exit.to)) return true;
		const terminator = cfg.blocks.get(exit.to)?.terminator;
		return exit.kind === 'return'
			? terminator?.kind === 'return'
			: terminator?.kind === 'throw';
	});
}

function isTopLevelWithin(
	loop: NaturalLoop,
	analyses: CFGAnalyses,
	scope: AddressSet<BlockAddr>,
	/** A loop headed here bounds the scope and does not own its children. */
	boundary?: BlockAddr,
): boolean {
	if (loop.parent == null) return true;
	const parent = analyses.naturalLoops.loops[loop.parent];
	return parent == null || !scope.has(parent.header) ||
		parent.header === boundary;
}

function normalReachable(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	allowed?: AddressSet<BlockAddr>,
): AddressSet<BlockAddr> {
	const reachable = new AddressSet<BlockAddr>();
	const pending = [entry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (
			reachable.has(address) || !cfg.blocks.has(address) ||
			(allowed && !allowed.has(address))
		) continue;
		reachable.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
	}
	return reachable;
}

/**
 * Whether a case body reaches the switch's continuation rather than ending the
 * function or transferring somewhere the Region already represents.
 *
 * A body that completes normally has to `break`, or control falls into the case
 * the skeleton happens to order next.
 */
function caseCompletesAtJoin(body: Region, cfg: ImmutableCFG): boolean {
	if (isEmptyRegion(body)) return true;
	for (const from of body.sourceBlocks) {
		for (const to of cfg.normalSuccessors.get(from) ?? []) {
			if (!body.sourceBlocks.has(to)) return true;
		}
	}
	return false;
}

/** A transfer for an edge leaving a composed subset, supplied by its caller. */
type ArmExit = (from: BlockAddr, to: BlockAddr) => Region | null;

/**
 * How a partitioned arm leaves its branch.
 *
 * An arm the partition owns is composed against the branch's own boundary, and
 * an arm that resumes exactly at that boundary is empty. What the labelled
 * order could express and the partition could not is an arm that resumes at the
 * *enclosing* boundary: it has to skip this branch's own trailer, so it breaks
 * out of a label naming the whole composition. That is one label for the
 * branch rather than one rung per arm.
 *
 * `exit` hands the same disposition to the arm's own composition, so an edge
 * leaving from inside the arm is a transfer rather than a refusal. The arm
 * still owns and emits every block it covers; only the edge becomes a jump.
 * That distinction is the whole constraint here — replacing an entire arm with
 * a transfer strands any definition the skipped path carried, which is why an
 * arm *entry* the partition does not own is still declined rather than handed
 * to `scope.completion`. Measured on TestApp fn#7850 and fn#6540, which leak
 * five register names that way.
 *
 * `wrap` adds the label only if something actually asked for it.
 */
function armExits(
	subEntry: BlockAddr,
	fallthrough: BlockAddr | undefined,
	armBoundary: BlockAddr | undefined,
	labelPrefix: string,
	nodeFor: (address: BlockAddr) => BlockAddr,
	outerExit?: ArmExit,
): {
	arm: (
		entry: BlockAddr,
		owned: AddressSet<BlockAddr> | undefined,
		from: BlockAddr,
		to: BlockAddr,
		compose: (
			entry: BlockAddr,
			owned: AddressSet<BlockAddr>,
		) => Region | null,
	) => Region | null;
	exit: ArmExit;
	wrap: (region: Region) => Region;
} {
	let label: string | undefined;
	const skip = (from: BlockAddr, to: BlockAddr): Region => {
		label ??= `${labelPrefix}_${formatAddress(subEntry)}_${
			formatAddress(fallthrough!)
		}`;
		return boundedScopeExit(from, to, label);
	};
	const exit: ArmExit = (from, to) =>
		fallthrough != null && nodeFor(to) === fallthrough
			? skip(from, to)
			: outerExit?.(from, to) ?? null;
	return {
		arm(entry, owned, from, to, compose) {
			if (owned?.has(entry)) return compose(entry, owned);
			if (entry === armBoundary) return emptyRegion();
			if (fallthrough != null && entry === fallthrough) {
				return skip(from, to);
			}
			return null;
		},
		exit,
		wrap(region) {
			return label == null ? region : sequenceRegion([region], label);
		},
	};
}

/**
 * The earliest common node reached on every path from both branch arms.
 *
 * The forest is already acyclic after loop contraction, so the topological
 * order gives a stable nearest candidate. Requiring every path to reach it is
 * the local postdominance proof that lets the caller move it out as a shared
 * Sequence trailer.
 */
function sharedPostdominatingJoin(
	consequent: BlockAddr,
	alternate: BlockAddr,
	nodes: AddressSet<BlockAddr>,
	successors: ReadonlyMap<BlockAddr, AddressSet<BlockAddr>>,
	order: readonly BlockAddr[],
): BlockAddr | null {
	if (!nodes.has(consequent) || !nodes.has(alternate)) return null;
	if (consequent === alternate) return consequent;
	const postdominators = new AddressMap<AddressSet<BlockAddr>>();
	for (const node of order.toReversed()) {
		const outgoing = successors.get(node) ?? new AddressSet<BlockAddr>();
		let common: AddressSet<BlockAddr>;
		if (outgoing.size === 0) {
			common = new AddressSet();
		} else {
			const [first, ...rest] = [...outgoing];
			common = new AddressSet(postdominators.get(first!) ?? []);
			for (const successor of rest) {
				common = common.intersection(
					postdominators.get(successor) ?? new AddressSet(),
				);
			}
		}
		common.add(node);
		postdominators.set(node, common);
	}
	const common = (postdominators.get(consequent) ?? new AddressSet())
		.intersection(postdominators.get(alternate) ?? new AddressSet());
	for (const candidate of order) {
		if (common.has(candidate)) return candidate;
	}
	return null;
}

function forwardEdgeLabels(
	order: readonly BlockAddr[],
	successors: AddressMap<AddressSet<BlockAddr>>,
	labelPrefix: string,
): AddressMap<string> {
	const labels = new AddressMap<string>();
	for (let index = 0; index < order.length; index++) {
		const node = order[index]!;
		const next = order[index + 1];
		for (const target of successors.get(node) ?? []) {
			if (target === next) continue;
			labels.set(
				target,
				`${labelPrefix}_${formatAddress(order[0]!)}_${
					formatAddress(target)
				}`,
			);
		}
	}
	return labels;
}

/**
 * The edges by which a contracted node leaves itself, and the skeleton nodes
 * they resume at.
 *
 * A contracted node is opaque to the skeleton: its own blocks are owned, so
 * what has to be routed is exactly the normal edges that cross the boundary.
 */
function leavingEdges(
	region: Region,
	nodeFor: (address: BlockAddr) => BlockAddr,
	cfg: ImmutableCFG,
): {
	owned: AddressSet<BlockAddr>;
	leaving: Array<{ from: BlockAddr; to: BlockAddr }>;
	targets: AddressSet<BlockAddr>;
} {
	const owned = region.sourceBlocks;
	const covered = regionCoveredBlocks(region);
	const leaving: Array<{ from: BlockAddr; to: BlockAddr }> = [];
	const targets = new AddressSet<BlockAddr>();
	for (const from of owned) {
		for (const to of cfg.normalSuccessors.get(from) ?? []) {
			if (covered.has(to)) continue;
			const terminal = cfg.blocks.get(to)?.terminator.kind;
			if (
				terminal === 'return' || terminal === 'throw' ||
				terminal === 'unreachable'
			) continue;
			leaving.push({ from, to });
			targets.add(nodeFor(to));
		}
	}
	return { owned, leaving, targets };
}

/**
 * Order the transfer for one leaving edge after the Region it leaves.
 *
 * An empty transfer means the edge resumes at the node the skeleton already
 * orders next, so the Region stands alone.
 */
function appendTransfer(
	region: Region,
	from: BlockAddr,
	to: BlockAddr,
	next: BlockAddr | undefined,
	edgeRegion: (
		from: BlockAddr,
		to: BlockAddr,
		next: BlockAddr | undefined,
	) => Region | null,
): Region | null {
	const transfer = edgeRegion(from, to, next);
	if (!transfer) return null;
	return isEmptyRegion(transfer)
		? region
		: sequenceRegion([region, transfer]);
}

/**
 * Place a contracted exception Region in the skeleton.
 *
 * Contraction already put the protected body and the handler or finalizer under
 * one node, so what remains is the normal edges that leave it. The protected
 * body and its exceptional part usually rejoin at the same block — that is what
 * makes the range a composite — and the skeleton either orders that node next
 * or names it with a label. When they resume at distinct blocks, route each
 * completion within the part that owns its source edge.
 */
function routeExceptionExits(
	region: Region,
	next: BlockAddr | undefined,
	nodeFor: (address: BlockAddr) => BlockAddr,
	edgeRegion: (
		from: BlockAddr,
		to: BlockAddr,
		next: BlockAddr | undefined,
	) => Region | null,
	cfg: ImmutableCFG,
): Region | null {
	const { owned, leaving, targets } = leavingEdges(region, nodeFor, cfg);
	if (targets.size === 0) return region;
	if (targets.size > 1) {
		if (region.kind === 'tryCatch' || region.kind === 'tryFinally') {
			const body = routeExceptionPart(
				region.body,
				next,
				nodeFor,
				edgeRegion,
				cfg,
			);
			const other = routeExceptionPart(
				region.kind === 'tryCatch' ? region.handler : region.finalizer,
				next,
				nodeFor,
				edgeRegion,
				cfg,
			);
			if (body && other) {
				return region.kind === 'tryCatch'
					? { ...region, body, handler: other }
					: { ...region, body, finalizer: other };
			}
		}
		return null;
	}
	// The try body and the handler each leave by their own edge, and those edges
	// carry different Phi copies. One transfer after the node can only place the
	// first edge's, so each path takes a marker for its own edge.
	const placed = leaving.length > 1
		? (region.kind === 'tryCatch'
			? {
				...region,
				body: withEdgeMarkers(region.body, leaving),
				handler: withEdgeMarkers(region.handler, leaving),
			}
			: region.kind === 'tryFinally'
			? {
				...region,
				body: withEdgeMarkers(region.body, leaving),
				finalizer: withEdgeMarkers(region.finalizer, leaving),
			}
			: null)
		: region;
	if (!placed) return null;
	const [{ from, to }] = leaving;
	return appendTransfer(placed, from, to, next, edgeRegion);
}

function routeExceptionPart(
	part: Region,
	next: BlockAddr | undefined,
	nodeFor: (address: BlockAddr) => BlockAddr,
	edgeRegion: (
		from: BlockAddr,
		to: BlockAddr,
		next: BlockAddr | undefined,
	) => Region | null,
	cfg: ImmutableCFG,
): Region | null {
	const { leaving, targets } = leavingEdges(part, nodeFor, cfg);
	if (targets.size === 0) return part;
	if (targets.size > 1) {
		return routeExceptionPartEdges(
			part,
			leaving,
			next,
			edgeRegion,
			cfg,
		);
	}
	const [{ from, to }] = leaving;
	return appendTransfer(part, from, to, next, edgeRegion);
}

/**
 * Route distinct exits at the lexical leaves that own their source edges.
 *
 * A contracted catch can contain a protected branch whose arms resume at two
 * different nodes after the try. Appending one transfer after the whole try
 * would make both paths take it. Descending through the already-proven Region
 * tree keeps each transfer in the arm that actually leaves by that edge. The
 * rewrite is transactional: every edge must resolve to exactly one leaf.
 */
function routeExceptionPartEdges(
	part: Region,
	edges: ReadonlyArray<{ from: BlockAddr; to: BlockAddr }>,
	next: BlockAddr | undefined,
	edgeRegion: (
		from: BlockAddr,
		to: BlockAddr,
		next: BlockAddr | undefined,
	) => Region | null,
	cfg: ImmutableCFG,
): Region | null {
	if (edges.length === 0) return part;
	if (part.kind === 'sequence') {
		const routed: Region[] = [];
		const remaining = [...edges];
		for (const child of part.regions) {
			const childEdges = remaining.filter((edge) =>
				child.sourceBlocks.has(edge.from)
			);
			for (const edge of childEdges) {
				remaining.splice(remaining.indexOf(edge), 1);
			}
			const rewritten = routeExceptionPartEdges(
				child,
				childEdges,
				next,
				edgeRegion,
				cfg,
			);
			if (!rewritten) return null;
			routed.push(rewritten);
		}
		if (remaining.length > 0) return null;
		return { ...part, regions: routed };
	}
	if (part.kind === 'if') {
		const terminator = cfg.blocks.get(part.header)?.terminator;
		if (terminator?.kind !== 'if') return null;
		const consequentEdge = part.branchEdges?.consequent ?? {
			from: part.header,
			to: terminator.taken,
			kind: 'normal' as const,
		};
		const alternateEdge = part.branchEdges?.alternate ?? {
			from: part.header,
			to: terminator.fallthrough,
			kind: 'normal' as const,
		};
		const routeArm = (
			arm: Region,
			branch: CFGEdge,
		): Region | null => {
			const childEdges = edges.filter((edge) =>
				arm.sourceBlocks.has(edge.from)
			);
			const direct = edges.find((edge) =>
				edge.from === branch.from && edge.to === branch.to
			);
			const routed = routeExceptionPartEdges(
				arm,
				childEdges,
				next,
				edgeRegion,
				cfg,
			);
			if (!routed) return null;
			return direct
				? appendTransfer(
					routed,
					direct.from,
					direct.to,
					next,
					edgeRegion,
				)
				: routed;
		};
		const consequent = routeArm(part.consequent, consequentEdge);
		const alternate = routeArm(part.alternate, alternateEdge);
		if (!consequent || !alternate) return null;
		const assigned = new Set<string>();
		for (const edge of edges) {
			if (
				part.consequent.sourceBlocks.has(edge.from) ||
				part.alternate.sourceBlocks.has(edge.from) ||
				(edge.from === consequentEdge.from &&
					edge.to === consequentEdge.to) ||
				(edge.from === alternateEdge.from &&
					edge.to === alternateEdge.to)
			) assigned.add(`${edge.from}:${edge.to}`);
		}
		if (assigned.size !== edges.length) return null;
		return { ...part, consequent, alternate };
	}
	if (part.kind === 'tryCatch' || part.kind === 'tryFinally') {
		const bodyEdges = edges.filter((edge) =>
			part.body.sourceBlocks.has(edge.from)
		);
		const other = part.kind === 'tryCatch' ? part.handler : part.finalizer;
		const otherEdges = edges.filter((edge) =>
			other.sourceBlocks.has(edge.from)
		);
		if (bodyEdges.length + otherEdges.length !== edges.length) return null;
		const body = routeExceptionPartEdges(
			part.body,
			bodyEdges,
			next,
			edgeRegion,
			cfg,
		);
		const routedOther = routeExceptionPartEdges(
			other,
			otherEdges,
			next,
			edgeRegion,
			cfg,
		);
		if (!body || !routedOther) return null;
		return part.kind === 'tryCatch'
			? { ...part, body, handler: routedOther }
			: { ...part, body, finalizer: routedOther };
	}
	if (!edges.every((edge) => part.sourceBlocks.has(edge.from))) return null;
	if (edges.length !== 1) return null;
	const [edge] = edges;
	return appendTransfer(part, edge.from, edge.to, next, edgeRegion);
}

/**
 * Append a Phi-only marker for each edge this part of the region leaves by.
 *
 * `toJoin` with no actions emits nothing itself; it exists so the emitter takes
 * that edge's Phi copies where control actually leaves along it.
 */
function withEdgeMarkers(
	part: Region,
	leaving: ReadonlyArray<{ from: BlockAddr; to: BlockAddr }>,
): Region {
	const own = leaving.filter((edge) => part.sourceBlocks.has(edge.from));
	if (own.length === 0) return part;
	if (part.kind === 'tryCatch') {
		return {
			...part,
			body: withEdgeMarkers(part.body, own),
			handler: withEdgeMarkers(part.handler, own),
		};
	}
	if (part.kind === 'tryFinally') {
		return {
			...part,
			body: withEdgeMarkers(part.body, own),
			finalizer: withEdgeMarkers(part.finalizer, own),
		};
	}
	return sequenceRegion([
		part,
		...own.map((edge): Region => ({
			kind: 'deferredExit',
			exit: {
				kind: 'toJoin',
				edge: { from: edge.from, to: edge.to, kind: 'normal' },
				target: edge.to,
				actions: [],
			},
			sourceBlocks: new AddressSet(),
		})),
	]);
}

/**
 * Place a contracted Switch Region in the skeleton.
 *
 * Contraction already put the recovered chain's blocks under its dispatch node,
 * so what remains is the edges that leave it. A recovered chain has one
 * continuation — the join its cases fall out to — and the skeleton either
 * orders that node next or names it with a label, exactly as for an ordinary
 * block's outgoing edge.
 *
 * More than one leaving target is declined: each case would need its own routed
 * completion placed inside the case body, which a contracted node cannot carry.
 */
function routeSwitchExits(
	region: Region,
	next: BlockAddr | undefined,
	nodeFor: (address: BlockAddr) => BlockAddr,
	edgeRegion: (
		from: BlockAddr,
		to: BlockAddr,
		next: BlockAddr | undefined,
	) => Region | null,
	cfg: ImmutableCFG,
): Region | null {
	const { owned, leaving, targets } = leavingEdges(region, nodeFor, cfg);
	if (targets.size === 0) return region;
	if (targets.size === 1) {
		// Every leaving edge reaches the same node, so one transfer after the
		// switch completes all of them.
		const [{ from, to }] = leaving;
		return appendTransfer(region, from, to, next, edgeRegion);
	}
	// Arms that resume at different nodes need their transfer placed at the
	// lexical leaf owning that edge. This is the same exact, transactional
	// descent used for distinct exception-part exits.
	if (region.kind !== 'switch') return null;
	// A recovered comparison chain whose arms are only dispatch aliases already
	// proved their control ownership. Route one representative edge per case as
	// before; the remaining dispatch edges are aliases of those same cases, not
	// independent lexical leaves. Feeding them to the generic descent below
	// leaves the aliases unmatched and rejects an otherwise exact forest.
	if (
		region.cases.every((switchCase) => isEmptyRegion(switchCase.body)) &&
		isEmptyRegion(region.defaultBody)
	) {
		const routeDispatchArm = (
			body: Region,
			source: BlockAddr | undefined,
			target: BlockAddr,
			fallsThrough: boolean,
		): Region | null => {
			if (owned.has(target) || fallsThrough) return body;
			return appendTransfer(
				body,
				source ?? region.header,
				target,
				next,
				edgeRegion,
			);
		};
		const cases: SwitchRegionCase[] = [];
		for (const switchCase of region.cases) {
			const body = routeDispatchArm(
				switchCase.body,
				switchCase.source,
				switchCase.target,
				switchCase.completion === 'fallthrough',
			);
			if (!body) return null;
			cases.push({ ...switchCase, body });
		}
		const defaultBody = routeDispatchArm(
			region.defaultBody,
			region.defaultSource,
			region.defaultTarget,
			false,
		);
		return defaultBody ? { ...region, cases, defaultBody } : null;
	}
	const remaining = [...leaving];
	const routeArm = (
		body: Region,
		source: BlockAddr | undefined,
		target: BlockAddr,
		fallsThrough: boolean,
	): Region | null => {
		const childEdges = remaining.filter((edge) =>
			body.sourceBlocks.has(edge.from)
		);
		for (const edge of childEdges) {
			remaining.splice(remaining.indexOf(edge), 1);
		}
		const direct = fallsThrough
			? undefined
			: remaining.find((edge) =>
				edge.from === (source ?? region.header) && edge.to === target
			);
		if (direct) remaining.splice(remaining.indexOf(direct), 1);
		const routed = routeExceptionPartEdges(
			body,
			childEdges,
			next,
			edgeRegion,
			cfg,
		);
		if (!routed) return null;
		return direct
			? appendTransfer(
				routed,
				direct.from,
				direct.to,
				next,
				edgeRegion,
			)
			: routed;
	};
	const cases: SwitchRegionCase[] = [];
	for (const switchCase of region.cases) {
		const body = routeArm(
			switchCase.body,
			switchCase.source,
			switchCase.target,
			switchCase.completion === 'fallthrough',
		);
		if (!body) return null;
		cases.push({ ...switchCase, body });
	}
	const defaultBody = routeArm(
		region.defaultBody,
		region.defaultSource,
		region.defaultTarget,
		false,
	);
	if (!defaultBody || remaining.length > 0) return null;
	return { ...region, cases, defaultBody };
}

function regionForBlock(
	address: BlockAddr,
	edgeRegion: (
		from: BlockAddr,
		to: BlockAddr,
		next: BlockAddr | undefined,
	) => Region | null,
	next: BlockAddr | undefined,
	nodeFor: (address: BlockAddr) => BlockAddr,
	loopRegions: ReadonlyMap<BlockAddr, LoopRegion>,
	cfg: ImmutableCFG,
): Region | null {
	const block = cfg.blocks.get(address);
	if (!block) return null;
	const basic: Region = {
		kind: 'basic',
		body: [],
		sourceBlocks: new AddressSet([address]),
	};
	switch (block.terminator.kind) {
		case 'goto': {
			const transfer = edgeRegion(
				address,
				block.terminator.target,
				next,
			);
			if (!transfer) return null;
			return isEmptyRegion(transfer)
				? basic
				: sequenceRegion([basic, transfer]);
		}
		case 'if': {
			const fallthrough = block.terminator.fallthrough;
			const taken = block.terminator.taken;
			if (nodeFor(fallthrough) === nodeFor(taken)) return basic;
			if (
				redundantForInGuardLoop(
					address,
					fallthrough,
					taken,
					loopRegions,
					cfg,
				)
			) return basic;
			const consequent = edgeRegion(address, taken, next);
			const alternate = edgeRegion(address, fallthrough, next);
			if (!consequent || !alternate) return null;
			return {
				kind: 'if',
				header: address,
				test: t.cloneNode(block.terminator.test, true),
				consequent,
				alternate,
				join: next ?? address,
				sourceBlocks: new AddressSet([address]),
			};
		}
		case 'return':
		case 'throw':
		case 'unreachable':
			return basic;
		case 'switch':
			return switchRegionForBlock(
				address,
				block.terminator,
				edgeRegion,
				next,
			);
	}
}

/**
 * Own a dispatch terminator as one skeleton node. Every case transfers control
 * explicitly: a case that would fall through to the next skeleton node breaks
 * out of the switch instead, and any other case carries the same deferred edge
 * action and labelled sequence exit an ordinary branch would use.
 */
function switchRegionForBlock(
	address: BlockAddr,
	terminator: Extract<Terminator, { kind: 'switch' }>,
	edgeRegion: (
		from: BlockAddr,
		to: BlockAddr,
		next: BlockAddr | undefined,
	) => Region | null,
	next: BlockAddr | undefined,
): Region | null {
	const caseBody = (target: BlockAddr) => {
		const transfer = edgeRegion(address, target, next);
		if (!transfer) return null;
		return isEmptyRegion(transfer)
			? { body: transfer, completion: 'break' as const }
			: { body: transfer, completion: undefined };
	};
	const cases: SwitchRegionCase[] = [];
	const caseByTarget = new AddressMap<SwitchRegionCase>();
	for (const edge of terminator.cases) {
		if (edge.target === terminator.defaultTarget) continue;
		const test = edge.test ? t.cloneNode(edge.test, true) : null;
		const existing = caseByTarget.get(edge.target);
		if (existing) {
			if (test) (existing.aliases ??= []).push(test);
			continue;
		}
		const structured = caseBody(edge.target);
		if (!structured) return null;
		const switchCase: SwitchRegionCase = {
			test,
			target: edge.target,
			source: address,
			body: structured.body,
			completion: structured.completion,
		};
		cases.push(switchCase);
		caseByTarget.set(edge.target, switchCase);
	}
	const defaultBody = caseBody(terminator.defaultTarget);
	if (!defaultBody) return null;
	return {
		kind: 'switch',
		header: address,
		discriminant: t.cloneNode(terminator.discriminant, true),
		cases,
		defaultTarget: terminator.defaultTarget,
		defaultSource: address,
		defaultBody: defaultBody.body,
		sourceBlocks: new AddressSet([address]),
	};
}

function redundantForInGuardLoop(
	guard: BlockAddr,
	fallthrough: BlockAddr,
	taken: BlockAddr,
	loopRegions: ReadonlyMap<BlockAddr, LoopRegion>,
	cfg: ImmutableCFG,
): boolean {
	for (const [header, loop] of loopRegions) {
		if (
			loop.syntax?.kind !== 'forIn' ||
			loop.syntax.preheader?.block !== guard
		) continue;
		const fallthroughEnters = fallthrough === header;
		const takenEnters = taken === header;
		if (fallthroughEnters === takenEnters) continue;
		const bypass = fallthroughEnters ? taken : fallthrough;
		if (!loop.exits.some((exit) => exit.to === bypass)) continue;
		// A bypass Phi is real value semantics and requires the explicit optional-
		// loop Region used by the specialized path. The generic forest may erase
		// only the control-only GetPNameList guard.
		const bypassHasPhi = cfg.blocks.get(bypass)?.ssaInstructions.some(
			(instruction) =>
				instruction.instruction === 'Phi' &&
				instruction.sources.has(guard),
		);
		if (!bypassHasPhi) return true;
	}
	return false;
}

/**
 * Leave a composed scope for its enclosing join: the edge action is emitted on
 * the original edge, then control breaks out of the scope's labelled sequence.
 */
export function boundedScopeExit(
	from: BlockAddr,
	to: BlockAddr,
	label: string,
): Region {
	return forwardJump(from, to, to, label);
}

function forwardJump(
	from: BlockAddr,
	edgeTarget: BlockAddr,
	target: BlockAddr,
	label: string,
): Region {
	return sequenceRegion([
		{
			kind: 'deferredExit',
			exit: {
				kind: 'toJoin',
				edge: { from, to: edgeTarget, kind: 'normal' },
				target: edgeTarget,
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

function routeLoopExits(
	loop: LoopRegion,
	next: BlockAddr | undefined,
	nodeFor: (address: BlockAddr) => BlockAddr,
	labels: ReadonlyMap<BlockAddr, string>,
	leavesScope: (to: BlockAddr) => boolean,
	scope: ControlForestScope | undefined,
): LoopRegion | null {
	// An exit leaving a bounded scope is completed by the caller. Its ordered
	// trailer would have to execute inside this loop, so a trailer or an already
	// routed sequence exit is left to the enclosing specialized builder.
	const escaping = loop.exits.filter((exit) =>
		exit.kind !== 'return' && exit.kind !== 'throw' &&
		leavesScope(exit.to)
	);
	if (
		escaping.some((exit) =>
			!scope || exit.trailer != null || exit.sequenceExit != null
		)
	) return null;
	const completions = new Map<LoopRegionExit, Region>();
	for (const exit of escaping) {
		const completion = scope?.completion(exit.from, exit.to);
		if (!completion) return null;
		completions.set(exit, completion);
	}

	// A return/throw exit is a terminal reference owned by the loop itself. Its
	// block is not part of the skeleton, so it needs neither a completion nor a
	// labelled sequence exit.
	// An exit whose target the loop Region owns — its own ordered trailer, for
	// instance — stays inside the contracted node and needs no routing, as does a
	// return/throw exit, whose terminal block the loop references itself.
	const routed = (exit: LoopRegionExit) =>
		!completions.has(exit) && exit.kind !== 'return' &&
		exit.kind !== 'throw' && nodeFor(exit.to) !== loop.header;
	const exits = loop.exits.map((exit) => {
		if (completions.has(exit)) return exit;
		const target = nodeFor(exit.to);
		if (target !== next) {
			const label = labels.get(target);
			if (label) return { ...exit, sequenceExit: { target, label } };
		}
		// An exit that resumes past the loop through an ordered trailer already
		// carries the block it leaves at, but `structureExits` has no labels to
		// give it. The skeleton does: without one the exit lowers to a bare
		// `break` and lands wherever the loop's own continuation was ordered,
		// which is the trailer's own successor rather than this target.
		const pending = exit.sequenceExit;
		if (pending?.label != null || pending == null) return exit;
		const pendingLabel = nodeFor(pending.target) === pending.target
			? labels.get(pending.target)
			: undefined;
		return pendingLabel
			? {
				...exit,
				sequenceExit: { target: pending.target, label: pendingLabel },
			}
			: exit;
	});
	if (
		exits.some((exit) =>
			routed(exit) && nodeFor(exit.to) !== next &&
			!labels.has(nodeFor(exit.to))
		)
	) return null;
	return {
		...loop,
		exits,
		body: rewriteLoopExitRegions(loop.body, exits, completions),
	};
}

function rewriteLoopExitRegions(
	region: Region,
	exits: readonly LoopRegionExit[],
	completions: ReadonlyMap<LoopRegionExit, Region> = new Map(),
): Region {
	const updatedExit = (exit: LoopRegionExit | undefined) =>
		exit == null
			? undefined
			: exits.find((candidate) =>
				candidate.from === exit.from && candidate.to === exit.to
			) ?? exit;
	const recurse = (child: Region) =>
		rewriteLoopExitRegions(child, exits, completions);
	if (
		(region.kind === 'break' || region.kind === 'continue' ||
			region.kind === 'labelBreak' ||
			region.kind === 'labelContinue') && region.exit
	) {
		const exit = updatedExit(region.exit);
		const completion = exit && completions.get(exit);
		if (completion) return completion;
	}
	if (
		(region.kind === 'break' || region.kind === 'labelBreak') && region.exit
	) {
		const exit = updatedExit(region.exit);
		if (exit?.sequenceExit?.label) {
			return {
				kind: 'labelBreak',
				label: exit.sequenceExit.label,
				target: exit.sequenceExit.target,
				exit,
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		}
		return { ...region, exit };
	}
	switch (region.kind) {
		case 'sequence':
			return {
				...region,
				regions: region.regions.map((child) => recurse(child)),
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		case 'if':
			return {
				...region,
				consequent: recurse(region.consequent),
				alternate: recurse(region.alternate),
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		case 'switch':
			return {
				...region,
				cases: region.cases.map((switchCase) => ({
					...switchCase,
					body: recurse(switchCase.body),
				})),
				defaultBody: recurse(region.defaultBody),
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		case 'tryCatch':
			return {
				...region,
				body: recurse(region.body),
				handler: recurse(region.handler),
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		case 'tryFinally':
			return {
				...region,
				body: recurse(region.body),
				finalizer: recurse(region.finalizer),
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		case 'loop':
			return region;
		default:
			return region;
	}
}

function formatAddress(address: BlockAddr): string {
	return address.toString(16);
}
