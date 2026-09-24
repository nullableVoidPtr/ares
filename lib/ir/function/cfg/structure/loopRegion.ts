import * as t from '@babel/types';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../../utils/set.ts';
import { invertTest } from '../../../ast/expression.ts';
import type { CFGAnalyses, NaturalLoop } from '../algorithms/mod.ts';
import {
	type CFGDescriptors,
	finalizerCopyBlocks,
} from '../descriptors/mod.ts';
import type { ExceptionDescriptor } from '../descriptors/exceptions.ts';
import { recordCFGCompatibilityAttempt } from '../compatibility.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import {
	blockNeedsBranchRegion,
	isEmptyRegion,
	type LoopRegionExit,
	nestedSubsumedLoopHandlers,
	type Region,
	regionDuplicateOwnership,
	regionStructuredBlocks,
	visitRegions,
} from '../regions/region.ts';
import {
	type RegionAt,
	structureStraightLineSequenceFrom,
} from './sequence.ts';
import { tryStructureBoundedScopeForest } from './loopForest.ts';
import {
	iteratorCleanupHandlersForLoop,
	recoverIteratorLoopSyntax,
} from './iteratorLoop.ts';
import { tryStructureIfRegion } from './ifRegion.ts';
import {
	handlerOwnedBlocks,
	tryStructureSwitchRegion,
} from './switchRegion.ts';
import {
	contractedExceptionBlocks,
	openableProtectedEntries,
	restoreStructuredHandlers,
	tryStructureExceptionRegion,
} from './exceptionRegion.ts';

export function tryStructureLoopRegion(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
	options: {
		allowHierarchicalExits?: boolean;
		allowMixedAbruptExits?: boolean;
		/**
		 * The handler ledger the enclosing composition threads.
		 *
		 * Passing it lets a discarded speculative body give its claims back. The
		 * ledger is monotonic on purpose -- a handler claimed once is never
		 * offered again, which is what keeps a protected range from being
		 * emitted twice -- so an attempt that is thrown away would otherwise
		 * leave the handler owned by nothing.
		 */
		structuredHandlers?: AddressSet<BlockAddr>;
	} = {},
): Region | null {
	const discoveredLoop = analyses.naturalLoops.loopByHeader.get(cfg.entry);
	if (!discoveredLoop) return null;
	const loop = withExceptionOwnedBlocks(
		cfg,
		discoveredLoop,
		analyses,
		descriptors,
	);
	const ledger = options.structuredHandlers;

	const syntax = recoverIteratorLoopSyntax(loop, cfg);
	const classifiedExits = classifyLoopExits(loop, analyses);
	const structureExits = (trailerRegionAt?: RegionAt) => {
		const structured = structureLoopExitTrailers(
			cfg,
			analyses,
			loop,
			classifiedExits,
			options.allowHierarchicalExits === true,
			syntax != null,
			trailerRegionAt,
		);
		const completions = classifyAbruptLoopCompletions(
			structured,
			loop,
			cfg,
			descriptors,
			options.allowMixedAbruptExits === true,
		);
		return {
			exitStructure: structured,
			exits: completions,
			body: structureLoopBody(
				cfg,
				loop,
				completions,
				syntax != null,
				analyses,
				descriptors,
				regionAt,
				ledger,
			),
		};
	};
	const beforeExits = ledger ? new AddressSet(ledger) : undefined;
	let structured = structureExits(regionAt);
	// A recursively structured exit trailer costs the header/latch shape, which
	// is the only representation that places both header-edge Phi actions. Keep
	// the simpler trailers when the body would otherwise leave that branch
	// unowned.
	if (
		regionAt &&
		structured.exitStructure.exits.some((exit) => exit.trailer != null) &&
		!structured.body.headerLatchBranch &&
		loopHeaderBranchNeedsBody(cfg, loop) &&
		!regionOwnsBranchHeader(structured.body.body, loop.header)
	) {
		const afterRecursive = ledger ? new AddressSet(ledger) : undefined;
		if (ledger && beforeExits) {
			restoreStructuredHandlers(ledger, beforeExits);
		}
		const simple = structureExits(undefined);
		if (
			simple.body.headerLatchBranch ||
			regionOwnsBranchHeader(simple.body.body, loop.header)
		) structured = simple;
		else if (ledger && beforeExits && afterRecursive) {
			// The recursive attempt is the one being kept, so its claims are the
			// ones that must stand.
			restoreStructuredHandlers(ledger, beforeExits);
			for (const handler of afterRecursive) ledger.add(handler);
		}
	}
	const { exitStructure, exits } = structured;
	const bodyStructure = structured.body;
	const bodyOwnedExits = exits.filter((exit) =>
		exit.trailer?.sourceBlocks.isSubsetOf(
			bodyStructure.body.sourceBlocks,
		) === true
	);
	const bodyOwnedTrailerBlocks = new AddressSet<BlockAddr>(
		bodyOwnedExits.flatMap((exit) => [...exit.trailer!.sourceBlocks]),
	);
	const representedExits = representedExternalLoopExits(
		bodyStructure.body,
		loop,
		exits,
	);
	const regionExits = [
		...exits.filter((exit) =>
			!exit.trailer ||
			!exit.trailer.sourceBlocks.isSubsetOf(bodyOwnedTrailerBlocks)
		),
		...representedExits,
	];
	attachStructuredLoopExitActions(bodyStructure.body, regionExits);
	const needsLabel = loop.children.length > 0 ||
		regionExits.some((exit) => exit.label != null);
	const continuation = exitStructure.continuation ??
		directBreakContinuation(
			regionExits.filter((exit) =>
				exit.kind === 'break' || exit.kind === 'labelledBreak'
			),
		);
	// Handler blocks this Region owns that are not loop-body blocks: nothing
	// branches to a handler, yet the Loop Region is the only owner of the
	// cleanup pad its syntax represents and of the handler of a try its body
	// structures. They are sources of the Region without being loop blocks.
	const bodyScope = withNestedHandlerBlocks(
		cfg,
		loop,
		analyses,
		descriptors,
		loop.body,
	);
	const ownedHandlers = new AddressSet([
		...iteratorCleanupHandlersForLoop(loop, cfg, descriptors),
		...[...bodyStructure.body.sourceBlocks].filter((block) =>
			!loop.body.has(block) && !bodyOwnedTrailerBlocks.has(block) &&
			bodyScope.has(block)
		),
	]);
	return {
		kind: 'loop',
		id: loop.id,
		label: needsLabel ? loopLabel(loop.id) : undefined,
		syntax,
		header: loop.header,
		latches: loop.latches,
		loopBlocks: loop.body.union(bodyOwnedTrailerBlocks),
		continuation:
			regionExits.some((exit) =>
					exit.kind === 'break' || exit.kind === 'labelledBreak'
				)
				? continuation
				: undefined,
		exits: regionExits,
		bodyOwnedExits: bodyOwnedExits.length === 0
			? undefined
			: bodyOwnedExits,
		children: loop.children,
		headerLatchBranch: bodyStructure.headerLatchBranch,
		bodyOwnsHeader: bodyStructure.ownsHeader,
		suppressedBodyBlocks: bodyStructure.suppressed,
		subsumedHandlers: ownedHandlers.size === 0 ? undefined : ownedHandlers,
		body: bodyStructure.body,
		sourceBlocks: new AddressSet([
			...loop.body,
			...exitStructure.trailerBlocks,
			...ownedHandlers,
		]),
	};
}

interface StructuredLoopBody {
	body: Region;
	headerLatchBranch?: {
		bodyEntry: BlockAddr;
		latch: BlockAddr;
	};
	/** The body starts at the header and emits the header's statements. */
	ownsHeader?: boolean;
	/** Body blocks a finalizer the body represents emits instead. */
	suppressed?: AddressSet<BlockAddr>;
}

interface StructuredLoopExits {
	exits: LoopRegionExit[];
	continuation?: BlockAddr;
	trailerBlocks: AddressSet<BlockAddr>;
}

/**
 * Recover the linear blocks that execute only for one loop exit before all
 * ordinary exits reconverge. These blocks cannot be emitted after the loop:
 * doing so both changes their ordering and loses the Phi copies on their
 * incoming/outgoing edges.
 */
function structureLoopExitTrailers(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	allowHierarchicalExits: boolean,
	allowIteratorCloseRegions: boolean,
	regionAt?: RegionAt,
): StructuredLoopExits {
	const unchanged = (continuation?: BlockAddr): StructuredLoopExits => ({
		exits,
		continuation,
		trailerBlocks: new AddressSet(),
	});
	if (exits.length === 0) {
		return unchanged();
	}
	if (
		cfg.hasExceptionRegions && !allowIteratorCloseRegions &&
		!allowHierarchicalExits
	) {
		return unchanged(directBreakContinuation(exits));
	}
	const breakExits = exits.filter((exit) => exit.kind === 'break');
	if (breakExits.length === 0) return unchanged();

	let continuation: BlockAddr | null = breakExits[0]!.to;
	for (const exit of breakExits.slice(1)) {
		continuation = analyses.postdominators.nearestCommonPostdominator(
			continuation,
			exit.to,
		);
		if (continuation == null) return unchanged();
	}
	if (continuation == null || loop.body.has(continuation)) return unchanged();
	const owned = new AddressSet<BlockAddr>();
	const structured: LoopRegionExit[] = [];
	for (const exit of exits) {
		if (exit.kind !== 'break') {
			structured.push(exit);
			continue;
		}
		let trailer = linearExitTrailer(
			cfg,
			loop,
			exit,
			continuation,
			owned,
		);
		if (trailer === false && regionAt) {
			trailer = recursiveExitTrailer(
				cfg,
				loop,
				exit,
				continuation,
				owned,
				regionAt,
			);
		}
		if (trailer === false) {
			if (!allowHierarchicalExits || breakExits.length !== exits.length) {
				return unchanged();
			}
			return structureHierarchicalLoopExits(
				cfg,
				analyses,
				loop,
				breakExits,
				continuation,
			) ?? unchanged();
		}
		structured.push({
			...exit,
			trailer: trailer ?? undefined,
			continuation,
		});
	}
	return { exits: structured, continuation, trailerBlocks: owned };
}

/**
 * Structure the common two-level exit shape where most breaks reach an
 * ordinary continuation, while a less frequent exit runs a private trailer
 * and skips that continuation to a later postdominator.
 */
function structureHierarchicalLoopExits(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	outerContinuation: BlockAddr,
): StructuredLoopExits | null {
	const counts = new Map<BlockAddr, number>();
	for (const exit of exits) {
		counts.set(exit.to, (counts.get(exit.to) ?? 0) + 1);
	}
	const ranked = [...counts.entries()].toSorted((left, right) =>
		right[1] - left[1] || left[0] - right[0]
	);
	const nonOuterTargets = ranked.filter(([target]) =>
		target !== outerContinuation
	);
	const singleNonOuterTarget = nonOuterTargets.length === 1
		? nonOuterTargets[0]
		: undefined;
	const externallyJoinedTargets = nonOuterTargets.filter(([target]) =>
		[...(cfg.normalPredecessors.get(target) ?? [])].some((predecessor) =>
			!loop.body.has(predecessor)
		)
	);
	const [primary, primaryCount] = externallyJoinedTargets.length === 1
		? externallyJoinedTargets[0]!
		: singleNonOuterTarget ?? ranked[0] ?? [];
	const singleNonOuterPrimary = singleNonOuterTarget?.[0] === primary;
	if (
		primary == null || primary === outerContinuation ||
		(primaryCount < 2 && externallyJoinedTargets.length !== 1 &&
			!singleNonOuterPrimary) ||
		(externallyJoinedTargets.length !== 1 && !singleNonOuterPrimary &&
			primaryCount === ranked[1]?.[1]) ||
		loop.body.has(primary) ||
		analyses.postdominators.nearestCommonPostdominator(
				primary,
				outerContinuation,
			) !== outerContinuation
	) return null;

	const owned = new AddressSet<BlockAddr>();
	const structured: LoopRegionExit[] = [];
	for (const exit of exits) {
		if (exit.to === primary) {
			structured.push({ ...exit, continuation: primary });
			continue;
		}
		const trailer = linearExitTrailer(
			cfg,
			loop,
			exit,
			outerContinuation,
			owned,
		);
		if (trailer === false) return null;
		structured.push({
			...exit,
			trailer: trailer ?? undefined,
			continuation: outerContinuation,
			sequenceExit: { target: outerContinuation },
		});
	}
	return { exits: structured, continuation: primary, trailerBlocks: owned };
}

function directBreakContinuation(
	exits: readonly LoopRegionExit[],
): BlockAddr | undefined {
	if (exits.length === 0 || exits.some((exit) => exit.kind !== 'break')) {
		return undefined;
	}
	const continuation = exits[0]!.to;
	return exits.every((exit) => exit.to === continuation)
		? continuation
		: undefined;
}

function linearExitTrailer(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exit: LoopRegionExit,
	continuation: BlockAddr,
	owned: AddressSet<BlockAddr>,
): Region | null | false {
	if (exit.to === continuation) return null;
	const blocks: BlockAddr[] = [];
	let previous = exit.from;
	let current = exit.to;
	const seen = new AddressSet<BlockAddr>();
	while (current !== continuation) {
		if (seen.has(current) || loop.body.has(current) || owned.has(current)) {
			return false;
		}
		seen.add(current);
		const block = cfg.blocks.get(current);
		if (!block || block.terminator.kind !== 'goto') return false;
		const predecessors = cfg.normalPredecessors.get(current) ??
			new AddressSet<BlockAddr>();
		if (
			predecessors.size !== 1 ||
			!predecessors.has(previous)
		) return false;
		blocks.push(current);
		previous = current;
		current = block.terminator.target;
	}
	if (blocks.length === 0) return null;
	for (const address of blocks) owned.add(address);
	const regions: Region[] = blocks.map((address) => ({
		kind: 'basic',
		body: [],
		sourceBlocks: new AddressSet([address]),
	}));
	return regions.length === 1 ? regions[0]! : {
		kind: 'sequence',
		regions,
		sourceBlocks: new AddressSet(blocks),
	};
}

/**
 * Recover a private acyclic exit trailer whose branches reconverge before the
 * loop's common continuation. The trailer is bounded by graph ownership first;
 * recursive Region construction is accepted only when it represents that
 * exact set without leaving a conditional in a Basic Region.
 */
function recursiveExitTrailer(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exit: LoopRegionExit,
	continuation: BlockAddr,
	owned: AddressSet<BlockAddr>,
	regionAt: RegionAt,
): Region | false {
	if (exit.to === continuation) return false;
	const blocks = new AddressSet<BlockAddr>();
	const pending = [exit.to];
	while (pending.length > 0) {
		const current = pending.pop()!;
		if (current === continuation || blocks.has(current)) continue;
		if (
			!cfg.blocks.has(current) || loop.body.has(current) ||
			owned.has(current)
		) {
			return false;
		}
		blocks.add(current);
		for (const successor of cfg.normalSuccessors.get(current) ?? []) {
			if (successor !== continuation) pending.push(successor);
		}
	}
	if (blocks.size === 0) return false;
	for (const address of blocks) {
		for (const predecessor of cfg.normalPredecessors.get(address) ?? []) {
			if (blocks.has(predecessor)) continue;
			if (address === exit.to && predecessor === exit.from) continue;
			return false;
		}
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (!blocks.has(successor) && successor !== continuation) {
				return false;
			}
		}
	}
	const trailer = regionAt(exit.to, blocks);
	if (
		!trailer || trailer.kind === 'fallback' ||
		!trailer.sourceBlocks.isSubsetOf(blocks) ||
		!blocks.isSubsetOf(regionStructuredBlocks(trailer)) ||
		containsUnstructuredLoopBodyBranch(trailer, cfg)
	) return false;
	for (const address of blocks) owned.add(address);
	return trailer;
}

function classifyLoopExits(
	loop: NaturalLoop,
	analyses: CFGAnalyses,
): LoopRegionExit[] {
	return loop.exits.map((edge) => {
		for (const ancestorId of ancestorLoopIds(loop, analyses)) {
			const ancestor = analyses.naturalLoops.loops[ancestorId];
			if (edge.to === ancestor.header) {
				return {
					from: edge.from,
					to: edge.to,
					kind: 'labelledContinue',
					targetLoop: ancestorId,
					label: loopLabel(ancestorId),
				};
			}
			if (!ancestor.body.has(edge.to)) {
				return {
					from: edge.from,
					to: edge.to,
					kind: 'labelledBreak',
					targetLoop: ancestorId,
					label: loopLabel(ancestorId),
				};
			}
		}

		return {
			from: edge.from,
			to: edge.to,
			kind: 'break',
		};
	});
}

function classifyAbruptLoopCompletions(
	structure: StructuredLoopExits,
	loop: NaturalLoop,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	allowMixedAbruptExits: boolean,
): LoopRegionExit[] {
	const allTerminal = structure.exits.every((exit) =>
		directTerminalExitKind(exit.to, cfg) != null
	);
	const terminalTargets = new Set(
		structure.exits
			.filter((exit) => directTerminalExitKind(exit.to, cfg) != null)
			.map((exit) => exit.to),
	);
	// Lowering a terminal exit as an ordinary `break` places its block after the
	// loop, where the remaining break's own completion reaches it as well — a
	// guarded `throw` then runs on every ordinary loop completion. Terminalize
	// it instead when the rest of the loop leaves at exactly one continuation,
	// so the two exits stay distinguishable.
	//
	// A labelled exit or a protected body keeps the old model: their suffix is a
	// real enclosing Region that this classification cannot see.
	const nonTerminalTargets = new Set(
		structure.exits
			.filter((exit) => directTerminalExitKind(exit.to, cfg) == null)
			.map((exit) => exit.to),
	);
	const divergentBreaks = (
		!cfg.hasExceptionRegions ||
		structure.exits.every((exit) =>
			exceptionHandlersEqualAcrossEdge(
				exit.from,
				exit.to,
				descriptors,
			)
		)
	) &&
		nonTerminalTargets.size === 1 &&
		!structure.exits.some((exit) =>
			exit.kind === 'labelledBreak' || exit.kind === 'labelledContinue'
		);
	return structure.exits.map((exit) => {
		const terminalKind = directTerminalExitKind(exit.to, cfg);
		if (!terminalKind) return exit;
		// One terminal shared by the entry guard and every loop exit is the
		// loop's continuation, not a body-local abrupt completion. Keeping it as
		// a break lets the enclosing Region emit that terminal exactly once.
		if (
			allTerminal && terminalTargets.size === 1 &&
			[...(cfg.normalPredecessors.get(exit.to) ?? [])].some(
				(predecessor) => !loop.body.has(predecessor),
			)
		) return exit;
		// A mixed body-level abrupt exit and ordinary break needs an enclosing
		// ordered suffix Region. Until that boundary is available, retain the old
		// continuation model. Header exits are safe because their completion occurs
		// before the loop body, and all-terminal loops have no shared suffix.
		if (
			!allowMixedAbruptExits && !allTerminal && !divergentBreaks &&
			exit.from !== loop.header
		) return exit;
		// Multiple exits may intentionally converge on one terminal continuation,
		// with private ordered trailers on the way there. Keep that continuation
		// model: terminalizing only one incoming edge would bypass its siblings and
		// lose the common post-loop emission.
		if (
			structure.exits.length > 1 &&
			structure.continuation === exit.to
		) return exit;
		return { ...exit, kind: terminalKind };
	});
}

function exceptionHandlersEqualAcrossEdge(
	from: BlockAddr,
	to: BlockAddr,
	descriptors: CFGDescriptors,
): boolean {
	const handlersAt = (block: BlockAddr) =>
		new AddressSet<BlockAddr>(
			descriptors.exceptions.handlers
				.filter((descriptor) => descriptor.protectedBlocks.has(block))
				.map((descriptor) => descriptor.handler),
		);
	const fromHandlers = handlersAt(from);
	const toHandlers = handlersAt(to);
	return fromHandlers.equals(toHandlers);
}

function directTerminalExitKind(
	target: BlockAddr,
	cfg: ImmutableCFG,
): 'return' | 'throw' | null {
	const terminator = cfg.blocks.get(target)?.terminator;
	if (terminator?.kind === 'throw') return 'throw';
	if (terminator?.kind === 'return' && !cfg.isScript) return 'return';
	return null;
}

function ancestorLoopIds(loop: NaturalLoop, analyses: CFGAnalyses): number[] {
	const ids: number[] = [];
	let parent = loop.parent;
	while (parent != null) {
		ids.push(parent);
		parent = analyses.naturalLoops.loops[parent].parent;
	}
	return ids;
}

function loopLabel(id: number) {
	return `loop_${id}`;
}

/**
 * Structure the loop body, then require it to represent every natural-loop
 * block. A body that stops at an unrecognized conditional silently drops the
 * whole subgraph below it, so an incomplete result is recomposed exactly
 * through the loop-local control skeleton before it is accepted.
 */
function structureLoopBody(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	hasIteratorSyntax: boolean,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
	ledger?: AddressSet<BlockAddr>,
): StructuredLoopBody {
	const protectedHeader = speculate(
		ledger,
		() =>
			structureProtectedHeaderLoopBody(
				cfg,
				loop,
				analyses,
				descriptors,
				regionAt,
			),
		(value) => value != null,
	);
	if (protectedHeader) return protectedHeader;
	const candidate = structureLoopBodyCandidate(
		cfg,
		loop,
		exits,
		analyses,
		descriptors,
		regionAt,
		ledger,
	);
	if (candidate.headerLatchBranch) return candidate;
	const represented = regionStructuredBlocks(candidate.body)
		.union(new AddressSet([loop.header]));
	// An incomplete body drops the blocks below an unrecognized branch; a body
	// that claims a block twice keeps its statements only at the first claimant.
	// Both are repaired by owning the body exactly once.
	if (
		loop.body.isSubsetOf(represented) &&
		regionDuplicateOwnership(candidate.body, cfg).length === 0
	) return candidate;
	const residual = speculate(
		ledger,
		() =>
			structureLoopBodyResidual(
				cfg,
				loop,
				exits,
				hasIteratorSyntax,
				analyses,
				descriptors,
				regionAt,
			),
		(value) => value != null,
	);
	return residual ? { body: residual } : candidate;
}

/**
 * Build something speculatively without leaving claims behind.
 *
 * The handler ledger is monotonic: a handler claimed by one Region is never
 * offered to another, which is what stops a protected range being emitted
 * twice. An attempt whose result is thrown away must therefore hand its claims
 * back, or the builder that would have owned the handler never sees it.
 */
function speculate<T>(
	ledger: AddressSet<BlockAddr> | undefined,
	build: () => T,
	keep: (value: T) => boolean,
): T {
	if (!ledger) return build();
	const snapshot = new AddressSet(ledger);
	const value = build();
	if (!keep(value)) restoreStructuredHandlers(ledger, snapshot);
	return value;
}

/** A loop header whose successors all stay inside the body it heads. */
function loopHeaderBranchNeedsBody(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
): boolean {
	const terminator = cfg.blocks.get(loop.header)?.terminator;
	if (terminator?.kind === 'switch') return true;
	if (terminator?.kind !== 'if') return false;
	const { fallthrough, taken } = terminator;
	return fallthrough !== taken && fallthrough !== loop.header &&
		taken !== loop.header && loop.body.has(fallthrough) &&
		loop.body.has(taken);
}

function regionOwnsBranchHeader(region: Region, header: BlockAddr): boolean {
	if (
		(region.kind === 'if' || region.kind === 'switch') &&
		region.header === header
	) return true;
	return loopBodyChildRegions(region).some((child) =>
		regionOwnsBranchHeader(child, header)
	);
}

/**
 * Compose the body of a loop whose protected range opens at its own header.
 *
 * Hermes emits `while (_) try { ... } catch (e) { ... } finally { ... }` with
 * the protected range covering the body and the header among its entries --
 * and the header is the range's *only* openable entry, because every other one
 * is reached from inside. Contracting the loop first claims that header, so the
 * `try` can never open and the handler is left unstructured; opening the `try`
 * first cannot work either, because the body's back edge re-enters it.
 *
 * Composing the body from the header resolves both: the `try` owns the header's
 * statements, and the back edge stays the loop's own `continue`, which the
 * emitter's loop rewrite already places. The loop then must not emit the header
 * itself, which `ownsHeader` says.
 */
function structureProtectedHeaderLoopBody(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
): StructuredLoopBody | null {
	if (!regionAt) return null;
	const descriptor = protectedHeaderDescriptor(
		cfg,
		loop,
		analyses,
		descriptors,
	);
	if (!descriptor) return null;
	const scope = new AddressSet<BlockAddr>([loop.header, ...loop.body]);
	for (const block of descriptor.protectedBlocks) scope.add(block);
	scope.add(descriptor.handler);
	if (descriptor.canonicalFinallyAddress != null) {
		scope.add(descriptor.canonicalFinallyAddress);
	}
	for (const handler of descriptors.exceptions.handlers) {
		if (!handler.protectedBlocks.has(loop.header)) continue;
		for (const block of handler.protectedBlocks) scope.add(block);
		scope.add(handler.handler);
		for (const copy of handler.finallyCopies) {
			scope.add(copy.copyRoot);
			for (const block of copy.copyBlocks ?? []) scope.add(block);
		}
		if (handler.finallyBodyBlocks) {
			for (const block of handler.finallyBodyBlocks) scope.add(block);
		}
	}
	const protectedRegion = tryStructureExceptionRegion(
		cfgEnteringAt(cfg, loop.header),
		descriptors,
		(cursor, childAllowed) =>
			cursor === loop.header
				? null
				: regionAt(cursor, (childAllowed ?? scope).intersection(scope)),
		scope,
		new AddressSet<BlockAddr>(),
		analyses,
	);
	if (!protectedRegion) return null;
	if (!regionStructuredBlocks(protectedRegion).has(loop.header)) return null;
	// Every block the loop runs has to be owned, except the finalizer copies:
	// their statements are suppressed on purpose, because the `finally` emits
	// them once. What is left over is the dispatch tail Hermes emits after the
	// copy chain, ending at the latch: the `try` is only the body's first
	// statement, and the remainder follows it in the same body.
	const copies = finalizerCopyBlocks(descriptors.exceptions.handlers);
	const claimed = regionStructuredBlocks(protectedRegion);
	const remaining = new AddressSet<BlockAddr>(
		[...loop.body].filter((block) =>
			!claimed.has(block) && !copies.has(block)
		),
	);
	let body = protectedRegion;
	if (remaining.size > 0) {
		// The tail is entered where control arrives from outside it -- from the
		// suppressed copy chain. More than one such block is a shape this
		// composition cannot order.
		const entries = [...remaining].filter((block) =>
			[...cfg.normalPredecessors.get(block) ?? []].some((predecessor) =>
				!remaining.has(predecessor)
			)
		);
		if (entries.length !== 1) return null;
		const tail = regionAt(entries[0]!, scope);
		if (!tail) return null;
		body = sequenceLoopRegions([protectedRegion, tail]);
	}
	const covered = regionStructuredBlocks(body);
	const missing = [...loop.body].filter((block) =>
		!covered.has(block) && !copies.has(block)
	);
	if (missing.length > 0) return null;
	return {
		body,
		ownsHeader: true,
		suppressed: loop.body.intersection(copies),
	};
}

/**
 * A descriptor whose range the loop cannot contract around: its only openable
 * entry is the loop's own header, and it protects nothing outside the loop.
 */
function protectedHeaderDescriptor(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
): ExceptionDescriptor | undefined {
	return descriptors.exceptions.handlers.find((descriptor) => {
		const openable = openableProtectedEntries(cfg, descriptor);
		// The header has to be a place the range can open, and every other such
		// place must sit inside the loop -- otherwise the range is not this
		// loop's to own and some enclosing scope can hold it.
		if (!openable.has(loop.header)) return false;
		for (const entry of openable) {
			if (!analyses.dominators.dominates(loop.header, entry)) {
				return false;
			}
		}
		// Dominance, not the natural-loop body: a `return` inside the loop is
		// lexically in it while reaching no latch, so it is not a body block --
		// and Hermes protects it all the same. A landing pad is reached only by
		// an exceptional edge, which dominance does not describe.
		for (const block of descriptor.protectedBlocks) {
			if (analyses.dominators.dominates(loop.header, block)) continue;
			if (descriptors.exceptions.handlerByAddress.has(block)) continue;
			return false;
		}
		return true;
	});
}

function structureLoopBodyCandidate(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
	ledger?: AddressSet<BlockAddr>,
): StructuredLoopBody {
	const bodyWithoutHeader = withNestedHandlerBlocks(
		cfg,
		loop,
		analyses,
		descriptors,
		loop.body,
	);
	bodyWithoutHeader.delete(loop.header);
	const headerLatchBody = speculate(
		ledger,
		() =>
			structureHeaderToLatchLoopBody(
				cfg,
				loop,
				exits,
				bodyWithoutHeader,
				analyses,
				descriptors,
				regionAt,
			),
		(value) => value != null,
	);
	if (headerLatchBody) return headerLatchBody;
	const headerSwitch = loopHeaderSwitchRegion(
		cfg,
		loop,
		analyses,
		descriptors,
		regionAt,
	);
	if (headerSwitch?.join != null && loop.body.has(headerSwitch.join)) {
		const tailAllowed = bodyWithoutHeader.difference(
			headerSwitch.sourceBlocks,
		);
		const tail = speculate(
			ledger,
			() =>
				structureLoopBodySequence(
					cfg,
					loop,
					exits,
					headerSwitch.join!,
					tailAllowed,
					new Map(),
					analyses,
					descriptors,
					regionAt,
					ledger,
				),
			(value) =>
				value != null &&
				!value.sourceBlocks.isSubsetOf(headerSwitch.sourceBlocks),
		);
		if (!tail || tail.sourceBlocks.isSubsetOf(headerSwitch.sourceBlocks)) {
			return { body: headerSwitch };
		}
		return {
			body: {
				kind: 'sequence',
				regions: [headerSwitch, tail],
				sourceBlocks: new AddressSet([
					...headerSwitch.sourceBlocks,
					...tail.sourceBlocks,
				]),
			},
		};
	}

	const firstBody = firstBodyBlock(cfg, loop);
	const entryPredicates = loopHeaderEntryPredicates(cfg, loop);
	const headerBranch = loopHeaderBranchRegion(
		cfg,
		loop,
		analyses,
		descriptors,
		regionAt,
	);
	if (headerBranch?.kind === 'if' && headerBranch.join != null) {
		const tail = speculate(
			ledger,
			() =>
				structureLoopBodySequence(
					cfg,
					loop,
					exits,
					headerBranch.join!,
					bodyWithoutHeader,
					entryPredicates,
					analyses,
					descriptors,
					regionAt,
					ledger,
				),
			(value) =>
				value != null &&
				!value.sourceBlocks.isSubsetOf(headerBranch.sourceBlocks),
		);
		if (!tail || tail.sourceBlocks.isSubsetOf(headerBranch.sourceBlocks)) {
			return { body: headerBranch };
		}
		return {
			body: {
				kind: 'sequence',
				regions: [headerBranch, tail],
				sourceBlocks: new AddressSet([
					...headerBranch.sourceBlocks,
					...tail.sourceBlocks,
				]),
			},
		};
	}
	const exitBranch = loopHeaderExitBranchRegion(
		cfg,
		loop,
		exits,
		analyses,
		descriptors,
	);
	if (exitBranch) {
		const combined = speculate(
			ledger,
			() => {
				const tail = structureLoopBodySequence(
					cfg,
					loop,
					exits,
					exitBranch.join,
					bodyWithoutHeader.difference(
						exitBranch.region.sourceBlocks,
					),
					entryPredicates,
					analyses,
					descriptors,
					regionAt,
				);
				return tail
					? sequenceLoopRegions([exitBranch.region, tail])
					: exitBranch.region;
			},
			(value) => loop.body.isSubsetOf(value.sourceBlocks),
		);
		if (loop.body.isSubsetOf(combined.sourceBlocks)) {
			return { body: combined };
		}
	}
	if (firstBody == null) {
		if (loop.body.size === 1 && loop.body.has(loop.header)) {
			return {
				body: {
					kind: 'sequence',
					regions: [],
					sourceBlocks: new AddressSet(),
				},
			};
		}
		recordCFGCompatibilityAttempt(
			descriptors.compatibility,
			'local-fallback-region',
			loop.header,
			'loop has no non-backedge body entry yet',
		);
		return {
			body: {
				kind: 'fallback',
				entry: loop.header,
				sourceBlocks: new AddressSet(loop.body),
				reason: 'loop has no non-backedge body entry yet',
			},
		};
	}

	const body = speculate(
		ledger,
		() =>
			structureLoopBodySequence(
				cfg,
				loop,
				exits,
				firstBody,
				bodyWithoutHeader,
				entryPredicates,
				analyses,
				descriptors,
				regionAt,
				ledger,
			) ??
				structureStraightLineSequenceFrom(
					cfg,
					firstBody,
					bodyWithoutHeader,
					regionAt,
				),
		(value) => value != null,
	);
	if (body) return { body };
	recordCFGCompatibilityAttempt(
		descriptors.compatibility,
		'local-fallback-region',
		firstBody,
		'loop body is not a straight-line sequence yet',
	);
	return {
		body: {
			kind: 'fallback',
			entry: firstBody,
			sourceBlocks: bodyWithoutHeader,
			reason: 'loop body is not a straight-line sequence yet',
		},
	};
}

/**
 * Keep a loop header's direct edge to a distinct latch as control flow rather
 * than treating the other successor as an unconditional body entry. The latch
 * is deliberately excluded from `body`: the emitter places it after the
 * conditional and can therefore consume the header-to-latch Phi action on the
 * bypass arm without duplicating the latch statements.
 */
function structureHeaderToLatchLoopBody(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	bodyWithoutHeader: AddressSet<BlockAddr>,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
): StructuredLoopBody | null {
	const header = cfg.blocks.get(loop.header);
	if (!header || header.terminator.kind !== 'if') return null;
	if (blockContainsForInPrelude(header.body)) return null;
	// This shape emits the header branch itself and has no place for an ordered
	// exit trailer, so a loop that owns one keeps the ordinary body.
	if (exits.some((exit) => exit.trailer != null)) return null;
	const fallthroughIsLatch = header.terminator.fallthrough !== loop.header &&
		loop.latches.includes(header.terminator.fallthrough);
	const takenIsLatch = header.terminator.taken !== loop.header &&
		loop.latches.includes(header.terminator.taken);
	if (fallthroughIsLatch === takenIsLatch) return null;
	const latch = fallthroughIsLatch
		? header.terminator.fallthrough
		: header.terminator.taken;
	const bodyEntry = fallthroughIsLatch
		? header.terminator.taken
		: header.terminator.fallthrough;
	if (!loop.body.has(bodyEntry) || bodyEntry === latch) return null;

	const allowed = new AddressSet(bodyWithoutHeader);
	allowed.delete(latch);
	const bodyCandidate = structureLoopBodySequence(
		cfg,
		loop,
		exits,
		bodyEntry,
		allowed,
		new Map(),
		analyses,
		descriptors,
		regionAt,
	) ?? structureStraightLineSequenceFrom(cfg, bodyEntry, allowed, regionAt);
	const body = bodyCandidate == null
		? null
		: detachLoopLatchSuffix(bodyCandidate, latch, cfg, exits);
	if (!body || !body.sourceBlocks.isSubsetOf(allowed)) return null;
	const covered = regionStructuredBlocks(body);
	if (!allowed.isSubsetOf(covered) || !covered.isSubsetOf(allowed)) {
		return null;
	}
	if (containsUnstructuredLoopBodyBranch(body, cfg)) return null;
	return {
		body,
		headerLatchBranch: { bodyEntry, latch },
	};
}

/**
 * Region composition can claim a bounded If's join as part of that If, or
 * append the join as a lexical suffix. A loop header-to-latch branch needs the
 * latch to remain outside the ordinary body so its two incoming Phi edges stay
 * path-local. Detach only those two mechanically proven shapes.
 */
function detachLoopLatchSuffix(
	region: Region,
	latch: BlockAddr,
	cfg: ImmutableCFG,
	exits: readonly LoopRegionExit[],
): Region | null {
	if (!region.sourceBlocks.has(latch)) return region;
	if (region.sourceBlocks.size === 1) return null;
	if (region.kind === 'if') {
		const consequentIsLatch = region.consequent.sourceBlocks.size === 1 &&
			region.consequent.sourceBlocks.has(latch);
		const alternateIsLatch = region.alternate.sourceBlocks.size === 1 &&
			region.alternate.sourceBlocks.has(latch);
		const nonLatchArm = consequentIsLatch
			? region.alternate
			: region.consequent;
		const terminator = cfg.blocks.get(region.header)?.terminator;
		if (
			consequentIsLatch !== alternateIsLatch &&
			isEmptyRegion(nonLatchArm) &&
			terminator?.kind === 'if'
		) {
			const exitTarget = consequentIsLatch
				? terminator.fallthrough
				: terminator.taken;
			const exit = exits.find((candidate) =>
				candidate.kind === 'break' &&
				candidate.from === region.header &&
				candidate.to === exitTarget
			);
			if (!exit) return null;
			const exitRegion: Region = {
				kind: 'break',
				target: exit.to,
				exit,
				sourceBlocks: new AddressSet(),
			};
			const sourceBlocks = new AddressSet(region.sourceBlocks);
			sourceBlocks.delete(latch);
			return {
				...region,
				join: latch,
				consequent: consequentIsLatch ? emptyLoopRegion() : exitRegion,
				alternate: alternateIsLatch ? emptyLoopRegion() : exitRegion,
				conditionalValue: undefined,
				sourceBlocks,
			};
		}
		if (
			region.join === latch &&
			!region.consequent.sourceBlocks.has(latch) &&
			!region.alternate.sourceBlocks.has(latch)
		) {
			const sourceBlocks = new AddressSet(region.sourceBlocks);
			sourceBlocks.delete(latch);
			return { ...region, sourceBlocks };
		}
		return null;
	}
	if (region.kind !== 'sequence') return null;

	const regions: Region[] = [];
	for (let index = 0; index < region.regions.length; index++) {
		const child = region.regions[index]!;
		if (!child.sourceBlocks.has(latch)) {
			regions.push(child);
			continue;
		}
		const trimmed = detachLoopLatchSuffix(child, latch, cfg, exits);
		if (trimmed) regions.push(trimmed);
		const suffix = region.regions.slice(index + 1);
		if (
			suffix.some((candidate) =>
				[...candidate.sourceBlocks].some((block) => block !== latch)
			)
		) return null;
		return sequenceLoopRegions(regions);
	}
	return region;
}

function blockContainsForInPrelude(
	statements: readonly t.Statement[],
): boolean {
	for (const statement of statements) {
		let found = false;
		t.traverseFast(statement, (node) => {
			if (
				t.isCallExpression(node) &&
				t.isV8IntrinsicIdentifier(node.callee, { name: 'GetPNameList' })
			) found = true;
		});
		if (found) return true;
	}
	return false;
}

/**
 * A loop body branch that no nested Region represents.
 *
 * This is deliberately more permissive than `regionUnstructuredBranches`: a
 * weak-SESE If Region may claim blocks it does not hand to an arm, and those
 * claims are the boundary the loop builders were written against. The strict
 * predicate is used where exact ownership is required instead.
 */
function containsUnstructuredLoopBodyBranch(
	region: Region,
	cfg: ImmutableCFG,
): boolean {
	const basicBranches = new AddressSet<BlockAddr>();
	const structuredBranches = new AddressSet<BlockAddr>();
	const visit = (candidate: Region) => {
		if (candidate.kind === 'basic') {
			for (const address of candidate.sourceBlocks) {
				if (blockNeedsBranchRegion(address, cfg)) {
					basicBranches.add(address);
				}
			}
			return;
		}
		switch (candidate.kind) {
			case 'if': {
				const childBlocks = candidate.consequent.sourceBlocks.union(
					candidate.alternate.sourceBlocks,
				);
				for (
					const address of candidate.sourceBlocks.difference(
						childBlocks,
					)
				) {
					if (cfg.blocks.get(address)?.terminator.kind === 'if') {
						structuredBranches.add(address);
					}
				}
				break;
			}
			case 'switch':
				for (const address of candidate.sourceBlocks) {
					if (cfg.blocks.get(address)?.terminator.kind === 'switch') {
						structuredBranches.add(address);
					}
				}
				break;
			case 'loop':
				structuredBranches.add(candidate.header);
				for (const latch of candidate.latches) {
					structuredBranches.add(latch);
				}
				break;
		}
		for (const child of loopBodyChildRegions(candidate)) visit(child);
	};
	visit(region);
	return [...basicBranches].some((address) =>
		!structuredBranches.has(address)
	);
}

function loopBodyChildRegions(region: Region): Region[] {
	switch (region.kind) {
		case 'sequence':
			return region.regions;
		case 'if':
			return [region.consequent, region.alternate];
		case 'switch':
			return [
				...region.cases.map((switchCase) => switchCase.body),
				region.defaultBody,
			];
		case 'tryCatch':
			return [region.body, region.handler];
		case 'tryFinally':
			return [region.body, region.finalizer];
		case 'loop':
			return [region.body];
		default:
			return [];
	}
}

/**
 * Structure a loop-header diamond whose internal arm contains an early loop
 * exit. Global postdominance places the join outside the loop, so the ordinary
 * If Region builder cannot see the internal reconvergence. Here exit edges are
 * explicit leaves and the nearest reconvergence of the remaining loop-local
 * paths is used instead.
 */
function loopHeaderExitBranchRegion(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
): { region: Region; join: BlockAddr } | null {
	const header = cfg.blocks.get(loop.header);
	if (!header || header.terminator.kind !== 'if') return null;
	const join = nearestLoopReconvergence(
		[header.terminator.fallthrough, header.terminator.taken],
		loop,
		cfg,
	);
	if (join == null) return null;
	const region = structureLoopPathToJoin(
		loop.header,
		join,
		cfg,
		loop,
		exits,
		new AddressSet(),
		analyses,
		descriptors,
	);
	return region ? { region, join } : null;
}

function structureLoopPathToJoin(
	entry: BlockAddr,
	join: BlockAddr,
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	seen: AddressSet<BlockAddr>,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
): Region | null {
	if (entry === join) return emptyLoopRegion();
	if (seen.has(entry) || !loop.body.has(entry)) return null;
	const block = cfg.blocks.get(entry);
	if (!block) return null;
	const nextSeen = new AddressSet(seen);
	nextSeen.add(entry);
	if (descriptors.switches.switchByDispatch.has(entry)) {
		const switchRegion = tryStructureSwitchRegion(
			cfg,
			analyses,
			descriptors,
			(target) =>
				structureLoopPathToJoin(
					target,
					join,
					cfg,
					loop,
					exits,
					nextSeen,
					analyses,
					descriptors,
				),
			{
				dispatchBlock: entry,
				enclosingRegionOwnsCases: true,
				joinOverride: join,
			},
		);
		if (switchRegion) {
			// Compare-chain descriptors conservatively include terminal targets and
			// the shared continuation in `coveredBlocks`. Inside a loop those are
			// represented by the loop-aware child callback as abrupt exits/backedges,
			// not statement ownership of the Switch Region itself.
			const sourceBlocks = switchRegion.sourceBlocks.intersection(
				loop.body,
			);
			sourceBlocks.delete(join);
			const boundedSwitch = { ...switchRegion, sourceBlocks };
			const structuredBlocks = regionStructuredBlocks(boundedSwitch);
			if (
				boundedSwitch.sourceBlocks.isSubsetOf(structuredBlocks) &&
				structuredBlocks.isSubsetOf(loop.body) &&
				!boundedSwitch.sourceBlocks.has(join)
			) return boundedSwitch;
		}
	}
	const basic: Region = {
		kind: 'basic',
		body: [],
		sourceBlocks: new AddressSet([entry]),
	};
	if (block.terminator.kind === 'goto') {
		const target = block.terminator.target;
		if (target === join) return basic;
		const tail = loopPathArm(
			entry,
			target,
			join,
			cfg,
			loop,
			exits,
			nextSeen,
			analyses,
			descriptors,
		);
		if (!tail) return null;
		return sequenceLoopRegions([basic, tail]);
	}
	if (block.terminator.kind !== 'if') return null;

	const successors = [
		block.terminator.fallthrough,
		block.terminator.taken,
	];
	// A loop-local reconvergence is the branch's own boundary even when the
	// remaining path completes with `continue` instead of reaching the caller's
	// join: without it both arms structure the shared suffix and each claims its
	// blocks, so only the arm emitted first keeps their statements.
	const localJoin = nearestLoopReconvergence(successors, loop, cfg);
	const branchJoin = localJoin ?? join;
	const alternate = loopPathArm(
		entry,
		block.terminator.fallthrough,
		branchJoin,
		cfg,
		loop,
		exits,
		nextSeen,
		analyses,
		descriptors,
	);
	const consequent = loopPathArm(
		entry,
		block.terminator.taken,
		branchJoin,
		cfg,
		loop,
		exits,
		nextSeen,
		analyses,
		descriptors,
	);
	if (!alternate || !consequent) return null;
	const branch: Region = {
		kind: 'if',
		header: entry,
		test: t.cloneNode(block.terminator.test, true),
		consequent,
		alternate,
		join: branchJoin,
		sourceBlocks: new AddressSet([
			entry,
			...consequent.sourceBlocks,
			...alternate.sourceBlocks,
		]),
	};
	if (branchJoin === join) return branch;
	const tail = structureLoopPathToJoin(
		branchJoin,
		join,
		cfg,
		loop,
		exits,
		nextSeen,
		analyses,
		descriptors,
	);
	return tail ? sequenceLoopRegions([branch, tail]) : null;
}

function loopPathArm(
	from: BlockAddr,
	target: BlockAddr,
	join: BlockAddr,
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	seen: AddressSet<BlockAddr>,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
): Region | null {
	if (target === join) return emptyLoopRegion();
	if (target === loop.header) {
		return loopContinueRegion(from, loop);
	}
	if (!loop.body.has(target)) {
		const exit = exits.find((candidate) =>
			candidate.from === from && candidate.to === target
		);
		if (!exit) return null;
		return loopExitRegion(exit);
	}
	return structureLoopPathToJoin(
		target,
		join,
		cfg,
		loop,
		exits,
		seen,
		analyses,
		descriptors,
	);
}

function nearestLoopReconvergence(
	entries: readonly BlockAddr[],
	loop: NaturalLoop,
	cfg: ImmutableCFG,
): BlockAddr | null {
	const distances = entries
		.filter((entry) => loop.body.has(entry))
		.map((entry) => loopDistances(entry, loop, cfg));
	if (distances.length < 2) return null;
	const common = [...distances[0]!.keys()].filter((candidate) =>
		candidate !== loop.header &&
		distances.every((distance) => distance.has(candidate)) &&
		entries.every((entry) =>
			loopLocallyPostdominates(candidate, entry, loop, cfg)
		)
	);
	return common.toSorted((left, right) => {
		const leftMax = Math.max(
			...distances.map((distance) => distance.get(left)!),
		);
		const rightMax = Math.max(
			...distances.map((distance) => distance.get(right)!),
		);
		return leftMax - rightMax || left - right;
	})[0] ?? null;
}

/**
 * Prove that every loop-local path which keeps executing this iteration reaches
 * `candidate`. Leaving the loop or returning to the header is an explicit arm
 * completion and therefore does not invalidate a local reconvergence.
 */
function loopLocallyPostdominates(
	candidate: BlockAddr,
	entry: BlockAddr,
	loop: NaturalLoop,
	cfg: ImmutableCFG,
): boolean {
	const memo = new Map<BlockAddr, boolean>();
	const active = new AddressSet<BlockAddr>();
	const candidateSuffix = loopDistances(candidate, loop, cfg);
	const visit = (current: BlockAddr): boolean => {
		if (current === candidate) return true;
		// A path may complete via break or continue before the partial join. It may
		// not, however, enter a later block also reached from the candidate: that is
		// the real shared suffix and consuming it inside the bypass arm would steal
		// it from the candidate arm.
		if (candidateSuffix.has(current)) return false;
		if (current === loop.header) return true;
		if (!loop.body.has(current)) return true;
		const cached = memo.get(current);
		if (cached != null) return cached;
		if (active.has(current)) return false;
		active.add(current);
		const successors = cfg.normalSuccessors.get(current) ??
			new AddressSet<BlockAddr>();
		const result = successors.size > 0 &&
			[...successors].every(visit);
		active.delete(current);
		memo.set(current, result);
		return result;
	};
	return visit(entry);
}

function loopDistances(
	entry: BlockAddr,
	loop: NaturalLoop,
	cfg: ImmutableCFG,
): Map<BlockAddr, number> {
	const distances = new Map<BlockAddr, number>();
	const queue: Array<[BlockAddr, number]> = [[entry, 0]];
	while (queue.length > 0) {
		const [current, distance] = queue.shift()!;
		if (
			current === loop.header || !loop.body.has(current) ||
			distances.has(current)
		) continue;
		distances.set(current, distance);
		for (const successor of cfg.normalSuccessors.get(current) ?? []) {
			queue.push([successor, distance + 1]);
		}
	}
	return distances;
}

function loopPathCanReach(
	entry: BlockAddr,
	target: BlockAddr,
	loop: NaturalLoop,
	cfg: ImmutableCFG,
): boolean {
	return entry === target || loopDistances(entry, loop, cfg).has(target);
}

function emptyLoopRegion(): Region {
	return { kind: 'sequence', regions: [], sourceBlocks: new AddressSet() };
}

function sequenceLoopRegions(regions: Region[]): Region {
	return {
		kind: 'sequence',
		regions,
		sourceBlocks: new AddressSet(
			regions.flatMap((region) => [...region.sourceBlocks]),
		),
	};
}

function loopHeaderSwitchRegion(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
): Extract<Region, { kind: 'switch' }> | null {
	if (cfg.blocks.get(loop.header)?.terminator.kind !== 'switch') return null;
	const region = tryStructureSwitchRegion(
		cfg,
		analyses,
		descriptors,
		(cursor, childAllowed) => {
			if (cursor === loop.header || !loop.body.has(cursor)) return null;
			const bounded = childAllowed == null
				? new AddressSet(loop.body)
				: childAllowed.intersection(loop.body);
			return regionAt?.(cursor, bounded) ?? null;
		},
		// The enclosing natural loop already owns every case block. Retain the
		// candidate join here even when a case cannot independently prove complete
		// ownership; the loop body and final Region audit remain the safety boundary.
		{ enclosingRegionOwnsCases: true },
	);
	if (!region || !region.sourceBlocks.isSubsetOf(loop.body)) return null;
	return region;
}

function loopHeaderBranchRegion(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
): Region | null {
	const header = cfg.blocks.get(loop.header);
	if (!header || header.terminator.kind !== 'if') return null;
	if (
		header.terminator.fallthrough === loop.header ||
		header.terminator.taken === loop.header ||
		!loop.body.has(header.terminator.fallthrough) ||
		!loop.body.has(header.terminator.taken)
	) return null;
	return tryStructureIfRegion(
		cfg,
		analyses,
		regionAt,
		loop.body,
		true,
		undefined,
		descriptors.compatibility,
	);
}

function representsLoopControlEdge(
	region: Region,
	from: BlockAddr,
	to: BlockAddr,
): boolean {
	switch (region.kind) {
		case 'break':
		case 'continue':
		case 'labelBreak':
		case 'labelContinue':
		case 'terminalReference':
			return region.exit?.from === from && region.exit.to === to;
		case 'deferredExit':
			return region.exit.edge?.from === from &&
				region.exit.edge.to === to;
		case 'sequence':
			return region.regions.some((child) =>
				representsLoopControlEdge(child, from, to)
			);
		case 'if':
			return representsLoopControlEdge(region.consequent, from, to) ||
				representsLoopControlEdge(region.alternate, from, to);
		case 'switch':
			return region.cases.some((switchCase) =>
				representsLoopControlEdge(switchCase.body, from, to)
			) || representsLoopControlEdge(region.defaultBody, from, to);
		case 'tryCatch':
			return representsLoopControlEdge(region.body, from, to) ||
				representsLoopControlEdge(region.handler, from, to);
		case 'tryFinally':
			return representsLoopControlEdge(region.body, from, to) ||
				representsLoopControlEdge(region.finalizer, from, to);
		default:
			return false;
	}
}
/**
 * A nested loop can carry the control statement for an exit from this loop.
 * Give that statement this loop's ordered trailer so edge-local work executes
 * before the labelled transfer rather than being stranded after the loop.
 */
function attachStructuredLoopExitActions(
	region: Region,
	exits: readonly LoopRegionExit[],
): void {
	visitRegions(region, (candidate) => {
		if (
			candidate.kind !== 'break' &&
			candidate.kind !== 'continue' &&
			candidate.kind !== 'labelBreak' &&
			candidate.kind !== 'labelContinue' &&
			candidate.kind !== 'terminalReference'
		) return;
		const embedded = candidate.exit;
		if (!embedded) return;
		const structured = exits.find((exit) =>
			exit.from === embedded.from && exit.to === embedded.to &&
			(
				exit.trailer != null ||
				exit.normalCompletionFlag != null ||
				exit.sequenceExit != null
			)
		);
		if (!structured) return;
		candidate.exit = {
			...structured,
			kind: embedded.kind,
			label: embedded.label,
			targetLoop: embedded.targetLoop,
		};
	});
}
/**
 * Exception landing pads are not natural-loop blocks, but a nested `try`
 * can place their explicit transfer out of this loop. Retain those exits on
 * the Loop Region so the emitter can place their edge-local Phi copies.
 */

function representedExternalLoopExits(
	region: Region,
	loop: NaturalLoop,
	knownExits: readonly LoopRegionExit[],
): LoopRegionExit[] {
	const result: LoopRegionExit[] = [];
	const breakTargets = new Set(
		knownExits
			.filter((exit) =>
				exit.kind === 'break' || exit.kind === 'labelledBreak'
			)
			.flatMap((exit) => [
				exit.to,
				...(exit.continuation == null ? [] : [exit.continuation]),
			]),
	);
	const visit = (current: Region): void => {
		switch (current.kind) {
			case 'break':
			case 'labelBreak':
			case 'continue':
			case 'labelContinue': {
				const exit = current.exit;
				if (!exit || loop.body.has(exit.from)) return;
				const targetsThisLoop = exit.kind === 'continue' ||
						exit.kind === 'labelledContinue'
					? exit.to === loop.header
					: breakTargets.has(exit.to);
				if (!targetsThisLoop) return;
				const duplicate = [...knownExits, ...result].some((known) =>
					known.from === exit.from && known.to === exit.to &&
					known.kind === exit.kind
				);
				if (!duplicate) result.push(exit);
				return;
			}
			case 'sequence':
				current.regions.forEach(visit);
				return;
			case 'if':
				visit(current.consequent);
				visit(current.alternate);
				return;
			case 'switch':
				current.cases.forEach((switchCase) => visit(switchCase.body));
				visit(current.defaultBody);
				return;
			case 'tryCatch':
				visit(current.body);
				visit(current.handler);
				return;
			case 'tryFinally':
				visit(current.body);
				visit(current.finalizer);
				return;
			case 'loop':
				return;
		}
	};
	visit(region);
	return result;
}

/**
 * Put one loop transfer into the empty Region arm or Basic Region that owns its
 * source edge. The transfer owns no block, so every enclosing ownership set is
 * unchanged.
 */
function placeProtectedLoopControl(
	region: Region,
	from: BlockAddr,
	to: BlockAddr,
	control: Region,
	cfg: ImmutableCFG,
): Region | null {
	if (representsLoopControlEdge(region, from, to)) return region;
	if (region.kind === 'if' && region.header === from) {
		const block = cfg.blocks.get(from);
		if (block?.terminator.kind !== 'if') return null;
		if (block.terminator.taken === to) {
			if (region.consequent.sourceBlocks.size !== 0) return null;
			return { ...region, consequent: control };
		}
		if (block.terminator.fallthrough === to) {
			if (region.alternate.sourceBlocks.size !== 0) return null;
			return { ...region, alternate: control };
		}
		return null;
	}
	if (region.kind === 'basic' && region.sourceBlocks.has(from)) {
		const outside = [...region.sourceBlocks].flatMap((block) =>
			[...(cfg.normalSuccessors.get(block) ?? [])].filter((successor) =>
				!region.sourceBlocks.has(successor)
			).map((successor) => ({ block, successor }))
		);
		if (
			outside.length !== 1 ||
			outside[0].block !== from ||
			outside[0].successor !== to
		) return null;
		return {
			kind: 'sequence',
			regions: [region, control],
			sourceBlocks: new AddressSet(region.sourceBlocks),
		};
	}
	const replace = (child: Region): Region | null =>
		child.sourceBlocks.has(from)
			? placeProtectedLoopControl(child, from, to, control, cfg)
			: child;
	switch (region.kind) {
		case 'sequence': {
			const owners = region.regions.filter((child) =>
				child.sourceBlocks.has(from)
			);
			if (owners.length !== 1) return null;
			const regions = region.regions.map(replace);
			if (regions.some((child) => child == null)) return null;
			return { ...region, regions: regions as Region[] };
		}
		case 'if': {
			const consequent = replace(region.consequent);
			const alternate = replace(region.alternate);
			if (!consequent || !alternate) return null;
			return { ...region, consequent, alternate };
		}
		case 'switch': {
			const cases = region.cases.map((switchCase) => ({
				...switchCase,
				body: replace(switchCase.body),
			}));
			const defaultBody = replace(region.defaultBody);
			if (
				cases.some((switchCase) => switchCase.body == null) ||
				!defaultBody
			) return null;
			return {
				...region,
				cases: cases as typeof region.cases,
				defaultBody,
			};
		}
		case 'tryCatch': {
			const body = replace(region.body);
			const handler = replace(region.handler);
			if (!body || !handler) return null;
			return { ...region, body, handler };
		}
		case 'tryFinally': {
			const body = replace(region.body);
			const finalizer = replace(region.finalizer);
			if (!body || !finalizer) return null;
			return { ...region, body, finalizer };
		}
		default:
			return null;
	}
}

function routeProtectedLoopControls(
	region: Region,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	cfg: ImmutableCFG,
): Region | null {
	const outgoing: Array<{ from: BlockAddr; to: BlockAddr }> = [];
	for (const from of region.sourceBlocks) {
		for (const to of cfg.normalSuccessors.get(from) ?? []) {
			if (!region.sourceBlocks.has(to)) outgoing.push({ from, to });
		}
	}
	let routed = region;
	for (const edge of outgoing) {
		if (representsLoopControlEdge(routed, edge.from, edge.to)) continue;
		const control = loopControlRegion(
			edge.from,
			edge.to,
			loop,
			exits,
		);
		if (!control) continue;
		const placed = placeProtectedLoopControl(
			routed,
			edge.from,
			edge.to,
			control,
			cfg,
		);
		if (!placed) return null;
		routed = placed;
	}
	return routed;
}

/**
 * The exception Region a protected entry inside the loop body opens.
 *
 * Offered before the branch builders, which would otherwise claim the entry as
 * an ordinary conditional and leave the range with no block whose Region can
 * be the `try`. Declined unless the candidate is exactly that try, stays inside
 * the body's scope, and leaves every block a loop exit places to that exit --
 * swallowing one would emit its statements twice.
 */
function protectedEntryTryRegion(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	cursor: BlockAddr,
	allowed: AddressSet<BlockAddr>,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
	ledger?: AddressSet<BlockAddr>,
): { region: Region; continuation?: BlockAddr } | null {
	if (!regionAt) return null;
	if (
		!descriptors.exceptions.handlers.some((descriptor) =>
			descriptor.protectedEntries.has(cursor) &&
			!descriptors.exceptions.finalizerCopyModel.copyDescriptorHandlers
				.has(descriptor.handler)
		)
	) return null;
	return speculate(ledger, () => {
		let candidate = regionAt(cursor, allowed);
		if (
			!candidate ||
			(candidate.kind !== 'tryCatch' && candidate.kind !== 'tryFinally')
		) return null;
		if (!candidate.sourceBlocks.has(cursor)) return null;
		if (!candidate.sourceBlocks.isSubsetOf(allowed)) return null;
		if (regionContainsLoop(candidate, loop.id)) return null;
		for (const exit of exits) {
			const placed = exit.trailer ? exit.continuation : exit.to;
			if (placed != null && candidate.sourceBlocks.has(placed)) {
				return null;
			}
		}
		const routed = routeProtectedLoopControls(candidate, loop, exits, cfg);
		if (!routed) return null;
		candidate = routed as typeof candidate;
		const continuation = uniqueAllowedExit(
			cfg,
			candidate.sourceBlocks,
			allowed,
		);
		if (continuation != null) return { region: candidate, continuation };
		for (const from of candidate.sourceBlocks) {
			for (const to of cfg.normalSuccessors.get(from) ?? []) {
				if (candidate.sourceBlocks.has(to)) continue;
				if (!representsLoopControlEdge(candidate, from, to)) {
					return null;
				}
			}
		}
		return { region: candidate };
	}, (value) => value != null);
}

function structureLoopBodySequence(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	entry: BlockAddr,
	allowed: AddressSet<BlockAddr>,
	entryPredicates: Map<BlockAddr, t.Expression>,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
	ledger?: AddressSet<BlockAddr>,
): Region | null {
	const regions: Region[] = [];
	const consumed = new AddressSet<BlockAddr>();
	let cursor: BlockAddr | undefined = entry;

	while (cursor != null && allowed.has(cursor) && !consumed.has(cursor)) {
		const block = cfg.blocks.get(cursor);
		if (!block) break;
		const iteratorGuard = nestedForInGuardRegion(
			cfg,
			loop,
			cursor,
			allowed,
			analyses,
			descriptors,
			regionAt,
		);
		if (iteratorGuard) {
			regions.push(iteratorGuard.region);
			for (const consumedBlock of iteratorGuard.region.sourceBlocks) {
				consumed.add(consumedBlock);
			}
			cursor = iteratorGuard.continuation;
			continue;
		}
		const nestedGuard = nestedLoopGuardRegion(
			cfg,
			loop,
			cursor,
			allowed,
			analyses,
			regionAt,
		);
		if (nestedGuard) {
			regions.push(nestedGuard.region);
			for (const consumedBlock of nestedGuard.region.sourceBlocks) {
				consumed.add(consumedBlock);
			}
			cursor = nestedGuard.continuation;
			continue;
		}
		const nestedLoop = analyses.naturalLoops.loopByHeader.get(cursor);
		if (nestedLoop && nestedLoop.id !== loop.id) {
			const candidate = regionAt?.(cursor, allowed);
			const structured = candidate?.kind === 'loop' &&
					candidate.id === nestedLoop.id &&
					candidate.sourceBlocks.isSubsetOf(allowed)
				? candidate
				: null;
			if (structured) {
				regions.push(structured);
				for (const consumedBlock of structured.sourceBlocks) {
					consumed.add(consumedBlock);
				}
				const continuation = uniqueAllowedExit(
					cfg,
					structured.sourceBlocks,
					allowed,
				);
				if (continuation == null || consumed.has(continuation)) break;
				cursor = continuation;
				continue;
			}
		}
		if (descriptors.switches.switchByDispatch.has(cursor)) {
			const localSwitch = structureLoopPathToJoin(
				cursor,
				loop.header,
				cfg,
				loop,
				exits,
				new AddressSet(),
				analyses,
				descriptors,
			);
			const candidate = localSwitch ?? regionAt?.(cursor, allowed);
			const structured = candidate &&
					!regionContainsLoop(candidate, loop.id) &&
					candidate.sourceBlocks.isSubsetOf(allowed)
				? candidate
				: null;
			if (structured) {
				regions.push(structured);
				for (const consumedBlock of structured.sourceBlocks) {
					consumed.add(consumedBlock);
				}
				const continuation = uniqueAllowedExit(
					cfg,
					structured.sourceBlocks,
					allowed,
				);
				if (continuation == null || consumed.has(continuation)) break;
				cursor = continuation;
				continue;
			}
		}

		// A protected entry is the only block whose Region can be the `try`. A
		// branch builder claiming it first leaves the handler with nowhere to
		// open, so the recursion is offered the cursor before them.
		const protectedTry = protectedEntryTryRegion(
			cfg,
			loop,
			exits,
			cursor,
			allowed,
			descriptors,
			regionAt,
			ledger,
		);
		if (protectedTry) {
			regions.push(protectedTry.region);
			for (const consumedBlock of protectedTry.region.sourceBlocks) {
				consumed.add(consumedBlock);
			}
			if (
				protectedTry.continuation == null ||
				consumed.has(protectedTry.continuation)
			) break;
			cursor = protectedTry.continuation;
			continue;
		}

		const branch = branchControlRegion(
			cfg,
			loop,
			exits,
			cursor,
			allowed,
			entryPredicates.get(cursor),
		);
		if (branch) {
			if (block.body.length > 0) {
				regions.push({
					kind: 'basic',
					body: [],
					sourceBlocks: new AddressSet([cursor]),
				});
			}
			regions.push(branch.region);
			consumed.add(cursor);
			cursor = branch.continuation;
			continue;
		}

		const localBranch = loopLocalBranchRegion(
			cfg,
			loop,
			exits,
			cursor,
			allowed.difference(consumed),
			analyses,
			descriptors,
			entryPredicates.get(cursor),
		);
		if (localBranch) {
			regions.push(localBranch.region);
			for (const consumedBlock of localBranch.region.sourceBlocks) {
				consumed.add(consumedBlock);
			}
			cursor = localBranch.continuation;
			continue;
		}

		const candidate = regionAt?.(cursor, allowed);
		// A recursively structured internal branch may rediscover the loop that is
		// currently being built. Accept nested loops and loop-local source coverage,
		// but never recursively embed this same loop Region in its own body.
		const structured = candidate && regionContainsLoop(candidate, loop.id)
			? null
			: candidate;
		if (!structured && regionAt && !entryPredicates.has(cursor)) {
			const residual = composeLoopScopeForest(
				cfg,
				loop,
				exits,
				cursor,
				allowed.difference(consumed),
				analyses,
				descriptors,
				regionAt,
			);
			if (residual) {
				regions.push(residual);
				for (const consumedBlock of regionStructuredBlocks(residual)) {
					consumed.add(consumedBlock);
				}
				break;
			}
		}
		if (structured) {
			regions.push(structured);
			for (const consumedBlock of structured.sourceBlocks) {
				consumed.add(consumedBlock);
			}
			const continuation = uniqueAllowedExit(
				cfg,
				structured.sourceBlocks,
				allowed,
			);
			if (continuation == null || consumed.has(continuation)) break;
			cursor = continuation;
			continue;
		}

		regions.push({
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([cursor]),
		});
		consumed.add(cursor);

		const successors = cfg.normalSuccessors.get(cursor) ??
			new AddressSet<BlockAddr>();
		if (successors.size !== 1) break;
		const [next] = [...successors];
		if (!allowed.has(next)) break;
		cursor = next;
	}

	if (regions.length === 0) return null;
	if (regions.length === 1) return regions[0];
	return {
		kind: 'sequence',
		regions,
		sourceBlocks: consumed,
	};
}

/**
 * Recover the GetPNameList guard immediately surrounding a nested for-in loop.
 *
 * Hermes branches around GetNextPName when GetPNameList reports no enumerable
 * properties. `for (… in …)` already has exactly that zero-iteration behavior,
 * so the guard is protocol scaffolding rather than a source-level conditional.
 * Keeping the guard and Loop Regions adjacent lets the emitter consume the
 * preheader intrinsic while the enclosing loop still owns the continuation.
 */
function nestedForInGuardRegion(
	cfg: ImmutableCFG,
	enclosingLoop: NaturalLoop,
	guard: BlockAddr,
	allowed: AddressSet<BlockAddr>,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
): { region: Region; continuation: BlockAddr } | null {
	if (!regionAt) return null;
	const block = cfg.blocks.get(guard);
	if (!block || block.terminator.kind !== 'if') return null;
	const candidates = [
		{
			loopTarget: block.terminator.taken,
			bypass: block.terminator.fallthrough,
			loopOnTaken: true,
		},
		{
			loopTarget: block.terminator.fallthrough,
			bypass: block.terminator.taken,
			loopOnTaken: false,
		},
	];
	for (const candidate of candidates) {
		const nestedLoop = analyses.naturalLoops.loopByHeader.get(
			candidate.loopTarget,
		);
		if (
			!nestedLoop || nestedLoop.id === enclosingLoop.id ||
			!allowed.has(candidate.bypass)
		) continue;
		const nested = tryStructureLoopRegion(
			cfgEnteringAt(cfg, candidate.loopTarget),
			analyses,
			descriptors,
			regionAt,
			{ allowMixedAbruptExits: true },
		) ?? regionAt(candidate.loopTarget, allowed);
		if (
			nested?.kind !== 'loop' || nested.id !== nestedLoop.id ||
			nested.syntax?.kind !== 'forIn' ||
			nested.syntax.preheader?.block !== guard ||
			!nested.sourceBlocks.isSubsetOf(allowed) ||
			!nested.exits.some((exit) => exit.to === candidate.bypass)
		) continue;
		const empty = emptyLoopRegion();
		return {
			region: {
				kind: 'if',
				header: guard,
				test: t.cloneNode(block.terminator.test, true),
				consequent: candidate.loopOnTaken ? nested : empty,
				alternate: candidate.loopOnTaken ? empty : nested,
				join: candidate.bypass,
				sourceBlocks: new AddressSet([
					guard,
					...nested.sourceBlocks,
				]),
			},
			continuation: candidate.bypass,
		};
	}
	return null;
}

/**
 * Recover an ordinary conditional which either enters an immediate child loop
 * or skips directly to that loop's sole continuation.
 *
 * The generic loop-local branch walker cannot traverse a child backedge: it
 * sees the child header a second time and rejects the arm as cyclic. Structure
 * the child first, then use it as the conditional arm.
 */
function nestedLoopGuardRegion(
	cfg: ImmutableCFG,
	enclosingLoop: NaturalLoop,
	guard: BlockAddr,
	allowed: AddressSet<BlockAddr>,
	analyses: CFGAnalyses,
	regionAt?: RegionAt,
): { region: Region; continuation: BlockAddr } | null {
	if (!regionAt) return null;
	const block = cfg.blocks.get(guard);
	if (!block || block.terminator.kind !== 'if') return null;
	const candidates = [
		{
			loopTarget: block.terminator.taken,
			bypass: block.terminator.fallthrough,
			loopOnTaken: true,
		},
		{
			loopTarget: block.terminator.fallthrough,
			bypass: block.terminator.taken,
			loopOnTaken: false,
		},
	];
	for (const candidate of candidates) {
		const childLoop = analyses.naturalLoops.loopByHeader.get(
			candidate.loopTarget,
		);
		if (
			!childLoop || childLoop.parent !== enclosingLoop.id ||
			!allowed.has(candidate.bypass)
		) continue;
		const child = regionAt(candidate.loopTarget, allowed);
		if (
			child?.kind !== 'loop' || child.id !== childLoop.id ||
			!child.sourceBlocks.isSubsetOf(allowed) ||
			child.sourceBlocks.has(candidate.bypass) ||
			uniqueAllowedExit(cfg, child.sourceBlocks, allowed) !==
				candidate.bypass
		) continue;
		const empty = emptyLoopRegion();
		return {
			region: {
				kind: 'if',
				header: guard,
				test: t.cloneNode(block.terminator.test, true),
				consequent: candidate.loopOnTaken ? child : empty,
				alternate: candidate.loopOnTaken ? empty : child,
				join: candidate.bypass,
				sourceBlocks: new AddressSet([
					guard,
					...child.sourceBlocks,
				]),
			},
			continuation: candidate.bypass,
		};
	}
	return null;
}

/**
 * A loop-body block set widened by nested handlers and their private subgraphs.
 *
 * Nothing branches normally to a handler, so it is never a natural-loop block,
 * yet a try whose protected range lies inside one iteration is part of that
 * body. Admit everything only that handler reaches, stopping at natural-loop
 * blocks and known loop exits; predecessor validation keeps shared
 * continuations outside. The `for...of` cleanup landing pad is deliberately
 * excluded because the loop syntax already represents it.
 */
function withExceptionOwnedBlocks(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
): NaturalLoop {
	const body = withNestedHandlerBlocks(
		cfg,
		loop,
		analyses,
		descriptors,
		loop.body,
	);
	if (body.size === loop.body.size) return loop;
	const exits = [...body].flatMap((from) =>
		[...(cfg.normalSuccessors.get(from) ?? [])]
			.filter((to) => !body.has(to))
			.map((to) => ({ from, to, kind: 'normal' as const }))
	);
	return { ...loop, body, exits };
}

function withNestedHandlerBlocks(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	base: AddressSet<BlockAddr>,
): AddressSet<BlockAddr> {
	const elided = iteratorCleanupHandlersForLoop(loop, cfg, descriptors);
	const scope = new AddressSet(base);
	// A protected return or throw remains lexically inside the loop even though
	// it reaches no latch and therefore is absent from the natural-loop body.
	// Admit the whole range only when every place it can open is already in this
	// scope and every added protected block is dominated by the loop header.
	for (let changed = true; changed;) {
		changed = false;
		for (const descriptor of descriptors.exceptions.handlers) {
			const openable = openableProtectedEntries(cfg, descriptor);
			if (
				descriptor.protectedBlocks.size === 0 ||
				openable.intersection(loop.body).size === 0 ||
				openable.has(loop.header) ||
				!openable.isSubsetOf(scope) ||
				[...descriptor.protectedBlocks].some((block) =>
					!scope.has(block) &&
					!analyses.dominators.dominates(loop.header, block)
				)
			) continue;
			for (const block of descriptor.protectedBlocks) {
				if (scope.has(block)) continue;
				scope.add(block);
				changed = true;
			}
			for (const from of descriptor.protectedBlocks) {
				for (const to of cfg.normalSuccessors.get(from) ?? []) {
					if (
						scope.has(to) ||
						directTerminalExitKind(to, cfg) == null ||
						!analyses.dominators.dominates(loop.header, to)
					) continue;
					scope.add(to);
					changed = true;
				}
			}
		}
	}
	// Iterated: an enclosing try can protect the handler of the try nested
	// inside it, so the inner handler and trailer must join the scope first.
	for (let changed = true; changed;) {
		changed = false;
		const exitTargets = new AddressSet<BlockAddr>(
			[...scope].flatMap((from) =>
				[...(cfg.normalSuccessors.get(from) ?? [])].filter((to) =>
					!scope.has(to)
				)
			),
		);
		for (const descriptor of descriptors.exceptions.handlers) {
			if (
				elided.has(descriptor.handler) ||
				scope.has(descriptor.handler) ||
				descriptor.protectedBlocks.size === 0 ||
				!descriptor.protectedBlocks.isSubsetOf(scope) ||
				descriptor.protectedEntries.intersection(base).size === 0
			) continue;
			const owned = handlerOwnedBlocks(
				descriptor.handler,
				cfg,
				scope,
				exitTargets,
			);
			if (!owned) continue;
			for (const block of owned) scope.add(block);
			changed = true;
		}
	}
	return scope;
}

/**
 * Own a loop body through its acyclic control skeleton.
 *
 * The body walk recognizes one branch shape at a time. When no builder claims a
 * block the walk keeps it as a Basic Region and stops, which silently drops
 * every block below its conditional terminator. Composing the residual instead
 * keeps ownership exact: nested loops stay opaque contracted nodes, non-adjacent
 * edges become labelled sequence exits, and every edge leaving the scope becomes
 * its ordered loop completion.
 *
 * The scope is deliberately narrow: a recovered switch dispatch keeps its
 * specialized descriptor rather than degrading to a comparison ladder.
 */
function composeLoopScopeForest(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	entry: BlockAddr,
	allowed: AddressSet<BlockAddr>,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt: RegionAt,
): Region | null {
	// A dispatch terminator is owned by the skeleton itself; a recovered
	// comparison chain is contracted so the skeleton keeps the recovered
	// `switch` instead of the equality ladder it came from.
	const compareChains = new AddressSet<BlockAddr>(
		[...allowed].filter((address) =>
			descriptors.switches.switchByDispatch.get(address)?.kind ===
				'compareChain'
		),
	);
	// A source-level try/catch may be wholly contained by one loop iteration
	// while one protected block is an ordered exit trailer. That trailer still
	// executes lexically inside the loop and the try, so let the body forest own
	// the complete trailer rather than splitting the protected range. Later the
	// Loop Region replaces the pre-trailer exit with the explicit transfer this
	// body emits.
	const bodyScope = withNestedHandlerBlocks(
		cfg,
		loop,
		analyses,
		descriptors,
		allowed,
	);
	const exitTrailers = exits.flatMap((exit) =>
		exit.trailer ? [exit.trailer] : []
	);
	const exitTrailerBlocks = new AddressSet<BlockAddr>(
		exitTrailers.flatMap((trailer) => [...trailer.sourceBlocks]),
	);
	for (const descriptor of descriptors.exceptions.handlers) {
		if (descriptor.protectedEntries.intersection(bodyScope).size === 0) {
			continue;
		}
		const missing = descriptor.protectedBlocks.difference(bodyScope);
		if (missing.size === 0 || !missing.isSubsetOf(exitTrailerBlocks)) {
			continue;
		}
		for (const trailer of exitTrailers) {
			if (trailer.sourceBlocks.intersection(missing).size === 0) continue;
			for (const block of trailer.sourceBlocks) bodyScope.add(block);
		}
	}
	for (
		const block of withNestedHandlerBlocks(
			cfg,
			loop,
			analyses,
			descriptors,
			bodyScope,
		)
	) bodyScope.add(block);
	const containedExceptionDescriptors = descriptors.exceptions.handlers
		.filter(
			(descriptor) =>
				bodyScope.has(descriptor.handler) &&
				descriptor.protectedBlocks.isSubsetOf(bodyScope) &&
				descriptor.protectedEntries.intersection(bodyScope).size > 0,
		);
	const containedHandlers = new AddressSet(
		containedExceptionDescriptors.map((descriptor) => descriptor.handler),
	);
	const containedExceptionRoots = containedExceptionDescriptors.filter(
		(descriptor) => {
			const parent = descriptors.exceptions.forest.parentByHandler.get(
				descriptor.handler,
			);
			return parent == null || !containedHandlers.has(parent);
		},
	);
	const exceptionByEntry = new Map<BlockAddr, ExceptionDescriptor>();
	for (const descriptor of containedExceptionRoots) {
		for (
			const protectedEntry of descriptor.protectedEntries.intersection(
				bodyScope,
			)
		) {
			exceptionByEntry.set(protectedEntry, descriptor);
		}
	}
	const containedExceptionEntries = new AddressSet<BlockAddr>(
		containedExceptionRoots.flatMap((descriptor) => [
			...descriptor.protectedEntries.intersection(bodyScope),
		]),
	);
	const containedProtectedBlocks = new AddressSet<BlockAddr>(
		containedExceptionRoots.flatMap((descriptor) => [
			...descriptor.protectedBlocks,
		]),
	);
	const enclosingExceptionBoundaries = descriptors.exceptions
			.iteratorCleanupActionElision
		? descriptors.exceptions.handlers.filter((descriptor) =>
			!containedHandlers.has(descriptor.handler) &&
			descriptor.protectedBlocks.intersection(bodyScope).size > 0
		)
		: [];
	const residual = tryStructureBoundedScopeForest(
		cfg,
		analyses,
		(nested) => {
			if (nested.id === loop.id) return null;
			const candidate = regionAt(nested.header, bodyScope);
			return candidate?.kind === 'loop' && candidate.id === nested.id &&
					candidate.sourceBlocks.isSubsetOf(bodyScope)
				? candidate
				: null;
		},
		{
			entry,
			allowed: bodyScope,
			labelPrefix: `loop${loop.id}_body`,
			completion: (from, to) => loopControlRegion(from, to, loop, exits),
			exceptionBoundary: (from, to) =>
				bodyScope.has(from) &&
				enclosingExceptionBoundaries.some((descriptor) =>
					descriptor.handler === to &&
					descriptor.protectedBlocks.has(from)
				),
		},
		compareChains.size === 0 ? undefined : {
			dispatches: compareChains,
			switchAt: (dispatch) =>
				tryStructureSwitchRegion(
					cfgEnteringAt(cfg, dispatch),
					analyses,
					descriptors,
					(cursor, childAllowed) => {
						if (cursor === dispatch) return null;
						return regionAt(
							cursor,
							(childAllowed ?? bodyScope).intersection(bodyScope),
						);
					},
					{ dispatchBlock: dispatch },
				),
		},
		containedExceptionEntries.size === 0 ? undefined : {
			entries: containedExceptionEntries,
			protectedBlocks: containedProtectedBlocks,
			exceptionAt: (protectedEntry) => {
				const descriptor = exceptionByEntry.get(protectedEntry);
				if (!descriptor) return null;
				const bound = contractedExceptionBlocks(
					cfg,
					descriptor,
					descriptors,
				).intersection(bodyScope);
				const candidate = tryStructureExceptionRegion(
					cfgEnteringAt(cfg, protectedEntry),
					descriptors,
					(cursor, childAllowed) => {
						if (cursor === protectedEntry) return null;
						return regionAt(
							cursor,
							(childAllowed ?? bound).intersection(bound),
						);
					},
					bound,
					new AddressSet<BlockAddr>(),
					analyses,
					{ exactScope: true },
				);
				return candidate?.sourceBlocks.isSubsetOf(bound)
					? candidate
					: null;
			},
		},
	);
	if (!residual) return null;
	const covered = regionStructuredBlocks(residual);
	return covered.isSubsetOf(bodyScope) &&
			!containsUnstructuredLoopBodyBranch(residual, cfg) &&
			regionDuplicateOwnership(residual, cfg).length === 0
		? residual
		: null;
}

/**
 * Recompose a whole loop body that the ordinary builders left incomplete.
 *
 * A header that branches or dispatches into the body keeps its own control flow
 * inside the body, so the skeleton starts at the header itself and the loop
 * backedges become its `continue` completions. Otherwise the body has one entry
 * below the header. Iterator loops and header entry predicates carry syntax and
 * values that the generic skeleton cannot represent, so they keep their
 * specialized builders.
 */
function structureLoopBodyResidual(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	hasIteratorSyntax: boolean,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
): Region | null {
	if (!regionAt) return null;
	const header = cfg.blocks.get(loop.header);
	if (!header) return null;
	// A recovered iterator loop keeps its header: the machine statements there are
	// subsumed by `for...of`/`for...in` syntax, so only the body below it may be
	// recomposed.
	const headerOwnable = !hasIteratorSyntax &&
		!blockContainsForInPrelude(header.body);
	const headerDiamond = headerOwnable &&
		header.terminator.kind === 'if' &&
		header.terminator.fallthrough !== loop.header &&
		header.terminator.taken !== loop.header &&
		loop.body.has(header.terminator.fallthrough) &&
		loop.body.has(header.terminator.taken);
	// A dispatch header cannot be split from its cases at all: the Switch Region
	// owns the header block, and the loop emitter recognizes that the body
	// already emitted it.
	const headerDispatch = headerOwnable &&
		header.terminator.kind === 'switch';
	const ownsHeader = headerDiamond || headerDispatch;
	const bodyScope = withNestedHandlerBlocks(
		cfg,
		loop,
		analyses,
		descriptors,
		loop.body,
	);
	const bodyWithoutHeader = new AddressSet(bodyScope);
	bodyWithoutHeader.delete(loop.header);
	const entry = ownsHeader ? loop.header : firstBodyBlock(cfg, loop);
	if (entry == null) return null;
	if (!ownsHeader && loopHeaderEntryPredicates(cfg, loop).has(entry)) {
		return null;
	}
	const residual = composeLoopScopeForest(
		cfg,
		loop,
		exits,
		entry,
		ownsHeader ? bodyScope : bodyWithoutHeader,
		analyses,
		descriptors,
		regionAt,
	);
	return residual &&
			loop.body.isSubsetOf(
				regionStructuredBlocks(residual)
					.union(nestedSubsumedLoopHandlers(residual))
					.union(new AddressSet([loop.header])),
			)
		? residual
		: null;
}

/**
 * Structure an acyclic conditional inside a natural loop without consulting
 * global postdominance. One arm may reconverge locally, or may be a bounded
 * forwarding path to the loop header while the other arm continues the body.
 */
function loopLocalBranchRegion(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	addr: BlockAddr,
	allowed: AddressSet<BlockAddr>,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	entryPredicate?: t.Expression,
): { region: Region; continuation: BlockAddr } | null {
	const block = cfg.blocks.get(addr);
	if (!block || block.terminator.kind !== 'if') return null;
	const successors = [
		block.terminator.fallthrough,
		block.terminator.taken,
	];
	const join = nearestLoopReconvergence(successors, loop, cfg);
	if (join != null && allowed.has(join)) {
		const region = structureLoopPathToJoin(
			addr,
			join,
			cfg,
			loop,
			exits,
			new AddressSet(),
			analyses,
			descriptors,
		);
		if (
			region?.sourceBlocks.has(addr) &&
			region.sourceBlocks.isSubsetOf(allowed)
		) return { region, continuation: join };
	}

	const fallthroughBackedge = structureLoopBackedgeArm(
		addr,
		block.terminator.fallthrough,
		cfg,
		loop,
		allowed,
	);
	const takenBackedge = structureLoopBackedgeArm(
		addr,
		block.terminator.taken,
		cfg,
		loop,
		allowed,
	);
	if ((fallthroughBackedge == null) === (takenBackedge == null)) return null;
	const continuation = fallthroughBackedge
		? block.terminator.taken
		: block.terminator.fallthrough;
	if (!allowed.has(continuation)) return null;
	const empty = emptyLoopRegion();
	const test = entryPredicate
		? t.logicalExpression(
			'&&',
			t.cloneNode(entryPredicate, true),
			t.cloneNode(block.terminator.test, true),
		)
		: t.cloneNode(block.terminator.test, true);
	const consequent = takenBackedge ?? empty;
	const alternate = fallthroughBackedge ?? empty;
	return {
		region: {
			kind: 'if',
			header: addr,
			test,
			consequent,
			alternate,
			join: continuation,
			sourceBlocks: new AddressSet([
				addr,
				...consequent.sourceBlocks,
				...alternate.sourceBlocks,
			]),
		},
		continuation,
	};
}

/** A single-entry forwarding arm whose only completion is a loop backedge. */
function structureLoopBackedgeArm(
	from: BlockAddr,
	target: BlockAddr,
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	allowed: AddressSet<BlockAddr>,
): Region | null {
	if (target === loop.header) return loopContinueRegion(from, loop);
	const regions: Region[] = [];
	const seen = new AddressSet<BlockAddr>();
	let previous = from;
	let current = target;
	while (current !== loop.header) {
		if (
			seen.has(current) || !allowed.has(current) ||
			!loop.body.has(current)
		) return null;
		const inLoopPredecessors = new AddressSet(
			[...(cfg.normalPredecessors.get(current) ?? [])].filter((
				predecessor,
			) => loop.body.has(predecessor)),
		);
		if (
			inLoopPredecessors.size !== 1 ||
			!inLoopPredecessors.has(previous)
		) return null;
		const block = cfg.blocks.get(current);
		if (!block || block.terminator.kind !== 'goto') return null;
		seen.add(current);
		regions.push({
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([current]),
		});
		previous = current;
		current = block.terminator.target;
	}
	regions.push(loopContinueRegion(previous, loop));
	return sequenceLoopRegions(regions);
}

/** The same CFG viewed from another entry block. */
function cfgEnteringAt(cfg: ImmutableCFG, entry: BlockAddr): ImmutableCFG {
	if (cfg.entry === entry) return cfg;
	return Object.assign(Object.create(Object.getPrototypeOf(cfg)), cfg, {
		entry,
	}) as ImmutableCFG;
}

function loopContinueRegion(from: BlockAddr, loop: NaturalLoop): Region {
	return {
		kind: 'continue',
		target: loop.header,
		exit: {
			from,
			to: loop.header,
			kind: 'continue',
		},
		sourceBlocks: new AddressSet(),
	};
}

function regionContainsLoop(region: Region, loopId: number): boolean {
	if (region.kind === 'loop' && region.id === loopId) return true;
	switch (region.kind) {
		case 'sequence':
			return region.regions.some((child) =>
				regionContainsLoop(child, loopId)
			);
		case 'if':
			return regionContainsLoop(region.consequent, loopId) ||
				regionContainsLoop(region.alternate, loopId);
		case 'switch':
			return region.cases.some((switchCase) =>
				regionContainsLoop(switchCase.body, loopId)
			) || regionContainsLoop(region.defaultBody, loopId);
		case 'tryCatch':
			return regionContainsLoop(region.body, loopId) ||
				regionContainsLoop(region.handler, loopId);
		case 'tryFinally':
			return regionContainsLoop(region.body, loopId) ||
				regionContainsLoop(region.finalizer, loopId);
		default:
			return false;
	}
}

function uniqueAllowedExit(
	cfg: ImmutableCFG,
	sourceBlocks: AddressSet<BlockAddr>,
	allowed: AddressSet<BlockAddr>,
): BlockAddr | null {
	const exits = new AddressSet<BlockAddr>();
	for (const block of sourceBlocks) {
		for (const succ of cfg.normalSuccessors.get(block) ?? []) {
			if (sourceBlocks.has(succ)) continue;
			if (!allowed.has(succ)) continue;
			exits.add(succ);
		}
	}
	return exits.size === 1 ? [...exits][0] : null;
}

function branchControlRegion(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	exits: LoopRegionExit[],
	addr: BlockAddr,
	allowed: AddressSet<BlockAddr>,
	entryPredicate?: t.Expression,
): { region: Region; continuation?: BlockAddr } | null {
	const block = cfg.blocks.get(addr);
	if (!block || block.terminator.kind !== 'if') return null;

	const fallthroughClass = classifyLoopBodyTarget(
		block.terminator.fallthrough,
		loop,
	);
	const takenClass = classifyLoopBodyTarget(block.terminator.taken, loop);
	if (fallthroughClass.kind === 'body' && takenClass.kind === 'body') {
		return null;
	}
	if (fallthroughClass.kind !== 'body' && takenClass.kind !== 'body') {
		const alternate = loopControlRegion(
			addr,
			fallthroughClass.target,
			loop,
			exits,
		);
		const consequent = loopControlRegion(
			addr,
			takenClass.target,
			loop,
			exits,
		);
		if (!alternate || !consequent) return null;
		return {
			region: {
				kind: 'if',
				header: addr,
				test: t.cloneNode(block.terminator.test, true),
				consequent,
				alternate,
				join: loop.header,
				sourceBlocks: new AddressSet([addr]),
			},
		};
	}

	const control = fallthroughClass.kind === 'body'
		? takenClass
		: fallthroughClass;
	const continuation = fallthroughClass.kind === 'body'
		? block.terminator.fallthrough
		: block.terminator.taken;
	if (!allowed.has(continuation)) return null;

	const loopExit = exits.find((exit) =>
		exit.from === addr && exit.to === control.target
	);
	const controlRegion = loopExit
		? loopExitRegion(loopExit)
		: loopContinueRegion(addr, loop);
	const empty: Region = {
		kind: 'sequence',
		regions: [],
		sourceBlocks: new AddressSet(),
	};
	const controlOnTest = control.target === block.terminator.taken;
	const test = entryPredicate
		? t.logicalExpression(
			'&&',
			t.cloneNode(entryPredicate, true),
			t.cloneNode(block.terminator.test, true),
		)
		: t.cloneNode(block.terminator.test, false);
	return {
		region: {
			kind: 'if',
			header: addr,
			test,
			consequent: controlOnTest ? controlRegion : empty,
			alternate: controlOnTest ? empty : controlRegion,
			join: continuation,
			sourceBlocks: new AddressSet([addr]),
		},
		continuation,
	};
}

function loopControlRegion(
	from: BlockAddr,
	target: BlockAddr,
	loop: NaturalLoop,
	exits: readonly LoopRegionExit[],
): Region | null {
	if (target === loop.header) return loopContinueRegion(from, loop);
	const direct = exits.find((candidate) =>
		candidate.from === from && candidate.to === target
	);
	if (direct) return loopExitRegion(direct);
	const throughTrailer = exits.find((candidate) =>
		candidate.trailer?.sourceBlocks.has(from) &&
		candidate.continuation === target
	);
	if (!throughTrailer) return null;
	return loopExitRegion({
		...throughTrailer,
		from,
		to: target,
		trailer: undefined,
		continuation: undefined,
	});
}

function loopExitRegion(exit: LoopRegionExit): Region {
	if (exit.kind === 'return' || exit.kind === 'throw') {
		return {
			kind: 'terminalReference',
			entry: exit.to,
			exit,
			sourceBlocks: new AddressSet(),
		};
	}
	if (exit.sequenceExit?.label) {
		return {
			kind: 'labelBreak',
			label: exit.sequenceExit.label,
			target: exit.sequenceExit.target,
			exit,
			sourceBlocks: new AddressSet(),
		};
	}
	if (exit.kind === 'labelledBreak' && exit.label) {
		return {
			kind: 'labelBreak',
			label: exit.label,
			target: exit.to,
			exit,
			sourceBlocks: new AddressSet(),
		};
	}
	if (exit.kind === 'labelledContinue' && exit.label) {
		return {
			kind: 'labelContinue',
			label: exit.label,
			target: exit.to,
			exit,
			sourceBlocks: new AddressSet(),
		};
	}
	return {
		kind: exit.kind === 'continue' ? 'continue' : 'break',
		target: exit.to,
		exit,
		sourceBlocks: new AddressSet(),
	};
}

function loopHeaderEntryPredicates(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
): Map<BlockAddr, t.Expression> {
	const predicates = new Map<BlockAddr, t.Expression>();
	const header = cfg.blocks.get(loop.header);
	if (!header || header.terminator.kind !== 'if') return predicates;
	const fallthrough = header.terminator.fallthrough;
	const taken = header.terminator.taken;
	if (
		!loop.body.has(fallthrough) ||
		!loop.body.has(taken) ||
		fallthrough === loop.header ||
		taken === loop.header
	) return predicates;
	if (uniqueLoopLocalExit(cfg, fallthrough, loop) === taken) {
		predicates.set(
			fallthrough,
			invertTest(t.cloneNode(header.terminator.test, true)),
		);
	}
	if (uniqueLoopLocalExit(cfg, taken, loop) === fallthrough) {
		predicates.set(taken, t.cloneNode(header.terminator.test, true));
	}
	return predicates;
}

function uniqueLoopLocalExit(
	cfg: ImmutableCFG,
	entry: BlockAddr,
	loop: NaturalLoop,
): BlockAddr | null {
	const exits = new AddressSet<BlockAddr>();
	const stack = [entry];
	const visited = new AddressSet<BlockAddr>();
	while (stack.length > 0) {
		const addr = stack.pop()!;
		if (visited.has(addr) || !loop.body.has(addr) || addr === loop.header) {
			continue;
		}
		visited.add(addr);
		for (const succ of cfg.normalSuccessors.get(addr) ?? []) {
			if (!loop.body.has(succ) || succ === loop.header) continue;
			if (visited.has(succ)) continue;
			const predecessors = cfg.normalPredecessors.get(succ) ??
				new AddressSet<BlockAddr>();
			if (
				[...predecessors].some((pred) =>
					!visited.has(pred) && pred !== addr
				)
			) {
				exits.add(succ);
				continue;
			}
			stack.push(succ);
		}
	}
	return exits.size === 1 ? [...exits][0] : null;
}

function classifyLoopBodyTarget(
	target: BlockAddr,
	loop: NaturalLoop,
): { kind: 'body' | 'break' | 'continue'; target: BlockAddr } {
	if (target === loop.header) return { kind: 'continue', target };
	if (!loop.body.has(target)) return { kind: 'break', target };
	return { kind: 'body', target };
}

function firstBodyBlock(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
): BlockAddr | null {
	for (const succ of cfg.normalSuccessors.get(loop.header) ?? []) {
		if (loop.body.has(succ) && succ !== loop.header) return succ;
	}
	return null;
}
