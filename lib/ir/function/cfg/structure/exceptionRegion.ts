import * as t from '@babel/types';
import { AddressSet } from '../../../../utils/set.ts';
import {
	type CFGDescriptors,
	edgeKey,
	type ExceptionDescriptor,
	type ExceptionRegionForestNode,
} from '../descriptors/mod.ts';
import { statementFingerprint } from '../descriptors/subgraphMatch.ts';
import type { CFGBlock, CFGEdge, ImmutableCFG } from '../immutableCFG.ts';
import {
	blockNeedsBranchRegion,
	type DeferredExit,
	type EdgeAction,
	type EdgePhiAssignment,
	type Region,
	regionCoveredBlocks,
	regionUnstructuredBranches,
	sequenceRegion,
} from '../regions/region.ts';
import {
	type RegionAt,
	structureStraightLineSequenceFrom,
} from './sequence.ts';
import type { CFGAnalyses } from '../algorithms/mod.ts';
import {
	type RecoveredSwitches,
	tryStructureBoundedScopeForest,
} from './loopForest.ts';
import { tryStructureIfRegion } from './ifRegion.ts';
import { tryStructureSwitchRegion } from './switchRegion.ts';

export function tryStructureExceptionRegion(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
	allowed?: AddressSet<number>,
	structuredHandlers: AddressSet<number> = new AddressSet<number>(),
	analyses?: CFGAnalyses,
	options: { exactScope?: boolean } = {},
): Region | null {
	let descriptor = exceptionStartingAt(
		cfg,
		cfg.entry,
		descriptors,
		allowed,
		true,
	);
	let retryPrelude: number | undefined;
	let protectedEntry: number | undefined;
	if (!descriptor) {
		const block = cfg.blocks.get(cfg.entry);
		if (block?.terminator.kind === 'goto') {
			const candidate = exceptionStartingAt(
				cfg,
				block.terminator.target,
				descriptors,
				allowed,
				true,
			);
			if (
				candidate?.kind === 'catch' &&
				handlerRetryControl(cfg, candidate.handler, cfg.entry)
			) {
				descriptor = candidate;
				retryPrelude = cfg.entry;
				protectedEntry = block.terminator.target;
			}
		}
	}
	if (!descriptor) return null;
	// Already emitted elsewhere in the tree: a continuation block that still
	// carries this descriptor's protectedEntries must not re-open it.
	if (structuredHandlers.has(descriptor.handler)) return null;
	const enclosingFinalizer = descriptor.canonicalFinallyAddress != null &&
			allowed != null &&
			!allowed.has(descriptor.canonicalFinallyAddress)
		? descriptor.canonicalFinallyAddress
		: undefined;

	return structureExceptionDescriptor(
		protectedEntry == null ? cfg : cfgWithEntry(cfg, protectedEntry),
		descriptors,
		descriptor,
		regionAt,
		enclosingFinalizer,
		structuredHandlers,
		analyses,
		retryPrelude,
		allowed,
		options.exactScope === true,
	);
}

function structureExceptionDescriptor(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	descriptor: ExceptionDescriptor,
	regionAt?: RegionAt,
	suppressCatchFinallyHandler?: number,
	structuredHandlers: AddressSet<number> = new AddressSet<number>(),
	analyses?: CFGAnalyses,
	retryPrelude?: number,
	scope?: AddressSet<number>,
	exactScope = false,
): Region {
	structuredHandlers.add(descriptor.handler);
	const ownedCatch = descriptor.kind === 'finally'
		? catchOwnedByFinallyAt(cfg.entry, descriptor, descriptors)
		: null;
	const deferProtectedExits = descriptor.kind === 'finally';
	const body = ownedCatch
		? structureExceptionDescriptor(
			cfg,
			descriptors,
			ownedCatch,
			regionAt,
			descriptor.handler,
			structuredHandlers,
			analyses,
			undefined,
			scope,
			exactScope,
		)
		: structureProtectedBody(
			cfg,
			descriptors,
			descriptor,
			regionAt,
			deferProtectedExits,
			structuredHandlers,
			analyses,
			exactScope ? scope : undefined,
		);
	let normalizedBody = body ?? {
		kind: 'sequence' as const,
		regions: [],
		sourceBlocks: new AddressSet(),
	};
	const finalizerEntry = descriptor.kind === 'finally'
		? preferredFinallyBodyEntry(descriptor, false)
		: descriptor.handler;
	const retryLoop = descriptor.kind === 'catch'
		? exceptionRetryLoop(cfg, descriptor, retryPrelude)
		: undefined;
	let handlerBodyBlocks = descriptor.kind === 'finally'
		? expandedFinallyBodyBlocks(
			cfg,
			descriptor,
			descriptors,
			finalizerEntry,
		)
		: expandedCatchBodyBlocks(
			cfg,
			descriptor,
			descriptors,
			retryLoop == null ? undefined : new AddressSet([
				retryLoop.header,
				retryLoop.normalExit,
			]),
		);
	if (descriptor.kind === 'catch') {
		addNestedCatchHandlers(
			cfg,
			handlerBodyBlocks,
			descriptor,
			descriptors,
		);
		removeCatchPostFinallyBlocks(
			cfg,
			handlerBodyBlocks,
			descriptor,
			descriptors,
		);
	}
	// Finally bodies have exact lexical ownership. Catch landing pads normally
	// expand beyond a normal-flow scope, but a bounded forest supplies the whole
	// ownership set explicitly and must not absorb its shared continuation.
	if (scope && (descriptor.kind === 'finally' || exactScope)) {
		const scopedHandlerBody = handlerBodyBlocks.intersection(scope);
		handlerBodyBlocks = descriptor.kind === 'catch' && exactScope
			? exactScopedCatchBodyBlocks(
				cfg,
				descriptor.handler,
				handlerBodyBlocks,
				scopedHandlerBody,
				scope,
			)
			: scopedHandlerBody;
	}
	let handler = descriptor.kind === 'finally'
		? structureFinallyHandlerBody(
			cfg,
			descriptors,
			descriptor,
			finalizerEntry,
			handlerBodyBlocks,
			regionAt,
			structuredHandlers,
			analyses,
		)
		: structureCatchHandlerBody(
			cfg,
			descriptors,
			descriptor,
			handlerBodyBlocks,
			regionAt,
			structuredHandlers,
			analyses,
			retryLoop?.conditionalExit == null ? retryLoop?.header : undefined,
			exactScope,
		);
	if (retryLoop?.conditionalExit) {
		handler = demoteConditionalRetryDecision(
			handler,
			retryLoop.conditionalExit.decision,
		);
	}
	if (descriptor.kind === 'catch') {
		const sharedContinuation = sharedCatchContinuation(
			cfg,
			descriptor,
			normalizedBody,
			handler,
		);
		if (
			sharedContinuation != null &&
			hasLexicalContinuationSuffix(normalizedBody, sharedContinuation)
		) {
			normalizedBody = detachContinuationSuffix(
				normalizedBody,
				sharedContinuation,
			) ?? sequenceRegion([]);
		}
	}
	// A retry loop already routes the pad back into the protected range, so its
	// continuation is the retry's own exit rather than an enclosing loop's.
	if (descriptor.kind === 'catch' && analyses && retryLoop == null) {
		const padBreak = catchLoopBreakRegion(
			cfg,
			descriptors,
			descriptor,
			handlerBodyBlocks,
			analyses,
		);
		if (padBreak) handler = sequenceRegion([handler, padBreak]);
	}
	if (descriptor.kind === 'finally') {
		normalizedBody = nestEarlyFinalizerExit(
			normalizedBody,
			descriptor,
		);
		normalizedBody = stripNormalFinallyCopyFallthrough(
			normalizedBody,
			descriptor,
		);
	}
	const sourceBlocks = new AddressSet([
		...normalizedBody.sourceBlocks,
		...handler.sourceBlocks,
		...(retryPrelude == null ? [] : [retryPrelude]),
		...(retryLoop?.abruptExits ?? []),
	]);

	if (descriptor.kind === 'finally') {
		const normalExitCandidates = normalFinalizerCopyContinuations(
			cfg,
			descriptor,
			normalizedBody.sourceBlocks,
		);
		return {
			kind: 'tryFinally',
			body: normalizedBody,
			finalizer: handler,
			handlerAddress: descriptor.handler,
			protectedBlocks: new AddressSet(descriptor.protectedBlocks),
			normalExit: normalExitCandidates[0],
			normalExitCandidates,
			sourceBlocks,
			deferredExits: finalizerDeferredExits(cfg, descriptors, descriptor),
			finallyCopyKinds: descriptor.finallyCopies.map((copy) =>
				`${copy.kind}:0x${copy.copyRoot.toString(16)}`
			),
		};
	}
	const tryCatchRegion: Region = {
		kind: 'tryCatch',
		body: normalizedBody,
		handler,
		handlerAddress: descriptor.handler,
		protectedBlocks: new AddressSet(descriptor.protectedBlocks),
		retryLoop,
		sourceBlocks,
	};
	const finalizerDescriptor = descriptor.canonicalFinallyAddress == null ||
			descriptor.canonicalFinallyAddress === suppressCatchFinallyHandler
		? null
		: descriptors.exceptions.handlerByAddress.get(
			descriptor.canonicalFinallyAddress,
		) ?? null;
	if (finalizerDescriptor?.kind !== 'finally') return tryCatchRegion;

	const nestedFinalizerEntry = preferredFinallyBodyEntry(
		finalizerDescriptor,
		false,
	);
	const nestedNormalExitCandidates = normalFinalizerCopyContinuations(
		cfg,
		finalizerDescriptor,
		tryCatchRegion.sourceBlocks,
	);
	const nestedFinalizer = nestedFinalizerEntry !== finalizerDescriptor.handler
		? {
			kind: 'basic' as const,
			body: [],
			sourceBlocks: new AddressSet([nestedFinalizerEntry]),
		}
		: (structuredHandlers.add(finalizerDescriptor.handler),
			structureFinallyHandlerBody(
				cfg,
				descriptors,
				finalizerDescriptor,
				nestedFinalizerEntry,
				expandedFinallyBodyBlocks(
					cfg,
					finalizerDescriptor,
					descriptors,
					nestedFinalizerEntry,
				),
				regionAt,
				structuredHandlers,
				analyses,
			));
	return {
		kind: 'tryFinally',
		body: tryCatchRegion,
		finalizer: nestedFinalizer,
		handlerAddress: finalizerDescriptor.handler,
		protectedBlocks: new AddressSet(descriptor.protectedBlocks),
		normalExit: nestedNormalExitCandidates[0],
		normalExitCandidates: nestedNormalExitCandidates,
		sourceBlocks: new AddressSet([
			...tryCatchRegion.sourceBlocks,
			...nestedFinalizer.sourceBlocks,
		]),
		deferredExits: finalizerDeferredExits(
			cfg,
			descriptors,
			finalizerDescriptor,
		),
		finallyCopyKinds: finalizerDescriptor.finallyCopies.map((copy) =>
			`${copy.kind}:0x${copy.copyRoot.toString(16)}`
		),
	};
}

/**
 * Exact protected scopes bound the catch landing pad to the enclosing body, but
 * a handler can still own the normal continuation blocks reached only by that
 * landing pad. Grow from the scoped landing pad through blocks reached only by
 * retained handler blocks. If a suffix leaves the catch body, keep it only when
 * it exits to the exact enclosing scope (for example an async catch flowing into
 * its finally copy); otherwise prune it so a catch cannot swallow a shared
 * continuation outside the bounded arm. The landing pad stays represented even
 * when its branch remains outside the exact scope.
 */
function exactScopedCatchBodyBlocks(
	cfg: ImmutableCFG,
	handler: number,
	handlerBodyBlocks: AddressSet<number>,
	scopedHandlerBody: AddressSet<number>,
	scope: AddressSet<number>,
): AddressSet<number> {
	const retained = new AddressSet(scopedHandlerBody);
	if (handlerBodyBlocks.has(handler)) retained.add(handler);
	for (let changed = true; changed;) {
		changed = false;
		for (const block of handlerBodyBlocks) {
			if (retained.has(block)) continue;
			const predecessors = cfg.normalPredecessors.get(block) ??
				new AddressSet<number>();
			if (predecessors.size === 0) continue;
			if (!predecessors.isSubsetOf(handlerBodyBlocks)) continue;
			if (!predecessors.isSubsetOf(retained)) continue;
			retained.add(block);
			changed = true;
		}
	}
	for (let changed = true; changed;) {
		changed = false;
		for (const block of [...retained]) {
			if (block === handler) continue;
			const successors = cfg.normalSuccessors.get(block) ??
				new AddressSet<number>();
			if (
				[...successors].every((successor) =>
					retained.has(successor) || scope.has(successor)
				)
			) {
				continue;
			}
			retained.delete(block);
			changed = true;
		}
	}
	return retained;
}

/**
 * A branch at the start of a protected body may skip the natural loop that
 * follows it and jump straight to a finalizer copy. The bounded body builder
 * represents that edge as a deferred loop exit followed by the loop, which
 * emits an unsyntactic bare `break`. Nest the suffix under the continuing arm
 * instead: falling out of the other arm leaves the `try` normally, so JavaScript
 * runs the surrounding `finally` exactly once.
 */
function nestEarlyFinalizerExit(
	region: Region,
	descriptor: ExceptionDescriptor,
): Region {
	if (region.kind !== 'sequence' || region.regions.length < 2) return region;
	const [prefix, ...suffixParts] = region.regions;
	if (prefix.kind !== 'if' || prefix.join == null) return region;
	const suffix = sequenceRegion(suffixParts);
	if (!suffix.sourceBlocks.has(prefix.join)) return region;
	const copyBlocks = new AddressSet<number>(
		descriptor.finallyCopies.flatMap((copy) =>
			copy.copyBlocks ?? [copy.copyRoot]
		),
	);
	const asNormalExit = (arm: Region): Region | null => {
		if (
			arm.kind !== 'deferredExit' ||
			arm.exit.kind !== 'loopExit' ||
			!copyBlocks.has(arm.exit.target) ||
			arm.sourceBlocks.size !== 0
		) return null;
		return {
			...arm,
			exit: { ...arm.exit, kind: 'toJoin' },
		};
	};
	const consequentExit = asNormalExit(prefix.consequent);
	const alternateExit = asNormalExit(prefix.alternate);
	if ((consequentExit == null) === (alternateExit == null)) return region;
	return {
		...prefix,
		consequent: consequentExit ?? suffix,
		alternate: alternateExit ?? suffix,
		join: undefined,
		sourceBlocks: new AddressSet(region.sourceBlocks),
	};
}

/**
 * A normal finalizer copy is the bytecode edge by which the protected body
 * falls through into source-level `finally`. When expanded protected-body
 * ownership reaches that copy, the bounded forest represents it as a deferred
 * loop exit; emitting the marker produces a bare `break` even though no source
 * loop exists. Remove only a tail made entirely from the descriptor's proven
 * normal-copy blocks. Nested Loop/exception Regions keep their own control.
 */
function stripNormalFinallyCopyFallthrough(
	region: Region,
	descriptor: ExceptionDescriptor,
): Region {
	const normalCopyBlocks = new AddressSet<number>(
		descriptor.finallyCopies
			.filter((copy) => copy.kind === 'normalExit')
			.flatMap((copy) => copy.copyBlocks ?? [copy.copyRoot]),
	);
	if (normalCopyBlocks.size === 0) return region;
	const rewrite = (
		candidate: Region,
	): { region: Region; removed: AddressSet<number> } => {
		if (
			candidate.kind === 'deferredExit' &&
			candidate.exit.kind === 'loopExit' &&
			normalCopyBlocks.has(candidate.exit.target) &&
			candidate.sourceBlocks.isSubsetOf(normalCopyBlocks)
		) {
			return {
				region: {
					kind: 'sequence',
					regions: [],
					sourceBlocks: new AddressSet(),
				},
				removed: new AddressSet(candidate.sourceBlocks),
			};
		}
		const finish = (
			next: Region,
			removed: AddressSet<number>,
		) => ({
			region: {
				...next,
				sourceBlocks: next.sourceBlocks.difference(removed),
			} as Region,
			removed,
		});
		switch (candidate.kind) {
			case 'sequence': {
				const children = candidate.regions.map(rewrite);
				const removed = new AddressSet<number>(
					children.flatMap((child) => [...child.removed]),
				);
				return finish({
					...candidate,
					regions: children.map((child) => child.region),
				}, removed);
			}
			case 'if': {
				const consequent = rewrite(candidate.consequent);
				const alternate = rewrite(candidate.alternate);
				const removed = consequent.removed.union(alternate.removed);
				return finish({
					...candidate,
					consequent: consequent.region,
					alternate: alternate.region,
				}, removed);
			}
			case 'switch': {
				const cases = candidate.cases.map((item) => ({
					...item,
					mapped: rewrite(item.body),
				}));
				const defaultBody = rewrite(candidate.defaultBody);
				const removed = new AddressSet<number>([
					...cases.flatMap((item) => [...item.mapped.removed]),
					...defaultBody.removed,
				]);
				return finish({
					...candidate,
					cases: cases.map(({ mapped, ...item }) => ({
						...item,
						body: mapped.region,
					})),
					defaultBody: defaultBody.region,
				}, removed);
			}
			default:
				return { region: candidate, removed: new AddressSet() };
		}
	};
	return rewrite(region).region;
}

/** The retry emitter owns this branch so it can place both edge Phi copies. */
function demoteConditionalRetryDecision(
	region: Region,
	decision: number,
): Region {
	if (region.kind === 'if' && region.header === decision) {
		return {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([decision]),
		};
	}
	if (region.kind !== 'sequence') return region;
	return {
		...region,
		regions: region.regions.map((child) =>
			demoteConditionalRetryDecision(child, decision)
		),
	};
}

/**
 * Recognize an exception-driven retry loop.
 *
 * This shape has no normal backedge in the protected body: successful work
 * leaves the loop, while the catch landing pad alone jumps back to the protected
 * header. Consequently it is intentionally absent from the natural-loop forest.
 * Keep this proof narrow: the handler must itself be the unique normal backedge,
 * and all ordinary protected exits must agree on one continuation.
 */
function exceptionRetryLoop(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	retryPrelude?: number,
): Extract<Region, { kind: 'tryCatch' }>['retryLoop'] {
	// A catch owned by a canonical finally is emitted through the combined
	// try/catch/finally path, which has different retry/finalization ordering.
	// Leave that composite to a dedicated recognizer rather than moving its
	// finalizer inside or outside the retry loop by accident.
	if (
		descriptor.kind !== 'catch' ||
		descriptor.canonicalFinallyAddress != null
	) return undefined;
	if (!descriptor.protectedEntries.has(cfg.entry)) return undefined;
	const retryHeader = retryPrelude ?? cfg.entry;
	const retry = handlerRetryControl(cfg, descriptor.handler, retryHeader);
	if (!retry) return undefined;

	const exits = new AddressSet<number>();
	for (const block of descriptor.protectedBlocks) {
		for (const successor of cfg.normalSuccessors.get(block) ?? []) {
			if (descriptor.protectedBlocks.has(successor)) continue;
			exits.add(successor);
		}
	}
	let normalExit: number;
	// A retry decision whose other arm rejoins the protected body's own
	// continuation is the loop's `break`: the emitter lowers that arm to one.
	const conditionalExit = retry.exit && exits.has(retry.exit.to)
		? retry.exit
		: undefined;
	if (conditionalExit) {
		// Other protected exits are allowed only when they are explicit abrupt
		// completions (for example an AbortSignal early return). They do not join
		// the successful retry-loop continuation.
		for (const exit of exits) {
			if (exit === conditionalExit.to) continue;
			const terminator = cfg.blocks.get(exit)?.terminator;
			if (
				terminator?.kind !== 'return' && terminator?.kind !== 'throw' &&
				terminator?.kind !== 'unreachable'
			) return undefined;
		}
		normalExit = conditionalExit.to;
	} else {
		// The decision rethrows on its other arm instead of leaving the loop.
		// That arm is a catch-body block the handler Region owns and emits, so
		// the retry is the catch's own fallthrough and the protected body's
		// single exit is the loop's continuation.
		if (retry.exit && !isAbruptTerminalBlock(cfg, retry.exit.to)) {
			return undefined;
		}
		if (exits.size !== 1) return undefined;
		normalExit = [...exits][0];
	}
	if (normalExit === cfg.entry || normalExit === descriptor.handler) {
		return undefined;
	}
	return {
		header: retryHeader,
		prelude: retryPrelude,
		normalExit,
		abruptExits: [...exits].filter((exit) => exit !== normalExit),
		backedge: retry.backedge,
		conditionalExit: conditionalExit
			? { decision: retry.backedge.from, exit: conditionalExit }
			: undefined,
	};
}

/**
 * Find either a direct catch backedge or a bounded conditional retry trailer.
 *
 * The trailer may test more than once before retrying: Hermes emits
 * `catch (e) { if (++n >= limit) throw e; …; if (retryable) continue; throw e }`
 * as a chain of decisions whose non-retrying arm leaves the function outright.
 * Such an arm cannot be the retry loop's continuation, so the chain is walked
 * through it while the other arm remains the only way back to the header.
 */
function handlerRetryControl(
	cfg: ImmutableCFG,
	handler: number,
	header: number,
): { backedge: CFGEdge; exit?: CFGEdge } | null {
	const seen = new AddressSet<number>();
	let cursor = handler;
	while (seen.size <= 16 && !seen.has(cursor)) {
		seen.add(cursor);
		const block = cfg.blocks.get(cursor);
		if (!block) return null;
		if (block.terminator.kind === 'goto') {
			if (block.terminator.target === header) {
				return {
					backedge: { from: cursor, to: header, kind: 'normal' },
				};
			}
			cursor = block.terminator.target;
			continue;
		}
		if (block.terminator.kind !== 'if') return null;
		const retriesOnTaken = block.terminator.taken === header;
		const retriesOnFallthrough = block.terminator.fallthrough === header;
		if (retriesOnTaken === retriesOnFallthrough) {
			const guarded = abruptGuardContinuation(cfg, block);
			if (guarded == null) return null;
			cursor = guarded;
			continue;
		}
		const exitTarget = retriesOnTaken
			? block.terminator.fallthrough
			: block.terminator.taken;
		return {
			backedge: { from: cursor, to: header, kind: 'normal' },
			exit: { from: cursor, to: exitTarget, kind: 'normal' },
		};
	}
	return null;
}

/**
 * The arm a rethrow guard continues on: one arm leaves the function outright,
 * so the other is the only path the guard can take. A decision whose arms both
 * continue is an ordinary two-way branch and is not part of a retry trailer.
 */
function abruptGuardContinuation(
	cfg: ImmutableCFG,
	block: CFGBlock,
): number | null {
	if (block.terminator.kind !== 'if') return null;
	const { taken, fallthrough } = block.terminator;
	if (taken === fallthrough) return null;
	const takenLeaves = isAbruptTerminalBlock(cfg, taken);
	const fallthroughLeaves = isAbruptTerminalBlock(cfg, fallthrough);
	if (takenLeaves === fallthroughLeaves) return null;
	return takenLeaves ? fallthrough : taken;
}

/** A block that ends the function on every path through it. */
function isAbruptTerminalBlock(cfg: ImmutableCFG, address: number): boolean {
	const terminator = cfg.blocks.get(address)?.terminator;
	return terminator?.kind === 'return' || terminator?.kind === 'throw' ||
		terminator?.kind === 'unreachable';
}

/**
 * Find the first normal continuation reached by both a protected body and its
 * catch handler. It belongs after the try/catch, not inside the protected arm.
 *
 * Contracted exception Regions are built without their surrounding branch, so
 * a recursive body walk can otherwise append the shared continuation to the
 * protected body. That gives the contracted node a second normal entry and
 * prevents the enclosing continuation forest from representing the real join.
 */
function sharedCatchContinuation(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	body: Region,
	handler: Region,
): number | undefined {
	const handlerReachable = normalReachableWithin(
		cfg,
		handler.sourceBlocks,
	);
	const queue = [...handler.sourceBlocks];
	const seen = new AddressSet<number>();
	while (queue.length > 0) {
		const candidate = queue.shift()!;
		if (seen.has(candidate)) continue;
		seen.add(candidate);
		if (
			body.sourceBlocks.has(candidate) &&
			!descriptor.protectedBlocks.has(candidate)
		) {
			return candidate;
		}
		for (const successor of cfg.normalSuccessors.get(candidate) ?? []) {
			if (handlerReachable.has(successor) && !seen.has(successor)) {
				queue.push(successor);
			}
		}
	}
	return undefined;
}

function normalReachableWithin(
	cfg: ImmutableCFG,
	entries: AddressSet<number>,
): AddressSet<number> {
	const reachable = new AddressSet<number>();
	const queue = [...entries];
	while (queue.length > 0) {
		const address = queue.shift()!;
		if (reachable.has(address)) continue;
		reachable.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (!reachable.has(successor)) queue.push(successor);
		}
	}
	return reachable;
}

/**
 * Whether `target` begins a lexical sequence suffix rather than occurring
 * inside path-specific control. The latter cannot be detached without also
 * deleting the other branch or loop path that shares its containing Region.
 */
function hasLexicalContinuationSuffix(
	region: Region,
	target: number,
): boolean {
	if (!region.sourceBlocks.has(target)) return true;
	if (region.kind !== 'sequence') {
		return region.sourceBlocks.size === 1 &&
			region.sourceBlocks.has(target);
	}
	const child = region.regions.find((candidate) =>
		candidate.sourceBlocks.has(target)
	);
	return child != null && hasLexicalContinuationSuffix(child, target);
}

/**
 * Remove a continuation and every Region sequenced after it. This deliberately
 * accepts only a lexical sequence path: trimming through a branch/loop/handler
 * would discard path-specific work without proving where the join begins.
 */
function detachContinuationSuffix(
	region: Region,
	target: number,
): Region | null {
	if (!region.sourceBlocks.has(target)) return region;
	if (region.kind !== 'sequence') {
		if (region.sourceBlocks.size === 1 && region.sourceBlocks.has(target)) {
			return null;
		}
		return null;
	}

	const regions: Region[] = [];
	for (const child of region.regions) {
		if (!child.sourceBlocks.has(target)) {
			regions.push(child);
			continue;
		}
		const trimmed = detachContinuationSuffix(child, target);
		if (trimmed) regions.push(trimmed);
		break;
	}
	return sequenceRegion(regions);
}

function structureFinallyHandlerBody(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	descriptor: ExceptionDescriptor,
	finalizerEntry: number,
	handlerBodyBlocks: AddressSet<number>,
	regionAt?: RegionAt,
	structuredHandlers: AddressSet<number> = new AddressSet<number>(),
	analyses?: CFGAnalyses,
): Region {
	const regions: Region[] = [];
	const consumed = new AddressSet<number>();
	const append = (region: Region) => {
		if (region.sourceBlocks.isSubsetOf(consumed)) return;
		regions.push(region);
		for (const block of region.sourceBlocks) consumed.add(block);
	};

	const canonical = containedRegion(
		regionAt?.(finalizerEntry, handlerBodyBlocks),
		handlerBodyBlocks,
	) ?? structureStraightLineSequenceFrom(
		cfg,
		finalizerEntry,
		handlerBodyBlocks,
		(childEntry, allowed) => {
			if (childEntry === finalizerEntry) return null;
			const nestedDescriptor = exceptionStartingAt(
				cfg,
				childEntry,
				descriptors,
				allowed,
			);
			if (
				nestedDescriptor &&
				nestedDescriptor.handler !== descriptor.handler &&
				!structuredHandlers.has(nestedDescriptor.handler)
			) {
				return structureExceptionDescriptor(
					cfgWithEntry(cfg, childEntry),
					descriptors,
					nestedDescriptor,
					regionAt,
					undefined,
					structuredHandlers,
					analyses,
				);
			}
			return regionAt?.(childEntry, allowed) ?? null;
		},
	) ?? {
		kind: 'basic',
		body: [],
		sourceBlocks: new AddressSet([finalizerEntry]),
	};
	append(canonical);

	for (
		const entry of finalizerContinuationEntries(
			cfg,
			descriptor,
			handlerBodyBlocks,
			consumed,
		)
	) {
		const continuation = regionAt?.(entry, handlerBodyBlocks) ??
			structureStraightLineSequenceFrom(
				cfg,
				entry,
				handlerBodyBlocks,
				(childEntry, allowed) =>
					childEntry === entry
						? null
						: regionAt?.(childEntry, allowed) ?? null,
			);
		if (continuation) append(continuation);
	}

	return regions.length === 1 ? regions[0] : {
		kind: 'sequence',
		regions,
		sourceBlocks: consumed,
	};
}

function finalizerContinuationEntries(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	handlerBodyBlocks: AddressSet<number>,
	consumed: AddressSet<number>,
): number[] {
	return [...handlerBodyBlocks].filter((entry) =>
		entry !== descriptor.handler &&
		!descriptor.protectedBlocks.has(entry) &&
		!consumed.has(entry) && cfg.blocks.has(entry)
	).toSorted((left, right) => left - right);
}

function preferredFinallyBodyEntry(
	descriptor: ExceptionDescriptor,
	preferPreHandlerCopy: boolean,
): number {
	const preHandlerCopy =
		[...descriptor.finallyCopies].filter((copy) =>
			copy.copyRoot < descriptor.handler
		).toSorted((left, right) => left.copyRoot - right.copyRoot)[0];
	const explicit = descriptor.finallyBodyBlocks?.[0];
	if (preferPreHandlerCopy && preHandlerCopy != null) {
		return preHandlerCopy.copyRoot;
	}
	return explicit ?? preHandlerCopy?.copyRoot ?? descriptor.handler;
}

function structureCatchHandlerBody(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	descriptor: ExceptionDescriptor,
	handlerBodyBlocks: AddressSet<number>,
	regionAt?: RegionAt,
	structuredHandlers: AddressSet<number> = new AddressSet<number>(),
	analyses?: CFGAnalyses,
	/**
	 * The protected header the catch retries at. It belongs to the retry loop
	 * that wraps the whole try/catch, so an arm reaching it leaves the catch
	 * body rather than owning the protected blocks a second time.
	 */
	retryHeader?: number,
	exactScope = false,
): Region {
	const regions: Region[] = [];
	const consumed = new AddressSet<number>();
	const append = (region: Region) => {
		if (region.sourceBlocks.isSubsetOf(consumed)) return;
		regions.push(region);
		for (const block of region.sourceBlocks) consumed.add(block);
	};
	const structureChild = (
		childEntry: number,
		allowed: AddressSet<number> | undefined,
	): Region | null => {
		const childAllowed = allowed ?? handlerBodyBlocks;
		const exceptionLoop = tryStructureCatchExceptionLoop(
			childEntry,
			cfg,
			descriptors,
			descriptor,
			childAllowed,
			regionAt,
			structuredHandlers,
			analyses,
		);
		if (exceptionLoop) return exceptionLoop;
		const nested = exceptionStartingAt(
			cfg,
			childEntry,
			descriptors,
			childAllowed,
		);
		if (
			nested && nested !== descriptor &&
			!structuredHandlers.has(nested.handler)
		) {
			return structureExceptionDescriptor(
				cfgWithEntry(cfg, childEntry),
				descriptors,
				nested,
				regionAt,
				undefined,
				structuredHandlers,
				analyses,
			);
		}
		return containedRegion(
			regionAt?.(childEntry, childAllowed),
			childAllowed,
		);
	};
	const catchRegionAt: RegionAt = (childEntry, allowed) =>
		tryStructureCatchExceptionLoop(
			childEntry,
			cfg,
			descriptors,
			descriptor,
			allowed ?? handlerBodyBlocks,
			regionAt,
			structuredHandlers,
			analyses,
		) ?? regionAt?.(childEntry, allowed ?? handlerBodyBlocks) ?? null;

	// A catch body is a bounded CFG in exactly the same sense as a protected
	// body. In particular, a landing pad can feed a branch, a natural loop, or a
	// nested try whose join is still inside the catch. The generic Region builder
	// may return only the landing-pad prefix when the nested exceptional edges
	// prevent it from proving a weak SESE. Try the edge-aware bounded DAG builder
	// before accepting that prefix: it composes branches itself and delegates
	// loops/nested exception ranges back to `regionAt`.
	//
	// This is also what makes exceptional Phis usable. Their mutable state is
	// placed correctly on entry to protected blocks, but the handler Phi cannot
	// be removed unless the Region owns the handler joins that consume it.
	const handlersBeforeCatchDAG = new AddressSet(structuredHandlers);
	const catchDAG = structureProtectedDAGFrom(
		cfgWithEntry(cfg, descriptor.handler),
		descriptors,
		descriptor,
		descriptor.handler,
		handlerBodyBlocks,
		new AddressSet(),
		retryHeader,
		false,
		new AddressSet(),
		new AddressSet(),
		catchRegionAt,
		structuredHandlers,
		analyses,
		exactScope ? handlerBodyBlocks : undefined,
	);
	if (
		catchDAG &&
		handlerBodyBlocks.isSubsetOf(catchDAG.sourceBlocks) &&
		(!exactScope || catchDAG.sourceBlocks.isSubsetOf(handlerBodyBlocks)) &&
		regionCoversNormalCycles(cfg, handlerBodyBlocks, catchDAG)
	) return catchDAG;
	// The DAG attempt is speculative. A nested handler it structured belongs to
	// the discarded candidate until a later handler-body path commits it.
	for (const handler of [...structuredHandlers]) {
		if (!handlersBeforeCatchDAG.has(handler)) {
			structuredHandlers.delete(handler);
		}
	}
	const catchForest = tryStructureCatchScopeForest(
		cfg,
		descriptors,
		descriptor,
		handlerBodyBlocks,
		regionAt,
		structuredHandlers,
		analyses,
	);
	if (
		catchForest &&
		handlerBodyBlocks.isSubsetOf(catchForest.sourceBlocks) &&
		(!exactScope || catchForest.sourceBlocks.isSubsetOf(handlerBodyBlocks))
	) return catchForest;

	// A landing pad that branches has no straight line to walk: the builder
	// below asks for a child Region at the handler itself, which must decline to
	// avoid recursing, so the walk stops and the pad becomes a Basic Region that
	// owns the branch and drops everything under it. Structure it recursively
	// instead, bounded to the handler body.
	const branchingPad = blockNeedsBranchRegion(descriptor.handler, cfg)
		? containedRegion(
			regionAt?.(descriptor.handler, handlerBodyBlocks),
			handlerBodyBlocks,
		)
		: null;
	const landingPad = branchingPad ?? structureStraightLineSequenceFrom(
		cfg,
		descriptor.handler,
		handlerBodyBlocks,
		(childEntry, allowed) =>
			childEntry === descriptor.handler
				? null
				: structureChild(childEntry, allowed),
	) ?? {
		kind: 'basic' as const,
		body: [],
		sourceBlocks: new AddressSet([descriptor.handler]),
	};
	append(landingPad);

	for (
		const entry of catchContinuationEntries(descriptor, handlerBodyBlocks)
	) {
		if (consumed.has(entry)) continue;
		const structured = containedRegion(
			regionAt?.(entry, handlerBodyBlocks),
			handlerBodyBlocks,
		) ??
			structureStraightLineSequenceFrom(
				cfg,
				entry,
				handlerBodyBlocks,
				(childEntry, allowed) =>
					childEntry === entry
						? null
						: structureChild(childEntry, allowed),
			);
		if (structured) append(structured);
	}

	if (regions.length === 0) {
		return {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([descriptor.handler]),
		};
	}
	if (regions.length === 1) return regions[0];
	return {
		kind: 'sequence',
		regions,
		sourceBlocks: consumed,
	};
}

/**
 * Leave the enclosing loop when the landing pad's only continuation is that
 * loop's own exit target.
 *
 * Hermes compiles `for (…) { try { … } catch (e) { … break } }` with the pad
 * outside the loop body: nothing branches to a pad, so it is not a body block,
 * and its normal successor is the block the loop breaks to. The catch Region is
 * a child of the loop body, so ending the catch there would fall into the next
 * iteration instead of leaving the loop. Naming the edge as the loop's `break`
 * both restores the transfer and gives the edge's Phi actions their site.
 */
function catchLoopBreakRegion(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	descriptor: ExceptionDescriptor,
	handlerBodyBlocks: AddressSet<number>,
	analyses: CFGAnalyses,
): Region | null {
	let edge: CFGEdge | undefined;
	for (const block of handlerBodyBlocks) {
		for (const successor of cfg.normalSuccessors.get(block) ?? []) {
			if (handlerBodyBlocks.has(successor)) continue;
			// Two continuations are a branch out of the pad, which the catch
			// body owns itself; only a single transfer is this loop's break.
			if (edge) return null;
			edge = { from: block, to: successor, kind: 'normal' };
		}
	}
	if (!edge) return null;
	// The innermost loop holding a protected entry is the one the catch Region
	// is lexically inside, so it is the loop an unlabelled `break` leaves.
	const owner = analyses.naturalLoops.loops
		.filter((loop) =>
			[...descriptor.protectedEntries].some((entry) =>
				loop.body.has(entry)
			)
		)
		.toSorted((left, right) => left.body.size - right.body.size)[0];
	if (!owner) return null;
	// The loop has to own the whole protected range: only then is the try a
	// child of its body. A nested landing pad inside the range is exempt for
	// the same reason this pad is — no normal edge reaches it.
	for (const block of descriptor.protectedBlocks) {
		if (owner.body.has(block)) continue;
		if (descriptors.exceptions.handlerByAddress.has(block)) continue;
		return null;
	}
	if (owner.body.has(edge.to)) return null;
	for (const block of handlerBodyBlocks) {
		if (owner.body.has(block)) return null;
	}
	// The continuation must be where this loop already leaves: breaking to a
	// block no body edge reaches would name an enclosing loop's exit.
	let breaksTo = false;
	for (const block of owner.body) {
		if (cfg.normalSuccessors.get(block)?.has(edge.to)) breaksTo = true;
	}
	if (!breaksTo) return null;
	return {
		kind: 'break',
		target: edge.to,
		exit: { from: edge.from, to: edge.to, kind: 'break' },
		sourceBlocks: new AddressSet(),
	};
}

/**
 * Recover a normal loop whose body contains a catch that rejoins its latch.
 *
 * The dominator tree cannot classify this as a natural loop: the exceptional
 * landing pad appears to be a second entry into the latch. The normal SCC still
 * proves the cyclic core, and the nested exception descriptor proves that the
 * apparent second entry belongs to a lexical try/catch inside the loop body.
 */
function tryStructureCatchExceptionLoop(
	entry: number,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	owner: ExceptionDescriptor,
	allowed: AddressSet<number>,
	regionAt: RegionAt | undefined,
	structuredHandlers: AddressSet<number>,
	analyses: CFGAnalyses | undefined,
): Extract<Region, { kind: 'loop' }> | null {
	if (!analyses || !regionAt || !allowed.has(entry)) return null;
	if (analyses.naturalLoops.loopByHeader.has(entry)) return null;
	const componentIndex = analyses.sccs.componentOf.get(entry);
	if (componentIndex == null) return null;
	const core = analyses.sccs.components[componentIndex];
	if (core.size < 2 || !core.isSubsetOf(allowed)) return null;
	const header = cfg.blocks.get(entry);
	if (header?.terminator.kind !== 'goto') return null;
	const bodyEntry = header.terminator.target;
	if (!core.has(bodyEntry)) return null;
	const latches = [...(cfg.normalPredecessors.get(entry) ?? [])].filter(
		(predecessor) => core.has(predecessor),
	);
	if (latches.length !== 1) return null;

	const exitEdges: Array<{ from: number; to: number }> = [];
	for (const from of core) {
		for (const to of cfg.normalSuccessors.get(from) ?? []) {
			if (!core.has(to)) exitEdges.push({ from, to });
		}
	}
	if (
		exitEdges.length === 0 ||
		exitEdges.some(({ from }) => !latches.includes(from))
	) return null;
	const continuation = exitEdges[0]!.to;
	if (exitEdges.some(({ to }) => to !== continuation)) return null;
	for (const latch of latches) {
		const terminator = cfg.blocks.get(latch)?.terminator;
		if (
			terminator?.kind !== 'if' ||
			!([terminator.fallthrough, terminator.taken].includes(entry)) ||
			!([terminator.fallthrough, terminator.taken].includes(continuation))
		) return null;
	}

	const nested = exceptionStartingAt(cfg, bodyEntry, descriptors, allowed);
	if (!nested || nested === owner || structuredHandlers.has(nested.handler)) {
		return null;
	}
	if (!nested.protectedBlocks.isSubsetOf(core)) return null;
	const handlersBeforeLoop = new AddressSet(structuredHandlers);
	const restoreHandlers = () =>
		restoreStructuredHandlers(structuredHandlers, handlersBeforeLoop);
	const nestedBody = structureExceptionDescriptor(
		cfgWithEntry(cfg, bodyEntry),
		descriptors,
		nested,
		regionAt,
		undefined,
		structuredHandlers,
		analyses,
	);
	const body = sequenceRegion([
		nestedBody,
		{
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet(latches),
		},
	]);
	const requiredBody = new AddressSet(core);
	requiredBody.delete(entry);
	if (
		!requiredBody.isSubsetOf(body.sourceBlocks) ||
		!body.sourceBlocks.isSubsetOf(allowed) ||
		body.sourceBlocks.has(entry)
	) {
		restoreHandlers();
		return null;
	}
	const sourceBlocks = new AddressSet([
		...core,
		...body.sourceBlocks,
	]);
	// A genuine ordinary secondary entry would make this irreducible. The only
	// extra path admitted here is the nested handler already owned by `body`.
	for (const block of sourceBlocks) {
		if (block === entry) continue;
		for (const predecessor of cfg.normalPredecessors.get(block) ?? []) {
			if (!sourceBlocks.has(predecessor)) {
				restoreHandlers();
				return null;
			}
		}
	}
	const id = analyses.naturalLoops.loops.length + componentIndex + 1;
	return {
		kind: 'loop',
		id,
		header: entry,
		latches,
		loopBlocks: sourceBlocks,
		continuation,
		exits: exitEdges.map(({ from, to }) => ({
			from,
			to,
			kind: 'break' as const,
			continuation,
		})),
		children: [],
		body,
		sourceBlocks,
	};
}

/**
 * Exactly compose a catch body whose loops or nested exception ranges prevent
 * the ordinary weak-SESE builders from owning the whole handler.
 *
 * Nested ranges are contracted as complete try/catch nodes. Exceptional edges
 * to an enclosing handler/finalizer are lexical boundaries owned by that outer
 * Region, while normal edges leaving the bounded catch body are its ordinary
 * completion and need no synthetic control transfer here.
 */
function tryStructureCatchScopeForest(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	descriptor: ExceptionDescriptor,
	handlerBodyBlocks: AddressSet<number>,
	regionAt: RegionAt | undefined,
	structuredHandlers: AddressSet<number>,
	analyses: CFGAnalyses | undefined,
	recoveredSwitches?: RecoveredSwitches,
): Region | null {
	if (!analyses || !regionAt) return null;
	const handlersBeforeForest = new AddressSet(structuredHandlers);
	const nestedCandidates = descriptors.exceptions.handlers.filter((nested) =>
		nested !== descriptor &&
		nested.protectedEntries.intersection(handlerBodyBlocks).size > 0 &&
		shallowDescriptorOwnedBlocks(nested).isSubsetOf(handlerBodyBlocks)
	);
	const nestedHandlers = new AddressSet(
		nestedCandidates.map((nested) => nested.handler),
	);
	const nestedRoots = nestedCandidates.filter((nested) => {
		const parent = descriptors.exceptions.forest.parentByHandler.get(
			nested.handler,
		);
		return parent == null || !nestedHandlers.has(parent);
	});
	const nestedEntries = new AddressSet<number>(
		nestedRoots.flatMap((nested) => [...nested.protectedEntries]),
	);
	const nestedProtectedBlocks = new AddressSet<number>(
		nestedRoots.flatMap((nested) => [...nested.protectedBlocks]),
	);
	const handlerBoundaries = new AddressSet<number>();
	if (descriptor.canonicalFinallyAddress != null) {
		handlerBoundaries.add(descriptor.canonicalFinallyAddress);
	}
	let parent = descriptors.exceptions.forest.parentByHandler.get(
		descriptor.handler,
	);
	while (parent != null && !handlerBoundaries.has(parent)) {
		handlerBoundaries.add(parent);
		parent = descriptors.exceptions.forest.parentByHandler.get(parent);
	}
	const scopeSwitches = recoveredSwitches ??
		recoveredCompareChainSwitchesForScope(
			cfg,
			analyses,
			descriptors,
			regionAt,
			handlerBodyBlocks,
		);

	const composed = tryStructureBoundedScopeForest(
		cfg,
		analyses,
		(loop) => {
			const candidate = regionAt(loop.header, handlerBodyBlocks);
			return candidate?.kind === 'loop' && candidate.id === loop.id &&
					candidate.sourceBlocks.isSubsetOf(handlerBodyBlocks)
				? candidate
				: null;
		},
		{
			entry: descriptor.handler,
			allowed: handlerBodyBlocks,
			labelPrefix: `catch_${descriptor.handler.toString(16)}`,
			completion: (from, to) =>
				terminalExitRegion(
					cfg,
					to,
					false,
					new AddressSet<number>(),
					[],
					new AddressSet<number>(),
					descriptors,
					{ from, to, kind: 'normal' },
					[],
					structuredHandlers,
				) ?? {
					kind: 'sequence',
					regions: [],
					sourceBlocks: new AddressSet<number>(),
				},
			exceptionBoundary: (from, to) =>
				handlerBodyBlocks.has(from) && handlerBoundaries.has(to),
		},
		scopeSwitches,
		nestedEntries.size === 0 ? undefined : {
			entries: nestedEntries,
			protectedBlocks: nestedProtectedBlocks,
			exceptionAt: (protectedEntry) => {
				const nested = nestedRoots.find((candidate) =>
					candidate.protectedEntries.has(protectedEntry)
				);
				if (!nested) return null;
				return structureExceptionDescriptor(
					cfgWithEntry(cfg, protectedEntry),
					descriptors,
					nested,
					regionAt,
					undefined,
					structuredHandlers,
					analyses,
				);
			},
		},
	);
	if (
		composed &&
		handlerBodyBlocks.isSubsetOf(composed.sourceBlocks) &&
		regionCoversNormalCycles(cfg, handlerBodyBlocks, composed)
	) {
		return composed;
	}
	restoreStructuredHandlers(structuredHandlers, handlersBeforeForest);
	return null;
}

/** Restore handler ownership after discarding a speculative Region tree. */
export function restoreStructuredHandlers(
	structuredHandlers: AddressSet<number>,
	snapshot: AddressSet<number>,
): void {
	for (const handler of [...structuredHandlers]) {
		if (!snapshot.has(handler)) structuredHandlers.delete(handler);
	}
}

/**
 * Require every normal-flow cycle in a bounded candidate to be represented by
 * a Loop Region. Exact source ownership alone is insufficient: the recursive
 * DAG composer can visit all blocks in a cycle once and accidentally emit them
 * as a linear path.
 */
function regionCoversNormalCycles(
	cfg: ImmutableCFG,
	allowed: AddressSet<number>,
	region: Region,
): boolean {
	if (!hasCycleWithin(cfg, allowed)) return true;
	const loops: AddressSet<number>[] = [];
	const collect = (candidate: Region) => {
		if (candidate.kind === 'loop') loops.push(candidate.loopBlocks);
		switch (candidate.kind) {
			case 'sequence':
				candidate.regions.forEach(collect);
				break;
			case 'if':
				collect(candidate.consequent);
				collect(candidate.alternate);
				break;
			case 'switch':
				candidate.cases.forEach((switchCase) =>
					collect(switchCase.body)
				);
				collect(candidate.defaultBody);
				break;
			case 'tryCatch':
				collect(candidate.body);
				collect(candidate.handler);
				break;
			case 'tryFinally':
				collect(candidate.body);
				collect(candidate.finalizer);
				break;
			case 'loop':
				collect(candidate.body);
				break;
		}
	};
	collect(region);

	const visiting = new AddressSet<number>();
	const visited = new AddressSet<number>();
	const visit = (address: number): boolean => {
		if (!allowed.has(address) || visited.has(address)) return true;
		visiting.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (!allowed.has(successor)) continue;
			if (visiting.has(successor)) {
				if (
					!loops.some((loop) =>
						loop.has(address) && loop.has(successor)
					)
				) return false;
				continue;
			}
			if (!visit(successor)) return false;
		}
		visiting.delete(address);
		visited.add(address);
		return true;
	};
	for (const address of allowed) {
		if (!visit(address)) return false;
	}
	return true;
}

function catchContinuationEntries(
	descriptor: ExceptionDescriptor,
	handlerBodyBlocks: AddressSet<number>,
): number[] {
	const explicitBody = descriptor.catchBody ?? new AddressSet<number>();
	const entries = new AddressSet<number>();
	for (const block of explicitBody) {
		if (block === descriptor.handler) continue;
		if (descriptor.protectedBlocks.has(block)) continue;
		if (handlerBodyBlocks.has(block)) entries.add(block);
	}
	for (const candidate of explicitBody) {
		if (!handlerBodyBlocks.has(candidate)) continue;
		if (entries.has(candidate)) continue;
		if (candidate === descriptor.handler) continue;
		if (descriptor.protectedBlocks.has(candidate)) continue;
		entries.add(candidate);
	}
	return [...entries].toSorted((left, right) => left - right);
}

function containedRegion(
	region: Region | null | undefined,
	allowed: AddressSet<number> | undefined,
): Region | null {
	if (!region) return null;
	if (!allowed) return region;
	return region.sourceBlocks.isSubsetOf(allowed) ? region : null;
}

function addNestedCatchHandlers(
	cfg: ImmutableCFG,
	handlerBodyBlocks: AddressSet<number>,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
) {
	const postFinallyBlocks = catchPostFinallyBlocks(
		cfg,
		descriptor,
		descriptors,
	);
	let changed = true;
	while (changed) {
		changed = false;
		for (const nested of descriptors.exceptions.handlers) {
			if (nested === descriptor) continue;
			if (handlerBodyBlocks.has(nested.handler)) continue;
			if (
				!nested.protectedEntries.intersection(handlerBodyBlocks).size
			) {
				continue;
			}
			if (nested.protectedEntries.intersection(postFinallyBlocks).size) {
				continue;
			}
			const nestedOwned = shallowDescriptorOwnedBlocks(nested);
			if (nested.kind === 'catch') {
				for (
					const block of expandedCatchBodyBlocks(
						cfg,
						nested,
						descriptors,
					)
				) nestedOwned.add(block);
			}
			for (const block of nestedOwned) {
				if (!handlerBodyBlocks.has(block)) {
					handlerBodyBlocks.add(block);
					changed = true;
				}
			}
			handlerBodyBlocks.add(nested.handler);
			changed = true;
		}
	}
}

function catchPostFinallyBlocks(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
): AddressSet<number> {
	const finallyAddress = descriptor.canonicalFinallyAddress;
	if (finallyAddress == null) return new AddressSet();
	const finalizer = descriptors.exceptions.handlerByAddress.get(
		finallyAddress,
	);
	if (finalizer?.kind !== 'finally') return new AddressSet();
	// The finalizer body runs after the catch and is emitted in `finally {}`, so
	// it (and everything past it) must not be absorbed into the catch body —
	// otherwise the finalizer statements duplicate inside the catch. Seed the
	// walk with the finalizer's own canonical body in addition to its normal-exit
	// continuations.
	const entries = new AddressSet(
		normalFinalizerCopyContinuations(cfg, finalizer),
	);
	for (const block of finalizer.boundedFinallyBodyBlocks ?? []) {
		entries.add(block);
	}
	return reachableFromEntries(cfg, entries);
}

function removeCatchPostFinallyBlocks(
	cfg: ImmutableCFG,
	handlerBodyBlocks: AddressSet<number>,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
) {
	const postFinally = catchPostFinallyBlocks(cfg, descriptor, descriptors);
	const nestedOwned = new AddressSet<number>();
	for (const nested of descriptors.exceptions.handlers) {
		if (nested === descriptor) continue;
		if (
			nested.protectedEntries.intersection(handlerBodyBlocks).size ===
				0 ||
			nested.protectedEntries.intersection(postFinally).size > 0
		) continue;
		for (const block of shallowDescriptorOwnedBlocks(nested)) {
			nestedOwned.add(block);
		}
	}
	for (const block of postFinally) {
		if (nestedOwned.has(block)) continue;
		handlerBodyBlocks.delete(block);
	}
}

function shallowDescriptorOwnedBlocks(
	descriptor: ExceptionDescriptor,
): AddressSet<number> {
	const owned = new AddressSet<number>(descriptor.protectedBlocks);
	owned.add(descriptor.handler);
	for (const block of descriptor.boundedFinallyBodyBlocks ?? []) {
		owned.add(block);
	}
	return owned;
}

/**
 * Every block a contracted Region for this protected range may own: the
 * protected body with its bridges, the handler forest below it, and the catch
 * bodies and finalizer copies those handlers emit.
 *
 * A contraction has to stop at the range's continuation. Structuring the range
 * as an ordinary Region does not: it keeps appending the code after the join,
 * which for a function built from a row of small try/catch probes means the
 * first range claims every later one and the skeleton can never compose.
 */
export function contractedExceptionBlocks(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
): AddressSet<number> {
	const blocks = descriptorOwnedBlocks(descriptor, descriptors);
	const seen = new AddressSet<number>();
	const pending = [descriptor];
	while (pending.length > 0) {
		const current = pending.pop()!;
		if (seen.has(current.handler)) continue;
		seen.add(current.handler);
		for (
			const block of protectedBodyBlocks(cfg, current, descriptors)
		) blocks.add(block);
		for (
			const block of expandedCatchBodyBlocks(cfg, current, descriptors)
		) blocks.add(block);
		for (const block of current.finallyBodyBlocks ?? []) blocks.add(block);
		for (const root of current.finallyCopyRoots) blocks.add(root);
		for (const copy of current.finallyCopies) {
			blocks.add(copy.copyRoot);
			for (const block of copy.copyBlocks ?? []) blocks.add(block);
		}
		for (const suffix of current.finallyCopySuffixes) {
			blocks.add(suffix.copyRoot);
			blocks.add(suffix.ownerBlock);
		}
		for (
			const child of descriptors.exceptions.forest.nodeByHandler.get(
				current.handler,
			)?.children ?? []
		) pending.push(child.descriptor);
	}
	return blocks;
}

function reachableFromEntries(
	cfg: ImmutableCFG,
	entries: AddressSet<number>,
): AddressSet<number> {
	const reachable = new AddressSet<number>();
	const queue = [...entries];
	while (queue.length > 0) {
		const addr = queue.shift()!;
		if (reachable.has(addr)) continue;
		reachable.add(addr);
		for (const successor of cfg.normalSuccessors.get(addr) ?? []) {
			if (!reachable.has(successor)) queue.push(successor);
		}
	}
	return reachable;
}

function expandedFinallyBodyBlocks(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
	finalizerEntry: number,
): AddressSet<number> {
	const body = new AddressSet<number>(
		descriptor.boundedFinallyBodyBlocks ?? [finalizerEntry],
	);
	body.add(finalizerEntry);

	const node = descriptors.exceptions.forest.nodeByHandler.get(
		descriptor.handler,
	);
	const normalExits = new AddressSet(
		normalFinalizerCopyContinuations(cfg, descriptor).filter((exit) =>
			exit !== finalizerEntry
		),
	);
	removeFinallyNormalContinuationBody(cfg, body, normalExits);

	let changed = true;
	while (changed) {
		changed = false;
		if (
			expandFinallyNormalContinuations(
				cfg,
				descriptor,
				descriptors,
				body,
				normalExits,
			)
		) {
			changed = true;
		}
		if (!node) continue;
		const candidates = uniqueExceptionDescriptors([
			...finallyBodyChildCandidates(
				descriptor,
				descriptors,
				node,
			),
			...finallyBodyTrailerHandlerCandidates(
				cfg,
				descriptor,
				descriptors,
				body,
			),
		]);
		for (const child of candidates) {
			const childDescriptor = child.descriptor;
			if (childDescriptor === descriptor) continue;
			if (
				exceptionAnchoredInNormalContinuation(
					cfg,
					childDescriptor,
					body,
					normalExits,
				)
			) {
				continue;
			}
			if (!exceptionAnchoredInFinallyBody(cfg, childDescriptor, body)) {
				continue;
			}
			for (
				const block of descriptorOwnedBlocks(
					childDescriptor,
					descriptors,
				)
			) {
				if (body.has(block)) continue;
				body.add(block);
				changed = true;
			}
		}
	}

	removeFinallyNormalContinuationBody(cfg, body, normalExits);
	// Drop copies of an enclosing finalizer that leaked into this body: e.g. the
	// outer finally's normal-exit copy (return 22) embedded after inner1's finally.
	// They belong to an ancestor finalizer, so a descendant must not absorb and
	// re-structure them — the emitter suppresses these copies (fixes G3 leak).
	for (const block of [...body]) {
		if (block === finalizerEntry) continue;
		const classification = descriptors.exceptions.finalizerCopyModel
			.copyBlocks
			.get(block);
		if (
			classification &&
			isEnclosingFinalizerOwner(
				descriptors,
				classification.ownerHandler,
				descriptor.handler,
			)
		) {
			body.delete(block);
		}
	}
	return body;
}

// True when `ownerHandler` is a proper forest-ancestor finally of `handler` — i.e.
// a finalizer that encloses `handler`, whose body copies must not be absorbed by
// the enclosed finalizer.
function isEnclosingFinalizerOwner(
	descriptors: CFGDescriptors,
	ownerHandler: number,
	handler: number,
): boolean {
	if (ownerHandler === handler) return false;
	let current: number | undefined = handler;
	const seen = new AddressSet<number>();
	while (current != null && !seen.has(current)) {
		seen.add(current);
		const parent: number | undefined = descriptors.exceptions.forest
			.parentByHandler.get(current);
		if (parent === ownerHandler) return true;
		current = parent;
	}
	return false;
}

function exceptionAnchoredInNormalContinuation(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	body: AddressSet<number>,
	normalExits: AddressSet<number>,
): boolean {
	const reachable = finalizerNormalContinuationReachable(
		cfg,
		normalExits,
		body,
	);
	if (reachable.has(descriptor.handler)) return true;
	return descriptor.protectedEntries.intersection(reachable).size > 0;
}

function finalizerNormalContinuationReachable(
	cfg: ImmutableCFG,
	entries: AddressSet<number>,
	allowed: AddressSet<number>,
): AddressSet<number> {
	const reachable = new AddressSet<number>();
	const queue = [...entries];
	while (queue.length > 0) {
		const addr = queue.shift()!;
		if (reachable.has(addr)) continue;
		reachable.add(addr);
		for (const successor of cfg.normalSuccessors.get(addr) ?? []) {
			if (allowed.has(successor) && !reachable.has(successor)) {
				queue.push(successor);
			}
		}
	}
	return reachable;
}

function removeFinallyNormalContinuationBody(
	cfg: ImmutableCFG,
	body: AddressSet<number>,
	normalExits: AddressSet<number>,
) {
	const queue = [...normalExits];
	const seen = new AddressSet<number>();
	while (queue.length > 0) {
		const addr = queue.shift()!;
		if (seen.has(addr)) continue;
		seen.add(addr);
		if (body.has(addr)) body.delete(addr);
		for (const successor of cfg.normalSuccessors.get(addr) ?? []) {
			if (body.has(successor)) queue.push(successor);
		}
	}
}

function expandFinallyNormalContinuations(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
	body: AddressSet<number>,
	normalExits: AddressSet<number>,
): boolean {
	// A linear successor of a bounded canonical body is the continuation after
	// `finally`, not more finalizer code. Expansion exists for branching handler
	// roots (notably a loop compiled directly in the exception landing pad), where
	// the handler graph cannot discover the complete body with a linear trace.
	if (
		![...body].some((address) => {
			const terminator = cfg.blocks.get(address)?.terminator;
			return terminator?.kind === 'if' || terminator?.kind === 'switch';
		})
	) return false;
	let changed = false;
	// Grow only from the canonical landing-pad body. Normal successors of the
	// protected range are per-exit finalizer copies; admitting them here places a
	// copied return/throw path inside the source-level `finally`.
	const sources = new AddressSet(body);
	for (const block of sources) {
		for (const successor of cfg.normalSuccessors.get(block) ?? []) {
			if (body.has(successor)) continue;
			if (descriptor.protectedBlocks.has(successor)) continue;
			if (normalExits.has(successor)) continue;
			if (descriptor.finallyCopyRoots.has(successor)) continue;
			if (descriptors.exceptions.handlerByAddress.has(successor)) {
				continue;
			}
			body.add(successor);
			changed = true;
		}
	}
	return changed;
}

function finallyBodyChildCandidates(
	_descriptor: ExceptionDescriptor,
	_descriptors: CFGDescriptors,
	node: ExceptionRegionForestNode,
): ExceptionRegionForestNode[] {
	return flattenForestChildren(node);
}

function finallyBodyTrailerHandlerCandidates(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
	body: AddressSet<number>,
): ExceptionRegionForestNode[] {
	const declaredBody = new AddressSet<number>(
		descriptor.finallyBodyBlocks ?? [],
	);
	if (declaredBody.size === 0) return [];
	return descriptors.exceptions.handlers
		.filter((candidate) =>
			candidate.kind === 'catch' &&
			candidate !== descriptor &&
			candidate.protectedEntries.intersection(declaredBody).size > 0 &&
			exceptionAnchoredInFinallyBody(cfg, candidate, body)
		)
		.map((candidate) => ({ descriptor: candidate, children: [] }));
}

function uniqueExceptionDescriptors(
	nodes: ExceptionRegionForestNode[],
): ExceptionRegionForestNode[] {
	const seen = new Set<number>();
	return nodes.filter((node) => {
		if (seen.has(node.descriptor.handler)) return false;
		seen.add(node.descriptor.handler);
		return true;
	});
}

function exceptionAnchoredInFinallyBody(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	body: AddressSet<number>,
): boolean {
	if (body.has(descriptor.handler)) return true;
	for (const block of body) {
		for (const successor of cfg.normalSuccessors.get(block) ?? []) {
			if (successor === descriptor.handler) return true;
		}
	}
	return false;
}

function flattenForestChildren(
	node: ExceptionRegionForestNode,
): ExceptionRegionForestNode[] {
	const result: ExceptionRegionForestNode[] = [];
	const seen = new Set<ExceptionRegionForestNode>();
	const queue = [...node.children];
	while (queue.length > 0) {
		const child = queue.shift()!;
		if (seen.has(child)) continue;
		seen.add(child);
		result.push(child);
		queue.push(...child.children);
	}
	return result;
}

function descriptorOwnedBlocks(
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
): AddressSet<number> {
	const owned = new AddressSet<number>(descriptor.protectedBlocks);
	owned.add(descriptor.handler);
	for (const block of descriptor.finallyBodyBlocks ?? []) owned.add(block);

	const node = descriptors.exceptions.forest.nodeByHandler.get(
		descriptor.handler,
	);
	for (const child of node?.children ?? []) {
		for (
			const block of descriptorOwnedBlocks(
				child.descriptor,
				descriptors,
			)
		) {
			owned.add(block);
		}
	}
	return owned;
}

function expandedCatchBodyBlocks(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
	additionalStops?: AddressSet<number>,
): AddressSet<number> {
	const boundary = catchBodyBoundaryBlocks(cfg, descriptor, descriptors);
	for (const block of additionalStops ?? []) boundary.stop.add(block);
	const body = new AddressSet<number>();
	const catchBodyLimit = descriptor.catchBody;
	body.add(descriptor.handler);
	for (const block of catchBodyLimit ?? []) {
		if (boundary.stop.has(block)) continue;
		if (descriptor.protectedBlocks.has(block)) continue;
		body.add(block);
	}
	const queue = [...body];

	while (queue.length > 0) {
		const addr = queue.shift()!;
		for (const successor of cfg.normalSuccessors.get(addr) ?? []) {
			if (
				catchBodyLimit != null &&
				successor !== descriptor.handler &&
				!catchBodyLimit.has(successor)
			) {
				continue;
			}
			if (boundary.passThrough.has(successor)) {
				for (
					const next of boundary.passThroughNext.get(successor) ?? []
				) {
					if (!body.has(next)) queue.push(next);
				}
				for (const next of cfg.normalSuccessors.get(successor) ?? []) {
					if (!body.has(next)) queue.push(next);
				}
				continue;
			}
			if (descriptor.protectedBlocks.has(successor)) continue;
			if (boundary.stop.has(successor)) continue;
			if (successor === cfg.entry && descriptor.handler !== cfg.entry) {
				continue;
			}
			if (body.has(successor)) continue;
			if (!cfg.blocks.has(successor)) continue;
			body.add(successor);
			queue.push(successor);
		}
	}

	return body;
}

/**
 * Blocks the protected body reaches over normal edges without re-entering the
 * handler: the range's continuation and everything past it.
 *
 * A `finally` runs on the normal path too, so its own body is reachable this
 * way and the closure would swallow it; those descriptors keep the narrower
 * successor rule the copy model already bounds.
 */
function protectedContinuationClosure(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	protectedBody: AddressSet<number>,
): AddressSet<number> {
	const closure = new AddressSet<number>();
	const queue: number[] = [];
	for (const block of protectedBody) {
		for (const successor of cfg.normalSuccessors.get(block) ?? []) {
			queue.push(successor);
		}
	}
	while (queue.length > 0) {
		const candidate = queue.shift()!;
		if (
			candidate === descriptor.handler || closure.has(candidate) ||
			protectedBody.has(candidate)
		) continue;
		closure.add(candidate);
		if (descriptor.kind !== 'catch') continue;
		for (const successor of cfg.normalSuccessors.get(candidate) ?? []) {
			queue.push(successor);
		}
	}
	return closure;
}

function catchBodyBoundaryBlocks(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
): {
	stop: AddressSet<number>;
	passThrough: AddressSet<number>;
	passThroughNext: Map<number, number[]>;
} {
	const stop = new AddressSet<number>();
	const passThrough = new AddressSet<number>();
	const passThroughNext = new Map<number, number[]>();
	const protectedBody = protectedBodyBlocks(cfg, descriptor, descriptors);
	// A block the protected body reaches normally is the code after the
	// `try/catch`, not part of the catch body. HandlerGraph's bounded catch trace
	// can include that join (notably when it is protected by an outer handler),
	// so stop before it and let the enclosing protected DAG emit it once.
	//
	// The whole forward closure is excluded, not just the immediate successors:
	// a protected range routinely ends in an unprotected trailer (the
	// non-throwing tail of the `try`) and only joins the handler one or more
	// blocks later. Stopping at the successors alone let a catch body swallow
	// the join and everything after it, which for a row of small try/catch
	// probes means the first one claims all the others.
	for (
		const candidate of protectedContinuationClosure(
			cfg,
			descriptor,
			protectedBody,
		)
	) stop.add(candidate);
	for (const candidate of descriptors.exceptions.handlers) {
		if (candidate === descriptor) continue;
		if (
			candidate.kind !== 'finally' ||
			!candidate.protectedBlocks.has(descriptor.handler)
		) {
			continue;
		}
		stop.add(candidate.handler);
		for (const block of candidate.finallyBodyBlocks ?? []) {
			stop.add(block);
		}
		for (const root of candidate.finallyCopyRoots) stop.add(root);
		for (const copy of candidate.finallyCopies) {
			stop.add(copy.copyRoot);
		}
		for (
			const continuation of normalFinalizerCopyContinuations(
				cfg,
				candidate,
			)
		) {
			stop.add(continuation);
		}
		for (const suffix of candidate.finallyCopySuffixes) {
			if (
				suffix.kind === 'abruptExitTrailer' ||
				suffix.kind === 'canonical' ||
				suffix.kind === 'catchTrailer'
			) {
				stop.add(suffix.ownerBlock);
				stop.add(suffix.copyRoot);
			}
		}
	}
	return { stop, passThrough, passThroughNext };
}

// Build a delegate-yield region if `entry` is a recovered delegate prelude. Kept local to
// avoid a cyclic import of structureRegion.ts.
function delegateYieldRegionForPrelude(
	entry: number,
	descriptors: CFGDescriptors,
): Region | null {
	const descriptor = descriptors.delegateYields.delegateByPrelude.get(entry);
	if (!descriptor) return null;
	return {
		kind: 'delegateYield',
		argument: t.cloneNode(descriptor.argument, true),
		completion: descriptor.completion,
		completionTarget: descriptor.completionTarget
			? t.cloneNode(descriptor.completionTarget, true)
			: undefined,
		trailing: descriptor.trailing?.map((stmt) => t.cloneNode(stmt, true)),
		sourceBlocks: new AddressSet(descriptor.sourceBlocks),
	};
}

function structureProtectedBody(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	descriptor: ExceptionDescriptor,
	regionAt?: RegionAt,
	deferProtectedExits = false,
	structuredHandlers: AddressSet<number> = new AddressSet<number>(),
	analyses?: CFGAnalyses,
	ownershipScope?: AddressSet<number>,
): Region | null {
	const protectedBlocks = protectedBodyBlocks(
		cfg,
		descriptor,
		descriptors,
	);
	const routeNestedSideExits = (region: Region): Region =>
		routeNestedExceptionSideExitsInProtectedBody(
			region,
			protectedBlocks,
			cfg,
			descriptor,
		) ?? region;
	const normalFinalizerCopyRoots = normalFinalizerCopyExitRoots(descriptor);
	const abruptFinalizerCopyRoots = abruptFinalizerCopyExitRoots(descriptor);
	const iteratorLoop = structureProtectedIteratorGuardLoop(
		cfg,
		descriptor,
		regionAt,
		analyses,
	);
	if (iteratorLoop) return iteratorLoop;
	let candidate: Region | null = null;
	if (!hasCycleWithin(cfg, protectedBlocks)) {
		const branched = structureProtectedDAGFrom(
			cfg,
			descriptors,
			descriptor,
			cfg.entry,
			protectedBlocks,
			new AddressSet(),
			undefined,
			deferProtectedExits,
			normalFinalizerCopyRoots,
			abruptFinalizerCopyRoots,
			regionAt,
			structuredHandlers,
			analyses,
			ownershipScope,
		);
		if (branched && branched.sourceBlocks.size > 1) {
			const continuationEntry = uniqueProtectedExit(
				cfg,
				branched.sourceBlocks,
				protectedBlocks,
			);
			if (
				continuationEntry == null ||
				branched.sourceBlocks.has(continuationEntry)
			) candidate = branched;
			if (
				candidate && protectedBodyComplete(candidate, protectedBlocks)
			) {
				return routeNestedSideExits(candidate);
			}
			if (continuationEntry == null) {
				return tryStructureProtectedScopeForest(
					cfg,
					descriptors,
					descriptor,
					regionAt,
					deferProtectedExits,
					normalFinalizerCopyRoots,
					abruptFinalizerCopyRoots,
					analyses,
					structuredHandlers,
					undefined,
					ownershipScope,
				) ?? (candidate ? routeNestedSideExits(candidate) : null);
			}
			const continuation = structureProtectedDAGFrom(
				cfg,
				descriptors,
				descriptor,
				continuationEntry,
				protectedBlocks,
				new AddressSet(branched.sourceBlocks),
				undefined,
				deferProtectedExits,
				normalFinalizerCopyRoots,
				abruptFinalizerCopyRoots,
				regionAt,
				structuredHandlers,
				analyses,
				ownershipScope,
			);
			candidate = !continuation ? branched : {
				kind: 'sequence',
				regions: [branched, continuation],
				sourceBlocks: new AddressSet([
					...branched.sourceBlocks,
					...continuation.sourceBlocks,
				]),
			};
			if (protectedBodyComplete(candidate, protectedBlocks)) {
				return routeNestedSideExits(candidate);
			}
		}
	}

	const entryDelegate = delegateYieldRegionForPrelude(cfg.entry, descriptors);
	if (
		entryDelegate && protectedBodyComplete(entryDelegate, protectedBlocks)
	) {
		return routeNestedSideExits(entryDelegate);
	}
	const handlersBeforeNestedEntry = new AddressSet(structuredHandlers);
	const nestedEntryDescriptor = exceptionStartingAt(
		cfg,
		cfg.entry,
		descriptors,
		protectedBlocks,
	);
	const nestedEntryCandidate = nestedEntryDescriptor != null &&
			nestedEntryDescriptor.handler !== descriptor.handler &&
			!structuredHandlers.has(nestedEntryDescriptor.handler)
		? structureExceptionDescriptor(
			cfg,
			descriptors,
			nestedEntryDescriptor,
			regionAt,
			undefined,
			structuredHandlers,
			analyses,
		)
		: null;
	const nestedEntryRegion = nestedEntryCandidate?.sourceBlocks.isSubsetOf(
			protectedBlocks,
		)
		? nestedEntryCandidate
		: null;
	if (nestedEntryCandidate && !nestedEntryRegion) {
		restoreStructuredHandlers(
			structuredHandlers,
			handlersBeforeNestedEntry,
		);
	}

	const body = structureStraightLineSequenceFrom(
		cfg,
		cfg.entry,
		protectedBlocks,
		(childEntry, allowed) =>
			childEntry === cfg.entry
				// same exception region, so attempt the builders it would have
				// reached here: a nested handler sharing the protected entry, a
				// delegate-yield prelude wrapped by the try (`try { x = yield*
				// g() }`), and an ordinary branch whose header is the protected
				// entry itself.
				? nestedEntryRegion ??
					delegateYieldRegionForPrelude(childEntry, descriptors) ??
					protectedEntryBranchRegion(
						cfg,
						descriptors,
						protectedBlocks,
						regionAt,
						structuredHandlers,
						analyses,
					)
				: regionAt?.(childEntry, allowed) ?? null,
	);
	if (body && protectedBodyComplete(body, protectedBlocks)) {
		const continuationEntry = uniqueProtectedExit(
			cfg,
			body.sourceBlocks,
			protectedBlocks,
		);
		if (
			continuationEntry == null ||
			continuationEntry === cfg.entry ||
			!regionAt
		) {
			return routeNestedSideExits(body);
		}
		const continuation = regionAt(continuationEntry, protectedBlocks);
		if (
			!continuation ||
			continuation.sourceBlocks.isSubsetOf(body.sourceBlocks)
		) {
			return routeNestedSideExits(body);
		}
		return routeNestedSideExits({
			kind: 'sequence',
			regions: [body, continuation],
			sourceBlocks: new AddressSet([
				...body.sourceBlocks,
				...continuation.sourceBlocks,
			]),
		});
	}
	restoreStructuredHandlers(structuredHandlers, handlersBeforeNestedEntry);
	const forest = tryStructureProtectedScopeForest(
		cfg,
		descriptors,
		descriptor,
		regionAt,
		deferProtectedExits,
		normalFinalizerCopyRoots,
		abruptFinalizerCopyRoots,
		analyses,
		structuredHandlers,
		undefined,
		ownershipScope,
	);
	if (forest) return routeNestedSideExits(forest);
	if (!body || !regionAt) return body ?? candidate;

	const continuationEntry = uniqueProtectedExit(
		cfg,
		body.sourceBlocks,
		protectedBlocks,
	);
	if (continuationEntry == null || continuationEntry === cfg.entry) {
		return body ?? candidate;
	}

	const continuation = regionAt(continuationEntry, protectedBlocks);
	if (!continuation) return body ?? candidate;
	if (continuation.sourceBlocks.isSubsetOf(body.sourceBlocks)) return body;
	return routeNestedSideExits({
		kind: 'sequence',
		regions: [body, continuation],
		sourceBlocks: new AddressSet([
			...body.sourceBlocks,
			...continuation.sourceBlocks,
		]),
	});
}

/**
 * Recover an ordinary branch whose header is the protected entry.
 *
 * The straight-line walk must not ask the generic builder here — that would
 * re-form this same exception region — so it kept the entry as a Basic Region
 * and stopped at its two successors, leaving the branch unstructured and the
 * remainder of the range re-attached through `uniqueProtectedExit`. The If
 * builder is bounded to the blocks the try body owns, so no arm can leave the
 * protected range, and the candidate is accepted only when it owns the entry:
 * the sequence then continues at the branch's own forward exit, which is the
 * same continuation the walk would have found.
 */
function protectedEntryBranchRegion(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	protectedBlocks: AddressSet<number>,
	regionAt: RegionAt | undefined,
	structuredHandlers: AddressSet<number>,
	analyses: CFGAnalyses | undefined,
): Region | null {
	if (!analyses || !blockNeedsBranchRegion(cfg.entry, cfg)) return null;
	const snapshot = new AddressSet(structuredHandlers);
	const candidate = tryStructureIfRegion(
		cfg,
		analyses,
		(cursor, childAllowed) =>
			cursor === cfg.entry ? null : regionAt?.(
				cursor,
				(childAllowed ?? protectedBlocks).intersection(protectedBlocks),
			) ?? null,
		protectedBlocks,
		true,
		structuredHandlers,
		descriptors.compatibility,
	);
	if (
		candidate && candidate.sourceBlocks.has(cfg.entry) &&
		candidate.sourceBlocks.isSubsetOf(protectedBlocks) &&
		!ownsForeignLoopExitTarget(
			cfg,
			analyses,
			protectedBlocks,
			candidate.sourceBlocks,
		)
	) return candidate;
	restoreStructuredHandlers(structuredHandlers, snapshot);
	return null;
}

/**
 * Whether the branch would own a block some loop it does not contain exits to.
 *
 * A Loop Region places its own exit destinations. When the branch also owns the
 * loop, that destination is the loop's lexical continuation inside an arm and
 * the branch is its rightful owner. When the loop lies outside the branch, the
 * two would emit the block twice, so the branch declines and the entry stays a
 * Basic Region. Only loops inside the protected range are at stake: the try
 * body is where this branch is composed.
 */
function ownsForeignLoopExitTarget(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	protectedBlocks: AddressSet<number>,
	owned: AddressSet<number>,
): boolean {
	for (const loop of analyses.naturalLoops.loops) {
		if (!loop.body.isSubsetOf(protectedBlocks)) continue;
		if (loop.body.isSubsetOf(owned)) continue;
		for (const block of loop.body) {
			for (const successor of cfg.normalSuccessors.get(block) ?? []) {
				if (loop.body.has(successor)) continue;
				if (owned.has(successor)) return true;
			}
		}
	}
	return false;
}

/**
 * Include non-throwing register-copy blocks that bridge split protected ranges.
 *
 * Hermes exception tables only need to cover instructions that can throw. A
 * source-level try can therefore be represented as several protected ranges
 * separated by a `Mov` block. Region structuring still needs that block: it is
 * the lexical path from one protected range to the next. Absorb only a unique,
 * linear register-copy bridge whose predecessor is already protected; broader
 * code motion belongs to binding/alias coalescing.
 */
function protectedBodyBlocks(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
): AddressSet<number> {
	const result = new AddressSet(descriptor.protectedBlocks);
	for (const entry of descriptor.protectedEntries) {
		if (entry === cfg.entry) continue;
		const bridge: number[] = [];
		let cursor = entry;
		for (let depth = 0; depth < 4; depth++) {
			const outsidePredecessors = [
				...(cfg.normalPredecessors.get(cursor) ?? []),
			].filter((predecessor) => !result.has(predecessor));
			if (outsidePredecessors.length !== 1) break;
			const predecessor = outsidePredecessors[0]!;
			const block = cfg.blocks.get(predecessor);
			if (
				!block || !isTransparentProtectedBridge(block) ||
				hasCompetingExceptionalSuccessor(
					cfg,
					predecessor,
					descriptor,
					descriptors,
				) ||
				[...descriptors.exceptions.handlers].some((candidate) =>
					candidate !== descriptor &&
					!isEnclosingExceptionDescriptor(
						descriptor,
						candidate,
						descriptors,
					) &&
					(candidate.handler === predecessor ||
						candidate.protectedBlocks.has(predecessor))
				)
			) break;
			bridge.push(predecessor);
			cursor = predecessor;
			const predecessors = cfg.normalPredecessors.get(cursor) ?? [];
			if ([...predecessors].some((candidate) => result.has(candidate))) {
				for (const address of bridge) result.add(address);
				break;
			}
		}
	}
	// A range can also end before a non-throwing completion-value copy. Keep
	// those path-specific copies with the protected arm so its outgoing Phi edge
	// still has a lexical assignment site.
	for (let changed = true; changed;) {
		changed = false;
		for (const address of [...result]) {
			for (const successor of cfg.normalSuccessors.get(address) ?? []) {
				if (result.has(successor)) continue;
				const block = cfg.blocks.get(successor);
				if (
					!block || !isTransparentProtectedBridge(block) ||
					hasCompetingExceptionalSuccessor(
						cfg,
						successor,
						descriptor,
						descriptors,
					) ||
					[...(cfg.normalPredecessors.get(successor) ?? [])].some(
						(predecessor) => !result.has(predecessor),
					) ||
					[...descriptors.exceptions.handlers].some((candidate) =>
						candidate !== descriptor &&
						!isEnclosingExceptionDescriptor(
							descriptor,
							candidate,
							descriptors,
						) &&
						(candidate.handler === successor ||
							candidate.protectedBlocks.has(successor))
					)
				) continue;
				result.add(successor);
				changed = true;
			}
		}
	}
	return result;
}

/**
 * An inner exception table can omit a non-throwing bridge even though the
 * enclosing table still covers it. That outer ownership is not a competing
 * lexical scope: the bridge remains part of the inner source-level try. Only
 * an unrelated or nested descriptor prevents bridge expansion.
 */
function isEnclosingExceptionDescriptor(
	descriptor: ExceptionDescriptor,
	candidate: ExceptionDescriptor,
	descriptors: CFGDescriptors,
): boolean {
	let parent = descriptors.exceptions.forest.parentByHandler.get(
		descriptor.handler,
	);
	while (parent != null) {
		if (parent === candidate.handler) return true;
		parent = descriptors.exceptions.forest.parentByHandler.get(parent);
	}
	return false;
}

function hasCompetingExceptionalSuccessor(
	cfg: ImmutableCFG,
	address: number,
	descriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
): boolean {
	const enclosingHandlers = new AddressSet<number>();
	let parent = descriptors.exceptions.forest.parentByHandler.get(
		descriptor.handler,
	);
	while (parent != null) {
		enclosingHandlers.add(parent);
		parent = descriptors.exceptions.forest.parentByHandler.get(parent);
	}
	return [...cfg.exceptionalSuccessors.get(address) ?? []].some(
		(successor) => !enclosingHandlers.has(successor),
	);
}

function isTransparentProtectedBridge(block: CFGBlock): boolean {
	if (block.terminator.kind !== 'goto') return false;
	return block.body.every((statement) => {
		if (t.isVariableDeclaration(statement)) {
			return statement.declarations.every((declaration) =>
				t.isIdentifier(declaration.id) &&
				(declaration.init == null ||
					isTransparentProtectedBridgeValue(declaration.init))
			);
		}
		if (!t.isExpressionStatement(statement)) return false;
		const expression = statement.expression;
		return t.isAssignmentExpression(expression, { operator: '=' }) &&
			t.isIdentifier(expression.left) &&
			isTransparentProtectedBridgeValue(expression.right);
	});
}

function isTransparentProtectedBridgeValue(node: t.Expression): boolean {
	return t.isIdentifier(node) || isConstantBridgeValue(node) ||
		isPhiBridgeMarker(node);
}

function isConstantBridgeValue(node: t.Expression): boolean {
	return t.isNullLiteral(node) || t.isStringLiteral(node) ||
		t.isNumericLiteral(node) || t.isBooleanLiteral(node) ||
		t.isBigIntLiteral(node);
}

function isPhiBridgeMarker(node: t.Expression): boolean {
	return t.isCallExpression(node) &&
		t.isV8IntrinsicIdentifier(node.callee, { name: 'Phi' });
}

/**
 * Compose a protected GetPNameList guard with its recovered for-in loop.
 *
 * Hermes puts the zero-property guard before GetNextPName. The guard branches
 * either to the natural-loop header or directly to the loop continuation, but
 * `for (… in …)` already represents that zero-iteration branch. When the whole
 * machine is protected, treating the guard as an ordinary branch prevents the
 * exception Region from owning the loop and leaves its landing pad unhandled.
 *
 * Keep this exact: the recovered loop must name this block as its preheader,
 * both loop completion paths must agree, and the guard plus loop must own the
 * complete protected range.
 */
function structureProtectedIteratorGuardLoop(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	regionAt: RegionAt | undefined,
	analyses: CFGAnalyses | undefined,
): Region | null {
	if (!regionAt || !analyses) return null;
	const guard = cfg.blocks.get(cfg.entry);
	if (!guard || guard.terminator.kind !== 'if') return null;

	for (
		const [loopTarget, bypass] of [
			[guard.terminator.taken, guard.terminator.fallthrough],
			[guard.terminator.fallthrough, guard.terminator.taken],
		] as const
	) {
		const naturalLoop = analyses.naturalLoops.loopByHeader.get(loopTarget);
		if (
			!naturalLoop || descriptor.protectedBlocks.has(bypass) ||
			!naturalLoop.body.isSubsetOf(descriptor.protectedBlocks)
		) continue;
		const loop = regionAt(loopTarget, descriptor.protectedBlocks);
		if (
			loop?.kind !== 'loop' || loop.id !== naturalLoop.id ||
			loop.syntax?.kind !== 'forIn' ||
			loop.syntax.preheader?.block !== cfg.entry ||
			!loop.sourceBlocks.isSubsetOf(descriptor.protectedBlocks) ||
			!loop.exits.some((exit) => exit.to === bypass)
		) continue;

		const sourceBlocks = new AddressSet([
			cfg.entry,
			...loop.sourceBlocks,
		]);
		if (!sourceBlocks.equals(descriptor.protectedBlocks)) continue;
		return {
			kind: 'sequence',
			regions: [
				{
					kind: 'basic',
					body: [],
					sourceBlocks: new AddressSet([cfg.entry]),
				},
				loop,
			],
			sourceBlocks,
		};
	}
	return null;
}

function protectedBodyComplete(
	region: Region,
	protectedBlocks: AddressSet<number>,
): boolean {
	return protectedBlocks.isSubsetOf(region.sourceBlocks);
}

function recoveredCompareChainSwitchesForScope(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses | undefined,
	descriptors: CFGDescriptors,
	regionAt: RegionAt | undefined,
	scope: AddressSet<number>,
): RecoveredSwitches | undefined {
	if (!analyses || !regionAt) return undefined;
	const dispatches = new AddressSet<number>(
		[...scope].filter((address) =>
			descriptors.switches.switchByDispatch.get(address)?.kind ===
				'compareChain'
		),
	);
	if (dispatches.size === 0) return undefined;
	return {
		dispatches,
		switchAt: (dispatch) =>
			tryStructureSwitchRegion(
				cfgWithEntry(cfg, dispatch),
				analyses,
				descriptors,
				(cursor, childAllowed) => {
					if (cursor === dispatch) return null;
					const bounded = childAllowed == null
						? scope
						: childAllowed.intersection(scope);
					return containedRegion(
						regionAt(cursor, bounded),
						bounded,
					);
				},
				{ dispatchBlock: dispatch },
			),
	};
}

/**
 * Compose a protected scope exactly after the readable recognizers leave a
 * segment behind. Resume boundaries and handler-only loop backedges can give a
 * source-level `try` several graph entries even though its normal-flow body is
 * one bounded forest. Exceptional edges to this handler (or its owning
 * finalizer) are consumed by the surrounding exception Region and therefore
 * form the forest boundary rather than additional skeleton edges.
 */
function tryStructureProtectedScopeForest(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	descriptor: ExceptionDescriptor,
	regionAt: RegionAt | undefined,
	deferProtectedExits: boolean,
	normalFinalizerCopyRoots: AddressSet<number>,
	abruptFinalizerCopyRoots: AddressSet<number>,
	analyses: CFGAnalyses | undefined,
	structuredHandlers?: AddressSet<number>,
	recoveredSwitches?: RecoveredSwitches,
	ownershipScope?: AddressSet<number>,
): Region | null {
	if (!analyses || !regionAt) return null;
	const allowedProtectedBody = protectedBodyBlocks(
		cfg,
		descriptor,
		descriptors,
	);
	const handlerBoundaries = new AddressSet<number>([descriptor.handler]);
	if (descriptor.canonicalFinallyAddress != null) {
		handlerBoundaries.add(descriptor.canonicalFinallyAddress);
	}
	let parent = descriptors.exceptions.forest.parentByHandler.get(
		descriptor.handler,
	);
	while (parent != null && !handlerBoundaries.has(parent)) {
		handlerBoundaries.add(parent);
		parent = descriptors.exceptions.forest.parentByHandler.get(parent);
	}
	const enclosingHandlerBoundaries = new AddressSet<number>(
		descriptors.exceptions.handlers
			.filter((candidate) =>
				candidate !== descriptor &&
				!allowedProtectedBody.has(candidate.handler) &&
				candidate.protectedBlocks.intersection(allowedProtectedBody)
						.size > 0
			)
			.map((candidate) => candidate.handler),
	);
	// A try wholly inside this range is contracted the same way a loop is, so
	// its exceptional edges become internal to one skeleton node. Without that
	// the composition sees a bare edge from one protected block to another and
	// declines, even though the nested descriptor is exactly its owner.
	const nestedDescriptors = descriptors.exceptions.handlers.filter(
		(candidate) =>
			candidate !== descriptor &&
			candidate.protectedBlocks.size > 0 &&
			allowedProtectedBody.has(candidate.handler) &&
			candidate.protectedBlocks.isSubsetOf(allowedProtectedBody) &&
			!descriptors.exceptions.elidedIteratorCleanupHandlers.has(
				candidate.handler,
			),
	);
	const nestedHandlers = new AddressSet<number>(
		nestedDescriptors.map((candidate) => candidate.handler),
	);
	const nestedRoots = nestedDescriptors.filter((candidate) => {
		const owner = descriptors.exceptions.forest.parentByHandler.get(
			candidate.handler,
		);
		return owner == null || !nestedHandlers.has(owner);
	});
	const nestedByEntry = new Map<number, ExceptionDescriptor>();
	for (const candidate of nestedRoots) {
		for (
			const protectedEntry of candidate.protectedEntries.intersection(
				allowedProtectedBody,
			)
		) {
			nestedByEntry.set(protectedEntry, candidate);
		}
	}
	const nestedEntries = new AddressSet<number>(
		nestedRoots.flatMap((candidate) => [
			...candidate.protectedEntries.intersection(allowedProtectedBody),
		]),
	);
	const nestedProtectedBlocks = new AddressSet<number>(
		nestedRoots.flatMap((candidate) => [...candidate.protectedBlocks]),
	);

	const scopeSwitches = recoveredSwitches ??
		recoveredCompareChainSwitchesForScope(
			cfg,
			analyses,
			descriptors,
			regionAt,
			allowedProtectedBody,
		);
	const composed = tryStructureBoundedScopeForest(
		cfg,
		analyses,
		(loop) => {
			const region = regionAt(loop.header, allowedProtectedBody);
			return region?.kind === 'loop' ? region : null;
		},
		{
			entry: cfg.entry,
			allowed: allowedProtectedBody,
			labelPrefix: `try_${descriptor.handler.toString(16)}`,
			completion: (from, to) => {
				if (
					deferProtectedExits &&
					abruptFinalizerCopyRoots.has(to)
				) {
					return protectedDeferredExitRegion(to);
				}
				return terminalExitRegion(
					cfg,
					to,
					deferProtectedExits,
					new AddressSet<number>(),
					[],
					normalFinalizerCopyRoots.union(
						abruptFinalizerCopyRoots,
					),
					descriptors,
					{ from, to, kind: 'normal' },
					[],
					structuredHandlers,
					false,
					{ orphaned: false },
					ownershipScope,
				) ?? {
					kind: 'sequence',
					regions: [],
					sourceBlocks: new AddressSet<number>(),
				};
			},
			exceptionBoundary: (from, to) =>
				(descriptor.protectedBlocks.has(from) &&
					handlerBoundaries.has(to)) ||
				(allowedProtectedBody.has(from) &&
					enclosingHandlerBoundaries.has(to)),
		},
		scopeSwitches,
		nestedEntries.size === 0 ? undefined : {
			entries: nestedEntries,
			protectedBlocks: nestedProtectedBlocks,
			exceptionAt: (protectedEntry) => {
				const nested = nestedByEntry.get(protectedEntry);
				if (!nested) return null;
				const bound = contractedExceptionBlocks(
					cfg,
					nested,
					descriptors,
				).intersection(allowedProtectedBody);
				const candidate = tryStructureExceptionRegion(
					cfgWithEntry(cfg, protectedEntry),
					descriptors,
					(cursor, childAllowed) => {
						if (cursor === protectedEntry) return null;
						return regionAt(
							cursor,
							(childAllowed ?? bound).intersection(bound),
						);
					},
					bound,
					new AddressSet<number>(),
					analyses,
					{ exactScope: true },
				);
				return candidate?.sourceBlocks.isSubsetOf(bound) &&
						candidate.sourceBlocks.has(nested.handler) &&
						nested.protectedBlocks.isSubsetOf(
							regionCoveredBlocks(candidate),
						)
					? candidate
					: null;
			},
		},
	);
	if (
		composed == null &&
		Deno.env.get('ARES_DEBUG_PROTECTED') ===
			descriptor.handler.toString(16)
	) {
		console.error(
			`protected forest 0x${descriptor.handler.toString(16)} declined: ` +
				`entry=0x${cfg.entry.toString(16)} ` +
				`allowed=${descriptor.protectedBlocks.size}`,
		);
	}
	return composed;
}

function hasCycleWithin(
	cfg: ImmutableCFG,
	allowed: AddressSet<number>,
): boolean {
	const visiting = new AddressSet<number>();
	const visited = new AddressSet<number>();
	const visit = (addr: number): boolean => {
		if (!allowed.has(addr)) return false;
		if (visiting.has(addr)) return true;
		if (visited.has(addr)) return false;
		visiting.add(addr);
		for (const successor of cfg.normalSuccessors.get(addr) ?? []) {
			if (visit(successor)) return true;
		}
		visiting.delete(addr);
		visited.add(addr);
		return false;
	};
	for (const addr of allowed) {
		if (visit(addr)) return true;
	}
	return false;
}

function structureProtectedDAGFrom(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	owner: ExceptionDescriptor,
	entry: number,
	allowed: AddressSet<number>,
	consumed: AddressSet<number>,
	stop?: number,
	deferProtectedExits = false,
	normalFinalizerCopyRoots = new AddressSet<number>(),
	abruptFinalizerCopyRoots = new AddressSet<number>(),
	regionAt?: RegionAt,
	structuredHandlers: AddressSet<number> = new AddressSet<number>(),
	analyses?: CFGAnalyses,
	ownershipScope?: AddressSet<number>,
): Region | null {
	if (!allowed.has(entry) || consumed.has(entry) || entry === stop) {
		return null;
	}
	const block = cfg.blocks.get(entry);
	if (!block) return null;

	const current = new AddressSet(consumed);
	current.add(entry);

	let region: Region;
	let next: number | undefined;
	let sideExitLabel: string | undefined;
	const nestedDescriptor = exceptionStartingAt(
		cfg,
		entry,
		descriptors,
		allowed,
	);
	const structuringDirectNested = nestedDescriptor != null &&
		nestedDescriptor.handler !== owner.handler &&
		(
			!structuredHandlers.has(nestedDescriptor.handler) ||
			!consumed.has(nestedDescriptor.handler)
		);
	// Both the direct and the regionAt-sourced structuring below are speculative:
	// the resulting nestedRegion can be discarded (subset-of-consumed, single
	// block, or an if/basic branch chosen instead). Snapshot the ledger so any
	// handlers marked while building a discarded region are rolled back, letting
	// the genuine structuring re-open them later.
	const ledgerBeforeNested = new AddressSet(structuredHandlers);
	const directNestedRegion = structuringDirectNested
		? structureExceptionDescriptor(
			cfgWithEntry(cfg, entry),
			descriptors,
			nestedDescriptor!,
			regionAt,
			undefined,
			structuredHandlers,
			analyses,
			undefined,
			ownershipScope,
			ownershipScope != null,
		)
		: null;
	// The bounded composer owns ordinary sequences and branches. Accepting a
	// generic prefix Region here lets a weak-SESE walk stop at the first hard
	// branch while still short-circuiting this edge-aware composition. A proven
	// folded predicate chain is different: it is the only representation that
	// preserves a shared arm without emitting it once per predicate. Build that
	// candidate without recursive arms, accept it only when fully structured and
	// bounded, then let this composer continue at its unique exit.
	const foldedPredicateCandidate = block.terminator.kind === 'if' && analyses
		? tryStructureIfRegion(
			cfgWithEntry(cfg, entry),
			analyses,
			undefined,
			allowed,
			false,
			undefined,
			descriptors.compatibility,
		)
		: null;
	const foldedPredicate = foldedPredicateCandidate?.kind === 'if' &&
			!regionContainsFallback(foldedPredicateCandidate) &&
			(foldedPredicateCandidate.predicateBlocks?.size ?? 0) > 1 &&
			foldedPredicateCandidate.sourceBlocks.isSubsetOf(allowed) &&
			regionUnstructuredBranches(foldedPredicateCandidate, cfg).size === 0
		? foldedPredicateCandidate
		: null;
	const recursiveCandidate = regionAt?.(entry, allowed);
	const recursiveNestedRegion = foldedPredicate ??
		(recursiveCandidate?.kind === 'loop' ||
				recursiveCandidate?.kind === 'switch' ||
				recursiveCandidate?.kind === 'delegateYield'
			? recursiveCandidate
			: null);
	const nestedRegion = directNestedRegion ??
		(block.terminator.kind === 'if' &&
				recursiveNestedRegion?.kind !== 'loop' &&
				recursiveNestedRegion?.kind !== 'if'
			? null
			: recursiveNestedRegion);
	const useNestedRegion = !!(
		nestedRegion &&
		(nestedRegion.sourceBlocks.size > 1 || nestedRegion.kind === 'loop') &&
		(
			directNestedRegion != null ||
			nestedRegion.sourceBlocks.isSubsetOf(allowed)
		) &&
		!nestedRegion.sourceBlocks.isSubsetOf(consumed)
	);
	// Roll speculative handler ownership back before recursively composing the
	// replacement arms. Waiting until after those arms are built makes a genuine
	// nested try appear already consumed and prevents an exception-spanning loop
	// in the replacement from claiming it.
	if (!useNestedRegion) {
		for (const handlerAddr of [...structuredHandlers]) {
			if (!ledgerBeforeNested.has(handlerAddr)) {
				structuredHandlers.delete(handlerAddr);
			}
		}
	}
	if (useNestedRegion && nestedRegion) {
		region = nestedRegion;
		for (const addr of region.sourceBlocks) current.add(addr);
		const nestedNormalExit = nestedRegion.kind === 'tryFinally'
			? firstAllowedExitCandidate(nestedRegion, allowed, current)
			: undefined;
		next = nestedNormalExit ??
			uniqueProtectedExit(cfg, region.sourceBlocks, allowed) ??
			undefined;
		if (
			(region.kind === 'tryCatch' || region.kind === 'tryFinally') &&
			next != null
		) {
			const routed = routeNestedProtectedSideExit(
				region,
				allowed,
				next,
				cfg,
				`try_${owner.handler.toString(16)}_nested_${
					region.handlerAddress.toString(16)
				}`,
			);
			if (routed) {
				region = routed.region;
				sideExitLabel = routed.label;
			}
		}
	} else if (block.terminator.kind === 'if') {
		const trueTarget = block.terminator.taken;
		const falseTarget = block.terminator.fallthrough;
		const trueInAllowed = allowed.has(trueTarget);
		const falseInAllowed = allowed.has(falseTarget);
		const trueIsNormalExit = !trueInAllowed &&
			normalFinalizerCopyRoots.has(trueTarget);
		const falseIsNormalExit = !falseInAllowed &&
			normalFinalizerCopyRoots.has(falseTarget);
		const outsideTarget = trueInAllowed ? falseTarget : trueTarget;
		const outsideIsAbrupt = trueInAllowed !== falseInAllowed &&
			outsideTarget !== stop &&
			terminalExitRegion(
					cfg,
					outsideTarget,
					deferProtectedExits,
					new AddressSet<number>(),
					[],
					normalFinalizerCopyRoots.union(abruptFinalizerCopyRoots),
					undefined,
					undefined,
					undefined,
					undefined,
					undefined,
					undefined,
					ownershipScope,
				) != null;
		// An arm that leaves for a shared terminal stays empty, so the branch's
		// continuation is that terminal. Naming the sibling target the join
		// instead makes it the code after the `if`, which drops the branch and
		// runs one arm unconditionally.
		const oneSidedContinuation = trueInAllowed !== falseInAllowed
			? trueIsNormalExit || falseIsNormalExit || !outsideIsAbrupt ||
					leavesToSharedProtectedTerminal(
						cfg,
						outsideTarget,
						allowed,
						deferProtectedExits,
					)
				? null
				: (trueInAllowed ? trueTarget : falseTarget)
			: null;
		const inheritedJoin = stop != null &&
				(trueTarget === stop || falseTarget === stop)
			? stop
			: null;
		const join = oneSidedContinuation ?? nearestProtectedJoin(
			cfg,
			trueTarget,
			falseTarget,
			allowed,
		) ?? nearestSharedProtectedTerminal(
			cfg,
			trueTarget,
			falseTarget,
			allowed,
		) ?? inheritedJoin;
		const consequent = structureProtectedArm(
			cfg,
			descriptors,
			owner,
			trueTarget,
			entry,
			allowed,
			current,
			join ?? undefined,
			deferProtectedExits,
			normalFinalizerCopyRoots,
			abruptFinalizerCopyRoots,
			trueIsNormalExit,
			regionAt,
			structuredHandlers,
			analyses,
			ownershipScope,
		);
		const alternate = structureProtectedArm(
			cfg,
			descriptors,
			owner,
			falseTarget,
			entry,
			allowed,
			current,
			join ?? undefined,
			deferProtectedExits,
			normalFinalizerCopyRoots,
			abruptFinalizerCopyRoots,
			falseIsNormalExit,
			regionAt,
			structuredHandlers,
			analyses,
			ownershipScope,
		);
		region = {
			kind: 'if',
			header: entry,
			test: t.cloneNode(block.terminator.test, true),
			consequent,
			alternate,
			join: join ?? entry,
			sourceBlocks: new AddressSet([
				entry,
				...consequent.sourceBlocks,
				...alternate.sourceBlocks,
			]),
		};
		for (const addr of region.sourceBlocks) current.add(addr);
		next = join ?? undefined;
	} else {
		region = {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([entry]),
		};
		const successors = cfg.normalSuccessors.get(entry) ??
			new AddressSet<number>();
		if (successors.size === 1) {
			const [successor] = [...successors];
			if (successor !== stop && current.has(successor)) {
				const terminalReference =
					sharedProtectedTerminalReferenceForEdge(
						cfg,
						descriptors,
						entry,
						successor,
					);
				if (terminalReference) {
					return sequenceRegion([region, terminalReference]);
				}
			}
			if (allowed.has(successor) && successor !== stop) {
				next = successor;
			} else if (
				successor !== stop &&
				(cfg.normalPredecessors.get(successor)?.size ?? 0) === 1
			) {
				const terminal = terminalExitRegion(
					cfg,
					successor,
					deferProtectedExits,
					new AddressSet<number>(),
					[],
					normalFinalizerCopyRoots.union(abruptFinalizerCopyRoots),
					descriptors,
					{ from: entry, to: successor, kind: 'normal' },
					[],
					structuredHandlers,
					false,
					{ orphaned: false },
					ownershipScope,
				);
				if (terminal) {
					return {
						kind: 'sequence',
						regions: [region, terminal],
						// This path is private (`successor` has one predecessor), so the
						// terminal is represented here rather than shared after the try.
						// Claim it as well; otherwise the enclosing sequence emits a
						// copied-finalizer return a second time after the try/finally.
						sourceBlocks: region.sourceBlocks.union(
							terminal.sourceBlocks,
						),
					};
				}
			}
		}
	}

	// The speculative nestedRegion was not committed as this block's region:
	// undo the ledger marks it made so the genuine structuring re-fires.
	if (region !== nestedRegion) {
		for (const handlerAddr of [...structuredHandlers]) {
			if (!ledgerBeforeNested.has(handlerAddr)) {
				structuredHandlers.delete(handlerAddr);
			}
		}
	}

	const closeSideExit = (candidate: Region): Region =>
		sideExitLabel == null ? candidate : {
			kind: 'sequence',
			regions: [candidate],
			exitLabel: sideExitLabel,
			sourceBlocks: new AddressSet(candidate.sourceBlocks),
		};
	if (next == null || current.has(next)) return closeSideExit(region);
	// A child arm is deliberately bounded before its parent's join. Reaching
	// that stop closes the child; treating it as an out-of-range terminal walks
	// through the join and steals a shared Phi/return into this one arm.
	if (next === stop) return closeSideExit(region);
	if (!allowed.has(next)) {
		const sharedReturn = sharedCatchReturnReference(
			cfg,
			owner,
			region,
			next,
			deferProtectedExits,
		);
		if (sharedReturn) {
			return closeSideExit({
				kind: 'sequence',
				regions: [region, sharedReturn],
				sourceBlocks: new AddressSet(region.sourceBlocks),
			});
		}
		const incomingSources = [...region.sourceBlocks].filter((from) =>
			cfg.normalSuccessors.get(from)?.has(next)
		);
		const continuationPredecessors = cfg.normalPredecessors.get(next) ??
			new AddressSet<number>();
		const sharedPhiContinuation = incomingSources.length > 1 &&
			continuationPredecessors.isSubsetOf(
				new AddressSet(incomingSources),
			);
		const terminal = terminalExitRegion(
			cfg,
			next,
			deferProtectedExits,
			new AddressSet<number>(),
			[],
			normalFinalizerCopyRoots.union(abruptFinalizerCopyRoots),
			descriptors,
			incomingSources.length === 1
				? {
					from: incomingSources[0],
					to: next,
					kind: 'normal',
				}
				: undefined,
			[],
			structuredHandlers,
			sharedPhiContinuation,
			{ orphaned: false },
			ownershipScope,
		);
		if (!terminal) {
			return region;
		}
		return closeSideExit({
			kind: 'sequence',
			regions: [region, terminal],
			sourceBlocks: new AddressSet([
				...region.sourceBlocks,
				...terminal.sourceBlocks,
			]),
		});
	}
	const continuation = structureProtectedDAGFrom(
		cfg,
		descriptors,
		owner,
		next,
		allowed,
		current,
		stop,
		deferProtectedExits,
		normalFinalizerCopyRoots,
		abruptFinalizerCopyRoots,
		regionAt,
		structuredHandlers,
		analyses,
		ownershipScope,
	);
	if (!continuation) return closeSideExit(region);
	return closeSideExit({
		kind: 'sequence',
		regions: [region, continuation],
		sourceBlocks: new AddressSet([
			...region.sourceBlocks,
			...continuation.sourceBlocks,
		]),
	});
}

function sharedProtectedTerminalReferenceForEdge(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	from: number,
	target: number,
): Region | null {
	const edge: CFGEdge = { from, to: target, kind: 'normal' };
	const block = cfg.blocks.get(target);
	if (
		!block ||
		(block.terminator.kind !== 'return' &&
			block.terminator.kind !== 'throw' &&
			block.terminator.kind !== 'unreachable') ||
		!cfg.normalSuccessors.get(from)?.has(target) ||
		!descriptors.phis.phisByEdgeKey.has(edgeKey(edge))
	) return null;
	return {
		kind: 'terminalReference',
		entry: target,
		edge,
		sourceBlocks: new AddressSet(),
	};
}

/**
 * Reference a shared, inert return on one protected fallthrough edge.
 *
 * The terminal stays owned by the enclosing continuation; this leaf supplies
 * only this edge's Phi copy and return. Restrict the rewrite to a catch-only
 * boundary and a non-throwing return value, so it cannot move evaluation under
 * a handler or cause a finally body to run twice.
 */
function sharedCatchReturnReference(
	cfg: ImmutableCFG,
	owner: ExceptionDescriptor,
	region: Region,
	target: number,
	deferProtectedExits: boolean,
): Region | null {
	if (deferProtectedExits || owner.kind !== 'catch') return null;
	const block = cfg.blocks.get(target);
	if (
		!block || block.terminator.kind !== 'return' ||
		(cfg.normalPredecessors.get(target)?.size ?? 0) <= 1 ||
		(cfg.exceptionalSuccessors.get(target)?.size ?? 0) !== 0 ||
		!inertSharedReturnBody(block.body)
	) return null;
	const exits = [...region.sourceBlocks].filter((from) =>
		cfg.normalSuccessors.get(from)?.has(target)
	);
	if (exits.length !== 1) return null;
	return sharedCatchReturnReferenceForEdge(
		cfg,
		owner,
		exits[0]!,
		target,
		deferProtectedExits,
	);
}

function sharedCatchReturnReferenceForEdge(
	cfg: ImmutableCFG,
	owner: ExceptionDescriptor,
	from: number,
	target: number,
	deferProtectedExits: boolean,
): Region | null {
	if (deferProtectedExits || owner.kind !== 'catch') return null;
	const block = cfg.blocks.get(target);
	if (
		!block || block.terminator.kind !== 'return' ||
		(cfg.normalPredecessors.get(target)?.size ?? 0) <= 1 ||
		(cfg.exceptionalSuccessors.get(target)?.size ?? 0) !== 0 ||
		!inertSharedReturnBody(block.body) ||
		!cfg.normalSuccessors.get(from)?.has(target)
	) return null;
	const handlers = cfg.exceptionalSuccessors.get(from!) ??
		new AddressSet<number>();
	if (handlers.size !== 1 || !handlers.has(owner.handler)) return null;
	return {
		kind: 'terminalReference',
		entry: target,
		edge: { from: from!, to: target, kind: 'normal' },
		sourceBlocks: new AddressSet(),
	};
}

function inertSharedReturnBody(body: readonly t.Statement[]): boolean {
	let returns = 0;
	for (const [index, statement] of body.entries()) {
		if (t.isReturnStatement(statement)) {
			if (index !== body.length - 1) return false;
			returns++;
			const argument = statement.argument;
			if (
				argument != null && !t.isIdentifier(argument) &&
				!t.isNullLiteral(argument) && !t.isBooleanLiteral(argument) &&
				!t.isNumericLiteral(argument) && !t.isStringLiteral(argument)
			) return false;
			continue;
		}
		if (
			!t.isVariableDeclaration(statement, { kind: 'const' }) ||
			statement.declarations.length !== 1
		) return false;
		const [declaration] = statement.declarations;
		if (
			!t.isIdentifier(declaration.id) ||
			!t.isCallExpression(declaration.init) ||
			!t.isV8IntrinsicIdentifier(declaration.init.callee, { name: 'Phi' })
		) return false;
	}
	return returns === 1;
}

/**
 * Close an inner exception Region together with the protected suffix one of
 * its normal exits skips. Straight-line recovery often discovers the inner
 * try and that suffix separately, so the edge-aware routing in
 * `structureProtectedDAGFrom` has no opportunity to see both at once.
 */
function routeNestedExceptionSideExitsInProtectedBody(
	region: Region,
	allowed: AddressSet<number>,
	cfg: ImmutableCFG,
	owner: ExceptionDescriptor,
): Region | null {
	if (region.kind !== 'sequence' || region.exitLabel) return null;
	const regions = flattenUnlabelledSequence(region.regions);
	for (let index = regions.length - 1; index >= 0; index--) {
		const candidate = regions[index]!;
		if (candidate.kind !== 'tryCatch' && candidate.kind !== 'tryFinally') {
			continue;
		}
		const leavingTargets = new AddressSet<number>();
		for (const from of candidate.sourceBlocks) {
			for (const to of cfg.normalSuccessors.get(from) ?? []) {
				if (!candidate.sourceBlocks.has(to)) leavingTargets.add(to);
			}
		}
		const continuations = [...leavingTargets].filter((target) =>
			allowed.has(target)
		);
		if (continuations.length !== 1) continue;
		const routed = routeNestedProtectedSideExit(
			candidate,
			allowed,
			continuations[0]!,
			cfg,
			`try_${owner.handler.toString(16)}_nested_${
				candidate.handlerAddress.toString(16)
			}`,
		);
		if (!routed) continue;
		const suffix = sequenceRegion(
			[routed.region, ...regions.slice(index + 1)],
			routed.label,
		);
		return sequenceRegion([...regions.slice(0, index), suffix]);
	}
	return null;
}

function flattenUnlabelledSequence(regions: readonly Region[]): Region[] {
	return regions.flatMap((region) =>
		region.kind === 'sequence' && region.exitLabel == null
			? flattenUnlabelledSequence(region.regions)
			: [region]
	);
}

/**
 * Route a nested try's outer-scope exit around its in-scope continuation.
 *
 * A contracted inner exception Region can complete in two ways: continue with
 * the enclosing protected body, or leave that body at its shared terminal. A
 * plain Sequence makes the latter path fall into the former. Keep the original
 * edge at its lexical source (so its Phi action is emitted there), then break a
 * label surrounding the remainder of the protected body.
 */
function routeNestedProtectedSideExit(
	region: Extract<Region, { kind: 'tryCatch' | 'tryFinally' }>,
	allowed: AddressSet<number>,
	continuation: number,
	cfg: ImmutableCFG,
	labelPrefix: string,
): { region: typeof region; label: string } | null {
	if (!allowed.has(continuation)) return null;
	const leaving: Array<{ from: number; to: number }> = [];
	for (const from of region.sourceBlocks) {
		for (const to of cfg.normalSuccessors.get(from) ?? []) {
			if (!region.sourceBlocks.has(to)) leaving.push({ from, to });
		}
	}
	if (!leaving.some((edge) => edge.to === continuation)) return null;
	const sideEdges = leaving.filter((edge) => !allowed.has(edge.to));
	const sideTargets = new AddressSet(sideEdges.map((edge) => edge.to));
	if (sideEdges.length === 0 || sideTargets.size !== 1) return null;
	const [target] = [...sideTargets];
	const terminator = cfg.blocks.get(target)?.terminator;
	if (
		terminator?.kind !== 'return' && terminator?.kind !== 'throw' &&
		terminator?.kind !== 'unreachable'
	) return null;
	const label = `${labelPrefix}_exit_${target.toString(16)}`;
	let routed: Region = region;
	for (const edge of sideEdges) {
		const placed = placeNestedProtectedSideExit(routed, edge, label, cfg);
		if (!placed) return null;
		routed = placed;
	}
	return { region: routed as typeof region, label };
}

function placeNestedProtectedSideExit(
	region: Region,
	edge: { from: number; to: number },
	label: string,
	cfg: ImmutableCFG,
): Region | null {
	const transfer = (): Region => ({
		kind: 'sequence',
		regions: [{
			kind: 'deferredExit',
			exit: {
				kind: 'toJoin',
				edge: { ...edge, kind: 'normal' },
				target: edge.to,
				actions: [],
			},
			sourceBlocks: new AddressSet(),
		}, {
			kind: 'labelBreak',
			label,
			target: edge.to,
			sourceBlocks: new AddressSet(),
		}],
		sourceBlocks: new AddressSet(),
	});
	if (region.kind === 'if' && region.header === edge.from) {
		const terminator = cfg.blocks.get(edge.from)?.terminator;
		if (terminator?.kind !== 'if') return null;
		if (terminator.taken === edge.to) {
			if (region.consequent.sourceBlocks.size !== 0) return null;
			return { ...region, consequent: transfer() };
		}
		if (terminator.fallthrough === edge.to) {
			if (region.alternate.sourceBlocks.size !== 0) return null;
			return { ...region, alternate: transfer() };
		}
		return null;
	}
	if (region.kind === 'basic' && region.sourceBlocks.has(edge.from)) {
		const successors = cfg.normalSuccessors.get(edge.from) ?? [];
		if (![...successors].includes(edge.to)) return null;
		return {
			kind: 'sequence',
			regions: [region, transfer()],
			sourceBlocks: new AddressSet(region.sourceBlocks),
		};
	}
	const replace = (child: Region): Region | null =>
		child.sourceBlocks.has(edge.from)
			? placeNestedProtectedSideExit(child, edge, label, cfg)
			: child;
	switch (region.kind) {
		case 'sequence': {
			const owners = region.regions.filter((child) =>
				child.sourceBlocks.has(edge.from)
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
			) {
				return null;
			}
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

function regionContainsFallback(region: Region): boolean {
	if (region.kind === 'fallback') return true;
	switch (region.kind) {
		case 'sequence':
			return region.regions.some(regionContainsFallback);
		case 'if':
			return regionContainsFallback(region.consequent) ||
				regionContainsFallback(region.alternate);
		case 'switch':
			return region.cases.some((switchCase) =>
				regionContainsFallback(switchCase.body)
			) || regionContainsFallback(region.defaultBody);
		case 'tryCatch':
			return regionContainsFallback(region.body) ||
				regionContainsFallback(region.handler);
		case 'tryFinally':
			return regionContainsFallback(region.body) ||
				regionContainsFallback(region.finalizer);
		case 'loop':
			return regionContainsFallback(region.body);
		default:
			return false;
	}
}

/**
 * A terminal the arm has to leave to the enclosing composition: a
 * return/throw block outside the bound that more than one protected path
 * reaches. `structureProtectedArm` keeps such an arm empty so the terminal is
 * emitted once after the try, which means the branch's continuation is that
 * terminal — not the sibling target inside the bound.
 */
function leavesToSharedProtectedTerminal(
	cfg: ImmutableCFG,
	target: number,
	allowed: AddressSet<number>,
	deferProtectedExits: boolean,
): boolean {
	if (deferProtectedExits || allowed.has(target) || allowed.size > 8) {
		return false;
	}
	const block = cfg.blocks.get(target);
	if (!block) return false;
	return (block.terminator.kind === 'return' ||
		block.terminator.kind === 'throw' ||
		block.terminator.kind === 'unreachable') &&
		(cfg.normalPredecessors.get(target)?.size ?? 0) > 1;
}

function structureProtectedArm(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	owner: ExceptionDescriptor,
	entry: number,
	predecessor: number,
	allowed: AddressSet<number>,
	consumed: AddressSet<number>,
	stop?: number,
	deferProtectedExits = false,
	normalFinalizerCopyRoots = new AddressSet<number>(),
	abruptFinalizerCopyRoots = new AddressSet<number>(),
	forceNormalExit = false,
	regionAt?: RegionAt,
	structuredHandlers: AddressSet<number> = new AddressSet<number>(),
	analyses?: CFGAnalyses,
	ownershipScope?: AddressSet<number>,
): Region {
	if (entry === stop) {
		return {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		};
	}
	if (forceNormalExit) {
		return {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		};
	}
	if (!allowed.has(entry)) {
		if (deferProtectedExits && abruptFinalizerCopyRoots.has(entry)) {
			return protectedDeferredExitRegion(entry) ?? {
				kind: 'sequence',
				regions: [],
				sourceBlocks: new AddressSet(),
			};
		}
		// The catch retries: this arm re-enters the protected header, which the
		// retry loop wrapping the whole try/catch owns. The catch body's own
		// fallthrough is that backedge, so the arm is empty; walking into the
		// header instead makes the catch claim the protected blocks twice.
		if (retriesAtProtectedHeader(cfg, descriptors, owner, entry, allowed)) {
			return {
				kind: 'sequence',
				regions: [],
				sourceBlocks: new AddressSet(),
			};
		}
		if (
			leavesToSharedProtectedTerminal(
				cfg,
				entry,
				allowed,
				deferProtectedExits,
			)
		) {
			// In a bounded protected DAG this terminal is a continuation shared by
			// more than one protected
			// path. Owning it in the first arm duplicates/misorders the return and
			// leaves the other incoming Phi edge with no lexical emission site.
			// Leave the arm empty: its direct edge action is emitted by emitIfArm,
			// while the enclosing sequence appends the terminal once after the
			// try/catch and places the remaining fallthrough action there. Larger
			// protected forests need their branch ordering validated as a whole;
			// accepting only this local ownership fact can mask a misnested branch.
			return {
				kind: 'sequence',
				regions: [],
				sourceBlocks: new AddressSet(),
			};
		}
		const sharedReturn = sharedCatchReturnReferenceForEdge(
			cfg,
			owner,
			predecessor,
			entry,
			deferProtectedExits,
		);
		if (sharedReturn) return sharedReturn;
		return terminalExitRegion(
			cfg,
			entry,
			deferProtectedExits,
			new AddressSet<number>(),
			[],
			normalFinalizerCopyRoots.union(abruptFinalizerCopyRoots),
			descriptors,
			{ from: predecessor, to: entry, kind: 'normal' },
			[],
			structuredHandlers,
			false,
			{ orphaned: false },
			ownershipScope,
		) ?? {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		};
	}
	// A nested branch may discover a different terminal join and recursively
	// absorb the continuation named by its parent. That moves the shared suffix
	// into only one arm (for example, `if (!value)` becomes reachable solely from
	// the preceding `typeof` arm). Bound the child to blocks before the parent's
	// join; the enclosing call emits that join and its suffix once.
	const armAllowed = stop != null && allowed.has(stop)
		? allowed.difference(reachableWithin(cfg, stop, allowed))
		: allowed;
	return structureProtectedDAGFrom(
		cfg,
		descriptors,
		owner,
		entry,
		armAllowed,
		consumed,
		stop,
		deferProtectedExits,
		normalFinalizerCopyRoots,
		abruptFinalizerCopyRoots,
		regionAt,
		structuredHandlers,
		analyses,
		ownershipScope,
	) ?? {
		kind: 'sequence',
		regions: [],
		sourceBlocks: new AddressSet(),
	};
}

/**
 * Whether this out-of-scope arm is the catch's retry backedge.
 *
 * Recognized from the graph alone, so no caller has to thread the retry loop
 * through the protected DAG: the target has to open the owner's protected
 * range (directly or through its scalar prelude), the owner's landing pad has
 * to reach that target as its only way back, and the scope has to be the catch
 * body — the protected body never contains its own handler.
 */
function retriesAtProtectedHeader(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	owner: ExceptionDescriptor,
	entry: number,
	allowed: AddressSet<number>,
): boolean {
	if (owner.kind !== 'catch' || !allowed.has(owner.handler)) return false;
	if (
		descriptors.exceptions.finalizerCopyModel.copyDescriptorHandlers.has(
			owner.handler,
		)
	) return false;
	const terminator = cfg.blocks.get(entry)?.terminator;
	const opensRange = owner.protectedEntries.has(entry) ||
		(terminator?.kind === 'goto' &&
			owner.protectedEntries.has(terminator.target));
	if (!opensRange) return false;
	return handlerRetryControl(cfg, owner.handler, entry) != null;
}

function normalFinalizerCopyExitRoots(
	descriptor: ExceptionDescriptor,
): AddressSet<number> {
	return new AddressSet(
		descriptor.finallyCopies.filter((copy) => copy.kind === 'normalExit')
			.map((copy) => copy.copyRoot),
	);
}

function abruptFinalizerCopyExitRoots(
	descriptor: ExceptionDescriptor,
): AddressSet<number> {
	return new AddressSet(
		descriptor.finallyCopies.map((copy) => copy.copyRoot),
	);
}

function normalFinalizerCopyContinuations(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	preferredPredecessors?: AddressSet<number>,
): number[] {
	const continuations = new AddressSet<number>();
	for (const copy of descriptor.finallyCopies) {
		if (copy.kind === 'normalExit') {
			continuations.add(copy.next ?? copy.copyRoot);
			continue;
		}
		if (copy.kind === 'catchTrailer') {
			for (
				const successor of cfg.normalSuccessors.get(copy.copyRoot) ?? []
			) {
				continuations.add(successor);
			}
			continue;
		}
		if (copy.kind === 'abruptExit') {
			continuations.add(copy.copyRoot);
		}
	}
	// A finalizer whose only copies are other handlers' abrupt-exit trailers
	// names no continuation of its own, and the enclosing sequence is then left
	// to guess from the Region's forward edges — which include the shared
	// rethrow tail and so are not unique. The protected body's own normal
	// successors are that continuation: they are where control resumes once the
	// range completes without throwing.
	if (continuations.size === 0 && preferredPredecessors) {
		for (const block of preferredPredecessors) {
			for (const successor of cfg.normalSuccessors.get(block) ?? []) {
				if (preferredPredecessors.has(successor)) continue;
				continuations.add(successor);
			}
		}
	}
	return [...continuations].toSorted((left, right) => {
		if (!preferredPredecessors) return left - right;
		const leftPreferred = [...(cfg.normalPredecessors.get(left) ?? [])]
			.some((predecessor) => preferredPredecessors.has(predecessor));
		const rightPreferred = [...(cfg.normalPredecessors.get(right) ?? [])]
			.some((predecessor) => preferredPredecessors.has(predecessor));
		return Number(rightPreferred) - Number(leftPreferred) || left - right;
	});
}

function firstAllowedExitCandidate(
	region: Extract<Region, { kind: 'tryFinally' }>,
	allowed: AddressSet<number>,
	consumed: AddressSet<number>,
): number | undefined {
	for (const candidate of region.normalExitCandidates ?? []) {
		if (!allowed.has(candidate)) continue;
		if (consumed.has(candidate)) continue;
		return candidate;
	}
	return undefined;
}

/**
 * Whether folding from `block` leaves a range with no way to be opened.
 *
 * Only a protected *entry* matters: that is the block whose Region has to be
 * the `try`, and the one the recursion would otherwise never be offered. The
 * fold is refused only when it takes the range's last openable entry with it
 * -- while another entry stays outside the chain, some other path can still
 * open the handler, and declining there would cost folds that orphan nothing.
 */
function foldWouldOrphanRange(
	block: number,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	seen: AddressSet<number>,
	structuredHandlers?: AddressSet<number>,
): boolean {
	const copyHandlers = descriptors.exceptions.finalizerCopyModel
		.copyDescriptorHandlers;
	return descriptors.exceptions.handlers.some((descriptor) => {
		if (
			structuredHandlers?.has(descriptor.handler) ||
			copyHandlers.has(descriptor.handler) ||
			!descriptor.protectedEntries.has(block)
		) return false;
		return [...openableProtectedEntries(cfg, descriptor)].every((entry) =>
			entry === block || seen.has(entry)
		);
	});
}

function terminalExitRegion(
	cfg: ImmutableCFG,
	entry: number,
	deferProtectedExits = false,
	seen = new AddressSet<number>(),
	pending: t.Statement[] = [],
	copyRoots = new AddressSet<number>(),
	descriptors?: CFGDescriptors,
	incomingEdge?: CFGEdge,
	pendingPhiActions: EdgeAction[] = [],
	structuredHandlers?: AddressSet<number>,
	skipEntryPhiDeclarations = false,
	stopped: { orphaned: boolean } = { orphaned: false },
	ownershipScope?: AddressSet<number>,
): Region | null {
	if (ownershipScope && !ownershipScope.has(entry)) {
		const terminator = cfg.blocks.get(entry)?.terminator.kind;
		if (
			terminator !== 'return' &&
			terminator !== 'throw' &&
			terminator !== 'unreachable'
		) return null;
		const predecessors = cfg.normalPredecessors.get(entry) ??
			new AddressSet<number>();
		if (
			predecessors.size === 0 ||
			!predecessors.isSubsetOf(ownershipScope)
		) return null;
	}
	if (seen.has(entry)) return null;
	// Folding a chain into a terminal turns its blocks into statements, which
	// no longer carry the exceptional edges a `try` is built from. A block
	// belonging to a range nobody has opened yet would take its handler with
	// it, so the fold stops and the ordinary builders keep the block.
	if (
		descriptors &&
		foldWouldOrphanRange(entry, cfg, descriptors, seen, structuredHandlers)
	) {
		// The caller must keep this block for the ordinary builders instead of
		// standing in a deferred exit, which would name control nothing places.
		stopped.orphaned = true;
		return null;
	}
	seen.add(entry);
	const block = cfg.blocks.get(entry);
	if (!block) return null;
	const incomingPhiActions = terminalEntryPhiActions(
		descriptors,
		incomingEdge,
	);
	const loweredBody = copyRoots.has(entry)
		? { statements: [], actions: [] }
		: skipEntryPhiDeclarations
		? {
			statements: omitPhiDeclarations(
				block.body,
				descriptors?.phis.phisByBlock.get(entry) ?? [],
			),
			actions: [],
		}
		: lowerPhiDeclarationsForEdge(block.body, incomingPhiActions);
	// Accumulate this block's genuine statements onto the goto/fallthrough chain,
	// but never a finalizer-copy block's body (that would duplicate the finally and
	// re-declare its SSA temps). Copy-block statements are suppressed and their
	// finally body is emitted by the enclosing tryFinally.
	const carry = [
		...pending,
		...loweredBody.statements,
	];
	const carryPhiActions = [...pendingPhiActions, ...loweredBody.actions];
	// A copied close with a terminal still owns the function completion. Let the
	// terminal cases below preserve that return/throw; lowering the whole block
	// to the control-only marker would emit a bare `break` after the owning loop.
	if (
		deferProtectedExits &&
		block.terminator.kind !== 'return' &&
		block.terminator.kind !== 'throw' &&
		block.body.some((statement) =>
			statementContainsIntrinsic(statement, 'IteratorClose')
		)
	) {
		return protectedDeferredExitRegion(entry, true, seen);
	}
	if (
		deferProtectedExits &&
		(pending.length > 0 || block.body.length > 0) &&
		jumpsDirectlyToFunctionReturn(cfg, block)
	) {
		// The arm runs some genuine statements (e.g. `console.log("return1")`) then
		// jumps through a finally copy to `return v`. Defer as a functionReturn that
		// carries those statements + the return value; the finally copy in the
		// return block is dropped (the enclosing tryFinally emits the finally body).
		// `pending` accumulates block bodies traversed along the goto chain so that
		// value definitions in predecessor blocks (e.g. `r = "return1"`) are kept and
		// fold into their uses.
		const returnTarget = (block.terminator as { target: number }).target;
		const returnBlock = cfg.blocks.get(returnTarget);
		if (returnBlock && returnBlock.terminator.kind === 'return') {
			const statements = carry;
			return {
				kind: 'deferredExit',
				exit: {
					kind: 'functionReturn',
					actions: [
						...carryPhiActions,
						...statements.map((statement) => ({
							kind: 'statement' as const,
							statement: t.cloneNode(statement, true),
						})),
						{
							kind: 'return' as const,
							argument: terminalReturnArgument(
								returnBlock.body,
								returnBlock.terminator.argument,
							),
						},
					],
				},
				sourceBlocks: new AddressSet(seen),
			};
		}
		return protectedDeferredExitRegion(entry, true, seen);
	}
	switch (block.terminator.kind) {
		case 'return': {
			const split = splitAbruptFinalizerStatements(carry);
			const argument = split.terminal?.kind === 'return'
				? split.terminal.argument
				: block.terminator.argument;
			if (
				split.statements.length > 0 || carryPhiActions.length > 0
			) {
				return deferredTerminalRegion(
					'return',
					split.statements,
					argument ?? null,
					seen,
					carryPhiActions,
				);
			}
			return {
				kind: 'return',
				argument: terminalReturnArgument(
					block.body,
					block.terminator.argument,
				),
				sourceBlocks: new AddressSet(seen),
			};
		}
		case 'throw': {
			if (!block.terminator.argument) return null;
			const split = splitAbruptFinalizerStatements(carry);
			const argument = split.terminal?.kind === 'throw'
				? split.terminal.argument
				: block.terminator.argument;
			if (
				split.statements.length > 0 || carryPhiActions.length > 0
			) {
				return deferredTerminalRegion(
					'throw',
					split.statements,
					argument,
					seen,
					carryPhiActions,
				);
			}
			return {
				kind: 'throw',
				argument: t.cloneNode(block.terminator.argument, true),
				sourceBlocks: new AddressSet(seen),
			};
		}
		case 'goto':
			return terminalExitRegion(
				cfg,
				block.terminator.target,
				deferProtectedExits,
				seen,
				carry,
				copyRoots,
				descriptors,
				{ from: entry, to: block.terminator.target, kind: 'normal' },
				carryPhiActions,
				structuredHandlers,
				false,
				stopped,
				ownershipScope,
			) ?? (stopped.orphaned ? null : protectedDeferredExitRegion(
				entry,
				deferProtectedExits,
				seen,
			));
		default: {
			const successors = cfg.normalSuccessors.get(entry) ??
				new AddressSet<number>();
			if (successors.size !== 1) {
				return protectedDeferredExitRegion(
					entry,
					deferProtectedExits,
					seen,
				);
			}
			const [successor] = [...successors];
			return terminalExitRegion(
				cfg,
				successor,
				deferProtectedExits,
				seen,
				carry,
				copyRoots,
				descriptors,
				{ from: entry, to: successor, kind: 'normal' },
				carryPhiActions,
				structuredHandlers,
				false,
				stopped,
				ownershipScope,
			) ?? (stopped.orphaned ? null : protectedDeferredExitRegion(
				entry,
				deferProtectedExits,
				seen,
			));
		}
	}
}

function omitPhiDeclarations(
	statements: readonly t.Statement[],
	phis: readonly { target: t.Identifier }[],
): t.Statement[] {
	if (phis.length === 0) return [...statements];
	const targets = new Set(phis.map((phi) => phi.target.name));
	return statements.filter((statement) =>
		!t.isVariableDeclaration(statement) ||
		statement.declarations.some((declaration) =>
			!t.isIdentifier(declaration.id) ||
			!targets.has(declaration.id.name)
		)
	);
}

function terminalEntryPhiActions(
	descriptors: CFGDescriptors | undefined,
	edge: CFGEdge | undefined,
): EdgeAction[] {
	if (!descriptors || !edge) return [];
	const assignments = descriptors.phis.phisByEdgeKey.get(edgeKey(edge)) ?? [];
	return assignments.length === 0 ? [] : [{ kind: 'placedPhi', assignments }];
}

function lowerPhiDeclarationsForEdge(
	statements: readonly t.Statement[],
	actions: readonly EdgeAction[],
): { statements: t.Statement[]; actions: EdgeAction[] } {
	const assignments = new Map(
		actions.flatMap((action) =>
			action.kind === 'placedPhi'
				? action.assignments.map((assignment) =>
					[
						assignment.target.name,
						assignment,
					] as const
				)
				: []
		),
	);
	if (assignments.size === 0) {
		return { statements: [...statements], actions: [] };
	}
	const loweredActions: EdgePhiAssignment[] = [];
	const loweredStatements = statements.map((statement) => {
		const assignment = phiDeclarationAssignment(statement, assignments);
		if (!assignment) return statement;
		loweredActions.push(assignment);
		return t.expressionStatement(t.assignmentExpression(
			'=',
			t.cloneNode(assignment.target, true),
			t.cloneNode(assignment.value, true),
		));
	});
	return {
		statements: loweredStatements,
		actions: loweredActions.length === 0 ? [] : [
			{ kind: 'placedPhi', assignments: loweredActions },
		],
	};
}

function phiDeclarationAssignment(
	statement: t.Statement,
	assignments: ReadonlyMap<string, EdgePhiAssignment>,
): EdgePhiAssignment | null {
	if (
		!t.isVariableDeclaration(statement) ||
		statement.declarations.length !== 1
	) {
		return null;
	}
	const declaration = statement.declarations[0]!;
	if (
		!t.isIdentifier(declaration.id) ||
		!t.isCallExpression(declaration.init) ||
		!t.isV8IntrinsicIdentifier(declaration.init.callee, { name: 'Phi' })
	) {
		return null;
	}
	return assignments.get(declaration.id.name) ?? null;
}

function deferredTerminalRegion(
	kind: 'return' | 'throw',
	statements: readonly t.Statement[],
	argument: t.Expression | null,
	sourceBlocks = new AddressSet<number>(),
	prefixActions: readonly EdgeAction[] = [],
): Region {
	const terminal = kind === 'return'
		? {
			kind: 'return' as const,
			argument: argument == null ? null : t.cloneNode(argument, true),
		}
		: {
			kind: 'throw' as const,
			argument: t.cloneNode(argument!, true),
		};
	return {
		kind: 'deferredExit',
		exit: {
			kind: kind === 'return' ? 'functionReturn' : 'functionThrow',
			actions: [
				...prefixActions,
				...statements.map((statement) => ({
					kind: 'statement' as const,
					statement: t.cloneNode(statement, true),
				})),
				terminal,
			],
		},
		sourceBlocks: new AddressSet(sourceBlocks),
	};
}

function jumpsDirectlyToFunctionReturn(
	cfg: ImmutableCFG,
	block: NonNullable<ReturnType<ImmutableCFG['blocks']['get']>>,
): boolean {
	if (block.terminator.kind !== 'goto') return false;
	const target = cfg.blocks.get(block.terminator.target);
	return target?.terminator.kind === 'return';
}

function protectedDeferredExitRegion(
	target: number,
	enabled = true,
	sourceBlocks = new AddressSet<number>(),
): Region | null {
	return enabled
		? {
			kind: 'deferredExit',
			exit: {
				kind: 'loopExit',
				edge: { from: target, to: target, kind: 'normal' },
				target,
				actions: [],
			},
			sourceBlocks: new AddressSet(sourceBlocks),
		}
		: null;
}

function terminalReturnArgument(
	body: readonly t.Statement[],
	argument: t.Expression | null | undefined,
): t.Expression | null {
	if (!argument) return argument ?? null;
	if (!t.isIdentifier(argument)) return t.cloneNode(argument, true);
	for (let i = body.length - 1; i >= 0; i--) {
		const stmt = body[i];
		if (!t.isVariableDeclaration(stmt)) continue;
		for (const decl of stmt.declarations) {
			if (!t.isIdentifier(decl.id, { name: argument.name })) continue;
			if (!decl.init || !t.isExpression(decl.init)) continue;
			// A Phi declaration is a placement marker, not an executable value.
			// Its incoming-edge actions initialize the identifier before this
			// terminal; folding the marker into `return` leaks `%Phi(...)` again.
			if (
				t.isCallExpression(decl.init) &&
				t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })
			) continue;
			return t.cloneNode(decl.init, true);
		}
	}
	return t.cloneNode(argument, true);
}

function nearestProtectedJoin(
	cfg: ImmutableCFG,
	left: number,
	right: number,
	allowed: AddressSet<number>,
): number | null {
	const leftReachable = reachableWithin(cfg, left, allowed);
	const rightReachable = reachableWithin(cfg, right, allowed);
	const common = [...leftReachable].filter((addr) =>
		rightReachable.has(addr)
	);
	if (common.length === 0) return null;
	return common.toSorted((a, b) =>
		distanceWithin(cfg, left, a, allowed) +
			distanceWithin(cfg, right, a, allowed) -
			(distanceWithin(cfg, left, b, allowed) +
				distanceWithin(cfg, right, b, allowed)) ||
		a - b
	)[0];
}

/** A terminal immediately beyond two protected arms is their lexical join. */
function nearestSharedProtectedTerminal(
	cfg: ImmutableCFG,
	left: number,
	right: number,
	allowed: AddressSet<number>,
): number | null {
	const leftExits = protectedExitTargets(cfg, left, allowed);
	const rightExits = protectedExitTargets(cfg, right, allowed);
	const common = [...leftExits].filter((target) => {
		if (!rightExits.has(target)) return false;
		const terminator = cfg.blocks.get(target)?.terminator;
		return terminator?.kind === 'return' || terminator?.kind === 'throw' ||
			terminator?.kind === 'unreachable';
	});
	return common.length === 1 ? common[0]! : null;
}

function protectedExitTargets(
	cfg: ImmutableCFG,
	entry: number,
	allowed: AddressSet<number>,
): AddressSet<number> {
	const exits = new AddressSet<number>();
	if (!allowed.has(entry)) return exits;
	const seen = new AddressSet<number>();
	const pending = [entry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (seen.has(address) || !allowed.has(address)) continue;
		seen.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (allowed.has(successor)) pending.push(successor);
			else exits.add(successor);
		}
	}
	return exits;
}

function reachableWithin(
	cfg: ImmutableCFG,
	entry: number,
	allowed: AddressSet<number>,
): AddressSet<number> {
	const reachable = new AddressSet<number>();
	if (!allowed.has(entry)) return reachable;
	const queue = [entry];
	while (queue.length > 0) {
		const current = queue.shift()!;
		if (reachable.has(current)) continue;
		reachable.add(current);
		for (const successor of cfg.normalSuccessors.get(current) ?? []) {
			if (!allowed.has(successor) || reachable.has(successor)) continue;
			queue.push(successor);
		}
	}
	return reachable;
}

function distanceWithin(
	cfg: ImmutableCFG,
	from: number,
	to: number,
	allowed: AddressSet<number>,
): number {
	if (from === to) return 0;
	const seen = new AddressSet<number>();
	const queue: Array<{ addr: number; distance: number }> = [{
		addr: from,
		distance: 0,
	}];
	while (queue.length > 0) {
		const current = queue.shift()!;
		if (seen.has(current.addr)) continue;
		seen.add(current.addr);
		for (const successor of cfg.normalSuccessors.get(current.addr) ?? []) {
			if (!allowed.has(successor)) continue;
			if (successor === to) return current.distance + 1;
			queue.push({ addr: successor, distance: current.distance + 1 });
		}
	}
	return Number.MAX_SAFE_INTEGER;
}

function uniqueProtectedExit(
	cfg: ImmutableCFG,
	sourceBlocks: AddressSet<number>,
	protectedBlocks: AddressSet<number>,
): number | null {
	const exits = new AddressSet<number>();
	for (const block of sourceBlocks) {
		for (const succ of cfg.normalSuccessors.get(block) ?? []) {
			if (sourceBlocks.has(succ)) continue;
			if (!protectedBlocks.has(succ)) continue;
			exits.add(succ);
		}
	}
	return exits.size === 1 ? [...exits][0] : null;
}

function finalizerDeferredExits(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	descriptor: ExceptionDescriptor,
): DeferredExit[] {
	const exits: DeferredExit[] = [];
	const ownership = descriptors.exceptions.finalizerEdgeActions.filter(
		(action) =>
			action.handler === descriptor.handler &&
			(action.kind === 'catch-copy' || action.kind === 'abrupt-copy'),
	);
	for (const owned of ownership) {
		const suffix = descriptor.finallyCopySuffixes.find((candidate) =>
			candidate.copyRoot === owned.copyRoot &&
			candidate.ownerBlock === owned.ownerBlock
		);
		if (suffix) {
			let { statements, terminal } = splitAbruptFinalizerStatements(
				owned.statements,
			);
			const terminalOwnerBlock = protectedFinalizerCopyOwner(
				cfg,
				descriptor,
				owned.copyRoot,
			);
			if (!terminal && owned.next == null && terminalOwnerBlock != null) {
				terminal = reachableFinalizerCopyTerminal(
					cfg,
					descriptor,
					owned.copyRoot,
				) ?? undefined;
			}
			const actions: DeferredExit['actions'] = [{
				kind: 'finally',
				action: {
					canonical: owned.canonical,
					copyRoot: owned.copyRoot,
					ownerBlock: owned.ownerBlock,
					terminalOwnerBlock: terminalOwnerBlock ?? undefined,
					next: owned.next,
					kind: suffix.kind,
					statements,
				},
			}];
			if (terminal) actions.push(terminal);
			exits.push({
				kind: terminal?.kind === 'throw'
					? 'functionThrow'
					: 'functionReturn',
				edge: owned.next == null ? undefined : {
					from: owned.ownerBlock,
					to: owned.next,
					kind: 'normal',
				},
				actions,
			});
			continue;
		}

		if (owned.next != null) continue;
		const block = cfg.blocks.get(owned.copyRoot);
		if (!block) continue;
		const terminal = finalizerCopyTerminal(block);
		if (!terminal) continue;
		const phiAssignments = (descriptors.phis.phisByBlock.get(
			owned.copyRoot,
		) ?? []).flatMap((phi) => {
			const assignment = phi.incoming.get(owned.ownerBlock);
			return assignment ? [assignment] : [];
		});
		const actions: DeferredExit['actions'] = [{
			kind: 'finally',
			action: {
				canonical: owned.canonical,
				copyRoot: owned.copyRoot,
				ownerBlock: owned.ownerBlock,
				terminalOwnerBlock: owned.ownerBlock,
				next: null,
				kind: owned.kind === 'catch-copy'
					? 'catchTrailer'
					: 'abruptExitTrailer',
				statements: [],
			},
		}];
		if (phiAssignments.length > 0) {
			actions.push({ kind: 'phi', assignments: phiAssignments });
		}
		actions.push(terminal);
		exits.push({
			kind: terminal.kind === 'throw'
				? 'functionThrow'
				: 'functionReturn',
			edge: owned.edge,
			actions,
		});
	}
	return exits;
}

// The return/throw belongs at the protected edge that enters the copy. Putting
// it on the suppressed copy root leaves no emitted Region to own it.
function protectedFinalizerCopyOwner(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	copyRoot: number,
): number | null {
	const owners = [...cfg.normalPredecessors.get(copyRoot) ?? []].filter(
		(predecessor) => descriptor.protectedBlocks.has(predecessor),
	);
	return owners.length === 1 ? owners[0]! : null;
}

// Copied finalizers can contain branches or cleanup loops before their
// completion. Recover only a single terminal reached by every normal path;
// anything less precise remains on the conservative continuation path.
function reachableFinalizerCopyTerminal(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	copyRoot: number,
):
	| Extract<DeferredExit['actions'][number], {
		kind: 'return' | 'throw';
	}>
	| null {
	const reachable = new AddressSet<number>();
	const pending = [copyRoot];
	const terminals: CFGBlock[] = [];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (reachable.has(address)) continue;
		if (
			address !== copyRoot &&
			(descriptor.protectedBlocks.has(address) ||
				address === descriptor.handler)
		) return null;
		const block = cfg.blocks.get(address);
		if (!block) return null;
		reachable.add(address);
		const successors = [...cfg.normalSuccessors.get(address) ?? []];
		if (successors.length === 0) {
			if (
				block.terminator.kind !== 'return' &&
				block.terminator.kind !== 'throw'
			) return null;
			terminals.push(block);
			continue;
		}
		pending.push(...successors);
	}
	if (terminals.length !== 1) return null;
	const terminalAddress = terminals[0]!.address;
	const reachesTerminal = new AddressSet<number>([terminalAddress]);
	const reversePending = [terminalAddress];
	while (reversePending.length > 0) {
		const address = reversePending.pop()!;
		for (const predecessor of cfg.normalPredecessors.get(address) ?? []) {
			if (
				!reachable.has(predecessor) || reachesTerminal.has(predecessor)
			) {
				continue;
			}
			reachesTerminal.add(predecessor);
			reversePending.push(predecessor);
		}
	}
	if (!reachable.isSubsetOf(reachesTerminal)) return null;
	return finalizerCopyTerminal(terminals[0]!);
}

function finalizerCopyTerminal(
	block: CFGBlock,
):
	| Extract<DeferredExit['actions'][number], {
		kind: 'return' | 'throw';
	}>
	| null {
	if (block.terminator.kind === 'return') {
		return {
			kind: 'return',
			argument: terminalReturnArgument(
				block.body,
				block.terminator.argument,
			),
		};
	}
	if (block.terminator.kind === 'throw' && block.terminator.argument) {
		return {
			kind: 'throw',
			argument: t.cloneNode(block.terminator.argument, true),
		};
	}
	return null;
}

function splitAbruptFinalizerStatements(
	statements: t.Statement[],
): {
	statements: t.Statement[];
	terminal?: Extract<DeferredExit['actions'][number], {
		kind: 'return' | 'throw';
	}>;
} {
	const last = statements.at(-1);
	if (t.isReturnStatement(last)) {
		return {
			statements: statements.slice(0, -1),
			terminal: {
				kind: 'return',
				argument: last.argument == null
					? null
					: t.cloneNode(last.argument, true),
			},
		};
	}
	if (t.isThrowStatement(last)) {
		return {
			statements: statements.slice(0, -1),
			terminal: {
				kind: 'throw',
				argument: t.cloneNode(last.argument, true),
			},
		};
	}
	return { statements };
}

function copiedNormalFinalizerExitBlocks(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	handler: Region,
): AddressSet<number> {
	const normalCopyRoots = new AddressSet(
		descriptor.finallyCopies.filter((copy) =>
			copy.kind === 'normalExit' || copy.kind === 'catchTrailer'
		).map((copy) => copy.copyRoot),
	);
	const finalizerFingerprint = firstEffectiveStatementFingerprint(
		cfg,
		handler.sourceBlocks,
	);
	if (finalizerFingerprint == null) return new AddressSet();

	const copied = new AddressSet<number>();
	for (const block of descriptor.protectedBlocks) {
		for (const succ of cfg.normalSuccessors.get(block) ?? []) {
			if (descriptor.protectedBlocks.has(succ)) continue;
			if (handler.sourceBlocks.has(succ)) continue;
			if (copied.has(succ)) continue;
			if (!normalCopyRoots.has(succ)) continue;
			const succFingerprint = firstEffectiveStatementFingerprint(
				cfg,
				new AddressSet([succ]),
			);
			if (succFingerprint === finalizerFingerprint) copied.add(succ);
		}
	}
	return copied;
}

function firstEffectiveStatementFingerprint(
	cfg: ImmutableCFG,
	blocks: AddressSet<number>,
): string | null {
	for (const addr of [...blocks].toSorted((left, right) => left - right)) {
		const block = cfg.blocks.get(addr);
		if (!block) continue;
		for (const stmt of block.body) {
			if (isCatchIntrinsicDeclaration(stmt)) continue;
			if (t.isThrowStatement(stmt)) continue;
			return statementFingerprint(stmt);
		}
	}
	return null;
}

function isCatchIntrinsicDeclaration(stmt: t.Statement): boolean {
	if (!t.isVariableDeclaration(stmt)) return false;
	return stmt.declarations.some((decl) =>
		t.isCallExpression(decl.init) &&
		t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Catch' })
	);
}

function statementContainsIntrinsic(stmt: t.Statement, name: string): boolean {
	let found = false;
	t.traverseFast(stmt, (node) => {
		if (found) return t.traverseFast.skip;
		if (
			t.isCallExpression(node) &&
			t.isV8IntrinsicIdentifier(node.callee, { name })
		) {
			found = true;
		}
	});
	return found;
}

function catchOwnedByFinallyAt(
	entry: number,
	finallyDescriptor: ExceptionDescriptor,
	descriptors: CFGDescriptors,
): ExceptionDescriptor | null {
	const childHandlers = descriptors.exceptions.forest.nodeByHandler.get(
		finallyDescriptor.handler,
	)?.children.map((child) => child.descriptor.handler) ?? [];
	const candidates = descriptors.exceptions.handlers.filter((descriptor) =>
		descriptor.kind === 'catch' &&
		descriptor.protectedEntries.has(entry) &&
		childHandlers.includes(descriptor.handler)
	);
	return candidates.toSorted((left, right) =>
		left.protectedBlocks.size - right.protectedBlocks.size ||
		left.handler - right.handler
	)[0] ?? null;
}

const openableProtectedEntryCache = new WeakMap<
	ExceptionDescriptor,
	AddressSet<number>
>();

/**
 * The protected entries a Region may be opened at.
 *
 * Hermes splits a protected range around a nested handler, so that handler's
 * block is registered as an entry of the enclosing range too. It is reachable
 * only exceptionally, and composing the range from there covers nothing but
 * the handler itself — the nested descriptor owns it instead. A range whose
 * every entry is exception-only (protected code that begins at a handler)
 * keeps them all, so this only ever removes an alternative.
 */
export function openableProtectedEntries(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
): AddressSet<number> {
	const cached = openableProtectedEntryCache.get(descriptor);
	if (cached) return cached;
	const openable = new AddressSet<number>(
		[...descriptor.protectedEntries].filter((entry) => {
			const predecessors = cfg.normalPredecessors.get(entry);
			if (
				predecessors != null &&
				[...predecessors].some((predecessor) =>
					!descriptor.protectedBlocks.has(predecessor)
				)
			) return true;
			// The function's own entry block has no predecessors of either kind;
			// a handler block has exceptional ones.
			return (predecessors?.size ?? 0) === 0 &&
				(cfg.exceptionalPredecessors.get(entry)?.size ?? 0) === 0;
		}),
	);
	const entries = openable.size === 0
		? descriptor.protectedEntries
		: openable;
	openableProtectedEntryCache.set(descriptor, entries);
	return entries;
}

function exceptionStartingAt(
	cfg: ImmutableCFG,
	entry: number,
	descriptors: CFGDescriptors,
	allowed?: AddressSet<number>,
	preferOutermost = false,
): ExceptionDescriptor | null {
	const copyHandlers = descriptors.exceptions.finalizerCopyModel
		.copyDescriptorHandlers;
	let candidates = descriptors.exceptions.handlers.filter((descriptor) =>
		openableProtectedEntries(cfg, descriptor).has(entry) &&
		descriptorContainedBy(descriptor, allowed) &&
		// A per-exit-path finalizer copy must not open a region: the emitter
		// suppresses its statements, and opening one leaves a spurious `try {}`.
		!copyHandlers.has(descriptor.handler)
	);
	if (candidates.length === 0) return null;
	// Inside a bounded loop/body, prefer a handler that is itself part of that
	// scope. Iterator-close finalizers often protect one call in the loop but sit
	// outside it; choosing that outer finalizer here makes the loop Region overlap
	// the cleanup handler. The in-scope catch is the lexical body owner, while the
	// recovered iterator loop subsumes the close-only finalizer.
	if (allowed) {
		const inScope = candidates.filter((candidate) =>
			allowed.has(candidate.handler)
		);
		if (inScope.length > 0) candidates = inScope;
	}
	const catchCandidates = candidates.filter((candidate) =>
		candidate.kind === 'catch'
	);
	const owningFinally =
		candidates.filter((candidate) =>
			candidate.kind === 'finally' &&
			catchCandidates.some((catchCandidate) =>
				preferOutermost
					? isEnclosingFinalizerOwner(
						descriptors,
						candidate.handler,
						catchCandidate.handler,
					)
					: forestParentOf(descriptors, catchCandidate) === candidate
			)
		).toSorted((left, right) =>
			(preferOutermost
				? right.protectedBlocks.size - left.protectedBlocks.size
				: left.protectedBlocks.size - right.protectedBlocks.size) ||
			left.handler - right.handler
		)[0];
	if (owningFinally) return owningFinally;
	return candidates.toSorted((left, right) =>
		(preferOutermost
			? right.protectedBlocks.size - left.protectedBlocks.size
			: left.protectedBlocks.size - right.protectedBlocks.size) ||
		left.handler - right.handler
	)[0];
}

function forestParentOf(
	descriptors: CFGDescriptors,
	descriptor: ExceptionDescriptor,
): ExceptionDescriptor | null {
	const parent = descriptors.exceptions.forest.parentByHandler.get(
		descriptor.handler,
	);
	return parent == null
		? null
		: descriptors.exceptions.handlerByAddress.get(parent) ?? null;
}

function descriptorContainedBy(
	descriptor: ExceptionDescriptor,
	allowed?: AddressSet<number>,
): boolean {
	if (!allowed) return true;
	for (const block of descriptor.protectedBlocks) {
		if (!allowed.has(block)) return false;
	}
	return true;
}

function finallyPlausiblyOwnsCatch(
	finallyDescriptor: ExceptionDescriptor,
	catchDescriptor: ExceptionDescriptor,
): boolean {
	const finallySize = finallyDescriptor.protectedBlocks.size;
	const catchSize = catchDescriptor.protectedBlocks.size;
	if (finallySize <= catchSize + 4) return true;
	return catchSize > 8 && finallySize <= catchSize * 4;
}

function finallyHasStructuredNormalPath(
	descriptor: ExceptionDescriptor,
): boolean {
	return descriptor.finallyCopies.some((copy) =>
		copy.kind === 'normalExit' || copy.kind === 'catchTrailer'
	) ||
		descriptor.finallyCopySuffixes.some((suffix) =>
			suffix.kind === 'tryTrailer' || suffix.kind === 'catchTrailer'
		);
}

function finallyCanOwnCatch(descriptor: ExceptionDescriptor): boolean {
	return finallyHasStructuredNormalPath(descriptor) ||
		(descriptor.finallyBodyBlocks?.length ?? 0) > 0;
}

function cfgWithEntry(cfg: ImmutableCFG, entry: number): ImmutableCFG {
	if (cfg.entry === entry) return cfg;
	return Object.assign(Object.create(Object.getPrototypeOf(cfg)), cfg, {
		entry,
	}) as ImmutableCFG;
}
