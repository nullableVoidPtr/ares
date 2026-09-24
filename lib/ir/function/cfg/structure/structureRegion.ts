import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import * as t from '@babel/types';
import { invertTest } from '../../../ast/expression.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { IRFunction } from '../../mod.ts';
import {
	recordCFGCompatibilityAttempt,
	recordCFGCompatibilitySelection,
} from '../compatibility.ts';
import { CFGAnalyses, findWeakSESE } from '../algorithms/mod.ts';
import { StructuringDiagnostics } from '../diagnostics.ts';
import {
	type CFGDescriptors,
	iteratorCleanupRethrowRegister,
	recoverDescriptors,
} from '../descriptors/mod.ts';
import { ImmutableCFG } from '../immutableCFG.ts';
import {
	type CFGNormalizationSummary,
	normalizeCFGForRegions,
	validateRegionDescriptorInvariants,
	validateRegionFunctionMetadata,
} from '../normalization.ts';
import {
	cloneRegion,
	emptyRegion,
	ledgerSnapshot,
	loopRegionCoverageIssues,
	type LoopRegionExit,
	type Region,
	regionCoveredBlocks,
	regionDuplicateOwnership,
	regionStructuredBlocks,
	regionUnstructuredBranches,
	restoreLedger,
	visitRegions,
} from '../regions/region.ts';
import {
	contractedExceptionBlocks,
	openableProtectedEntries,
	tryStructureExceptionRegion,
} from './exceptionRegion.ts';
import {
	elidedIteratorCleanupHandlers,
	iteratorCleanupHandlersForLoop,
	recoverIteratorLoopSyntax,
	recoverSingleShotForInSyntax,
} from './iteratorLoop.ts';
import type { Terminator } from '../terminator.ts';
import {
	hasUnsupportedBoundedLoopArm,
	tryStructureIfRegion,
} from './ifRegion.ts';
import { tryStructureSharedAcyclicRegion } from './acyclicRegion.ts';
import { tryStructureLoopRegion } from './loopRegion.ts';
import {
	boundedScopeExit,
	type ContractibleExceptions,
	tryStructureBoundedContinuationForest,
	tryStructureBoundedLoopForest,
	tryStructureBoundedScopeForest,
} from './loopForest.ts';
import { structureStraightLineSequenceFrom } from './sequence.ts';
import {
	isClosedTerminalForest,
	tryStructureSwitchRegion,
} from './switchRegion.ts';

export interface StructuringOptions {
	strict?: boolean;
	/** Enable the Phase 1 graph-only canonical CFG boundary. */
	normalizeForRegions?: boolean;
	/** Check graph, Phi-edge, and handler-ownership invariants. */
	validateNormalization?: boolean;
}

export interface StructuringContext {
	func: IRFunction;
	cfg: ImmutableCFG;
	analyses: CFGAnalyses;
	descriptors: CFGDescriptors;
	diagnostics: StructuringDiagnostics;
	options: StructuringOptions;
}

export interface StructuringResult {
	ok: boolean;
	cfg: ImmutableCFG;
	analyses: CFGAnalyses;
	descriptors: CFGDescriptors;
	normalization: CFGNormalizationSummary;
	region?: Region;
	diagnostics: StructuringDiagnostics;
}

interface RegionMemoEntry {
	region: Region;
	structuredHandlersAdded: BlockAddr[];
}

const regionMemo = new WeakMap<
	CFGAnalyses,
	Map<string, RegionMemoEntry>
>();

/** Calls `structureRegionAt` has made for one function's analyses. */
const structureCallCounts = new WeakMap<CFGAnalyses, { calls: number }>();

/** Normal-plus-exceptional reachability from one entry, per function. */
const recursionClosures = new WeakMap<
	CFGAnalyses,
	AddressMap<AddressSet<BlockAddr>>
>();

/**
 * Call budget before region caching switches on, as a multiple of the block
 * count. A graph structured in one pass costs a bounded number of calls per
 * block; needing more means sub-regions are being re-derived.
 */
const MEMO_CALLS_PER_BLOCK = 4;
const MEMO_CALL_FLOOR = 64;

/**
 * Stable identity for a `structureRegionAt` restriction set.
 *
 * Cached per set object, because the same restriction is passed down many
 * branches and re-sorting it at every call would trade one cost for another.
 */
const restrictionKeys = new WeakMap<object, string>();

function restrictionKey(
	allowed: AddressSet<BlockAddr> | undefined,
): string {
	if (allowed == null) return '*';
	const cached = restrictionKeys.get(allowed);
	if (cached != null) return cached;
	const key = [...allowed].toSorted((left, right) => left - right).join(',');
	restrictionKeys.set(allowed, key);
	return key;
}

function addressSetKey(values: AddressSet<BlockAddr>): string {
	return [...values].toSorted((left, right) => left - right).join(',');
}
const MAX_SPECULATIVE_TERMINAL_LADDER_BLOCKS = 96;
const forInDispatchCache = new WeakMap<ImmutableCFG, boolean>();

export function structureCFG(
	func: IRFunction,
	options: StructuringOptions = {},
): StructuringResult {
	const inputCFG = ImmutableCFG.fromIRFunction(func);
	const normalized = normalizeCFGForRegions(inputCFG, {
		enabled: options.normalizeForRegions,
		validate: options.validateNormalization,
	});
	const cfg = normalized.cfg;
	const analyses = new CFGAnalyses(cfg);
	const descriptors = recoverDescriptors(cfg, func, analyses);
	// The loops are only known now, so the descriptors learn here which cleanup
	// landing pads a recovered `for...of` represents. No Region is opened for
	// one, and an edge into one is a lexical boundary of the loop that owns it.
	for (
		const handler of elidedIteratorCleanupHandlers(
			cfg,
			analyses,
			descriptors,
		)
	) descriptors.exceptions.elidedIteratorCleanupHandlers.add(handler);
	const diagnostics = cfg.diagnostics;
	if (
		options.normalizeForRegions && options.validateNormalization !== false
	) {
		normalized.summary.invariantIssues.push(
			...validateRegionDescriptorInvariants(cfg, descriptors),
			...validateRegionFunctionMetadata(cfg, func),
		);
		for (const issue of normalized.summary.invariantIssues) {
			diagnostics.add({
				kind: 'invalidNormalization',
				entry: issue.address ?? cfg.entry,
				message: issue.message,
			});
		}
	}
	const unreachable = new AddressSet(cfg.blocks.keys()).difference(
		analyses.reachability.allReachable,
	);
	for (const addr of unreachable) {
		if ((cfg.exceptionalPredecessors.get(addr)?.size ?? 0) > 0) continue;
		diagnostics.add({
			kind: 'unreachableBlock',
			entry: addr,
			message: `block 0x${addr.toString(16)} is unreachable`,
		});
	}
	for (const scc of analyses.reducibility.irreducibleSCCs) {
		diagnostics.add({
			kind: 'irreducibleSCC',
			entry: [...scc][0],
			relevantSCC: scc,
			message: 'normal-flow SCC has no dominating single entry',
		});
	}

	// Shared, monotonic ledger of exception-handler addresses already emitted as a
	// region. Threaded by reference (never cloned) through the whole structuring tree
	// so each exception descriptor is structured exactly once — a continuation block
	// that still carries a structured descriptor's protectedEntries must not re-open it.
	const structuredHandlers = new AddressSet<BlockAddr>();
	let region: Region | undefined;
	try {
		region = structureRegionAt(
			cfg.entry,
			cfg,
			analyses,
			descriptors,
			undefined,
			undefined,
			structuredHandlers,
		);
		if (
			region && regionNeedsExactContinuationForest(region, cfg, analyses)
		) {
			recordCFGCompatibilityAttempt(
				descriptors.compatibility,
				'whole-cfg-continuation-forest',
				cfg.entry,
				regionContainsKind(region, 'fallback')
					? 'primary Region contains a local fallback'
					: 'primary Region has incomplete exact ownership',
			);
			let exact: Region | null = null;
			try {
				exact = tryStructureWholeCFGContinuationForest(
					cfg,
					analyses,
					descriptors,
					region,
				);
			} catch (error) {
				// This is a speculative replacement. The primary Region remains
				// valid when recursive decomposition of the exact forest exhausts
				// the JavaScript stack; non-recursion failures still surface.
				if (
					!(error instanceof RangeError) ||
					!error.message.toLowerCase().includes('call stack')
				) throw error;
			}
			if (Deno.env.get('ARES_DEBUG_FOREST') === cfg.entry.toString(16)) {
				console.error(`whole CFG forest=${exact != null}`);
			}
			if (exact) {
				recordCFGCompatibilitySelection(
					descriptors.compatibility,
					'whole-cfg-continuation-forest',
					cfg.entry,
					'exact forest replaced the primary Region',
				);
				region = exact;
			}
		}
		if (region) {
			const continuationEntry = uniqueRegionExit(
				cfg,
				region.sourceBlocks,
			);
			const continuationTerminator = continuationEntry == null
				? null
				: cfg.blocks.get(continuationEntry)?.terminator.kind ?? null;
			if (
				continuationEntry != null &&
				continuationTerminator !== 'return' &&
				continuationTerminator !== 'throw' &&
				continuationTerminator !== 'unreachable' &&
				!region.sourceBlocks.has(continuationEntry) &&
				!regionReferencesTerminalEntry(region, continuationEntry)
			) {
				const continuation = structureRegionAt(
					continuationEntry,
					cfg,
					analyses,
					descriptors,
					undefined,
					new AddressSet([cfg.entry]),
					structuredHandlers,
				);
				if (
					continuation.sourceBlocks.size > 0 &&
					!continuation.sourceBlocks.isSubsetOf(region.sourceBlocks)
				) {
					region = {
						kind: 'sequence',
						regions: [region, continuation],
						sourceBlocks: new AddressSet([
							...region.sourceBlocks,
							...continuation.sourceBlocks,
						]),
					};
				}
			}
		}
		if (region) region = routeMultiDestinationLoopContinuations(region);
		if (region) region = labelPendingLoopSequenceExits(region);
		if (region) region = labelStrandedProtectedExits(region);
		if (region) region = rewriteBackEdgeLabelBreaks(region);
		if (region) {
			region = collapseEquivalentCatchCopies(
				region,
				cfg,
				descriptors.exceptions.equivalentCatchHandlerAliases,
			);
			suppressEquivalentCatchPhiAssignments(region, descriptors);
		}
		if (region && regionContainsKind(region, 'fallback')) {
			recordCFGCompatibilitySelection(
				descriptors.compatibility,
				'local-fallback-region',
				cfg.entry,
				'a local fallback survives in the final Region tree',
			);
		}
	} catch (error) {
		if (
			!(error instanceof RangeError) ||
			!error.message.toLowerCase().includes('call stack')
		) {
			throw error;
		}
		if (Deno.env.get('ARES_DEBUG_REGION') === '1') {
			console.error(error.stack ?? error.message);
		}
		diagnostics.add({
			kind: 'unstructuredRegion',
			entry: cfg.entry,
			message:
				'recursive CFG structuring exceeded the JavaScript call stack',
		});
	}

	return {
		ok: !options.strict || !diagnostics.hasErrors,
		cfg,
		analyses,
		descriptors,
		normalization: normalized.summary,
		region,
		diagnostics,
	};
}

/**
 * Fold compiler-split catch pads only after Region discovery is complete.
 *
 * Keeping the duplicate during discovery preserves its exceptional edge and
 * loop-exit ownership. Once the tree is fixed, the canonical parent catch can
 * own those blocks without emitting a nested source-level catch.
 */
function collapseEquivalentCatchCopies(
	region: Region,
	cfg: ImmutableCFG,
	aliases: ReadonlyMap<BlockAddr, BlockAddr>,
): Region {
	const rewrite = (candidate: Region): Region => {
		switch (candidate.kind) {
			case 'sequence':
				return {
					...candidate,
					regions: candidate.regions.map(rewrite),
				};
			case 'if':
				return {
					...candidate,
					consequent: rewrite(candidate.consequent),
					alternate: rewrite(candidate.alternate),
				};
			case 'switch':
				return {
					...candidate,
					cases: candidate.cases.map((switchCase) => ({
						...switchCase,
						body: rewrite(switchCase.body),
					})),
					defaultBody: rewrite(candidate.defaultBody),
				};
			case 'tryCatch': {
				const body = rewrite(candidate.body);
				const handler = rewrite(candidate.handler);
				const collapsed = collapseCatchCopiesOwnedBy(
					body,
					candidate.handlerAddress,
					cfg,
					aliases,
				);
				const subsumedHandlerBlocks = new AddressSet([
					...(candidate.subsumedHandlerBlocks ?? []),
					...collapsed.subsumedHandlerBlocks,
				]);
				return {
					...candidate,
					body: collapsed.region,
					handler,
					subsumedHandlerBlocks: subsumedHandlerBlocks.size === 0
						? undefined
						: subsumedHandlerBlocks,
				};
			}
			case 'tryFinally':
				return {
					...candidate,
					body: rewrite(candidate.body),
					finalizer: rewrite(candidate.finalizer),
				};
			case 'loop':
				return {
					...candidate,
					body: rewrite(candidate.body),
					exits: candidate.exits.map((exit) => ({
						...exit,
						trailer: exit.trailer == null
							? undefined
							: rewrite(exit.trailer),
					})),
				};
			default:
				return candidate;
		}
	};
	return rewrite(region);
}

function collapseCatchCopiesOwnedBy(
	region: Region,
	canonicalHandler: BlockAddr,
	cfg: ImmutableCFG,
	aliases: ReadonlyMap<BlockAddr, BlockAddr>,
): {
	region: Region;
	subsumedHandlerBlocks: AddressSet<BlockAddr>;
} {
	const subsumedHandlerBlocks = new AddressSet<BlockAddr>();
	const collapse = (candidate: Region): Region => {
		if (
			candidate.kind === 'tryCatch' &&
			aliases.get(candidate.handlerAddress) === canonicalHandler
		) {
			for (
				const block of candidate.sourceBlocks.difference(
					candidate.body.sourceBlocks,
				)
			) subsumedHandlerBlocks.add(block);
			subsumedHandlerBlocks.add(candidate.handlerAddress);
			addPrivateSubsumedCatchContinuations(
				cfg,
				subsumedHandlerBlocks,
				candidate.body.sourceBlocks,
			);
			return {
				kind: 'sequence',
				regions: [candidate.body],
				sourceBlocks: new AddressSet(candidate.sourceBlocks),
			};
		}
		switch (candidate.kind) {
			case 'sequence':
				return {
					...candidate,
					regions: candidate.regions.map(collapse),
				};
			case 'if':
				return {
					...candidate,
					consequent: collapse(candidate.consequent),
					alternate: collapse(candidate.alternate),
				};
			case 'switch':
				return {
					...candidate,
					cases: candidate.cases.map((switchCase) => ({
						...switchCase,
						body: collapse(switchCase.body),
					})),
					defaultBody: collapse(candidate.defaultBody),
				};
			case 'tryCatch':
				return {
					...candidate,
					body: collapse(candidate.body),
					handler: collapse(candidate.handler),
				};
			case 'tryFinally':
				return {
					...candidate,
					body: collapse(candidate.body),
					finalizer: collapse(candidate.finalizer),
				};
			case 'loop':
				return {
					...candidate,
					body: collapse(candidate.body),
					exits: candidate.exits.map((exit) => ({
						...exit,
						trailer: exit.trailer == null
							? undefined
							: collapse(exit.trailer),
					})),
				};
			default:
				return candidate;
		}
	};
	return { region: collapse(region), subsumedHandlerBlocks };
}

function addPrivateSubsumedCatchContinuations(
	cfg: ImmutableCFG,
	subsumed: AddressSet<BlockAddr>,
	bodyBlocks: AddressSet<BlockAddr>,
): void {
	for (let changed = true; changed;) {
		changed = false;
		for (const block of [...subsumed]) {
			for (const successor of cfg.normalSuccessors.get(block) ?? []) {
				if (subsumed.has(successor) || bodyBlocks.has(successor)) {
					continue;
				}
				const predecessors = cfg.normalPredecessors.get(successor) ??
					new AddressSet<BlockAddr>();
				if (
					predecessors.size === 0 ||
					!predecessors.isSubsetOf(subsumed)
				) continue;
				subsumed.add(successor);
				changed = true;
			}
		}
	}
}

function suppressEquivalentCatchPhiAssignments(
	region: Region,
	descriptors: CFGDescriptors,
) {
	const subsumed = new AddressSet<BlockAddr>();
	visitRegions(region, (candidate) => {
		if (candidate.kind !== 'tryCatch') return;
		for (const block of candidate.subsumedHandlerBlocks ?? []) {
			subsumed.add(block);
		}
	});
	if (subsumed.size === 0) return;
	for (const phi of descriptors.phis.phis) {
		for (const block of subsumed) {
			phi.incoming.delete(block);
			phi.exceptionalIncoming.delete(block);
		}
	}
	for (const [key, assignments] of descriptors.phis.phisByEdgeKey) {
		const retained = assignments.filter((assignment) =>
			!subsumed.has(assignment.edge.from)
		);
		if (retained.length === 0) {
			descriptors.phis.phisByEdgeKey.delete(key);
		} else if (retained.length !== assignments.length) {
			descriptors.phis.phisByEdgeKey.set(key, retained);
		}
	}
}
/**
 * The ordinary recursive builders intentionally prefer readable nested
 * Regions. A weak-SESE arm can nevertheless omit a shared continuation, or a
 * compatibility loop append can leave a conditional block represented only as
 * Basic. Detect those two objective failures before considering the bounded
 * exact continuation forest.
 */
function regionNeedsExactContinuationForest(
	region: Region,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
): boolean {
	const covered = regionCoveredBlocks(region);
	if (
		!analyses.reachability.normalReachable.isSubsetOf(covered) ||
		regionContainsKind(region, 'fallback')
	) return true;
	// Handler-only completion dispatchers are not normally reachable from the
	// function entry, so ordinary coverage cannot notice them. If a represented
	// landing pad flows to an uncovered normal successor, the exact exception
	// forest must own that shared cleanup/rethrow suffix as well.
	for (const handler of covered) {
		if ((cfg.exceptionalPredecessors.get(handler)?.size ?? 0) === 0) {
			continue;
		}
		for (const successor of cfg.normalSuccessors.get(handler) ?? []) {
			if (!covered.has(successor)) return true;
		}
	}

	const ownedControl = new AddressSet<BlockAddr>();
	const collectOwnedControl = (candidate: Region) => {
		switch (candidate.kind) {
			case 'if':
				for (
					const address of candidate.predicateBlocks ??
						[candidate.header]
				) ownedControl.add(address);
				collectOwnedControl(candidate.consequent);
				collectOwnedControl(candidate.alternate);
				break;
			case 'switch':
				for (const address of candidate.sourceBlocks) {
					const kind = cfg.blocks.get(address)?.terminator.kind;
					if (kind === 'if' || kind === 'switch') {
						ownedControl.add(address);
					}
				}
				candidate.cases.forEach((switchCase) =>
					collectOwnedControl(switchCase.body)
				);
				collectOwnedControl(candidate.defaultBody);
				break;
			case 'loop':
				ownedControl.add(candidate.header);
				candidate.latches.forEach((latch) => ownedControl.add(latch));
				candidate.exits.forEach((exit) => ownedControl.add(exit.from));
				collectOwnedControl(candidate.body);
				break;
			case 'sequence':
				candidate.regions.forEach(collectOwnedControl);
				break;
			case 'tryCatch':
				collectOwnedControl(candidate.body);
				collectOwnedControl(candidate.handler);
				break;
			case 'tryFinally':
				collectOwnedControl(candidate.body);
				collectOwnedControl(candidate.finalizer);
				break;
		}
	};
	collectOwnedControl(region);
	// A guard that enters an owned loop is represented by that Loop Region's
	// entry, exactly as the unstructured-branch summary counts it. Demanding the
	// forest for one would replace a complete region with a contracted skeleton.
	const loopHeaders = new AddressSet<BlockAddr>();
	const collectLoopHeaders = (candidate: Region) => {
		if (candidate.kind === 'loop') loopHeaders.add(candidate.header);
		for (const child of regionChildren(candidate)) {
			collectLoopHeaders(child);
		}
	};
	collectLoopHeaders(region);
	for (const address of analyses.reachability.normalReachable) {
		const terminator = cfg.blocks.get(address)?.terminator;
		if (terminator?.kind !== 'if' && terminator?.kind !== 'switch') {
			continue;
		}
		if (ownedControl.has(address)) continue;
		if (
			terminator.kind === 'if' &&
			(loopHeaders.has(terminator.fallthrough) ||
				loopHeaders.has(terminator.taken))
		) continue;
		return true;
	}
	return false;
}

function regionChildren(region: Region): Region[] {
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
			return [
				region.body,
				...region.exits.flatMap((exit) =>
					exit.trailer ? [exit.trailer] : []
				),
			];
		default:
			return [];
	}
}

/**
 * Own a residual acyclic scope through its control skeleton.
 *
 * The ordinary builders structure one recognized shape at a time; when none of
 * them claims a conditional they keep it as a Basic Region and stop, dropping
 * every block below it. Composing the same scope exactly gives every block one
 * owner: nested loops stay contracted, non-adjacent edges become labelled
 * sequence exits, and the single edge leaving the scope becomes a deferred exit
 * to the enclosing join.
 *
 * The scope must have exactly one non-terminal exit. More than one would need
 * the enclosing Region to resolve several deferred joins, which only the
 * specialized builders model today. A whole-function scope is left to the
 * dedicated continuation forest, which applies the same composition after the
 * ordinary candidate is judged incomplete.
 */
function tryStructureResidualScope(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	allowed: AddressSet<BlockAddr> | undefined,
	active: AddressSet<BlockAddr>,
	structuredHandlers: AddressSet<BlockAddr>,
): Region | null {
	if (allowed == null && entry === cfg.entry) return null;
	const scope = scopeReachableFrom(entry, cfg, allowed);
	// Iterator recovery owns the preheader that produces a property list. The
	// skeleton may contract the loop itself, but must not take over the block
	// that feeds it.
	for (const address of scope) {
		if (blockHasForInDispatch(cfg, address)) return null;
	}
	// A recovered comparison chain inside the scope is contracted like a loop, so
	// the skeleton keeps the recovered `switch` instead of the equality ladder it
	// came from. One elsewhere in the function is none of this scope's business.
	const compareChains = new AddressSet<BlockAddr>(
		[...scope].filter((address) =>
			descriptors.switches.switchByDispatch.get(address)?.kind ===
				'compareChain'
		),
	);
	const joins = new AddressSet<BlockAddr>();
	for (const address of scope) {
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (scope.has(successor) || isTerminalLeaf(successor, cfg)) {
				continue;
			}
			joins.add(successor);
		}
	}
	if (joins.size > 1) return null;
	const join = [...joins][0];
	const label = `cfg_scope_${formatAddress(entry)}`;
	let labelled = false;
	const region = tryStructureBoundedScopeForest(
		cfg,
		analyses,
		(loop) => {
			const candidate = structureLoopChildAt(
				loop.header,
				cfg,
				analyses,
				descriptors,
				scope,
				active,
				structuredHandlers,
			);
			return candidate?.kind === 'loop' && candidate.id === loop.id &&
					candidate.sourceBlocks.isSubsetOf(scope)
				? candidate
				: null;
		},
		{
			entry,
			allowed: scope,
			labelPrefix: `scope_${formatAddress(entry)}`,
			completion: (from, to) => {
				if (to === join) {
					labelled = true;
					return boundedScopeExit(from, to, label);
				}
				return isTerminalLeaf(to, cfg)
					? {
						kind: 'terminalReference',
						entry: to,
						edge: { from, to, kind: 'normal' },
						sourceBlocks: new AddressSet(),
					}
					: null;
			},
			exceptionBoundary: (from, to) => scope.has(from) && !scope.has(to),
		},
		compareChains.size === 0 ? undefined : {
			dispatches: compareChains,
			switchAt: (dispatch) =>
				tryStructureSwitchRegion(
					cfgWithEntry(cfg, dispatch),
					analyses,
					descriptors,
					(cursor, childAllowed) => {
						if (cursor === dispatch) return null;
						return structureRegionAt(
							cursor,
							cfg,
							analyses,
							descriptors,
							(childAllowed ?? scope).intersection(scope),
							active,
							structuredHandlers,
						);
					},
					{ dispatchBlock: dispatch },
				),
		},
		contractibleCatchRanges(cfg, analyses, descriptors) ?? undefined,
	);
	// A residual that leaves a branch unowned or claims a block twice is not an
	// improvement on the candidate it would replace.
	if (
		!region || regionUnstructuredBranches(region, cfg).size > 0 ||
		regionDuplicateOwnership(region, cfg).length > 0 ||
		!scope.isSubsetOf(regionStructuredBlocks(region))
	) return null;
	return labelled
		? {
			kind: 'sequence',
			regions: [region],
			exitLabel: label,
			sourceBlocks: new AddressSet(region.sourceBlocks),
		}
		: region;
}

/** A non-owning terminal leaf: a shared `return`, `throw`, or unreachable end. */
function isTerminalLeaf(address: BlockAddr, cfg: ImmutableCFG): boolean {
	const terminator = cfg.blocks.get(address)?.terminator;
	if (!terminator) return false;
	if (cfg.isScript && terminator.kind === 'return') return false;
	return terminator.kind === 'return' || terminator.kind === 'throw' ||
		terminator.kind === 'unreachable';
}

function blockHasForInDispatch(
	cfg: ImmutableCFG,
	address: BlockAddr,
): boolean {
	let found = false;
	for (const statement of cfg.blocks.get(address)?.body ?? []) {
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

function scopeReachableFrom(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	allowed: AddressSet<BlockAddr> | undefined,
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

/** Structure one contracted natural loop inside a composed scope. */
function structureLoopChildAt(
	header: BlockAddr,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	scope: AddressSet<BlockAddr>,
	active: AddressSet<BlockAddr>,
	structuredHandlers: AddressSet<BlockAddr>,
): Region | null {
	const nextActive = new AddressSet(active);
	nextActive.add(header);
	return tryStructureLoopRegion(
		cfgWithEntry(cfg, header),
		analyses,
		descriptors,
		(cursor, childAllowed) => {
			if (cursor === header) return null;
			return structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				(childAllowed ?? scope).intersection(scope),
				nextActive,
				structuredHandlers,
			);
		},
		{ allowHierarchicalExits: true, structuredHandlers },
	);
}

function formatAddress(address: BlockAddr): string {
	return address.toString(16);
}

/**
 * The protected ranges a control-forest composition may contract, or null when
 * the function has one it cannot.
 *
 * Contract only outer exception-forest roots. Their Region owns nested catches,
 * finalizers, and copies as one node; contracting children independently would
 * overlap that ownership. Multiple protected entries are aliases of the same
 * node and are accepted by the bounded forest's exact secondary-entry check.
 */
function contractibleCatchRanges(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	seededRegions = new AddressMap<Region>(),
): ContractibleExceptions | null | undefined {
	const handlers = descriptors.exceptions.handlers;
	// Undefined means there is nothing to contract, which is not a refusal: a
	// function without protected ranges composes exactly as it always did.
	if (handlers.length === 0) return undefined;
	let roots = descriptors.exceptions.forest.roots.map((node) =>
		node.descriptor
	);
	const rootHandlers = new AddressSet(
		roots.map((descriptor) => descriptor.handler),
	);
	for (const descriptor of handlers) {
		if (
			!descriptors.exceptions.forest.parentByHandler.has(
				descriptor.handler,
			) && !rootHandlers.has(descriptor.handler)
		) roots.push(descriptor);
	}
	roots = roots.filter((candidate) =>
		!roots.some((owner) =>
			owner !== candidate && owner.kind === 'finally' &&
			(owner.handler === candidate.canonicalFinallyAddress ||
				(owner.protectedBlocks.has(candidate.handler) &&
					candidate.protectedBlocks.isSubsetOf(
						owner.protectedBlocks,
					)))
		)
	);
	// One node per descriptor. A resume-split protected range has an entry per
	// bytecode range, but all of them alias the same try: composing each entry
	// separately would build overlapping nodes for the same handler. The
	// representative is the entry that dominates the others (the lexical start
	// of the try); the aliases stay in `entries` so the forest still recognises
	// them as secondary entries of the node that owns them, and they are
	// visited only after it.
	const rootByEntry = new AddressMap<
		CFGDescriptors['exceptions']['handlers'][number]
	>();
	const representatives = new AddressSet<BlockAddr>();
	const aliases = new AddressSet<BlockAddr>();
	for (const descriptor of roots) {
		const openable = [...openableProtectedEntries(cfg, descriptor)]
			.filter((entry) => !rootByEntry.has(entry));
		if (openable.length === 0) continue;
		const representative = openable.find((candidate) =>
			openable.every((other) =>
				other === candidate ||
				analyses.dominators.dominates(candidate, other)
			)
		) ?? openable.reduce((left, right) =>
			left < right ? left : right
		);
		for (const entry of openable) {
			rootByEntry.set(entry, descriptor);
			if (entry === representative) representatives.add(entry);
			else aliases.add(entry);
		}
	}
	const entries = new AddressSet<BlockAddr>([
		...representatives,
		...aliases,
	]);
	const protectedBlocks = new AddressSet<BlockAddr>(
		roots.flatMap((descriptor) => [...descriptor.protectedBlocks]),
	);
	if (entries.size === 0) return undefined;
	return {
		entries,
		protectedBlocks,
		exceptionAt: (protectedEntry) => {
			const descriptor = rootByEntry.get(protectedEntry);
			if (!descriptor) return null;
			// A contracted node owns its range and nothing past it, so the
			// composition is bounded even though an ordinary Region at the same
			// entry would continue into the code after the join.
			const bound = contractedExceptionBlocks(
				cfg,
				descriptor,
				descriptors,
			);
			const seeded = seededRegions.get(descriptor.handler);
			if (
				seeded &&
				seeded.sourceBlocks.isSubsetOf(bound) &&
				descriptor.protectedBlocks.isSubsetOf(
					regionCoveredBlocks(seeded),
				)
			) return cloneRegion(seeded);
			const candidate = tryStructureExceptionRegion(
				cfgWithEntry(cfg, protectedEntry),
				descriptors,
				(cursor, childAllowed) => {
					if (cursor === protectedEntry) return null;
					return structureRegionAt(
						cursor,
						cfg,
						analyses,
						descriptors,
						childAllowed == null
							? bound
							: childAllowed.intersection(bound),
						new AddressSet<BlockAddr>([protectedEntry]),
						new AddressSet<BlockAddr>(),
					);
				},
				bound,
				new AddressSet<BlockAddr>(),
				analyses,
				{ exactScope: true },
			);
			return candidate?.sourceBlocks.isSubsetOf(bound) &&
					candidate.sourceBlocks.has(descriptor.handler) &&
					descriptor.protectedBlocks.isSubsetOf(
						regionCoveredBlocks(candidate),
					)
				? candidate
				: null;
		},
	};
}

/**
 * A comparison chain is recovered from ordinary equality branches, so the
 * generic skeleton would silently emit that ladder again instead of the
 * recovered `switch`.
 */
function hasRecoveredCompareChainSwitch(descriptors: CFGDescriptors): boolean {
	return descriptors.switches.switches.some((descriptor) =>
		descriptor.kind !== 'terminator'
	);
}

function tryStructureWholeCFGContinuationForest(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	primary: Region,
): Region | null {
	const seededLoops = new AddressMap<
		Extract<Region, { kind: 'loop' }>
	>();
	const seededExceptions = new AddressMap<Region>();
	visitRegions(primary, (candidate) => {
		if (candidate.kind === 'loop') {
			seededLoops.set(candidate.header, candidate);
		} else if (
			candidate.kind === 'tryCatch' || candidate.kind === 'tryFinally'
		) {
			seededExceptions.set(candidate.handlerAddress, candidate);
		}
	});
	// Protected exception-forest roots are contracted like loops so their
	// exceptional edges become internal to one skeleton node.
	const contractibleExceptions = contractibleCatchRanges(
		cfg,
		analyses,
		descriptors,
		seededExceptions,
	);
	if (contractibleExceptions === null) return null;
	// A recovered comparison chain is contracted like a loop, exactly as the
	// scope forest already does, so the skeleton keeps the recovered `switch`
	// rather than degrading into the equality ladder it came from. Declining
	// outright instead left every function containing one to post-reduction.
	const compareChains = new AddressSet<BlockAddr>(
		[...cfg.blocks.keys()].filter((address) =>
			descriptors.switches.switchByDispatch.get(address)?.kind ===
				'compareChain'
		),
	);
	return tryStructureBoundedContinuationForest(
		cfg,
		analyses,
		(loop) => {
			const seeded = seededLoops.get(loop.header);
			if (
				seeded &&
				loop.body.isSubsetOf(seeded.sourceBlocks) &&
				loop.body.difference(
					seeded.suppressedBodyBlocks ?? new AddressSet<BlockAddr>(),
				).isSubsetOf(regionCoveredBlocks(seeded)) &&
				loopRegionCoverageIssues(seeded).length === 0
			) return seeded;
			const active = new AddressSet<BlockAddr>([loop.header]);
			const candidate = tryStructureLoopRegion(
				cfgWithEntry(cfg, loop.header),
				analyses,
				descriptors,
				(cursor, allowed) => {
					if (cursor === loop.header) return null;
					return structureRegionAt(
						cursor,
						cfg,
						analyses,
						descriptors,
						allowed,
						active,
						new AddressSet<BlockAddr>(),
					);
				},
				{ allowHierarchicalExits: true },
			);
			return candidate?.kind === 'loop' ? candidate : null;
		},
		contractibleExceptions,
		compareChains.size === 0 ? undefined : {
			dispatches: compareChains,
			switchAt: (dispatch) =>
				tryStructureSwitchRegion(
					cfgWithEntry(cfg, dispatch),
					analyses,
					descriptors,
					(cursor, childAllowed) => {
						if (cursor === dispatch) return null;
						return structureRegionAt(
							cursor,
							cfg,
							analyses,
							descriptors,
							childAllowed,
							new AddressSet<BlockAddr>([dispatch]),
							new AddressSet<BlockAddr>(),
						);
					},
					{ dispatchBlock: dispatch },
				),
		},
	);
}

export function structureRegionAt(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	allowed?: AddressSet<BlockAddr>,
	active = new AddressSet<BlockAddr>(),
	structuredHandlers = new AddressSet<BlockAddr>(),
): Region {
	return structureRegionAtInner(
		entry,
		cfg,
		analyses,
		descriptors,
		allowed,
		active,
		structuredHandlers,
	);
}

/**
 * Blocks a call at `entry` can recurse into: its normal successors plus the
 * handlers reached from them by an exceptional edge.
 *
 * `active` is the chain of entries currently being structured, and it reaches
 * the result only through the ancestor-repeat bail in
 * `structureRegionAtUncached`. A member outside this closure can never be the
 * entry of a descendant call, so it cannot change what this call returns and
 * must not split its cache key -- which is what makes the cache effective on a
 * graph whose sub-regions are reached along many different paths.
 */
function recursionClosure(
	analyses: CFGAnalyses,
	entry: BlockAddr,
): AddressSet<BlockAddr> {
	const byEntry = recursionClosures.get(analyses) ??
		new AddressMap<AddressSet<BlockAddr>>();
	recursionClosures.set(analyses, byEntry);
	const cached = byEntry.get(entry);
	if (cached) return cached;
	const cfg = analyses.cfg;
	const closure = new AddressSet<BlockAddr>();
	const pending = [entry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (closure.has(address) || !cfg.blocks.has(address)) continue;
		closure.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
		for (const successor of cfg.exceptionalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
	}
	byEntry.set(entry, closure);
	return closure;
}

function structureRegionAtInner(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	allowed?: AddressSet<BlockAddr>,
	active = new AddressSet<BlockAddr>(),
	structuredHandlers = new AddressSet<BlockAddr>(),
): Region {
	// Restricted calls are memoised as well as unrestricted ones, keyed by the
	// restriction, the reachable part of the recursion chain and the current
	// exception-handler ledger. Without that, `structureRegionAt` is
	// exponential: it re-derives the same sub-region once per path that reaches
	// it. Function #115926 of the 127k-function bundle (66 blocks) made 1.82
	// million calls at a bounded depth of 52 and never finished; function #6682
	// (261 blocks, 10 catch descriptors) made 600k calls in 99s across only
	// ~1,300 distinct sub-problems, deadlocking a whole parallel lift batch.
	//
	// Handler ownership is a side-effect as well as an input, so cache entries
	// replay the handlers they added for the exact starting ledger encoded in
	// the key. Caching is not free -- every hit and miss clones a Region -- so
	// it switches on only once a function has made more calls than the size of
	// its graph justifies, leaving the many small functions that finish in one
	// pass to run without any bookkeeping.
	const counter = structureCallCounts.get(analyses) ?? { calls: 0 };
	if (counter.calls === 0) structureCallCounts.set(analyses, counter);
	counter.calls++;
	const memoable = counter.calls >
		MEMO_CALLS_PER_BLOCK * cfg.blocks.size + MEMO_CALL_FLOOR;
	const memo = memoable
		? regionMemo.get(analyses) ?? new Map<string, RegionMemoEntry>()
		: undefined;
	if (memo && !regionMemo.has(analyses)) {
		regionMemo.set(analyses, memo);
	}
	const memoKey = memo
		? `${entry}|${restrictionKey(allowed)}|${
			addressSetKey(
				active.size === 0
					? active
					: active.intersection(recursionClosure(analyses, entry)),
			)
		}|${addressSetKey(structuredHandlers)}`
		: '';
	const cached = memo?.get(memoKey);
	if (cached) {
		for (const handler of cached.structuredHandlersAdded) {
			structuredHandlers.add(handler);
		}
		return cloneRegion(cached.region);
	}
	const handlersBefore = memo
		? new AddressSet(structuredHandlers)
		: undefined;
	const region = structureRegionAtUncached(
		entry,
		cfg,
		analyses,
		descriptors,
		allowed,
		active,
		structuredHandlers,
	);
	if (memo) {
		memo.set(memoKey, {
			region: cloneRegion(region),
			structuredHandlersAdded: [...structuredHandlers].filter((handler) =>
				!handlersBefore!.has(handler)
			),
		});
	}
	return region;
}

function structureRegionAtUncached(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	allowed: AddressSet<BlockAddr> | undefined,
	active: AddressSet<BlockAddr>,
	structuredHandlers: AddressSet<BlockAddr>,
): Region {
	if (allowed && !allowed.has(entry)) {
		const terminal = cfg.blocks.get(entry)?.terminator;
		if (
			!cfg.hasExceptionRegions &&
			((terminal?.kind === 'return' && !cfg.isScript) ||
				terminal?.kind === 'throw' ||
				terminal?.kind === 'unreachable')
		) {
			return {
				kind: 'terminalReference',
				entry,
				sourceBlocks: new AddressSet(),
			};
		}
		return {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		};
	}
	if (active.has(entry) || active.size > cfg.blocks.size) {
		recordCFGCompatibilityAttempt(
			descriptors.compatibility,
			'local-fallback-region',
			entry,
			'recursive structuring cycle',
		);
		return {
			kind: 'fallback',
			entry,
			sourceBlocks: new AddressSet([entry]),
			reason: 'recursive structuring cycle',
		};
	}
	const nextActive = new AddressSet(active);
	nextActive.add(entry);
	const scopedCFG = entry === cfg.entry ? cfg : cfgWithEntry(cfg, entry);
	// A delegate `yield*` loop can sit inside a user try/catch/finally whose protected
	// range starts at the same block (the delegate prelude). Structure the exception
	// region first so it wraps the delegate; the recursion then recognizes the delegate
	// inside the try body (the structured-handler ledger prevents the try re-firing).
	const exceptionRegion = tryStructureExceptionRegion(
		scopedCFG,
		descriptors,
		(cursor, childAllowed) => {
			if (cursor === entry) {
				// Re-forming this exception region would recurse, but the entry block can
				// itself be a delegate-yield prelude wrapped by the try — recognize that.
				return tryStructureDelegateYieldRegion(cursor, descriptors);
			}
			return structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				nextActive,
				structuredHandlers,
			);
		},
		allowed,
		structuredHandlers,
		analyses,
		{ exactScope: allowed != null },
	);
	if (exceptionRegion) return exceptionRegion;
	const delegateYieldRegion = tryStructureDelegateYieldRegion(
		entry,
		descriptors,
	);
	if (delegateYieldRegion) return delegateYieldRegion;
	const owningLoop = analyses.naturalLoops.loopByHeader.get(entry);
	const ownedIteratorCleanupHandlers = owningLoop == null
		? new AddressSet<BlockAddr>()
		: iteratorCleanupHandlersForLoop(
			owningLoop,
			cfg,
			descriptors,
		);
	const structureLoopChild = (
		cursor: BlockAddr,
		childAllowed?: AddressSet<BlockAddr>,
		ownerClosed?: boolean,
	): Region | null => {
		if (cursor === entry) return null;
		// Protected and recovered for-in loops need their specialized descriptor to
		// remain the owning recursive boundary. A bounded arm whose complete
		// normal/exceptional closure has no outside predecessor may recurse without
		// taking ownership from that descriptor.
		if (
			((exceptionSplitsProtectedRange(
				cursor,
				descriptors,
				ownedIteratorCleanupHandlers,
			) && !ownerClosed) || hasForInDispatchAt(cfg, cursor)) &&
			!analyses.naturalLoops.loopByHeader.has(cursor) &&
			!descriptors.switches.switchByDispatch.has(cursor) &&
			!exceptionStartsAt(cursor, descriptors)
		) return null;
		if (
			childAllowed &&
			exceptionStartsAt(cursor, descriptors) &&
			!exceptionProtectedBlocksContainedBy(
				cursor,
				descriptors,
				childAllowed,
			)
		) {
			return null;
		}
		return structureRegionAt(
			cursor,
			cfg,
			analyses,
			descriptors,
			childAllowed ?? allowed,
			nextActive,
			structuredHandlers,
		);
	};
	const loopRegion = tryStructureLoopRegion(
		scopedCFG,
		analyses,
		descriptors,
		structureLoopChild,
		{
			allowHierarchicalExits: true,
			structuredHandlers,
		},
	);
	if (loopRegion?.kind === 'loop') {
		const continuationEntry = loopContinuationEntry(
			loopRegion,
			cfg,
			undefined,
		);
		if (allowed == null && continuationEntry != null) {
			const continuation = structureRegionAt(
				continuationEntry,
				cfg,
				analyses,
				descriptors,
				allowed,
				nextActive,
				structuredHandlers,
			);
			if (
				continuation.sourceBlocks.size > 0 &&
				!continuation.sourceBlocks.isSubsetOf(loopRegion.sourceBlocks)
			) {
				return {
					kind: 'sequence',
					regions: [loopRegion, continuation],
					sourceBlocks: new AddressSet([
						...loopRegion.sourceBlocks,
						...continuation.sourceBlocks,
					]),
				};
			}
		}
		const mixedAbruptSwitch = tryStructureMixedAbruptLoopSwitch(
			loopRegion,
			() =>
				tryStructureLoopRegion(
					scopedCFG,
					analyses,
					descriptors,
					structureLoopChild,
					{
						allowMixedAbruptExits: true,
						structuredHandlers,
					},
				),
			cfg,
			descriptors,
			(cursor, childAllowed) =>
				structureRegionAt(
					cursor,
					cfg,
					analyses,
					descriptors,
					childAllowed ?? allowed,
					nextActive,
					structuredHandlers,
				),
			allowed,
		);
		if (mixedAbruptSwitch) return mixedAbruptSwitch;
		return loopRegion;
	}
	// A property iteration with no backedge is not in the loop forest at all,
	// so it has to be recognized before the generic branch builders claim its
	// dispatch as an ordinary conditional over the raw intrinsics.
	const singleShotForIn = tryStructureSingleShotForInRegion(
		scopedCFG,
		analyses,
		descriptors,
		(cursor, childAllowed) =>
			structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				nextActive,
				structuredHandlers,
			),
		allowed,
	);
	if (singleShotForIn) return singleShotForIn;
	// Iterator/for-in recovery owns its preheader, header Phis, and environment
	// bindings as one descriptor. Keep that specialized path ahead of generic
	// whole-function loop-forest composition.
	const loopForest = hasForInDispatch(cfg) ||
			hasRecoveredCompareChainSwitch(descriptors)
		? null
		: tryStructureBoundedLoopForest(
			scopedCFG,
			analyses,
			(loop) => {
				if (
					descriptors.exceptions.finalizerCopyModel.copyBlocks.has(
						loop.header,
					)
				) return null;
				const candidate = tryStructureLoopRegion(
					cfgWithEntry(cfg, loop.header),
					analyses,
					descriptors,
					structureLoopChild,
					{
						allowHierarchicalExits: true,
						structuredHandlers,
					},
				);
				return candidate?.kind === 'loop' ? candidate : null;
			},
			allowed,
		);
	if (loopForest && !regionUnstructuredBranches(loopForest, cfg).has(entry)) {
		return loopForest;
	}
	const switchRegion = tryStructureSwitchRegion(
		scopedCFG,
		analyses,
		descriptors,
		(cursor, childAllowed) => {
			if (cursor === entry) return null;
			return structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				nextActive,
				structuredHandlers,
			);
		},
	);
	if (switchRegion) {
		if (
			switchRegion.join != null &&
			(!allowed || allowed.has(switchRegion.join))
		) {
			const continuation = structureRegionAt(
				switchRegion.join,
				cfg,
				analyses,
				descriptors,
				allowed,
				nextActive,
				structuredHandlers,
			);
			if (
				continuation.sourceBlocks.size > 0 &&
				!continuation.sourceBlocks.isSubsetOf(switchRegion.sourceBlocks)
			) {
				return {
					kind: 'sequence',
					regions: [switchRegion, continuation],
					sourceBlocks: new AddressSet([
						...switchRegion.sourceBlocks,
						...continuation.sourceBlocks,
					]),
				};
			}
		}
		return switchRegion;
	}
	const optionalLoopRegion = tryStructureOptionalLoopRegion(
		scopedCFG,
		analyses,
		(cursor, childAllowed) =>
			structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				nextActive,
				structuredHandlers,
			),
		allowed,
		structuredHandlers,
	);
	if (optionalLoopRegion?.kind === 'if' && optionalLoopRegion.join != null) {
		const continuation = structureRegionAt(
			optionalLoopRegion.join,
			cfg,
			analyses,
			descriptors,
			allowed,
			allowed == null ? undefined : nextActive,
			structuredHandlers,
		);
		if (
			continuation.sourceBlocks.size > 0 &&
			!continuation.sourceBlocks.isSubsetOf(
				optionalLoopRegion.sourceBlocks,
			)
		) {
			return {
				kind: 'sequence',
				regions: [optionalLoopRegion, continuation],
				sourceBlocks: new AddressSet([
					...optionalLoopRegion.sourceBlocks,
					...continuation.sourceBlocks,
				]),
			};
		}
		return optionalLoopRegion;
	}
	const loopGuardRegion = tryStructureLoopGuardRegion(
		scopedCFG,
		analyses,
		descriptors,
		allowed,
	);
	const deferLoopEntryGuard = shouldDeferLoopEntryGuard(
		scopedCFG,
		analyses,
	);
	if (loopGuardRegion?.kind === 'if' && loopGuardRegion.join != null) {
		const continuation = structureRegionAt(
			loopGuardRegion.join,
			cfg,
			analyses,
			descriptors,
			allowed,
			allowed == null ? undefined : nextActive,
			structuredHandlers,
		);
		if (
			continuation.sourceBlocks.size > 0 &&
			!continuation.sourceBlocks.isSubsetOf(loopGuardRegion.sourceBlocks)
		) {
			return {
				kind: 'sequence',
				regions: [loopGuardRegion, continuation],
				sourceBlocks: new AddressSet([
					...loopGuardRegion.sourceBlocks,
					...continuation.sourceBlocks,
				]),
			};
		}
		return loopGuardRegion;
	}
	const sharedAlternateGuard = tryStructureSharedAlternateGuardRegion(
		scopedCFG,
		analyses,
		(cursor, childAllowed) =>
			structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				nextActive,
				structuredHandlers,
			),
		allowed,
	);
	if (sharedAlternateGuard) {
		const continuation = structureRegionAt(
			sharedAlternateGuard.continuation,
			cfg,
			analyses,
			descriptors,
			allowed,
			allowed == null ? undefined : nextActive,
			structuredHandlers,
		);
		if (
			continuation.sourceBlocks.size > 0 &&
			!continuation.sourceBlocks.isSubsetOf(
				sharedAlternateGuard.region.sourceBlocks,
			)
		) {
			return {
				kind: 'sequence',
				regions: [sharedAlternateGuard.region, continuation],
				sourceBlocks: new AddressSet([
					...sharedAlternateGuard.region.sourceBlocks,
					...continuation.sourceBlocks,
				]),
			};
		}
		return sharedAlternateGuard.region;
	}
	const ifRegion = deferLoopEntryGuard ? null : tryStructureIfRegion(
		scopedCFG,
		analyses,
		(cursor, childAllowed, ownerClosed) => {
			if (cursor === entry) return null;
			// A generic arm cannot split a protected range: it could move a
			// finalizer Phi onto a different enclosing If. A bounded arm whose
			// complete normal/exceptional closure has no outside predecessor is
			// safe to recurse; its enclosing descriptor retains the handler.
			if (
				exceptionSplitsProtectedRange(cursor, descriptors) &&
				!ownerClosed
			) return null;
			if (
				childAllowed &&
				exceptionStartsAt(cursor, descriptors) &&
				!exceptionProtectedBlocksContainedBy(
					cursor,
					descriptors,
					childAllowed,
				)
			) return null;
			return structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				nextActive,
				structuredHandlers,
			);
		},
		allowed,
		undefined,
		structuredHandlers,
		descriptors.compatibility,
	);
	const sharedAcyclic = tryStructureSharedAcyclicRegion(
		scopedCFG,
		analyses,
		new AddressSet(
			[
				...descriptors.switches.switches.map((descriptor) =>
					descriptor.dispatchBlock
				),
				...descriptors.exceptions.handlers.flatMap((descriptor) =>
					structuredHandlers.has(descriptor.handler)
						? []
						: [...descriptor.protectedEntries]
				),
			],
		),
		allowed,
	);
	// Weak-SESE arms contain only nodes dominated by their respective entries.
	// When both arms flow through a shared non-terminal node before the real join,
	// an otherwise valid-looking If Region can therefore omit that node entirely.
	// Prefer the exact-SESE DAG only in that proven incomplete-coverage case.
	const ifRegionIsComplete = ifRegion?.kind !== 'if' ||
		sharedAcyclic == null ||
		sharedAcyclic.region.sourceBlocks.isSubsetOf(
			regionCoveredBlocks(ifRegion),
		);
	if (
		ifRegion?.kind === 'if' && ifRegionIsComplete && ifRegion.join != null
	) {
		const continuation = structureRegionAt(
			ifRegion.join,
			cfg,
			analyses,
			descriptors,
			allowed,
			allowed == null ? undefined : nextActive,
			structuredHandlers,
		);
		if (
			continuation.sourceBlocks.size > 0 &&
			!continuation.sourceBlocks.isSubsetOf(ifRegion.sourceBlocks)
		) {
			return closeSingleDeferredJoin({
				kind: 'sequence',
				regions: [ifRegion, continuation],
				sourceBlocks: new AddressSet([
					...ifRegion.sourceBlocks,
					...continuation.sourceBlocks,
				]),
			});
		}
		return ifRegion;
	}
	if (ifRegion && ifRegionIsComplete) return ifRegion;
	if (sharedAcyclic) {
		if (!allowed || allowed.has(sharedAcyclic.join)) {
			const continuation = structureRegionAt(
				sharedAcyclic.join,
				cfg,
				analyses,
				descriptors,
				allowed,
				allowed == null ? undefined : nextActive,
				structuredHandlers,
			);
			if (
				continuation.sourceBlocks.size > 0 &&
				!continuation.sourceBlocks.isSubsetOf(
					sharedAcyclic.region.sourceBlocks,
				)
			) {
				return {
					kind: 'sequence',
					regions: [sharedAcyclic.region, continuation],
					sourceBlocks: new AddressSet([
						...sharedAcyclic.region.sourceBlocks,
						...continuation.sourceBlocks,
					]),
				};
			}
		}
		return sharedAcyclic.region;
	}
	const sharedSwitchContinuation = tryStructureSharedSwitchContinuation(
		entry,
		cfg,
		analyses,
		descriptors,
		(cursor, childAllowed) =>
			structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				nextActive,
				structuredHandlers,
			),
		allowed,
	);
	if (sharedSwitchContinuation) return sharedSwitchContinuation;
	const guardedTerminalSwitch = tryStructureGuardedTerminalSwitch(
		entry,
		cfg,
		descriptors,
		(cursor, childAllowed) =>
			structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				nextActive,
				structuredHandlers,
			),
		allowed,
	);
	if (guardedTerminalSwitch) {
		const continuation = structureRegionAt(
			guardedTerminalSwitch.continuation,
			cfg,
			analyses,
			descriptors,
			allowed,
			allowed == null ? undefined : nextActive,
			structuredHandlers,
		);
		if (
			continuation.sourceBlocks.size > 0 &&
			!continuation.sourceBlocks.isSubsetOf(
				guardedTerminalSwitch.region.sourceBlocks,
			)
		) {
			return {
				kind: 'sequence',
				regions: [guardedTerminalSwitch.region, continuation],
				sourceBlocks: new AddressSet([
					...guardedTerminalSwitch.region.sourceBlocks,
					...continuation.sourceBlocks,
				]),
			};
		}
		return guardedTerminalSwitch.region;
	}
	const terminalIf = deferLoopEntryGuard
		? null
		: tryStructureTerminalIfLadder(
			entry,
			cfg,
			analyses,
			descriptors,
			allowed,
			nextActive,
			structuredHandlers,
		);
	if (terminalIf) return terminalIf;
	if (loopForest) return loopForest;
	const straightLine = structureStraightLineSequenceFrom(
		scopedCFG,
		entry,
		allowed,
		(cursor, childAllowed) => {
			if (cursor === entry) return null;
			return structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				nextActive,
				structuredHandlers,
			);
		},
		(cursor, childAllowed) => {
			const ledgerBefore = ledgerSnapshot(structuredHandlers);
			const candidate = structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				nextActive,
				structuredHandlers,
			);
			if (
				candidate.kind === 'tryCatch' &&
				candidate.retryLoop?.header === cursor
			) return candidate;
			restoreLedger(structuredHandlers, ledgerBefore);
			return null;
		},
	) ?? {
		kind: 'sequence' as const,
		regions: [],
		sourceBlocks: new AddressSet<BlockAddr>(),
	};
	if (straightLine.kind !== 'sequence' || straightLine.regions.length > 0) {
		recordCFGCompatibilityAttempt(
			descriptors.compatibility,
			'single-top-level-loop',
			entry,
			'primary sequence may leave a top-level loop unowned',
		);
		const composed = appendSingleTopLevelLoop(
			straightLine,
			entry,
			cfg,
			analyses,
			descriptors,
			allowed,
			nextActive,
			structuredHandlers,
		);
		if (composed !== straightLine) {
			recordCFGCompatibilitySelection(
				descriptors.compatibility,
				'single-top-level-loop',
				entry,
				'compatibility composer appended a top-level loop',
			);
		}
		if (regionUnstructuredBranches(composed, cfg).size === 0) {
			return composed;
		}
		return tryStructureResidualScope(
			entry,
			cfg,
			analyses,
			descriptors,
			allowed,
			nextActive,
			structuredHandlers,
		) ?? composed;
	}
	recordCFGCompatibilityAttempt(
		descriptors.compatibility,
		'local-fallback-region',
		cfg.entry,
		'recursive structuring emission is not enabled yet',
	);
	return {
		kind: 'fallback',
		entry: cfg.entry,
		sourceBlocks: new AddressSet(analyses.reachability.normalReachable),
		reason: 'recursive structuring emission is not enabled yet',
	};
}

/**
 * Own a closed Switch Region once when both sides of a conditional either
 * terminate or reach its dispatch. A normal postdominator does not exist when
 * one path returns/throws before the dispatch, which otherwise makes the
 * terminal-ladder builder duplicate or omit the shared switch suffix.
 */
function tryStructureSharedSwitchContinuation(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt: (entry: BlockAddr, allowed?: AddressSet<BlockAddr>) => Region,
	allowed?: AddressSet<BlockAddr>,
): Region | null {
	if (cfg.hasExceptionRegions || analyses.naturalLoops.loops.length > 0) {
		return null;
	}
	const block = cfg.blocks.get(entry);
	if (!block || block.terminator.kind !== 'if') return null;
	const terminator = block.terminator;
	const fallthroughDistances = normalDistancesFrom(
		terminator.fallthrough,
		cfg,
		allowed,
	);
	const takenDistances = normalDistancesFrom(
		terminator.taken,
		cfg,
		allowed,
	);
	const candidates = descriptors.switches.switches.flatMap((descriptor) => {
		if (
			descriptor.dispatchBlock === entry ||
			(allowed && !allowed.has(descriptor.dispatchBlock))
		) return [];
		const fallthroughDistance = fallthroughDistances.get(
			descriptor.dispatchBlock,
		);
		if (fallthroughDistance == null) return [];
		const takenDistance = takenDistances.get(descriptor.dispatchBlock);
		return takenDistance == null ? [] : [{
			descriptor,
			distance: fallthroughDistance + takenDistance,
		}];
	}).toSorted((left, right) =>
		left.distance - right.distance ||
		left.descriptor.dispatchBlock - right.descriptor.dispatchBlock
	);
	for (const { descriptor } of candidates) {
		const join = descriptor.dispatchBlock;
		const arm = (armEntry: BlockAddr): Region | null => {
			if (armEntry === join) {
				return {
					kind: 'sequence',
					regions: [],
					sourceBlocks: new AddressSet(),
				};
			}
			const sese = findWeakSESE(armEntry, join, {
				cfg,
				dominators: analyses.dominators,
				postdominators: analyses.postdominators,
			});
			if (
				!sese || sese.deferredExits.length > 0 ||
				(allowed && !sese.body.isSubsetOf(allowed))
			) return null;
			const region = regionAt(armEntry, sese.body);
			const covered = regionCoveredBlocks(region);
			if (
				region.kind === 'fallback' ||
				!region.sourceBlocks.isSubsetOf(sese.body) ||
				!sese.body.isSubsetOf(covered)
			) return null;
			return region;
		};
		const consequent = arm(terminator.taken);
		const alternate = arm(terminator.fallthrough);
		if (!consequent || !alternate) continue;
		if (regionsOverlap(consequent.sourceBlocks, alternate.sourceBlocks)) {
			continue;
		}
		const switchRegion = regionAt(join, allowed);
		if (
			!regionContainsKind(switchRegion, 'switch') ||
			switchRegion.kind === 'fallback' ||
			!isClosedTerminalForest(switchRegion, cfg) ||
			regionsOverlap(
				switchRegion.sourceBlocks,
				consequent.sourceBlocks,
			) ||
			regionsOverlap(switchRegion.sourceBlocks, alternate.sourceBlocks)
		) continue;
		const conditional: Region = {
			kind: 'if',
			header: entry,
			test: t.cloneNode(terminator.test, true),
			consequent,
			alternate,
			join,
			conditionalValue: {
				kind: 'conditionalPhi',
				branch: entry,
				consequentEntry: terminator.taken,
				alternateEntry: terminator.fallthrough,
				join,
				forms: ['shortcut', 'ternary'],
			},
			sourceBlocks: new AddressSet([
				entry,
				...consequent.sourceBlocks,
				...alternate.sourceBlocks,
			]),
		};
		return {
			kind: 'sequence',
			regions: [conditional, switchRegion],
			sourceBlocks: new AddressSet([
				...conditional.sourceBlocks,
				...switchRegion.sourceBlocks,
			]),
		};
	}
	return null;
}

/**
 * Retain a terminal switch arm hanging from a guard while the other guard edge
 * rejoins the outer branch's shared continuation:
 *
 *     entry -> guard -> terminal switch
 *        |       `----> continuation
 *        `------------> continuation
 *
 * The continuation is emitted once after the two conditionals. This is the
 * Region-native counterpart of cloning a shared continuation onto the guard
 * edge before reducing the two branches.
 */
function tryStructureGuardedTerminalSwitch(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	regionAt: (entry: BlockAddr, allowed?: AddressSet<BlockAddr>) => Region,
	allowed?: AddressSet<BlockAddr>,
): { region: Region; continuation: BlockAddr } | null {
	if (cfg.hasExceptionRegions) return null;
	const outerBlock = cfg.blocks.get(entry);
	if (!outerBlock || outerBlock.terminator.kind !== 'if') return null;
	for (
		const [guardEntry, continuation] of [
			[
				outerBlock.terminator.fallthrough,
				outerBlock.terminator.taken,
			],
			[
				outerBlock.terminator.taken,
				outerBlock.terminator.fallthrough,
			],
		] as const
	) {
		if (
			(allowed &&
				(!allowed.has(guardEntry) || !allowed.has(continuation))) ||
			(cfg.normalPredecessors.get(guardEntry)?.size ?? 0) !== 1 ||
			!cfg.normalPredecessors.get(guardEntry)?.has(entry)
		) continue;
		const guard = cfg.blocks.get(guardEntry);
		if (!guard || guard.terminator.kind !== 'if') continue;
		const fallthroughContinues =
			guard.terminator.fallthrough === continuation;
		const takenContinues = guard.terminator.taken === continuation;
		if (fallthroughContinues === takenContinues) continue;
		const terminalEntry = fallthroughContinues
			? guard.terminator.taken
			: guard.terminator.fallthrough;
		if (allowed && !allowed.has(terminalEntry)) continue;
		const continuationPredecessors = cfg.normalPredecessors.get(
			continuation,
		) ?? new AddressSet<BlockAddr>();
		if (
			[...continuationPredecessors].some((predecessor) =>
				predecessor !== entry && predecessor !== guardEntry
			)
		) continue;
		const terminal = regionAt(terminalEntry, allowed);
		if (
			terminal.kind === 'fallback' ||
			!regionContainsKind(terminal, 'switch') ||
			!isClosedTerminalForest(terminal, cfg) ||
			terminal.sourceBlocks.has(entry) ||
			terminal.sourceBlocks.has(guardEntry) ||
			terminal.sourceBlocks.has(continuation)
		) continue;
		const empty = (): Region => ({
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		});
		const guardTakenIsTerminal = guard.terminator.taken === terminalEntry;
		const guardRegion: Region = {
			kind: 'if',
			header: guardEntry,
			test: t.cloneNode(guard.terminator.test, true),
			consequent: guardTakenIsTerminal ? terminal : empty(),
			alternate: guardTakenIsTerminal ? empty() : terminal,
			join: continuation,
			sourceBlocks: new AddressSet([
				guardEntry,
				...terminal.sourceBlocks,
			]),
		};
		const outerTakesGuard = outerBlock.terminator.taken === guardEntry;
		return {
			region: {
				kind: 'if',
				header: entry,
				test: t.cloneNode(outerBlock.terminator.test, true),
				consequent: outerTakesGuard ? guardRegion : empty(),
				alternate: outerTakesGuard ? empty() : guardRegion,
				join: continuation,
				sourceBlocks: new AddressSet([
					entry,
					...guardRegion.sourceBlocks,
				]),
			},
			continuation,
		};
	}
	return null;
}

/**
 * A mixed loop exit is kept as an ordinary break until an enclosing suffix can
 * prove where normal control continues. When exactly one non-terminal exit is
 * a recovered switch, retry abrupt-exit classification and accept it only when
 * that switch owns a closed terminal forest. This makes the switch the unique
 * post-loop continuation while direct return/throw exits remain in the loop.
 */
function tryStructureMixedAbruptLoopSwitch(
	loop: Extract<Region, { kind: 'loop' }>,
	retry: () => Region | null,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	regionAt: (entry: BlockAddr, allowed?: AddressSet<BlockAddr>) => Region,
	allowed?: AddressSet<BlockAddr>,
): Region | null {
	if (cfg.hasExceptionRegions || loop.continuation != null) return null;
	const breakTargets = new AddressSet<BlockAddr>();
	for (const exit of loop.exits) {
		if (exit.kind !== 'break' && exit.kind !== 'labelledBreak') continue;
		breakTargets.add(normalizeLoopExitTarget(cfg, exit.to));
	}
	const switchTargets = new AddressSet(
		[...breakTargets].filter((target) =>
			descriptors.switches.switchByDispatch.has(target)
		),
	);
	if (switchTargets.size !== 1) return null;
	const [switchTarget] = switchTargets;
	if (allowed && !allowed.has(switchTarget)) return null;
	let hasAbruptExit = false;
	for (const target of breakTargets) {
		if (target === switchTarget) continue;
		if (!isShareableTerminal(target, cfg)) return null;
		hasAbruptExit = true;
	}
	if (!hasAbruptExit) return null;

	const retried = retry();
	if (
		!retried || retried.kind !== 'loop' ||
		retried.continuation !== switchTarget
	) return null;
	const switchRegion = regionAt(switchTarget, allowed);
	if (
		switchRegion.kind === 'fallback' ||
		!regionContainsKind(switchRegion, 'switch') ||
		!isClosedTerminalForest(switchRegion, cfg) ||
		regionsOverlap(retried.sourceBlocks, switchRegion.sourceBlocks)
	) return null;
	return {
		kind: 'sequence',
		regions: [retried, switchRegion],
		sourceBlocks: new AddressSet([
			...retried.sourceBlocks,
			...switchRegion.sourceBlocks,
		]),
	};
}

function normalDistancesFrom(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	allowed?: AddressSet<BlockAddr>,
): Map<BlockAddr, number> {
	const distances = new Map<BlockAddr, number>([[entry, 0]]);
	const pending = [entry];
	while (pending.length > 0) {
		const address = pending.shift()!;
		const distance = distances.get(address)!;
		if (allowed && !allowed.has(address)) continue;
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (distances.has(successor)) continue;
			distances.set(successor, distance + 1);
			pending.push(successor);
		}
	}
	return distances;
}

/**
 * Structure a preheader that conditionally enters a natural loop and otherwise
 * skips directly to the loop's single continuation. Keeping the loop as the
 * non-empty if arm preserves loop ownership and makes the continuation an
 * ordinary Region join.
 */
function tryStructureOptionalLoopRegion(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	regionAt: (entry: BlockAddr, allowed?: AddressSet<BlockAddr>) => Region,
	allowed?: AddressSet<BlockAddr>,
	ledger?: AddressSet<BlockAddr>,
): Region | null {
	const ledgerBefore = ledger ? ledgerSnapshot(ledger) : null;
	const reject = () => {
		if (ledger && ledgerBefore) restoreLedger(ledger, ledgerBefore);
		return null;
	};
	const block = cfg.blocks.get(cfg.entry);
	if (!block || block.terminator.kind !== 'if') return null;
	const fallthroughArm = optionalLoopArmFrom(
		block.terminator.fallthrough,
		cfg,
		analyses,
		allowed,
	);
	const takenArm = optionalLoopArmFrom(
		block.terminator.taken,
		cfg,
		analyses,
		allowed,
	);
	if (!fallthroughArm && !takenArm) {
		const fallthroughGuard = guardedOptionalLoopArm(
			block.terminator.fallthrough,
			block.terminator.taken,
			cfg,
			analyses,
			regionAt,
			allowed,
			ledger,
		);
		const takenGuard = guardedOptionalLoopArm(
			block.terminator.taken,
			block.terminator.fallthrough,
			cfg,
			analyses,
			regionAt,
			allowed,
			ledger,
		);
		if (!!fallthroughGuard === !!takenGuard) return reject();
		const guardedArm = fallthroughGuard ?? takenGuard!;
		const empty: Region = {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		};
		return {
			kind: 'if',
			header: cfg.entry,
			test: t.cloneNode(block.terminator.test, true),
			consequent: takenGuard ? guardedArm.region : empty,
			alternate: fallthroughGuard ? guardedArm.region : empty,
			join: guardedArm.continuation,
			conditionalValue: {
				kind: 'conditionalPhi',
				branch: cfg.entry,
				consequentEntry: block.terminator.taken,
				alternateEntry: block.terminator.fallthrough,
				join: guardedArm.continuation,
				forms: ['shortcut', 'ternary'],
			},
			sourceBlocks: new AddressSet([
				cfg.entry,
				...guardedArm.region.sourceBlocks,
			]),
		};
	}
	if (!!fallthroughArm === !!takenArm) return null;
	const arm = fallthroughArm ?? takenArm;
	const loop = arm?.loop;
	if (!loop) return null;
	if (loop.parent != null) {
		const parent = analyses.naturalLoops.loops[loop.parent];
		// A bounded caller may be structuring an optional child loop inside its
		// natural parent. Admit that child only when the allowed set cuts the parent
		// boundary; otherwise the ordinary top-level ownership rule still applies.
		if (!allowed || parent?.body.isSubsetOf(allowed)) return null;
	}
	const continuation = fallthroughArm
		? block.terminator.taken
		: block.terminator.fallthrough;
	if (
		allowed &&
		(!loop.body.isSubsetOf(allowed) ||
			!arm.prelude.every((address) => allowed.has(address)))
	) return null;

	// Keep recursive discovery bounded to the natural-loop core. The loop builder
	// may explicitly add proven exit trailers to its ownership, but giving the
	// callback the whole enclosing arm lets it append the continuation and no
	// longer return a Loop Region here.
	const loopRegion = regionAt(loop.header, loop.body);
	if (
		loopRegion.kind !== 'loop' ||
		(allowed && !loopRegion.sourceBlocks.isSubsetOf(allowed)) ||
		!loop.body.isSubsetOf(regionCoveredBlocks(loopRegion))
	) return reject();
	let loopArm: Region = loopRegion;
	if (loopRegion.continuation !== continuation) {
		if (loopRegion.continuation == null) return reject();
		const suffixSESE = findWeakSESE(
			loopRegion.continuation,
			continuation,
			{
				cfg,
				dominators: analyses.dominators,
				postdominators: analyses.postdominators,
			},
		);
		if (
			!suffixSESE || suffixSESE.deferredExits.length > 0 ||
			(allowed && !suffixSESE.body.isSubsetOf(allowed))
		) return reject();
		const suffix = regionAt(suffixSESE.entry, suffixSESE.body);
		if (
			suffix.kind === 'fallback' ||
			!suffix.sourceBlocks.isSubsetOf(suffixSESE.body) ||
			!suffixSESE.body.isSubsetOf(regionCoveredBlocks(suffix))
		) return reject();
		loopArm = {
			kind: 'sequence',
			regions: [loopRegion, suffix],
			sourceBlocks: new AddressSet([
				...loopRegion.sourceBlocks,
				...suffix.sourceBlocks,
			]),
		};
	}
	if (arm.prelude.length > 0) {
		const preludeRegions: Region[] = arm.prelude.map((address) => ({
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([address]),
		}));
		loopArm = {
			kind: 'sequence',
			regions: [...preludeRegions, loopArm],
			sourceBlocks: new AddressSet([
				...arm.prelude,
				...loopArm.sourceBlocks,
			]),
		};
	}
	const empty: Region = {
		kind: 'sequence',
		regions: [],
		sourceBlocks: new AddressSet(),
	};
	const loopOnTest = arm.entry === block.terminator.taken;
	return {
		kind: 'if',
		header: cfg.entry,
		test: t.cloneNode(block.terminator.test, true),
		consequent: loopOnTest ? loopArm : empty,
		alternate: loopOnTest ? empty : loopArm,
		join: continuation,
		conditionalValue: {
			kind: 'conditionalPhi',
			branch: cfg.entry,
			consequentEntry: block.terminator.taken,
			alternateEntry: block.terminator.fallthrough,
			join: continuation,
			forms: ['shortcut', 'ternary'],
		},
		sourceBlocks: new AddressSet([cfg.entry, ...loopArm.sourceBlocks]),
	};
}

/**
 * A property iteration whose body always leaves it: `for (const k in o) return k`.
 *
 * Hermes emits the ordinary `%GetPNameList`/`%GetNextPName` protocol, but the
 * body never branches back, so the graph carries no backedge and the loop is
 * absent from the natural-loop forest. Left to the generic builders the
 * dispatch survives as an if-chain over the raw intrinsics.
 *
 * The recovered Region is a Loop Region with no latch. Every path through the
 * body returns, throws, or leaves for the continuation, and a leaving path is
 * exactly a `break`: without a backedge the loop cannot take a second
 * iteration, which is what the source said.
 */
function tryStructureSingleShotForInRegion(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt: (entry: BlockAddr, allowed?: AddressSet<BlockAddr>) => Region,
	allowed?: AddressSet<BlockAddr>,
): Region | null {
	const entry = cfg.entry;
	const header = cfg.blocks.get(entry);
	if (!header || header.terminator.kind !== 'if') return null;
	if (analyses.naturalLoops.loopByHeader.has(entry)) return null;
	if (cfg.exceptionalSuccessors.get(entry)?.size) return null;
	const arms = undefinedComparisonArms(header.terminator);
	if (!arms) return null;
	const { continuation, bodyEntry } = arms;
	if (
		bodyEntry === entry || continuation === entry ||
		(allowed && !allowed.has(bodyEntry))
	) return null;
	const body = singleShotForInBodyBlocks(
		entry,
		bodyEntry,
		continuation,
		cfg,
		allowed,
	);
	if (!body) return null;
	const loopBlocks = new AddressSet<BlockAddr>([entry, ...body.blocks]);
	const syntax = recoverSingleShotForInSyntax(entry, loopBlocks, cfg);
	if (
		!syntax || syntax.value.name !== arms.name ||
		!singleShotForInHeaderIsProtocol(header.body, syntax.value.name)
	) return null;
	// A shared trailing `break` cannot carry a Phi copy that belongs to one
	// leaving edge, so leave those shapes to the ordinary builders.
	if (
		body.breakSources.size > 0 &&
		(descriptors.phis.phisByBlock.get(continuation) ?? []).some((phi) =>
			[...phi.incoming.values()].some((assignment) =>
				body.blocks.has(assignment.edge.from)
			)
		)
	) return null;
	const bodyRegion = regionAt(bodyEntry, body.blocks);
	if (
		bodyRegion.kind === 'fallback' ||
		!bodyRegion.sourceBlocks.isSubsetOf(body.blocks) ||
		!body.blocks.isSubsetOf(regionCoveredBlocks(bodyRegion)) ||
		regionUnstructuredBranches(bodyRegion, cfg).size >
			body.breakSources.size
	) return null;
	const exits: LoopRegionExit[] = [
		{ from: entry, to: continuation, kind: 'break' },
		...[...body.breakSources].map((from) => ({
			from,
			to: continuation,
			kind: 'break' as const,
		})),
	];
	return {
		kind: 'loop',
		// Outside the natural-loop forest, so outside its id range as well.
		id: analyses.naturalLoops.loops.length + entry,
		header: entry,
		latches: [],
		loopBlocks,
		continuation,
		exits,
		children: [],
		syntax,
		body: body.breakSources.size === 0 ? bodyRegion : {
			kind: 'sequence',
			regions: [bodyRegion, {
				kind: 'break',
				target: continuation,
				exit: exits[1]!,
				sourceBlocks: new AddressSet<BlockAddr>(),
			}],
			sourceBlocks: new AddressSet(bodyRegion.sourceBlocks),
		},
		sourceBlocks: loopBlocks,
	};
}

interface SingleShotForInArms {
	/** The register `%GetNextPName` assigns the next property name to. */
	name: string;
	continuation: BlockAddr;
	bodyEntry: BlockAddr;
}

/**
 * The two arms of an `x === undefined` branch, named by which one the equality
 * selects. `%GetNextPName` reports exhaustion with `undefined`, so the equal
 * arm is the code after the loop.
 */
function undefinedComparisonArms(
	terminator: Extract<Terminator, { kind: 'if' }>,
): SingleShotForInArms | null {
	const test = terminator.test;
	if (!t.isBinaryExpression(test)) return null;
	const operand = t.isIdentifier(test.right, { name: 'undefined' })
		? test.left
		: t.isIdentifier(test.left, { name: 'undefined' })
		? test.right
		: null;
	if (!t.isIdentifier(operand)) return null;
	if (test.operator === '===') {
		return {
			name: operand.name,
			continuation: terminator.taken,
			bodyEntry: terminator.fallthrough,
		};
	}
	if (test.operator === '!==') {
		return {
			name: operand.name,
			continuation: terminator.fallthrough,
			bodyEntry: terminator.taken,
		};
	}
	return null;
}

/**
 * The body of a single-shot `for...in`: everything the key-bearing arm reaches
 * before the loop's continuation. The body must be entered only from the header
 * and may leave only for that continuation; anything else means the dispatch is
 * shared with code this Region would not own.
 */
function singleShotForInBodyBlocks(
	header: BlockAddr,
	bodyEntry: BlockAddr,
	continuation: BlockAddr,
	cfg: ImmutableCFG,
	allowed?: AddressSet<BlockAddr>,
):
	| { blocks: AddressSet<BlockAddr>; breakSources: AddressSet<BlockAddr> }
	| null {
	const blocks = new AddressSet<BlockAddr>();
	const pending = [bodyEntry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (address === continuation || blocks.has(address)) continue;
		// Reaching the header again is a backedge: an ordinary loop, not this.
		if (address === header) return null;
		if (!cfg.blocks.has(address)) return null;
		if (allowed && !allowed.has(address)) return null;
		if (cfg.exceptionalSuccessors.get(address)?.size) return null;
		blocks.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
	}
	if (blocks.size === 0) return null;
	const breakSources = new AddressSet<BlockAddr>();
	for (const address of blocks) {
		for (const predecessor of cfg.normalPredecessors.get(address) ?? []) {
			if (predecessor !== header && !blocks.has(predecessor)) return null;
		}
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (blocks.has(successor)) continue;
			if (successor !== continuation) return null;
			breakSources.add(address);
		}
	}
	return { blocks, breakSources };
}

/**
 * The loop emitter represents the header with the recovered syntax and emits no
 * statement for it, so the header may hold nothing but the protocol: the
 * `%GetNextPName` declaration, header Phis, and register aliases.
 */
function singleShotForInHeaderIsProtocol(
	statements: readonly t.Statement[],
	key: string,
): boolean {
	return statements.every((statement) => {
		if (!t.isVariableDeclaration(statement)) return false;
		return statement.declarations.every((declaration) => {
			if (t.isIdentifier(declaration.init)) return true;
			if (!t.isCallExpression(declaration.init)) return false;
			if (
				t.isV8IntrinsicIdentifier(declaration.init.callee, {
					name: 'Phi',
				})
			) return true;
			return t.isV8IntrinsicIdentifier(declaration.init.callee, {
				name: 'GetNextPName',
			}) &&
				t.isArrayPattern(declaration.id) &&
				t.isIdentifier(declaration.id.elements[0], { name: key });
		});
	});
}

interface OptionalLoopArm {
	entry: BlockAddr;
	loop: CFGAnalyses['naturalLoops']['loops'][number];
	prelude: BlockAddr[];
}

function optionalLoopArmFrom(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	allowed?: AddressSet<BlockAddr>,
): OptionalLoopArm | null {
	const prelude: BlockAddr[] = [];
	const seen = new AddressSet<BlockAddr>();
	let cursor = entry;
	while (!seen.has(cursor) && (!allowed || allowed.has(cursor))) {
		const loop = analyses.naturalLoops.loopByHeader.get(cursor);
		if (loop) return { entry, loop, prelude };
		seen.add(cursor);
		const block = cfg.blocks.get(cursor);
		if (!block || block.terminator.kind !== 'goto') return null;
		prelude.push(cursor);
		cursor = block.terminator.target;
	}
	return null;
}

function guardedOptionalLoopArm(
	entry: BlockAddr,
	continuation: BlockAddr,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	regionAt: (entry: BlockAddr, allowed?: AddressSet<BlockAddr>) => Region,
	allowed?: AddressSet<BlockAddr>,
	ledger?: AddressSet<BlockAddr>,
): { region: Region; continuation: BlockAddr } | null {
	if (allowed && !allowed.has(entry)) return null;
	const guard = cfg.blocks.get(entry);
	if (!guard || guard.terminator.kind !== 'if') return null;
	const fallthroughContinues = guard.terminator.fallthrough === continuation;
	const takenContinues = guard.terminator.taken === continuation;
	if (fallthroughContinues === takenContinues) return null;
	const loopEntry = fallthroughContinues
		? guard.terminator.taken
		: guard.terminator.fallthrough;
	const arm = optionalLoopArmFrom(
		loopEntry,
		cfg,
		analyses,
		allowed,
	);
	if (!arm || arm.loop.parent != null) return null;
	const armAllowed = new AddressSet<BlockAddr>([
		entry,
		...arm.prelude,
		...arm.loop.body,
	]);
	if (allowed && !armAllowed.isSubsetOf(allowed)) return null;
	const ledgerBefore = ledger ? ledgerSnapshot(ledger) : null;
	const region = regionAt(entry, armAllowed);
	const covered = regionCoveredBlocks(region);
	if (
		region.kind === 'fallback' ||
		!region.sourceBlocks.isSubsetOf(armAllowed) ||
		!armAllowed.isSubsetOf(covered)
	) {
		if (ledger && ledgerBefore) restoreLedger(ledger, ledgerBefore);
		return null;
	}
	return { region, continuation };
}

/**
 * Close a nested weak-SESE side exit around the shared suffix that it skips.
 * Phase 2 deliberately handles one enclosing continuation at a time; multiple
 * distinct targets require a proper region hierarchy instead of nested labels
 * chosen heuristically.
 */
function closeSingleDeferredJoin(
	region: Extract<Region, { kind: 'sequence' }>,
): Region {
	const covered = regionCoveredBlocks(region);
	const targets = new AddressSet<BlockAddr>();
	visitRegion(region, (candidate) => {
		if (
			candidate.kind === 'deferredExit' &&
			candidate.exit.kind === 'toJoin' &&
			!covered.has(candidate.exit.target)
		) targets.add(candidate.exit.target);
		if (candidate.kind === 'loop') {
			for (const exit of candidate.exits) {
				if (
					exit.sequenceExit &&
					!covered.has(exit.sequenceExit.target)
				) targets.add(exit.sequenceExit.target);
			}
		}
	});
	if (targets.size !== 1) return region;
	const [target] = targets;
	const label = `cfg_exit_${target.toString(16)}`;
	const reopened = reopenDeferredJoinScope(region, label);
	const rewritten = rewriteDeferredJoinAsBreak(reopened, target, label);
	if (rewritten.kind !== 'sequence') return region;
	return {
		...rewritten,
		exitLabel: label,
	};
}

function reopenDeferredJoinScope(
	region: Region,
	label: string,
): Region {
	if (
		region.kind === 'labelBreak' && region.label === label && !region.exit
	) {
		return {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		};
	}
	switch (region.kind) {
		case 'sequence':
			return {
				...region,
				exitLabel: region.exitLabel === label
					? undefined
					: region.exitLabel,
				regions: region.regions.map((child) =>
					reopenDeferredJoinScope(child, label)
				),
			};
		case 'if':
			return {
				...region,
				consequent: reopenDeferredJoinScope(region.consequent, label),
				alternate: reopenDeferredJoinScope(region.alternate, label),
			};
		case 'switch':
			return {
				...region,
				cases: region.cases.map((switchCase) => ({
					...switchCase,
					body: reopenDeferredJoinScope(switchCase.body, label),
				})),
				defaultBody: reopenDeferredJoinScope(region.defaultBody, label),
			};
		case 'tryCatch':
			return {
				...region,
				body: reopenDeferredJoinScope(region.body, label),
				handler: reopenDeferredJoinScope(region.handler, label),
			};
		case 'tryFinally':
			return {
				...region,
				body: reopenDeferredJoinScope(region.body, label),
				finalizer: reopenDeferredJoinScope(region.finalizer, label),
			};
		case 'loop':
			return {
				...region,
				body: reopenDeferredJoinScope(region.body, label),
			};
		default:
			return region;
	}
}

function rewriteDeferredJoinAsBreak(
	region: Region,
	target: BlockAddr,
	label: string,
): Region {
	if (
		region.kind === 'deferredExit' &&
		region.exit.kind === 'toJoin' &&
		region.exit.target === target
	) {
		return {
			kind: 'sequence',
			regions: [
				region,
				{
					kind: 'labelBreak',
					label,
					target,
					sourceBlocks: new AddressSet(),
				},
			],
			sourceBlocks: new AddressSet(),
		};
	}
	switch (region.kind) {
		case 'sequence':
			return {
				...region,
				regions: region.regions.map((child) =>
					rewriteDeferredJoinAsBreak(child, target, label)
				),
			};
		case 'if':
			return {
				...region,
				consequent: rewriteDeferredJoinAsBreak(
					region.consequent,
					target,
					label,
				),
				alternate: rewriteDeferredJoinAsBreak(
					region.alternate,
					target,
					label,
				),
			};
		case 'loop': {
			const exits = region.exits.map((exit) =>
				exit.to === target || exit.sequenceExit?.target === target
					? { ...exit, sequenceExit: { target } }
					: exit
			);
			return activateLoopSequenceExit(
				{ ...region, exits },
				target,
				label,
			);
		}
		default:
			return region;
	}
}

function visitRegion(region: Region, visit: (region: Region) => void) {
	visit(region);
	switch (region.kind) {
		case 'sequence':
			region.regions.forEach((child) => visitRegion(child, visit));
			break;
		case 'if':
			visitRegion(region.consequent, visit);
			visitRegion(region.alternate, visit);
			break;
		case 'switch':
			region.cases.forEach((switchCase) =>
				visitRegion(switchCase.body, visit)
			);
			visitRegion(region.defaultBody, visit);
			break;
		case 'tryCatch':
			visitRegion(region.body, visit);
			visitRegion(region.handler, visit);
			break;
		case 'tryFinally':
			visitRegion(region.body, visit);
			visitRegion(region.finalizer, visit);
			break;
		case 'loop':
			visitRegion(region.body, visit);
			break;
	}
}

function tryStructureDelegateYieldRegion(
	entry: BlockAddr,
	descriptors: CFGDescriptors,
): Region | null {
	const descriptor =
		descriptors.delegateYields.delegateByPrelude.get(entry) ??
			descriptors.delegateYields.delegateByHeader.get(entry);
	if (!descriptor) return null;
	return {
		kind: 'delegateYield',
		argument: t.cloneNode(descriptor.argument, true),
		preludeStatements: descriptor.preludeStatements?.map((stmt) =>
			t.cloneNode(stmt, true)
		),
		completion: descriptor.completion,
		completionTarget: descriptor.completionTarget
			? t.cloneNode(descriptor.completionTarget, true)
			: undefined,
		trailing: descriptor.trailing?.map((stmt) => t.cloneNode(stmt, true)),
		completionSkip: descriptor.completionSkip == null
			? undefined
			: { ...descriptor.completionSkip },
		declaresCompletionTarget: descriptor.declaresCompletionTarget,
		sourceBlocks: new AddressSet(descriptor.sourceBlocks),
		preludeSkip: descriptor.preludeSkip == null ? undefined : {
			block: descriptor.preludeSkip.block,
			statements: [...descriptor.preludeSkip.statements],
		},
	};
}

function tryStructureLoopGuardRegion(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	allowed?: AddressSet<BlockAddr>,
): Region | null {
	const block = cfg.blocks.get(cfg.entry);
	if (!block || block.terminator.kind !== 'if') return null;

	const fallthrough = block.terminator.fallthrough;
	const taken = block.terminator.taken;
	const fallthroughLoop = analyses.naturalLoops.loopByHeader.get(fallthrough);
	const takenLoop = analyses.naturalLoops.loopByHeader.get(taken);
	if (!!fallthroughLoop === !!takenLoop) return null;

	const loopHeader = fallthroughLoop ? fallthrough : taken;
	const guardTarget = fallthroughLoop ? taken : fallthrough;
	const guardBody = terminalGuardBody(cfg, guardTarget, allowed);
	if (!guardBody) return null;
	// The guard arm is claimed as one Basic Region, so nothing inside it is
	// ever offered to the recursion. A `try` on that chain would lose its
	// exception Region for the whole function; leave those arms to the
	// ordinary If builder, which recurses into every block it owns.
	if (
		[...guardBody.sourceBlocks].some((block) =>
			exceptionStartsAt(block, descriptors) ||
			descriptors.exceptions.handlerByAddress.has(block) ||
			descriptors.exceptions.handlers.some((descriptor) =>
				descriptor.protectedBlocks.has(block)
			)
		)
	) return null;

	return {
		kind: 'if',
		header: cfg.entry,
		test: guardTarget === taken
			? t.cloneNode(block.terminator.test, true)
			: invertTest(t.cloneNode(block.terminator.test, true)),
		consequent: guardBody,
		alternate: {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		},
		join: loopHeader,
		sourceBlocks: new AddressSet([cfg.entry, ...guardBody.sourceBlocks]),
	};
}

/**
 * Structure a shared-arm shape containing an already bounded loop:
 *
 *     A ──────────────┐
 *     └─> guard ──────┼─> shared arm ─> join
 *             └───────────────────────> join
 *
 * Some guards compute values before their predicate. Keeping the guard as its
 * own If Region preserves that body and its branch, while the guard-to-join
 * edge becomes a deferred exit from a labelled sequence so the shared arm is
 * owned and emitted exactly once.
 */
function tryStructureSharedAlternateGuardRegion(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	regionAt: (entry: BlockAddr, allowed?: AddressSet<BlockAddr>) => Region,
	allowed?: AddressSet<BlockAddr>,
): { region: Region; continuation: BlockAddr } | null {
	if (cfg.hasExceptionRegions) return null;
	const entry = cfg.blocks.get(cfg.entry);
	if (!entry || entry.terminator.kind !== 'if') return null;
	const containingLoops = analyses.naturalLoops.loops.filter((loop) =>
		loop.body.has(cfg.entry)
	);
	const sharedScope = allowed ??
		containingLoops.toSorted((left, right) =>
			left.body.size - right.body.size
		)
			.at(0)?.body;
	if (!sharedScope?.has(cfg.entry)) return null;
	const boundedLoops = analyses.naturalLoops.loops.filter((loop) =>
		loop.body.isSubsetOf(sharedScope)
	);
	if (
		boundedLoops.length === 0 ||
		boundedLoops.some((loop) => hasUnsupportedBoundedLoopArm(loop, cfg))
	) return null;

	for (
		const [guardEntry, sharedEntry] of [
			[entry.terminator.fallthrough, entry.terminator.taken],
			[entry.terminator.taken, entry.terminator.fallthrough],
		] as const
	) {
		const guard = cfg.blocks.get(guardEntry);
		if (!guard || guard.terminator.kind !== 'if') continue;
		const guardFallsThroughShared =
			guard.terminator.fallthrough === sharedEntry;
		const guardTakesShared = guard.terminator.taken === sharedEntry;
		if (guardFallsThroughShared === guardTakesShared) continue;
		const join = guardFallsThroughShared
			? guard.terminator.taken
			: guard.terminator.fallthrough;
		if (join === cfg.entry || join === guardEntry || join === sharedEntry) {
			continue;
		}
		if (!sharedScope.has(guardEntry) || !sharedScope.has(sharedEntry)) {
			continue;
		}
		const guardPredecessors = cfg.normalPredecessors.get(guardEntry) ??
			new AddressSet<BlockAddr>();
		if (
			guardPredecessors.size !== 1 ||
			!guardPredecessors.has(cfg.entry)
		) continue;
		const sharedPredecessors = cfg.normalPredecessors.get(sharedEntry) ??
			new AddressSet<BlockAddr>();
		if (
			[...sharedPredecessors].some((predecessor) =>
				predecessor !== cfg.entry && predecessor !== guardEntry
			)
		) continue;

		const sharedSESE = findWeakSESE(sharedEntry, join, {
			cfg,
			dominators: analyses.dominators,
			postdominators: analyses.postdominators,
		});
		const sharedBody = sharedSESE?.body.size &&
				sharedSESE.deferredExits.length === 0 &&
				sharedSESE.body.isSubsetOf(sharedScope)
			? sharedSESE.body
			: sharedAlternateArmBody(
				cfg,
				sharedEntry,
				join,
				guardEntry,
				sharedScope,
			);
		if (!sharedBody || sharedBody.size === 0) continue;
		const shared = regionAt(sharedEntry, sharedBody);
		const sharedCovered = regionCoveredBlocks(shared);
		if (
			shared.kind === 'fallback' ||
			!shared.sourceBlocks.isSubsetOf(sharedBody) ||
			!sharedBody.isSubsetOf(sharedCovered) ||
			regionUnstructuredBranches(shared, cfg).size > 0
		) continue;

		const empty = (): Region => ({
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		});
		const deferred: Region = {
			kind: 'deferredExit',
			exit: {
				kind: 'toJoin',
				target: join,
				edge: { from: guardEntry, to: join, kind: 'normal' },
				actions: [],
			},
			sourceBlocks: new AddressSet(),
		};
		const guardTakenIsJoin = guard.terminator.taken === join;
		const guardRegion: Region = {
			kind: 'if',
			header: guardEntry,
			test: t.cloneNode(guard.terminator.test, true),
			consequent: guardTakenIsJoin ? deferred : empty(),
			alternate: guardTakenIsJoin ? empty() : deferred,
			join: sharedEntry,
			conditionalValue: {
				kind: 'conditionalPhi',
				branch: guardEntry,
				consequentEntry: guard.terminator.taken,
				alternateEntry: guard.terminator.fallthrough,
				join: sharedEntry,
				forms: ['shortcut', 'ternary'],
			},
			sourceBlocks: new AddressSet([guardEntry]),
		};
		const entryTakesGuard = entry.terminator.taken === guardEntry;
		const outer: Region = {
			kind: 'if',
			header: cfg.entry,
			test: t.cloneNode(entry.terminator.test, true),
			consequent: entryTakesGuard ? guardRegion : empty(),
			alternate: entryTakesGuard ? empty() : guardRegion,
			join: sharedEntry,
			conditionalValue: {
				kind: 'conditionalPhi',
				branch: cfg.entry,
				consequentEntry: entry.terminator.taken,
				alternateEntry: entry.terminator.fallthrough,
				join: sharedEntry,
				forms: ['shortcut', 'ternary'],
			},
			sourceBlocks: new AddressSet([cfg.entry, guardEntry]),
		};
		const sequence = closeSingleDeferredJoin({
			kind: 'sequence',
			regions: [outer, shared],
			sourceBlocks: new AddressSet([
				cfg.entry,
				guardEntry,
				...shared.sourceBlocks,
			]),
		});
		const expected = new AddressSet([
			cfg.entry,
			guardEntry,
			...sharedBody,
		]);
		if (
			!sequence.sourceBlocks.isSubsetOf(expected) ||
			!expected.isSubsetOf(regionCoveredBlocks(sequence))
		) continue;
		return { region: sequence, continuation: join };
	}
	return null;
}

function sharedAlternateArmBody(
	cfg: ImmutableCFG,
	sharedEntry: BlockAddr,
	join: BlockAddr,
	guardEntry: BlockAddr,
	allowed: AddressSet<BlockAddr>,
): AddressSet<BlockAddr> | null {
	const body = new AddressSet<BlockAddr>();
	const pending = [sharedEntry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (address === join || body.has(address)) continue;
		if (
			address === cfg.entry || address === guardEntry ||
			!allowed.has(address) || !cfg.blocks.has(address)
		) return null;
		body.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
	}
	return body;
}

function shouldDeferLoopEntryGuard(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
): boolean {
	const block = cfg.blocks.get(cfg.entry);
	if (!block || block.terminator.kind !== 'if') return false;
	const fallthroughLoop = analyses.naturalLoops.loopByHeader.get(
		block.terminator.fallthrough,
	);
	const takenLoop = analyses.naturalLoops.loopByHeader.get(
		block.terminator.taken,
	);
	if (!!fallthroughLoop === !!takenLoop) return false;
	const loop = fallthroughLoop ?? takenLoop;
	if (!loop) return false;
	const otherTarget = fallthroughLoop
		? block.terminator.taken
		: block.terminator.fallthrough;
	return !loop.body.has(otherTarget);
}

function terminalGuardBody(
	cfg: ImmutableCFG,
	entry: BlockAddr,
	allowed?: AddressSet<BlockAddr>,
): Region | null {
	if (allowed && !allowed.has(entry)) {
		const terminator = cfg.blocks.get(entry)?.terminator;
		if (
			!cfg.hasExceptionRegions &&
			((terminator?.kind === 'return' && !cfg.isScript) ||
				terminator?.kind === 'throw' ||
				terminator?.kind === 'unreachable')
		) {
			return {
				kind: 'terminalReference',
				entry,
				edge: { from: cfg.entry, to: entry, kind: 'normal' },
				sourceBlocks: new AddressSet(),
			};
		}
		return null;
	}
	const body = new AddressSet<BlockAddr>();
	let cursor: BlockAddr | undefined = entry;
	while (cursor != null && !body.has(cursor)) {
		const block = cfg.blocks.get(cursor);
		if (!block) return null;
		body.add(cursor);
		if (
			block.terminator.kind === 'return' ||
			block.terminator.kind === 'throw' ||
			block.terminator.kind === 'unreachable'
		) {
			return {
				kind: 'basic',
				body: [],
				sourceBlocks: body,
			};
		}
		if (block.terminator.kind !== 'goto') return null;
		cursor = block.terminator.target;
	}
	return null;
}

function tryStructureTerminalIfLadder(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	allowed?: AddressSet<BlockAddr>,
	active = new AddressSet<BlockAddr>(),
	structuredHandlers = new AddressSet<BlockAddr>(),
): Region | null {
	const block = cfg.blocks.get(entry);
	if (!block || block.terminator.kind !== 'if') return null;
	if (allowed && !allowed.has(entry)) return null;
	// A terminal ladder is only valid when its emitted arms are disjoint. Small
	// candidates can be built speculatively and checked precisely below. For a
	// large DAG, recursively rebuilding overlapping suffixes can grow
	// exponentially before that check (Discord function 82413 has this shape), so
	// reject a provably overlapping candidate before descending. The ordinary CFG
	// reducers still get the untouched graph as their fallback.
	if (
		cfg.blocks.size > MAX_SPECULATIVE_TERMINAL_LADDER_BLOCKS &&
		normalReachableRegionsOverlap(
			block.terminator.fallthrough,
			block.terminator.taken,
			cfg,
			allowed,
		)
	) return null;
	const handlersBeforeArms = new AddressSet(structuredHandlers);

	let consequent = structureRegionAt(
		block.terminator.taken,
		cfg,
		analyses,
		descriptors,
		allowed,
		active,
		structuredHandlers,
	);
	let alternate = structureRegionAt(
		block.terminator.fallthrough,
		cfg,
		analyses,
		descriptors,
		allowed,
		active,
		structuredHandlers,
	);
	const rollbackHandlers = () => {
		// Both arms are speculative until the ladder is proven disjoint. A nested
		// exception region may have marked its handler while building an arm; if the
		// ladder is rejected, leave the shared ledger exactly as we found it so the
		// enclosing DAG can structure that handler at its genuine entry.
		for (const handler of [...structuredHandlers]) {
			if (!handlersBeforeArms.has(handler)) {
				structuredHandlers.delete(handler);
			}
		}
	};
	if (
		consequent.kind === 'fallback' ||
		alternate.kind === 'fallback'
	) {
		rollbackHandlers();
		return null;
	}

	const overlap = regionBlockIntersection(consequent, alternate);
	if (overlap.size > 0) {
		// Only shared terminal leaves may be referenced without ownership. Loop and
		// exception Regions remain intact because the rewrite descends exclusively
		// through subtrees whose source ownership intersects the terminal overlap.
		const referencedConsequent = replaceSharedTerminalLeaves(
			consequent,
			overlap,
			cfg,
		);
		const referencedAlternate = replaceSharedTerminalLeaves(
			alternate,
			overlap,
			cfg,
		);
		if (!referencedConsequent || !referencedAlternate) {
			rollbackHandlers();
			return null;
		}
		consequent = referencedConsequent;
		alternate = referencedAlternate;
	}

	return {
		kind: 'if',
		header: entry,
		test: t.cloneNode(block.terminator.test, true),
		consequent,
		alternate,
		join: entry,
		sourceBlocks: new AddressSet([
			entry,
			...consequent.sourceBlocks,
			...alternate.sourceBlocks,
		]),
	};
}

function regionBlockIntersection(
	left: Region,
	right: Region,
): AddressSet<BlockAddr> {
	return left.sourceBlocks.intersection(right.sourceBlocks);
}

/**
 * Convert an overlapping terminal leaf into a non-owning reference. Only
 * basic/sequence/if trees are accepted here: loop and exception ownership is
 * handled by their dedicated Region reducers.
 */
function replaceSharedTerminalLeaves(
	region: Region,
	shared: AddressSet<BlockAddr>,
	cfg: ImmutableCFG,
): Region | null {
	if (!regionsOverlap(region.sourceBlocks, shared)) return region;
	switch (region.kind) {
		case 'basic': {
			if (region.sourceBlocks.size !== 1) return null;
			const [entry] = region.sourceBlocks;
			if (!shared.has(entry) || !isShareableTerminal(entry, cfg)) {
				return null;
			}
			return {
				kind: 'terminalReference',
				entry,
				sourceBlocks: new AddressSet(),
			};
		}
		case 'sequence': {
			const regions: Region[] = [];
			for (const child of region.regions) {
				const replaced = replaceSharedTerminalLeaves(
					child,
					shared,
					cfg,
				);
				if (!replaced) return null;
				regions.push(replaced);
			}
			return {
				...region,
				regions,
				sourceBlocks: region.sourceBlocks.difference(shared),
			};
		}
		case 'if': {
			const header =
				[...region.sourceBlocks].toSorted((left, right) =>
					left - right
				)[0];
			if (header == null || shared.has(header)) return null;
			const consequent = replaceSharedTerminalLeaves(
				region.consequent,
				shared,
				cfg,
			);
			const alternate = replaceSharedTerminalLeaves(
				region.alternate,
				shared,
				cfg,
			);
			if (!consequent || !alternate) return null;
			return {
				...region,
				consequent,
				alternate,
				sourceBlocks: region.sourceBlocks.difference(shared),
			};
		}
		default:
			return null;
	}
}

function isShareableTerminal(
	entry: BlockAddr,
	cfg: ImmutableCFG,
): boolean {
	if (cfg.hasExceptionRegions) return false;
	const terminator = cfg.blocks.get(entry)?.terminator;
	return (terminator?.kind === 'return' && !cfg.isScript) ||
		terminator?.kind === 'throw' ||
		terminator?.kind === 'unreachable';
}

function normalReachableRegionsOverlap(
	leftEntry: BlockAddr,
	rightEntry: BlockAddr,
	cfg: ImmutableCFG,
	allowed?: AddressSet<BlockAddr>,
): boolean {
	const left = normalReachableWithin(leftEntry, cfg, allowed);
	const stack = [rightEntry];
	const seen = new AddressSet<BlockAddr>();
	while (stack.length > 0) {
		const address = stack.pop()!;
		if (
			seen.has(address) || !cfg.blocks.has(address) ||
			(allowed && !allowed.has(address))
		) continue;
		if (left.has(address)) return true;
		seen.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			stack.push(successor);
		}
	}
	return false;
}

function normalReachableWithin(
	entry: BlockAddr,
	cfg: ImmutableCFG,
	allowed?: AddressSet<BlockAddr>,
): AddressSet<BlockAddr> {
	const reachable = new AddressSet<BlockAddr>();
	const stack = [entry];
	while (stack.length > 0) {
		const address = stack.pop()!;
		if (
			reachable.has(address) || !cfg.blocks.has(address) ||
			(allowed && !allowed.has(address))
		) continue;
		reachable.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			stack.push(successor);
		}
	}
	return reachable;
}

function regionsOverlap(
	left: AddressSet<BlockAddr>,
	right: AddressSet<BlockAddr>,
): boolean {
	for (const block of left) {
		if (right.has(block)) return true;
	}
	return false;
}

/**
 * Retain the old one-loop compatibility completion for shapes deliberately
 * excluded from the exact forest composer (notably protected and for-in CFGs).
 * The generic multi-root path never uses this address-ordered fallback.
 */
function appendSingleTopLevelLoop(
	region: Region,
	entry: BlockAddr,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	allowed?: AddressSet<BlockAddr>,
	active = new AddressSet<BlockAddr>(),
	structuredHandlers = new AddressSet<BlockAddr>(),
): Region {
	if (regionContainsKind(region, 'loop')) return region;
	const loop =
		analyses.naturalLoops.loops.filter((candidate) =>
			isTopLevelLoopWithin(candidate, analyses, allowed) &&
			(!allowed || allowed.has(candidate.header)) &&
			!descriptors.exceptions.finalizerCopyModel.copyBlocks.has(
				candidate.header,
			) &&
			!region.sourceBlocks.has(candidate.header) &&
			analyses.loopDominators.dominates(entry, candidate.header)
		).toSorted((left, right) => left.header - right.header)[0];
	if (!loop) return region;

	const structureLoopChild = (
		cursor: BlockAddr,
		childAllowed?: AddressSet<BlockAddr>,
		ownerClosed?: boolean,
	): Region | null => {
		if (cursor === loop.header) return null;
		// Match the primary loop path's protected/for-in ownership rule.
		const ownedIteratorCleanupHandlers = iteratorCleanupHandlersForLoop(
			loop,
			cfg,
			descriptors,
		);
		if (
			((exceptionSplitsProtectedRange(
				cursor,
				descriptors,
				ownedIteratorCleanupHandlers,
			) && !ownerClosed) || hasForInDispatchAt(cfg, cursor)) &&
			!analyses.naturalLoops.loopByHeader.has(cursor) &&
			!descriptors.switches.switchByDispatch.has(cursor) &&
			!exceptionStartsAt(cursor, descriptors)
		) return null;
		if (
			childAllowed &&
			exceptionStartsAt(cursor, descriptors) &&
			!exceptionProtectedBlocksContainedBy(
				cursor,
				descriptors,
				childAllowed,
			)
		) {
			return null;
		}
		return structureRegionAt(
			cursor,
			cfg,
			analyses,
			descriptors,
			childAllowed ?? allowed,
			active,
			structuredHandlers,
		);
	};
	const loopRegion = tryStructureLoopRegion(
		cfgWithEntry(cfg, loop.header),
		analyses,
		descriptors,
		structureLoopChild,
		{
			allowHierarchicalExits: true,
			structuredHandlers,
		},
	);
	if (!loopRegion || loopRegion.kind !== 'loop') return region;
	const mixedAbruptSwitch = tryStructureMixedAbruptLoopSwitch(
		loopRegion,
		() =>
			tryStructureLoopRegion(
				cfgWithEntry(cfg, loop.header),
				analyses,
				descriptors,
				structureLoopChild,
				{
					allowHierarchicalExits: true,
					allowMixedAbruptExits: true,
					structuredHandlers,
				},
			),
		cfg,
		descriptors,
		(cursor, childAllowed) =>
			structureRegionAt(
				cursor,
				cfg,
				analyses,
				descriptors,
				childAllowed ?? allowed,
				active,
				structuredHandlers,
			),
		allowed,
	);
	if (mixedAbruptSwitch) {
		return {
			kind: 'sequence',
			regions: [region, mixedAbruptSwitch],
			sourceBlocks: new AddressSet([
				...region.sourceBlocks,
				...mixedAbruptSwitch.sourceBlocks,
			]),
		};
	}

	const hierarchical = appendGuardedLoopWithHierarchicalExit(
		region,
		loop,
		loopRegion,
		cfg,
		analyses,
		descriptors,
		allowed,
		active,
		structuredHandlers,
	);
	if (hierarchical) return hierarchical;

	const directGuard = appendDirectGuardedSingleLoop(
		region,
		loopRegion,
		cfg,
		analyses,
		descriptors,
		allowed,
		active,
		structuredHandlers,
	);
	if (directGuard) return directGuard;

	const sequenceRegions = [region, loopRegion];
	const sourceBlocks = new AddressSet([
		...region.sourceBlocks,
		...loopRegion.sourceBlocks,
	]);
	const continuationEntry = loopContinuationEntry(
		loopRegion,
		cfg,
		allowed,
	) ?? uniqueRegionExit(cfg, sourceBlocks, allowed);
	if (continuationEntry != null && !sourceBlocks.has(continuationEntry)) {
		const continuation = structureRegionAt(
			continuationEntry,
			cfg,
			analyses,
			descriptors,
			allowed,
			active,
			structuredHandlers,
		);
		if (
			continuation.sourceBlocks.size > 0 &&
			!continuation.sourceBlocks.isSubsetOf(sourceBlocks)
		) {
			sequenceRegions.push(continuation);
			for (const block of continuation.sourceBlocks) {
				sourceBlocks.add(block);
			}
		}
	}

	return {
		kind: 'sequence',
		regions: sequenceRegions,
		sourceBlocks,
	};
}

/**
 * The compatibility one-loop path can discover a specialized for-in loop only
 * after its entry guard has already been emitted as Basic. Re-form the exact
 * optional-loop boundary here: one guard edge enters the loop, the other skips
 * to a continuation also reached by an ordinary loop exit. This gives both
 * incoming Phi edges an explicit owner and keeps the continuation outside the
 * loop exactly once.
 */
function appendDirectGuardedSingleLoop(
	prefix: Region,
	loop: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	allowed: AddressSet<BlockAddr> | undefined,
	active: AddressSet<BlockAddr>,
	structuredHandlers: AddressSet<BlockAddr>,
): Region | null {
	if (cfg.hasExceptionRegions || loop.syntax?.kind !== 'forIn') return null;
	const guards = [...prefix.sourceBlocks].flatMap((address) => {
		const terminator = cfg.blocks.get(address)?.terminator;
		if (terminator?.kind !== 'if') return [];
		const takenEnters = terminator.taken === loop.header;
		const fallthroughEnters = terminator.fallthrough === loop.header;
		if (takenEnters === fallthroughEnters) return [];
		return [{
			address,
			terminator,
			loopOnTaken: takenEnters,
			continuation: takenEnters
				? terminator.fallthrough
				: terminator.taken,
		}];
	});
	if (guards.length !== 1) return null;
	const [guard] = guards;
	if (
		loop.sourceBlocks.has(guard.continuation) ||
		(allowed && !allowed.has(guard.continuation)) ||
		!loop.exits.some((exit) => exit.to === guard.continuation)
	) return null;

	const trimmedPrefix = removeBasicBlocks(
		prefix,
		new AddressSet([guard.address]),
	);
	if (!trimmedPrefix) return null;
	const empty = emptyRegion();
	const guardedLoop: Region = {
		kind: 'if',
		header: guard.address,
		test: t.cloneNode(guard.terminator.test, true),
		consequent: guard.loopOnTaken ? loop : empty,
		alternate: guard.loopOnTaken ? empty : loop,
		join: guard.continuation,
		conditionalValue: {
			kind: 'conditionalPhi',
			branch: guard.address,
			consequentEntry: guard.terminator.taken,
			alternateEntry: guard.terminator.fallthrough,
			join: guard.continuation,
			forms: ['shortcut', 'ternary'],
		},
		sourceBlocks: new AddressSet([
			guard.address,
			...loop.sourceBlocks,
		]),
	};
	const continuation = structureRegionAt(
		guard.continuation,
		cfg,
		analyses,
		descriptors,
		allowed,
		active,
		structuredHandlers,
	);
	if (
		continuation.sourceBlocks.size === 0 ||
		regionsOverlap(guardedLoop.sourceBlocks, continuation.sourceBlocks)
	) return null;

	const regions: Region[] = [];
	if (regionCoveredBlocks(trimmedPrefix).size > 0) {
		regions.push(trimmedPrefix);
	}
	regions.push(guardedLoop, continuation);
	return {
		kind: 'sequence',
		regions,
		sourceBlocks: new AddressSet(
			regions.flatMap((candidate) => [...candidate.sourceBlocks]),
		),
	};
}

/**
 * Recover an acyclic guard chain that can either enter a loop or skip its
 * ordinary continuation, together with a rarer loop exit that skips that same
 * continuation. The two transfers require nested labels:
 *
 *     outer: { inner: { guard; loop; } ordinarySuffix; }
 */
function appendGuardedLoopWithHierarchicalExit(
	prefix: Region,
	loop: CFGAnalyses['naturalLoops']['loops'][number],
	loopRegion: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	allowed: AddressSet<BlockAddr> | undefined,
	active: AddressSet<BlockAddr>,
	structuredHandlers: AddressSet<BlockAddr>,
): Region | null {
	if (cfg.hasExceptionRegions || loopRegion.continuation == null) return null;
	const sequenceExits = loopRegion.exits.flatMap((exit) =>
		exit.sequenceExit ? [exit.sequenceExit] : []
	);
	if (sequenceExits.length === 0) return null;
	const outerTarget = sequenceExits[0]!.target;
	const outerLabel = `cfg_exit_${outerTarget.toString(16)}`;
	if (
		sequenceExits.some((exit) => exit.target !== outerTarget) ||
		(allowed && !allowed.has(outerTarget))
	) return null;
	const labelledLoop = activateLoopSequenceExit(
		loopRegion,
		outerTarget,
		outerLabel,
	);

	const guardEntry = loopEntryGuardEntry(
		prefix.sourceBlocks,
		loop,
		cfg,
		analyses,
	);
	if (guardEntry == null) return null;
	const guard = structureLoopEntryGuard(
		guardEntry,
		loop.header,
		labelledLoop.continuation!,
		new AddressSet(
			[...(allowed ?? analyses.reachability.normalReachable)].filter(
				(block) => !loop.body.has(block),
			),
		),
		cfg,
	);
	if (!guard || !guard.reachesHeader || !guard.skipsLoop) return null;
	const trimmedPrefix = removeBasicBlocks(prefix, guard.region.sourceBlocks);
	if (!trimmedPrefix) return null;

	const innerLabel = `cfg_exit_${labelledLoop.continuation!.toString(16)}`;
	const guarded = rewriteDeferredJoinAsBreak(
		guard.region,
		labelledLoop.continuation!,
		innerLabel,
	);
	const inner: Region = {
		kind: 'sequence',
		exitLabel: innerLabel,
		regions: [guarded, labelledLoop],
		sourceBlocks: new AddressSet([
			...guard.region.sourceBlocks,
			...labelledLoop.sourceBlocks,
		]),
	};

	const suffixAllowed = reachableBeforeTarget(
		labelledLoop.continuation!,
		outerTarget,
		cfg,
		allowed,
	);
	if (suffixAllowed.size === 0) return null;
	const suffix = structureRegionAt(
		loopRegion.continuation,
		cfg,
		analyses,
		descriptors,
		suffixAllowed,
		active,
		structuredHandlers,
	);
	if (
		suffix.sourceBlocks.size === 0 ||
		!suffix.sourceBlocks.isSubsetOf(suffixAllowed)
	) return null;
	const outer: Region = {
		kind: 'sequence',
		exitLabel: outerLabel,
		regions: [inner, suffix],
		sourceBlocks: new AddressSet([
			...inner.sourceBlocks,
			...suffix.sourceBlocks,
		]),
	};

	const regions: Region[] = [];
	if (regionCoveredBlocks(trimmedPrefix).size > 0) {
		regions.push(trimmedPrefix);
	}
	regions.push(outer);
	const sourceBlocks = new AddressSet<BlockAddr>([
		...trimmedPrefix.sourceBlocks,
		...outer.sourceBlocks,
	]);
	const continuation = structureRegionAt(
		outerTarget,
		cfg,
		analyses,
		descriptors,
		allowed,
		active,
		structuredHandlers,
	);
	if (
		continuation.sourceBlocks.size > 0 &&
		!continuation.sourceBlocks.isSubsetOf(sourceBlocks)
	) {
		regions.push(continuation);
		for (const block of continuation.sourceBlocks) sourceBlocks.add(block);
	}
	return regions.length === 1 ? regions[0]! : {
		kind: 'sequence',
		regions,
		sourceBlocks,
	};
}

function activateLoopSequenceExit(
	loop: Extract<Region, { kind: 'loop' }>,
	target: BlockAddr,
	label: string,
): Extract<Region, { kind: 'loop' }> {
	const exits = loop.exits.map((exit) =>
		exit.sequenceExit?.target === target
			? { ...exit, sequenceExit: { target, label } }
			: exit
	);
	const exitFor = (exit: LoopRegionExit | undefined) =>
		exit == null
			? undefined
			: exits.find((candidate) =>
				candidate.from === exit.from && candidate.to === exit.to
			) ?? exit;
	const rewrite = (region: Region): Region => {
		if (
			(region.kind === 'break' || region.kind === 'labelBreak') &&
			region.exit?.sequenceExit?.target === target
		) {
			if (target === loop.header) {
				return {
					kind: 'continue',
					target,
					exit: exitFor(region.exit),
					sourceBlocks: new AddressSet(region.sourceBlocks),
				};
			}
			return {
				kind: 'labelBreak',
				label,
				target,
				exit: exitFor(region.exit),
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		}
		switch (region.kind) {
			case 'sequence':
				return {
					...region,
					regions: region.regions.map(rewrite),
					sourceBlocks: new AddressSet(region.sourceBlocks),
				};
			case 'if':
				return {
					...region,
					consequent: rewrite(region.consequent),
					alternate: rewrite(region.alternate),
					sourceBlocks: new AddressSet(region.sourceBlocks),
				};
			case 'switch':
				return {
					...region,
					cases: region.cases.map((switchCase) => ({
						...switchCase,
						body: rewrite(switchCase.body),
					})),
					defaultBody: rewrite(region.defaultBody),
					sourceBlocks: new AddressSet(region.sourceBlocks),
				};
			default:
				return region;
		}
	};
	return { ...loop, exits, body: rewrite(loop.body) };
}

/**
 * Resolve a loop with several ordinary break destinations against the final
 * lexical Region order.
 *
 * The first destination owned after the loop is its JavaScript fallthrough.
 * Every other destination becomes an ordered sequence exit; the label pass
 * below then wraps exactly the statements that exit must skip. Doing this only
 * after the full tree exists lets loops nested in protected Regions target
 * continuations owned after the enclosing `try`.
 */
function routeMultiDestinationLoopContinuations(
	region: Region,
	following: readonly Region[] = [],
): Region {
	if (region.kind === 'sequence') {
		const regions = new Array<Region>(region.regions.length);
		let later = [...following];
		for (let index = region.regions.length - 1; index >= 0; index--) {
			const child = routeMultiDestinationLoopContinuations(
				region.regions[index]!,
				later,
			);
			regions[index] = child;
			later = [child, ...later];
		}
		return { ...region, regions };
	}
	const routeChild = (child: Region) =>
		routeMultiDestinationLoopContinuations(child, following);
	if (region.kind === 'if') {
		return {
			...region,
			consequent: routeChild(region.consequent),
			alternate: routeChild(region.alternate),
		};
	}
	if (region.kind === 'switch') {
		return {
			...region,
			cases: region.cases.map((switchCase) => ({
				...switchCase,
				body: routeChild(switchCase.body),
			})),
			defaultBody: routeChild(region.defaultBody),
		};
	}
	if (region.kind === 'tryCatch') {
		return {
			...region,
			body: routeChild(region.body),
			handler: routeChild(region.handler),
		};
	}
	if (region.kind === 'tryFinally') {
		return {
			...region,
			body: routeChild(region.body),
			finalizer: routeChild(region.finalizer),
		};
	}
	if (region.kind !== 'loop') return region;

	const body = routeChild(region.body);
	const exits = region.exits.map((exit) =>
		exit.trailer ? { ...exit, trailer: routeChild(exit.trailer) } : exit
	);
	if (region.continuation != null) return { ...region, body, exits };
	const breaks = exits.filter((exit) =>
		exit.kind === 'break' && exit.trailer == null
	);
	const destinations = new AddressSet<BlockAddr>(
		breaks.map((exit) => exit.to),
	);
	if (destinations.size < 2) return { ...region, body, exits };
	const ordered = following.flatMap((candidate) =>
		[...destinations].filter((target) => candidate.sourceBlocks.has(target))
	);
	if (new AddressSet(ordered).size !== destinations.size) {
		return { ...region, body, exits };
	}
	const continuation = ordered[0]!;
	return {
		...region,
		body,
		continuation,
		exits: exits.map((exit) =>
			exit.kind === 'break' && exit.trailer == null &&
				exit.to !== continuation
				? {
					...exit,
					sequenceExit: exit.sequenceExit ?? { target: exit.to },
				}
				: exit
		),
	};
}

/**
 * A Loop Region can be built from several places, and only the ones that
 * compose an enclosing scope can name it. `structureExits` therefore attaches
 * the block an ordered exit resumes at without a label, leaving the exit to
 * lower as a bare `break` that lands at the loop's own continuation instead —
 * running everything in between.
 *
 * Everything needed to name it is present once the tree is built: the sequence
 * holding the loop also holds the child that owns the target. Wrap the span
 * between them in a labelled sequence so the exit becomes `break <label>`.
 *
 * Running this over the finished tree rather than at each construction site is
 * deliberate: the shape is the same wherever the loop came from, and the paths
 * that build nested loops never reach the composers that could label them.
 */
export function labelPendingLoopSequenceExits(region: Region): Region {
	const region_ = mapChildRegions(region, labelPendingLoopSequenceExits);
	if (region_.kind !== 'sequence') return region_;
	const children = region_.regions;
	for (let index = 0; index < children.length; index++) {
		const routed = [...pendingSequenceExitTargets(children[index]!)]
			.map((target) => ({
				target,
				owner: children.findIndex((child, at) =>
					at > index && child.sourceBlocks.has(target)
				),
			}))
			.filter((candidate) => candidate.owner >= 0)
			.toSorted((left, right) =>
				left.owner - right.owner || left.target - right.target
			)[0];
		if (!routed) continue;
		const { target, owner } = routed;
		const label = `cfg_exit_${target.toString(16)}`;
		const span = children.slice(index, owner).map((child) =>
			activatePendingSequenceExit(child, target, label)
		);
		const scoped: Region = {
			kind: 'sequence',
			exitLabel: label,
			regions: span,
			sourceBlocks: new AddressSet(
				span.flatMap((child) => [...child.sourceBlocks]),
			),
		};
		return labelPendingLoopSequenceExits({
			...region_,
			regions: [
				...children.slice(0, index),
				scoped,
				...children.slice(owner),
			],
		});
	}
	return region_;
}

/**
 * A protected exit lowers as a bare `break`, which reaches only the innermost
 * enclosing loop or switch. When the exit leaves a protected range that no loop
 * encloses, that `break` has no statement to leave at all.
 *
 * The target is nevertheless present in the finished tree: the sequence holding
 * the `try` also holds the child that owns the block the exit resumes at. Wrap
 * the span between them in a labelled sequence and name the exit's transfer, the
 * way the ordered loop exits above are named. JavaScript runs the intervening
 * `finally` clauses on a labelled break, which is exactly what the deferral
 * models.
 */
export function labelStrandedProtectedExits(region: Region): Region {
	return labelStrandedProtectedExitsWithin(region, { next: 0 });
}

interface StrandedExitLabels {
	next: number;
}

function labelStrandedProtectedExitsWithin(
	region: Region,
	labels: StrandedExitLabels,
): Region {
	const region_ = mapChildRegions(
		region,
		(child) => labelStrandedProtectedExitsWithin(child, labels),
	);
	if (region_.kind !== 'sequence') return region_;
	const children = region_.regions;
	for (let index = 0; index < children.length; index++) {
		const routed = [...strandedProtectedExitTargets(children[index]!)]
			.map((target) => ({
				target,
				owner: children.findIndex((child, at) =>
					at > index && child.sourceBlocks.has(target)
				),
			}))
			.toSorted((left, right) =>
				(left.owner < 0 ? Number.MAX_SAFE_INTEGER : left.owner) -
					(right.owner < 0 ? Number.MAX_SAFE_INTEGER : right.owner) ||
				left.target - right.target
			)[0];
		if (!routed) continue;
		const { target, owner } = routed;
		// One name per wrap site: a subtree reached from two places would other-
		// wise declare the same label twice, which is not valid JavaScript.
		const label = `cfg_leave_${target.toString(16)}_${labels.next++}`;
		const end = owner >= 0 ? owner : index + 1;
		const span = children.slice(index, end).map((child) =>
			nameStrandedProtectedExits(child, target, label)
		);
		const scoped: Region = {
			kind: 'sequence',
			exitLabel: label,
			regions: span,
			sourceBlocks: new AddressSet(
				span.flatMap((child) => [...child.sourceBlocks]),
			),
		};
		return labelStrandedProtectedExitsWithin({
			...region_,
			regions: [
				...children.slice(0, index),
				scoped,
				...children.slice(end),
			],
		}, labels);
	}
	return region_;
}

/**
 * Blocks the unnamed protected exits inside `region` resume at.
 *
 * An exit inside a loop is not stranded: its bare `break` leaves that loop,
 * which is the transfer the loop's own exit ledger already models.
 */
function strandedProtectedExitTargets(
	region: Region,
): AddressSet<BlockAddr> {
	const targets = new AddressSet<BlockAddr>();
	// A loop or switch binds a bare `break`, so the walk stops there: exits
	// inside them are not stranded.
	const visit = (candidate: Region) => {
		switch (candidate.kind) {
			case 'deferredExit':
				if (
					candidate.exit.kind === 'loopExit' &&
					candidate.exit.label == null
				) targets.add(candidate.exit.target);
				return;
			case 'sequence':
				candidate.regions.forEach(visit);
				return;
			case 'if':
				visit(candidate.consequent);
				visit(candidate.alternate);
				return;
			case 'tryCatch':
				visit(candidate.body);
				visit(candidate.handler);
				return;
			case 'tryFinally':
				visit(candidate.body);
				visit(candidate.finalizer);
				return;
			default:
				return;
		}
	};
	visit(region);
	// A target the span already owns is reached by falling through it, so
	// leaving early would skip statements that must still run.
	return targets.difference(region.sourceBlocks);
}

function nameStrandedProtectedExits(
	region: Region,
	target: BlockAddr,
	label: string,
): Region {
	if (region.kind === 'loop' || region.kind === 'switch') return region;
	if (
		region.kind === 'deferredExit' &&
		region.exit.kind === 'loopExit' &&
		region.exit.label == null && region.exit.target === target
	) {
		return {
			...region,
			exit: { ...region.exit, label },
			sourceBlocks: new AddressSet(region.sourceBlocks),
		};
	}
	return mapChildRegions(
		region,
		(child) => nameStrandedProtectedExits(child, target, label),
	);
}

/**
 * A labelled break whose target is the loop it sits inside is a `continue`.
 *
 * A composed scope completes an edge leaving its own bound with a break to the
 * scope's label. When the block that edge resumes at is the header of a loop
 * the edge is already inside, the loop node was contracted and the header
 * looked like the scope's continuation -- but the label lives outside the
 * loop, so the break names a scope the statement cannot reach. The edge is the
 * loop's own back edge, which is what `continue` says.
 */
export function rewriteBackEdgeLabelBreaks(
	region: Region,
	innermostLoopHeader?: BlockAddr,
): Region {
	if (
		region.kind === 'labelBreak' && innermostLoopHeader != null &&
		region.target === innermostLoopHeader
	) {
		return {
			kind: 'continue',
			target: region.target,
			...(region.exit ? { exit: region.exit } : {}),
			sourceBlocks: new AddressSet(region.sourceBlocks),
		};
	}
	if (region.kind === 'loop') {
		return {
			...region,
			sourceBlocks: new AddressSet(region.sourceBlocks),
			body: rewriteBackEdgeLabelBreaks(region.body, region.header),
			exits: region.exits.map((exit) =>
				exit.trailer
					? {
						...exit,
						trailer: rewriteBackEdgeLabelBreaks(
							exit.trailer,
							innermostLoopHeader,
						),
					}
					: exit
			),
		};
	}
	return mapChildRegions(
		region,
		(child) => rewriteBackEdgeLabelBreaks(child, innermostLoopHeader),
	);
}

/** Blocks that unlabelled ordered loop exits inside `region` resume at. */
function pendingSequenceExitTargets(region: Region): AddressSet<BlockAddr> {
	const targets = new AddressSet<BlockAddr>();
	visitRegion(region, (child) => {
		if (child.kind !== 'loop') return;
		for (const exit of child.exits) {
			if (exit.sequenceExit && exit.sequenceExit.label == null) {
				targets.add(exit.sequenceExit.target);
			}
		}
	});
	// A target the region already owns is reached by falling through, not by
	// leaving; labelling it would break past statements that must still run.
	return targets.difference(region.sourceBlocks);
}

function activatePendingSequenceExit(
	region: Region,
	target: BlockAddr,
	label: string,
): Region {
	if (
		region.kind === 'loop' &&
		region.exits.some((exit) =>
			exit.sequenceExit?.target === target &&
			exit.sequenceExit.label == null
		)
	) return activateLoopSequenceExit(region, target, label);
	return mapChildRegions(
		region,
		(child) => activatePendingSequenceExit(child, target, label),
	);
}

function mapChildRegions(
	region: Region,
	map: (child: Region) => Region,
): Region {
	switch (region.kind) {
		case 'sequence':
			return { ...region, regions: region.regions.map(map) };
		case 'if':
			return {
				...region,
				consequent: map(region.consequent),
				alternate: map(region.alternate),
			};
		case 'switch':
			return {
				...region,
				cases: region.cases.map((switchCase) => ({
					...switchCase,
					body: map(switchCase.body),
				})),
				defaultBody: map(region.defaultBody),
			};
		case 'loop':
			return {
				...region,
				body: map(region.body),
				exits: region.exits.map((exit) =>
					exit.trailer
						? { ...exit, trailer: map(exit.trailer) }
						: exit
				),
			};
		case 'tryCatch':
			return {
				...region,
				body: map(region.body),
				handler: map(region.handler),
			};
		case 'tryFinally':
			return {
				...region,
				body: map(region.body),
				finalizer: map(region.finalizer),
			};
		default:
			return region;
	}
}

function loopEntryGuardEntry(
	prefixBlocks: AddressSet<BlockAddr>,
	loop: CFGAnalyses['naturalLoops']['loops'][number],
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
): BlockAddr | null {
	const entries = [...(cfg.normalPredecessors.get(loop.header) ?? [])]
		.filter((predecessor) => !loop.body.has(predecessor));
	if (entries.length < 2) return null;
	const candidates = [...prefixBlocks].filter((candidate) => {
		const block = cfg.blocks.get(candidate);
		return block?.terminator.kind === 'if' &&
			entries.every((entry) =>
				analyses.dominators.dominates(candidate, entry)
			);
	});
	return candidates.find((candidate) =>
		candidates.every((other) =>
			other === candidate ||
			analyses.dominators.dominates(other, candidate)
		)
	) ?? null;
}

interface StructuredLoopEntryGuard {
	region: Region;
	reachesHeader: boolean;
	skipsLoop: boolean;
}

function structureLoopEntryGuard(
	entry: BlockAddr,
	loopHeader: BlockAddr,
	skipTarget: BlockAddr,
	allowed: AddressSet<BlockAddr>,
	cfg: ImmutableCFG,
	seen = new AddressSet<BlockAddr>(),
): StructuredLoopEntryGuard | null {
	if (entry === loopHeader) {
		return {
			region: emptyRegion(),
			reachesHeader: true,
			skipsLoop: false,
		};
	}
	if (entry === skipTarget) return null;
	if (seen.has(entry) || !allowed.has(entry)) return null;
	const block = cfg.blocks.get(entry);
	if (!block) return null;
	const nextSeen = new AddressSet(seen);
	nextSeen.add(entry);
	if (block.terminator.kind === 'goto') {
		const target = block.terminator.target;
		const tail = target === skipTarget
			? deferredJoinRegion(entry, target)
			: structureLoopEntryGuard(
				target,
				loopHeader,
				skipTarget,
				allowed,
				cfg,
				nextSeen,
			);
		if (!tail) return null;
		const basic: Region = {
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([entry]),
		};
		return {
			region: {
				kind: 'sequence',
				regions: [basic, tail.region],
				sourceBlocks: new AddressSet([
					entry,
					...tail.region.sourceBlocks,
				]),
			},
			reachesHeader: tail.reachesHeader,
			skipsLoop: tail.skipsLoop,
		};
	}
	if (block.terminator.kind !== 'if') return null;
	const arm = (target: BlockAddr): StructuredLoopEntryGuard | null => {
		if (target === loopHeader) {
			return {
				region: emptyRegion(),
				reachesHeader: true,
				skipsLoop: false,
			};
		}
		if (target === skipTarget) {
			return deferredJoinRegion(entry, target);
		}
		return structureLoopEntryGuard(
			target,
			loopHeader,
			skipTarget,
			allowed,
			cfg,
			nextSeen,
		);
	};
	const consequent = arm(block.terminator.taken);
	const alternate = arm(block.terminator.fallthrough);
	if (!consequent || !alternate) return null;
	const reachesHeader = consequent.reachesHeader || alternate.reachesHeader;
	if (!reachesHeader) return null;
	return {
		region: {
			kind: 'if',
			header: entry,
			test: t.cloneNode(block.terminator.test, true),
			consequent: consequent.region,
			alternate: alternate.region,
			join: loopHeader,
			sourceBlocks: new AddressSet([
				entry,
				...consequent.region.sourceBlocks,
				...alternate.region.sourceBlocks,
			]),
		},
		reachesHeader,
		skipsLoop: consequent.skipsLoop || alternate.skipsLoop,
	};
}

function deferredJoinRegion(
	from: BlockAddr,
	target: BlockAddr,
): StructuredLoopEntryGuard {
	return {
		region: {
			kind: 'deferredExit',
			exit: {
				kind: 'toJoin',
				edge: { from, to: target, kind: 'normal' },
				target,
				actions: [],
			},
			sourceBlocks: new AddressSet(),
		},
		reachesHeader: false,
		skipsLoop: true,
	};
}

/** Remove guard blocks only when they are still represented as raw basics. */
function removeBasicBlocks(
	region: Region,
	remove: AddressSet<BlockAddr>,
): Region | null {
	if (region.kind === 'basic') {
		const remaining = new AddressSet(
			[...region.sourceBlocks].filter((block) => !remove.has(block)),
		);
		return remaining.size === 0
			? emptyRegion()
			: { ...region, sourceBlocks: remaining };
	}
	if (region.kind !== 'sequence') {
		return regionsOverlap(region.sourceBlocks, remove) ? null : region;
	}
	const children: Region[] = [];
	for (const child of region.regions) {
		const trimmed = removeBasicBlocks(child, remove);
		if (!trimmed) return null;
		if (regionCoveredBlocks(trimmed).size > 0) children.push(trimmed);
	}
	return {
		...region,
		regions: children,
		sourceBlocks: new AddressSet(
			[...region.sourceBlocks].filter((block) => !remove.has(block)),
		),
	};
}

function reachableBeforeTarget(
	entry: BlockAddr,
	target: BlockAddr,
	cfg: ImmutableCFG,
	allowed?: AddressSet<BlockAddr>,
): AddressSet<BlockAddr> {
	const reachable = new AddressSet<BlockAddr>();
	const stack = [entry];
	while (stack.length > 0) {
		const current = stack.pop()!;
		if (
			current === target || reachable.has(current) ||
			(allowed && !allowed.has(current))
		) continue;
		reachable.add(current);
		for (const successor of cfg.normalSuccessors.get(current) ?? []) {
			stack.push(successor);
		}
	}
	return reachable;
}

function isTopLevelLoopWithin(
	loop: CFGAnalyses['naturalLoops']['loops'][number],
	analyses: CFGAnalyses,
	allowed?: AddressSet<BlockAddr>,
): boolean {
	if (loop.parent == null) return true;
	if (!allowed) return false;
	const parent = analyses.naturalLoops.loops[loop.parent];
	return !allowed.has(parent.header);
}

function hasForInDispatchAt(
	cfg: ImmutableCFG,
	address: BlockAddr,
): boolean {
	for (const statement of cfg.blocks.get(address)?.body ?? []) {
		let found = false;
		t.traverseFast(statement, (node) => {
			if (
				t.isCallExpression(node) &&
				t.isV8IntrinsicIdentifier(node.callee, {
					name: 'GetPNameList',
				})
			) found = true;
		});
		if (found) return true;
	}
	return false;
}

function hasForInDispatch(cfg: ImmutableCFG): boolean {
	const cached = forInDispatchCache.get(cfg);
	if (cached != null) return cached;
	let found = false;
	for (const block of cfg.blocks.values()) {
		for (const statement of block.body) {
			t.traverseFast(statement, (node) => {
				if (
					t.isCallExpression(node) &&
					t.isV8IntrinsicIdentifier(node.callee, {
						name: 'GetPNameList',
					})
				) found = true;
			});
			if (found) break;
		}
		if (found) break;
	}
	forInDispatchCache.set(cfg, found);
	return found;
}

function uniqueRegionExit(
	cfg: ImmutableCFG,
	sourceBlocks: AddressSet<BlockAddr>,
	allowed?: AddressSet<BlockAddr>,
): BlockAddr | null {
	const exits = new AddressSet<BlockAddr>();
	for (const block of sourceBlocks) {
		for (const successor of cfg.normalSuccessors.get(block) ?? []) {
			const normalized = normalizeLoopExitTarget(cfg, successor);
			if (sourceBlocks.has(normalized)) continue;
			if (allowed && !allowed.has(normalized)) continue;
			exits.add(normalized);
		}
	}
	return exits.size === 1 ? [...exits][0] : null;
}

function loopContinuationEntry(
	loop: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	allowed?: AddressSet<BlockAddr>,
): BlockAddr | null {
	if (loop.continuation != null) {
		if (loop.sourceBlocks.has(loop.continuation)) return null;
		if (allowed && !allowed.has(loop.continuation)) return null;
		return loop.continuation;
	}
	const exits = new AddressSet<BlockAddr>();
	for (const exit of loop.exits) {
		if (exit.kind !== 'break' && exit.kind !== 'labelledBreak') continue;
		const normalized = normalizeLoopExitTarget(cfg, exit.to);
		if (loop.sourceBlocks.has(normalized)) continue;
		if (allowed && !allowed.has(normalized)) continue;
		exits.add(normalized);
	}
	return exits.size === 1 ? [...exits][0] : null;
}

function normalizeLoopExitTarget(
	cfg: ImmutableCFG,
	target: BlockAddr,
): BlockAddr {
	const block = cfg.blocks.get(target);
	// Only an empty forwarding block can be skipped. A non-empty block is an
	// ordered loop-exit trailer and must remain owned by the surrounding Region.
	if (!block || block.terminator.kind !== 'goto' || block.body.length !== 0) {
		return target;
	}
	const successor = cfg.blocks.get(block.terminator.target);
	if (successor?.terminator.kind !== 'return') return target;
	return successor.address;
}

/**
 * Whether recursing at this block would cut a protected range in half.
 *
 * The range's own entry opens a try/catch Region, and a block outside every
 * range is ordinary. A block strictly inside one is neither: the exception
 * descriptor already owns it, and a second owner moves its Phi actions.
 */
function exceptionSplitsProtectedRange(
	entry: BlockAddr,
	descriptors: CFGDescriptors,
	ignoredHandlers = new AddressSet<BlockAddr>(),
): boolean {
	const containing = descriptors.exceptions.handlers.filter((descriptor) =>
		!ignoredHandlers.has(descriptor.handler) &&
		descriptor.protectedBlocks.has(entry)
	);
	if (containing.length === 0) return false;
	// A block can sit inside one descriptor's range while opening another's —
	// nested try/catch, or a finalizer whose range covers its own catch. Opening
	// a region there is exactly what the inner descriptor wants, so only a block
	// that opens nothing splits a range.
	return !containing.some((descriptor) =>
		descriptor.protectedEntries.has(entry)
	);
}

function exceptionStartsAt(
	entry: BlockAddr,
	descriptors: CFGDescriptors,
): boolean {
	return descriptors.exceptions.handlers.some((descriptor) =>
		descriptor.protectedEntries.has(entry)
	);
}

function exceptionStartingAtContainedBy(
	entry: BlockAddr,
	descriptors: CFGDescriptors,
	allowed: AddressSet<BlockAddr>,
): boolean {
	return descriptors.exceptions.handlers.some((descriptor) =>
		descriptor.protectedEntries.has(entry) &&
		descriptorBlocks(descriptor).isSubsetOf(allowed)
	);
}

function exceptionProtectedBlocksContainedBy(
	entry: BlockAddr,
	descriptors: CFGDescriptors,
	allowed: AddressSet<BlockAddr>,
): boolean {
	return descriptors.exceptions.handlers.some((descriptor) =>
		descriptor.protectedEntries.has(entry) &&
		descriptor.protectedBlocks.isSubsetOf(allowed)
	);
}

function descriptorBlocks(
	descriptor: CFGDescriptors['exceptions']['handlers'][number],
): AddressSet<BlockAddr> {
	const blocks = new AddressSet<BlockAddr>(descriptor.protectedBlocks);
	blocks.add(descriptor.handler);
	for (const block of descriptor.catchBody ?? []) blocks.add(block);
	for (const block of descriptor.finallyBodyBlocks ?? []) blocks.add(block);
	for (const block of descriptor.finallyCopyRoots) blocks.add(block);
	for (const copy of descriptor.finallyCopies) blocks.add(copy.copyRoot);
	return blocks;
}

function regionReferencesTerminalEntry(
	region: Region,
	entry: BlockAddr,
): boolean {
	switch (region.kind) {
		case 'terminalReference':
			return region.entry === entry;
		case 'sequence':
			return region.regions.some((child) =>
				regionReferencesTerminalEntry(child, entry)
			);
		case 'if':
			return regionReferencesTerminalEntry(region.consequent, entry) ||
				regionReferencesTerminalEntry(region.alternate, entry);
		case 'switch':
			return region.cases.some((switchCase) =>
				regionReferencesTerminalEntry(switchCase.body, entry)
			) || regionReferencesTerminalEntry(region.defaultBody, entry);
		case 'loop':
			return regionReferencesTerminalEntry(region.body, entry) ||
				region.exits.some((exit) =>
					exit.trailer != null &&
					regionReferencesTerminalEntry(exit.trailer, entry)
				);
		case 'tryCatch':
			return regionReferencesTerminalEntry(region.body, entry) ||
				regionReferencesTerminalEntry(region.handler, entry);
		case 'tryFinally':
			return regionReferencesTerminalEntry(region.body, entry) ||
				regionReferencesTerminalEntry(region.finalizer, entry);
		default:
			return false;
	}
}

function regionContainsKind(region: Region, kind: Region['kind']): boolean {
	if (region.kind === kind) return true;
	switch (region.kind) {
		case 'sequence':
			return region.regions.some((child) =>
				regionContainsKind(child, kind)
			);
		case 'if':
			return regionContainsKind(region.consequent, kind) ||
				regionContainsKind(region.alternate, kind);
		case 'switch':
			return region.cases.some((switchCase) =>
				regionContainsKind(switchCase.body, kind)
			) || regionContainsKind(region.defaultBody, kind);
		case 'loop':
			return regionContainsKind(region.body, kind);
		case 'delegateYield':
			return false;
		default:
			return false;
	}
}

function cfgWithEntry(cfg: ImmutableCFG, entry: BlockAddr): ImmutableCFG {
	return Object.create(cfg, {
		entry: { value: entry },
	}) as ImmutableCFG;
}
