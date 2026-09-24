import * as t from '@babel/types';
import type { BlockAddr } from '../../../hbc/disassembly/function.ts';
import { emitRegionToAST, emitRegionToCode } from './emit/emitRegion.ts';
import { printRegion } from './regions/printer.ts';
import type { StructuringResult } from './structure/structureRegion.ts';
import {
	blockNeedsBranchRegion,
	type LoopRegionCoverageIssue,
	loopRegionCoverageIssues,
	type Region,
	regionCoveredBlocks,
	regionDuplicatedSSABlockCounts,
} from './regions/region.ts';
import {
	type ExceptionDescriptor,
	finalizerCopyBlocks,
} from './descriptors/mod.ts';
import { AddressSet } from '../../../utils/set.ts';
import { statementFingerprint } from './descriptors/subgraphMatch.ts';
import type { CFGNormalizationSummary } from './normalization.ts';
import {
	type CFGCompatibilityEvent,
	summarizeCFGCompatibilityTelemetry,
} from './compatibility.ts';

export interface RecursiveCFGSummary {
	functionId: number;
	blockCount: number;
	normalEdgeCount: number;
	exceptionalEdgeCount: number;
	sccCount: number;
	loopCount: number;
	phiCount: number;
	switchCount: number;
	delegateYieldCount: number;
	destructuringCount: number;
	destructuringProtocolCandidateCount: number;
	exceptionHandlerCount: number;
	normalization: CFGNormalizationSummary;
	diagnostics: Array<{ kind: string; message: string }>;
	/**
	 * Original SSA/basic-block addresses materialized more than once by the
	 * current selected candidate, keyed as hexadecimal addresses. Values are
	 * total ownership claims, and are therefore always greater than one.
	 *
	 * Blocks owned by a recognized finalizer are omitted: Hermes duplicates
	 * finalizer bodies at compile time, so those copies are not reducer defects.
	 */
	duplicatedSSABlockCounts: Record<string, number>;
	loopCoverageIssues: LoopRegionCoverageIssue[];
	unstructuredBranches: RecursiveBranchShapeSummary[];
	phiEdges: RecursivePhiEdgeSummary[];
	exceptionHandlers: RecursiveExceptionHandlerSummary[];
	finalizerEdgeActions: RecursiveFinalizerEdgeActionSummary[];
	unhandledExceptionHandlers: BlockAddr[];
	/**
	 * Reachable CFG blocks no Region leaf owns, excluding the finalizer copies a
	 * represented `finally` emits instead.
	 *
	 * A Region that drops blocks still emits and still parses, so no other check
	 * sees it. Measuring it keeps the selection honest about how much of the
	 * function the recursive path actually represents.
	 */
	uncoveredBlocks: BlockAddr[];
	/**
	 * Labels the bounded control forest put in the emitted Region.
	 *
	 * `tryStructureBoundedControlForest` is a last resort: it owns every block
	 * and edge exactly once by threading non-local forward edges through labelled
	 * breaks. The linearized-acyclic miss heuristic is for ordinary recursive
	 * Regions that expanded a branch ladder without exact edge ownership; a
	 * labelled control forest is already the exact ownership fallback, so those
	 * labels also prove the heuristic should not reject the candidate.
	 */
	controlForestLabels?: number;
	emittedStatementCount?: number;
	emissionStatus: 'emitted' | 'failed';
	emittedProgram?: t.Program;
	emittedCode?: string;
	emitDiagnostics: string[];
	regionKind?: string;
	regionText?: string;
	misses: string[];
	/** Exact output of the initial Region emitter, never replaced by fallback. */
	rawEmission: RecursiveCFGEmission;
	/** Region analysis performed after the ordinary reducers have converged. */
	postReductionAnalysis?: RecursiveCFGPostReductionAnalysis;
	/** Single-block AST produced by the ordinary reducers. */
	reducedFallbackEmission?: RecursiveCFGEmission;
	/** The candidate selected for materialization, if any. */
	selectedEmission?: RecursiveCFGEmission;
	selection: RecursiveCFGSelection;
	/** Present only when the opt-in CFG migration audit is enabled. */
	migrationAudit?: RecursiveCFGMigrationAudit;
	compatibilityPaths: RecursiveCFGCompatibilityEvent[];
}

export interface RecursiveCFGMigrationAudit {
	mode: 'observe' | 'strict';
	normalization: CFGNormalizationSummary;
	classification: {
		bytecodeVersion: number;
		generator: 'none' | 'native' | 'lowered' | 'other';
		async: boolean;
		exceptionHandlerCount: number;
		cfgSize: 'small' | 'medium' | 'large';
		branchShapes: RecursiveBranchShapeSummary[];
	};
	initial: RecursiveCFGMigrationState;
	passTrace: RecursiveCFGMigrationPassTrace[];
	firstHealingPass: string | null;
	guardedPhiRetry: RecursiveCFGMigrationRetry;
	legacyPhiRescue: RecursiveCFGMigrationLegacyRescue;
	destructuringLegacyRescue: RecursiveCFGMigrationLegacyRescue;
	compatibilityPaths: RecursiveCFGCompatibilityEvent[];
	candidateRejections: RecursiveCFGMigrationCandidateRejection[];
	/** Deduplicated binding/destructuring cleanup outcomes and refusal reasons. */
	bindingCleanupTelemetry: Record<string, number>;
	/** Per-function cleanup and binding-placement cost. */
	bindingPerformance: RecursiveCFGBindingPerformanceAudit;
	/** Actual unified binding-placement work performed on this function. */
	bindingPlacement?: RecursiveCFGBindingPlacementAudit;
	final?: RecursiveCFGMigrationFinalState;
}

export interface RecursiveCFGBindingPlacementAudit {
	/** Bindings that would move, by reason. A binding may have several. */
	reasons: Record<string, number>;
	placed: number;
	localized: number;
	/**
	 * References with no declaration and no reaching write.
	 *
	 * These are the population the unbound-register gate rejects on, and the
	 * one thing placement must never repair: a declaration invented here turns
	 * a rejected candidate into wrong output.
	 */
	unresolved: number;
}

export interface RecursiveCFGBindingPerformanceAudit {
	cleanupCalls: number;
	cleanupIterations: number;
	cleanupMilliseconds: number;
	placementChecks: number;
	placementRewrites: number;
	placementMilliseconds: number;
}

export interface RecursiveCFGMigrationState {
	blockCount: number;
	/** Reachable blocks no Region leaf owns; see `RecursiveCFGSummary`. */
	uncoveredBlockCount: number;
	unresolvedPhiCount: number;
	duplicatedSSABlockCounts: Record<string, number>;
	misses: string[];
	loopCoverageIssues: LoopRegionCoverageIssue[];
	emitDiagnostics: string[];
	emissionStatus: RecursiveCFGEmission['status'];
	programAvailable: boolean;
}

export interface RecursiveCFGMigrationPassTrace {
	stage: string;
	pass: string;
	result: 'changed' | 'restart';
	blocksBefore: number;
	blocksAfter: number;
	phisBefore: number;
	phisAfter: number;
	/** Populated only until the first complete Region is found. */
	regionMissesAfter?: string[];
	regionEmitDiagnosticsAfter?: string[];
	healedMisses?: string[];
	healedEmitDiagnostics?: string[];
	regressedMisses?: string[];
	regressedEmitDiagnostics?: string[];
}

export interface RecursiveCFGMigrationRetry {
	eligible: boolean;
	attempted: boolean;
	adopted: boolean;
	blocksBefore: number | null;
	blocksAfter: number | null;
	phisBefore: number | null;
	phisAfter: number | null;
}

export interface RecursiveCFGMigrationLegacyRescue {
	eligible: boolean;
	attempted: boolean;
	shadowOnly: boolean;
	wouldImprove: boolean;
	adopted: boolean;
	blocksBefore: number | null;
	blocksAfter: number | null;
	phisBefore: number | null;
	phisAfter: number | null;
	error: string | null;
}

export type RecursiveCFGCompatibilityPath =
	| CFGCompatibilityEvent['path']
	| 'short-circuit-rollback'
	| 'destructuring-legacy-rescue'
	| 'guarded-phi-retry'
	| 'natural-loop-rollback'
	| 'wide-leading-phi-rollback'
	| 'legacy-phi-rescue';

export interface RecursiveCFGCompatibilityEvent {
	path: RecursiveCFGCompatibilityPath;
	phase: 'raw-region' | 'reduction' | 'post-reduction-region';
	attempts: number;
	selections: number;
	entries: BlockAddr[];
	reasons: string[];
}

export interface RecursiveCFGMigrationCandidateRejection {
	candidate: RecursiveCFGEmission['source'];
	reasons: string[];
}

export interface RecursiveCFGMigrationFinalState
	extends RecursiveCFGMigrationState {
	selectedCandidate: RecursiveCFGSelection['candidate'];
	materialized: boolean;
	singleBlockReferenceAvailable: boolean;
}

export interface RecursiveCFGEmission {
	source: 'raw-region' | 'post-reduction-region' | 'reduced-fallback';
	statementCount: number;
	status: 'emitted' | 'failed';
	program?: t.Program;
	code?: string;
	diagnostics: string[];
}

export interface RecursiveCFGPostReductionAnalysis {
	normalization: CFGNormalizationSummary;
	diagnostics: Array<{ kind: string; message: string }>;
	duplicatedSSABlockCounts: Record<string, number>;
	loopCoverageIssues: LoopRegionCoverageIssue[];
	uncoveredBlocks: BlockAddr[];
	regionKind?: string;
	regionText?: string;
	misses: string[];
	rawEmission: RecursiveCFGEmission;
	compatibilityPaths: RecursiveCFGCompatibilityEvent[];
}

export interface RecursiveCFGSummaryOptions {
	/** Generate and retain source text for emitted Region candidates. */
	generateCode?: boolean;
}

export interface RecursiveCFGSelection {
	candidate: RecursiveCFGEmission['source'] | 'none';
	reason: string;
	materialized: boolean;
}

export interface RecursivePhiEdgeSummary {
	from: BlockAddr;
	to: BlockAddr;
	kind: string;
	assignments: Array<{ target: string; value: string }>;
}

export type RecursiveBranchShape =
	| 'shared-continuation'
	| 'terminal-arm'
	| 'shared-terminal'
	| 'phi-join'
	| 'empty-arm'
	| 'duplicate-edge'
	| 'protected-region-boundary'
	| 'irreducible-subgraph'
	| 'unclassified';

export interface RecursiveBranchShapeSummary {
	block: BlockAddr;
	shapes: RecursiveBranchShape[];
}

export interface RecursiveExceptionHandlerSummary {
	handler: BlockAddr;
	kind: 'catch' | 'finally';
	protectedEntries: BlockAddr[];
	protectedBlocks: BlockAddr[];
	catchBody: BlockAddr[] | null;
	finallyCopyRoots: BlockAddr[];
	finallyBodyBlocks: BlockAddr[] | null;
	finallyCopies: RecursiveFinallyCopySummary[];
	finallyCopySuffixes: RecursiveFinallyCopySuffixSummary[];
	enclosingFinallyCopyRoots: Array<{
		owner: BlockAddr;
		copyRoot: BlockAddr;
		tailRoot: BlockAddr;
	}>;
}

export interface RecursiveFinalizerEdgeActionSummary {
	handler: BlockAddr;
	from: BlockAddr;
	to: BlockAddr;
	edgeKind: 'normal' | 'exceptional';
	copyRoot: BlockAddr;
	kind:
		| 'canonical'
		| 'normal-copy'
		| 'catch-copy'
		| 'abrupt-copy'
		| 'enclosing-copy';
	completion: 'normal' | 'return' | 'throw' | 'break-or-continue';
	depth: number;
}

export interface RecursiveStatementRangeSummary {
	block: BlockAddr;
	start: number;
	end: number;
}

export interface RecursiveFinallyCopySummary {
	canonical: BlockAddr;
	copyRoot: BlockAddr;
	next: BlockAddr | null;
	kind: 'normalExit' | 'abruptExit' | 'catchTrailer';
	copyBlocks?: BlockAddr[];
	skipRanges?: RecursiveStatementRangeSummary[];
}

export interface RecursiveFinallyCopySuffixSummary {
	canonical: BlockAddr;
	copyRoot: BlockAddr;
	ownerBlock: BlockAddr;
	next: BlockAddr | null;
	kind: 'tryTrailer' | 'catchTrailer' | 'abruptExitTrailer' | 'canonical';
	skipRanges?: RecursiveStatementRangeSummary[];
}

/**
 * Labels in `regionText` that the bounded control forest produced.
 *
 * Counted by prefix rather than detected in the forest: its four entry points
 * funnel into one builder, and the prefix is what survives into the Region.
 */
function countControlForestLabels(regionText: string | undefined): number {
	if (!regionText) return 0;
	return regionText.match(
		/label=(?:cfg_cont_|cfg_forest_|scope_|loop\d+_body_)/g,
	)?.length ?? 0;
}

function regionLooksLinearizedAcyclicCFG(
	result: StructuringResult,
	regionText: string | undefined,
): boolean {
	return regionTextLooksLinearizedAcyclicCFG(regionText, {
		blockCount: result.cfg.blocks.size,
		loopCount: result.analyses.naturalLoops.loops.length,
		sccCount: result.analyses.sccs.components.length,
	});
}

export function regionTextLooksLinearizedAcyclicCFG(
	regionText: string | undefined,
	shape: { blockCount: number; sccCount: number; loopCount: number },
): boolean {
	if (!regionText) return false;
	if (countControlForestLabels(regionText) > 0) return false;
	if (shape.loopCount !== 0) return false;
	if (shape.sccCount !== shape.blockCount) return false;

	const ifCount = countMatches(
		regionText,
		/\bif join=0x[0-9a-f]+ header=0x[0-9a-f]+(?:\s|$)/g,
	);
	if (ifCount < 8) return false;

	const basicLeafCount = countMatches(regionText, /\bbasic blocks=0x/g);
	const emptyArmCount = countMatches(
		regionText,
		/\b(?:then|else) sequence blocks=$/gm,
	);
	if (emptyArmCount < 8) return false;

	// The tail re-listed at level after level is not evidence of anything: a
	// sequence's block list is the union of its descendants, so any deep nest
	// names a long suffix at every level. Linearization means the same block
	// was placed under more than one leaf -- that is what makes the Region
	// larger than the graph, and it is the only thing worth rejecting.
	const clonedLeafBlocks = clonedLeafBlockCount(regionText);
	const longSuffixCount = countMatches(
		regionText,
		/^ +sequence blocks=0x[0-9a-f]+(?:,0x[0-9a-f]+){31,}$/gm,
	);
	if (
		clonedLeafBlocks > 0 && shape.blockCount >= 64 &&
		basicLeafCount >= 16 && longSuffixCount >= 8
	) {
		return true;
	}

	// More branch nodes than the graph has blocks: arms were cloned under
	// several parents, so the Region is larger than the CFG it represents.
	//
	// Size and empty arms alone prove nothing. A folded short-circuit chain
	// and a conditional-Phi arm each leave exactly one `if` node with one
	// empty arm — their operands live in the folded predicate, not in a
	// block — so any guard-heavy acyclic function crosses those thresholds
	// while its Region is precisely the nest the source had.
	return ifCount > shape.blockCount;
}

function countMatches(text: string, pattern: RegExp): number {
	return text.match(pattern)?.length ?? 0;
}

/**
 * Blocks a `basic` leaf claims that another leaf claims too.
 *
 * One block emitted from two leaves is a copy, whichever shape produced it:
 * that is the cloning an ordinary nest never does, however deep it runs.
 */
function clonedLeafBlockCount(regionText: string): number {
	const claims = new Map<string, number>();
	for (
		const match of regionText.matchAll(
			/\bbasic blocks=((?:0x[0-9a-f]+,?)+)/g,
		)
	) {
		for (const block of match[1]!.split(',')) {
			if (block === '') continue;
			claims.set(block, (claims.get(block) ?? 0) + 1);
		}
	}
	let cloned = 0;
	for (const count of claims.values()) if (count > 1) cloned++;
	return cloned;
}

/**
 * Raw Hermes switch calls are CFG terminators, not executable JavaScript.
 * Once their successor table has been consumed into an AST body there is no
 * way to recover the case targets from the call's arguments alone, so no
 * emission containing one can be considered complete.
 */
export function containsRawSwitchIntrinsic(node: t.Node): boolean {
	let found = false;
	t.traverseFast(node, (candidate) => {
		if (
			t.isCallExpression(candidate) &&
			t.isV8IntrinsicIdentifier(candidate.callee) &&
			(candidate.callee.name === 'UIntSwitchImm' ||
				candidate.callee.name === 'StringSwitchImm')
		) {
			found = true;
			return t.traverseFast.skip;
		}
	});
	return found;
}

/** A Phi call is likewise CFG metadata and must be lowered onto its edges. */
export function containsRawPhiIntrinsic(node: t.Node): boolean {
	let found = false;
	t.traverseFast(node, (candidate) => {
		if (
			t.isCallExpression(candidate) &&
			t.isV8IntrinsicIdentifier(candidate.callee, { name: 'Phi' })
		) {
			found = true;
			return t.traverseFast.skip;
		}
	});
	return found;
}

/**
 * The `for...in` protocol is CFG machinery too: `%GetPNameList` sets up the
 * property list and `%GetNextPName` advances it. Emitting either means the
 * loop was not recovered as `for (k in o)`, so the candidate is incomplete
 * however well-formed the rest of it looks.
 */
export function containsRawForInIntrinsic(node: t.Node): boolean {
	let found = false;
	t.traverseFast(node, (candidate) => {
		if (
			t.isCallExpression(candidate) &&
			t.isV8IntrinsicIdentifier(candidate.callee) &&
			(candidate.callee.name === 'GetPNameList' ||
				candidate.callee.name === 'GetNextPName')
		) {
			found = true;
			return t.traverseFast.skip;
		}
	});
	return found;
}

function compactRecursiveCFGEmission(
	emission: RecursiveCFGEmission | undefined,
): RecursiveCFGEmission | undefined {
	if (!emission) return undefined;
	const { program: _program, code: _code, ...compact } = emission;
	return compact;
}

export function compactRecursiveCFGSummary(
	summary: RecursiveCFGSummary | undefined,
): RecursiveCFGSummary | undefined {
	if (!summary) return undefined;
	const {
		emittedProgram: _emittedProgram,
		emittedCode: _emittedCode,
		...compact
	} = summary;
	return {
		...compact,
		rawEmission: compactRecursiveCFGEmission(summary.rawEmission)!,
		postReductionAnalysis: summary.postReductionAnalysis == null
			? undefined
			: {
				...summary.postReductionAnalysis,
				rawEmission: compactRecursiveCFGEmission(
					summary.postReductionAnalysis.rawEmission,
				)!,
			},
		reducedFallbackEmission: compactRecursiveCFGEmission(
			summary.reducedFallbackEmission,
		),
		selectedEmission: compactRecursiveCFGEmission(summary.selectedEmission),
	};
}

/**
 * Reachable blocks the Region tree never claims.
 *
 * Unreachable blocks are excluded because nothing should emit them, and so are
 * the finalizer copies: a represented `finally` emits their statements once, so
 * the copy itself is owned while emitting nothing of its own.
 */
function uncoveredRegionBlocks(result: StructuringResult): BlockAddr[] {
	if (!result.region) return [];
	const covered = regionCoveredBlocks(result.region);
	const suppressed = finalizerCopyBlocks(
		result.descriptors.exceptions.handlers,
	);
	const reachable = result.analyses.reachability.allReachable;
	const uncovered: BlockAddr[] = [];
	for (const block of result.cfg.blocks.keys()) {
		if (!reachable.has(block)) continue;
		if (covered.has(block) || suppressed.has(block)) continue;
		uncovered.push(block);
	}
	return uncovered.toSorted((left, right) => left - right);
}

/**
 * Original SSA blocks represented by compiler-owned finalizer machinery.
 *
 * Descriptor addresses can name either an original SSA block or a live block
 * produced by compatibility reduction. Include the live block's provenance in
 * the latter case so the diagnostic remains stable across reduction stages.
 */
function finalizerOwnedSSASources(
	result: StructuringResult,
): AddressSet<BlockAddr> {
	const handlers = result.descriptors.exceptions.handlers;
	const ownedBlocks = finalizerCopyBlocks(handlers);
	for (const descriptor of handlers) {
		if (descriptor.kind !== 'finally') continue;
		ownedBlocks.add(descriptor.handler);
		if (descriptor.canonicalFinallyAddress != null) {
			ownedBlocks.add(descriptor.canonicalFinallyAddress);
		}
		for (
			const block of descriptor.finallyBodyBlocks ??
				descriptor.boundedFinallyBodyBlocks ??
				[]
		) ownedBlocks.add(block);
		for (const copy of descriptor.enclosingFinallyCopyRoots) {
			ownedBlocks.add(copy.copyRoot);
			ownedBlocks.add(copy.tailRoot);
		}
	}
	for (
		const copies of result.descriptors.exceptions.finalizerCopyModel
			.embeddedEnclosingCopies.values()
	) {
		for (const copy of copies) {
			ownedBlocks.add(copy.copyRoot);
			ownedBlocks.add(copy.tailRoot);
		}
	}

	const sources = new AddressSet<BlockAddr>();
	for (const address of ownedBlocks) {
		sources.add(address);
		for (
			const source of result.cfg.blocks.get(address)?.sourceAddresses ??
				[]
		) sources.add(source);
	}
	return sources;
}

function duplicatedSSABlockCounts(
	result: StructuringResult,
): Record<string, number> {
	if (!result.region) return {};
	const ignored = finalizerOwnedSSASources(result);
	const counts = regionDuplicatedSSABlockCounts(
		result.region,
		result.cfg,
		ignored,
	);
	const summary: Record<string, number> = {};
	for (const [address, count] of counts) {
		summary[`0x${address.toString(16)}`] = count;
	}
	return summary;
}

export function summarizeRecursiveCFG(
	functionId: number,
	result: StructuringResult,
	options: RecursiveCFGSummaryOptions = {},
): RecursiveCFGSummary {
	const regionText = result.region ? printRegion(result.region) : undefined;
	const generateCode = options.generateCode !== false;
	const emittedRegion = result.region;
	const emitted = emittedRegion
		? generateCode
			? emitRegionToCode(emittedRegion, result.cfg, result.descriptors)
			: emitRegionToAST(emittedRegion, result.cfg, result.descriptors)
		: undefined;
	const emittedCode: string | undefined =
		emitted && 'code' in emitted && typeof emitted.code === 'string'
			? emitted.code
			: undefined;
	const misses = new Set<string>();
	const loopCoverageIssues = result.region
		? loopRegionCoverageIssues(result.region)
		: [];
	if (!result.region) {
		misses.add('no-region');
	} else {
		collectRegionMisses(regionText ?? '', misses);
		if (regionContainsUnstructuredBranch(result.region, result)) {
			misses.add('basic-branch-not-structured');
		}
		if (unhandledExceptionHandlers(result.region, result).length > 0) {
			misses.add('exception-handler-not-structured');
		}
		if (hasUnmodelledFinalizerTerminal(result.region, result)) {
			misses.add('finalizer-terminal-not-structured');
		}
		if (loopCoverageIssues.length > 0) {
			misses.add('loops-not-structured');
		}
	}
	if (
		result.analyses.naturalLoops.loops.length > 0 &&
		!regionText?.includes('loop id=') &&
		!regionText?.includes('delegateYield ')
	) {
		misses.add('loops-not-structured');
	}
	if (
		result.region &&
		hasUnrepresentedSwitchDescriptor(result.region, result)
	) {
		misses.add('switches-not-structured');
	}
	if (emitted?.program && containsRawSwitchIntrinsic(emitted.program)) {
		misses.add('switches-not-structured');
	}
	if (emitted?.program && containsRawPhiIntrinsic(emitted.program)) {
		misses.add('phis-not-lowered');
	}
	if (emitted?.program && containsRawForInIntrinsic(emitted.program)) {
		misses.add('for-in-not-structured');
	}
	if (emitted?.program && hasUnsyntacticLoopControl(emitted.program)) {
		misses.add('loop-control-not-structured');
	}
	if (regionLooksLinearizedAcyclicCFG(result, regionText)) {
		misses.add('linearized-acyclic-region');
	}
	const uncoveredBlocks = uncoveredRegionBlocks(result);
	const duplicatedSSABlocks = duplicatedSSABlockCounts(result);
	const controlForestLabels = countControlForestLabels(regionText);
	const phiEdges = summarizePhiEdges(result);
	for (const diagnostic of result.diagnostics.items) {
		if (diagnostic.kind === 'unreachableBlock') continue;
		misses.add(`diagnostic:${diagnostic.kind}`);
	}

	const emissionStatus = emitted == null ? 'failed' : 'emitted';
	const rawEmission: RecursiveCFGEmission = {
		source: 'raw-region',
		statementCount: emitted?.statements.length ?? 0,
		status: emissionStatus,
		program: emitted?.program == null
			? undefined
			: t.cloneNode(emitted.program, true),
		code: emittedCode,
		diagnostics: emitted?.diagnostics ?? [],
	};
	const unstructuredBranches = summarizeUnstructuredBranches(result);
	const compatibilityPaths = summarizeCFGCompatibilityTelemetry(
		result.descriptors.compatibility,
	).map((event) => ({
		...event,
		phase: 'raw-region' as const,
	}));
	return {
		functionId,
		blockCount: result.cfg.blocks.size,
		controlForestLabels,
		normalEdgeCount: result.cfg.normalEdges().length,
		exceptionalEdgeCount: result.cfg.exceptionalEdges().length,
		sccCount: result.analyses.sccs.components.length,
		loopCount: result.analyses.naturalLoops.loops.length,
		phiCount: result.descriptors.phis.phis.length,
		switchCount: result.descriptors.switches.switches.length,
		delegateYieldCount: result.descriptors.delegateYields.delegates.length,
		destructuringCount: result.descriptors.destructuring.descriptors.length,
		destructuringProtocolCandidateCount:
			result.descriptors.destructuring.protocolCandidates.length,
		exceptionHandlerCount: result.descriptors.exceptions.handlers.length,
		normalization: result.normalization,
		diagnostics: [
			...result.diagnostics.items.map((diagnostic) => ({
				kind: diagnostic.kind,
				message: diagnostic.message,
			})),
			...duplicateOwnershipDiagnostics(duplicatedSSABlocks),
		],
		duplicatedSSABlockCounts: duplicatedSSABlocks,
		loopCoverageIssues,
		unstructuredBranches,
		phiEdges,
		exceptionHandlers: result.descriptors.exceptions.handlers.map((
			handler,
		) => ({
			handler: handler.handler,
			kind: handler.kind,
			protectedEntries: [...handler.protectedEntries].toSorted((
				left,
				right,
			) => left - right),
			protectedBlocks: [...handler.protectedBlocks].toSorted((
				left,
				right,
			) => left - right),
			catchBody: handler.catchBody == null
				? null
				: [...handler.catchBody].toSorted((left, right) =>
					left - right
				),
			finallyCopyRoots: [...handler.finallyCopyRoots].toSorted((
				left,
				right,
			) => left - right),
			finallyBodyBlocks: handler.finallyBodyBlocks == null
				? null
				: [...handler.finallyBodyBlocks],
			finallyCopies: handler.finallyCopies.map((copy) => ({
				canonical: copy.canonical,
				copyRoot: copy.copyRoot,
				next: copy.next,
				kind: copy.kind,
				copyBlocks: copy.copyBlocks == null
					? undefined
					: [...copy.copyBlocks],
				skipRanges: copy.skipRanges?.map((range) => ({ ...range })),
			})).toSorted((left, right) =>
				left.copyRoot - right.copyRoot ||
				left.kind.localeCompare(right.kind)
			),
			finallyCopySuffixes: handler.finallyCopySuffixes.map((suffix) => ({
				canonical: suffix.canonical,
				copyRoot: suffix.copyRoot,
				ownerBlock: suffix.ownerBlock,
				next: suffix.next,
				kind: suffix.kind,
				skipRanges: suffix.skipRanges?.map((range) => ({
					...range,
				})),
			})).toSorted((left, right) =>
				left.copyRoot - right.copyRoot ||
				left.kind.localeCompare(right.kind)
			),
			enclosingFinallyCopyRoots: handler.enclosingFinallyCopyRoots.map((
				copy,
			) => ({
				owner: copy.owner,
				copyRoot: copy.copyRoot,
				tailRoot: copy.tailRoot,
			})).toSorted((left, right) =>
				left.owner - right.owner || left.copyRoot - right.copyRoot
			),
		})),
		finalizerEdgeActions: result.descriptors.exceptions.finalizerEdgeActions
			.map((action) => ({
				handler: action.handler,
				from: action.edge.from,
				to: action.edge.to,
				edgeKind: action.edge.kind,
				copyRoot: action.copyRoot,
				kind: action.kind,
				completion: action.completion,
				depth: action.depth,
			})),
		uncoveredBlocks,
		unhandledExceptionHandlers: result.region == null
			? result.descriptors.exceptions.handlers.map((handler) =>
				handler.handler
			)
			: unhandledExceptionHandlers(result.region, result),
		emittedStatementCount: emitted?.statements.length,
		emissionStatus,
		emittedProgram: emitted?.program,
		emittedCode,
		emitDiagnostics: emitted?.diagnostics ?? [],
		regionKind: result.region?.kind,
		regionText,
		misses: [...misses].toSorted(),
		rawEmission,
		compatibilityPaths,
		selection: {
			candidate: 'none',
			reason: 'materialization has not been evaluated',
			materialized: false,
		},
	};
}

export function effectiveRecursiveCFGEmission(
	summary: RecursiveCFGSummary,
): RecursiveCFGEmission {
	return summary.selectedEmission ?? summary.rawEmission;
}

/**
 * A `break` or `continue` the emitted program cannot execute: no enclosing
 * loop, switch, or matching label.
 *
 * The Region model can be internally consistent and still emit this — a loop
 * whose statement is dropped keeps the transfers its body owns — and the
 * result is not even parseable JavaScript, so it is a miss like any other
 * unstructured control.
 */
function hasUnsyntacticLoopControl(program: t.Program): boolean {
	let found = false;
	const visit = (
		node: t.Node,
		loops: number,
		switches: number,
		labels: ReadonlySet<string>,
	) => {
		if (found) return;
		if (t.isBreakStatement(node)) {
			if (
				node.label
					? !labels.has(node.label.name)
					: loops + switches === 0
			) found = true;
			return;
		}
		if (t.isContinueStatement(node)) {
			if (node.label ? !labels.has(node.label.name) : loops === 0) {
				found = true;
			}
			return;
		}
		// A nested function body starts its own control context.
		if (t.isFunction(node) || t.isClass(node)) return;
		// Re-declaring a label inside its own scope is not valid JavaScript, and
		// it means two Regions claimed the same transfer name -- the breaks
		// below cannot say which one they leave.
		if (t.isLabeledStatement(node) && labels.has(node.label.name)) {
			found = true;
			return;
		}
		const nextLabels = t.isLabeledStatement(node)
			? new Set([...labels, node.label.name])
			: labels;
		const nextLoops = t.isLoop(node) ? loops + 1 : loops;
		const nextSwitches = t.isSwitchStatement(node)
			? switches + 1
			: switches;
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			for (const child of Array.isArray(value) ? value : [value]) {
				if (
					child && typeof child === 'object' &&
					typeof (child as t.Node).type === 'string'
				) visit(child as t.Node, nextLoops, nextSwitches, nextLabels);
			}
		}
	};
	visit(program, 0, 0, new Set<string>());
	return found;
}

function hasUnmodelledFinalizerTerminal(
	region: Region,
	result: StructuringResult,
): boolean {
	const representedRoots = new Set<number>();
	collectDeferredFinalizerTerminalRoots(region, representedRoots);
	return result.descriptors.exceptions.handlers.some((descriptor) => {
		if (descriptor.kind !== 'finally') return false;
		const modelledRoots = new Set(
			descriptor.finallyCopySuffixes.map((suffix) => suffix.copyRoot),
		);
		return descriptor.finallyCopies.some((copy) => {
			if (copy.kind === 'normalExit' || copy.next != null) return false;
			if (copy.copyRoot === descriptor.handler) return false;
			if (modelledRoots.has(copy.copyRoot)) return false;
			const terminator = result.cfg.blocks.get(copy.copyRoot)?.terminator;
			return (terminator?.kind === 'return' ||
				terminator?.kind === 'throw') &&
				!representedRoots.has(copy.copyRoot);
		});
	});
}

function collectDeferredFinalizerTerminalRoots(
	region: Region,
	roots: Set<number>,
) {
	for (const exit of region.deferredExits ?? []) {
		if (
			!exit.actions.some((action) =>
				action.kind === 'return' || action.kind === 'throw'
			)
		) continue;
		for (const action of exit.actions) {
			if (action.kind === 'finally') roots.add(action.action.copyRoot);
		}
	}
	switch (region.kind) {
		case 'sequence':
			for (const child of region.regions) {
				collectDeferredFinalizerTerminalRoots(child, roots);
			}
			break;
		case 'if':
			collectDeferredFinalizerTerminalRoots(region.consequent, roots);
			collectDeferredFinalizerTerminalRoots(region.alternate, roots);
			break;
		case 'switch':
			for (const switchCase of region.cases) {
				collectDeferredFinalizerTerminalRoots(switchCase.body, roots);
			}
			collectDeferredFinalizerTerminalRoots(region.defaultBody, roots);
			break;
		case 'tryCatch':
			collectDeferredFinalizerTerminalRoots(region.body, roots);
			collectDeferredFinalizerTerminalRoots(region.handler, roots);
			break;
		case 'tryFinally':
			collectDeferredFinalizerTerminalRoots(region.body, roots);
			collectDeferredFinalizerTerminalRoots(region.finalizer, roots);
			break;
		case 'loop':
			collectDeferredFinalizerTerminalRoots(region.body, roots);
			break;
	}
}

function unhandledExceptionHandlers(
	region: Region,
	result: StructuringResult,
): BlockAddr[] {
	const represented = new Set<number>();
	collectRegionHandlerAddresses(region, represented);
	const representedBasicBlocks = new Set<number>();
	collectRegionBasicBlocks(region, representedBasicBlocks);
	const copyHandlers = result.descriptors.exceptions.finalizerCopyModel
		.copyDescriptorHandlers;
	return result.descriptors.exceptions.handlers.filter((descriptor) =>
		!copyHandlers.has(descriptor.handler) &&
		!represented.has(descriptor.handler) &&
		!regionSubsumesEquivalentCatchAlias(
			descriptor.handler,
			represented,
			result,
		) &&
		!regionSubsumesEquivalentHandler(descriptor, represented, result) &&
		!regionSubsumesEquivalentBasicBlock(
			descriptor,
			representedBasicBlocks,
			result,
		) &&
		!destructuringProtocolSubsumesIteratorFinalizer(descriptor, result) &&
		!regionSubsumesIteratorFinalizer(region, descriptor, result)
	).map((descriptor) => descriptor.handler);
}

function regionSubsumesEquivalentCatchAlias(
	handler: BlockAddr,
	represented: ReadonlySet<number>,
	result: StructuringResult,
): boolean {
	const aliases = result.descriptors.exceptions
		.equivalentCatchHandlerAliases;
	const visited = new Set<BlockAddr>();
	let canonical = aliases.get(handler);
	while (canonical != null && !visited.has(canonical)) {
		if (represented.has(canonical)) return true;
		visited.add(canonical);
		canonical = aliases.get(canonical);
	}
	return false;
}

function regionSubsumesEquivalentBasicBlock(
	descriptor: ExceptionDescriptor,
	basicBlocks: ReadonlySet<number>,
	result: StructuringResult,
): boolean {
	const fingerprint = exceptionHandlerFingerprint(descriptor, result);
	if (fingerprint == null) return false;
	return [...basicBlocks].some((address) =>
		blockFingerprint(address, result) === fingerprint
	);
}

function regionSubsumesEquivalentHandler(
	descriptor: ExceptionDescriptor,
	represented: ReadonlySet<number>,
	result: StructuringResult,
): boolean {
	const fingerprint = exceptionHandlerFingerprint(descriptor, result);
	if (fingerprint == null) return false;
	return result.descriptors.exceptions.handlers.some((candidate) =>
		candidate.kind === descriptor.kind &&
		represented.has(candidate.handler) &&
		exceptionHandlerFingerprint(candidate, result) === fingerprint
	);
}

function exceptionHandlerFingerprint(
	descriptor: ExceptionDescriptor,
	result: StructuringResult,
): string | null {
	const blocks = descriptor.kind === 'finally'
		? descriptor.boundedFinallyBodyBlocks ?? [descriptor.handler]
		: [descriptor.handler];
	const fingerprints: string[] = [];
	for (const address of blocks) {
		for (const statement of result.cfg.blocks.get(address)?.body ?? []) {
			if (isCatchIntrinsicDeclaration(statement)) continue;
			if (isGeneratedGlobalBinding(statement)) continue;
			if (t.isThrowStatement(statement)) continue;
			fingerprints.push(statementFingerprint(statement));
		}
	}
	return fingerprints.length === 0 ? null : fingerprints.join('|');
}

function blockFingerprint(
	address: number,
	result: StructuringResult,
): string | null {
	const fingerprints = (result.cfg.blocks.get(address)?.body ?? [])
		.filter((statement) =>
			!isCatchIntrinsicDeclaration(statement) &&
			!isGeneratedGlobalBinding(statement) &&
			!t.isThrowStatement(statement)
		)
		.map(statementFingerprint);
	return fingerprints.length === 0 ? null : fingerprints.join('|');
}

function isGeneratedGlobalBinding(statement: t.Statement): boolean {
	return t.isVariableDeclaration(statement) &&
		statement.declarations.every((declaration) =>
			t.isIdentifier(declaration.id) &&
			t.isIdentifier(declaration.init, { name: 'global' })
		);
}

function isCatchIntrinsicDeclaration(statement: t.Statement): boolean {
	if (!t.isVariableDeclaration(statement)) return false;
	return statement.declarations.some((declaration) =>
		t.isCallExpression(declaration.init) &&
		t.isV8IntrinsicIdentifier(declaration.init.callee, { name: 'Catch' })
	);
}

/** Whether a recovered `yield*` machine owns every block of `descriptor`. */
function delegateMachineOwnsRange(
	region: Region,
	descriptor: ExceptionDescriptor,
): boolean {
	let owned = false;
	visitHighLevelIteratorRegions(region, (candidate) => {
		if (candidate.kind !== 'delegateYield') return;
		if (!candidate.sourceBlocks.has(descriptor.handler)) return;
		for (const block of descriptor.protectedBlocks) {
			if (!candidate.sourceBlocks.has(block)) return;
		}
		owned = true;
	});
	return owned;
}

/**
 * Whether a straight-line array-destructuring protocol owns an abrupt
 * IteratorClose handler.
 *
 * Hermes emits IteratorBegin and the first IteratorNext in one block for a
 * fixed-arity destructuring operation. Its exceptional ranges can be split by
 * later branches, so no single Region necessarily wraps the entire cleanup
 * handler. Matching the exact IteratorNext state closed by the handler proves
 * that native destructuring represents that finalizer instead.
 */
function destructuringProtocolSubsumesIteratorFinalizer(
	descriptor: ExceptionDescriptor,
	result: StructuringResult,
): boolean {
	if (descriptor.kind !== 'finally') return false;
	const closeStates = new Set<string>();
	for (
		const address of descriptor.finallyBodyBlocks ??
			[descriptor.handler]
	) {
		for (const statement of result.cfg.blocks.get(address)?.body ?? []) {
			t.traverseFast(statement, (node) => {
				if (
					!t.isCallExpression(node) ||
					!t.isV8IntrinsicIdentifier(node.callee, {
						name: 'IteratorClose',
					}) ||
					!t.isIdentifier(node.arguments[0])
				) return;
				closeStates.add(node.arguments[0].name);
			});
		}
	}
	if (closeStates.size === 0) return false;
	for (
		const candidate of result.descriptors.destructuring.protocolCandidates
	) {
		if (candidate.kind !== 'iterator') continue;
		if (
			![...descriptor.protectedEntries].every((entry) =>
				result.analyses.dominators.dominates(candidate.entry, entry)
			)
		) continue;
		const block = result.cfg.blocks.get(candidate.entry);
		if (!block) continue;
		let iteratorInputs: [string, string] | null = null;
		for (const statement of block.body) {
			if (
				!t.isVariableDeclaration(statement) ||
				statement.declarations.length !== 1
			) continue;
			const declaration = statement.declarations[0];
			if (
				!t.isArrayPattern(declaration.id) ||
				declaration.id.elements.length !== 2 ||
				!declaration.id.elements.every((element) =>
					t.isIdentifier(element)
				) ||
				!t.isCallExpression(declaration.init) ||
				!t.isV8IntrinsicIdentifier(declaration.init.callee)
			) continue;
			const [first, second] = declaration.id.elements;
			if (!t.isIdentifier(first) || !t.isIdentifier(second)) continue;
			if (declaration.init.callee.name === 'IteratorBegin') {
				iteratorInputs = [first.name, second.name];
				continue;
			}
			if (
				declaration.init.callee.name !== 'IteratorNext' ||
				iteratorInputs == null ||
				declaration.init.arguments.length < 2 ||
				!t.isIdentifier(declaration.init.arguments[0], {
					name: iteratorInputs[0],
				}) ||
				!t.isIdentifier(declaration.init.arguments[1], {
					name: iteratorInputs[1],
				})
			) continue;
			if (closeStates.has(second.name)) return true;
		}
	}
	return false;
}

function regionSubsumesIteratorFinalizer(
	region: Region,
	descriptor: ExceptionDescriptor,
	result: StructuringResult,
): boolean {
	// A `yield*` machine carries its own `catch`: the delegate protocol routes a
	// thrown value to `iterator.throw`, and the recovered `yield*` expression is
	// that whole protocol. The machine has to own the entire range for this --
	// a user `try` around `yield*` protects blocks the machine does not.
	if (
		descriptor.kind === 'catch' &&
		delegateMachineOwnsRange(region, descriptor)
	) return true;
	if (descriptor.kind !== 'finally') return false;
	let delegateSubsumes = false;
	let forOfSubsumes = false;
	visitHighLevelIteratorRegions(region, (candidate) => {
		if (
			candidate.kind === 'delegateYield' &&
			(candidate.sourceBlocks.has(descriptor.handler) ||
				[...descriptor.protectedEntries].some((entry) =>
					candidate.sourceBlocks.has(entry)
				))
		) delegateSubsumes = true;
		if (
			candidate.kind === 'loop' && candidate.syntax?.kind === 'forOf' &&
			[...descriptor.protectedEntries].some((entry) =>
				candidate.sourceBlocks.has(entry)
			)
		) forOfSubsumes = true;
	});
	if (delegateSubsumes) return true;
	if (!forOfSubsumes) return false;
	const finalizerBlocks = descriptor.finallyBodyBlocks ??
		[descriptor.handler];
	const closesIterator = finalizerBlocks.some((address) =>
		result.cfg.blocks.get(address)?.body.some((statement) => {
			let found = false;
			t.traverseFast(statement, (node) => {
				if (
					t.isV8IntrinsicIdentifier(node, { name: 'IteratorClose' })
				) found = true;
			});
			return found;
		}) ?? false
	);
	return closesIterator;
}

function visitHighLevelIteratorRegions(
	region: Region,
	visit: (region: Region) => void,
) {
	if (
		region.kind === 'delegateYield' ||
		(region.kind === 'loop' && region.syntax?.kind === 'forOf')
	) visit(region);
	switch (region.kind) {
		case 'sequence':
			for (const child of region.regions) {
				visitHighLevelIteratorRegions(child, visit);
			}
			break;
		case 'if':
			visitHighLevelIteratorRegions(region.consequent, visit);
			visitHighLevelIteratorRegions(region.alternate, visit);
			break;
		case 'switch':
			for (const switchCase of region.cases) {
				visitHighLevelIteratorRegions(switchCase.body, visit);
			}
			visitHighLevelIteratorRegions(region.defaultBody, visit);
			break;
		case 'tryCatch':
			visitHighLevelIteratorRegions(region.body, visit);
			visitHighLevelIteratorRegions(region.handler, visit);
			break;
		case 'tryFinally':
			visitHighLevelIteratorRegions(region.body, visit);
			visitHighLevelIteratorRegions(region.finalizer, visit);
			break;
		case 'loop':
			visitHighLevelIteratorRegions(region.body, visit);
			break;
	}
}

function collectRegionHandlerAddresses(region: Region, handlers: Set<number>) {
	if (region.kind === 'tryCatch' || region.kind === 'tryFinally') {
		handlers.add(region.handlerAddress);
	}
	switch (region.kind) {
		case 'sequence':
			for (const child of region.regions) {
				collectRegionHandlerAddresses(child, handlers);
			}
			break;
		case 'if':
			collectRegionHandlerAddresses(region.consequent, handlers);
			collectRegionHandlerAddresses(region.alternate, handlers);
			break;
		case 'switch':
			for (const switchCase of region.cases) {
				collectRegionHandlerAddresses(switchCase.body, handlers);
			}
			collectRegionHandlerAddresses(region.defaultBody, handlers);
			break;
		case 'tryCatch':
			collectRegionHandlerAddresses(region.body, handlers);
			collectRegionHandlerAddresses(region.handler, handlers);
			break;
		case 'tryFinally':
			collectRegionHandlerAddresses(region.body, handlers);
			collectRegionHandlerAddresses(region.finalizer, handlers);
			break;
		case 'loop':
			collectRegionHandlerAddresses(region.body, handlers);
			break;
	}
}

function collectRegionBasicBlocks(region: Region, blocks: Set<number>) {
	if (region.kind === 'basic') {
		for (const address of region.sourceBlocks) blocks.add(address);
		return;
	}
	switch (region.kind) {
		case 'sequence':
			for (const child of region.regions) {
				collectRegionBasicBlocks(child, blocks);
			}
			break;
		case 'if':
			collectRegionBasicBlocks(region.consequent, blocks);
			collectRegionBasicBlocks(region.alternate, blocks);
			break;
		case 'switch':
			for (const switchCase of region.cases) {
				collectRegionBasicBlocks(switchCase.body, blocks);
			}
			collectRegionBasicBlocks(region.defaultBody, blocks);
			break;
		case 'tryCatch':
			collectRegionBasicBlocks(region.body, blocks);
			collectRegionBasicBlocks(region.handler, blocks);
			break;
		case 'tryFinally':
			collectRegionBasicBlocks(region.body, blocks);
			collectRegionBasicBlocks(region.finalizer, blocks);
			break;
		case 'loop':
			collectRegionBasicBlocks(region.body, blocks);
			break;
	}
}

function regionContainsUnstructuredBranch(
	region: Region,
	result: StructuringResult,
): boolean {
	const loopHeaders = new Set<number>();
	collectLoopHeaders(region, loopHeaders);
	const structuredBranchBlocks = new Set<number>();
	collectStructuredBranchBlocks(region, result, structuredBranchBlocks);
	return containsUnstructuredBranch(
		region,
		result,
		loopHeaders,
		structuredBranchBlocks,
	);
}

function containsUnstructuredBranch(
	region: Region,
	result: StructuringResult,
	loopHeaders: ReadonlySet<number>,
	structuredBranchBlocks: ReadonlySet<number>,
): boolean {
	if (region.kind === 'basic') {
		for (const addr of region.sourceBlocks) {
			if (structuredBranchBlocks.has(addr)) continue;
			const terminator = result.cfg.blocks.get(addr)?.terminator;
			if (
				terminator?.kind === 'if' &&
				(loopHeaders.has(terminator.fallthrough) ||
					loopHeaders.has(terminator.taken))
			) continue;
			if (blockNeedsBranchRegion(addr, result.cfg)) return true;
		}
		return false;
	}
	switch (region.kind) {
		case 'sequence':
			return region.regions.some((child) =>
				containsUnstructuredBranch(
					child,
					result,
					loopHeaders,
					structuredBranchBlocks,
				)
			);
		case 'if':
			return containsUnstructuredBranch(
				region.consequent,
				result,
				loopHeaders,
				structuredBranchBlocks,
			) || containsUnstructuredBranch(
				region.alternate,
				result,
				loopHeaders,
				structuredBranchBlocks,
			);
		case 'switch':
			return region.cases.some((switchCase) =>
				containsUnstructuredBranch(
					switchCase.body,
					result,
					loopHeaders,
					structuredBranchBlocks,
				)
			) || containsUnstructuredBranch(
				region.defaultBody,
				result,
				loopHeaders,
				structuredBranchBlocks,
			);
		case 'tryCatch':
			return containsUnstructuredBranch(
				region.body,
				result,
				loopHeaders,
				structuredBranchBlocks,
			) || containsUnstructuredBranch(
				region.handler,
				result,
				loopHeaders,
				structuredBranchBlocks,
			);
		case 'tryFinally':
			return containsUnstructuredBranch(
				region.body,
				result,
				loopHeaders,
				structuredBranchBlocks,
			) || containsUnstructuredBranch(
				region.finalizer,
				result,
				loopHeaders,
				structuredBranchBlocks,
			);
		case 'loop':
			return containsUnstructuredBranch(
				region.body,
				result,
				loopHeaders,
				structuredBranchBlocks,
			);
		default:
			return false;
	}
}

function collectStructuredBranchBlocks(
	region: Region,
	result: StructuringResult,
	blocks: Set<number>,
	inForOf = false,
) {
	if (region.kind === 'if' && region.predicateBlocks) {
		for (const address of region.predicateBlocks) blocks.add(address);
	} else if (region.kind === 'if') {
		blocks.add(region.header);
	} else if (region.kind === 'switch') {
		blocks.add(region.header);
	}
	if (inForOf && (region.kind === 'if' || region.kind === 'switch')) {
		for (const address of region.sourceBlocks) {
			const kind = result.cfg.blocks.get(address)?.terminator.kind;
			if (kind === 'if' || kind === 'switch') blocks.add(address);
		}
	}
	switch (region.kind) {
		case 'sequence':
			for (const child of region.regions) {
				collectStructuredBranchBlocks(child, result, blocks, inForOf);
			}
			break;
		case 'if':
			collectStructuredBranchBlocks(
				region.consequent,
				result,
				blocks,
				inForOf,
			);
			collectStructuredBranchBlocks(
				region.alternate,
				result,
				blocks,
				inForOf,
			);
			break;
		case 'switch':
			for (const switchCase of region.cases) {
				collectStructuredBranchBlocks(
					switchCase.body,
					result,
					blocks,
					inForOf,
				);
			}
			collectStructuredBranchBlocks(
				region.defaultBody,
				result,
				blocks,
				inForOf,
			);
			break;
		case 'tryCatch':
			if (region.retryLoop?.conditionalExit) {
				// The retry emitter lowers this handler trailer to a conditional
				// backedge/`break` and places each edge's Phi actions itself.
				blocks.add(region.retryLoop.conditionalExit.decision);
			}
			collectStructuredBranchBlocks(
				region.body,
				result,
				blocks,
				inForOf,
			);
			collectStructuredBranchBlocks(
				region.handler,
				result,
				blocks,
				inForOf,
			);
			break;
		case 'tryFinally':
			collectStructuredBranchBlocks(
				region.body,
				result,
				blocks,
				inForOf,
			);
			collectStructuredBranchBlocks(
				region.finalizer,
				result,
				blocks,
				inForOf,
			);
			break;
		case 'loop':
			blocks.add(region.header);
			for (const latch of region.latches) {
				blocks.add(latch);
			}
			collectStructuredBranchBlocks(
				region.body,
				result,
				blocks,
				inForOf || region.syntax?.kind === 'forOf',
			);
			for (const exit of region.exits) {
				if (!exit.trailer) continue;
				collectStructuredBranchBlocks(
					exit.trailer,
					result,
					blocks,
					inForOf || region.syntax?.kind === 'forOf',
				);
			}
			break;
	}
}

function hasUnrepresentedSwitchDescriptor(
	region: Region,
	result: StructuringResult,
): boolean {
	const structuredBranches = new Set<number>();
	collectStructuredBranchBlocks(region, result, structuredBranches);
	return result.descriptors.switches.switches.some((descriptor) => {
		if (structuredBranches.has(descriptor.dispatchBlock)) return false;
		if (
			descriptor.kind === 'compareChain' &&
			descriptor.coveredBlocks &&
			[...descriptor.coveredBlocks].every((address) =>
				structuredBranches.has(address)
			)
		) return false;
		return true;
	});
}

function collectLoopHeaders(region: Region, headers: Set<number>) {
	if (region.kind === 'loop') headers.add(region.header);
	switch (region.kind) {
		case 'sequence':
			for (const child of region.regions) {
				collectLoopHeaders(child, headers);
			}
			break;
		case 'if':
			collectLoopHeaders(region.consequent, headers);
			collectLoopHeaders(region.alternate, headers);
			break;
		case 'switch':
			for (const switchCase of region.cases) {
				collectLoopHeaders(switchCase.body, headers);
			}
			collectLoopHeaders(region.defaultBody, headers);
			break;
		case 'tryCatch':
			collectLoopHeaders(region.body, headers);
			collectLoopHeaders(region.handler, headers);
			break;
		case 'tryFinally':
			collectLoopHeaders(region.body, headers);
			collectLoopHeaders(region.finalizer, headers);
			break;
		case 'loop':
			collectLoopHeaders(region.body, headers);
			break;
	}
}

/**
 * A block claimed by two Regions keeps its statements at the first claimant, so
 * the second tests values nothing declares. This is reported rather than
 * treated as a miss: every branch is still structured.
 */
function duplicateOwnershipDiagnostics(
	duplicated: Readonly<Record<string, number>>,
): Array<{ kind: string; message: string }> {
	const entries = Object.entries(duplicated);
	if (entries.length === 0) return [];
	return [{
		kind: 'duplicateBlockOwnership',
		message: `blocks ${
			entries.map(([address, count]) => `${address} (${count} claims)`)
				.join(
					', ',
				)
		} are claimed by more than one Region`,
	}];
}

function summarizeUnstructuredBranches(
	result: StructuringResult,
): RecursiveBranchShapeSummary[] {
	const structured = new Set<number>();
	const loopHeaders = new Set<number>();
	if (result.region) {
		collectStructuredBranchBlocks(result.region, result, structured);
		collectLoopHeaders(result.region, loopHeaders);
	}
	const summaries: RecursiveBranchShapeSummary[] = [];
	for (const [block, cfgBlock] of result.cfg.blocks) {
		if (cfgBlock.terminator.kind !== 'if' || structured.has(block)) {
			continue;
		}
		if (
			loopHeaders.has(cfgBlock.terminator.fallthrough) ||
			loopHeaders.has(cfgBlock.terminator.taken)
		) continue;
		const fallthrough = cfgBlock.terminator.fallthrough;
		const taken = cfgBlock.terminator.taken;
		const shapes = new Set<RecursiveBranchShape>();
		if (fallthrough === taken) shapes.add('duplicate-edge');
		const join = result.analyses.postdominators.nearestCommonPostdominator(
			fallthrough,
			taken,
		);
		if (join != null) {
			shapes.add('shared-continuation');
			if (fallthrough === join || taken === join) shapes.add('empty-arm');
			if (
				(result.descriptors.phis.phisByBlock.get(join)?.length ?? 0) > 0
			) {
				shapes.add('phi-join');
			}
		}
		const fallthroughTerminals = reachableTerminalBlocks(
			fallthrough,
			result,
		);
		const takenTerminals = reachableTerminalBlocks(taken, result);
		if (
			isTerminalBlock(fallthrough, result) ||
			isTerminalBlock(taken, result)
		) shapes.add('terminal-arm');
		if (
			[...fallthroughTerminals].some((terminal) =>
				takenTerminals.has(terminal)
			)
		) shapes.add('shared-terminal');
		if (crossesProtectedRegionBoundary(block, fallthrough, taken, result)) {
			shapes.add('protected-region-boundary');
		}
		if (
			result.analyses.reducibility.irreducibleSCCs.some((component) =>
				component.has(block) || component.has(fallthrough) ||
				component.has(taken)
			)
		) shapes.add('irreducible-subgraph');
		if (shapes.size === 0) shapes.add('unclassified');
		summaries.push({
			block,
			shapes: [...shapes].toSorted(),
		});
	}
	return summaries.toSorted((left, right) => left.block - right.block);
}

function reachableTerminalBlocks(
	entry: BlockAddr,
	result: StructuringResult,
): Set<BlockAddr> {
	const terminals = new Set<BlockAddr>();
	const seen = new Set<BlockAddr>();
	const pending = [entry];
	while (pending.length > 0) {
		const block = pending.pop()!;
		if (seen.has(block)) continue;
		seen.add(block);
		if (isTerminalBlock(block, result)) {
			terminals.add(block);
			continue;
		}
		for (const successor of result.cfg.normalSuccessors.get(block) ?? []) {
			if (!seen.has(successor)) pending.push(successor);
		}
	}
	return terminals;
}

function isTerminalBlock(
	block: BlockAddr,
	result: StructuringResult,
): boolean {
	const kind = result.cfg.blocks.get(block)?.terminator.kind;
	return kind === 'return' || kind === 'throw' || kind === 'unreachable';
}

function crossesProtectedRegionBoundary(
	block: BlockAddr,
	fallthrough: BlockAddr,
	taken: BlockAddr,
	result: StructuringResult,
): boolean {
	const owners = (address: BlockAddr) =>
		[...(result.cfg.exceptionalSuccessors.get(address) ?? [])]
			.toSorted((left, right) => left - right)
			.join(',');
	const owner = owners(block);
	return owners(fallthrough) !== owner || owners(taken) !== owner;
}

function summarizePhiEdges(
	result: StructuringResult,
): RecursivePhiEdgeSummary[] {
	return [...result.descriptors.phis.phisByEdgeKey.values()].map((
		assignments,
	) => {
		const [first] = assignments;
		return {
			from: first.edge.from,
			to: first.edge.to,
			kind: first.edge.kind,
			assignments: assignments.map((assignment) => ({
				target: expressionDebugName(assignment.target),
				value: expressionDebugName(assignment.value),
			})),
		};
	}).toSorted((left, right) =>
		left.from - right.from || left.to - right.to ||
		left.kind.localeCompare(right.kind)
	);
}

function expressionDebugName(expr: t.Expression): string {
	if (t.isIdentifier(expr)) return expr.name;
	if (t.isNumericLiteral(expr)) return String(expr.value);
	if (t.isStringLiteral(expr)) return JSON.stringify(expr.value);
	if (t.isBooleanLiteral(expr)) return String(expr.value);
	if (t.isNullLiteral(expr)) return 'null';
	return expr.type;
}

function collectRegionMisses(regionText: string, misses: Set<string>) {
	if (regionText.includes('fallback')) misses.add('fallback-region');
	if (regionText.includes('weak-SESE arm')) {
		misses.add('weak-sese-arm-not-structured');
	}
}
