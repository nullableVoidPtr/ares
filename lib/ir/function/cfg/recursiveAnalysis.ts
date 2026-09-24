import { LiftError } from '../../error.ts';
import type { IRFunction } from '../mod.ts';
import { summarizeRecursiveCFG } from './recursiveSummary.ts';
import {
	structureCFG,
	type StructuringResult,
} from './structure/structureRegion.ts';

export interface RecursiveCFGAnalysisOptions {
	strict?: boolean;
	debug?: boolean;
	subject?: string;
	normalizeForRegions?: boolean;
	validateNormalization?: boolean;
	/** Internal diagnostics hook; never serialized or consulted by reducers. */
	retainArtifacts?: boolean;
	observer?: (result: StructuringResult) => void;
}

export function runRecursiveCFGAnalysis(
	func: IRFunction,
	options: RecursiveCFGAnalysisOptions = {},
): StructuringResult {
	const result = structureCFG(func, {
		strict: options.strict,
		normalizeForRegions: options.normalizeForRegions,
		validateNormalization: options.validateNormalization,
	});
	options.observer?.(result);
	func.recursiveCFGSummary = summarizeRecursiveCFG(func.id, result, {
		generateCode: options.retainArtifacts !== false,
	});
	func.cleanupRecursiveCFGSummaryEmission();

	if (options.debug) {
		const subject = options.subject ?? 'function';
		console.error(
			`[recursive-cfg] ${subject} #${func.id}: ` +
				`${result.cfg.blocks.size} blocks, ` +
				`${result.analyses.sccs.components.length} SCCs, ` +
				`${result.analyses.naturalLoops.loops.length} loops, ` +
				`${result.descriptors.phis.phis.length} phis, ` +
				`${result.descriptors.switches.switches.length} switches, ` +
				`${result.descriptors.delegateYields.delegates.length} delegate-yields, ` +
				`${result.descriptors.destructuring.descriptors.length} destructuring patterns, ` +
				`${result.descriptors.destructuring.protocolCandidates.length} destructuring protocol candidates`,
		);
		if (result.normalization.enabled) {
			console.error(
				`[recursive-cfg] normalization: ` +
					`${result.normalization.blocksBefore} -> ` +
					`${result.normalization.blocksAfter} blocks, ` +
					`idempotent=${result.normalization.idempotent}, ` +
					`invariants=${result.normalization.invariantIssues.length}`,
			);
		}
		if (func.recursiveCFGSummary.regionText) {
			console.error(func.recursiveCFGSummary.regionText);
		}
		for (const diagnostic of result.diagnostics.items) {
			console.error(
				`[recursive-cfg:${diagnostic.kind}] ${diagnostic.message}`,
			);
		}
	}

	if (options.strict) {
		const diagnostic = result.diagnostics.items[0];
		if (diagnostic) throw new LiftError(diagnostic.message);
	}

	return result;
}
