import * as t from '@babel/types';
import { envCFGReducerOptions } from '../cfg/options.ts';
import { runRecursiveCFGAnalysis } from '../cfg/recursiveAnalysis.ts';
import { reduceSequence, reduceSharedSequenceEdge } from '../cfg/linear.ts';
import { reduceSimpleIf } from '../cfg/predicates.ts';
import {
	reduceInlineTerminal,
	reduceSharedAlternateGuard,
} from '../cfg/terminals.ts';
import type { IRFunction } from '../mod.ts';
import { recoveredGeneratorCFGDebugEnabled } from './debug.ts';
import { analyseLoweredGeneratorStateMachine } from './model.ts';
import { promoteRecoveredEnvironmentSlots } from './environmentMem2Reg.ts';
import { finishRecoveredGenerator } from './postRecovery.ts';
import { buildRecoveredGeneratorCFG } from './recoveryCFG.ts';
import type { LoweredGeneratorModel } from './types.ts';

export {
	analyseLoweredGeneratorClosure,
	applyLoweredGeneratorWrapperSlotAliases,
	recordLoweredGeneratorWrapperSlotAliases,
} from './aliases.ts';

export function tryInitializeLoweredGeneratorStateMachine(func: IRFunction) {
	try {
		if (Deno.env.get('ARES_TRACE_LG') === '1') {
			console.error(`[LG] try function #${func.id}`);
		}
	} catch { /* ignore */ }
	const model = analyseLoweredGeneratorStateMachine(func);
	try {
		if (Deno.env.get('ARES_TRACE_LG') === '1') {
			console.error(`[LG] model function #${func.id} = ${model != null}`);
		}
	} catch { /* ignore */ }
	if (!model) return false;

	buildRecoveredGeneratorCFG(func, model);
	promoteRecoveredEnvironmentSlots(
		func,
		model.materializedEnvironmentNames,
	);
	finishRecoveredGenerator(func, model);
	reduceRecoveredGeneratorCFG(func);
	recordRecoveredGeneratorRecursiveSummary(func, model);
	return true;
}

function reduceRecoveredGeneratorCFG(func: IRFunction) {
	let changed: boolean;
	do {
		changed = reduceSequence(func);
		changed = reduceSharedSequenceEdge(func) || changed;
		changed = reduceInlineTerminal(func) || changed;
		changed = reduceSharedAlternateGuard(func) || changed;
		changed = reduceSimpleIf(func) || changed;
		if (changed) func.cleanupLiftedBlocks();
	} while (changed);
}

function recordRecoveredGeneratorRecursiveSummary(
	func: IRFunction,
	model: LoweredGeneratorModel,
) {
	const cfgReducer = func.options.cfgReducer ?? envCFGReducerOptions();

	debugRecoveredGeneratorCFG(func);

	runRecursiveCFGAnalysis(func, {
		strict: cfgReducer.strict,
		debug: cfgReducer.debug,
		subject: 'recovered lowered generator',
		normalizeForRegions: cfgReducer.migrationAudit != null ||
			cfgReducer.debug === true,
		validateNormalization: cfgReducer.migrationAudit != null ||
			cfgReducer.debug === true,
		observer: (result) => {
			for (const decline of model.finalizerCopies.declines) {
				const entry = model.remap.get(decline.state) ??
					result.cfg.entry;
				result.diagnostics.add({
					kind: 'unmatchedFinalizer',
					entry,
					message:
						`lowered generator finalizer state ${decline.state} ` +
						`declined: ${decline.reason} ` +
						`[${decline.continuations.join(', ')}]`,
				});
			}
		},
	});
	func.initializeMigrationAudit(cfgReducer);
	func.finalizeMigrationAudit();
}

function debugRecoveredGeneratorCFG(func: IRFunction) {
	if (!recoveredGeneratorCFGDebugEnabled()) return;
	console.error(`[recovered-generator-cfg] function #${func.id}`);
	for (
		const [addr, block] of [...func.blocks].toSorted((left, right) =>
			left[0] - right[0]
		)
	) {
		const strings: string[] = [];
		for (const stmt of block.body) {
			t.traverseFast(stmt as t.Statement, (node) => {
				if (!t.isStringLiteral(node)) return;
				if (strings.includes(node.value)) return;
				strings.push(node.value);
			});
		}
		const terminal = block.body.at(-1) as t.Statement | undefined;
		const terminalKind = terminal?.type ?? 'none';
		const successors = block.consequentAddresses.map((successor) =>
			`0x${successor.toString(16)}`
		).join(',');
		const branch = block.branch == null ? '' : ' branch';
		const label = strings.length === 0
			? ''
			: ` strings=${strings.join('|')}`;
		console.error(
			`  0x${addr.toString(16)} -> [${successors}] ` +
				`${terminalKind}${branch}${label}`,
		);
	}
}
