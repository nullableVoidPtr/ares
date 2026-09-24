import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import type { IRFunction } from '../mod.ts';
import { debug, debugModel } from './debug.ts';
import { bindYieldResumeValues, collectSSACases } from './caseLifting.ts';
import {
	collectPreludeBody,
	reduceLoweredGeneratorEnvironmentAliases,
} from './environmentAnalysis.ts';
import type { LoweredGeneratorModel, StateDispatch } from './types.ts';
import {
	analyseEmbeddedFinallySplits,
	analyseFinalizerCopies,
	orderedStates,
} from './finalizerAnalysis.ts';
import { buildSSAGeneratorModel } from './ssaModel.ts';
import { stateRolesFromRecognition } from './recognition.ts';
import { statementDebugType } from './recoveredCleanup.ts';
import { collectParentParameterAliases } from './postRecovery.ts';
import { hasRecoveredIteratorEnvironmentDestructuring } from './iteratorRecovery.ts';
import { coalesceParameterAliases } from '../../ast/alias.ts';
import { caseContinuation } from './caseUtils.ts';

function validateLoweredGeneratorModel(model: LoweredGeneratorModel) {
	if (!model.cases.has(0)) {
		debug('lowered generator missing initial state');
		return false;
	}

	for (const info of model.cases.values()) {
		for (const nextState of caseContinuation(info).states) {
			if (model.cases.has(nextState)) continue;
			debug('lowered generator missing next state', {
				state: info.state,
				nextState,
			});
			return false;
		}
		if (
			info.activeHandlerIndex != null &&
			info.activeHandlerIndex !== 0
		) {
			const handlerState = model.roles.handlerIndexToState.get(
				info.activeHandlerIndex,
			);
			if (handlerState == null || !model.cases.has(handlerState)) {
				debug('lowered generator missing handler state', {
					state: info.state,
					activeHandlerIndex: info.activeHandlerIndex,
					handlerState,
				});
				return false;
			}
		}
	}

	for (const split of model.embeddedFinallySplits) {
		if (
			!model.cases.has(split.catchState) ||
			!model.cases.has(split.finallyState)
		) {
			debug('lowered generator invalid embedded finally split', split);
			return false;
		}
	}

	return true;
}

export function analyseLoweredGeneratorStateMachine(
	func: IRFunction,
): LoweredGeneratorModel | undefined {
	const ssaModel = buildSSAGeneratorModel(func);
	if (!ssaModel) return;
	const dispatch: StateDispatch = {
		roles: stateRolesFromRecognition(ssaModel.recognition),
		cases: ssaModel.recognition.dispatch,
	};
	const { roles } = dispatch;

	const cases = collectSSACases(func, ssaModel);
	if (!cases) return;
	debugModel('case emitter', {
		functionId: func.id,
		source: 'ssa',
		caseSize: cases.size,
	});
	debug(
		'state dispatch cases',
		[...cases.values()].map((info) => ({
			state: info.state,
			address: info.address,
			path: info.path,
			nextState: info.nextState,
			continuations: caseContinuation(info).states,
			bodyTypes: info.body.map(statementDebugType),
			terminal: statementDebugType(info.terminal),
		})),
	);
	if (!cases.has(0)) return;
	const order = orderedStates(cases, roles);
	const resumeDeclarations = bindYieldResumeValues(func, cases, order);
	const remap = new Map(
		order.map((state, index) => [state, index as BlockAddr]),
	);
	const preludeBody = collectPreludeBody(func, roles);
	preludeBody.unshift(...resumeDeclarations);
	const parentParameterAliases = collectParentParameterAliases(
		func,
		cases,
		preludeBody,
	);
	const materializedEnvironmentNames =
		hasRecoveredIteratorEnvironmentDestructuring(cases)
			? new Set<string>()
			: reduceLoweredGeneratorEnvironmentAliases(
				func,
				cases,
				order,
				preludeBody,
				roles,
			);
	// A captured parameter that Hermes copied into an environment slot comes
	// back as a materialized local initialised from the parameter. Fold it back
	// onto the parameter now that the prelude and every case body exist, which
	// is the first point where "the parameter is referenced exactly once" can
	// be established.
	coalesceParameterAliases(preludeBody, [
		...preludeBody,
		...[...cases.values()].flatMap((info) => [
			...info.body,
			info.terminal,
			...[...info.blocks?.values() ?? []].flatMap((block) => [
				...block.body,
				...block.terminal ? [block.terminal] : [],
			]),
		]),
	]);
	const embeddedFinallySplits = func.file.version >= 97
		? analyseEmbeddedFinallySplits(cases, roles)
		: [];
	const finalizerCopies = analyseFinalizerCopies(func, cases, roles, remap);

	const model: LoweredGeneratorModel = {
		roles,
		dispatch,
		cases,
		order,
		remap,
		embeddedFinallySplits,
		preludeBody,
		finalizerCopies,
		parentParameterAliases,
		materializedEnvironmentNames,
	};
	return validateLoweredGeneratorModel(model) ? model : undefined;
}
