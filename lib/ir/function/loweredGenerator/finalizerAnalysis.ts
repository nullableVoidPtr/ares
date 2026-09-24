import * as t from '@babel/types';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../utils/map.ts';
import type { SSAInstruction } from '../../../ssa.ts';
import type { IRFunction } from '../mod.ts';
import type { LiftedAST } from '../../ast/mod.ts';
import { comparableAst } from '../../ast/utils.ts';
import { FinallyRecord } from '../except/mod.ts';
import { storeEnvironmentCall } from './envAccess.ts';
import { debug, debugModel } from './debug.ts';
import {
	caseBodies,
	caseContinuation,
	yieldExpressionStatementValue,
} from './caseUtils.ts';
import type {
	CaseInfo,
	EmbeddedFinallySplit,
	EmbeddedSplitAddresses,
	FinalizerCopyAnalysis,
	ProtectedStateAnalysis,
	StateRoles,
} from './types.ts';
import {
	environmentLoadDeclarationSlot,
	environmentStoreStatementSlot,
	isLoadFromEnvironmentCall,
	stripLoweredGeneratorEnvironmentScaffolding,
} from './environmentScaffolding.ts';

function comparableInstructionKeys(instr: SSAInstruction) {
	return Object.keys(instr).filter((key) =>
		![
			'functionLocalOffset',
			'type',
			'length',
			'cacheIndex',
			'objectValueBufferIndex',
		].includes(key)
	).toSorted();
}

function shouldIgnoreForFinalizerSignature(
	instr: SSAInstruction,
	roles: StateRoles,
	syntheticConstRegisters: Set<number>,
	ignoreCaughtException = false,
) {
	if (instr.instruction === 'Phi') return true;
	if (instr.instruction === 'Jmp') return true;
	if (
		instr.instruction === 'LoadConst' &&
		syntheticConstRegisters.has(instr.destination.index)
	) return true;
	if (
		(instr.instruction === 'StoreNPToEnvironment' ||
			instr.instruction === 'StoreToEnvironment') && (
				instr.slotIndex === roles.switchSlot ||
				instr.slotIndex === roles.exceptionHandlerSlot ||
				instr.slotIndex === roles.executionStatusSlot
			)
	) return true;
	if (
		ignoreCaughtException &&
		(instr.instruction === 'StoreNPToEnvironment' ||
			instr.instruction === 'StoreToEnvironment') &&
		instr.slotIndex === roles.caughtExceptionSlot
	) return true;
	if (
		instr.instruction === 'LoadFromEnvironment' &&
		(instr.slotIndex === roles.exceptionHandlerSlot ||
			instr.slotIndex === roles.executionStatusSlot)
	) return true;
	if (
		ignoreCaughtException &&
		instr.instruction === 'LoadFromEnvironment' &&
		instr.slotIndex === roles.caughtExceptionSlot
	) return true;
	if (
		instr.instruction === 'JStrictEqual' &&
		instr.left.index === roles.actionRegister
	) return true;
	return false;
}

function normalizedInstructionValue(
	value: unknown,
	registers: Map<string, string>,
): unknown {
	if (Array.isArray(value)) {
		return value.map((v) => normalizedInstructionValue(v, registers));
	}
	if (value && typeof value === 'object') {
		const record = value as Record<string, unknown>;
		if (
			typeof record.index === 'number' &&
			(typeof record.version === 'number' ||
				typeof record.type === 'string')
		) {
			const key = `${record.index}:${record.version ?? ''}:${
				record.type ?? ''
			}`;
			let normalized = registers.get(key);
			if (!normalized) {
				registers.set(key, normalized = `r${registers.size}`);
			}
			return { register: normalized };
		}

		const result: Record<string, unknown> = {};
		for (const key of Object.keys(record).toSorted()) {
			result[key] = normalizedInstructionValue(record[key], registers);
		}
		return result;
	}
	return value;
}

function finalizerChainSignature(
	func: IRFunction,
	cases: Map<number, CaseInfo>,
	roles: StateRoles,
	startState: number,
	followNext = true,
	ignoreCaughtException = false,
) {
	const signature: unknown[] = [];
	const registers = new Map<string, string>();
	const seen = new Set<number>();
	let state: number | null | undefined = startState;

	while (state != null && cases.has(state) && !seen.has(state)) {
		seen.add(state);
		const info: CaseInfo = cases.get(state)!;
		if (!ignoreCaughtException && caseReadsCaughtException(info, roles)) {
			return;
		}

		const syntheticConstRegisters = new Set<number>();
		for (const blockAddress of info.path) {
			const block = func.ssa._func.basicBlocks.get(blockAddress);
			if (!block) return;
			for (const instr of block.instructions) {
				if (
					(instr.instruction === 'StoreNPToEnvironment' ||
						instr.instruction === 'StoreToEnvironment') && (
							instr.slotIndex === roles.switchSlot ||
							instr.slotIndex === roles.exceptionHandlerSlot ||
							instr.slotIndex === roles.executionStatusSlot
						)
				) {
					syntheticConstRegisters.add(instr.value.index);
				}
				if (
					instr.instruction === 'JStrictEqual' &&
					instr.left.index === roles.actionRegister
				) {
					syntheticConstRegisters.add(instr.right.index);
				}
			}
		}

		for (const blockAddress of info.path) {
			const block = func.ssa.basicBlocks.get(blockAddress);
			if (!block) return;
			for (const instr of block.ssaInstructions) {
				if (
					shouldIgnoreForFinalizerSignature(
						instr,
						roles,
						syntheticConstRegisters,
						ignoreCaughtException,
					)
				) continue;
				const normalized: Record<string, unknown> = {
					instruction: instr.instruction,
				};
				for (const key of comparableInstructionKeys(instr)) {
					normalized[key] = normalizedInstructionValue(
						(instr as unknown as Record<string, unknown>)[key],
						registers,
					);
				}
				if (instr.instruction === 'NewObjectWithBuffer') {
					normalized.objectBuffer = normalizedInstructionValue(
						func.file.getObjectBufferElements(instr),
						registers,
					);
				}
				signature.push(normalized);
			}
		}

		const continuation = caseContinuation(info);
		if (continuation.kind === 'multiple') return;
		if (!followNext || continuation.kind === 'none') break;
		state = continuation.state;
	}

	if (signature.length === 0) return;
	return JSON.stringify(signature);
}

function finalizerStatesForCatchHandlers(
	cases: Map<number, CaseInfo>,
	roles: StateRoles,
) {
	const result = new Set<number>();
	for (const catchState of roles.handlerIndexToState.values()) {
		const catchInfo = cases.get(catchState);
		if (
			catchInfo?.activeHandlerIndex == null ||
			!caseReadsCaughtException(catchInfo, roles)
		) continue;
		const finallyState = roles.handlerIndexToState.get(
			catchInfo.activeHandlerIndex,
		);
		const finallyInfo = finallyState == null
			? undefined
			: cases.get(finallyState);
		if (
			finallyState == null || !finallyInfo ||
			(caseReadsCaughtException(finallyInfo, roles) &&
				!t.isThrowStatement(finallyInfo.terminal))
		) continue;
		result.add(finallyState);
	}
	return result;
}

export function analyseFinalizerCopies(
	func: IRFunction,
	cases: Map<number, CaseInfo>,
	roles: StateRoles,
	remap: Map<number, number>,
): FinalizerCopyAnalysis {
	const finalizerStates = finalizerStatesForCatchHandlers(cases, roles);
	const declines: FinalizerCopyAnalysis['declines'] = [];
	const declinedStates = new Set<number>();
	const declineMultipleContinuations = (info: CaseInfo) => {
		const continuation = caseContinuation(info);
		if (continuation.kind !== 'multiple') return false;
		if (!declinedStates.has(info.state)) {
			declinedStates.add(info.state);
			declines.push({
				state: info.state,
				continuations: continuation.states,
				reason: 'multiple-continuations',
			});
		}
		return true;
	};
	for (const state of [...finalizerStates]) {
		const info = cases.get(state);
		if (info && declineMultipleContinuations(info)) {
			finalizerStates.delete(state);
		}
	}
	for (const catchState of roles.handlerIndexToState.values()) {
		const info = cases.get(catchState);
		if (info?.activeHandlerIndex == null) continue;
		declineMultipleContinuations(info);
		if (!caseReadsCaughtException(info, roles)) continue;
		const finalizerState = roles.handlerIndexToState.get(
			info.activeHandlerIndex,
		);
		const finalizerInfo = finalizerState == null
			? undefined
			: cases.get(finalizerState);
		if (finalizerInfo && declineMultipleContinuations(finalizerInfo)) {
			finalizerStates.delete(finalizerInfo.state);
		}
	}
	const finalizerStatesBySignature = new Map<string, Set<number>>();
	const finalizerStatesByPrefixSignature = new Map<string, Set<number>>();
	const nonCaughtStatesByAstPrefixSignature = new Map<string, Set<number>>();
	for (const finalizerState of finalizerStates) {
		const signature = finalizerChainSignature(
			func,
			cases,
			roles,
			finalizerState,
		);
		if (!signature) continue;
		let states = finalizerStatesBySignature.get(signature);
		if (!states) {
			finalizerStatesBySignature.set(signature, states = new Set());
		}
		states.add(finalizerState);

		const prefixSignature = finalizerChainSignature(
			func,
			cases,
			roles,
			finalizerState,
			false,
		);
		if (!prefixSignature) continue;
		let prefixStates = finalizerStatesByPrefixSignature.get(
			prefixSignature,
		);
		if (!prefixStates) {
			finalizerStatesByPrefixSignature.set(
				prefixSignature,
				prefixStates = new Set(),
			);
		}
		prefixStates.add(finalizerState);
	}
	for (const info of cases.values()) {
		if (caseReadsCaughtException(info, roles)) continue;
		const prefixSignature = suspendedFinalizerAstPrefixSignature(
			info,
			roles,
		);
		let states = nonCaughtStatesByAstPrefixSignature.get(
			prefixSignature,
		);
		if (!states) {
			nonCaughtStatesByAstPrefixSignature.set(
				prefixSignature,
				states = new Set(),
			);
		}
		states.add(info.state);
	}

	const suspendedFinalizerStates = new Set<number>();
	for (const info of cases.values()) {
		if (
			!caseIsYieldTerminal(info) ||
			!caseReadsCaughtException(info, roles)
		) continue;
		const prefixSignature = suspendedFinalizerAstPrefixSignature(
			info,
			roles,
		);
		if (nonCaughtStatesByAstPrefixSignature.has(prefixSignature)) {
			suspendedFinalizerStates.add(info.state);
		}
	}

	const copyRootsByFinalizerState = new Map<number, Set<number>>();
	const successorRedirects = new Map<number, number>();
	for (const state of cases.keys()) {
		if (finalizerStates.has(state)) continue;
		const info = cases.get(state)!;
		if (caseReadsCaughtException(info, roles)) continue;
		const signature = finalizerChainSignature(func, cases, roles, state);
		const prefixSignature = finalizerChainSignature(
			func,
			cases,
			roles,
			state,
			false,
		);
		const finalizers = signature == null
			? prefixSignature == null
				? undefined
				: finalizerStatesByPrefixSignature.get(prefixSignature)
			: finalizerStatesBySignature.get(signature) ??
				(prefixSignature == null
					? undefined
					: finalizerStatesByPrefixSignature.get(prefixSignature));
		if (!finalizers) continue;

		for (const finalizerState of finalizers) {
			let roots = copyRootsByFinalizerState.get(finalizerState);
			if (!roots) {
				copyRootsByFinalizerState.set(
					finalizerState,
					roots = new Set(),
				);
			}
			roots.add(state);
		}
	}
	for (const suspendedFinalizerState of suspendedFinalizerStates) {
		const info = cases.get(suspendedFinalizerState);
		if (!info) continue;
		const prefixSignature = suspendedFinalizerAstPrefixSignature(
			info,
			roles,
		);
		const signatureRoots = nonCaughtStatesByAstPrefixSignature.get(
			prefixSignature,
		);
		if (!signatureRoots) continue;
		const roots = new Set<number>();
		for (const root of signatureRoots) {
			const activeHandlerIndex = cases.get(root)?.activeHandlerIndex;
			if (
				activeHandlerIndex != null &&
				roles.handlerIndexToState.get(activeHandlerIndex) ===
					suspendedFinalizerState
			) roots.add(root);
		}
		if (roots.size === 0) {
			for (const root of signatureRoots) {
				if (
					cases.get(root)?.activeHandlerIndex ===
						info.activeHandlerIndex
				) roots.add(root);
			}
		}
		let changed = true;
		while (changed) {
			changed = false;
			for (const root of signatureRoots) {
				const rootInfo = cases.get(root);
				if (
					!rootInfo ||
					rootInfo.activeHandlerIndex !== info.activeHandlerIndex
				) continue;
				const continuation = caseContinuation(rootInfo);
				if (
					continuation.kind !== 'unique' ||
					!roots.has(continuation.state) ||
					roots.has(root)
				) continue;
				roots.add(root);
				changed = true;
			}
		}
		if (roots.size === 0) continue;
		let finalizerRoots = copyRootsByFinalizerState.get(
			suspendedFinalizerState,
		);
		if (!finalizerRoots) {
			copyRootsByFinalizerState.set(
				suspendedFinalizerState,
				finalizerRoots = new Set(),
			);
		}
		for (const root of roots) finalizerRoots.add(root);
	}
	const bodyStatesByFinalizerState = new Map<number, number[]>();
	const bodyStateStatementLimitsByFinalizerState = new Map<
		number,
		Map<number, number>
	>();
	for (const finalizerState of finalizerStates) {
		const info = cases.get(finalizerState);
		if (!info || caseReadsCaughtException(info, roles)) continue;
		const bodyStates = [finalizerState];
		const initialContinuation = caseContinuation(info);
		let state = initialContinuation.kind === 'unique'
			? initialContinuation.state
			: null;
		const seen = new Set<number>(bodyStates);
		while (state != null && cases.has(state) && !seen.has(state)) {
			const next = cases.get(state)!;
			if (caseReadsCaughtException(next, roles)) break;
			const continuation = caseContinuation(next);
			if (continuation.kind === 'multiple') {
				declineMultipleContinuations(next);
				break;
			}
			bodyStates.push(state);
			seen.add(state);
			const nestedFinallyState = next.activeHandlerIndex == null
				? null
				: roles.handlerIndexToState.get(next.activeHandlerIndex);
			const nestedFinallyInfo = nestedFinallyState == null
				? null
				: cases.get(nestedFinallyState);
			if (
				nestedFinallyInfo != null &&
				caseContinuation(nestedFinallyInfo).kind === 'none'
			) break;
			if (continuation.kind === 'none') break;
			state = continuation.state;
		}
		if (bodyStates.length > 1) {
			bodyStatesByFinalizerState.set(finalizerState, bodyStates);
		}
	}
	for (const suspendedFinalizerState of suspendedFinalizerStates) {
		const info = cases.get(suspendedFinalizerState);
		if (!info) continue;
		const roots = copyRootsByFinalizerState.get(suspendedFinalizerState);
		const rootState = roots == null
			? null
			: [...roots].toSorted((a, b) =>
				(remap.get(a) ?? Number.MAX_SAFE_INTEGER) -
				(remap.get(b) ?? Number.MAX_SAFE_INTEGER)
			)[0] ?? null;
		const bodyRoot = rootState ?? suspendedFinalizerState;
		const bodyRootInfo = cases.get(bodyRoot);
		if (!bodyRootInfo) continue;
		const bodyStates = [bodyRoot];
		const rootContinuation = caseContinuation(bodyRootInfo);
		if (rootContinuation.kind === 'multiple') {
			declineMultipleContinuations(bodyRootInfo);
		} else if (
			rootContinuation.kind === 'unique' &&
			cases.has(rootContinuation.state)
		) {
			bodyStates.push(rootContinuation.state);
			const resumeInfo = cases.get(rootContinuation.state);
			const resumeContinuation = resumeInfo == null
				? { kind: 'none' as const, states: [] as [] }
				: caseContinuation(resumeInfo);
			if (resumeContinuation.kind === 'multiple' && resumeInfo) {
				declineMultipleContinuations(resumeInfo);
			}
			const postFinallyState = resumeContinuation.kind === 'unique'
				? resumeContinuation.state
				: null;
			const postFinallyInfo = postFinallyState == null
				? null
				: cases.get(postFinallyState);
			if (
				postFinallyState != null &&
				postFinallyInfo != null &&
				modeledFinalizerPrefixLength(postFinallyInfo) > 0
			) {
				bodyStates.push(postFinallyState);
				bodyStateStatementLimitsByFinalizerState.set(
					suspendedFinalizerState,
					new Map([[
						postFinallyState,
						modeledFinalizerPrefixLength(postFinallyInfo),
					]]),
				);
			}
		}
		bodyStatesByFinalizerState.set(suspendedFinalizerState, bodyStates);
	}
	debug(
		'finalizer copies',
		[...copyRootsByFinalizerState].map(([finalizerState, roots]) => ({
			finalizerState,
			finalizerOffset: remap.get(finalizerState),
			copyRoots: [...roots].map((state) => ({
				state,
				offset: remap.get(state),
			})),
		})),
	);
	for (const roots of copyRootsByFinalizerState.values()) {
		const orderedRoots = [...roots].toSorted((a, b) =>
			(remap.get(a) ?? Number.MAX_SAFE_INTEGER) -
			(remap.get(b) ?? Number.MAX_SAFE_INTEGER)
		);
		const representative = orderedRoots[0];
		if (representative == null) continue;
		for (const root of orderedRoots.slice(1)) {
			successorRedirects.set(root, representative);
		}
	}
	debug(
		'finalizer redirects',
		[...successorRedirects].map(([from, to]) => ({
			from,
			fromOffset: remap.get(from),
			to,
			toOffset: remap.get(to),
		})),
	);
	return {
		finalizerStates,
		suspendedFinalizerStates,
		bodyStatesByFinalizerState,
		bodyStateStatementLimitsByFinalizerState,
		copyRootsByFinalizerState,
		successorRedirects,
		declines,
	};
}

export function loweredComparableAst(
	value: unknown,
	roles: StateRoles,
	key?: string,
): unknown {
	if (
		[
			'loc',
			'start',
			'end',
			'extra',
			'leadingComments',
			'innerComments',
			'trailingComments',
		].includes(key ?? '')
	) return undefined;

	if (typeof value === 'bigint') return value.toString();

	if (Array.isArray(value)) {
		return value.map((v) => loweredComparableAst(v, roles));
	}
	if (value && typeof value === 'object') {
		if (t.isIdentifier(value as t.Node)) {
			const name = (value as t.Identifier).name;
			const registerIndex = /^r(\d+)_\d+$/.exec(name)?.[1];
			if (registerIndex != null) {
				const constant = roles.constants.get(Number(registerIndex));
				if (constant !== undefined) {
					return { type: 'Identifier', constant };
				}
				return { type: 'Identifier', name: '$generated' };
			}
			if (/^e_\d+$/.test(name)) {
				return { type: 'Identifier', name: '$generated' };
			}
		}

		const result: Record<string, unknown> = {};
		for (
			const [childKey, childValue] of Object.entries(value).toSorted((
				[a],
				[b],
			) => a.localeCompare(b))
		) {
			const comparable = loweredComparableAst(
				childValue,
				roles,
				childKey,
			);
			if (comparable !== undefined) result[childKey] = comparable;
		}
		return result;
	}
	return value;
}

export function loweredStatementsEqual(
	left: t.Statement,
	right: t.Statement,
	roles: StateRoles,
) {
	return JSON.stringify(loweredComparableAst(left, roles)) ===
		JSON.stringify(loweredComparableAst(right, roles));
}

function commonFinalizerPrefixLength(
	copy: t.Statement[],
	copyOffset: number,
	finalizer: t.Statement[],
	roles: StateRoles,
) {
	const maxLength = Math.min(
		finalizer.length,
		copy.length - copyOffset,
	);
	let length = 0;
	while (
		length < maxLength &&
		loweredStatementsEqual(
			copy[copyOffset + length],
			finalizer[length],
			roles,
		)
	) {
		length++;
	}
	return length;
}

export function analyseEmbeddedFinallySplits(
	cases: Map<number, CaseInfo>,
	roles: StateRoles,
): EmbeddedFinallySplit[] {
	const protectedStatesByCatchState = new Map<number, Set<number>>();
	for (const info of cases.values()) {
		if (info.activeHandlerIndex == null) continue;
		const catchState = roles.handlerIndexToState.get(
			info.activeHandlerIndex,
		);
		if (catchState == null || !cases.has(catchState)) continue;
		let states = protectedStatesByCatchState.get(catchState);
		if (!states) {
			protectedStatesByCatchState.set(catchState, states = new Set());
		}
		states.add(info.state);
	}

	const splits: EmbeddedFinallySplit[] = [];
	const usedCatchStates = new Set<number>();
	const usedFinallyStates = new Set<number>();
	for (const [catchState, protectedStates] of protectedStatesByCatchState) {
		if (usedCatchStates.has(catchState)) continue;
		const catchInfo = cases.get(catchState);
		if (!catchInfo || !caseReadsCaughtException(catchInfo, roles)) {
			continue;
		}
		if (catchInfo.blocks) {
			debugModel('skip embedded finally split for subgraph catch', {
				catchState,
			});
			continue;
		}
		// Handler index 0 means "resume with no active handler". These catch
		// cases can still contain inlined finally copies before that resume.
		if (catchInfo.activeHandlerIndex !== 0) continue;

		for (const protectedState of protectedStates) {
			const protectedInfo = cases.get(protectedState);
			if (!protectedInfo) continue;
			const continuation = caseContinuation(protectedInfo);
			if (continuation.kind !== 'unique') continue;
			const finallyState = continuation.state;
			if (usedFinallyStates.has(finallyState)) continue;
			const finallyInfo = cases.get(finallyState);
			if (
				!finallyInfo || finallyInfo.blocks ||
				caseReadsCaughtException(finallyInfo, roles)
			) {
				continue;
			}

			let best: EmbeddedFinallySplit | null = null;
			for (
				let offset = 1;
				offset < catchInfo.body.length - 1;
				offset++
			) {
				const length = commonFinalizerPrefixLength(
					catchInfo.body,
					offset,
					finallyInfo.body,
					roles,
				);
				if (length < 3 || length >= finallyInfo.body.length) continue;
				if (
					best == null ||
					length > best.prefixLength ||
					(length === best.prefixLength &&
						offset < best.catchCopyStart)
				) {
					best = {
						catchState,
						finallyState,
						catchCopyStart: offset,
						prefixLength: length,
					};
				}
			}
			if (!best) continue;
			splits.push(best);
			usedCatchStates.add(catchState);
			usedFinallyStates.add(finallyState);
			break;
		}
	}

	debug('embedded finally splits', splits);
	return splits;
}

export function orderedStates(cases: Map<number, CaseInfo>, roles: StateRoles) {
	const priority: number[] = [];
	const seen = new Set<number>();

	const visit = (state: number | null | undefined) => {
		if (state == null || seen.has(state) || !cases.has(state)) return;
		seen.add(state);
		priority.push(state);
		for (const continuation of caseContinuation(cases.get(state)!).states) {
			visit(continuation);
		}
		const handlerState = cases.get(state)!.activeHandlerIndex == null
			? null
			: roles.handlerIndexToState.get(
				cases.get(state)!.activeHandlerIndex!,
			);
		visit(handlerState);
	};

	visit(0);
	for (const state of [...cases.keys()].toSorted((a, b) => a - b)) {
		visit(state);
	}

	const priorityIndex = new Map(
		priority.map((state, index) => [state, index]),
	);
	const successors = new Map<number, Set<number>>();
	const predecessors = new Map<number, Set<number>>();
	for (const state of priority) {
		successors.set(state, new Set());
		predecessors.set(state, new Set());
	}

	const addEdge = (from: number, to: number) => {
		if (from === to || !cases.has(from) || !cases.has(to)) return;
		successors.get(from)!.add(to);
		predecessors.get(to)!.add(from);
	};

	for (const state of priority) {
		let current: number | null | undefined = state;
		const chainSeen = new Set<number>();
		while (
			current != null && cases.has(current) && !chainSeen.has(current)
		) {
			chainSeen.add(current);
			const info: CaseInfo = cases.get(current)!;
			const handlerState: number | null | undefined =
				info.activeHandlerIndex == null
					? null
					: roles.handlerIndexToState.get(info.activeHandlerIndex);
			if (handlerState == null || !cases.has(handlerState)) break;
			addEdge(state, handlerState);
			current = handlerState;
		}
	}

	const ordered: number[] = [];
	const ready = priority.filter((state) =>
		predecessors.get(state)!.size === 0
	);
	while (ready.length > 0) {
		ready.sort((a, b) => priorityIndex.get(a)! - priorityIndex.get(b)!);
		const state = ready.shift()!;
		ordered.push(state);
		for (const successor of successors.get(state)!) {
			const preds = predecessors.get(successor)!;
			preds.delete(state);
			if (preds.size === 0) ready.push(successor);
		}
	}

	if (ordered.length !== priority.length) return priority;
	return ordered;
}

function caseIsYieldTerminal(info: CaseInfo) {
	if (!info.blocks) {
		return yieldExpressionStatementValue(info.terminal) != null;
	}
	return [...info.blocks.values()].some((block) =>
		yieldExpressionStatementValue(block.terminal) != null
	);
}

function modeledFinalizerPrefixLength(info: CaseInfo) {
	const terminalIndex = info.body.findIndex((stmt) =>
		t.isReturnStatement(stmt) ||
		t.isThrowStatement(stmt) ||
		yieldExpressionStatementValue(stmt) != null
	);
	return terminalIndex === -1 ? info.body.length : terminalIndex;
}

export function analyseProtectedStates(
	cases: Map<number, CaseInfo>,
	roles: StateRoles,
	remap: Map<number, number>,
	finalizerCopies: FinalizerCopyAnalysis,
) {
	const protectedStatesByCatchState = new Map<number, Set<number>>();
	const protectedStatesByFinallyState = new Map<number, Set<number>>();
	const addProtected = (
		target: Map<number, Set<number>>,
		handlerState: number,
		protectedState: number,
	) => {
		let states = target.get(handlerState);
		if (!states) target.set(handlerState, states = new Set());
		states.add(protectedState);
	};
	const finalizerCopyRoots = new Set(
		[...finalizerCopies.copyRootsByFinalizerState.values()].flatMap((
			roots,
		) => [...roots]),
	);
	const protectedContinuationStates = (info: CaseInfo) => {
		const states = [info.state];
		const seen = new Set<number>([info.state]);
		let continuation = caseContinuation(info);
		while (
			continuation.kind === 'unique' && !seen.has(continuation.state)
		) {
			const state = continuation.state;
			seen.add(state);
			if (finalizerCopyRoots.has(state)) break;
			const next = cases.get(state);
			if (!next || next.activeHandlerIndex != null) break;
			if (caseReadsCaughtException(next, roles)) break;
			if (!caseIsYieldTerminal(next)) break;
			states.push(state);
			continuation = caseContinuation(next);
		}
		return states;
	};

	for (const info of cases.values()) {
		const protectedStates = protectedContinuationStates(info);
		if (protectedStates.length === 0) continue;

		let activeHandlerIndex = info.activeHandlerIndex;
		const seenHandlers = new Set<number>();
		while (
			activeHandlerIndex != null && !seenHandlers.has(activeHandlerIndex)
		) {
			seenHandlers.add(activeHandlerIndex);
			const catchState = roles.handlerIndexToState.get(
				activeHandlerIndex,
			);
			if (catchState == null || !cases.has(catchState)) break;
			const catchOffset = remap.get(catchState);
			if (catchOffset == null) break;
			for (const protectedState of protectedStates) {
				addProtected(
					protectedStatesByCatchState,
					catchState,
					protectedState,
				);
			}
			activeHandlerIndex = cases.get(catchState)!.activeHandlerIndex;
		}
	}

	for (const catchState of roles.handlerIndexToState.values()) {
		const catchInfo = cases.get(catchState);
		if (
			catchInfo?.activeHandlerIndex == null ||
			!caseReadsCaughtException(catchInfo, roles)
		) continue;
		const finallyState = roles.handlerIndexToState.get(
			catchInfo.activeHandlerIndex,
		);
		const finallyInfo = finallyState == null
			? undefined
			: cases.get(finallyState);
		if (
			finallyState == null || !finallyInfo ||
			!isGeneratorFinallyCandidate(
				catchInfo,
				finallyInfo,
				roles,
				finalizerCopies,
			)
		) continue;

		const catchOffset = remap.get(catchState);
		const finallyOffset = remap.get(finallyState);
		if (catchOffset == null || finallyOffset == null) continue;
		const protectedByCatch = protectedStatesByCatchState.get(catchState);
		if (!protectedByCatch?.size) continue;
		if (caseReadsCaughtException(finallyInfo, roles)) {
			for (const protectedState of protectedByCatch) {
				addProtected(
					protectedStatesByFinallyState,
					finallyState,
					protectedState,
				);
			}
			continue;
		}

		for (const protectedState of protectedByCatch) {
			addProtected(
				protectedStatesByFinallyState,
				finallyState,
				protectedState,
			);
		}
		addProtected(
			protectedStatesByFinallyState,
			finallyState,
			catchState,
		);
	}

	debug('protected lowered generator states', {
		catch: [...protectedStatesByCatchState].map((
			[state, protectedStates],
		) => [state, [...protectedStates]]),
		finally: [...protectedStatesByFinallyState].map((
			[state, protectedStates],
		) => [state, [...protectedStates]]),
	});
	return { protectedStatesByCatchState, protectedStatesByFinallyState };
}

function recoveredAddressesForState(
	cases: Map<number, CaseInfo>,
	remap: Map<number, number>,
	recoveredAddressesByState: Map<number, AddressMap<BlockAddr>>,
	state: number,
) {
	const info = cases.get(state);
	if (!info) return [];
	const recoveredAddresses = recoveredAddressesByState.get(state);
	return recoveredAddresses
		? [...recoveredAddresses.values()]
		: [remap.get(info.state)].filter((addr): addr is number =>
			addr != null
		);
}

export function injectDirectHandlers(
	func: IRFunction,
	cases: Map<number, CaseInfo>,
	remap: Map<number, number>,
	protectedStates: ProtectedStateAnalysis,
	recoveredAddressesByState: Map<number, AddressMap<BlockAddr>>,
) {
	const addProtectedStates = (
		handlerState: number,
		states: Set<number>,
	) => {
		const handlerOffset = remap.get(handlerState);
		if (handlerOffset == null) return;
		const blocks: BlockAddr[] = [];
		for (const state of states) {
			for (
				const blockAddress of recoveredAddressesForState(
					cases,
					remap,
					recoveredAddressesByState,
					state,
				)
			) {
				blocks.push(blockAddress as BlockAddr);
			}
		}
		const minBlock = blocks.length > 0
			? (Math.min(...blocks) as BlockAddr)
			: undefined;
		func.exceptions.addDirectRecord(
			handlerOffset as BlockAddr,
			blocks,
			minBlock != null ? [minBlock] : [],
		);
	};

	for (
		const [catchState, states] of protectedStates
			.protectedStatesByCatchState
	) {
		addProtectedStates(catchState, states);
	}
	for (
		const [finallyState, states] of protectedStates
			.protectedStatesByFinallyState
	) {
		addProtectedStates(finallyState, states);
	}
}

function environmentLoadDeclaration(stmt: t.Statement) {
	if (!t.isVariableDeclaration(stmt)) return;
	const decl = stmt.declarations[0];
	if (!t.isVariableDeclarator(decl) || !t.isIdentifier(decl.id)) return;
	const init = decl.init;
	if (!isLoadFromEnvironmentCall(init)) return;
	return {
		name: decl.id.name,
		slot: (init.property as t.NumericLiteral).value,
	};
}

function environmentStore(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return;
	const store = storeEnvironmentCall(stmt.expression);
	if (!store || !t.isIdentifier(store.value)) return;
	return { slot: store.slot, value: store.value.name };
}

function caseCaughtExceptionAccess(info: CaseInfo, roles: StateRoles) {
	let loadsCaughtException = false;
	let preservesCaughtException = false;
	const caughtRegisters = new Set<string>();

	for (const body of caseBodies(info)) {
		for (const stmt of body) {
			const load = environmentLoadDeclaration(stmt);
			if (load?.slot === roles.caughtExceptionSlot) {
				loadsCaughtException = true;
				caughtRegisters.add(load.name);
				continue;
			}

			if (t.isVariableDeclaration(stmt)) {
				const decl = stmt.declarations[0];
				if (
					t.isVariableDeclarator(decl) &&
					t.isIdentifier(decl.id) &&
					t.isIdentifier(decl.init) &&
					caughtRegisters.has(decl.init.name)
				) {
					caughtRegisters.add(decl.id.name);
					continue;
				}
			}

			const store = environmentStore(stmt);
			if (
				store &&
				store.slot !== roles.switchSlot &&
				store.slot !== roles.exceptionHandlerSlot &&
				store.slot !== roles.caughtExceptionSlot &&
				caughtRegisters.has(store.value)
			) {
				preservesCaughtException = true;
			}
		}
	}

	return { loadsCaughtException, preservesCaughtException };
}

export function caseReadsCaughtException(info: CaseInfo, roles: StateRoles) {
	const { loadsCaughtException, preservesCaughtException } =
		caseCaughtExceptionAccess(info, roles);
	return loadsCaughtException && !preservesCaughtException;
}

function isGeneratorFinallyCandidate(
	catchInfo: CaseInfo,
	finallyInfo: CaseInfo,
	roles: StateRoles,
	finalizerCopies: FinalizerCopyAnalysis,
) {
	if (!caseReadsCaughtException(finallyInfo, roles)) return true;
	if (t.isThrowStatement(finallyInfo.terminal)) return true;
	return finalizerCopies.suspendedFinalizerStates.has(finallyInfo.state) &&
		finallyInfo.activeHandlerIndex !== catchInfo.activeHandlerIndex;
}

function suspendedFinalizerAstPrefixSignature(
	info: CaseInfo,
	roles: StateRoles,
) {
	const caughtAliases = new Set<string>();
	for (const stmt of info.body) {
		const load = environmentLoadDeclaration(stmt);
		if (load?.slot === roles.caughtExceptionSlot) {
			caughtAliases.add(load.name);
			continue;
		}
		if (!t.isVariableDeclaration(stmt)) continue;
		const declaration = stmt.declarations[0];
		if (
			t.isVariableDeclarator(declaration) &&
			t.isIdentifier(declaration.id) &&
			t.isIdentifier(declaration.init) &&
			caughtAliases.has(declaration.init.name)
		) {
			caughtAliases.add(declaration.id.name);
		}
	}
	const body = stripLoweredGeneratorEnvironmentScaffolding(
		<t.Statement[]> info.body,
		roles,
	).filter((stmt) => {
		const slot = environmentLoadDeclarationSlot(stmt) ??
			environmentStoreStatementSlot(stmt);
		if (slot === roles.caughtExceptionSlot) return false;
		if (
			t.isExpressionStatement(stmt) &&
			t.isAssignmentExpression(stmt.expression, { operator: '=' }) &&
			t.isIdentifier(stmt.expression.left) &&
			t.isIdentifier(stmt.expression.right)
		) {
			const slotOrigin = (stmt as LiftedAST<t.ExpressionStatement>).extra
				?.recoveredEnvironmentSlot ??
				(stmt.expression.left as LiftedAST<t.Identifier>).extra
					?.recoveredEnvironmentSlot;
			const valueExtra =
				(stmt.expression.right as LiftedAST<t.Identifier>).extra;
			const valueOrigin = valueExtra?.sourceRegister;
			if (
				(slotOrigin ||
					stmt.expression.left.name.startsWith('_envCell_')) &&
				(caughtAliases.has(stmt.expression.right.name) ||
					valueOrigin?.index === roles.actionRegister ||
					valueExtra?.loweredGeneratorResumeValue ||
					stmt.expression.right.name.startsWith(
						`r${roles.actionRegister}_`,
					))
			) return false;
		}
		return true;
	});
	const nodes = [...body, info.terminal].map((node) => comparableAst(node));
	return JSON.stringify(nodes);
}

export function synthesizeFinallyRecords(
	func: IRFunction,
	cases: Map<number, CaseInfo>,
	roles: StateRoles,
	remap: Map<number, number>,
	finalizerCopies: FinalizerCopyAnalysis,
	embeddedSplitByFinallyState: Map<number, EmbeddedFinallySplit>,
	embeddedSplitAddresses: Map<EmbeddedFinallySplit, EmbeddedSplitAddresses>,
) {
	const declinedStates = new Set(
		finalizerCopies.declines.map((decline) => decline.state),
	);
	const handlerStates = new Set(roles.handlerIndexToState.values());
	for (
		const finalizerState of finalizerCopies.suspendedFinalizerStates
	) {
		const info = cases.get(finalizerState);
		const bodyStates = finalizerCopies.bodyStatesByFinalizerState.get(
			finalizerState,
		);
		let completionInfo = info;
		const seenCompletions = new Set<number>();
		while (completionInfo && !seenCompletions.has(completionInfo.state)) {
			seenCompletions.add(completionInfo.state);
			const continuation = caseContinuation(completionInfo);
			if (continuation.kind !== 'unique') break;
			const next = cases.get(continuation.state);
			if (!next) break;
			completionInfo = next;
		}
		if (
			!info ||
			info.activeHandlerIndex != null ||
			!handlerStates.has(finalizerState) ||
			!t.isThrowStatement(completionInfo?.terminal)
		) continue;
		const finallyOffset = remap.get(finalizerState);
		if (
			finallyOffset == null ||
			!func.exceptions.records.has(finallyOffset)
		) continue;
		const finallyRecord =
			func.exceptions.finallyRecords.get(finallyOffset) ??
				new FinallyRecord(finallyOffset);
		const bodyBlocks = bodyStates!.map((state) => remap.get(state))
			.filter((address): address is number => address != null);
		if (bodyBlocks.length > 0) {
			finallyRecord.bodyBlocks = bodyBlocks as BlockAddr[];
		}
		for (
			const [state, limit] of finalizerCopies
				.bodyStateStatementLimitsByFinalizerState.get(finalizerState) ??
				[]
		) {
			const address = remap.get(state);
			if (address != null) {
				finallyRecord.bodyBlockStatementLimits.set(
					address as BlockAddr,
					limit,
				);
			}
		}
		for (
			const copyRootState
				of finalizerCopies.copyRootsByFinalizerState.get(
					finalizerState,
				) ?? []
		) {
			const copyRootOffset = remap.get(copyRootState);
			if (copyRootOffset != null && copyRootOffset !== finallyOffset) {
				finallyRecord.copyRoots.add(copyRootOffset);
			}
		}
		func.exceptions.finallyRecords.set(finallyOffset, finallyRecord);
	}
	for (const catchState of roles.handlerIndexToState.values()) {
		const catchInfo = cases.get(catchState);
		if (catchInfo?.activeHandlerIndex == null) continue;
		if (declinedStates.has(catchState)) continue;

		const finallyState = roles.handlerIndexToState.get(
			catchInfo.activeHandlerIndex,
		);
		if (finallyState == null || !cases.has(finallyState)) continue;
		const finallyInfo = cases.get(finallyState)!;
		if (declinedStates.has(finallyState)) continue;
		if (
			!caseReadsCaughtException(catchInfo, roles) ||
			!isGeneratorFinallyCandidate(
				catchInfo,
				finallyInfo,
				roles,
				finalizerCopies,
			)
		) continue;

		const catchOffset = remap.get(catchState);
		const finallyOffset = remap.get(finallyState);
		if (catchOffset == null || finallyOffset == null) continue;

		const catchRecord = func.exceptions.records.get(catchOffset);
		if (!catchRecord) continue;
		catchRecord.canonicalFinallyAddress = finallyOffset;
		if (catchOffset !== finallyOffset) {
			func.exceptions.finallyRecords.delete(catchOffset);
		}

		const finallyRecord =
			func.exceptions.finallyRecords.get(finallyOffset) ??
				new FinallyRecord(finallyOffset);
		finallyRecord.isReturnOverride = t.isReturnStatement(
			finallyInfo.terminal,
		);
		const catchContinuation = caseContinuation(catchInfo);
		const trailerOffset = catchContinuation.kind === 'unique'
			? remap.get(catchContinuation.state)
			: null;
		if (trailerOffset != null) {
			finallyRecord.catchTrailer = { start: trailerOffset, end: null };
		}
		const bodyStates = finalizerCopies.bodyStatesByFinalizerState.get(
			finallyState,
		);
		if (bodyStates != null) {
			const bodyBlocks = bodyStates.map((state) => remap.get(state))
				.filter((addr): addr is number => addr != null);
			if (bodyBlocks.length > 0) {
				finallyRecord.bodyBlocks = bodyBlocks as BlockAddr[];
			}
			const limits = finalizerCopies
				.bodyStateStatementLimitsByFinalizerState.get(finallyState);
			if (limits != null) {
				for (const [state, limit] of limits) {
					const addr = remap.get(state);
					if (addr != null) {
						finallyRecord.bodyBlockStatementLimits.set(
							addr as BlockAddr,
							limit,
						);
					}
				}
			}
		}
		const split = embeddedSplitByFinallyState.get(finallyState);
		const splitAddresses = split == null
			? null
			: embeddedSplitAddresses.get(split);
		if (splitAddresses != null) {
			const bodyBlocks = finallyRecord.bodyBlocks == null
				? [finallyOffset as BlockAddr]
				: [...finallyRecord.bodyBlocks];
			if (!bodyBlocks.includes(finallyOffset as BlockAddr)) {
				bodyBlocks.unshift(finallyOffset as BlockAddr);
			}
			if (!bodyBlocks.includes(splitAddresses.finallyContinuation)) {
				bodyBlocks.push(splitAddresses.finallyContinuation);
			}
			finallyRecord.bodyBlocks = bodyBlocks;
		}
		for (
			const copyRootState
				of finalizerCopies.copyRootsByFinalizerState.get(
					finallyState,
				) ?? []
		) {
			const copyRootOffset = remap.get(copyRootState);
			if (copyRootOffset != null && copyRootOffset !== finallyOffset) {
				finallyRecord.copyRoots.add(copyRootOffset);
			}
		}
		func.exceptions.finallyRecords.set(finallyOffset, finallyRecord);
	}
}
