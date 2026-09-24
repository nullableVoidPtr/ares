import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import { AddressGraph } from '../../../utils/graph.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import type { IRBlock, LiftedAST } from '../../ast/mod.ts';
import type { IRFunction } from '../mod.ts';
import { FinallyRecord, HandlerGraph } from '../except/mod.ts';
import {
	caseEndsControlFlow,
	yieldExpressionStatementValue,
} from './caseUtils.ts';
import {
	analyseProtectedStates,
	caseReadsCaughtException,
	injectDirectHandlers,
	loweredStatementsEqual,
	synthesizeFinallyRecords,
} from './finalizerAnalysis.ts';
import { makeCatchStatement } from './environmentScaffolding.ts';
import {
	traceRecoveredDuplicateRegisterDeclarations,
} from './recoveredCleanup.ts';
import type {
	CaseInfo,
	EmbeddedFinallySplit,
	EmbeddedSplitAddresses,
	LoweredGeneratorBuildPlan,
	LoweredGeneratorModel,
} from './types.ts';

interface RecoveredGeneratorLayout {
	embeddedSplitByCatchState: Map<number, EmbeddedFinallySplit>;
	embeddedSplitByFinallyState: Map<number, EmbeddedFinallySplit>;
	embeddedSplitAddresses: Map<EmbeddedFinallySplit, EmbeddedSplitAddresses>;
	handlerTargets: Set<number>;
}

function buildRecoveredGeneratorLayout(
	model: LoweredGeneratorModel,
): RecoveredGeneratorLayout {
	const embeddedSplitByCatchState = new Map(
		model.embeddedFinallySplits.map((split) => [
			split.catchState,
			split,
		]),
	);
	const embeddedSplitByFinallyState = new Map(
		model.embeddedFinallySplits.map((split) => [
			split.finallyState,
			split,
		]),
	);
	const embeddedSplitAddresses = new Map<
		EmbeddedFinallySplit,
		EmbeddedSplitAddresses
	>();
	let nextSyntheticAddress = recoveredCaseBlockCount(model) as BlockAddr;
	for (const split of model.embeddedFinallySplits) {
		const catchInfo = model.cases.get(split.catchState)!;
		const hasCatchRemainder =
			catchInfo.body.length > split.catchCopyStart + split.prefixLength;
		embeddedSplitAddresses.set(split, {
			finallyContinuation: nextSyntheticAddress++ as BlockAddr,
			catchCopy: nextSyntheticAddress++ as BlockAddr,
			catchRemainder: hasCatchRemainder
				? nextSyntheticAddress++ as BlockAddr
				: null,
		});
	}
	const handlerTargets = new Set([
		...model.roles.handlerIndexToState.values(),
	]);

	return {
		embeddedSplitByCatchState,
		embeddedSplitByFinallyState,
		embeddedSplitAddresses,
		handlerTargets,
	};
}

function recoveredCaseBlockCount(model: LoweredGeneratorModel) {
	const stateEntries = new Set<BlockAddr>();
	const subBlocks = new Set<BlockAddr>();
	for (const state of model.order) {
		const info = model.cases.get(state)!;
		stateEntries.add(info.address);
		if (info.blocks) {
			for (const address of info.blocks.keys()) subBlocks.add(address);
		}
	}
	let extra = 0;
	for (const address of subBlocks) {
		if (!stateEntries.has(address)) extra++;
	}
	return model.order.length + extra;
}

function allocateRecoveredCaseAddresses(
	model: LoweredGeneratorModel,
): Map<number, AddressMap<BlockAddr>> {
	let nextAddress = model.order.length as BlockAddr;
	const sharedRecovered = new AddressMap<BlockAddr>();
	const recoveredAddressesByState = new Map<
		number,
		AddressMap<BlockAddr>
	>();
	for (const state of model.order) {
		const info = model.cases.get(state)!;
		const recovered = new AddressMap<BlockAddr>();
		let entryAddress = sharedRecovered.get(info.address);
		if (entryAddress == null) {
			entryAddress = model.remap.get(state)!;
			sharedRecovered.set(info.address, entryAddress);
		}
		recovered.set(info.address, entryAddress);
		if (info.blocks) {
			for (const address of info.blocks.keys()) {
				if (address === info.address) continue;
				let recoveredAddress = sharedRecovered.get(address);
				if (recoveredAddress == null) {
					recoveredAddress = nextAddress++;
					sharedRecovered.set(address, recoveredAddress);
				}
				recovered.set(address, recoveredAddress);
			}
		}
		recoveredAddressesByState.set(state, recovered);
	}
	return recoveredAddressesByState;
}

function remapBranchTargets(
	body: t.Statement[],
	addresses: AddressMap<BlockAddr>,
) {
	const wrapped = t.file(t.program(body));
	traverse(wrapped, {
		CallExpression(path: NodePath<t.CallExpression>) {
			if (!t.isV8IntrinsicIdentifier(path.node.callee)) return;
			if (
				path.node.callee.name !== 'jmpIf' &&
				path.node.callee.name !== 'UIntSwitchImm'
			) return;
			for (const arg of path.node.arguments) {
				if (!t.isNumericLiteral(arg)) continue;
				const mapped = addresses.get(arg.value as BlockAddr);
				if (mapped != null) arg.value = mapped;
			}
		},
	});
	return wrapped.program.body;
}

function planRecoveredGeneratorCFG(
	model: LoweredGeneratorModel,
): LoweredGeneratorBuildPlan {
	const {
		roles,
		cases,
		order,
		remap,
		embeddedFinallySplits,
		preludeBody,
		finalizerCopies,
	} = model;
	const recoveredAddressesByState = allocateRecoveredCaseAddresses(model);
	const {
		embeddedSplitByCatchState,
		embeddedSplitByFinallyState,
		embeddedSplitAddresses,
		handlerTargets,
	} = buildRecoveredGeneratorLayout(model);

	const blocks = new AddressMap<IRBlock>();
	const mergedBlocks = new AddressGraph();
	const mappedNextAddress = (info: CaseInfo) => {
		const nextState = info.nextState == null
			? null
			: finalizerCopies.successorRedirects.get(info.nextState) ??
				info.nextState;
		return nextState == null ? null : remap.get(nextState) ?? null;
	};
	for (const state of order) {
		const info = cases.get(state)!;
		const address = remap.get(state)!;
		const catchSplit = embeddedSplitByCatchState.get(state);
		const finallySplit = embeddedSplitByFinallyState.get(state);
		if (info.blocks && !catchSplit && !finallySplit) {
			const activeHandlerState = info.activeHandlerIndex == null ||
					info.activeHandlerIndex === 0
				? null
				: roles.handlerIndexToState.get(info.activeHandlerIndex) ??
					null;
			for (const [rawAddress, blockInfo] of info.blocks) {
				const recoveredAddresses = recoveredAddressesByState.get(
					state,
				)!;
				const recoveredAddress = recoveredAddresses.get(
					rawAddress,
				)!;
				if (blocks.has(recoveredAddress)) continue;
				const body = remapBranchTargets(
					blockInfo.body.map((stmt) => t.cloneNode(stmt, true)),
					recoveredAddresses,
				);
				if (rawAddress === info.address && state === 0) {
					body.unshift(
						...preludeBody.map((stmt) => t.cloneNode(stmt, true)),
					);
				}
				if (
					rawAddress === info.address &&
					handlerTargets.has(state) &&
					caseReadsCaughtException(info, roles)
				) body.unshift(makeCatchStatement(recoveredAddress));
				const blockEndsWithYield =
					yieldExpressionStatementValue(body.at(-1)) != null;
				const suppressYieldSuccessor = blockEndsWithYield &&
					blockInfo.nextState === info.state &&
					info.state === 0;
				const successorAddresses = blockInfo.terminal ||
						suppressYieldSuccessor
					? []
					: blockInfo.consequentAddresses
						.map((succ) => recoveredAddresses.get(succ))
						.filter((succ): succ is BlockAddr => succ != null);
				if (
					successorAddresses.length === 0 &&
					(!blockInfo.terminal ||
						!caseEndsControlFlow(blockInfo.terminal))
				) {
					const blockNextState = suppressYieldSuccessor
						? undefined
						: blockInfo.nextState;
					const nextAddress = blockNextState === undefined
						? mappedNextAddress(info)
						: blockNextState === null
						? null
						: remap.get(
							finalizerCopies.successorRedirects.get(
								blockNextState,
							) ?? blockNextState,
						) ?? null;
					if (nextAddress != null) {
						successorAddresses.push(nextAddress);
					}
				}
				blocks.set(recoveredAddress, {
					address: recoveredAddress,
					sourceAddresses: new AddressSet([rawAddress]),
					body,
					branch: blockInfo.branch
						? t.cloneNode(blockInfo.branch, true)
						: undefined,
					consequentAddresses: successorAddresses,
					kind:
						handlerTargets.has(state) && rawAddress === info.address
							? 'catch'
							: 'generatorCase',
					generatorState: state,
					activeHandlerState,
					pairedFinallyState: null,
					terminalKind: blockInfo.terminal
						? !caseEndsControlFlow(blockInfo.terminal)
							? 'fallthrough'
							: t.isThrowStatement(blockInfo.terminal)
							? 'throw'
							: 'return'
						: 'fallthrough',
				});
				mergedBlocks.set(
					recoveredAddress,
					new AddressSet([recoveredAddress, rawAddress]),
				);
			}
			continue;
		}
		const splitAddresses = catchSplit
			? embeddedSplitAddresses.get(catchSplit)
			: finallySplit
			? embeddedSplitAddresses.get(finallySplit)
			: undefined;
		const bodySource = catchSplit
			? info.body.slice(0, catchSplit.catchCopyStart)
			: finallySplit
			? info.body.slice(0, finallySplit.prefixLength)
			: info.body;
		const body = bodySource.map((stmt) => t.cloneNode(stmt, true));
		if (state === 0) {
			body.unshift(...preludeBody.map((stmt) => t.cloneNode(stmt, true)));
		}
		if (
			handlerTargets.has(state) && caseReadsCaughtException(info, roles)
		) body.unshift(makeCatchStatement(address));
		const nextAddress = catchSplit
			? splitAddresses!.catchCopy
			: finallySplit
			? splitAddresses!.finallyContinuation
			: mappedNextAddress(info);
		const activeHandlerState = info.activeHandlerIndex == null ||
				info.activeHandlerIndex === 0
			? null
			: roles.handlerIndexToState.get(info.activeHandlerIndex) ?? null;
		const succAddresses =
			nextAddress != null && !caseEndsControlFlow(info.terminal)
				? [nextAddress]
				: [];
		blocks.set(address, {
			address,
			sourceAddresses: new AddressSet([info.address]),
			body,
			consequentAddresses: succAddresses,
			kind: handlerTargets.has(state)
				? 'catch'
				: finallySplit
				? 'finally'
				: 'generatorCase',
			generatorState: state,
			activeHandlerState,
			pairedFinallyState: catchSplit?.finallyState ?? null,
			recoveredFinalizerOwner: finallySplit ? address : undefined,
			recoveredFinalizerRole: finallySplit ? 'canonical' : undefined,
			terminalKind: t.isThrowStatement(info.terminal)
				? 'throw'
				: t.isReturnStatement(info.terminal)
				? 'return'
				: nextAddress == null
				? 'return'
				: 'fallthrough',
		});
		mergedBlocks.set(address, new AddressSet([address, info.address]));
	}

	for (const split of embeddedFinallySplits) {
		const addresses = embeddedSplitAddresses.get(split)!;
		const catchInfo = cases.get(split.catchState)!;
		const finallyInfo = cases.get(split.finallyState)!;
		const finallyOffset = remap.get(split.finallyState);
		const catchNextAddress = mappedNextAddress(catchInfo);
		const finallyNextAddress = mappedNextAddress(finallyInfo);

		const finalizerContinuationBody = finallyInfo.body.slice(
			split.prefixLength,
		).map((stmt) => t.cloneNode(stmt, true));
		blocks.set(addresses.finallyContinuation, {
			address: addresses.finallyContinuation,
			body: finalizerContinuationBody,
			consequentAddresses: finallyNextAddress != null &&
					!caseEndsControlFlow(finallyInfo.terminal)
				? [finallyNextAddress]
				: [],
			kind: 'synthetic',
			syntheticReason: 'embedded-finally-continuation',
			generatorState: split.finallyState,
			pairedFinallyState: split.finallyState,
			recoveredFinalizerOwner: finallyOffset as BlockAddr | undefined,
			recoveredFinalizerRole: 'continuation',
			terminalKind: caseEndsControlFlow(finallyInfo.terminal)
				? t.isThrowStatement(finallyInfo.terminal) ? 'throw' : 'return'
				: 'fallthrough',
		});
		mergedBlocks.set(
			addresses.finallyContinuation,
			new AddressSet([addresses.finallyContinuation]),
		);

		const catchCopyNext = addresses.catchRemainder ?? catchNextAddress;
		blocks.set(addresses.catchCopy, {
			address: addresses.catchCopy,
			body: catchInfo.body.slice(
				split.catchCopyStart,
				split.catchCopyStart + split.prefixLength,
			).map((stmt) => t.cloneNode(stmt, true)),
			consequentAddresses: catchCopyNext != null ? [catchCopyNext] : [],
			kind: 'synthetic',
			syntheticReason: 'embedded-finally-catch-copy',
			generatorState: split.catchState,
			pairedFinallyState: split.finallyState,
			recoveredFinalizerOwner: finallyOffset as BlockAddr | undefined,
			recoveredFinalizerRole: 'catchCopy',
			terminalKind: catchCopyNext == null ? 'return' : 'fallthrough',
		});
		mergedBlocks.set(
			addresses.catchCopy,
			new AddressSet([addresses.catchCopy]),
		);

		if (addresses.catchRemainder != null) {
			blocks.set(addresses.catchRemainder, {
				address: addresses.catchRemainder,
				body: catchInfo.body.slice(
					split.catchCopyStart + split.prefixLength,
				).map((stmt) => t.cloneNode(stmt, true)),
				consequentAddresses: catchNextAddress != null &&
						!caseEndsControlFlow(catchInfo.terminal)
					? [catchNextAddress]
					: [],
				kind: 'synthetic',
				syntheticReason: 'embedded-finally-catch-remainder',
				generatorState: split.catchState,
				pairedFinallyState: split.finallyState,
				recoveredFinalizerOwner: finallyOffset as BlockAddr | undefined,
				recoveredFinalizerRole: 'catchRemainder',
				terminalKind: caseEndsControlFlow(catchInfo.terminal)
					? t.isThrowStatement(catchInfo.terminal)
						? 'throw'
						: 'return'
					: 'fallthrough',
			});
			mergedBlocks.set(
				addresses.catchRemainder,
				new AddressSet([addresses.catchRemainder]),
			);
		}
	}

	const protectedStates = analyseProtectedStates(
		cases,
		roles,
		remap,
		finalizerCopies,
	);
	return {
		embeddedSplitByFinallyState,
		embeddedSplitAddresses,
		recoveredAddressesByState,
		blocks,
		mergedBlocks,
		protectedStates,
	};
}

/**
 * Hermes duplicates a suspension at a try/catch join because each state-machine
 * case needs its own terminal. Recreate the shared CFG tail before Region
 * structuring so the suspension is emitted after the try/catch rather than once
 * in each arm.
 */
function mergeEquivalentSuspendedTerminals(
	func: IRFunction,
	model: LoweredGeneratorModel,
) {
	const { roles, finalizerCopies } = model;
	const candidates = [...func.blocks.values()].filter((block) =>
		block.branch == null &&
		block.consequentAddresses.length === 1 &&
		block.recoveredFinalizerRole == null &&
		(block.generatorState == null ||
			(!finalizerCopies.finalizerStates.has(block.generatorState) &&
				!finalizerCopies.suspendedFinalizerStates.has(
					block.generatorState,
				))) &&
		yieldExpressionStatementValue(
				(block.body as t.Statement[]).at(-1),
			) != null
	);
	const consumed = new Set<BlockAddr>();
	let nextAddress = Math.max(0, ...func.blocks.keys()) + 1;
	for (const seed of candidates) {
		const seedTerminal = (seed.body as t.Statement[]).at(-1)!;
		const successor = seed.consequentAddresses[0];
		const group = candidates.filter((candidate) =>
			!consumed.has(candidate.address) &&
			candidate.consequentAddresses[0] === successor &&
			loweredStatementsEqual(
				seedTerminal,
				(candidate.body as t.Statement[]).at(-1)!,
				roles,
			)
		);
		if (group.length < 2) continue;
		const crossesCatchBoundary = group.some((left) =>
			group.some((right) =>
				left !== right &&
				(func.exceptions.isCatchTarget(left.address) ||
					func.exceptions.isCatchTarget(right.address)) &&
				!func.exceptions.activeHandlersEqual(
					left.address,
					right.address,
				)
			)
		);
		if (!crossesCatchBoundary) continue;

		const address = nextAddress++ as BlockAddr;
		func.blocks.set(address, {
			address,
			body: [
				t.cloneNode(seedTerminal, true) as LiftedAST<t.Statement>,
			],
			consequentAddresses: [successor],
			kind: 'synthetic',
			syntheticReason: 'merged-generator-suspended-terminal',
			terminalKind: 'fallthrough',
		});
		func.mergedBlocks.set(address, new AddressSet([address]));
		for (const block of group) {
			block.body = block.body.slice(0, -1);
			block.consequentAddresses = [address];
			block.terminalKind = 'fallthrough';
			consumed.add(block.address);
		}
	}
}

function applyRecoveredGeneratorCFGPlan(
	func: IRFunction,
	model: LoweredGeneratorModel,
	plan: LoweredGeneratorBuildPlan,
): void {
	const {
		roles,
		cases,
		remap,
		embeddedFinallySplits,
		finalizerCopies,
	} = model;
	const {
		embeddedSplitByFinallyState,
		embeddedSplitAddresses,
		recoveredAddressesByState,
		blocks,
		mergedBlocks,
		protectedStates,
	} = plan;

	func.blocks = blocks;
	func.mergedBlocks = mergedBlocks;
	func._exceptionHandlers = [];
	func.exceptions = new HandlerGraph(func);
	injectDirectHandlers(
		func,
		cases,
		remap,
		protectedStates,
		recoveredAddressesByState,
	);
	for (const split of embeddedFinallySplits) {
		const finallyInfo = cases.get(split.finallyState)!;
		const addresses = embeddedSplitAddresses.get(split)!;
		let activeHandlerIndex = finallyInfo.activeHandlerIndex;
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
			func.exceptions.addDirectRecord(
				catchOffset as BlockAddr,
				[addresses.finallyContinuation as BlockAddr],
				[addresses.finallyContinuation as BlockAddr],
			);
			activeHandlerIndex = cases.get(catchState)!.activeHandlerIndex;
		}
	}
	synthesizeFinallyRecords(
		func,
		cases,
		roles,
		remap,
		finalizerCopies,
		embeddedSplitByFinallyState,
		embeddedSplitAddresses,
	);
	for (const split of embeddedFinallySplits) {
		const catchOffset = remap.get(split.catchState);
		const finallyOffset = remap.get(split.finallyState);
		const addresses = embeddedSplitAddresses.get(split);
		if (catchOffset == null || finallyOffset == null || !addresses) {
			continue;
		}

		const catchRecord = func.exceptions.records.get(catchOffset);
		if (!catchRecord) continue;
		catchRecord.canonicalFinallyAddress = finallyOffset;
		const finallyRecord =
			func.exceptions.finallyRecords.get(finallyOffset) ??
				new FinallyRecord(finallyOffset);
		finallyRecord.catchTrailer = { start: addresses.catchCopy, end: null };
		finallyRecord.copyRoots.add(addresses.catchCopy);
		const bodyBlocks = finallyRecord.bodyBlocks == null
			? [finallyOffset as BlockAddr]
			: [...finallyRecord.bodyBlocks];
		if (!bodyBlocks.includes(finallyOffset as BlockAddr)) {
			bodyBlocks.unshift(finallyOffset as BlockAddr);
		}
		if (!bodyBlocks.includes(addresses.finallyContinuation)) {
			bodyBlocks.push(addresses.finallyContinuation);
		}
		finallyRecord.bodyBlocks = bodyBlocks;
		func.exceptions.finallyRecords.set(finallyOffset, finallyRecord);

		if (addresses.catchRemainder != null) {
			const catchInfo = cases.get(split.catchState)!;
			const remainder = catchInfo.body.slice(
				split.catchCopyStart + split.prefixLength,
			);
			for (const finalizerState of finalizerCopies.finalizerStates) {
				const finalizerInfo = cases.get(finalizerState);
				const outerFinallyOffset = remap.get(finalizerState);
				if (!finalizerInfo || outerFinallyOffset == null) continue;
				if (remainder.length < finalizerInfo.body.length) continue;
				let matches = true;
				for (let i = 0; i < finalizerInfo.body.length; i++) {
					if (
						!loweredStatementsEqual(
							remainder[i],
							finalizerInfo.body[i],
							roles,
						)
					) {
						matches = false;
						break;
					}
				}
				if (!matches) continue;
				const outerFinallyRecord =
					func.exceptions.finallyRecords.get(outerFinallyOffset) ??
						new FinallyRecord(outerFinallyOffset);
				outerFinallyRecord.copyRoots.add(addresses.catchRemainder);
				func.exceptions.finallyRecords.set(
					outerFinallyOffset,
					outerFinallyRecord,
				);
				break;
			}
		}
	}
	mergeEquivalentSuspendedTerminals(func, model);

	func.rebuildPredecessorMap();
	traceRecoveredDuplicateRegisterDeclarations(
		func,
		'after-build-before-threading',
	);
	const fallthrough = new AddressMap<BlockAddr>();
	for (const block of func.blocks.values()) {
		if (block.address === 0) continue;
		if (block.body.length > 0) continue;
		if (block.branch) continue;
		if (block.consequentAddresses.length !== 1) continue;
		if (func.exceptions.isCatchTarget(block.address)) continue;
		if (
			!func.exceptions.activeHandlersEqual(
				block.address,
				block.consequentAddresses[0],
			)
		) continue;
		if (
			![...func.predecessorsOf(block.address)].every((p) =>
				func.exceptions.activeHandlersEqual(block.address, p)
			)
		) {
			continue;
		}

		fallthrough.set(block.address, block.consequentAddresses[0]);
	}

	const threads = new AddressMap<BlockAddr>();
	for (const [src, target] of fallthrough) {
		let newTarget = fallthrough.get(target);
		if (newTarget == null) {
			threads.set(src, target);
			continue;
		}

		const visited = new AddressSet([target, newTarget]);
		while (fallthrough.has(newTarget)) {
			newTarget = fallthrough.get(newTarget)!;
			if (visited.has(newTarget)) throw new Error();
		}

		threads.set(src, newTarget);
	}

	for (const predecessor of func.blocks.values()) {
		predecessor.consequentAddresses = predecessor.consequentAddresses
			.flatMap((consequent) => {
				return threads.get(consequent) ?? consequent;
			});

		if (
			predecessor.consequentAddresses.length === 2 &&
			predecessor.consequentAddresses[0] ===
				predecessor.consequentAddresses[1]
		) {
			predecessor.consequentAddresses = [
				predecessor.consequentAddresses[0],
			];
			predecessor.branch = undefined;
		}
	}

	for (const block of fallthrough.keys()) {
		func.blocks.delete(block);
	}

	traceRecoveredDuplicateRegisterDeclarations(
		func,
		'after-build-after-threading',
	);
	func.isGenerator = true;
	func.isLoweredGenerator = true;
}

export function buildRecoveredGeneratorCFG(
	func: IRFunction,
	model: LoweredGeneratorModel,
): void {
	const plan = planRecoveredGeneratorCFG(model);
	applyRecoveredGeneratorCFGPlan(func, model, plan);
}
