import * as t from '@babel/types';
import traverse from '@babel/traverse';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import { isAbruptStatement } from '../../ast/completion.ts';
import { nodeHasDelegateYield } from '../../ast/effects.ts';
import type { IRBlock } from '../../ast/mod.ts';
import type { IRFunction } from '../mod.ts';
import { statementMatchesFinalizerPrefix } from '../finalizer.ts';
import {
	blockContainsIntrinsic,
	isIteratorCloseRethrowBody,
	isSharedIteratorCloseRethrowTail,
	isSyntheticIteratorCleanupCatchBody,
	reduceSequence,
	replaceCatchCallsWithIdentifier,
	statementMatchesFinalizerCopy,
	stripFinalizerPrefixSuffix,
} from './linear.ts';

function pickPreferredBodyBlock(
	func: IRFunction,
	bodyBlocks: Set<BlockAddr>,
): IRBlock | null {
	const liveBlocks: IRBlock[] = [];
	const entryBlocks: IRBlock[] = [];
	const terminalBlocks: IRBlock[] = [];
	for (const addr of bodyBlocks) {
		const block = func.blocks.get(addr);
		if (!block) continue;
		liveBlocks.push(block);
		const isCatchTarget = func.exceptions.isCatchTarget(addr);
		if (!isCatchTarget && block.consequentAddresses.length !== 0) {
			entryBlocks.push(block);
		} else if (block.consequentAddresses.length === 0) {
			terminalBlocks.push(block);
		}
	}
	const hasLiveCatchTarget = [...bodyBlocks].some((addr) =>
		func.blocks.has(addr) &&
		func.exceptions.isCatchTarget(addr)
	);
	if (!hasLiveCatchTarget && entryBlocks.length > 0) return entryBlocks[0];
	if (terminalBlocks.length > 0) {
		terminalBlocks.sort((left, right) => {
			const predDelta = func.predecessorsOf(right.address).size -
				func.predecessorsOf(left.address).size;
			if (predDelta !== 0) return predDelta;
			return right.address - left.address;
		});
		return terminalBlocks[0];
	}
	return liveBlocks[0] ?? null;
}

function pickFirstLiveBodyBlock(
	func: IRFunction,
	bodyBlocks: Set<BlockAddr>,
): IRBlock | null {
	for (const addr of bodyBlocks) {
		const block = func.blocks.get(addr);
		if (block) return block;
	}
	return null;
}

function canonicalFinalizerPrefix(
	func: IRFunction,
	finallyAddr: BlockAddr,
): t.Statement[] {
	const block = func.blocks.get(finallyAddr);
	if (!block) return [];
	let body = <t.Statement[]> block.body.slice();
	const catchInstIndex = body.findIndex((stmt) => {
		if (!t.isVariableDeclaration(stmt, { kind: 'const' })) return false;
		const [decl] = stmt.declarations;
		return t.isVariableDeclarator(decl) &&
			t.isCallExpression(decl.init) &&
			t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Catch' });
	});
	if (catchInstIndex !== -1) body.splice(catchInstIndex, 1);
	if (t.isThrowStatement(body.at(-1))) body = body.slice(0, -1);
	return body;
}

function completeFinalizerBodyFromBlock(
	func: IRFunction,
	finallyAddr: BlockAddr,
): t.Statement[] | null {
	const block = func.blocks.get(finallyAddr);
	if (!block || block.consequentAddresses.length !== 0) return null;
	const body = canonicalFinalizerPrefix(func, finallyAddr);
	if (body.length === 0) return null;
	return body.map((stmt) => t.cloneNode(stmt, true));
}

function collectLinearFinalizerCopyBody(
	func: IRFunction,
	startAddr: BlockAddr,
	isReturnOverride: boolean,
): {
	body: t.Statement[];
	mergedBlocks: BlockAddr[];
	successor: BlockAddr[];
} | null {
	let cursor: BlockAddr | undefined = startAddr;
	const visited = new AddressSet<BlockAddr>();
	const body: t.Statement[] = [];
	const mergedBlocks: BlockAddr[] = [];
	let successor: BlockAddr[] = [];

	while (cursor !== undefined) {
		if (visited.has(cursor)) return null;
		visited.add(cursor);

		const block = func.blocks.get(cursor);
		if (!block) return null;
		body.push(
			...(<t.Statement[]> block.body).map((stmt) =>
				t.cloneNode(stmt, true)
			),
		);
		mergedBlocks.push(cursor);

		if (block.consequentAddresses.length === 0) {
			successor = [];
			break;
		}
		if (block.consequentAddresses.length !== 1) return null;

		const [nextAddr] = block.consequentAddresses;
		if (func.exceptions.isCatchTarget(nextAddr)) {
			successor = [nextAddr];
			break;
		}
		if (func.predecessorsOf(nextAddr).size !== 1) {
			successor = [nextAddr];
			break;
		}

		cursor = nextAddr;
	}

	if (!isReturnOverride && successor.length === 0) {
		if (t.isReturnStatement(body.at(-1))) body.pop();
	}
	if (body.length === 0) return null;

	return { body, mergedBlocks, successor };
}

function collectModeledFinalizerBody(
	func: IRFunction,
	bodyBlocks: BlockAddr[] | null | undefined,
	statementLimits: Map<BlockAddr, number>,
	isReturnOverride: boolean,
): {
	body: t.Statement[];
	mergedBlocks: BlockAddr[];
	successor: BlockAddr[];
} | null {
	if (bodyBlocks == null || bodyBlocks.length === 0) return null;
	const body: t.Statement[] = [];
	const mergedBlocks: BlockAddr[] = [];
	for (const addr of bodyBlocks) {
		const block = func.blocks.get(addr);
		if (!block) return null;
		const statementLimit = statementLimits.get(addr);
		const blockBody = <t.Statement[]> block.body;
		const finalizerStatements = statementLimit == null
			? blockBody
			: blockBody.slice(0, statementLimit);
		body.push(
			...finalizerStatements.map((stmt) =>
				t.cloneNode(stmt, true)
			),
		);
		mergedBlocks.push(addr);
		if (statementLimit != null && blockBody.length > statementLimit) {
			const nextAddr = (Math.max(...func.blocks.keys()) + 1) as BlockAddr;
			func.blocks.set(nextAddr, {
				address: nextAddr,
				body: blockBody.slice(statementLimit),
				branch: block.branch,
				consequentAddresses: [...block.consequentAddresses],
			});
			func.mergedBlocks.set(nextAddr, new AddressSet([nextAddr]));
			return { body, mergedBlocks, successor: [nextAddr] };
		}
	}
	const lastBlock = func.blocks.get(bodyBlocks.at(-1)!);
	const successor = lastBlock?.consequentAddresses ?? [];
	if (!isReturnOverride && successor.length === 0) {
		if (t.isReturnStatement(body.at(-1))) body.pop();
	}
	if (body.length === 0) return null;
	return { body, mergedBlocks, successor };
}

function splitFinalizerCopyRemainder(
	func: IRFunction,
	finallyAddr: BlockAddr,
	block: IRBlock,
): BlockAddr | null {
	const prefix = canonicalFinalizerPrefix(func, finallyAddr);
	if (prefix.length === 0 || block.body.length <= prefix.length) {
		return null;
	}
	for (let i = 0; i < prefix.length; i++) {
		if (
			!statementMatchesFinalizerCopy(
				<t.Statement> block.body[i],
				prefix[i],
			)
		) {
			return null;
		}
	}

	const nextAddr = (Math.max(...func.blocks.keys()) + 1) as BlockAddr;
	const remainder = <t.Statement[]> block.body.slice(prefix.length);
	func.blocks.set(nextAddr, {
		address: nextAddr,
		body: remainder,
		branch: block.branch,
		consequentAddresses: [...block.consequentAddresses],
	});
	func.mergedBlocks.set(nextAddr, new AddressSet([nextAddr]));

	block.body = prefix;
	block.branch = undefined;
	block.consequentAddresses = [nextAddr];
	return nextAddr;
}

function finalizerCopyRemainder(
	func: IRFunction,
	finallyAddr: BlockAddr,
	block: IRBlock,
): t.Statement[] | null {
	const prefix = canonicalFinalizerPrefix(func, finallyAddr);
	if (prefix.length === 0 || block.body.length === 0) {
		return null;
	}
	const body = <t.Statement[]> block.body;
	for (let prefixStart = 0; prefixStart < prefix.length; prefixStart++) {
		const length = prefix.length - prefixStart;
		if (body.length < length) continue;
		let matches = true;
		for (let i = 0; i < length; i++) {
			if (
				!statementMatchesFinalizerCopy(
					body[i],
					prefix[prefixStart + i],
				)
			) {
				matches = false;
				break;
			}
		}
		if (!matches) continue;
		return body.slice(length).map((stmt) => t.cloneNode(stmt, true));
	}
	return null;
}

function splitTrailingFinalizerCopy(
	func: IRFunction,
	finallyAddr: BlockAddr,
	block: IRBlock,
): {
	finalizerBody: t.Statement[];
	successor: BlockAddr[];
	remainderAddr: BlockAddr | null;
} | null {
	const prefix = canonicalFinalizerPrefix(func, finallyAddr);
	if (prefix.length === 0 || block.body.length <= prefix.length) {
		return null;
	}

	const body = <t.Statement[]> block.body;
	for (let start = 1; start <= body.length - prefix.length; start++) {
		let matches = true;
		for (let i = 0; i < prefix.length; i++) {
			if (!statementMatchesFinalizerCopy(body[start + i], prefix[i])) {
				matches = false;
				break;
			}
		}
		if (!matches) continue;

		const remainder = body.slice(start + prefix.length);
		let remainderAddr: BlockAddr | null = null;
		if (remainder.length > 0 || block.consequentAddresses.length > 0) {
			remainderAddr = (Math.max(...func.blocks.keys()) + 1) as BlockAddr;
			func.blocks.set(remainderAddr, {
				address: remainderAddr,
				body: remainder,
				branch: block.branch,
				consequentAddresses: [...block.consequentAddresses],
			});
			func.mergedBlocks.set(
				remainderAddr,
				new AddressSet([remainderAddr]),
			);
		}

		block.body = body.slice(0, start);
		block.branch = undefined;
		block.consequentAddresses = remainderAddr == null
			? []
			: [remainderAddr];

		return {
			finalizerBody: prefix.map((stmt) => t.cloneNode(stmt, true)),
			successor: remainderAddr == null ? [] : [remainderAddr],
			remainderAddr,
		};
	}

	return null;
}

function splitTrailingExactFinalizerCopy(
	func: IRFunction,
	block: IRBlock,
	finalizerBody: t.Statement[],
): {
	finalizerBody: t.Statement[];
	successor: BlockAddr[];
	remainderAddr: BlockAddr | null;
} | null {
	if (finalizerBody.length === 0 || block.body.length <= finalizerBody.length) {
		return null;
	}

	const body = <t.Statement[]> block.body;
	for (let start = 1; start <= body.length - finalizerBody.length; start++) {
		let matches = true;
		for (let i = 0; i < finalizerBody.length; i++) {
			if (
				!statementMatchesFinalizerPrefix(
					body[start + i],
					finalizerBody[i],
				)
			) {
				matches = false;
				break;
			}
		}
		if (!matches) continue;

		const remainder = body.slice(start + finalizerBody.length);
		let remainderAddr: BlockAddr | null = null;
		if (remainder.length > 0 || block.consequentAddresses.length > 0) {
			remainderAddr = (Math.max(...func.blocks.keys()) + 1) as BlockAddr;
			func.blocks.set(remainderAddr, {
				address: remainderAddr,
				body: remainder,
				branch: block.branch,
				consequentAddresses: [...block.consequentAddresses],
			});
			func.mergedBlocks.set(
				remainderAddr,
				new AddressSet([remainderAddr]),
			);
		}

		block.body = body.slice(0, start);
		block.branch = undefined;
		block.consequentAddresses = remainderAddr == null
			? []
			: [remainderAddr];

		return {
			finalizerBody: finalizerBody.map((stmt) =>
				t.cloneNode(stmt, true)
			),
			successor: remainderAddr == null ? [] : [remainderAddr],
			remainderAddr,
		};
	}

	return null;
}

function hoistDelegateCompletionDeclaration(
	body: t.Statement[],
): { prelude: t.Statement[]; body: t.Statement[] } {
	if (body.length !== 1) return { prelude: [], body };
	const [stmt] = body;
	if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
		return { prelude: [], body };
	}
	const [decl] = stmt.declarations;
	if (
		!t.isVariableDeclarator(decl) ||
		!t.isIdentifier(decl.id) ||
		!t.isExpression(decl.init) ||
		!nodeHasDelegateYield(decl.init)
	) return { prelude: [], body };

	return {
		prelude: [
			t.variableDeclaration('let', [
				t.variableDeclarator(t.cloneNode(decl.id)),
			]),
		],
		body: [
			t.expressionStatement(
				t.assignmentExpression(
					'=',
					t.cloneNode(decl.id),
					t.cloneNode(decl.init, true),
				),
			),
		],
	};
}

function delegateYieldCallFromExpressionStatement(
	stmt: t.Statement | undefined,
): t.CallExpression | null {
	if (!t.isExpressionStatement(stmt)) return null;
	const expr = stmt.expression;
	if (
		t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, { name: 'DelegateYield' })
	) return expr;
	return null;
}

function replaceDelegateCompletionPhiValueReads(
	body: t.Statement[],
	name: string,
): boolean {
	let changed = false;
	const wrapped = t.file(t.program(body));
	traverse(wrapped, {
		MemberExpression(path) {
			if (memberExpressionName(path.node) !== 'value') return;
			const object = path.node.object;
			if (
				t.isCallExpression(object) &&
				t.isV8IntrinsicIdentifier(object.callee, { name: 'Phi' })
			) {
				path.replaceWith(t.identifier(name));
				changed = true;
				return;
			}
			if (t.isIdentifier(object)) {
				const binding = path.scope.getBinding(object.name);
				const bindingPath = binding?.path;
				const init = bindingPath?.isVariableDeclarator()
					? bindingPath.node.init
					: null;
				if (
					t.isCallExpression(init) &&
					t.isV8IntrinsicIdentifier(init.callee, { name: 'Phi' })
				) {
					path.replaceWith(t.identifier(name));
					changed = true;
				}
			}
		},
	});
	return changed;
}

function hoistSplitDelegateCompletion(
	tryBody: t.Statement[],
	continuation: IRBlock | undefined,
	name: string,
): { prelude: t.Statement[]; body: t.Statement[] } | null {
	if (!continuation || tryBody.length !== 1) return null;
	const delegateYield = delegateYieldCallFromExpressionStatement(tryBody[0]);
	if (!delegateYield) return null;
	if (
		!replaceDelegateCompletionPhiValueReads(
			continuation.body as t.Statement[],
			name,
		)
	) return null;
	return {
		prelude: [
			t.variableDeclaration('let', [
				t.variableDeclarator(t.identifier(name)),
			]),
		],
		body: [
			t.expressionStatement(
				t.assignmentExpression(
					'=',
					t.identifier(name),
					t.cloneNode(delegateYield, true),
				),
			),
		],
	};
}

function memberExpressionName(member: t.MemberExpression) {
	if (!member.computed && t.isIdentifier(member.property)) {
		return member.property.name;
	}
	if (member.computed && t.isStringLiteral(member.property)) {
		return member.property.value;
	}
	return null;
}

function isDiscardedCompletionValueReadBlock(block: IRBlock) {
	return block.body.length > 0 &&
		block.body.every((stmt) => {
			if (!t.isExpressionStatement(<t.Statement> stmt)) return false;
			const expr = (<t.ExpressionStatement> stmt).expression;
			return t.isMemberExpression(expr) &&
				memberExpressionName(expr) === 'value';
		});
}

export interface TryCatchReductionOptions {
	preferProtectedRegionOrder?: boolean;
	mergeSplitTryFinallyBody?: boolean;
}

interface TryCatchReductionCandidate {
	catchAddr: BlockAddr;
	bodyBlocks: AddressSet<BlockAddr>;
}

interface TryCatchReductionPlan {
	options: TryCatchReductionOptions;
	catchEntries: Map<BlockAddr, AddressSet<BlockAddr>>;
	candidates: TryCatchReductionCandidate[];
}

interface TryCatchFinallyMutationPlan {
	body: IRBlock;
	catchAddr: BlockAddr;
	finallyAddr: BlockAddr;
	errorName: string;
	catchBody: t.BlockStatement;
	tryPrelude: t.Statement[];
	tryBody: t.Statement[];
	finalizerBody: t.Statement[];
	successor: BlockAddr[];
	mergedFinallyBlocks: BlockAddr[];
	finallyHasOtherOwner: boolean;
}

interface TryFinallyMutationPlan {
	body: IRBlock;
	finallyAddr: BlockAddr;
	finalizerBody: t.Statement[];
	successor: BlockAddr[];
	mergedBlocks: BlockAddr[];
}

interface TryCatchMutationPlan {
	body: IRBlock;
	catchAddr: BlockAddr;
	errorName: string;
	catchBody: t.BlockStatement;
	successor?: BlockAddr[];
}

interface RemoveSyntheticCatchMutationPlan {
	body: IRBlock;
	catchAddr: BlockAddr;
	successor?: BlockAddr[];
}

function applyRemoveSyntheticCatchMutationPlan(
	func: IRFunction,
	plan: RemoveSyntheticCatchMutationPlan,
): void {
	if (plan.successor != null) {
		plan.body.consequentAddresses = plan.successor;
	}
	func.exceptions.removeStructuredCatchHandler(plan.catchAddr);
	func.markMergedBlocks(plan.body.address, plan.catchAddr);
}

function applyTryCatchMutationPlan(
	func: IRFunction,
	plan: TryCatchMutationPlan,
): void {
	plan.body.body = [
		t.tryStatement(
			t.blockStatement(<t.Statement[]> plan.body.body),
			t.catchClause(t.identifier(plan.errorName), plan.catchBody),
		),
	];
	if (plan.successor != null) {
		plan.body.consequentAddresses = plan.successor;
	}
	func.exceptions.removeStructuredCatchHandler(plan.catchAddr);
	func.markMergedBlocks(plan.body.address, plan.catchAddr);
}

function applyTryFinallyMutationPlan(
	func: IRFunction,
	plan: TryFinallyMutationPlan,
): void {
	plan.body.body = [t.tryStatement(
		t.blockStatement(<t.Statement[]> plan.body.body),
		null,
		t.blockStatement(plan.finalizerBody),
	)];
	plan.body.consequentAddresses = plan.successor;
	func.exceptions.removeStructuredFinallyHandler(plan.finallyAddr);
	for (const mergedAddr of plan.mergedBlocks) {
		func.markMergedBlocks(plan.body.address, mergedAddr);
	}
}

function applyTryCatchFinallyMutationPlan(
	func: IRFunction,
	plan: TryCatchFinallyMutationPlan,
): void {
	plan.body.body = [
		...plan.tryPrelude,
		t.tryStatement(
			t.blockStatement(plan.tryBody),
			t.catchClause(t.identifier(plan.errorName), plan.catchBody),
			t.blockStatement(plan.finalizerBody),
		),
	];
	plan.body.consequentAddresses = plan.successor;

	if (plan.finallyHasOtherOwner) {
		func.exceptions.removeStructuredCatchHandler(plan.catchAddr);
	} else {
		func.exceptions.removeStructuredTryCatchFinallyHandlers(
			plan.catchAddr,
			plan.finallyAddr,
		);
	}

	func.markMergedBlocks(plan.body.address, plan.catchAddr);
	for (const mergedFinallyAddr of plan.mergedFinallyBlocks) {
		func.markMergedBlocks(plan.body.address, mergedFinallyAddr);
	}
	if (!plan.finallyHasOtherOwner) {
		func.markMergedBlocks(plan.body.address, plan.finallyAddr);
	}
}

function activeHandlersAtMergedBlock(
	func: IRFunction,
	address: BlockAddr,
	options: Parameters<typeof func.exceptions.activeHandlersAtBlock>[1] = {},
): AddressSet<BlockAddr> {
	const mergedSourceAddresses = func.mergedBlocks.get(address);
	const sourceAddresses = mergedSourceAddresses == null ||
			mergedSourceAddresses.size === 0
		? new AddressSet([address])
		: mergedSourceAddresses;
	return [...sourceAddresses].reduce(
		(handlers, sourceAddr) =>
			handlers.union(
				func.exceptions.activeHandlersAtBlock(sourceAddr, options),
			),
		new AddressSet<BlockAddr>(),
	);
}

function planTryCatchReduction(
	func: IRFunction,
	options: TryCatchReductionOptions,
): TryCatchReductionPlan | null {
	const catchMap = func.exceptions.catchMapForBlocks();
	for (const [addr, block] of func.blocks) {
		if (!nodeHasDelegateYield(block.body)) continue;
		const sourceAddresses = func.mergedBlocks.get(addr) ?? new AddressSet();
		for (const sourceAddr of sourceAddresses) {
			for (
				const catchAddr of func.exceptions.activeHandlersAtBlock(
					sourceAddr,
				)
			) {
				catchMap.addEdge(catchAddr, addr);
			}
		}
		if (sourceAddresses.size === 0) {
			for (const [catchAddr, record] of func.exceptions.records) {
				if (!func.exceptions.liveHandlers().has(catchAddr)) continue;
				const hasLiveProtectedBlock = [...record.protectedBlocks].some(
					(protectedAddr) => func.blocks.has(protectedAddr),
				);
				if (!hasLiveProtectedBlock) {
					catchMap.addEdge(catchAddr, addr);
				}
			}
		}
	}

	if (catchMap.size === 0) return null;
	const catchEntries = new Map<BlockAddr, AddressSet<BlockAddr>>(
		[...catchMap].map(([catchAddr, bodyBlocks]) => [
			catchAddr,
			new AddressSet(bodyBlocks),
		]),
	);
	const sortedCatches = [...catchMap].sort((a, b) => {
		if (func.exceptions.isNestedWithin(a[0], b[0])) return -1;
		if (func.exceptions.isNestedWithin(b[0], a[0])) return 1;
		if (options.preferProtectedRegionOrder) {
			const aSize = a[1].size;
			const bSize = b[1].size;
			if (aSize !== bSize) return aSize - bSize;
		}
		const aFinallyAddr = func.exceptions.records.get(a[0])
			?.canonicalFinallyAddress;
		const bFinallyAddr = func.exceptions.records.get(b[0])
			?.canonicalFinallyAddress;
		if (
			aFinallyAddr != null &&
			func.exceptions.isNestedWithin(b[0], aFinallyAddr)
		) return 1;
		if (
			bFinallyAddr != null &&
			func.exceptions.isNestedWithin(a[0], bFinallyAddr)
		) return -1;
		return b[0] - a[0];
	});
	return {
		options,
		catchEntries,
		candidates: sortedCatches.map(([catchAddr, bodyBlocks]) => ({
			catchAddr,
			bodyBlocks: new AddressSet(bodyBlocks),
		})),
	};
}

function applyTryCatchReductionPlan(
	func: IRFunction,
	plan: TryCatchReductionPlan,
): boolean {
	let changed = false;
	const { options, catchEntries } = plan;
	const currentLiveHandlers = () =>
		func.exceptions.liveHandlers().intersection(
			new AddressSet(catchEntries.keys()),
		);
	const hasOtherLiveOwningCatchForFinally = (
		catchAddr: BlockAddr,
		finallyAddr: BlockAddr,
	) => {
		const liveHandlers = func.exceptions.liveHandlers();
		for (const [otherCatchAddr, record] of func.exceptions.records) {
			if (otherCatchAddr === catchAddr) continue;
			if (!liveHandlers.has(otherCatchAddr)) continue;
			if (record.canonicalFinallyAddress === finallyAddr) return true;
		}
		return false;
	};
	const hasLiveAncestorOwningFinally = (
		catchAddr: BlockAddr,
		finallyAddr: BlockAddr,
		bodyAddr: BlockAddr,
	) => {
		const liveHandlers = func.exceptions.liveHandlers();
		for (const [otherCatchAddr, record] of func.exceptions.records) {
			if (otherCatchAddr === catchAddr) continue;
			if (!liveHandlers.has(otherCatchAddr)) continue;
			if (record.canonicalFinallyAddress !== finallyAddr) continue;
			if (func.exceptions.isNestedWithin(catchAddr, otherCatchAddr)) {
				return true;
			}
			const otherBodyBlocks = catchEntries.get(otherCatchAddr);
			if (otherBodyBlocks?.has(bodyAddr)) return true;
			const mergedBodyBlocks = func.mergedBlocks.get(bodyAddr);
			if (
				mergedBodyBlocks != null &&
				[...mergedBodyBlocks].some((addr) =>
					otherBodyBlocks?.has(addr)
				)
			) {
				return true;
			}
			const otherCatcher = func.blocks.get(otherCatchAddr);
			let cursor = otherCatcher?.consequentAddresses.length === 1
				? otherCatcher.consequentAddresses[0]
				: undefined;
			const visited = new Set<BlockAddr>();
			while (cursor !== undefined && !visited.has(cursor)) {
				if (cursor === bodyAddr) return true;
				visited.add(cursor);
				if (func.exceptions.isCatchTarget(cursor)) break;
				const block = func.blocks.get(cursor);
				if (!block || block.consequentAddresses.length !== 1) break;
				cursor = block.consequentAddresses[0];
			}
		}
		return false;
	};
	for (const candidate of plan.candidates) {
		const { catchAddr, bodyBlocks } = candidate;
		if (func.exceptions.finallyRecords.has(catchAddr)) {
			reduceFinallyRecord: {
				const hasLiveOwningCatch = func.exceptions
					.hasLiveOwningCatchForFinally(
						catchAddr,
						func.exceptions.liveHandlers(),
					);
				if (hasLiveOwningCatch) continue;

				const finallyBlock = func.blocks.get(catchAddr);
				const body = pickPreferredBodyBlock(func, bodyBlocks);
				if (!finallyBlock || !body) break reduceFinallyRecord;
				const finallyRecord = func.exceptions.finallyRecords.get(catchAddr);
				const copyRootAddr = body.consequentAddresses.length === 1 &&
						finallyRecord?.copyRoots.has(body.consequentAddresses[0])
					? body.consequentAddresses[0]
					: null;
				const finalizerSource = copyRootAddr == null
					? finallyBlock
					: func.blocks.get(copyRootAddr);
				if (!finalizerSource) break reduceFinallyRecord;

				// Skip if the try-body isn't fully reduced yet (still has successors)
				// or if the finally handler itself still has unresolved structure (e.g. a while loop).
				if (body.consequentAddresses.length !== 0 && copyRootAddr == null) {
					break reduceFinallyRecord;
				}

				const collectedFinalizer = copyRootAddr != null &&
						options.mergeSplitTryFinallyBody
					? collectLinearFinalizerCopyBody(
						func,
						copyRootAddr,
						finallyRecord?.isReturnOverride === true,
					)
					: null;
				const modeledFinalizer = collectModeledFinalizerBody(
					func,
					finallyRecord?.bodyBlocks,
					finallyRecord?.bodyBlockStatementLimits ?? new AddressMap(),
					finallyRecord?.isReturnOverride === true,
				);
				if (
					modeledFinalizer == null &&
					collectedFinalizer == null &&
					finalizerSource.consequentAddresses.length !== 0
				) break reduceFinallyRecord;

					let finalizerBody = modeledFinalizer?.body ??
						collectedFinalizer?.body ??
						completeFinalizerBodyFromBlock(func, finalizerSource.address) ??
						<t.Statement[]> finalizerSource.body.slice();
				if (finalizerBody.length === 0) break reduceFinallyRecord;
				if (
					finalizerBody.length === 1 &&
					t.isExpressionStatement(finalizerBody[0]) &&
					t.isCallExpression(finalizerBody[0].expression) &&
					t.isV8IntrinsicIdentifier(finalizerBody[0].expression.callee, {
						name: 'IteratorClose',
					})
				) {
					break reduceFinallyRecord;
				}

				applyTryFinallyMutationPlan(func, {
					body,
					finallyAddr: catchAddr,
					finalizerBody,
					successor: modeledFinalizer?.successor ??
						collectedFinalizer?.successor ?? [],
					mergedBlocks: [
						catchAddr,
						...(copyRootAddr == null ? [] : [copyRootAddr]),
						...(collectedFinalizer?.mergedBlocks ?? []),
						...(modeledFinalizer?.mergedBlocks ?? []),
					],
				});

				changed = true;
				continue;
			}
		}
		const catcher = func.blocks.get(catchAddr);
		if (!catcher) continue;
		const handlerRecord = func.exceptions.records.get(catchAddr);
		const body = pickFirstLiveBodyBlock(func, bodyBlocks);
		if (!body) continue;
		const finallyAddr = handlerRecord?.canonicalFinallyAddress ?? null;
		const finallyRecord = finallyAddr !== null
			? func.exceptions.finallyRecords.get(finallyAddr)
			: null;
		const finallyOwnedByLiveAncestor = finallyAddr !== null
			? hasLiveAncestorOwningFinally(
				catchAddr,
				finallyAddr,
				body.address,
			)
			: false;
		const terminalBodyFinalizerSplit =
			!finallyOwnedByLiveAncestor &&
				finallyAddr != null &&
				body.consequentAddresses.length === 0
				? (
					options.mergeSplitTryFinallyBody
						? splitTrailingFinalizerCopy(func, finallyAddr, body)
						: null
				) ??
					(() => {
						if (!finallyRecord?.isReturnOverride) return null;
						const copyRoot = finallyRecord.catchTrailer?.start ??
							[...finallyRecord.copyRoots][0];
						const copyBlock = copyRoot == null
							? null
							: func.blocks.get(copyRoot);
						if (!copyBlock) return null;
						if (
							!func.exceptions
								.isSuspendingReturnOverrideFinalizerCopy(
									finallyAddr,
									copyRoot,
								)
						) {
							return null;
						}
						return splitTrailingExactFinalizerCopy(
							func,
							body,
							<t.Statement[]> copyBlock.body,
						);
					})()
				: null;
		if (
			handlerRecord?.canonicalFinallyAddress != null &&
			body.consequentAddresses.length === 0 &&
			terminalBodyFinalizerSplit == null
		) {
			continue;
		}
		const isFinallyCopyRoot = (addr: BlockAddr | undefined) =>
			addr !== undefined && finallyRecord?.copyRoots.has(addr) === true;
		const blockStartsWithCurrentFinalizer = (
			addr: BlockAddr | undefined,
		) => {
			if (addr === undefined || finallyAddr === null) return false;
			const block = func.blocks.get(addr);
			if (!block) return false;
			const prefix = canonicalFinalizerPrefix(func, finallyAddr);
			if (prefix.length === 0 || block.body.length < prefix.length) {
				return false;
			}
			for (let i = 0; i < prefix.length; i++) {
				if (
					!statementMatchesFinalizerCopy(
						<t.Statement> block.body[i],
						prefix[i],
					)
				) return false;
			}
			return true;
		};
		const finalizerTrailerStart = (
			addr: BlockAddr | undefined,
		): BlockAddr | null => {
			if (addr === undefined) return null;
			if (isFinallyCopyRoot(addr) || blockStartsWithCurrentFinalizer(addr)) {
				return addr;
			}
			const block = func.blocks.get(addr);
			if (
				block &&
				isDiscardedCompletionValueReadBlock(block) &&
				block.consequentAddresses.length === 1
			) {
				const nextAddr = block.consequentAddresses[0];
				if (
					isFinallyCopyRoot(nextAddr) ||
					blockStartsWithCurrentFinalizer(nextAddr)
				) return nextAddr;
			}
			return null;
		};
		let catcherFinallyCopyBodyStart: number | null = null;
		let catcherFinallyCopyAddr: BlockAddr | null = null;
		let externalFinallyCopySuccessor = false;
		let externalFinallyAddr: BlockAddr | null = null;

		// Inline the catcher's non-catch-target successors into the catcher block.
		// This handles deep chains like catcher→A→B→C where A,B,C are non-catch-target
		// blocks that can't be merged by reduceSequence yet (different handler sets).
		// Merging them here lets catcherIsTerminal be detected correctly for the
		// terminal-catcher finally path.
		const visited = new Set<number>([catchAddr]);
		while (catcher.consequentAddresses.length === 1) {
			const nextAddr = catcher.consequentAddresses[0];
			if (visited.has(nextAddr)) break;
			if (func.exceptions.isCatchTarget(nextAddr)) break;
			const nextIsFinallyCopyRoot = [
				...func.exceptions.finallyRecords.values(),
			].some((record) => record.copyRoots.has(nextAddr));
			if (nextIsFinallyCopyRoot && !isFinallyCopyRoot(nextAddr)) {
				externalFinallyCopySuccessor = true;
				externalFinallyAddr = [
					...func.exceptions.activeHandlersAtBlock(catchAddr, {
						liveHandlers: currentLiveHandlers(),
					}),
				]
					.filter((handler) =>
						func.exceptions.finallyRecords.has(handler)
					)
					.toSorted((a, b) =>
						(func.exceptions.records.get(a)?.protectedBlocks
							.size ??
							Number.MAX_SAFE_INTEGER) -
						(func.exceptions.records.get(b)?.protectedBlocks
							.size ??
							Number.MAX_SAFE_INTEGER)
					)[0] ?? null;
				break;
			}
			if (isFinallyCopyRoot(nextAddr)) {
				if (catcherFinallyCopyBodyStart == null) {
					catcherFinallyCopyBodyStart = catcher.body.length;
					catcherFinallyCopyAddr = nextAddr;
				}
				break;
			}
			const nextBlock = func.blocks.get(nextAddr);
			if (!nextBlock) break;
			const predsSize = func.predecessorsOf(nextAddr).size;
			if (predsSize !== 1) break;
			const catcherHandlerOffsets = func.exceptions.activeHandlersAtBlock(
				catchAddr,
				{ liveHandlers: currentLiveHandlers() },
			);
			const currentFinallyAddr =
				func.exceptions.records.get(catchAddr)
					?.canonicalFinallyAddress ?? null;
			const entersUnresolvedProtectedRange = [
				...func.exceptions.activeHandlersAtBlock(nextAddr, {
					liveHandlers: currentLiveHandlers(),
				}),
			].some((handler) => {
				if (handler === catchAddr) return false;
				if (catcherHandlerOffsets.has(handler)) return false;
				if (func.exceptions.finallyRecords.has(handler)) return false;
				if (
					currentFinallyAddr != null &&
					catcherHandlerOffsets.has(currentFinallyAddr) &&
					func.exceptions.records.get(handler)
							?.canonicalFinallyAddress ===
						currentFinallyAddr
				) {
					return false;
				}
				return true;
			});
			if (entersUnresolvedProtectedRange) break;
			visited.add(nextAddr);
			catcher.body.push(...nextBlock.body);
			catcher.branch = nextBlock.branch;
			catcher.consequentAddresses = nextBlock.consequentAddresses;
			func.markMergedBlocks(catchAddr, nextAddr);
		}

		if (
			options.mergeSplitTryFinallyBody && bodyBlocks.size > 1 &&
			finallyRecord != null && !finallyOwnedByLiveAncestor
		) {
			while (body.consequentAddresses.length === 1) {
				const nextAddr = body.consequentAddresses[0];
				if (nextAddr === catchAddr || nextAddr === finallyAddr) break;
				if (isFinallyCopyRoot(nextAddr)) break;
				if (func.exceptions.finallyRecords.has(nextAddr)) break;
				if (func.exceptions.isCatchTarget(nextAddr)) break;

				const nextBlock = func.blocks.get(nextAddr);
				if (!nextBlock) break;
				if (func.cfgPredecessorsOf(nextAddr).size !== 1) {
					break;
				}

				body.body.push(...nextBlock.body);
				body.branch = nextBlock.branch;
				body.consequentAddresses = nextBlock.consequentAddresses;
				func.markMergedBlocks(body.address, nextAddr);
			}
		}

		const catcherIsTerminal = catcher.consequentAddresses.length === 0 ||
			catcherFinallyCopyAddr != null || externalFinallyCopySuccessor;
		const bodyIsTerminal = body.consequentAddresses.length === 0;
		const liveBodyBlockCount = [...bodyBlocks].filter((addr) =>
			addr === body.address || func.blocks.has(addr)
		).length;
		const bodyFinalizerTrailerAddr =
			body.consequentAddresses.length === 1
				? finalizerTrailerStart(body.consequentAddresses[0])
				: null;
		if (liveBodyBlockCount > 1) {
			// Allow when both body and catcher are terminal: extra body blocks become
			// orphans and are cleaned up by the orphan-cleanup pass in IRFunction.
			if (
				!(bodyIsTerminal && catcherIsTerminal) &&
				!(
					finallyRecord != null &&
					!bodyIsTerminal &&
					!catcherIsTerminal &&
					body.consequentAddresses.length === 1 &&
					catcher.consequentAddresses.length === 1 &&
					body.consequentAddresses[0] ===
						catcher.consequentAddresses[0]
				) &&
				!(
					finallyRecord != null &&
					!bodyIsTerminal &&
					catcherIsTerminal &&
					catcherFinallyCopyAddr != null &&
					body.consequentAddresses.length === 1 &&
					body.consequentAddresses[0] === catcherFinallyCopyAddr
				) &&
				!(
					finallyRecord != null &&
					!bodyIsTerminal &&
					catcherIsTerminal &&
					catcherFinallyCopyAddr != null &&
					body.consequentAddresses.length === 1 &&
					bodyFinalizerTrailerAddr != null
				) &&
				!(finallyRecord != null && terminalBodyFinalizerSplit != null)
			) {
				continue;
			}
		}
		if (!catcherIsTerminal) {
			if (catcher.consequentAddresses.length !== 1) {
				continue;
			}
			if (!bodyIsTerminal && body.consequentAddresses.length !== 1) {
				continue;
			}
			if (
				!bodyIsTerminal &&
				catcher.consequentAddresses[0] !== body.consequentAddresses[0]
			) {
				continue;
			}
		} else {
			// Terminal catcher (early return from catch body).
			if (!bodyIsTerminal) {
				// With finally, body.succ is the TryTrailer. Plain try/catch can also
				// have a terminal catch branch while the try branch continues normally.
				if (body.consequentAddresses.length !== 1) {
					continue;
				}
			}
			// bodyIsTerminal: both body and catcher are terminal — fall through to emit plain try-catch.
		}

		// Detect finally early so we can exclude its handler from the parent check.
		// The catch block is protected by the finally canonical's range, which the try
		// body block does not share — that's expected and should not block reduction.
		// Check that every outer handler of the catch block also protects the body block.
		// Compare by catchOffset only — in nested structures the same outer handler uses
		// different range extents for the try body vs. the catch body.
		{
			const exclude = finallyAddr !== null ? [finallyAddr] : [];
			const liveHandlersForParentCheck = currentLiveHandlers();
			const bodyOffsets = activeHandlersAtMergedBlock(
				func,
				body.address,
				{ exclude, liveHandlers: liveHandlersForParentCheck },
			);
			const catchBlockOffsets = func.exceptions.activeHandlersAtBlock(
				catchAddr,
				{ exclude, liveHandlers: liveHandlersForParentCheck },
			);
			const missingParentAllowed = (parentAddr: BlockAddr) => {
				if (!options.mergeSplitTryFinallyBody) return false;
				if (func.exceptions.finallyRecords.has(parentAddr)) {
					return true;
				}
				const parentRecord = func.exceptions.records.get(parentAddr);
				return parentRecord?.canonicalFinallyAddress != null &&
					catchBlockOffsets.has(parentRecord.canonicalFinallyAddress);
			};
		if (
			![...catchBlockOffsets].every((c) =>
				bodyOffsets.has(c) || missingParentAllowed(c)
			)
		) {
			continue;
		}
	}

		if (
			isSyntheticIteratorCleanupCatchBody(<t.Statement[]> catcher.body) &&
			(
				isSharedIteratorCloseRethrowTail(
					func,
					catcher.consequentAddresses[0],
				) ||
				(catcher.consequentAddresses.length === 0 &&
					(blockContainsIntrinsic(body, 'IteratorBegin') ||
						blockContainsIntrinsic(body, 'IteratorNext')))
			) &&
			activeHandlersAtMergedBlock(func, body.address, {
				liveHandlers: currentLiveHandlers(),
			}).has(catchAddr)
		) {
			applyRemoveSyntheticCatchMutationPlan(func, {
				body,
				catchAddr,
				successor: bodyIsTerminal && !catcherIsTerminal
					? [...catcher.consequentAddresses]
					: undefined,
			});
			changed = true;
			continue;
		}

		const catchBody = t.blockStatement(
			<t.Statement[]> catcher.body.slice(),
		);
		if (externalFinallyAddr != null) {
			stripFinalizerPrefixSuffix(
				catchBody.body,
				canonicalFinalizerPrefix(func, externalFinallyAddr),
			);
		}

		const catchInstIndex = catchBody.body.findIndex((errorAssign) => {
			if (!t.isVariableDeclaration(errorAssign, { kind: 'const' })) {
				return false;
			}
			if (!t.isVariableDeclarator(errorAssign.declarations[0])) {
				return false;
			}
			if (!t.isCallExpression(errorAssign.declarations[0].init)) {
				return false;
			}
			if (
				!t.isV8IntrinsicIdentifier(
					errorAssign.declarations[0].init.callee,
					{ name: 'Catch' },
				)
			) return false;

			return true;
		});
		const errorName = `e_${catchAddr}`;
		if (catchInstIndex === -1) {
			if (!replaceCatchCallsWithIdentifier(catchBody.body, errorName)) {
				continue;
			}
		} else {
			const catchInst = catchBody.body[catchInstIndex];
			if (!t.isVariableDeclaration(catchInst, { kind: 'const' })) {
				continue;
			}
			const errorAssign = <t.VariableDeclaration> t.cloneNode(
				catchInst,
				true,
			);
			errorAssign.declarations[0].init = t.identifier(errorName);
			catchBody.body.splice(catchInstIndex, 1, errorAssign);
		}
		if (catcherFinallyCopyBodyStart != null) {
			catchBody.body.splice(catcherFinallyCopyBodyStart);
			const catcherFinallyCopyBlock = catcherFinallyCopyAddr == null
				? null
				: func.blocks.get(catcherFinallyCopyAddr);
			let suppressSyntheticReturn =
				finallyRecord?.isReturnOverride === true ||
				(catcherFinallyCopyBlock?.consequentAddresses.length ?? 0) > 0;
			const catchRemainder = catcherFinallyCopyBlock != null &&
					finallyAddr != null
				? finalizerCopyRemainder(
					func,
					finallyAddr,
					catcherFinallyCopyBlock,
				)
				: null;
			if (catchRemainder != null) {
				const implicitCompletionReturn =
					!finallyRecord?.isReturnOverride &&
					catchRemainder.length === 1 &&
					t.isReturnStatement(catchRemainder[0]) &&
					catchRemainder[0].argument == null;
				if (!implicitCompletionReturn) {
					catchBody.body.push(...catchRemainder);
				}
			}
			if (
				catcherIsTerminal &&
				!suppressSyntheticReturn &&
				!isAbruptStatement(catchBody.body.at(-1))
			) {
				catchBody.body.push(t.returnStatement());
			}
		}

		if (
			!finallyOwnedByLiveAncestor &&
			finallyAddr !== null &&
			finallyRecord != null &&
			finallyRecord.catchTrailer == null
		) {
			const modeledFinalizer = collectModeledFinalizerBody(
				func,
				finallyRecord.bodyBlocks,
				finallyRecord.bodyBlockStatementLimits,
				finallyRecord.isReturnOverride,
			);
			const finalizerBody = modeledFinalizer?.body ??
				completeFinalizerBodyFromBlock(func, finallyAddr) ??
				canonicalFinalizerPrefix(func, finallyAddr);
			if (finalizerBody.length > 0) {
				stripFinalizerPrefixSuffix(
					catchBody.body,
					finalizerBody,
				);
				const finalizerSuccessor = modeledFinalizer?.successor ?? [];
				const splitDelegateCompletion =
					finalizerSuccessor.length === 1
						? hoistSplitDelegateCompletion(
							<t.Statement[]> body.body,
							func.blocks.get(finalizerSuccessor[0]),
							`r${body.address}_delegate`,
						)
						: null;
				const tryBody = splitDelegateCompletion ?? {
					prelude: [],
					body: <t.Statement[]> body.body,
				};
				const finallyHasOtherOwner =
					hasOtherLiveOwningCatchForFinally(
						catchAddr,
						finallyAddr,
					);
				applyTryCatchFinallyMutationPlan(func, {
					body,
					catchAddr,
					finallyAddr,
					errorName,
					catchBody,
					tryPrelude: tryBody.prelude,
					tryBody: tryBody.body,
					finalizerBody,
					successor: finalizerSuccessor,
					mergedFinallyBlocks: modeledFinalizer?.mergedBlocks ??
						[finallyAddr],
					finallyHasOtherOwner,
				});

				changed = true;
				continue;
			}
		}

		if (
			!finallyOwnedByLiveAncestor &&
			finallyRecord?.catchTrailer != null &&
			finallyAddr !== null
		) {
			// For terminal catchers (early return from catch body), the normal CatchTrailer
			// never runs — the body.succ (TryTrailer) is the finally copy that actually executes.
			const catchTrailerAddr = catcherIsTerminal
				? bodyFinalizerTrailerAddr ?? body.consequentAddresses[0]
					?? catcherFinallyCopyAddr
					?? finallyRecord.catchTrailer.start
				: options.mergeSplitTryFinallyBody &&
						catcherFinallyCopyAddr != null
				? catcherFinallyCopyAddr
				: options.mergeSplitTryFinallyBody &&
						body.consequentAddresses.length === 1 &&
						isFinallyCopyRoot(body.consequentAddresses[0])
				? body.consequentAddresses[0]
				: finallyRecord.catchTrailer.start;
			const bodyTrailerBlock = body.consequentAddresses.length === 1
				? func.blocks.get(body.consequentAddresses[0])
				: undefined;
			const bodyTrailerRemainderAddr =
				options.mergeSplitTryFinallyBody && bodyTrailerBlock
					? splitFinalizerCopyRemainder(
						func,
						finallyAddr,
						bodyTrailerBlock,
					)
					: null;
			const modeledFinalizer = collectModeledFinalizerBody(
				func,
				finallyRecord.bodyBlocks,
				finallyRecord.bodyBlockStatementLimits,
				finallyRecord.isReturnOverride,
			);
			const canonicalReturnOverrideFinalizer =
				finallyRecord.isReturnOverride
					? modeledFinalizer?.body ??
						completeFinalizerBodyFromBlock(func, finallyAddr) ??
						completeFinalizerBodyFromBlock(func, catchTrailerAddr)
					: null;
			if (canonicalReturnOverrideFinalizer) {
				stripFinalizerPrefixSuffix(
					catchBody.body,
					canonicalReturnOverrideFinalizer,
				);
				const finallyHasOtherOwner =
					hasOtherLiveOwningCatchForFinally(
						catchAddr,
						finallyAddr,
					);
				applyTryCatchFinallyMutationPlan(func, {
					body,
					catchAddr,
					finallyAddr,
					errorName,
					catchBody,
					tryPrelude: [],
					tryBody: <t.Statement[]> body.body,
					finalizerBody: canonicalReturnOverrideFinalizer,
					successor: [],
					mergedFinallyBlocks: [],
					finallyHasOtherOwner,
				});

				changed = true;
				continue;
			}
			if (modeledFinalizer != null && bodyTrailerRemainderAddr == null) {
				stripFinalizerPrefixSuffix(
					catchBody.body,
					modeledFinalizer.body,
				);
				const splitDelegateCompletion =
					bodyTrailerRemainderAddr != null
						? hoistSplitDelegateCompletion(
							<t.Statement[]> body.body,
							func.blocks.get(bodyTrailerRemainderAddr),
							`r${body.address}_delegate`,
						)
						: null;
				const tryBody = splitDelegateCompletion ??
					(terminalBodyFinalizerSplit != null
						? hoistDelegateCompletionDeclaration(
							<t.Statement[]> body.body,
						)
						: { prelude: [], body: <t.Statement[]> body.body });
				const finallyHasOtherOwner =
					hasOtherLiveOwningCatchForFinally(
						catchAddr,
						finallyAddr,
					);
				applyTryCatchFinallyMutationPlan(func, {
					body,
					catchAddr,
					finallyAddr,
					errorName,
					catchBody,
					tryPrelude: tryBody.prelude,
					tryBody: tryBody.body,
					finalizerBody: modeledFinalizer.body,
					successor: modeledFinalizer.successor,
					mergedFinallyBlocks: modeledFinalizer.mergedBlocks,
					finallyHasOtherOwner,
				});

				changed = true;
				continue;
			}
			const catchTrailerBlock = func.blocks.get(catchTrailerAddr);

			if (catchTrailerBlock) {
				// Use the CatchTrailer block as the source of finally body statements.
				// It contains the complete finally code (unlike the canonical block which may
				// be multi-block and has the Catch header). The CatchTrailer is the normal-flow
				// copy that runs after the catch body completes.
				let finallyStmts: t.Statement[] = [];
				const mergedFinallyBlocks: BlockAddr[] = [];
				let finalizerCursor: BlockAddr | undefined = catchTrailerAddr;
				let blockedByNestedHandler = false;
				while (finalizerCursor !== undefined) {
					const finalizerBlock = func.blocks.get(finalizerCursor);
					if (!finalizerBlock) break;
					const splitRemainderAddr = options.mergeSplitTryFinallyBody
						? splitFinalizerCopyRemainder(
							func,
							finallyAddr,
							finalizerBlock,
						)
						: null;
					finallyStmts.push(...<t.Statement[]> finalizerBlock.body);
					mergedFinallyBlocks.push(finalizerCursor);
					if (splitRemainderAddr != null) break;
					if (
						bodyTrailerRemainderAddr != null &&
						finalizerCursor === catchTrailerAddr
					) break;
					if (
						options.mergeSplitTryFinallyBody &&
						isFinallyCopyRoot(finalizerCursor) &&
						func.blocks.get(finallyAddr)?.consequentAddresses
								.length ===
							0 &&
						finalizerBlock.body.length ===
							canonicalFinalizerPrefix(func, finallyAddr).length
					) {
						break;
					}
					if (finalizerBlock.consequentAddresses.length !== 1) break;

					const nextAddr = finalizerBlock.consequentAddresses[0];
					const nextHandlers = func.exceptions.activeHandlersAtBlock(
						nextAddr,
						{ liveHandlers: currentLiveHandlers() },
					);
					const nextProtectedByCurrentFinally =
						func.exceptions.records.get(finallyAddr)
							?.protectedBlocks
							.has(nextAddr) === true;
					if (nextAddr === catchAddr) break;
					const nextIsFinallyCopyRoot = [
						...func.exceptions.finallyRecords.values(),
					].some((record) => record.copyRoots.has(nextAddr));
					if (
						nextIsFinallyCopyRoot && !isFinallyCopyRoot(nextAddr)
					) break;
					if (
						options.mergeSplitTryFinallyBody &&
						func.exceptions.liveNestedHandlersAtBlock(
								nextAddr,
								finallyAddr,
								currentLiveHandlers(),
							).size > 0
					) {
						blockedByNestedHandler = true;
						break;
					}
					if (
						[...nextHandlers].some((handler) =>
							handler === nextAddr &&
							nextAddr !== finallyAddr
						)
					) break;
					if (
						[...nextHandlers].some((handler) =>
							handler !== catchAddr &&
							handler !== finallyAddr &&
							func.blocks.has(handler) &&
							!(
								options.mergeSplitTryFinallyBody &&
								(func.exceptions.isNestedWithin(
									finallyAddr,
									handler,
								) ||
									func.exceptions.isNestedWithin(
										catchAddr,
										handler,
									))
							)
						)
					) break;
					const onlyProtectedByCurrentFinally =
						nextHandlers.size > 0 &&
						[...nextHandlers].every((handler) =>
							handler === finallyAddr
						);
					if (
						nextAddr !== finallyAddr &&
						!onlyProtectedByCurrentFinally &&
						!(
							options.mergeSplitTryFinallyBody &&
							nextProtectedByCurrentFinally
						) &&
						func.predecessorsOf(nextAddr).size !== 1
					) {
						break;
					}
					if (
						options.mergeSplitTryFinallyBody &&
						finalizerBlock.body.some((stmt) =>
							t.isTryStatement(<t.Statement> stmt)
						)
					) {
						break;
					}
					finalizerCursor = nextAddr;
				}
				if (blockedByNestedHandler) continue;

				const copyFinalizerSuccessor = mergedFinallyBlocks.length === 0
					? catchTrailerBlock.consequentAddresses
					: func.blocks.get(mergedFinallyBlocks.at(-1)!)
						?.consequentAddresses ?? [];
				const canonicalFinalizerSuccessor = func.file.version >= 99 &&
						catcherFinallyCopyAddr != null && finallyAddr !== null
					? func.blocks.get(finallyAddr)?.consequentAddresses ??
						copyFinalizerSuccessor
					: copyFinalizerSuccessor;
				const finalizerSuccessor = bodyTrailerRemainderAddr != null
					? [bodyTrailerRemainderAddr]
					: terminalBodyFinalizerSplit != null
					? terminalBodyFinalizerSplit.successor
					: canonicalFinalizerSuccessor;
				if (terminalBodyFinalizerSplit != null) {
					finallyStmts = terminalBodyFinalizerSplit.finalizerBody;
				}

				// For non-return-override finallys, the CatchTrailer ends with the
				// implicit generator/function completion return. If the finalizer
				// suspends, that return can live in a second resume block, so check
				// the merged finalizer successor rather than only the source block.
				// For return-override finallys (explicit `return`), keep all statements.
				if (
					!finallyRecord.isReturnOverride &&
					finalizerSuccessor.length === 0
				) {
					if (t.isReturnStatement(finallyStmts.at(-1))) {
						finallyStmts = finallyStmts.slice(0, -1);
					}
				}

				const tryBody = terminalBodyFinalizerSplit != null
					? hoistDelegateCompletionDeclaration(
						<t.Statement[]> body.body,
					)
					: { prelude: [], body: <t.Statement[]> body.body };
				const finallyHasOtherOwner =
					hasOtherLiveOwningCatchForFinally(
						catchAddr,
						finallyAddr,
					);
				applyTryCatchFinallyMutationPlan(func, {
					body,
					catchAddr,
					finallyAddr,
					errorName,
					catchBody,
					tryPrelude: tryBody.prelude,
					tryBody: tryBody.body,
					finalizerBody: finallyStmts,
					successor: finalizerSuccessor,
					mergedFinallyBlocks,
					finallyHasOtherOwner,
				});

				changed = true;
				continue;
			}
		}

		if (finallyAddr !== null) {
			const finalizerSuffix =
				completeFinalizerBodyFromBlock(func, finallyAddr) ??
					canonicalFinalizerPrefix(func, finallyAddr);
			stripFinalizerPrefixSuffix(catchBody.body, finalizerSuffix);
		}

		if (
			isIteratorCloseRethrowBody(catchBody.body, errorName) &&
			activeHandlersAtMergedBlock(func, body.address, {
				liveHandlers: currentLiveHandlers(),
			}).has(catchAddr)
		) {
			applyRemoveSyntheticCatchMutationPlan(func, {
				body,
				catchAddr,
				successor: bodyIsTerminal && !catcherIsTerminal
					? [...catcher.consequentAddresses]
					: undefined,
			});
			changed = true;
			continue;
		}

		applyTryCatchMutationPlan(func, {
			body,
			catchAddr,
			errorName,
			catchBody,
			// A terminal try uses the catch continuation rather than a shared join.
			successor: bodyIsTerminal && !catcherIsTerminal
				? [...catcher.consequentAddresses]
				: undefined,
		});

		changed = true;
	}

	return changed;
}

export function reduceTryCatch(
	func: IRFunction,
	options: TryCatchReductionOptions = {},
): boolean {
	const plan = planTryCatchReduction(func, options);
	return plan == null ? false : applyTryCatchReductionPlan(func, plan);
}
