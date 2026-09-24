import * as t from '@babel/types';
import traverse from '@babel/traverse';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import type { SSABasicBlock } from '../../../ssa.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import { isAbruptStatement } from '../../ast/completion.ts';
import {
	nodeHasDelegateYield,
	statementsMaySuspend,
} from '../../ast/effects.ts';
import type { IRBlock, LiftedAST } from '../../ast/mod.ts';
import { comparableAst } from '../../ast/utils.ts';
import type { IRFunction } from '../mod.ts';
import { singleDeclarator } from '../utils.ts';
import {
	statementAlwaysTerminates,
	statementListMatchesFinalizerPrefix,
	statementMatchesFinalizerPrefix,
} from '../finalizer.ts';
import {
	blockEndsWithDelegateIteratorAcquisition,
	blockStartsWithDelegateYieldLoop,
} from './delegateYield.ts';
import { invertTest } from '../../ast/expression.ts';
import { livenessAnalysis } from '../../../utils/liveness.ts';
import { type PhiContext, phiContext, registerName } from './phi.ts';
import { isParameterExpression } from '../../ast/alias.ts';

const MAX_SHARED_SEQUENCE_NODE_COUNT = 512;
const MAX_SHARED_SEQUENCE_CLONED_NODE_COUNT = 1024;

export function reduceSequence(func: IRFunction) {
	const phis = phiContext(func);
	const parents = new AddressMap<BlockAddr>();
	const children = new AddressMap<BlockAddr>();
	const reachableFromEntry = func.reachableBlocksFromEntry();
	for (const [addr, block] of func.blocks) {
		if (block.branch) continue;

		const successors = block.consequentAddresses;
		if (successors.length !== 1) continue;

		const [childAddr] = successors;
		if (addr === childAddr) continue;
		if (childAddr === 0) continue;
		if (!func.blocks.has(childAddr)) continue;
		const childIsFinallyCopyRoot = [
			...func.exceptions.finallyRecords.values(),
		].some((record) => record.copyRoots.has(childAddr));
		const childBlock = func.blocks.get(childAddr);
		if (
			childBlock &&
			unresolvedPhiHasMultipleLiveOwners(
				func,
				phis,
				childAddr,
				childBlock,
			)
		) continue;
		if (
			!func.isNativeGenerator &&
			!func.isLoweredGenerator &&
			isGeneratedAliasPrelude(block.body) &&
			!block.branch &&
			childBlock !== undefined &&
			func.exceptions.activeHandlersEqual(addr, childAddr) &&
			!func.exceptions.isCatchTarget(childAddr) &&
			!childIsFinallyCopyRoot
		) {
			block.body.push(...childBlock.body);
			block.branch = childBlock.branch;
			block.consequentAddresses = childBlock.consequentAddresses;
			func.markMergedBlocks(addr, childAddr);
			continue;
		}
		if (childIsFinallyCopyRoot) {
			const last = block.body.at(-1) as t.Statement | undefined;
			if (
				t.isTryStatement(last) &&
				last.finalizer &&
				childBlock &&
				statementListMatchesFinalizerPrefix(
					last.finalizer.body,
					<t.Statement[]> childBlock.body,
				)
			) {
				block.consequentAddresses = [];
				func.markMergedBlocks(addr, childAddr);
				continue;
			}
		}
		if (
			func.exceptions.records.get(childAddr)?.canonicalFinallyAddress !=
				null
		) {
			continue;
		}
		if (childIsFinallyCopyRoot) {
			continue;
		}
		// Catch handler blocks must not be sequence-merged into their successors before
		// reduceTryCatch consumes them. Exception: if the IR successor is already terminal
		// (e.g., an internal try-catch-finally with return-override has been reduced), the
		// catcher's internal body is done and it's safe to merge so the catcher becomes
		// terminal itself (enabling reduceTryCatch to fire for the outer try-catch-finally).
		const addrIsCatchTarget = func.exceptions.isCatchTarget(addr);
		if (addrIsCatchTarget) {
			const childIRBlock = func.blocks.get(childAddr);
			const childIsTerminalInIR = childIRBlock !== undefined &&
				childIRBlock.consequentAddresses.length === 0;
			if (!childIsTerminalInIR) continue;
		}

		if (
			!func.exceptions.activeHandlersEqual(addr, childAddr)
		) {
			const isPureTrampoline = childBlock !== undefined &&
				childBlock.body.length === 0 && !childBlock.branch;

			if (!isPureTrampoline) {
				const canMergeDelegateYieldSplit = func.isNativeGenerator &&
					childBlock !== undefined &&
					block.branch == null &&
					(() => {
						const acquisition =
							blockEndsWithDelegateIteratorAcquisition(
								<t.Statement[]> block.body,
							);
						return acquisition != null &&
							blockStartsWithDelegateYieldLoop(
								<t.Statement[]> childBlock.body,
								acquisition.iteratorName,
							);
					})();
				const addrOffsets = func.exceptions.activeHandlersAtBlock(addr);
				const childOffsets = func.exceptions.activeHandlersAtBlock(
					childAddr,
				);
				const sameCatchOffsets =
					addrOffsets.size === childOffsets.size &&
					[...addrOffsets].every((o) => childOffsets.has(o));
				// Native generator delegate-yield lowering splits a non-suspending
				// prelude immediately before the protected ResumeGenerator region. The
				// generator reconstructor needs that pair kept linear, but extending this
				// exception to ordinary functions mixes protected and unprotected source
				// regions and prevents reduceTryCatch from isolating the try body.
				const canMergeNativeGeneratorProtectedPrefix =
					func.isNativeGenerator &&
					addrOffsets.size === 0 &&
					childOffsets.size > 0 &&
					!addrIsCatchTarget &&
					!func.exceptions.isCatchTarget(childAddr) &&
					!statementsMaySuspend(block.body as t.Statement[]) &&
					!block.body.some((stmt) =>
						statementAlwaysTerminates(stmt as t.Statement)
					);
				const ssaNonTerminal =
					func.ssa.basicBlocks.get(childAddr)?.consequentAddresses
						?.length !== 0;
				// Also allow merging if the IR block became terminal after reductions,
				// even if the original SSA block was non-terminal.
				const irTerminal = childBlock?.consequentAddresses.length === 0;
				if (
					!sameCatchOffsets &&
					ssaNonTerminal &&
					!irTerminal &&
					!canMergeDelegateYieldSplit &&
					!canMergeNativeGeneratorProtectedPrefix
				) {
					continue;
				}
				// For the IR-terminal fallback (SSA non-terminal but IR terminal): additionally
				// block if the parent has extra catch offsets that have attributed finallys.
				// Those finallys need this child block as the TryTrailer; absorbing it prematurely
				// makes body terminal and prevents the finally from being reconstructed.
				if (!sameCatchOffsets && ssaNonTerminal && irTerminal) {
					const extraOffsets = [...addrOffsets].filter((o) =>
						!childOffsets.has(o)
					);
					const blockedByPendingFinally = extraOffsets.some((o) =>
						func.exceptions.records.get(o)
							?.canonicalFinallyAddress != null
					);
					if (blockedByPendingFinally) continue;
				}
			}
		}

		const predecessors = func.predecessorsOf(childAddr);
		if (predecessors.size !== 1) {
			const canMergeStaleDelegateTail = func.isNativeGenerator &&
				predecessors.has(addr) &&
				nodeHasDelegateYield(block.body) &&
				[...predecessors].every((pred) =>
					pred === addr || !reachableFromEntry.has(pred)
				);
			if (!canMergeStaleDelegateTail) continue;
		}
		parents.set(childAddr, addr);
		children.set(addr, childAddr);
	}

	if (children.size === 0) {
		return false;
	}

	const starts = new AddressSet();
	for (const parent of children.keys()) {
		if (!parents.has(parent)) starts.add(parent);
	}

	let changed = false;
	for (const start of starts) {
		const parent = func.blocks.get(start);
		if (!parent) continue;

		const rootAddr = start;
		let parentAddr = rootAddr;
		while (true) {
			const childAddr = children.get(parentAddr);
			if (!childAddr) break;

			const child = func.blocks.get(childAddr);
			if (!child) break;
			if (
				!child.branch &&
				child.consequentAddresses.length === 0 &&
				child.body.some((stmt) => t.isReturnStatement(stmt as t.Node))
			) {
				parent.body.push(
					...cloneBodyForPredecessor(func, childAddr, parentAddr),
				);
			} else {
				parent.body.push(...child.body);
			}
			parent.branch = child.branch;
			parent.consequentAddresses = child.consequentAddresses;

			changed = true;
			func.markMergedBlocks(rootAddr, childAddr);
			if (
				!parent.branch &&
				isAbruptStatement(<t.Statement | undefined> parent.body.at(-1))
			) {
				parent.consequentAddresses = [];
				break;
			}

			parentAddr = childAddr;
		}
	}

	return changed;
}

/**
 * Duplicates a small shared linear continuation onto one of its incoming
 * edges. This is ordinary CFG node splitting: the selected predecessor still
 * executes the continuation exactly once, while the original block remains for
 * its other predecessors. It turns non-SESE acyclic diamonds into the nested
 * diamonds consumed by `reduceSimpleIf`.
 */
export function reduceSharedSequenceEdge(func: IRFunction): boolean {
	// Node splitting is a finishing pass for a mostly reduced DAG. Running it on
	// the original body of a very large function can repeatedly expose new shared
	// edges faster than the structural reducers consume them.
	if (func.blocks.size > 64) return false;
	// Script completion returns are not lexical `return` statements. Splitting a
	// shared edge across a top-level exception region can move those completions
	// into nested branches before script cleanup recognizes them.
	if (func.id === 0 && func.exceptions.records.size > 0) return false;
	for (const [childAddr, child] of func.blocks) {
		if (childAddr === 0 || child.branch) continue;
		if (child.consequentAddresses.length !== 1) continue;
		if (child.consequentAddresses[0] === childAddr) continue;
		if (child.body.length === 0 || child.body.length > 64) continue;
		const childNodeCount = boundedNodeCount(
			child.body as t.Statement[],
			MAX_SHARED_SEQUENCE_NODE_COUNT,
		);
		if (childNodeCount == null) continue;
		if (blockContainsPhi(child)) continue;

		const predecessors = func.predecessorsOf(childAddr);
		if (predecessors.size < 2 || predecessors.size > 8) continue;
		if (
			childNodeCount * (predecessors.size - 1) >
				MAX_SHARED_SEQUENCE_CLONED_NODE_COUNT
		) continue;
		if (func.exceptions.isCatchTarget(childAddr)) continue;
		if (
			func.exceptions.records.get(childAddr)?.canonicalFinallyAddress !=
				null
		) continue;
		if (func.exceptions.activeHandlersAtBlock(childAddr).size > 0) continue;

		// Split a branch edge first. Appending the continuation directly to a
		// branching predecessor would execute it on both outcomes; a synthetic edge
		// block keeps it conditional and makes the arm exclusively owned.
		for (const parentAddr of predecessors) {
			if (parentAddr === childAddr) continue;
			const parent = func.blocks.get(parentAddr);
			if (
				!parent?.branch ||
				!parent.consequentAddresses.includes(childAddr)
			) continue;
			if (!func.exceptions.activeHandlersEqual(parentAddr, childAddr)) {
				continue;
			}
			// Do not split a loop-exit edge. Giving one exit a cloned continuation
			// creates multiple syntactically distinct exits from the same SCC, which
			// prevents the natural-loop reducer from recognizing the original loop.
			if (blockCanReach(func, parentAddr, parentAddr, childAddr)) {
				continue;
			}
			const splitAddr = freshSyntheticBlockAddress(func);
			func.setBlock(splitAddr, {
				address: splitAddr,
				body: cloneStatementList(child.body),
				branch: undefined,
				consequentAddresses: [...child.consequentAddresses],
				kind: 'synthetic',
				syntheticReason: 'shared-sequence-edge',
				sourceAddresses: new AddressSet(
					child.sourceAddresses ?? [childAddr],
				),
			});
			parent.consequentAddresses = parent.consequentAddresses.map(
				(successor) => successor === childAddr ? splitAddr : successor,
			);
			func.rebuildPredecessorMap();
			return true;
		}

		const parentAddr = [...predecessors].find((address) => {
			if (address === childAddr) return false;
			const parent = func.blocks.get(address);
			return parent != null && !parent.branch &&
				parent.consequentAddresses.length === 1 &&
				parent.consequentAddresses[0] === childAddr &&
				func.exceptions.activeHandlersEqual(address, childAddr);
		});
		if (parentAddr == null) continue;
		const parent = func.blocks.get(parentAddr)!;

		// An SSA Phi may already have been lowered out of `child.body`; in that
		// case the predecessor assignment and the remaining child statements are
		// already edge-specific. Running `cloneBodyForPredecessor` again would
		// substitute the original SSA source a second time.
		parent.body.push(...cloneStatementList(child.body));
		parent.consequentAddresses = [...child.consequentAddresses];
		return true;
	}
	return false;
}

/**
 * Count an AST forest only up to `limit`.
 *
 * Shared-edge splitting clones a continuation. Top-level statement count is
 * not a useful size bound once earlier reductions have nested a large decision
 * tree inside one `if` statement; repeatedly cloning that single statement can
 * grow the tree exponentially and pin the subsequent whole-AST cleanup. Walk
 * Babel's visitor keys iteratively so an oversized tree is rejected as soon as
 * the bound is crossed.
 */
function boundedNodeCount(
	roots: readonly t.Node[],
	limit: number,
): number | null {
	let count = 0;
	const pending: t.Node[] = [...roots];
	while (pending.length > 0) {
		const node = pending.pop()!;
		if (++count > limit) return null;
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const child = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(child)) {
				for (const candidate of child) {
					if (candidate && typeof candidate === 'object') {
						pending.push(candidate as t.Node);
					}
				}
			} else if (child && typeof child === 'object') {
				pending.push(child as t.Node);
			}
		}
	}
	return count;
}

function blockCanReach(
	func: IRFunction,
	target: BlockAddr,
	start: BlockAddr,
	excluded: BlockAddr,
): boolean {
	const pending =
		func.blocks.get(start)?.consequentAddresses.filter((address) =>
			address !== excluded
		) ?? [];
	const seen = new AddressSet<BlockAddr>([start, excluded]);
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (address === target) return true;
		if (seen.has(address)) continue;
		seen.add(address);
		const block = func.blocks.get(address);
		if (block) pending.push(...block.consequentAddresses);
	}
	return false;
}

function freshSyntheticBlockAddress(func: IRFunction): BlockAddr {
	let address = -1_000_000_000 as BlockAddr;
	while (func.blocks.has(address)) address--;
	return address;
}

export function isScriptCompletionReturn(
	block: { body: LiftedAST<t.Statement>[] },
) {
	if (block.body.length !== 1) return false;
	const [stmt] = block.body;
	if (!t.isReturnStatement(<t.Statement> stmt)) return false;
	const argument = (<t.ReturnStatement> stmt).argument;
	return argument == null || t.isIdentifier(argument);
}

function statementContainsIntrinsic(stmt: t.Statement, name: string): boolean {
	let found = false;
	t.traverseFast(stmt, (node) => {
		if (
			t.isCallExpression(node) &&
			t.isV8IntrinsicIdentifier(node.callee, { name })
		) {
			found = true;
		}
	});
	return found;
}

export function expressionContainsIntrinsic(
	expr: t.Expression,
	name: string,
): boolean {
	let found = false;
	t.traverseFast(expr, (node) => {
		if (
			t.isCallExpression(node) &&
			t.isV8IntrinsicIdentifier(node.callee, { name })
		) {
			found = true;
		}
	});
	return found;
}

export function leadingPhiDeclarations(body: LiftedAST<t.Statement>[]) {
	const phis: Array<{
		index: number;
		name: string;
		call: t.CallExpression;
	}> = [];
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i] as t.Statement;
		if (
			!t.isVariableDeclaration(stmt, { kind: 'const' }) ||
			stmt.declarations.length !== 1
		) break;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id) || !t.isCallExpression(decl.init)) break;
		if (!t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })) {
			break;
		}
		phis.push({ index: i, name: decl.id.name, call: decl.init });
	}
	return phis;
}

function collectConstInitializers(
	func: IRFunction,
	addrs: Iterable<BlockAddr>,
): Map<string, t.Expression> {
	const inits = new Map<string, t.Expression>();
	for (const addr of addrs) {
		const block = func.blocks.get(addr);
		if (!block) continue;
		for (const stmt of block.body) {
			if (
				!t.isVariableDeclaration(stmt as t.Node, { kind: 'const' }) ||
				(stmt as t.VariableDeclaration).declarations.length !== 1
			) continue;
			const [decl] = (stmt as t.VariableDeclaration).declarations;
			if (
				t.isIdentifier(decl.id) &&
				decl.init &&
				t.isExpression(decl.init) &&
				!(t.isCallExpression(decl.init) &&
					t.isV8IntrinsicIdentifier(decl.init.callee, {
						name: 'Phi',
					}))
			) {
				inits.set(decl.id.name, decl.init);
			}
		}
	}
	return inits;
}

function constInitializerInBlock(
	block: IRBlock,
	name: string,
): t.Expression | null {
	for (const stmt of block.body) {
		if (
			!t.isVariableDeclaration(stmt as t.Node, { kind: 'const' }) ||
			(stmt as t.VariableDeclaration).declarations.length !== 1
		) continue;
		const [decl] = (stmt as t.VariableDeclaration).declarations;
		if (
			t.isIdentifier(decl.id, { name }) &&
			decl.init &&
			t.isExpression(decl.init)
		) return decl.init;
	}
	return null;
}

function resolvePhiSourceExpression(
	name: string,
	targetName: string,
	inits: Map<string, t.Expression>,
	seen = new Set<string>(),
): t.Expression {
	if (name === targetName || seen.has(name)) return t.identifier(name);
	const init = inits.get(name);
	if (!init) return t.identifier(name);
	if (t.isIdentifier(init)) {
		return resolvePhiSourceExpression(
			init.name,
			targetName,
			inits,
			new Set([...seen, name]),
		);
	}
	return t.cloneNode(init, true);
}

function expressionForLatchPhiSource(
	sourceName: string,
	targetName: string,
	predBlock: IRBlock,
	inits: Map<string, t.Expression>,
): t.Expression {
	const localInit = constInitializerInBlock(predBlock, sourceName);
	if (localInit && !t.isIdentifier(localInit)) {
		return t.identifier(sourceName);
	}
	return resolvePhiSourceExpression(sourceName, targetName, inits);
}

function assignmentsForLatchPhiSource(
	sourceName: string,
	targetName: string,
	predBlock: IRBlock,
	inits: Map<string, t.Expression>,
): t.Statement[] {
	const localInit = constInitializerInBlock(predBlock, sourceName);
	if (
		localInit &&
		t.isBinaryExpression(localInit) &&
		(localInit.operator === '+' || localInit.operator === '-') &&
		t.isIdentifier(localInit.left) &&
		!t.isIdentifier(localInit.left, { name: targetName }) &&
		t.isExpression(localInit.right)
	) {
		return [
			t.expressionStatement(
				t.assignmentExpression(
					'=',
					t.identifier(targetName),
					t.cloneNode(localInit.left, true),
				),
			),
			t.expressionStatement(
				t.assignmentExpression(
					'=',
					t.identifier(targetName),
					t.binaryExpression(
						localInit.operator,
						t.identifier(targetName),
						t.cloneNode(localInit.right, true),
					),
				),
			),
		];
	}

	const sourceExpr = expressionForLatchPhiSource(
		sourceName,
		targetName,
		predBlock,
		inits,
	);
	if (t.isIdentifier(sourceExpr, { name: targetName })) return [];
	return [
		t.expressionStatement(
			t.assignmentExpression(
				'=',
				t.identifier(targetName),
				sourceExpr,
			),
		),
	];
}

function replaceIdentifiersInExpression(
	expr: t.Expression,
	replacements: Map<string, string>,
): t.Expression {
	const cloned = t.cloneNode(expr, true);
	t.traverseFast(cloned, (node) => {
		if (!t.isIdentifier(node)) return;
		const replacement = replacements.get(node.name);
		if (replacement) node.name = replacement;
	});
	return cloned;
}

export function lowerLoopLatchPhiCopies(
	func: IRFunction,
	header: BlockAddr,
	latch: BlockAddr,
	body: AddressSet<BlockAddr>,
): boolean {
	if (func.isGenerator || func.isNativeGenerator || func.isLoweredGenerator) {
		return false;
	}
	const headerBlock = func.blocks.get(header);
	const latchBlock = func.blocks.get(latch);
	const latchSSA = func.ssa.basicBlocks.get(latch);
	const headerSSA = func.ssa.basicBlocks.get(header);
	if (!headerBlock || !latchBlock || !latchSSA || !headerSSA) return false;

	const latchPhis = leadingPhiDeclarations(latchBlock.body);
	if (latchPhis.length === 0) return false;
	const ssaLatchPhis = latchSSA.ssaInstructions.filter((instr) =>
		instr.instruction === 'Phi'
	);
	if (ssaLatchPhis.length < latchPhis.length) return false;

	const phiDestToHeaderTarget = new Map<string, string>();
	const copiedRegisterToHeaderTarget = new Map<string, string>();
	for (let i = latchPhis.length; i < latchBlock.body.length; i++) {
		const stmt = latchBlock.body[i] as t.Statement;
		if (
			!t.isVariableDeclaration(stmt, { kind: 'const' }) ||
			stmt.declarations.length !== 1
		) continue;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id) || !t.isIdentifier(decl.init)) continue;
		const latchPhiName = decl.init.name;
		if (!latchPhis.some((phi) => phi.name === latchPhiName)) continue;
		const copiedRegister = decl.id.name;

		for (const instr of headerSSA.ssaInstructions) {
			if (instr.instruction !== 'Phi') continue;
			const latchSource = instr.sources.get(latch);
			if (!latchSource || registerName(latchSource) !== copiedRegister) {
				continue;
			}
			const targetName = registerName(instr.destination);
			phiDestToHeaderTarget.set(latchPhiName, targetName);
			copiedRegisterToHeaderTarget.set(copiedRegister, targetName);
		}
	}
	if (phiDestToHeaderTarget.size === 0) return false;

	const predecessorAddrs = [...func.predecessorsOf(latch)].filter((pred) =>
		body.has(pred)
	);
	if (predecessorAddrs.length === 0) return false;

	const inits = collectConstInitializers(func, body);
	let changed = false;
	for (let i = 0; i < latchPhis.length; i++) {
		const latchPhi = latchPhis[i];
		const targetName = phiDestToHeaderTarget.get(latchPhi.name);
		if (!targetName) continue;
		const ssaPhi = ssaLatchPhis[i];
		if (ssaPhi.instruction !== 'Phi') continue;

		for (const pred of predecessorAddrs) {
			const predBlock = func.blocks.get(pred);
			const source = ssaPhi.sources.get(pred);
			if (!predBlock || !source) continue;
			const assignments = assignmentsForLatchPhiSource(
				registerName(source),
				targetName,
				predBlock,
				inits,
			);
			if (assignments.length === 0) continue;
			predBlock.body.push(...assignments);
			changed = true;
		}
	}
	if (!changed) return false;

	latchBlock.body.splice(0, latchPhis.length);
	for (let i = latchBlock.body.length - 1; i >= 0; i--) {
		const stmt = latchBlock.body[i] as t.Statement;
		if (
			!t.isVariableDeclaration(stmt, { kind: 'const' }) ||
			stmt.declarations.length !== 1
		) continue;
		const [decl] = stmt.declarations;
		if (
			t.isIdentifier(decl.id) &&
			t.isIdentifier(decl.init) &&
			copiedRegisterToHeaderTarget.has(decl.id.name)
		) {
			latchBlock.body.splice(i, 1);
		}
	}
	if (latchBlock.branch) {
		latchBlock.branch = replaceIdentifiersInExpression(
			latchBlock.branch as t.Expression,
			copiedRegisterToHeaderTarget,
		) as LiftedAST<t.Expression>;
	}
	return true;
}

export function blockContainsIntrinsic(
	block: { body: LiftedAST<t.Statement>[] },
	name: string,
): boolean {
	return block.body.some((stmt) =>
		statementContainsIntrinsic(<t.Statement> stmt, name)
	);
}

export function blockContainsPhi(
	block: { body: LiftedAST<t.Statement>[] },
): boolean {
	return blockContainsIntrinsic(block, 'Phi');
}

function unresolvedPhiHasMultipleLiveOwners(
	func: IRFunction,
	phis: PhiContext,
	address: BlockAddr,
	block: IRBlock,
): boolean {
	if (func.guardedPhiMode === 'disabled') return false;
	if (
		!blockContainsPhi(block) ||
		!blockContainsIntrinsic(block, 'CreateClosure')
	) return false;
	// reduceSequence may merge several blocks in one invocation.
	phis.refreshLiveOwners();
	const sourceOwners = new AddressSet<BlockAddr>();
	for (const instruction of phis.phisInMergedBlock(address)) {
		for (const owner of phis.liveOwners(instruction.sources.keys())) {
			sourceOwners.add(owner);
		}
	}
	return sourceOwners.size > 1;
}

function isGeneratedAliasPrelude(body: LiftedAST<t.Statement>[]): boolean {
	if (body.length === 0) return true;
	return body.every((node) => {
		const stmt = node as t.Statement;
		if (!t.isVariableDeclaration(stmt, { kind: 'const' })) return false;
		if (stmt.declarations.length !== 1) return false;
		const [decl] = stmt.declarations;
		return t.isIdentifier(decl.id) &&
			/^r\d+_\d+$/.test(decl.id.name) &&
			t.isIdentifier(decl.init) &&
			(decl.init.name === 'global' ||
				isParameterExpression(decl.init));
	});
}

export function createLatchConditionResolver(
	body: readonly LiftedAST<t.Statement>[],
	preservedNames: ReadonlySet<string> = new Set(),
): (expression: t.Expression) => t.Expression {
	const constInits = new Map<string, t.Expression>();
	for (const stmt of body) {
		const statement = <t.Statement> stmt;
		if (!t.isVariableDeclaration(statement, { kind: 'const' })) continue;
		if (statement.declarations.length !== 1) continue;
		const [decl] = statement.declarations;
		if (!t.isIdentifier(decl.id)) continue;
		if (!t.isExpression(decl.init)) continue;
		constInits.set(decl.id.name, decl.init);
	}

	const resolve = (
		expr: t.Expression,
		seen = new Set<string>(),
	): t.Expression => {
		if (t.isIdentifier(expr) && preservedNames.has(expr.name)) {
			return <t.Expression> t.cloneNode(expr, true);
		}
		if (t.isIdentifier(expr)) {
			if (seen.has(expr.name)) {
				return <t.Expression> t.cloneNode(expr, true);
			}
			const init = constInits.get(expr.name);
			if (!init) return <t.Expression> t.cloneNode(expr, true);
			return resolve(init, new Set([...seen, expr.name]));
		}

		if (t.isMemberExpression(expr)) {
			const member = t.cloneNode(expr, true);
			if (t.isExpression(member.object)) {
				member.object = resolve(member.object, seen);
			}
			if (member.computed && t.isExpression(member.property)) {
				member.property = resolve(member.property, seen);
			}
			return member;
		}

		if (t.isBinaryExpression(expr)) {
			return t.binaryExpression(
				expr.operator,
				resolve(expr.left as t.Expression, seen),
				resolve(expr.right as t.Expression, seen),
			);
		}

		if (t.isUnaryExpression(expr)) {
			return t.unaryExpression(
				expr.operator,
				resolve(expr.argument, seen),
				expr.prefix,
			);
		}

		if (t.isLogicalExpression(expr)) {
			return t.logicalExpression(
				expr.operator,
				resolve(expr.left, seen),
				resolve(expr.right, seen),
			);
		}

		if (t.isConditionalExpression(expr)) {
			return t.conditionalExpression(
				resolve(expr.test, seen),
				resolve(expr.consequent, seen),
				resolve(expr.alternate, seen),
			);
		}

		return <t.Expression> t.cloneNode(expr, true);
	};
	return resolve;
}

export function resolveLatchCondition(
	latchBlock: { body: LiftedAST<t.Statement>[] },
	branch: t.Expression,
	preservedNames: ReadonlySet<string> = new Set(),
): t.Expression {
	return createLatchConditionResolver(
		latchBlock.body,
		preservedNames,
	)(branch);
}

export function removeLatchConditionDeclaration(
	latchBlock: { body: LiftedAST<t.Statement>[] },
	branch: t.Expression,
	preservedNames: ReadonlySet<string> = new Set(),
): void {
	if (!t.isIdentifier(branch)) return;

	const namesToRemove = new Set<string>([branch.name]);
	for (let changed = true; changed;) {
		changed = false;
		for (const stmt of latchBlock.body) {
			const statement = <t.Statement> stmt;
			if (!t.isVariableDeclaration(statement, { kind: 'const' })) {
				continue;
			}
			if (statement.declarations.length !== 1) continue;
			const [decl] = statement.declarations;
			if (!t.isIdentifier(decl.id) || !namesToRemove.has(decl.id.name)) {
				continue;
			}
			if (!t.isExpression(decl.init)) continue;

			const identifiers: string[] = [];
			t.traverseFast(decl.init, (node) => {
				if (t.isIdentifier(node)) identifiers.push(node.name);
			});
			for (const name of identifiers) {
				if (
					!preservedNames.has(name) && !namesToRemove.has(name)
				) {
					namesToRemove.add(name);
					changed = true;
				}
			}
		}
	}

	for (let i = latchBlock.body.length - 1; i >= 0; i--) {
		const statement = <t.Statement> latchBlock.body[i];
		if (!t.isVariableDeclaration(statement, { kind: 'const' })) continue;
		if (statement.declarations.length !== 1) continue;
		const [decl] = statement.declarations;
		if (
			t.isIdentifier(decl.id) && namesToRemove.has(decl.id.name) &&
			!preservedNames.has(decl.id.name)
		) latchBlock.body.splice(i, 1);
	}
}

function expressionsEqual(left: t.Expression, right: t.Expression): boolean {
	return JSON.stringify(comparableAst(left)) ===
		JSON.stringify(comparableAst(right));
}

export function statementsEqual(
	left: t.Statement,
	right: t.Statement,
): boolean {
	return JSON.stringify(comparableAst(left)) ===
		JSON.stringify(comparableAst(right));
}

export function stripFinalizerPrefixSuffix(
	body: t.Statement[],
	finalizerPrefix: t.Statement[],
): boolean {
	if (finalizerPrefix.length === 0 || body.length === 0) return false;
	for (let start = 0; start < body.length; start++) {
		const length = Math.min(body.length - start, finalizerPrefix.length);
		if (length < finalizerPrefix.length) continue;
		let matches = true;
		for (let i = 0; i < length; i++) {
			if (!statementsEqual(body[start + i], finalizerPrefix[i])) {
				matches = false;
				break;
			}
		}
		if (!matches) continue;
		body.splice(start);
		return true;
	}
	return false;
}

export function statementMatchesFinalizerCopy(
	copy: t.Statement,
	finalizer: t.Statement,
): boolean {
	return statementMatchesFinalizerPrefix(copy, finalizer);
}

function iteratorCloseRethrowAlias(
	stmt: t.Statement,
	errorName: string,
): string | null {
	if (!t.isVariableDeclaration(stmt, { kind: 'const' })) return null;
	if (stmt.declarations.length !== 1) return null;
	const [decl] = stmt.declarations;
	if (
		!t.isIdentifier(decl.id) ||
		!t.isIdentifier(decl.init, { name: errorName })
	) return null;
	return decl.id.name;
}

function isIteratorCloseCallStatement(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	return t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, { name: 'IteratorClose' }) &&
		expr.arguments.length === 2 &&
		t.isBooleanLiteral(expr.arguments[1], { value: true });
}

export function isIteratorCloseRethrowBody(
	body: t.Statement[],
	errorName: string,
) {
	let closeIndex = 0;
	let thrownName = errorName;
	if (body.length === 3) {
		const alias = iteratorCloseRethrowAlias(body[0], errorName);
		if (!alias) return false;
		thrownName = alias;
		closeIndex = 1;
	} else if (body.length !== 2) {
		return false;
	}

	const throwStmt = body[closeIndex + 1];
	return isIteratorCloseCallStatement(body[closeIndex]) &&
		t.isThrowStatement(throwStmt) &&
		t.isIdentifier(throwStmt.argument, { name: thrownName });
}

export function isSyntheticIteratorCleanupCatchBody(
	body: t.Statement[],
): boolean {
	let sawCatch = false;
	for (const stmt of body) {
		const decl = singleDeclarator(stmt);
		if (!decl || !t.isIdentifier(decl.id)) return false;
		if (
			t.isCallExpression(decl.init) &&
			t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Catch' })
		) {
			sawCatch = true;
			continue;
		}
		if (
			t.isIdentifier(decl.init) ||
			t.isBooleanLiteral(decl.init) ||
			(t.isCallExpression(decl.init) &&
				t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' }))
		) continue;
		return false;
	}
	return sawCatch;
}

function isIteratorCloseTrueStatement(stmt: t.Statement): boolean {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	return t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, { name: 'IteratorClose' }) &&
		expr.arguments.length === 2 &&
		t.isBooleanLiteral(expr.arguments[1], { value: true });
}

function isPhiOrFlagDeclaration(stmt: t.Statement): boolean {
	const decl = singleDeclarator(stmt);
	if (!decl || !t.isIdentifier(decl.id)) return false;
	return t.isIdentifier(decl.init) ||
		t.isBooleanLiteral(decl.init) ||
		(t.isCallExpression(decl.init) &&
			t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' }));
}

export function isSharedIteratorCloseRethrowTail(
	func: IRFunction,
	startAddr: BlockAddr | undefined,
): boolean {
	if (startAddr === undefined) return false;
	let sawIteratorClose = false;
	const visited = new AddressSet<BlockAddr>();
	const stack: BlockAddr[] = [startAddr];
	while (stack.length > 0) {
		const addr = stack.pop()!;
		if (visited.has(addr)) continue;
		visited.add(addr);
		const block = func.blocks.get(addr);
		if (!block) return false;

		for (let i = 0; i < block.body.length; i++) {
			const stmt = block.body[i] as t.Statement;
			if (isIteratorCloseTrueStatement(stmt)) {
				sawIteratorClose = true;
				continue;
			}
			if (
				i === block.body.length - 1 &&
				block.consequentAddresses.length === 0 &&
				t.isThrowStatement(stmt)
			) continue;
			if (isPhiOrFlagDeclaration(stmt)) continue;
			return false;
		}

		if (block.consequentAddresses.length === 0) {
			const last = block.body.at(-1) as t.Statement | undefined;
			if (!last || !t.isThrowStatement(last)) return false;
			continue;
		}
		if (block.consequentAddresses.length > 2) return false;
		for (const succ of block.consequentAddresses) stack.push(succ);
	}
	return sawIteratorClose;
}

export function replaceCatchCallsWithIdentifier(
	body: t.Statement[],
	errorName: string,
): boolean {
	let changed = false;
	const wrapped = t.file(t.program(body));
	traverse(wrapped, {
		CallExpression(path) {
			if (
				t.isV8IntrinsicIdentifier(path.node.callee, { name: 'Catch' })
			) {
				path.replaceWith(t.identifier(errorName));
				changed = true;
			}
		},
	});
	return changed;
}

function stripTerminalLoopGuard(
	loop: t.WhileStatement,
	continueTest: t.Expression,
): boolean {
	if (!t.isBlockStatement(loop.body)) return false;
	const last = loop.body.body.at(-1);
	if (!last || !t.isIfStatement(last)) return false;
	if (last.alternate) {
		if (
			!t.isBlockStatement(last.alternate) ||
			last.alternate.body.length !== 0
		) return false;
	}

	let consequent: t.Statement = last.consequent;
	if (t.isBlockStatement(consequent)) {
		if (consequent.body.length !== 1) return false;
		consequent = consequent.body[0];
	}
	if (!t.isBreakStatement(consequent)) return false;

	let guardContinueTest: t.Expression;
	if (t.isUnaryExpression(last.test, { operator: '!' })) {
		if (!t.isExpression(last.test.argument)) return false;
		guardContinueTest = last.test.argument;
	} else {
		guardContinueTest = invertTest(last.test);
	}

	const guardAlias = guardContinueTest;
	guardContinueTest = resolveLatchCondition(
		{ body: loop.body.body },
		guardContinueTest,
	);
	if (!expressionsEqual(guardContinueTest, continueTest)) return false;
	removeLatchConditionDeclaration({ body: loop.body.body }, guardAlias);
	loop.body.body.pop();
	return true;
}

export function tryAbsorbAndChainIntoLoop(
	andTest: t.Expression,
	body: t.Statement[],
	prefixBody: LiftedAST<t.Statement>[],
): t.Statement[] | null {
	if (!t.isLogicalExpression(andTest, { operator: '&&' })) return null;
	if (body.length !== 1) return null;
	const [only] = body;
	if (!t.isWhileStatement(only)) return null;

	const left = resolveLatchCondition({ body: prefixBody }, andTest.left);
	const right = resolveLatchCondition({ body: prefixBody }, andTest.right);
	if (!expressionsEqual(only.test, right)) return null;
	if (!stripTerminalLoopGuard(only, left)) return null;
	removeLatchConditionDeclaration({ body: prefixBody }, andTest.left);
	removeLatchConditionDeclaration({ body: prefixBody }, andTest.right);

	only.test = t.logicalExpression('&&', left, right);
	return body;
}

export function cloneBodyForPredecessor(
	func: IRFunction,
	blockAddr: BlockAddr,
	predecessorAddr: BlockAddr,
): t.Statement[] {
	const block = func.blocks.get(blockAddr)!;
	const originalBody = block.body as t.Statement[];
	const leading = leadingPhiDeclarations(block.body);
	const phis = phiContext(func);
	const resolved = phis.resolveUses(
		blockAddr,
		leading.map(({ name }) => name),
		originalBody.slice(leading.length),
	);
	if (!resolved) return cloneStatementList(block.body);

	// `func.ssa` is immutable, while CFG reducers lower Phis into explicit
	// accumulators. Only specialize Phi destinations that still have a concrete
	// use in the current AST. Renaming every destination from the original SSA
	// would rewrite a lowered accumulator back to one predecessor's stale source.
	const replacements = new Map<string, string>();
	for (const target of resolved.targets) {
		const source = phis.sourceForPredecessor(
			target.instruction,
			predecessorAddr,
		);
		// Specialization is transactional. If a merged predecessor represents
		// conflicting incoming values, retain the original Phi-bearing body.
		if (!source) return cloneStatementList(block.body);
		replacements.set(target.name, registerName(source));
	}

	const body = resolved.body;
	if (replacements.size === 0) return body;

	t.traverseFast(t.blockStatement(body), (node) => {
		if (!t.isIdentifier(node)) return;
		const replacement = replacements.get(node.name);
		if (replacement) node.name = replacement;
	});

	return body;
}

export function cloneStatementList(
	body: LiftedAST<t.Statement>[],
): t.Statement[] {
	return body.map((stmt) => t.cloneNode(stmt as t.Statement, true));
}
