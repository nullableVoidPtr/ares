import * as t from '@babel/types';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import type { SSABasicBlock } from '../../../ssa.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import { statementListEndsAbruptly } from '../../ast/completion.ts';
import type { IRBlock, LiftedAST } from '../../ast/mod.ts';
import { invertTest } from '../../ast/expression.ts';
import { typeOfIsExpression } from '../../ast/typeOfIs.ts';
import {
	type LivenessInfo,
	ssaLivenessAnalysis,
} from '../../../utils/liveness.ts';
import type { IRFunction } from '../mod.ts';
import { ssaRegisterEquals } from '../../../ssa.ts';
import { phiContext, PhiLoweringPlan, registerName } from './phi.ts';
import {
	blockContainsPhi,
	cloneBodyForPredecessor,
	cloneStatementList,
	leadingPhiDeclarations,
	statementsEqual,
	tryAbsorbAndChainIntoLoop,
} from './linear.ts';

/**
 * Move a merged block's Phi sources onto the block it merged into.
 *
 * A Phi source is an edge action keyed by predecessor. Merging `from` into `to`
 * deletes that predecessor, and `recoverPhiDescriptors` drops any source whose
 * edge no longer exists in the CFG -- so without this the value arriving on
 * that path is simply never assigned, which surfaces later as an unplaced edge
 * Phi action or a read of an undeclared register.
 *
 * Returns false when the move would collide with a different value already
 * arriving from `to`. That is a collapse which genuinely cannot be represented,
 * and it is the exact form of the check `collapseDestroysPhi` approximates: it
 * counts chain members that are *direct* Phi predecessors, and so misses a value
 * that reaches the join through a single-predecessor intermediate block.
 */
function repointPhiSources(
	func: IRFunction,
	from: BlockAddr,
	to: BlockAddr,
	apply: boolean,
): boolean {
	for (const ssaBlock of func.ssa.basicBlocks.values()) {
		for (const instr of ssaBlock.ssaInstructions) {
			if (instr.instruction !== 'Phi') continue;
			const moved = instr.sources.get(from);
			if (moved == null) continue;
			const existing = instr.sources.get(to);
			if (existing != null && !ssaRegisterEquals(existing, moved)) {
				return false;
			}
			if (!apply) continue;
			instr.sources.delete(from);
			if (existing == null) instr.sources.set(to, moved);
		}
	}
	return true;
}

export function reduceOrChain(func: IRFunction): boolean {
	let changed = false;

	// Predecessor-address sets for every live SSA phi. Collapsing a chain that
	// supplies two or more of a phi's sources would merge those distinct
	// predecessors into one block, leaving the phi unable to select per branch
	// (e.g. an eventType-to-name switch where each branch assigns a different
	// string). This reads the phi's true source edges. Dead phis are ignored:
	// collapsing them is harmless and the result is just elided.
	const liveness = ssaLivenessAnalysis(func.ssa);
	const phiSourcePreds: AddressSet[] = [];
	for (const [addr, ssaBlock] of func.ssa.basicBlocks) {
		const liveOut = liveness.blockLiveness.get(addr)?.liveOut;
		for (const instr of ssaBlock.ssaInstructions) {
			if (instr.instruction !== 'Phi') continue;
			if (!liveOut?.has(instr.destination.index)) continue;
			phiSourcePreds.push(new AddressSet(instr.sources.keys()));
		}
	}
	const collapseDestroysPhi = (chain: BlockAddr[]): boolean => {
		for (const preds of phiSourcePreds) {
			let count = 0;
			for (const a of chain) {
				if (preds.has(a) && ++count >= 2) return true;
			}
		}
		return false;
	};

	for (const [addr, block] of func.blocks) {
		if (!block.branch) continue;
		if (block.consequentAddresses.length !== 2) continue;

		const [left, right] = block.consequentAddresses;
		if (reduceSharedArmChain(func, addr, left, right)) return true;

		const rightBlock = func.blocks.get(right);
		if (!rightBlock) continue;

		// Walk the left (fallthrough) chain, collecting every block whose
		// right-branch also targets the same `right`.
		const chain: BlockAddr[] = [addr];
		const seen = new Set<BlockAddr>(chain);
		let currentLeft = left;

		while (currentLeft !== right && func.blocks.has(currentLeft)) {
			if (seen.has(currentLeft)) break;

			// Each intermediate block must be exclusively reachable from the
			// preceding chain member.
			if (func.predecessorsOf(currentLeft).size !== 1) break;

			const nextBlock = func.blocks.get(currentLeft)!;
			if (!nextBlock.branch) break;
			if (nextBlock.consequentAddresses.length !== 2) break;

			const [nextLeft, nextRight] = nextBlock.consequentAddresses;
			if (nextRight !== right) break;

			if (
				!func.exceptions.activeHandlersEqual(addr, currentLeft)
			) break;

			chain.push(currentLeft);
			seen.add(currentLeft);
			currentLeft = nextLeft;
		}

		if (chain.length < 2) continue;

		// `currentLeft` is the continuation (taken when all conditions are false).
		const continuationAddr = currentLeft;

		// Try OR pattern first: right is the exclusive body block, chain is the guard.
		// Try AND pattern second: continuationAddr is the exclusive success body, right is the failure.
		const predsOfRight = func.predecessorsOf(right);
		const rightShared = predsOfRight.size === chain.length &&
			chain.every((a) => predsOfRight.has(a)) &&
			func.exceptions.activeHandlersEqual(addr, right);
		const rightExclusive = !rightBlock.branch &&
			rightShared;

		const contBlock = func.blocks.get(continuationAddr);
		const contExclusive = !!contBlock && !contBlock.branch &&
			func.predecessorsOf(continuationAddr).size === 1 &&
			func.exceptions.activeHandlersEqual(addr, continuationAddr);

		if (!rightShared && !contExclusive) continue;

		// Don't collapse a chain that feeds two or more sources to a single phi.
		if (collapseDestroysPhi(chain)) continue;

		// The merged blocks stop being predecessors, and a Phi source keyed by a
		// predecessor that no longer exists is dropped rather than moved. Decide
		// before touching anything: refuse when the move would collide, and carry
		// the sources over when it would not.
		const merged = chain.slice(1);
		if (
			merged.some((child) => !repointPhiSources(func, child, addr, false))
		) continue;
		for (const child of merged) repointPhiSources(func, child, addr, true);

		// Carry each intermediate block's body into A so that register declarations
		// are visible for the variable inliner to substitute into the test expression.
		for (let i = 1; i < chain.length; i++) {
			block.body.push(...<t.Statement[]> func.blocks.get(chain[i])!.body);
		}

		if (rightShared) {
			// OR: `if (branch_A || branch_B || …) { right_body }`
			// Execution after the body continues at right's own exit.
			const afterBody = rightBlock.consequentAddresses.length === 1
				? rightBlock.consequentAddresses[0]
				: continuationAddr;

			let orTest: t.Expression = <t.Expression> block.branch;
			for (let i = 1; i < chain.length; i++) {
				orTest = t.logicalExpression(
					'||',
					orTest,
					<t.Expression> func.blocks.get(chain[i])!.branch,
				);
			}

			if (rightBlock.branch || afterBody !== continuationAddr) {
				// The all-false path is a distinct `else` branch. Building an
				// else-less `if` here would silently drop it. Instead collapse
				// only the condition: keep a single 2-way branch and let
				// reduceSimpleIf build the if/else.
				block.branch = orTest;
				block.consequentAddresses = [continuationAddr, right];
				for (let i = 1; i < chain.length; i++) {
					func.markMergedBlocks(addr, chain[i]);
				}
			} else {
				block.body.push(
					t.ifStatement(
						orTest,
						t.blockStatement(<t.Statement[]> rightBlock.body),
						null,
					),
				);
				block.branch = undefined;
				block.consequentAddresses = [afterBody];

				for (let i = 1; i < chain.length; i++) {
					func.markMergedBlocks(addr, chain[i]);
				}
				func.markMergedBlocks(addr, right);
			}
		} else {
			// AND: right is the shared failure path; continuationAddr is the exclusive success body.
			// Emit `if (condA && condB && …) { cont_body }` and fall through to right on failure.
			// When all branches are negations (!condX) the && terms are the stripped conditions;
			// otherwise wrap the OR in a leading ! so De Morgan applies.
			let andTest: t.Expression;
			if (
				chain.every((a) =>
					t.isUnaryExpression(
						func.blocks.get(a)!.branch as t.Node | null | undefined,
						{ operator: '!' },
					)
				)
			) {
				// All branches are !cond → strip and use &&
				let test: t.Expression =
					<t.Expression> (block.branch as t.UnaryExpression).argument;
				for (let i = 1; i < chain.length; i++) {
					test = t.logicalExpression(
						'&&',
						test,
						<t.Expression> (func.blocks.get(chain[i])!
							.branch as t.UnaryExpression).argument,
					);
				}
				andTest = test;
			} else {
				// Mixed negations → !(branch_A || branch_B || …)
				let orTest: t.Expression = <t.Expression> block.branch;
				for (let i = 1; i < chain.length; i++) {
					orTest = t.logicalExpression(
						'||',
						orTest,
						<t.Expression> func.blocks.get(chain[i])!.branch,
					);
				}
				andTest = invertTest(orTest);
			}

			const absorbedLoopBody = tryAbsorbAndChainIntoLoop(
				andTest,
				<t.Statement[]> contBlock!.body,
				block.body,
			);
			if (absorbedLoopBody) {
				block.body.push(...absorbedLoopBody);
			} else {
				block.body.push(
					t.ifStatement(
						andTest,
						t.blockStatement(<t.Statement[]> contBlock!.body),
						null,
					),
				);
			}
			block.branch = undefined;
			block.consequentAddresses = [right]; // failure is the natural successor

			for (let i = 1; i < chain.length; i++) {
				func.markMergedBlocks(addr, chain[i]);
			}
			func.markMergedBlocks(addr, continuationAddr);
		}

		changed = true;
	}

	return changed;
}

function inlineBranchWithMovableBody(
	body: t.Statement[],
	branch: t.Expression,
): { test: t.Expression; movableBody: t.Statement[] } | null {
	if (body.length === 0) {
		return { test: t.cloneNode(branch, true), movableBody: [] };
	}

	let branchDeclIndex = -1;
	let branchTest: t.Expression | null = null;
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (!t.isVariableDeclaration(stmt, { kind: 'const' })) continue;
		if (stmt.declarations.length !== 1) continue;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id) || !decl.init) continue;
		if (!t.isIdentifier(branch, { name: decl.id.name })) continue;
		branchDeclIndex = i;
		branchTest = t.cloneNode(decl.init, true);
		break;
	}
	if (branchTest === null) return null;

	const movableBody: t.Statement[] = [];
	for (let i = 0; i < body.length; i++) {
		if (i === branchDeclIndex) continue;
		const stmt = body[i];
		if (!t.isVariableDeclaration(stmt, { kind: 'const' })) return null;
		if (stmt.declarations.length !== 1) return null;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id) || !t.isIdentifier(decl.init)) return null;
		movableBody.push(t.cloneNode(stmt, true));
	}

	return { test: branchTest, movableBody };
}

function reduceSharedArmChain(
	func: IRFunction,
	addr: BlockAddr,
	innerAddr: BlockAddr,
	sharedAddr: BlockAddr,
): boolean {
	const block = func.blocks.get(addr)!;
	const inner = func.blocks.get(innerAddr);
	const shared = func.blocks.get(sharedAddr);
	if (!inner || !shared || !inner.branch) return false;
	if (inner.consequentAddresses.length !== 2) return false;
	if (!func.exceptions.activeHandlersEqual(addr, innerAddr)) return false;
	if (!func.exceptions.activeHandlersEqual(addr, sharedAddr)) return false;
	if (func.predecessorsOf(innerAddr).size !== 1) return false;

	const [innerLeft, innerRight] = inner.consequentAddresses;
	let sharedTest: t.Expression;
	let exclusiveAddr: BlockAddr;
	const inlinedInner = inlineBranchWithMovableBody(
		<t.Statement[]> inner.body,
		inner.branch as t.Expression,
	);
	if (!inlinedInner) return false;

	if (innerLeft === sharedAddr) {
		sharedTest = t.logicalExpression(
			'||',
			t.cloneNode(block.branch as t.Expression, true),
			invertTest(inlinedInner.test),
		);
		exclusiveAddr = innerRight;
	} else if (innerRight === sharedAddr) {
		sharedTest = t.logicalExpression(
			'||',
			t.cloneNode(block.branch as t.Expression, true),
			inlinedInner.test,
		);
		exclusiveAddr = innerLeft;
	} else {
		return false;
	}

	const exclusive = func.blocks.get(exclusiveAddr);
	if (!exclusive || shared.branch || exclusive.branch) return false;
	if (func.predecessorsOf(sharedAddr).size !== 2) return false;
	if (!func.predecessorsOf(sharedAddr).has(addr)) return false;
	if (!func.predecessorsOf(sharedAddr).has(innerAddr)) return false;
	if (!func.exceptions.activeHandlersEqual(addr, exclusiveAddr)) return false;

	if (
		shared.consequentAddresses.length === 1 &&
		exclusive.consequentAddresses.length === 1 &&
		shared.consequentAddresses[0] === exclusive.consequentAddresses[0]
	) {
		if (func.predecessorsOf(exclusiveAddr).size !== 1) return false;
		block.body.push(...inlinedInner.movableBody);
		block.body.push(
			t.ifStatement(
				sharedTest,
				t.blockStatement(<t.Statement[]> shared.body),
				t.blockStatement(<t.Statement[]> exclusive.body),
			),
		);
		block.branch = undefined;
		block.consequentAddresses = [shared.consequentAddresses[0]];
		func.markMergedBlocks(addr, innerAddr);
		func.markMergedBlocks(addr, sharedAddr);
		func.markMergedBlocks(addr, exclusiveAddr);
		return true;
	}

	if (
		shared.consequentAddresses.length !== 1 ||
		shared.consequentAddresses[0] !== exclusiveAddr
	) return false;
	const exclusivePreds = func.predecessorsOf(exclusiveAddr);
	if (!exclusivePreds.has(innerAddr) || !exclusivePreds.has(sharedAddr)) {
		return false;
	}

	block.body.push(...inlinedInner.movableBody);
	block.body.push(
		t.ifStatement(
			sharedTest,
			t.blockStatement(<t.Statement[]> shared.body),
			null,
		),
	);
	block.branch = undefined;
	block.consequentAddresses = [exclusiveAddr];
	func.markMergedBlocks(addr, innerAddr);
	func.markMergedBlocks(addr, sharedAddr);
	return true;
}

function trueSuccessor(block: IRBlock): BlockAddr | null {
	return block.consequentAddresses.length === 2
		? block.consequentAddresses[1]
		: null;
}

function falseSuccessor(block: IRBlock): BlockAddr | null {
	return block.consequentAddresses.length === 2
		? block.consequentAddresses[0]
		: null;
}

export function conditionForSuccessor(
	block: IRBlock,
	successor: BlockAddr,
): t.Expression | null {
	if (!block.branch || block.consequentAddresses.length !== 2) return null;
	if (trueSuccessor(block) === successor) {
		return t.cloneNode(<t.Expression> block.branch, true);
	}
	if (falseSuccessor(block) === successor) {
		return invertTest(<t.Expression> block.branch);
	}
	return null;
}

export function otherSuccessor(
	block: IRBlock,
	successor: BlockAddr,
): BlockAddr | null {
	const falseAddr = falseSuccessor(block);
	const trueAddr = trueSuccessor(block);
	if (falseAddr === successor) return trueAddr;
	if (trueAddr === successor) return falseAddr;
	return null;
}

function logicalAnd(left: t.Expression, right: t.Expression): t.Expression {
	return t.logicalExpression('&&', left, right);
}

function logicalOr(left: t.Expression, right: t.Expression): t.Expression {
	return t.logicalExpression('||', left, right);
}

function phiSourceNameForPredecessor(
	func: IRFunction,
	joinAddr: BlockAddr,
	phiName: string,
	predAddr: BlockAddr,
): string | null {
	const ssaBlock = func.ssa.basicBlocks.get(joinAddr);
	if (!ssaBlock) return null;
	for (const instr of ssaBlock.ssaInstructions) {
		if (instr.instruction !== 'Phi') continue;
		if (registerName(instr.destination) !== phiName) continue;
		const source = instr.sources.get(predAddr);
		return source ? registerName(source) : null;
	}
	return null;
}

function blockBodyWithPhiAssignment(
	block: IRBlock,
	phiName: string,
	sourceName: string,
): t.Statement[] {
	return [
		...cloneStatementList(block.body),
		t.expressionStatement(
			t.assignmentExpression(
				'=',
				t.identifier(phiName),
				t.identifier(sourceName),
			),
		),
	];
}

export function predecessorSetEquals(
	func: IRFunction,
	addr: BlockAddr,
	expected: BlockAddr[],
): boolean {
	const actual = func.predecessorsOf(addr);
	if (actual.size !== expected.length) return false;
	return expected.every((pred) => actual.has(pred));
}

export function reduceGuardedBooleanPhiPredicate(func: IRFunction): boolean {
	for (const [addr, block] of func.blocks) {
		if (!block.branch || block.consequentAddresses.length !== 2) continue;

		for (const guardAddr of block.consequentAddresses) {
			const valueAddr = otherSuccessor(block, guardAddr);
			if (valueAddr == null) continue;

			const guard = func.blocks.get(guardAddr);
			const value = func.blocks.get(valueAddr);
			if (!guard || !value || !guard.branch || value.branch) continue;
			if (guard.consequentAddresses.length !== 2) continue;
			if (value.consequentAddresses.length !== 1) continue;
			if (!predecessorSetEquals(func, guardAddr, [addr])) continue;

			const innerAddr = otherSuccessor(guard, valueAddr);
			if (innerAddr == null) continue;
			const inner = func.blocks.get(innerAddr);
			if (!inner || !inner.branch) continue;
			if (inner.consequentAddresses.length !== 2) continue;
			if (!inner.consequentAddresses.includes(valueAddr)) continue;
			if (!predecessorSetEquals(func, innerAddr, [guardAddr])) continue;
			if (
				!predecessorSetEquals(func, valueAddr, [
					addr,
					guardAddr,
					innerAddr,
				])
			) continue;

			const joinAddr = otherSuccessor(inner, valueAddr);
			if (joinAddr == null || value.consequentAddresses[0] !== joinAddr) {
				continue;
			}
			const join = func.blocks.get(joinAddr);
			if (!join) continue;
			if (!predecessorSetEquals(func, joinAddr, [innerAddr, valueAddr])) {
				continue;
			}
			if (
				![guardAddr, valueAddr, innerAddr, joinAddr].every((other) =>
					func.exceptions.activeHandlersEqual(addr, other)
				)
			) continue;

			const phis = leadingPhiDeclarations(join.body);
			if (phis.length !== 1) continue;
			const [phi] = phis;
			const innerSource = phiSourceNameForPredecessor(
				func,
				joinAddr,
				phi.name,
				innerAddr,
			);
			const valueSource = phiSourceNameForPredecessor(
				func,
				joinAddr,
				phi.name,
				valueAddr,
			);
			if (!innerSource || !valueSource) continue;

			const toGuard = conditionForSuccessor(block, guardAddr);
			const guardToInner = conditionForSuccessor(guard, innerAddr);
			const innerToJoin = conditionForSuccessor(inner, joinAddr);
			if (!toGuard || !guardToInner || !innerToJoin) continue;

			const valueAssignment = () =>
				blockBodyWithPhiAssignment(value, phi.name, valueSource);
			const innerBody: t.Statement[] = [
				...cloneStatementList(inner.body),
				t.ifStatement(
					innerToJoin,
					t.blockStatement([
						t.expressionStatement(
							t.assignmentExpression(
								'=',
								t.identifier(phi.name),
								t.identifier(innerSource),
							),
						),
					]),
					t.blockStatement(valueAssignment()),
				),
			];
			const guardBody: t.Statement[] = [
				...cloneStatementList(guard.body),
				t.ifStatement(
					guardToInner,
					t.blockStatement(innerBody),
					t.blockStatement(valueAssignment()),
				),
			];

			block.body.push(
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier(phi.name), null),
				]),
				t.ifStatement(
					toGuard,
					t.blockStatement(guardBody),
					t.blockStatement(valueAssignment()),
				),
				...cloneStatementList(join.body.slice(phis.length)),
			);
			block.branch = join.branch;
			block.consequentAddresses = join.consequentAddresses;

			for (const merged of [guardAddr, valueAddr, innerAddr, joinAddr]) {
				func.markMergedBlocks(addr, merged);
			}
			return true;
		}
	}

	return false;
}

function reduceEmptyPredicateChain(func: IRFunction): boolean {
	for (const [addr, block] of func.blocks) {
		if (!block.branch || block.body.length !== 0) continue;
		if (block.consequentAddresses.length !== 2) continue;

		for (const midAddr of block.consequentAddresses) {
			const mid = func.blocks.get(midAddr);
			if (!mid || !mid.branch || mid.body.length !== 0) continue;
			if (mid.consequentAddresses.length !== 2) continue;
			if (func.predecessorsOf(midAddr).size !== 1) continue;
			if (!func.exceptions.activeHandlersEqual(addr, midAddr)) continue;

			const directAddr = otherSuccessor(block, midAddr);
			if (directAddr == null) continue;
			const exitAddr = otherSuccessor(mid, directAddr);
			if (exitAddr == null) continue;

			const pathToMid = conditionForSuccessor(block, midAddr);
			const midToExit = conditionForSuccessor(mid, exitAddr);
			if (!pathToMid || !midToExit) continue;

			block.branch = logicalAnd(pathToMid, midToExit);
			block.consequentAddresses = [directAddr, exitAddr];
			func.markMergedBlocks(addr, midAddr);
			return true;
		}
	}

	return false;
}

function reduceSharedExitGuardChain(func: IRFunction): boolean {
	for (const [addr, block] of func.blocks) {
		if (!block.branch || block.consequentAddresses.length !== 2) continue;

		for (const nextAddr of block.consequentAddresses) {
			const next = func.blocks.get(nextAddr);
			if (!next || !next.branch || next.body.length !== 0) continue;
			if (next.consequentAddresses.length !== 2) continue;
			if (func.predecessorsOf(nextAddr).size !== 1) continue;
			if (!func.exceptions.activeHandlersEqual(addr, nextAddr)) continue;

			const exitAddr = otherSuccessor(block, nextAddr);
			if (exitAddr == null) continue;
			if (!next.consequentAddresses.includes(exitAddr)) continue;
			const bodyAddr = otherSuccessor(next, exitAddr);
			if (bodyAddr == null) continue;

			const blockToExit = conditionForSuccessor(block, exitAddr);
			const blockToNext = conditionForSuccessor(block, nextAddr);
			const nextToExit = conditionForSuccessor(next, exitAddr);
			if (!blockToExit || !blockToNext || !nextToExit) continue;

			block.branch = logicalOr(
				blockToExit,
				logicalAnd(blockToNext, nextToExit),
			);
			block.consequentAddresses = [bodyAddr, exitAddr];
			func.markMergedBlocks(addr, nextAddr);
			return true;
		}
	}

	return false;
}

function declaredIdentifierNames(body: LiftedAST<t.Statement>[]): Set<string> {
	const names = new Set<string>();
	for (const stmt of body) {
		t.traverseFast(stmt as t.Node, (node) => {
			if (t.isVariableDeclarator(node)) {
				t.traverseFast(node.id, (id) => {
					if (t.isIdentifier(id)) names.add(id.name);
				});
			} else if (t.isFunctionDeclaration(node) && node.id) {
				names.add(node.id.name);
			} else if (t.isClassDeclaration(node) && node.id) {
				names.add(node.id.name);
			}
		});
	}
	return names;
}

function referencesAnyIdentifier(
	body: LiftedAST<t.Statement>[],
	names: Set<string>,
): boolean {
	if (names.size === 0) return false;
	let found = false;
	for (const stmt of body) {
		t.traverseFast(stmt as t.Node, (node) => {
			if (found) return t.traverseFast.skip;
			if (t.isIdentifier(node) && names.has(node.name)) found = true;
		});
		if (found) return true;
	}
	return false;
}

function reduceSharedBodyPredicateChain(func: IRFunction): boolean {
	const phiContext_ = phiContext(func);
	for (const [addr, block] of func.blocks) {
		if (!block.branch || block.consequentAddresses.length !== 2) continue;

		for (const sharedAddr of block.consequentAddresses) {
			const shared = func.blocks.get(sharedAddr);
			if (!shared || shared.branch) continue;
			if (shared.consequentAddresses.length !== 1) continue;
			if (shared.body.length > 8) continue;
			if (leadingPhiDeclarations(shared.body).length !== 0) continue;
			if (!func.exceptions.activeHandlersEqual(addr, sharedAddr)) {
				continue;
			}

			let nextAddr = otherSuccessor(block, sharedAddr);
			if (nextAddr == null) continue;

			const guards: BlockAddr[] = [addr];
			const seen = new AddressSet<BlockAddr>([addr, sharedAddr]);
			let valid = true;
			while (true) {
				if (seen.has(nextAddr)) {
					valid = false;
					break;
				}

				const next = func.blocks.get(nextAddr);
				if (
					next &&
					next.branch &&
					next.consequentAddresses.length === 2 &&
					next.consequentAddresses.includes(sharedAddr)
				) {
					if (func.predecessorsOf(nextAddr).size !== 1) {
						valid = false;
						break;
					}
					if (!func.exceptions.activeHandlersEqual(addr, nextAddr)) {
						valid = false;
						break;
					}
					guards.push(nextAddr);
					seen.add(nextAddr);
					const successor = otherSuccessor(next, sharedAddr);
					if (successor == null) {
						valid = false;
						break;
					}
					nextAddr = successor;
					continue;
				}
				break;
			}
			if (!valid || guards.length < 2) continue;

			const continuationAddr = nextAddr;
			const continuation = func.blocks.get(continuationAddr);
			if (!continuation || continuation.branch) continue;
			const continuationPhis = leadingPhiDeclarations(continuation.body);
			if (continuationPhis.length > 4) continue;
			if (!func.exceptions.activeHandlersEqual(addr, continuationAddr)) {
				continue;
			}
			if (shared.consequentAddresses[0] !== continuationAddr) continue;
			if (!predecessorSetEquals(func, sharedAddr, guards)) continue;
			if (
				!predecessorSetEquals(func, continuationAddr, [
					guards.at(-1)!,
					sharedAddr,
				])
			) continue;

			const nestedNames = new Set<string>();
			for (const guardAddr of guards.slice(1)) {
				const guard = func.blocks.get(guardAddr)!;
				for (const name of declaredIdentifierNames(guard.body)) {
					nestedNames.add(name);
				}
			}
			if (
				referencesAnyIdentifier(shared.body, nestedNames) ||
				referencesAnyIdentifier(
					continuation.body.slice(continuationPhis.length),
					nestedNames,
				)
			) continue;

			const finalGuardAddr = guards.at(-1)!;
			const phiAssignments: Array<{
				name: string;
				shared: t.Expression;
				fallback: t.Expression;
			}> = [];
			let phiComplete = true;
			for (const phi of continuationPhis) {
				const instr = phiContext_.phiInMergedBlock(
					continuationAddr,
					phi.name,
				);
				if (!instr) {
					phiComplete = false;
					break;
				}
				const sharedSource = phiContext_.sourceExpressionForPredecessor(
					instr,
					sharedAddr,
				);
				const fallbackSource = phiContext_
					.sourceExpressionForPredecessor(
						instr,
						finalGuardAddr,
					);
				if (!sharedSource || !fallbackSource) {
					phiComplete = false;
					break;
				}
				phiAssignments.push({
					name: phi.name,
					shared: sharedSource,
					fallback: fallbackSource,
				});
			}
			if (!phiComplete) continue;

			const assignmentsFor = (
				key: 'shared' | 'fallback',
			): t.Statement[] =>
				phiAssignments.map((assignment) =>
					t.expressionStatement(t.assignmentExpression(
						'=',
						t.identifier(assignment.name),
						t.cloneNode(assignment[key], true),
					))
				);

			const sharedBody = () =>
				t.blockStatement(
					[
						...cloneStatementList(shared.body),
						...assignmentsFor('shared'),
					],
				);

			let alternateBody: t.Statement[] = assignmentsFor('fallback');
			for (let i = guards.length - 1; i >= 1; i--) {
				const guardAddr = guards[i];
				const guard = func.blocks.get(guardAddr)!;
				const test = conditionForSuccessor(guard, sharedAddr);
				if (!test) {
					valid = false;
					break;
				}
				const alternate = alternateBody.length > 0
					? t.blockStatement(alternateBody)
					: null;
				alternateBody = [
					...cloneStatementList(guard.body),
					t.ifStatement(test, sharedBody(), alternate),
				];
			}
			if (!valid) continue;

			const test = conditionForSuccessor(block, sharedAddr);
			if (!test) continue;
			const reducedBody = [...block.body] as Array<
				t.Statement | LiftedAST<t.Statement>
			>;
			if (phiAssignments.length > 0) {
				reducedBody.push(
					t.variableDeclaration(
						'let',
						phiAssignments.map(({ name }) =>
							t.variableDeclarator(t.identifier(name))
						),
					),
				);
			}
			reducedBody.push(
				t.ifStatement(
					test,
					sharedBody(),
					t.blockStatement(alternateBody),
				),
				...cloneStatementList(
					continuation.body.slice(continuationPhis.length),
				),
			);
			const plan = new PhiLoweringPlan(func);
			if (!plan.replaceBody(addr, reducedBody)) continue;
			if (
				!plan.replaceControlFlow(
					addr,
					continuation.branch,
					continuation.consequentAddresses,
				)
			) continue;
			if (!plan.commit()) continue;

			for (
				const merged of [
					...guards.slice(1),
					sharedAddr,
					continuationAddr,
				]
			) {
				func.markMergedBlocks(addr, merged);
			}
			return true;
		}
	}

	return false;
}

function commonTerminalSuffixLength(
	left: LiftedAST<t.Statement>[],
	right: LiftedAST<t.Statement>[],
): number {
	let length = 0;
	while (length < left.length && length < right.length) {
		const leftStmt = left[left.length - length - 1] as t.Statement;
		const rightStmt = right[right.length - length - 1] as t.Statement;
		if (!statementsEqual(leftStmt, rightStmt)) break;
		length++;
	}
	return length;
}

function alternateBodyForStatement(
	stmt: t.Statement | undefined,
): t.Statement[] | null {
	if (!t.isIfStatement(stmt) || !stmt.alternate) return null;
	return t.isBlockStatement(stmt.alternate)
		? stmt.alternate.body
		: [stmt.alternate];
}

function soleAlternateExpression(
	stmt: t.Statement | undefined,
): t.Expression | null {
	const alternateBody = alternateBodyForStatement(stmt);
	if (!alternateBody) return null;
	if (alternateBody.length !== 1) return null;
	const [alternateStmt] = alternateBody;
	if (!t.isExpressionStatement(alternateStmt)) return null;
	return alternateStmt.expression;
}

function trailingAlternateExpression(
	stmt: t.Statement | undefined,
): t.Expression | null {
	const alternateBody = alternateBodyForStatement(stmt);
	if (!alternateBody || alternateBody.length === 0) return null;
	const last = alternateBody.at(-1);
	if (!t.isExpressionStatement(last)) return null;
	return last.expression;
}

function stripTrailingAlternateExpression(stmt: t.Statement | undefined) {
	if (!t.isIfStatement(stmt) || !stmt.alternate) return false;
	const alternateBody = alternateBodyForStatement(stmt);
	if (!alternateBody || alternateBody.length === 0) return false;
	const last = alternateBody.at(-1);
	if (!t.isExpressionStatement(last)) return false;
	if (!t.isBlockStatement(stmt.alternate)) {
		stmt.alternate = null;
		return true;
	}
	stmt.alternate.body.pop();
	if (stmt.alternate.body.length === 0) stmt.alternate = null;
	return true;
}

function recoverMergedTypeOfIsConditionForSuccessor(
	func: IRFunction,
	addr: BlockAddr,
	block: IRBlock,
	successor: BlockAddr,
): t.Expression | null {
	if (block.branch || block.consequentAddresses.length !== 2) return null;

	const value = soleAlternateExpression(block.body.at(-1) as t.Statement);
	if (!value) return null;

	const merged = func.mergedBlocks.get(addr);
	if (!merged) return null;

	for (const mergedAddr of merged) {
		if (mergedAddr === addr) continue;
		const raw = func.ssa.basicBlocks.get(mergedAddr);
		if (!raw || !raw.predicate) continue;
		const predicate = raw.predicate;
		if (raw.consequentAddresses.length !== 2) continue;
		if (
			raw.consequentAddresses[0] !== block.consequentAddresses[0] ||
			raw.consequentAddresses[1] !== block.consequentAddresses[1]
		) continue;
		if (!('operation' in predicate)) continue;
		if (predicate.operation !== 'typeof-is') continue;

		const trueTest = typeOfIsExpression(
			t.cloneNode(value),
			predicate.typeIndex,
		);
		const test = raw.consequentAddresses[1] === successor
			? trueTest
			: raw.consequentAddresses[0] === successor
			? invertTest(trueTest)
			: null;
		if (!test) continue;
		return predicate.not ? invertTest(test) : test;
	}

	return null;
}

function recoverMergedBooleanConditionForSuccessor(
	func: IRFunction,
	addr: BlockAddr,
	block: IRBlock,
	successor: BlockAddr,
): t.Expression | null {
	if (block.branch || block.consequentAddresses.length !== 2) return null;

	const value = trailingAlternateExpression(
		block.body.at(-1) as t.Statement,
	);
	if (!value) return null;

	const merged = func.mergedBlocks.get(addr);
	if (!merged) return null;

	for (const mergedAddr of merged) {
		if (mergedAddr === addr) continue;
		const raw = func.ssa.basicBlocks.get(mergedAddr);
		if (!raw?.predicate) continue;
		const terminal = raw.ssaInstructions.at(-1);
		if (
			terminal?.instruction !== 'JmpTrue' &&
			terminal?.instruction !== 'JmpFalse'
		) continue;
		if (!('predicate' in raw.predicate) || !('not' in raw.predicate)) {
			continue;
		}
		if (raw.consequentAddresses.length !== 2) continue;
		if (
			raw.consequentAddresses[0] !== block.consequentAddresses[0] ||
			raw.consequentAddresses[1] !== block.consequentAddresses[1]
		) continue;

		let test = t.cloneNode(value, true);
		if (raw.predicate.not) test = invertTest(test);
		if (raw.consequentAddresses[1] === successor) return test;
		if (raw.consequentAddresses[0] === successor) return invertTest(test);
	}

	return null;
}

function localSSAExpressionForRegister(
	func: IRFunction,
	block: SSABasicBlock,
	register: { index: number },
): t.Expression | null {
	const expressions = new Map<string, t.Expression>();
	const key = (reg: { index: number }) => `${reg.index}`;
	for (const instr of block.ssaInstructions) {
		if (instr.instruction === 'Phi') continue;
		if (!('defs' in instr) || !('destination' in instr.defs)) continue;
		const destination = instr.defs.destination;
		if (!destination) continue;
		const destinationName = key(destination);

		switch (instr.instruction) {
			case 'LoadConst':
				expressions.set(destinationName, t.valueToNode(instr.value));
				break;
			case 'LoadParam':
				expressions.set(
					destinationName,
					func.getParam(instr.parameterIndex),
				);
				break;
			case 'Mov': {
				const source = expressions.get(key(instr.uses.source));
				if (source) {
					expressions.set(destinationName, t.cloneNode(source));
				}
				break;
			}
			case 'GetById': {
				const object = expressions.get(key(instr.uses.object));
				if (!object) break;
				const property = func.fromIdentifierRef(instr.property);
				expressions.set(
					destinationName,
					t.memberExpression(
						t.cloneNode(object),
						property,
						t.isStringLiteral(property),
					),
				);
				break;
			}
		}
	}
	const expression = expressions.get(key(register));
	return expression ? t.cloneNode(expression) : null;
}

function recoverMergedRelationalConditionForSuccessor(
	func: IRFunction,
	addr: BlockAddr,
	block: IRBlock,
	successor: BlockAddr,
): t.Expression | null {
	if (block.branch || block.consequentAddresses.length !== 2) return null;
	if (!trailingAlternateExpression(block.body.at(-1) as t.Statement)) {
		return null;
	}

	const merged = func.mergedBlocks.get(addr);
	if (!merged) return null;

	for (const mergedAddr of merged) {
		if (mergedAddr === addr) continue;
		const raw = func.ssa.basicBlocks.get(mergedAddr);
		if (!raw || !raw.predicate) continue;
		const predicate = raw.predicate;
		if (raw.consequentAddresses.length !== 2) continue;
		if (
			raw.consequentAddresses[0] !== block.consequentAddresses[0] ||
			raw.consequentAddresses[1] !== block.consequentAddresses[1]
		) continue;
		if (!('operation' in predicate) || !('left' in predicate)) continue;
		if (!predicate.right) continue;

		let left = localSSAExpressionForRegister(func, raw, predicate.left);
		let right = localSSAExpressionForRegister(func, raw, predicate.right);
		if (
			(!left || !right) &&
			(predicate.operation === '==' || predicate.operation === '===')
		) {
			const alternate = alternateBodyForStatement(
				block.body.at(-1) as t.Statement,
			);
			const trailing = alternate?.slice(-2);
			if (
				trailing?.length === 2 &&
				trailing.every((stmt) => t.isExpressionStatement(stmt))
			) {
				left = t.cloneNode(trailing[0].expression, true);
				right = t.cloneNode(trailing[1].expression, true);
			}
		}
		if (!left || !right) continue;

		let test: t.Expression = t.binaryExpression(
			predicate.operation,
			left,
			right,
		);
		if (predicate.not) test = invertTest(test);
		if (raw.consequentAddresses[1] === successor) return test;
		if (raw.consequentAddresses[0] === successor) return invertTest(test);
	}

	return null;
}

function conditionForSharedTerminalSuffix(
	func: IRFunction,
	addr: BlockAddr,
	block: IRBlock,
	successor: BlockAddr,
): t.Expression | null {
	return conditionForSuccessor(block, successor) ??
		recoverMergedBooleanConditionForSuccessor(
			func,
			addr,
			block,
			successor,
		) ??
		recoverMergedTypeOfIsConditionForSuccessor(
			func,
			addr,
			block,
			successor,
		) ??
		recoverMergedRelationalConditionForSuccessor(
			func,
			addr,
			block,
			successor,
		);
}

function reduceSharedTerminalSuffix(func: IRFunction): boolean {
	for (const [addr, block] of func.blocks) {
		if (block.consequentAddresses.length !== 2) continue;

		const [leftAddr, rightAddr] = block.consequentAddresses;
		const left = func.blocks.get(leftAddr);
		const right = func.blocks.get(rightAddr);
		if (!left || !right) continue;
		if (left.branch || right.branch) continue;
		if (
			left.consequentAddresses.length !== 0 ||
			right.consequentAddresses.length !== 0
		) continue;
		if (func.predecessorsOf(leftAddr).size !== 1) continue;
		if (func.predecessorsOf(rightAddr).size !== 1) continue;
		if (
			![leftAddr, rightAddr].every((succ) =>
				func.exceptions.activeHandlersEqual(addr, succ)
			)
		) continue;

		const suffixLength = commonTerminalSuffixLength(left.body, right.body);
		if (suffixLength === 0) continue;
		const leftPrefix = left.body.slice(0, left.body.length - suffixLength);
		const rightPrefix = right.body.slice(
			0,
			right.body.length - suffixLength,
		);
		const suffix = left.body.slice(left.body.length - suffixLength);
		const hoistedDeclarations: LiftedAST<t.VariableDeclaration>[] = [];
		const existingNames = declaredIdentifierNames(block.body);
		const leftStmt = leftPrefix[0] as t.Statement | undefined;
		if (
			leftPrefix.length === 1 &&
			rightPrefix.length === 0 &&
			t.isVariableDeclaration(leftStmt) &&
			leftStmt.declarations.length === 1
		) {
			const [declaration] = leftStmt.declarations;
			if (
				t.isIdentifier(declaration.id) &&
				t.isExpression(declaration.init) &&
				!existingNames.has(declaration.id.name) &&
				referencesAnyIdentifier(
					suffix,
					new Set([declaration.id.name]),
				)
			) {
				const alternateValue = trailingAlternateExpression(
					block.body.at(-1) as t.Statement,
				);
				if (alternateValue) {
					const id = t.cloneNode(declaration.id);
					hoistedDeclarations.push(t.variableDeclaration('let', [
						t.variableDeclarator(t.cloneNode(id)),
					]) as LiftedAST<t.VariableDeclaration>);
					leftPrefix[0] = t.expressionStatement(
						t.assignmentExpression(
							'=',
							t.cloneNode(id),
							t.cloneNode(declaration.init, true),
						),
					) as LiftedAST<t.ExpressionStatement>;
					rightPrefix.push(t.expressionStatement(
						t.assignmentExpression(
							'=',
							t.cloneNode(id),
							t.cloneNode(alternateValue, true),
						),
					) as LiftedAST<t.ExpressionStatement>);
				}
			}
		}
		if (
			leftPrefix.length === 0 &&
			rightPrefix.length === 0 &&
			hoistedDeclarations.length === 0
		) continue;
		if (leftPrefix.length > 8 || rightPrefix.length > 8) continue;

		const suffixEndsAbruptly = statementListEndsAbruptly(
			suffix as t.Statement[],
		);
		if (
			!suffixEndsAbruptly &&
			(statementListEndsAbruptly(leftPrefix as t.Statement[]) ||
				statementListEndsAbruptly(rightPrefix as t.Statement[]))
		) {
			continue;
		}

		const leftNames = declaredIdentifierNames(leftPrefix);
		const rightNames = declaredIdentifierNames(rightPrefix);
		if (
			referencesAnyIdentifier(suffix, leftNames) ||
			referencesAnyIdentifier(suffix, rightNames)
		) continue;

		const leftTest = conditionForSharedTerminalSuffix(
			func,
			addr,
			block,
			leftAddr,
		);
		if (!leftTest) continue;

		if (!block.branch) {
			stripTrailingAlternateExpression(block.body.at(-1) as t.Statement);
		}

		block.body.push(...cloneStatementList(hoistedDeclarations));
		if (leftPrefix.length > 0 || rightPrefix.length > 0) {
			block.body.push(
				t.ifStatement(
					leftTest,
					t.blockStatement(cloneStatementList(leftPrefix)),
					rightPrefix.length > 0
						? t.blockStatement(cloneStatementList(rightPrefix))
						: null,
				),
			);
		}
		block.body.push(...cloneStatementList(suffix));
		block.branch = undefined;
		block.consequentAddresses = [];
		func.markMergedBlocks(addr, leftAddr);
		func.markMergedBlocks(addr, rightAddr);
		return true;
	}

	return false;
}

export function reducePredicateGuardChains(func: IRFunction): boolean {
	return reduceEmptyPredicateChain(func) ||
		reduceSharedExitGuardChain(func) ||
		reduceSharedBodyPredicateChain(func) ||
		reduceSharedTerminalSuffix(func);
}

function sharedLiveInNeutralReturnTerminal(
	func: IRFunction,
	liveness: LivenessInfo,
	blockAddr: BlockAddr,
): BlockAddr | null {
	const block = func.blocks.get(blockAddr);
	if (!block) return null;
	if (func.predecessorsOf(blockAddr).size !== 1) return null;
	if (block.consequentAddresses.length !== 1) return null;

	const [terminalAddr] = block.consequentAddresses;
	const terminal = func.blocks.get(terminalAddr);
	if (!terminal) return null;
	if (terminal.branch) return null;
	if (terminal.consequentAddresses.length !== 0) return null;
	if (terminal.body.length !== 1) return null;
	const [stmt] = terminal.body as t.Statement[];
	if (!t.isReturnStatement(stmt) || stmt.argument != null) return null;
	if ((liveness.blockLiveness.get(terminalAddr)?.liveIn.size ?? 1) !== 0) {
		return null;
	}
	if (!func.exceptions.activeHandlersEqual(blockAddr, terminalAddr)) {
		return null;
	}
	if (
		func.exceptions.records.get(terminalAddr)?.canonicalFinallyAddress !=
			null
	) {
		return null;
	}

	return terminalAddr;
}

function lowerConditionalSuccessorPhis(
	func: IRFunction,
	successorAddr: BlockAddr,
	directPredecessor: BlockAddr | null,
	consequentPredecessor: BlockAddr,
	alternatePredecessor: BlockAddr | null,
): {
	names: string[];
	direct: t.Statement[];
	consequent: t.Statement[];
	alternate: t.Statement[];
	body: t.Statement[];
} | null {
	const phiContext_ = phiContext(func);
	const successor = func.blocks.get(successorAddr);
	if (!successor) return null;
	const leading = leadingPhiDeclarations(successor.body);
	const resolved = phiContext_.resolveUses(
		successorAddr,
		leading.map(({ name }) => name),
		successor.body.slice(leading.length) as t.Statement[],
	);
	if (!resolved) return null;
	if (leading.length === 0 && resolved.inlineCount === 0) {
		return {
			names: [],
			direct: [],
			consequent: [],
			alternate: [],
			body: resolved.body,
		};
	}

	const direct: t.Statement[] = [];
	const consequent: t.Statement[] = [];
	const alternate: t.Statement[] = [];
	const callSourceExpression = (
		predecessor: BlockAddr,
		target: (typeof resolved.targets)[number],
	): t.Expression | null => {
		const call = leading.find(({ name }) => name === target.name)?.call;
		if (
			!call || call.arguments.length !== target.instruction.sources.size
		) {
			return null;
		}
		const predecessorSources = phiContext_.mergedSourceAddresses(
			predecessor,
		);
		const indexes = [...target.instruction.sources.keys()].flatMap(
			(sourceAddress, index) =>
				predecessorSources.has(sourceAddress) ? [index] : [],
		);
		if (indexes.length !== 1) return null;
		const argument = call.arguments[indexes[0]];
		return t.isExpression(argument) ? t.cloneNode(argument, true) : null;
	};
	const stableSourceInitializer = (
		predecessor: BlockAddr,
		source: t.Expression,
	): t.Expression => {
		if (!t.isIdentifier(source)) return source;
		const sourceBlock = func.blocks.get(predecessor);
		if (!sourceBlock) return source;
		for (const statement of sourceBlock.body) {
			if (
				!t.isVariableDeclaration(statement as t.Node, {
					kind: 'const',
				}) ||
				(statement as t.VariableDeclaration).declarations.length !== 1
			) continue;
			const [declaration] = (statement as t.VariableDeclaration)
				.declarations;
			if (
				!t.isIdentifier(declaration.id, { name: source.name }) ||
				!declaration.init || !t.isExpression(declaration.init) ||
				!isStablePhiSourceExpression(declaration.init)
			) continue;
			return t.cloneNode(declaration.init, true);
		}
		return source;
	};
	for (const target of resolved.targets) {
		const expectedOwners = new AddressSet<BlockAddr>([
			consequentPredecessor,
			...(alternatePredecessor == null
				? (directPredecessor == null ? [] : [directPredecessor])
				: [alternatePredecessor]),
		]);
		const actualOwners = phiContext_.liveOwners(
			target.instruction.sources.keys(),
		);
		if (
			actualOwners.size !== expectedOwners.size ||
			![...actualOwners].every((owner) => expectedOwners.has(owner))
		) return null;
		const append = (statements: t.Statement[], predecessor: BlockAddr) => {
			let source = callSourceExpression(predecessor, target) ??
				phiContext_.sourceExpressionForPredecessor(
					target.instruction,
					predecessor,
				);
			if (!source) return false;
			source = stableSourceInitializer(predecessor, source);
			statements.push(t.expressionStatement(t.assignmentExpression(
				'=',
				t.identifier(target.name),
				source,
			)));
			return true;
		};
		if (!append(consequent, consequentPredecessor)) return null;
		if (alternatePredecessor != null) {
			if (!append(alternate, alternatePredecessor)) return null;
		} else if (directPredecessor != null) {
			if (!append(direct, directPredecessor)) return null;
		} else {
			return null;
		}
	}

	return {
		names: resolved.targets.map(({ name }) => name),
		direct,
		consequent,
		alternate,
		body: resolved.body,
	};
}

function isStablePhiSourceExpression(expression: t.Expression): boolean {
	if (
		t.isIdentifier(expression) || t.isThisExpression(expression) ||
		t.isLiteral(expression)
	) return true;
	if (
		t.isUnaryExpression(expression) &&
		expression.operator !== 'delete' && t.isExpression(expression.argument)
	) return isStablePhiSourceExpression(expression.argument);
	if (t.isBinaryExpression(expression)) {
		return t.isExpression(expression.left) &&
			isStablePhiSourceExpression(expression.left) &&
			isStablePhiSourceExpression(expression.right);
	}
	return false;
}

interface ReduceSimpleIfOptions {
	/**
	 * Region pre-normalisation must not consume a Phi predecessor without first
	 * materialising its edge copy. Ordinary compatibility reduction retains its
	 * existing permissive behaviour.
	 */
	preserveSuccessorPhis?: boolean;
	/**
	 * Restrict Region pre-normalisation to a Phi join whose successor branches.
	 */
	requireBranchingPhiSuccessor?: boolean;
}

export function reduceSimpleIf(
	func: IRFunction,
	options: ReduceSimpleIfOptions = {},
) {
	const liveness = ssaLivenessAnalysis(func.ssa);
	const simpleIfs = new AddressMap<{
		test: LiftedAST<t.Expression>;
		consequent: BlockAddr;
		consequentTerminal: BlockAddr | null;
		consequentContained: boolean;
		alternate: BlockAddr | null;
		alternateTerminal: BlockAddr | null;
		alternateContained: boolean;
		successor: BlockAddr | null;
	}>();

	const compareKey = (expr: t.Expression | undefined) => {
		if (!t.isBinaryExpression(expr)) return null;
		if (expr.operator !== '===' && expr.operator !== '!==') return null;
		return new Set([JSON.stringify(expr.left), JSON.stringify(expr.right)]);
	};

	const isCompareChainHead = (
		block: { branch?: LiftedAST<t.Expression> },
		leftBlock: { branch?: LiftedAST<t.Expression> },
		rightBlock: { branch?: LiftedAST<t.Expression> },
	) => {
		const current = compareKey(block.branch as t.Expression | undefined);
		if (!current) return false;
		for (const next of [leftBlock.branch, rightBlock.branch]) {
			const nextKey = compareKey(next as t.Expression | undefined);
			if (!nextKey) continue;
			for (const key of current) {
				if (nextKey.has(key)) return true;
			}
		}
		return false;
	};

	for (const [addr, block] of func.blocks) {
		if (!block.branch) continue;

		const successors = block.consequentAddresses;
		if (successors.length !== 2) {
			continue;
		}
		if (successors.includes(addr)) continue;

		const [left, right] = successors;
		const leftBlock = func.blocks.get(left);
		const rightBlock = func.blocks.get(right);
		if (!leftBlock || !rightBlock) continue;
		if (isCompareChainHead(block, leftBlock, rightBlock)) continue;
		const leftSuccessors = leftBlock.consequentAddresses;
		const rightSuccessors = rightBlock.consequentAddresses;

		let ifTest: LiftedAST<t.Expression>;
		let consequent: BlockAddr;
		let alternate: BlockAddr | null;
		let successor: BlockAddr | null;

		const containedLeft = func.predecessorsOf(left).size === 1;
		const containedRight = func.predecessorsOf(right).size === 1;

		const leftConsequent = leftSuccessors.length === 1 &&
			leftSuccessors[0] === right &&
			containedLeft;
		const rightConsequent = rightSuccessors.length === 1 &&
			rightSuccessors[0] === left &&
			containedRight;
		const ifElse = leftSuccessors.length === 1 &&
			rightSuccessors.length === 1 &&
			leftSuccessors[0] === rightSuccessors[0] &&
			containedLeft &&
			containedRight;

		const leftEarlyReturn = leftSuccessors.length === 0 &&
			containedLeft;
		const rightEarlyReturn = rightSuccessors.length === 0 &&
			containedRight;
		const bothEarlyReturn = leftEarlyReturn && rightEarlyReturn;
		const leftSharedEarlyReturn = sharedLiveInNeutralReturnTerminal(
			func,
			liveness,
			left,
		);
		const rightSharedEarlyReturn = sharedLiveInNeutralReturnTerminal(
			func,
			liveness,
			right,
		);
		let consequentTerminal: BlockAddr | null = null;
		let alternateTerminal: BlockAddr | null = null;

		if (ifElse || bothEarlyReturn) {
			ifTest = block.branch;
			successor = leftSuccessors[0] ?? null;

			consequent = right;
			alternate = left;
		} else if (leftConsequent || leftEarlyReturn) {
			ifTest = invertTest(block.branch as t.Expression);

			consequent = left;
			alternate = null;
			successor = right;
		} else if (leftSharedEarlyReturn !== null) {
			ifTest = invertTest(block.branch as t.Expression);

			consequent = left;
			consequentTerminal = leftSharedEarlyReturn;
			alternate = null;
			successor = right;
		} else if (rightConsequent || rightEarlyReturn) {
			ifTest = block.branch;

			consequent = right;
			alternate = null;
			successor = left;
		} else if (rightSharedEarlyReturn !== null) {
			ifTest = block.branch;

			consequent = right;
			consequentTerminal = rightSharedEarlyReturn;
			alternate = null;
			successor = left;
		} else {
			continue;
		}
		if (options.requireBranchingPhiSuccessor) {
			if (successor == null) continue;
			const successorBlock = func.blocks.get(successor);
			if (
				!successorBlock?.branch ||
				!blockContainsPhi(successorBlock) ||
				func.predecessorsOf(successor).size !== 2
			) continue;
		}

		const consequentContained = func.predecessorsOf(consequent).size === 1;
		const alternateContained = alternate === null ||
			func.predecessorsOf(alternate).size === 1;

		const headerCatches = func.exceptions.activeHandlersAtBlock(addr);
		if (
			!func.exceptions.activeHandlersParent(
				headerCatches,
				consequent,
			)
		) {
			if (
				consequentTerminal === null &&
				func.blocks.get(consequent)!.consequentAddresses.length !== 0
			) {
				continue;
			}
		} else if (
			alternate &&
			!func.exceptions.activeHandlersParent(
				headerCatches,
				alternate,
			)
		) {
			if (
				alternateTerminal === null &&
				func.blocks.get(alternate)!.consequentAddresses.length !== 0
			) {
				continue;
			}
		}

		simpleIfs.set(addr, {
			test: ifTest,
			consequent,
			consequentTerminal,
			consequentContained,
			alternate,
			alternateTerminal,
			alternateContained,
			successor,
		});
	}

	if (simpleIfs.size === 0) {
		return false;
	}
	let reduced = false;

	for (
		const [
			headerAddr,
			{
				test,
				consequent: consequentAddr,
				consequentTerminal,
				consequentContained,
				alternate: alternateAddr,
				alternateTerminal,
				alternateContained,
				successor: successorAddr,
			},
		] of simpleIfs
	) {
		const header = func.blocks.get(headerAddr)!;
		const consequent = func.blocks.get(consequentAddr)!;
		const alternate = alternateAddr
			? func.blocks.get(alternateAddr)!
			: null;

		const consequentBody = consequentContained
			? <t.Statement[]> consequent.body
			: <t.Statement[]> consequent.body.map((stmt) =>
				t.cloneNode(<t.Statement> stmt, true)
			);
		if (consequentTerminal !== null) {
			consequentBody.push(
				...cloneBodyForPredecessor(
					func,
					consequentTerminal,
					consequentAddr,
				),
			);
		}
		const alternateBody = alternate
			? (alternateContained
				? <t.Statement[]> alternate.body
				: <t.Statement[]> alternate.body.map((stmt) =>
					t.cloneNode(<t.Statement> stmt, true)
				))
			: null;
		if (alternateBody && alternateTerminal !== null) {
			alternateBody.push(
				...cloneBodyForPredecessor(
					func,
					alternateTerminal,
					alternateAddr!,
				),
			);
		}
		const phiLowering = successorAddr == null
			? null
			: lowerConditionalSuccessorPhis(
				func,
				successorAddr,
				alternateAddr == null ? headerAddr : null,
				consequentAddr,
				alternateAddr,
			);
		if (
			(((func.guardedPhiMode === 'enabled' ||
				options.preserveSuccessorPhis === true) &&
				successorAddr != null &&
				func.blocks.get(successorAddr) != null &&
				blockContainsPhi(func.blocks.get(successorAddr)!)) ||
				options.requireBranchingPhiSuccessor) &&
			phiLowering == null
		) continue;
		if (phiLowering) {
			consequentBody.push(...phiLowering.consequent);
			alternateBody?.push(...phiLowering.alternate);
			func.blocks.get(successorAddr!)!.body = phiLowering.body;
			if (phiLowering.names.length > 0) {
				const directInitializers = alternateAddr == null &&
						phiLowering.direct.length === phiLowering.names.length
					? phiLowering.direct.map((statement, index) => {
						if (!t.isExpressionStatement(statement)) return null;
						const assignment = statement.expression;
						if (
							!t.isAssignmentExpression(assignment, {
								operator: '=',
							}) ||
							!t.isIdentifier(assignment.left, {
								name: phiLowering.names[index],
							}) || !t.isExpression(assignment.right)
						) return null;
						return assignment.right;
					})
					: [];
				const canInitializeDirect = directInitializers.length > 0 &&
					directInitializers.every((value): value is t.Expression =>
						value != null
					);
				const declaration = t.variableDeclaration(
					'let',
					phiLowering.names.map((name, index) =>
						t.variableDeclarator(
							t.identifier(name),
							canInitializeDirect
								? directInitializers[index]
								: null,
						)
					),
				) as LiftedAST<t.VariableDeclaration>;
				if (canInitializeDirect) {
					declaration.extra = {
						...declaration.extra,
						isPotentialConditionalValue: true,
					};
				}
				header.body.push(declaration);
				if (!canInitializeDirect) {
					header.body.push(...phiLowering.direct);
				}
			}
		}

		header.branch = undefined;

		header.body.push(
			t.ifStatement(
				<t.Expression> test,
				t.blockStatement(consequentBody),
				alternateBody ? t.blockStatement(alternateBody) : null,
			),
		);

		if (consequentContained) {
			func.markMergedBlocks(headerAddr, consequentAddr);
		}
		if (alternateAddr && alternateContained) {
			func.markMergedBlocks(headerAddr, alternateAddr);
		}

		if (successorAddr !== null) {
			header.consequentAddresses = [successorAddr];
			// IR-level recognition: when the if-region is fully contained, any Phi at the
			// head of the merge block is a conditional-merge value. Mark it so the deferred
			// fold can collapse `let X = D; if (C) { X = R }` into ??/||/&&/?./ternary once
			// the (possibly multi-statement) RVal has been reduced to a single expression.
			if (
				consequentContained &&
				(alternateAddr === null || alternateContained)
			) {
				const successor = func.blocks.get(successorAddr);
				if (successor) markPotentialConditionalPhis(successor);
			}
		} else {
			header.consequentAddresses = [];
		}
		reduced = true;
	}

	return reduced;
}

function markPotentialConditionalPhis(block: IRBlock): void {
	for (const stmt of block.body) {
		// Phis are emitted at the head of a block; stop at the first non-Phi statement.
		if (
			!t.isVariableDeclaration(stmt as t.Node, { kind: 'const' }) ||
			(stmt as t.VariableDeclaration).declarations.length !== 1
		) break;
		const [decl] = (stmt as t.VariableDeclaration).declarations;
		if (
			!t.isCallExpression(decl.init) ||
			!t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })
		) break;
		(stmt as LiftedAST<t.VariableDeclaration>).extra = {
			...(stmt as LiftedAST<t.VariableDeclaration>).extra,
			isPotentialConditionalValue: true,
		};
	}
}
