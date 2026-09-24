import * as t from '@babel/types';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../utils/set.ts';
import { liftPhiNodesInBody } from '../../ast/phi.ts';
import { invertTest } from '../../ast/expression.ts';
import type { IRFunction } from '../mod.ts';
import { statementAlwaysTerminates } from '../finalizer.ts';
import { tryBuildForInOrOfStatement } from './iterator.ts';
import { registerName } from './phi.ts';
import { reduceSwitch } from './switch.ts';
import { reduceTryCatch } from './tryCatch.ts';
import { conditionForSuccessor, reduceSimpleIf } from './predicates.ts';
import {
	appendExclusiveLoopExit,
	computeImmediateDominators,
	computeLoopBody,
	isHeaderTestedProtectedBodyLoop,
	reduceInlineTerminal,
	reduceSharedLeadingPhi,
} from './terminals.ts';
import {
	expressionContainsIntrinsic,
	isScriptCompletionReturn,
	leadingPhiDeclarations,
	lowerLoopLatchPhiCopies,
	reduceSequence,
	reduceSharedSequenceEdge,
	removeLatchConditionDeclaration,
	resolveLatchCondition,
} from './linear.ts';
function extractTerminalContinuationFromSelfLoopBody(body: t.Statement[]) {
	const topLevel = extractTerminalIfFromStatementList(body);
	if (topLevel) {
		return {
			loopBody: [
				...topLevel.prefix,
				t.ifStatement(
					t.cloneNode(topLevel.ifStmt.test, true),
					t.blockStatement([t.breakStatement()]),
				),
				...topLevel.suffix,
			],
			exitBody: topLevel.exitBody,
		};
	}

	if (body.length !== 1) return null;
	const [stmt] = body;
	if (!t.isTryStatement(stmt) || !stmt.finalizer) return null;
	if (stmt.block.body.length === 0) return null;
	const tryBody = stmt.block.body;
	const nested = extractTerminalIfFromStatementList(tryBody);
	if (!nested) return null;
	const replacementTry = t.cloneNode(stmt, true);
	replacementTry.block.body = nested.suffix.map((tryStmt) =>
		t.cloneNode(tryStmt, true)
	);
	return {
		loopBody: [
			...nested.prefix,
			t.ifStatement(
				t.cloneNode(nested.ifStmt.test, true),
				t.blockStatement([t.breakStatement()]),
			),
			replacementTry,
		],
		exitBody: nested.exitBody,
	};
}

function extractTerminalIfFromStatementList(body: t.Statement[]) {
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (!t.isIfStatement(stmt) || stmt.alternate) continue;
		const consequent = t.isBlockStatement(stmt.consequent)
			? stmt.consequent.body
			: [stmt.consequent];
		const isDoneExit = isDoneContinuationTest(body, i, stmt);
		const terminates = isDoneExit ||
			statementListTerminatesGeneratedLoop(consequent);
		if (!terminates) continue;
		return {
			prefix: body.slice(0, i).map((prefixStmt) =>
				t.cloneNode(prefixStmt, true)
			),
			ifStmt: stmt,
			suffix: body.slice(i + 1).map((suffixStmt) =>
				t.cloneNode(suffixStmt, true)
			),
			exitBody: consequent.map((exitStmt) => t.cloneNode(exitStmt, true)),
		};
	}
}

function isDoneContinuationTest(
	body: t.Statement[],
	index: number,
	stmt: t.IfStatement,
) {
	if (isDoneMemberExpression(stmt.test)) return true;
	if (!t.isIdentifier(stmt.test)) return false;
	for (let i = index - 1; i >= 0; i--) {
		const decl = singleDeclarator(body[i]);
		if (!decl || !t.isIdentifier(decl.id, { name: stmt.test.name })) {
			continue;
		}
		return t.isExpression(decl.init) && isDoneMemberExpression(decl.init);
	}
	return false;
}

function singleDeclarator(stmt: t.Statement) {
	if (!t.isVariableDeclaration(stmt)) return null;
	if (stmt.declarations.length !== 1) return null;
	const [decl] = stmt.declarations;
	return t.isVariableDeclarator(decl) ? decl : null;
}

function isDoneMemberExpression(expr: t.Expression) {
	return t.isMemberExpression(expr) &&
		!expr.computed &&
		t.isIdentifier(expr.property, { name: 'done' });
}

function statementListTerminatesGeneratedLoop(stmts: t.Statement[]) {
	const last = stmts.at(-1);
	return !!last && statementTerminatesGeneratedLoop(last);
}

function statementTerminatesGeneratedLoop(stmt: t.Statement): boolean {
	if (statementAlwaysTerminates(stmt)) return true;
	if (t.isBlockStatement(stmt)) {
		return statementListTerminatesGeneratedLoop(stmt.body);
	}
	if (
		t.isWhileStatement(stmt) &&
		t.isBooleanLiteral(stmt.test, { value: true }) &&
		t.isBlockStatement(stmt.body)
	) {
		return statementListTerminatesGeneratedLoop(stmt.body.body);
	}
	if (t.isIfStatement(stmt)) {
		return !!stmt.alternate &&
			statementTerminatesGeneratedLoop(stmt.consequent) &&
			statementTerminatesGeneratedLoop(stmt.alternate);
	}
	if (t.isTryStatement(stmt)) {
		if (
			stmt.finalizer &&
			statementTerminatesGeneratedLoop(stmt.finalizer)
		) return true;
		const tryTerminates = statementTerminatesGeneratedLoop(stmt.block);
		const catchTerminates = stmt.handler != null &&
			statementTerminatesGeneratedLoop(stmt.handler.body);
		return tryTerminates && catchTerminates;
	}
	return false;
}

function fallbackWhileTrue(
	body: t.Statement[],
	continuation: t.Statement[] = [],
): t.Statement[] {
	const whileLoop = t.whileStatement(
		t.booleanLiteral(true),
		t.blockStatement(body),
	);
	whileLoop.extra = { ...whileLoop.extra, fromCFGLoop: true };
	const wrapped: t.Statement[] = [whileLoop, ...continuation];
	liftPhiNodesInBody(wrapped, { preserveLoopPhiDestinations: true });
	return wrapped;
}

function generatedRegisterFamily(name: string): string | null {
	return /^r(\d+)_\d+$/.exec(name)?.[1] ?? null;
}

function identifierMatchesGeneratedVersion(
	expression: t.Expression,
	identifier: t.Identifier,
): boolean {
	if (!t.isIdentifier(expression)) return false;
	if (expression.name === identifier.name) return true;
	const left = generatedRegisterFamily(expression.name);
	return left != null && left === generatedRegisterFamily(identifier.name);
}

function isPNameEmptyListTest(
	test: t.Expression | undefined,
	propertyList: t.Identifier,
): boolean {
	if (!t.isBinaryExpression(test, { operator: '===' })) return false;
	return (
		identifierMatchesGeneratedVersion(test.left, propertyList) &&
		t.isIdentifier(test.right, { name: 'undefined' })
	) || (
		identifierMatchesGeneratedVersion(test.right, propertyList) &&
		t.isIdentifier(test.left, { name: 'undefined' })
	);
}

function removeForInEmptyListGuard(
	func: IRFunction,
	header: BlockAddr,
	loopExits: AddressSet<BlockAddr>,
	propertyList: t.Identifier | undefined,
): boolean {
	if (!propertyList) return false;
	const predecessors = func.predecessorsOf(header);
	let changed = false;
	for (const predecessor of predecessors) {
		const block = func.blocks.get(predecessor);
		if (!block || block.consequentAddresses.length !== 2) continue;
		if (!block.consequentAddresses.includes(header)) continue;
		if (
			!block.consequentAddresses.some((successor) =>
				successor !== header && loopExits.has(successor)
			)
		) continue;
		if (
			!isPNameEmptyListTest(
				block.branch as t.Expression | undefined,
				propertyList,
			)
		) continue;
		block.branch = undefined;
		block.consequentAddresses = [header];
		changed = true;
	}
	return changed;
}

function restoreSyntheticPreheader(
	func: IRFunction,
	header: BlockAddr,
	syntheticPreheader: BlockAddr,
): void {
	for (const [address, block] of func.blocks) {
		if (address === syntheticPreheader) continue;
		if (!block.consequentAddresses.includes(syntheticPreheader)) continue;
		block.consequentAddresses = block.consequentAddresses.map((successor) =>
			successor === syntheticPreheader ? header : successor
		) as BlockAddr[];
	}
}

interface NaturalLoopPlanBase {
	header: BlockAddr;
	latch: BlockAddr;
	body: AddressSet<BlockAddr>;
}

interface HeaderTestedLoopPlan extends NaturalLoopPlanBase {
	bodyEntry: BlockAddr;
	loopExit: BlockAddr;
	breakTest: t.Expression;
}

type NaturalLoopMutationPlan =
	| ({ kind: 'twoBlockHeaderTested' } & HeaderTestedLoopPlan)
	| ({ kind: 'reducibleHeaderTested' } & HeaderTestedLoopPlan)
	| (NaturalLoopPlanBase & {
		kind: 'unconditionalSelfLoop';
		terminalContinuation: ReturnType<
			typeof extractTerminalContinuationFromSelfLoopBody
		>;
	})
	| (NaturalLoopPlanBase & {
		kind: 'conditionalSelfLoop';
		loopExit: BlockAddr;
		breakTest: t.Expression;
	})
	| (NaturalLoopPlanBase & {
		kind: 'terminalExits';
		backEdgeIsRight: boolean;
		exitAddr: BlockAddr;
		terminalExits: AddressSet<BlockAddr>;
	})
	| (NaturalLoopPlanBase & {
		kind: 'latchTested';
		backEdgeIsRight: boolean;
		exitAddr: BlockAddr;
	});

function cloneLoopBreakTest(
	branch: t.Expression,
	rightContinues: boolean,
): t.Expression {
	return rightContinues ? invertTest(branch) : t.cloneNode(branch, true);
}

function planNaturalLoopMutation(
	func: IRFunction,
	header: BlockAddr,
	latch: BlockAddr,
): NaturalLoopMutationPlan {
	const headerBlock = func.blocks.get(header)!;
	const latchBlock = func.blocks.get(latch)!;
	const body = computeLoopBody(func, header, latch);
	const base: NaturalLoopPlanBase = { header, latch, body };

	if (
		headerBlock.branch && !latchBlock.branch && body.size === 2 &&
		body.has(latch)
	) {
		const [left, right] = headerBlock.consequentAddresses;
		const leftInLoop = body.has(left);
		const rightInLoop = body.has(right);
		if (leftInLoop !== rightInLoop) {
			return {
				...base,
				kind: 'twoBlockHeaderTested',
				bodyEntry: leftInLoop ? left : right,
				loopExit: leftInLoop ? right : left,
				breakTest: cloneLoopBreakTest(
					headerBlock.branch as t.Expression,
					rightInLoop,
				),
			};
		}
	}

	if (
		headerBlock.branch && !latchBlock.branch &&
		latchBlock.consequentAddresses.length === 1 &&
		latchBlock.consequentAddresses[0] === header
	) {
		const [left, right] = headerBlock.consequentAddresses;
		const leftInLoop = body.has(left);
		const rightInLoop = body.has(right);
		if (leftInLoop !== rightInLoop) {
			return {
				...base,
				kind: 'reducibleHeaderTested',
				bodyEntry: leftInLoop ? left : right,
				loopExit: leftInLoop ? right : left,
				breakTest: cloneLoopBreakTest(
					headerBlock.branch as t.Expression,
					rightInLoop,
				),
			};
		}
	}

	if (
		!headerBlock.branch && latch === header &&
		headerBlock.consequentAddresses.length === 1 &&
		headerBlock.consequentAddresses[0] === header
	) {
		return {
			...base,
			kind: 'unconditionalSelfLoop',
			terminalContinuation: extractTerminalContinuationFromSelfLoopBody(
				headerBlock.body as t.Statement[],
			),
		};
	}

	if (headerBlock.branch && latch === header) {
		const [left, right] = headerBlock.consequentAddresses;
		const leftIsSelf = left === header;
		const rightIsSelf = right === header;
		if (leftIsSelf !== rightIsSelf) {
			return {
				...base,
				kind: 'conditionalSelfLoop',
				loopExit: leftIsSelf ? right : left,
				breakTest: cloneLoopBreakTest(
					headerBlock.branch as t.Expression,
					rightIsSelf,
				),
			};
		}
	}

	const [latchLeft, latchRight] = latchBlock.consequentAddresses;
	const backEdgeIsRight = latchRight === header;
	const exitAddr = backEdgeIsRight ? latchLeft : latchRight;
	const hasExternalExitPredecessor = (exit: BlockAddr) =>
		[...func.predecessorsOf(exit)].some((pred) => !body.has(pred));
	const latchNormalExitIsTerminal = latchBlock.branch != null &&
		exitAddr != null &&
		!body.has(exitAddr) &&
		!hasExternalExitPredecessor(exitAddr) &&
		func.blocks.get(exitAddr)?.consequentAddresses.length === 0;
	const allExitsTerminal = [...body].every((addr) => {
		const block = func.blocks.get(addr);
		if (!block) return false;
		return block.consequentAddresses.every((succ) =>
			body.has(succ) || succ === header ||
			(!hasExternalExitPredecessor(succ) &&
				func.blocks.get(succ)?.consequentAddresses.length === 0)
		);
	}) && !latchNormalExitIsTerminal;

	if (allExitsTerminal) {
		const terminalExits = new AddressSet<BlockAddr>();
		for (const addr of body) {
			for (
				const successor of func.blocks.get(addr)!.consequentAddresses
			) {
				if (!body.has(successor) && successor !== header) {
					terminalExits.add(successor);
				}
			}
		}
		return {
			...base,
			kind: 'terminalExits',
			backEdgeIsRight,
			exitAddr,
			terminalExits,
		};
	}

	return {
		...base,
		kind: 'latchTested',
		backEdgeIsRight,
		exitAddr,
	};
}

function declaredNames(statements: readonly t.Statement[]): Set<string> {
	const names = new Set<string>();
	for (const statement of statements) {
		for (const name of Object.keys(t.getBindingIdentifiers(statement))) {
			names.add(name);
		}
	}
	return names;
}

function statementsReferenceNames(
	statements: readonly t.Statement[],
	names: ReadonlySet<string>,
): boolean {
	if (names.size === 0) return false;
	let found = false;
	for (const statement of statements) {
		t.traverseFast(statement, (node) => {
			if (found) return t.traverseFast.skip;
			if (t.isIdentifier(node) && names.has(node.name)) found = true;
		});
		if (found) return true;
	}
	return false;
}

/**
 * Collapse a sequence of loop filters that all enter one shared body and
 * otherwise advance through the common latch. A boolean gate keeps a large
 * shared body single-copy while preserving each guard's evaluation order.
 */
function reduceSharedLoopGuardChain(
	func: IRFunction,
	body: ReadonlySet<BlockAddr>,
	latch: BlockAddr,
): boolean {
	const latchBlock = func.blocks.get(latch);
	if (!latchBlock || leadingPhiDeclarations(latchBlock.body).length > 0) {
		return false;
	}

	for (const [address, block] of func.blocks) {
		if (
			address === latch || !body.has(address) || !block.branch ||
			block.consequentAddresses.length !== 2
		) continue;

		for (const sharedAddress of block.consequentAddresses) {
			const shared = func.blocks.get(sharedAddress);
			if (
				!shared || !body.has(sharedAddress) ||
				leadingPhiDeclarations(shared.body).length > 0 ||
				!func.exceptions.activeHandlersEqual(address, sharedAddress)
			) continue;
			const sharedContinuation = shared.branch &&
					shared.consequentAddresses.length === 2 &&
					shared.consequentAddresses.includes(latch)
				? shared.consequentAddresses.find((candidate) =>
					candidate !== latch
				)
				: !shared.branch &&
						shared.consequentAddresses.length === 1 &&
						shared.consequentAddresses[0] === latch
				? null
				: undefined;
			if (sharedContinuation === undefined) continue;

			const guards = [address];
			let next = block.consequentAddresses.find((candidate) =>
				candidate !== sharedAddress
			);
			while (next != null && next !== latch) {
				const guard = func.blocks.get(next);
				if (
					!guard || !body.has(next) || !guard.branch ||
					guard.consequentAddresses.length !== 2 ||
					!guard.consequentAddresses.includes(sharedAddress) ||
					func.predecessorsOf(next).size !== 1 ||
					!func.exceptions.activeHandlersEqual(address, next)
				) break;
				guards.push(next);
				next = guard.consequentAddresses.find((candidate) =>
					candidate !== sharedAddress
				);
			}
			if (guards.length < 2 || next !== latch) continue;
			const sharedPredecessors = func.predecessorsOf(sharedAddress);
			if (
				sharedPredecessors.size !== guards.length ||
				!guards.every((guard) => sharedPredecessors.has(guard))
			) continue;

			const nestedNames = new Set<string>();
			for (const guardAddress of guards.slice(1)) {
				for (
					const name of declaredNames(
						func.blocks.get(guardAddress)!.body as t.Statement[],
					)
				) nestedNames.add(name);
			}
			if (
				statementsReferenceNames(
					shared.body as t.Statement[],
					nestedNames,
				)
			) continue;

			const gate = t.identifier(
				`_cfgLoopGuard_${func.id}_${address}_${sharedAddress}`,
			);
			const setGate = () =>
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.cloneNode(gate),
					t.booleanLiteral(true),
				));
			let alternate: t.Statement[] = [];
			let valid = true;
			for (let i = guards.length - 1; i >= 1; i--) {
				const guard = func.blocks.get(guards[i]!)!;
				const test = conditionForSuccessor(guard, sharedAddress);
				if (!test) {
					valid = false;
					break;
				}
				alternate = [
					...guard.body as t.Statement[],
					t.ifStatement(
						test,
						t.blockStatement([setGate()]),
						alternate.length > 0
							? t.blockStatement(alternate)
							: null,
					),
				];
			}
			if (!valid) continue;
			const test = conditionForSuccessor(block, sharedAddress);
			if (!test) continue;

			const declarations = [
				t.variableDeclarator(
					t.cloneNode(gate),
					t.booleanLiteral(false),
				),
			];
			let sharedBody = shared.body as t.Statement[];
			if (sharedContinuation == null) {
				block.branch = undefined;
				block.consequentAddresses = [latch];
			} else {
				const continuationTest = conditionForSuccessor(
					shared,
					sharedContinuation,
				);
				if (!continuationTest) continue;
				const takeContinuation = t.identifier(
					`_cfgLoopGuardNext_${func.id}_${address}_${sharedAddress}`,
				);
				declarations.push(t.variableDeclarator(
					t.cloneNode(takeContinuation),
					t.booleanLiteral(false),
				));
				sharedBody = [
					...sharedBody,
					t.expressionStatement(t.assignmentExpression(
						'=',
						t.cloneNode(takeContinuation),
						continuationTest,
					)),
				];
				block.branch = t.cloneNode(takeContinuation);
				block.consequentAddresses = [latch, sharedContinuation];
			}
			block.body.push(
				t.variableDeclaration('let', declarations),
				t.ifStatement(
					test,
					t.blockStatement([setGate()]),
					t.blockStatement(alternate),
				),
				t.ifStatement(
					t.cloneNode(gate),
					t.blockStatement(sharedBody),
				),
			);
			for (const merged of [...guards.slice(1), sharedAddress]) {
				func.markMergedBlocks(address, merged);
			}
			return true;
		}
	}
	return false;
}

function assertNaturalLoopBodyCollapsed(
	func: IRFunction,
	header: BlockAddr,
	body: ReadonlySet<BlockAddr>,
): void {
	const remaining = [...body].filter((address) =>
		address !== header && func.blocks.has(address)
	);
	if (remaining.length === 0) return;
	throw new Error(
		`natural loop 0x${header.toString(16)} retained body blocks: ${
			remaining.map((address) => `0x${address.toString(16)}`).join(', ')
		}`,
	);
}

function applyNaturalLoopMutationPlan(
	func: IRFunction,
	plan: NaturalLoopMutationPlan,
	requireCollapsedBody: boolean,
): void {
	const { header, latch, body } = plan;
	const headerBlock = func.blocks.get(header)!;
	const latchBlock = func.blocks.get(latch)!;

	if (plan.kind === 'twoBlockHeaderTested') {
		const { bodyEntry, loopExit, breakTest } = plan;
		const bodyEntryBlock = func.blocks.get(bodyEntry)!;
		const whileBody = [
			...<t.Statement[]> headerBlock.body,
			t.ifStatement(
				breakTest,
				t.blockStatement([t.breakStatement()]),
			),
			...<t.Statement[]> bodyEntryBlock.body,
		];
		const structuredLoop = tryBuildForInOrOfStatement(
			func,
			header,
			body,
			whileBody,
			loopExit,
		);
		if (structuredLoop) {
			headerBlock.body = [
				structuredLoop.loop,
				...structuredLoop.exitStatements,
			];
			headerBlock.branch = undefined;
			headerBlock.consequentAddresses = [loopExit];
			func.markMergedBlocks(header, bodyEntry);

			removeForInEmptyListGuard(
				func,
				header,
				new AddressSet([loopExit]),
				structuredLoop.PNameArray,
			);

			return;
		}
		headerBlock.body = fallbackWhileTrue(whileBody);
		headerBlock.branch = undefined;
		headerBlock.consequentAddresses = [loopExit];
		func.markMergedBlocks(header, bodyEntry);
		return;
	}

	if (plan.kind === 'reducibleHeaderTested') {
		const SYNTHETIC_CONTINUE = -1 as BlockAddr;
		const SYNTHETIC_BREAK = -2 as BlockAddr;
		const PREHEADER_DUMMY = -3 as BlockAddr;
		const LOOP_EXIT_DUMMY = -4 as BlockAddr;
		const { bodyEntry, loopExit, breakTest } = plan;

		func.blocks.set(PREHEADER_DUMMY, {
			address: PREHEADER_DUMMY,
			body: [],
			branch: t.booleanLiteral(true),
			consequentAddresses: [header, PREHEADER_DUMMY],
		});
		func.blocks.set(LOOP_EXIT_DUMMY, {
			address: LOOP_EXIT_DUMMY,
			body: [],
			branch: t.booleanLiteral(true),
			consequentAddresses: [loopExit, LOOP_EXIT_DUMMY],
			kind: 'synthetic',
			syntheticReason: 'natural-loop-exit-guard',
		});
		func.mergedBlocks.set(LOOP_EXIT_DUMMY, new AddressSet());
		func.blocks.set(SYNTHETIC_CONTINUE, {
			address: SYNTHETIC_CONTINUE,
			body: [t.continueStatement()],
			branch: undefined,
			consequentAddresses: [],
		});
		func.mergedBlocks.set(SYNTHETIC_CONTINUE, new AddressSet());
		func.blocks.set(SYNTHETIC_BREAK, {
			address: SYNTHETIC_BREAK,
			body: [t.breakStatement()],
			branch: undefined,
			consequentAddresses: [],
			kind: 'synthetic',
			terminalKind: 'break',
			syntheticReason: 'natural-loop-break',
		});
		func.mergedBlocks.set(SYNTHETIC_BREAK, new AddressSet());

		const externalHeaderPredecessors = [...func.predecessorsOf(header)]
			.filter((pred) => pred !== PREHEADER_DUMMY && !body.has(pred));
		for (const pred of externalHeaderPredecessors) {
			const predBlock = func.blocks.get(pred);
			if (!predBlock) continue;
			predBlock.consequentAddresses = <BlockAddr[]> predBlock
				.consequentAddresses.map((succ) =>
					succ === header ? PREHEADER_DUMMY : succ
				);
		}

		headerBlock.body.push(
			t.ifStatement(
				breakTest,
				t.blockStatement([t.breakStatement()]),
			),
		);
		headerBlock.branch = undefined;
		headerBlock.consequentAddresses = [bodyEntry];
		latchBlock.consequentAddresses = [SYNTHETIC_CONTINUE];

		const redirectBodyExits = () => {
			for (const [addr, block] of func.blocks) {
				if (
					addr === header || addr === loopExit ||
					addr === PREHEADER_DUMMY ||
					addr === SYNTHETIC_CONTINUE || addr === SYNTHETIC_BREAK
				) continue;
				if (!body.has(addr)) continue;
				block.consequentAddresses = <BlockAddr[]> block
					.consequentAddresses.map((succ) =>
						succ === loopExit ? SYNTHETIC_BREAK : succ
					);
			}
		};
		redirectBodyExits();

		let inner;
		do {
			inner = false;
			redirectBodyExits();
			const currentHeader = func.blocks.get(header);
			if (
				currentHeader && !currentHeader.branch &&
				currentHeader.consequentAddresses.length === 0
			) break;
			inner = reduceSequence(func) || inner;
			inner = reduceInlineTerminal(func, {
				excludeAddresses: new Set([header, loopExit]),
			}) || inner;
			inner = reduceSwitch(func) || inner;
			inner = reduceSimpleIf(func) || inner;
			inner = reduceTryCatch(func) || inner;
		} while (inner);
		if (requireCollapsedBody) {
			assertNaturalLoopBodyCollapsed(func, header, body);
		}

		func.blocks.delete(LOOP_EXIT_DUMMY);
		func.mergedBlocks.delete(LOOP_EXIT_DUMMY);
		const currentHeader = func.blocks.get(header)!;
		restoreSyntheticPreheader(func, header, PREHEADER_DUMMY);
		const structuredLoop = tryBuildForInOrOfStatement(
			func,
			header,
			body,
			<t.Statement[]> currentHeader.body,
			loopExit,
		);
		if (structuredLoop) {
			currentHeader.body = [
				structuredLoop.loop,
				...structuredLoop.exitStatements,
			];
			currentHeader.branch = undefined;
			appendExclusiveLoopExit(func, currentHeader, header, loopExit);

			removeForInEmptyListGuard(
				func,
				header,
				new AddressSet([loopExit]),
				structuredLoop.PNameArray,
			);
		} else {
			currentHeader.body = fallbackWhileTrue(
				<t.Statement[]> currentHeader.body,
			);
			currentHeader.branch = undefined;
			appendExclusiveLoopExit(func, currentHeader, header, loopExit);
		}
		func.blocks.delete(SYNTHETIC_CONTINUE);
		func.blocks.delete(SYNTHETIC_BREAK);
		func.blocks.delete(PREHEADER_DUMMY);
		func.mergedBlocks.delete(SYNTHETIC_CONTINUE);
		func.mergedBlocks.delete(SYNTHETIC_BREAK);
		func.mergedBlocks.delete(PREHEADER_DUMMY);
		return;
	}

	if (plan.kind === 'unconditionalSelfLoop') {
		const { terminalContinuation } = plan;
		const loopBody = terminalContinuation?.loopBody ??
			(headerBlock.body as t.Statement[]);
		const structuredLoop = tryBuildForInOrOfStatement(
			func,
			header,
			body,
			loopBody,
			header,
			terminalContinuation?.exitBody,
		);
		if (structuredLoop) {
			headerBlock.body = [
				structuredLoop.loop,
				...structuredLoop.exitStatements,
				...(terminalContinuation?.exitBody ?? []),
			];
			headerBlock.consequentAddresses = [];
			return;
		}
		headerBlock.body = fallbackWhileTrue(
			loopBody,
			terminalContinuation?.exitBody,
		);
		headerBlock.consequentAddresses = [];
		return;
	}

	if (plan.kind === 'conditionalSelfLoop') {
		const { loopExit, breakTest } = plan;
		// [0]=fall-through, [1]=jump-target. rightIsSelf → right=[1]=jump-target=self means
		// the jump is taken (condition TRUE) → loop continues → break when condition FALSE.
		// leftIsSelf  → left=[0]=fall-through=self means fall-through (condition FALSE) →
		// loop continues → break when condition TRUE.
		const whileBody = [
			...<t.Statement[]> headerBlock.body,
			t.ifStatement(
				breakTest,
				t.blockStatement([t.breakStatement()]),
			),
		];
		const structuredLoop = tryBuildForInOrOfStatement(
			func,
			header,
			body,
			whileBody,
			loopExit,
		);
		if (structuredLoop) {
			headerBlock.body = [
				structuredLoop.loop,
				...structuredLoop.exitStatements,
			];
			headerBlock.branch = undefined;
			headerBlock.consequentAddresses = [loopExit];

			removeForInEmptyListGuard(
				func,
				header,
				new AddressSet([loopExit]),
				structuredLoop.PNameArray,
			);
			return;
		}
		headerBlock.body = fallbackWhileTrue(whileBody);
		headerBlock.branch = undefined;
		headerBlock.consequentAddresses = [loopExit];
		return;
	}

	const { backEdgeIsRight, exitAddr } = plan;
	// Latch temporaries are evaluated once before the backedge. Keep direct
	// condition aliases and loop-carried producer chains named: inlining them
	// into the synthesized guard can duplicate getters, calls, or increments.
	const loopCarriedLatchNames = new Set<string>();
	for (
		const instruction
			of func.ssa.basicBlocks.get(header)?.ssaInstructions ??
				[]
	) {
		if (instruction.instruction !== 'Phi') continue;
		const source = instruction.sources.get(latch);
		if (source) loopCarriedLatchNames.add(registerName(source));
	}
	const latchInitializers = new Map<string, t.Expression>();
	for (const node of latchBlock.body) {
		const statement = node as t.Statement;
		if (
			!t.isVariableDeclaration(statement, { kind: 'const' }) ||
			statement.declarations.length !== 1
		) continue;
		const [declaration] = statement.declarations;
		if (
			t.isIdentifier(declaration.id) && declaration.init &&
			t.isExpression(declaration.init)
		) {
			latchInitializers.set(declaration.id.name, declaration.init);
		}
	}
	if (latchBlock.branch) {
		t.traverseFast(latchBlock.branch as t.Expression, (node) => {
			if (
				t.isIdentifier(node) && latchInitializers.has(node.name)
			) loopCarriedLatchNames.add(node.name);
		});
	}
	const pendingLatchNames = [...loopCarriedLatchNames];
	for (let index = 0; index < pendingLatchNames.length; index++) {
		const initializer = latchInitializers.get(pendingLatchNames[index]!);
		if (!initializer) continue;
		t.traverseFast(initializer, (node) => {
			if (
				!t.isIdentifier(node) || !/^r\d+_\d+$/.test(node.name) ||
				loopCarriedLatchNames.has(node.name)
			) return;
			loopCarriedLatchNames.add(node.name);
			pendingLatchNames.push(node.name);
		});
	}
	for (let changed = true; changed;) {
		changed = false;
		for (const [name, initializer] of latchInitializers) {
			if (loopCarriedLatchNames.has(name)) continue;
			let referencesLoopCarriedValue = false;
			t.traverseFast(initializer, (node) => {
				if (
					t.isIdentifier(node) &&
					loopCarriedLatchNames.has(node.name)
				) referencesLoopCarriedValue = true;
			});
			if (!referencesLoopCarriedValue) continue;
			loopCarriedLatchNames.add(name);
			changed = true;
		}
	}
	const latchConditionInfo = () => {
		const resolvedLatchBranch = latchBlock.branch
			? resolveLatchCondition(
				latchBlock,
				<t.Expression> latchBlock.branch,
				loopCarriedLatchNames,
			)
			: undefined;
		const containsPhi = resolvedLatchBranch
			? expressionContainsIntrinsic(resolvedLatchBranch, 'Phi')
			: false;
		const continueCondExpr = resolvedLatchBranch
			? (containsPhi && latchBlock.branch
				? <t.Expression> t.cloneNode(
					<t.Expression> latchBlock.branch,
					true,
				)
				: resolvedLatchBranch)
			: t.booleanLiteral(true);
		return { continueCondExpr, containsPhi };
	};
	let { continueCondExpr, containsPhi: resolvedLatchBranchContainsPhi } =
		latchConditionInfo();

	const runSubReducers = () => {
		let inner;
		do {
			inner = false;
			const headerBlock = func.blocks.get(header);
			if (
				headerBlock && !headerBlock.branch &&
				headerBlock.consequentAddresses.length === 0
			) break;
			inner = reduceSequence(func) || inner;
			if (reduceSharedLoopGuardChain(func, body, latch)) {
				inner = true;
				continue;
			}
			inner = reduceSharedSequenceEdge(func) || inner;
			inner = reduceInlineTerminal(func, {
				excludeAddresses: new Set([header]),
			}) || inner;
			inner = reduceSwitch(func) || inner;
			inner = reduceSimpleIf(func) || inner;
			inner = reduceTryCatch(func) || inner;
		} while (inner);
	};

	if (plan.kind === 'terminalExits') {
		const SYNTHETIC = -1 as BlockAddr;
		const DUMMY = -2 as BlockAddr;
		const PREHEADER_DUMMY = -3 as BlockAddr;
		const { terminalExits } = plan;
		if (func.id === 0) {
			for (const exit of terminalExits) {
				const exitBlock = func.blocks.get(exit);
				if (exitBlock && isScriptCompletionReturn(exitBlock)) {
					exitBlock.body = [t.breakStatement()];
				}
			}
		}

		// Add a dummy block that points at every terminal exit.  This keeps
		// predecessorsOf(exit) > 1 so reduceSequence won't consume exits while
		// reduceInlineTerminal still clones them into the loop body.
		if (terminalExits.size > 0) {
			func.blocks.set(DUMMY, {
				address: DUMMY,
				body: [],
				branch: undefined,
				consequentAddresses: [...terminalExits],
			});
			func.mergedBlocks.set(DUMMY, new AddressSet());
		}
		func.blocks.set(PREHEADER_DUMMY, {
			address: PREHEADER_DUMMY,
			body: [],
			branch: t.booleanLiteral(true),
			consequentAddresses: [header, PREHEADER_DUMMY],
		});
		func.mergedBlocks.set(PREHEADER_DUMMY, new AddressSet());
		const externalHeaderPredecessors = [...func.predecessorsOf(header)]
			.filter((pred) => pred !== PREHEADER_DUMMY && !body.has(pred));
		for (const pred of externalHeaderPredecessors) {
			const predBlock = func.blocks.get(pred);
			if (!predBlock) continue;
			predBlock.consequentAddresses = <BlockAddr[]> predBlock
				.consequentAddresses.map((succ) =>
					succ === header ? PREHEADER_DUMMY : succ
				);
		}

		func.blocks.set(SYNTHETIC, {
			address: SYNTHETIC,
			body: [t.continueStatement()],
			branch: undefined,
			consequentAddresses: [],
		});
		func.mergedBlocks.set(SYNTHETIC, new AddressSet());
		if (lowerLoopLatchPhiCopies(func, header, latch, body)) {
			({ continueCondExpr, containsPhi: resolvedLatchBranchContainsPhi } =
				latchConditionInfo());
		}
		latchBlock.consequentAddresses = <BlockAddr[]> latchBlock
			.consequentAddresses.map(
				(a) => a === header ? SYNTHETIC : a,
			);

		runSubReducers();
		if (requireCollapsedBody) {
			assertNaturalLoopBodyCollapsed(func, header, body);
		}

		const headerBlock = func.blocks.get(header)!;
		restoreSyntheticPreheader(func, header, PREHEADER_DUMMY);
		// Fold constant-condition ifs, including const-register tests like
		// `const r = []; if (r)`, and strip dead code before wrapping.
		const structuredLoop = tryBuildForInOrOfStatement(
			func,
			header,
			body,
			<t.Statement[]> headerBlock.body,
			header,
		);
		if (structuredLoop) {
			headerBlock.body = [
				structuredLoop.loop,
				...structuredLoop.exitStatements,
			];
			removeForInEmptyListGuard(
				func,
				header,
				terminalExits,
				structuredLoop.PNameArray,
			);
		} else {
			headerBlock.body = fallbackWhileTrue(
				<t.Statement[]> headerBlock.body,
			);
		}
		headerBlock.branch = undefined;
		headerBlock.consequentAddresses = [];
		func.blocks.delete(SYNTHETIC);
		func.blocks.delete(DUMMY);
		func.blocks.delete(PREHEADER_DUMMY);
		func.mergedBlocks.delete(SYNTHETIC);
		func.mergedBlocks.delete(DUMMY);
		func.mergedBlocks.delete(PREHEADER_DUMMY);
	} else {
		const PREHEADER_DUMMY = -3 as BlockAddr;
		func.blocks.set(PREHEADER_DUMMY, {
			address: PREHEADER_DUMMY,
			body: [],
			branch: t.booleanLiteral(true),
			consequentAddresses: [header, PREHEADER_DUMMY],
		});
		func.mergedBlocks.set(PREHEADER_DUMMY, new AddressSet());

		// Redirect external preds of header through PREHEADER_DUMMY so they
		// can't be merged or simplified away during runSubReducers.
		const externalHeaderPredecessors = [...func.predecessorsOf(header)]
			.filter((pred) => pred !== PREHEADER_DUMMY && !body.has(pred));
		for (const pred of externalHeaderPredecessors) {
			const predBlock = func.blocks.get(pred);
			if (!predBlock) continue;
			predBlock.consequentAddresses = <BlockAddr[]> predBlock
				.consequentAddresses.map((succ) =>
					succ === header ? PREHEADER_DUMMY : succ
				);
		}

		// SYNTHETIC_FALLTHROUGH: empty terminal replacing latch's exit to exitAddr.
		// Prevents reduceInlineTerminal from cloning exitAddr's return into the loop body.
		const SYNTHETIC_FALLTHROUGH = -4 as BlockAddr;
		func.blocks.set(SYNTHETIC_FALLTHROUGH, {
			address: SYNTHETIC_FALLTHROUGH,
			body: [],
			branch: undefined,
			consequentAddresses: [],
		});
		func.mergedBlocks.set(SYNTHETIC_FALLTHROUGH, new AddressSet());

		// SYNTHETIC_BREAK: redirects other body→exitAddr edges so they produce `break`
		// rather than the function's return/throw statement.
		const SYNTHETIC_BREAK = -5 as BlockAddr;
		func.blocks.set(SYNTHETIC_BREAK, {
			address: SYNTHETIC_BREAK,
			body: [t.breakStatement()],
			branch: undefined,
			consequentAddresses: [],
			kind: 'synthetic',
			terminalKind: 'break',
			syntheticReason: 'natural-loop-break',
		});
		func.mergedBlocks.set(SYNTHETIC_BREAK, new AddressSet());

		for (const addr of body) {
			const block = func.blocks.get(addr);
			if (!block || addr === latch) continue;
			block.consequentAddresses = <BlockAddr[]> block.consequentAddresses
				.map(
					(succ) => succ === exitAddr ? SYNTHETIC_BREAK : succ,
				);
		}

		if (lowerLoopLatchPhiCopies(func, header, latch, body)) {
			({ continueCondExpr, containsPhi: resolvedLatchBranchContainsPhi } =
				latchConditionInfo());
		}
		if (latchBlock.branch && !resolvedLatchBranchContainsPhi) {
			removeLatchConditionDeclaration(
				latchBlock,
				<t.Expression> latchBlock.branch,
				loopCarriedLatchNames,
			);
		}
		latchBlock.consequentAddresses = [SYNTHETIC_FALLTHROUGH];
		latchBlock.branch = undefined;

		runSubReducers();
		if (requireCollapsedBody) {
			assertNaturalLoopBodyCollapsed(func, header, body);
		}

		restoreSyntheticPreheader(func, header, PREHEADER_DUMMY);

		const headerBlock = func.blocks.get(header)!;
		const whileBody = <t.Statement[]> headerBlock.body;
		const loopCondExpr = backEdgeIsRight
			? continueCondExpr
			: invertTest(continueCondExpr);
		if (!t.isBooleanLiteral(loopCondExpr, { value: true })) {
			whileBody.push(
				t.ifStatement(
					invertTest(loopCondExpr),
					t.blockStatement([t.breakStatement()]),
				),
			);
		}
		const whileTrue = t.whileStatement(
			t.booleanLiteral(true),
			t.blockStatement(whileBody),
		);
		whileTrue.extra = { ...whileTrue.extra, fromCFGLoop: true };
		headerBlock.body = [whileTrue];
		headerBlock.branch = undefined;
		headerBlock.consequentAddresses = [exitAddr];
		func.blocks.delete(SYNTHETIC_FALLTHROUGH);
		func.mergedBlocks.delete(SYNTHETIC_FALLTHROUGH);
		func.blocks.delete(SYNTHETIC_BREAK);
		func.mergedBlocks.delete(SYNTHETIC_BREAK);
		func.blocks.delete(PREHEADER_DUMMY);
		func.mergedBlocks.delete(PREHEADER_DUMMY);
	}
}

export function reduceNaturalLoop(
	func: IRFunction,
	beforeMutation?: () => void,
	options: { allowPartialBody?: boolean } = {},
): boolean {
	const idom = computeImmediateDominators(func);

	const backEdges: Array<[latch: BlockAddr, header: BlockAddr]> = [];
	for (const [src, block] of func.blocks) {
		for (const tgt of block.consequentAddresses) {
			if (!func.blocks.has(tgt)) continue;
			if (tgt === src) {
				backEdges.push([src, tgt]);
				continue;
			}
			let cur: BlockAddr | null = idom.get(src) ?? null;
			// A dominator chain cannot be longer than the block count. Walking
			// it unbounded assumes `idom` is acyclic, which does not hold for
			// every CFG this pass is handed: reached through the recursive
			// path, the graph has already been rewritten, and a cyclic chain
			// here spins forever on pointer-chasing -- 100% CPU, no
			// allocation, no completion. Three functions of the 127k-function
			// bundle hang exactly here.
			let steps = 0;
			while (cur !== null) {
				if (cur === tgt) {
					backEdges.push([src, tgt]);
					break;
				}
				if (++steps > func.blocks.size) {
					if (Deno.env.get('ARES_TRACE_FIXPOINT') != null) {
						Deno.stderr.writeSync(
							new TextEncoder().encode(
								`[idom] cyclic dominator chain from ` +
									`0x${
										src.toString(16)
									} (>${func.blocks.size}` +
									` steps); abandoning this edge\n`,
							),
						);
					}
					break;
				}
				cur = idom.get(cur) ?? null;
			}
		}
	}
	if (backEdges.length === 0) return false;
	const nlTrace = Deno.env.get('ARES_TRACE_FIXPOINT') != null;
	const nlSay = (m: string) => {
		if (nlTrace) {
			Deno.stderr.writeSync(new TextEncoder().encode(`[nl] ${m}\n`));
		}
	};
	nlSay(`backEdges=${backEdges.length}, sorting by loop-body size`);

	backEdges.sort(([s1, h1], [s2, h2]) =>
		computeLoopBody(func, h1, s1).size - computeLoopBody(func, h2, s2).size
	);
	nlSay('sorted; scanning back edges');

	for (const [latch, header] of backEdges) {
		nlSay(
			`edge latch=0x${latch.toString(16)} header=0x${
				header.toString(16)
			}`,
		);
		nlSay('  activeHandlersEqual');
		const handlersEqual = func.exceptions.activeHandlersEqual(
			header,
			latch,
		);
		nlSay(`  activeHandlersEqual -> ${handlersEqual}`);
		const iteratorCleanupHandlers = new AddressSet<BlockAddr>();
		if (!handlersEqual) {
			nlSay('  isHeaderTestedProtectedBodyLoop');
			const headerTested = isHeaderTestedProtectedBodyLoop(
				func,
				header,
				latch,
			);
			nlSay(`  isHeaderTestedProtectedBodyLoop -> ${headerTested}`);
			if (!headerTested) continue;
			for (
				const handler of func.exceptions.activeHandlersAtBlock(latch)
					.difference(
						func.exceptions.activeHandlersAtBlock(header),
					)
			) iteratorCleanupHandlers.add(handler);
		}
		nlSay('  planNaturalLoopMutation');
		const plan = planNaturalLoopMutation(func, header, latch);
		nlSay(`  planned body=${plan.body.size}`);
		const exitAddresses = new AddressSet<BlockAddr>();
		for (const address of plan.body) {
			const block = func.blocks.get(address);
			if (!block) continue;
			for (const successor of block.consequentAddresses) {
				if (successor !== header && !plan.body.has(successor)) {
					exitAddresses.add(successor);
				}
			}
		}
		for (const exitAddress of exitAddresses) {
			// Preserve the value selected by every normal/break edge before loop
			// mutation replaces those edges with synthetic terminals.
			if (
				reduceSharedLeadingPhi(func, {
					address: exitAddress,
					maxPhis: 8,
				})
			) return true;
		}
		beforeMutation?.();
		for (const handler of iteratorCleanupHandlers) {
			func.exceptions.removeStructuredCatchHandler(handler);
		}
		nlSay('  applyNaturalLoopMutationPlan');
		applyNaturalLoopMutationPlan(func, plan, !options.allowPartialBody);
		nlSay('  applied');
		return true;
	}
	return false;
}

// Detect chains of blocks that all jump to the same body block on their
// true branch while chaining through each other on the false branch:
//
//   A [left=B, right=Body]:  if condA → Body, else → B
//   B [left=C, right=Body]:  if condB → Body, else → C
//   C [left=Cont, right=Body]: if condC → Body, else → Cont
//
// This is short-circuit OR: `if (condA || condB || condC) { Body } else { Cont }`.
// Emits the combined if-statement on A and consumes B, C and Body.
