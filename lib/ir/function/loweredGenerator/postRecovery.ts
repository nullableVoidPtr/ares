import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import { statementListEndsAbruptly } from '../../ast/completion.ts';
import { rewriteStructuredStatementLists } from '../../ast/statementLists.ts';
import { stripStatementSuffix } from '../finalizer.ts';
import { reduceSequence, reduceTryCatch } from '../cfg/mod.ts';
import {
	reduceDelegateYieldCFG,
	reduceDelegateYieldStructuredBodies,
} from '../cfg/delegateYield.ts';
import { cleanupLocalIteratorForOfLoops } from '../cfg/iterator.ts';
import type { IRFunction } from '../mod.ts';
import {
	hoistRecoveredTrySharedRegisterDeclarations,
	lowerRecoveredEnvironmentCellsToLocals,
	repairDanglingRecoveredYieldOperands,
} from './cleanup.ts';
import {
	hasRecoveredIteratorEnvironmentDestructuring,
	normalizeRecoveredIteratorEnvironmentDestructuring,
} from './iteratorRecovery.ts';
import { debug } from './debug.ts';
import { loadEnvironmentCall } from './envAccess.ts';
import { caseBodies, yieldExpressionStatementValue } from './caseUtils.ts';
import { discoverParentEnvironmentNames } from './environmentAnalysis.ts';
import { stripLoweredGeneratorEnvironmentScaffolding } from './environmentScaffolding.ts';
import {
	analyseProtectedStates,
	caseReadsCaughtException,
} from './finalizerAnalysis.ts';
import {
	normalizeRecoveredDuplicateRegisterDeclarations,
	preserveRecoveredDuplicateRegisterScopes,
	recoverSubgraphDelegateTryCatch,
	reduceRecoveredFunction,
	replaceRecoveredParameterLoads,
	statementContainsDelegateYield,
	statementDebugType,
	traceRecoveredDuplicateRegisterDeclarations,
} from './recoveredCleanup.ts';
import type { CaseInfo, LoweredGeneratorModel } from './types.ts';

function isRecoveredGeneratorEnvironmentAccess(
	expression: t.Expression | null | undefined,
) {
	return t.isCallExpression(expression) &&
		t.isV8IntrinsicIdentifier(expression.callee, {
			name: 'GetParentEnvironment',
		});
}

function pruneDeadRecoveredEnvironmentSSA(func: IRFunction) {
	let changed = false;
	for (const block of func.blocks.values()) {
		const wrapped = t.file(t.program(block.body as t.Statement[]));
		const candidates = new Set<string>();
		traverse(wrapped, {
			Identifier(path: NodePath<t.Identifier>) {
				if (
					path.node.extra?.recoveredEnvironmentSSA ||
					path.node.extra?.loweredGeneratorResumeValue ||
					path.node.extra?.recoveredEnvironmentLocal
				) {
					candidates.add(path.node.name);
				}
			},
			AssignmentExpression(path: NodePath<t.AssignmentExpression>) {
				if (
					path.node.operator === '=' &&
					t.isIdentifier(path.node.left) &&
					isRecoveredGeneratorEnvironmentAccess(path.node.right)
				) candidates.add(path.node.left.name);
			},
			VariableDeclarator(path: NodePath<t.VariableDeclarator>) {
				if (
					t.isIdentifier(path.node.id) &&
					isRecoveredGeneratorEnvironmentAccess(
						t.isExpression(path.node.init) ? path.node.init : null,
					)
				) candidates.add(path.node.id.name);
			},
		});
		if (candidates.size === 0) continue;
		const referenced = new Set<string>();
		traverse(wrapped, {
			Identifier(path: NodePath<t.Identifier>) {
				if (
					candidates.has(path.node.name) &&
					path.isReferencedIdentifier()
				) referenced.add(path.node.name);
			},
		});
		const dead = candidates.difference(referenced);
		if (dead.size === 0) continue;
		traverse(wrapped, {
			AssignmentExpression: {
				exit(path: NodePath<t.AssignmentExpression>) {
					if (
						path.node.operator !== '=' ||
						!t.isIdentifier(path.node.left) ||
						!dead.has(path.node.left.name)
					) return;
					const right = path.get('right');
					const rightIsPure = right.isPure() ||
						t.isIdentifier(right.node, { name: 'undefined' }) ||
						isRecoveredGeneratorEnvironmentAccess(right.node);
					if (path.parentPath.isExpressionStatement()) {
						if (rightIsPure) path.parentPath.remove();
						else {path.parentPath.replaceWith(
								t.expressionStatement(path.node.right),
							);}
					} else {
						path.replaceWith(path.node.right);
					}
					changed = true;
				},
			},
			VariableDeclarator: {
				exit(path: NodePath<t.VariableDeclarator>) {
					if (!t.isIdentifier(path.node.id)) return;
					if (!dead.has(path.node.id.name)) return;
					const initIsPure = path.node.init == null ||
						path.get('init').isPure() ||
						t.isIdentifier(path.node.init, { name: 'undefined' }) ||
						isRecoveredGeneratorEnvironmentAccess(path.node.init);
					if (
						!initIsPure &&
						path.parent.declarations.length > 1
					) return;
					if (!initIsPure && path.node.init) {
						path.parentPath.replaceWith(
							t.expressionStatement(path.node.init),
						);
					} else {
						path.remove();
					}
					changed = true;
				},
			},
		});
		block.body = wrapped.program.body;
	}
	return changed;
}

export function finishRecoveredGenerator(
	func: IRFunction,
	model: LoweredGeneratorModel,
) {
	debug('recovered generator blocks before reduction', {
		blocks: [...func.blocks].map(([addr, block]) => ({
			addr,
			succ: block.consequentAddresses,
			bodyTypes: (block.body as t.Statement[]).map(statementDebugType),
		})),
		handlers: [...func.exceptions.records].map(([handler, record]) => ({
			handler,
			protectedBlocks: [...record.protectedBlocks],
			directProtectedBlocks: [...(record.directProtectedBlocks ?? [])],
			catchBody: [...(record.catchBody ?? [])],
			canonicalFinallyAddress: record.canonicalFinallyAddress,
		})),
		finalizers: [...func.exceptions.finallyRecords].map(
			([handler, record]) => ({
				handler,
				bodyBlocks: record.bodyBlocks,
				copyRoots: [...record.copyRoots],
			}),
		),
	});
	reduceRecoveredFunction(func);
	hoistRecoveredTrySharedRegisterDeclarations(func);
	traceRecoveredDuplicateRegisterDeclarations(func, 'after-initial-reduce');
	preserveRecoveredDuplicateRegisterScopes(func);
	const usesSharedIteratorDestructuring =
		hasRecoveredIteratorEnvironmentDestructuring(model.cases);
	normalizeRecoveredIteratorEnvironmentDestructuring(func);
	func.cleanupLiftedBlocks();
	if (usesSharedIteratorDestructuring) {
		replaceRecoveredParameterLoads(func);
	}
	normalizeRecoveredDuplicateRegisterDeclarations(func, 'after-cleanup');
	debug(
		'recovered lowered generator blocks',
		[...func.blocks].map(([addr, block]) => ({
			addr,
			succ: block.consequentAddresses,
			bodyTypes: (block.body as t.Statement[]).map(statementDebugType),
		})),
	);
	for (const block of func.blocks.values()) {
		block.body = stripLoweredGeneratorEnvironmentScaffolding(
			<t.Statement[]> block.body,
			model.roles,
		);
	}
	normalizeRecoveredDuplicateRegisterDeclarations(
		func,
		'after-strip-scaffolding',
	);
	debug(
		'stripped lowered generator blocks',
		[...func.blocks].map(([addr, block]) => ({
			addr,
			succ: block.consequentAddresses,
			bodyTypes: (block.body as t.Statement[]).map(statementDebugType),
		})),
	);
	func.cleanupLiftedBlocks();
	reduceRecoveredFunction(func);
	let localIteratorPassChanged: boolean;
	do {
		localIteratorPassChanged = false;
		for (const block of func.blocks.values()) {
			localIteratorPassChanged =
				cleanupLocalIteratorForOfLoops(block.body as t.Statement[]) ||
				localIteratorPassChanged;
		}
		if (localIteratorPassChanged) {
			func.cleanupLiftedBlocks();
		}
	} while (localIteratorPassChanged);
	mergeRecoveredSuspendedFinalizerContinuations(func);
	if (recoverSuspendedFinalizerCatchClauses(func, model)) {
		func.cleanupLiftedBlocks();
		reduceRecoveredFunction(func);
	}
	normalizeRecoveredDuplicateRegisterDeclarations(
		func,
		'after-reduce-recovered',
	);
	const delegateYieldCFGChanged = reduceDelegateYieldCFG(func);
	const delegateYieldStructuredChanged = reduceDelegateYieldStructuredBodies(
		func,
	);
	const hasDelegateYield = [...func.blocks.values()].some((block) =>
		(block.body as t.Statement[]).some(statementContainsDelegateYield)
	);
	if (
		delegateYieldCFGChanged || delegateYieldStructuredChanged ||
		hasDelegateYield
	) {
		if (recoverSubgraphDelegateTryCatch(func, model)) {
			normalizeRecoveredDuplicateRegisterDeclarations(
				func,
				'after-recover-subgraph-delegate-try-catch',
			);
			func.cleanupLiftedBlocks();
		}
		reduceTryCatch(func, {
			preferProtectedRegionOrder: func.file.version >= 97,
			mergeSplitTryFinallyBody: func.file.version >= 97,
		});
		reduceSequence(func);
		normalizeRecoveredDuplicateRegisterDeclarations(
			func,
			'after-delegate-try-catch-reduce-sequence',
		);
	}
	repairRecoveredAsyncIteratorYieldOperands(func);
	repairDanglingRecoveredYieldOperands(func, model);
	lowerRecoveredEnvironmentCellsToLocals(func);
	normalizeRecoveredDuplicateRegisterDeclarations(func, 'final');
	hoistRecoveredTrySharedRegisterDeclarations(func);
	pruneDeadRecoveredEnvironmentSSA(func);
	if (func.blocks.size === 1 && func.blocks.has(0)) {
		func.cleanupLiftedBlocks({ removeUnusedStructuredBindings: true });
		do {
			localIteratorPassChanged = false;
			for (const block of func.blocks.values()) {
				localIteratorPassChanged = cleanupLocalIteratorForOfLoops(
					block.body as t.Statement[],
				) || localIteratorPassChanged;
			}
			if (localIteratorPassChanged) {
				func.cleanupLiftedBlocks({
					removeUnusedStructuredBindings: true,
				});
			}
		} while (localIteratorPassChanged);
	} else {
		debug(
			'unstructured lowered generator',
			func.blocks.size,
			[...func.blocks.keys()].slice(0, 40),
		);
	}
}

export function collectParentParameterAliases(
	func: IRFunction,
	cases: Map<number, CaseInfo>,
	preludeBody: t.Statement[],
) {
	const parentEnvironmentNames = discoverParentEnvironmentNames(cases);
	for (const statement of preludeBody) {
		if (!t.isVariableDeclaration(statement)) continue;
		for (const declaration of statement.declarations) {
			if (
				t.isIdentifier(declaration.id) &&
				t.isCallExpression(declaration.init) &&
				t.isV8IntrinsicIdentifier(declaration.init.callee, {
					name: 'GetParentEnvironment',
				})
			) parentEnvironmentNames.add(declaration.id.name);
		}
	}
	const aliases = new Map<string, t.Expression>();
	for (const info of cases.values()) {
		for (const body of caseBodies(info)) {
			for (const statement of body) {
				if (!t.isVariableDeclaration(statement)) continue;
				for (const declaration of statement.declarations) {
					if (
						!t.isIdentifier(declaration.id) ||
						!t.isExpression(declaration.init)
					) continue;
					const load = loadEnvironmentCall(declaration.init);
					if (
						!load || !t.isIdentifier(load.env) ||
						!parentEnvironmentNames.has(load.env.name) ||
						load.slot >= func.params.length
					) continue;
					const parameter = func.params[load.slot];
					if (!t.isExpression(parameter)) continue;
					aliases.set(
						declaration.id.name,
						t.memberExpression(
							t.callExpression(
								t.v8IntrinsicIdentifier('expectEnvironment'),
								[t.callExpression(
									t.v8IntrinsicIdentifier(
										'GetParentEnvironment',
									),
									[t.numericLiteral(0)],
								)],
							),
							t.numericLiteral(load.slot),
							true,
						),
					);
				}
			}
		}
	}
	return aliases;
}

function mergeRecoveredSuspendedFinalizerContinuations(func: IRFunction) {
	let changed = false;
	for (const block of func.blocks.values()) {
		changed = mergeSuspendedFinalizerContinuationsInBody(
			block.body as t.Statement[],
		) || changed;
	}
	return changed;
}

function mergeSuspendedFinalizerContinuationsInBody(
	body: t.Statement[],
): boolean {
	let changed = false;
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (t.isTryStatement(stmt)) {
			changed = mergeSuspendedFinalizerContinuationsInBody(
				stmt.block.body,
			) || changed;
			if (stmt.handler) {
				changed = mergeSuspendedFinalizerContinuationsInBody(
					stmt.handler.body.body,
				) || changed;
			}
			if (stmt.finalizer) {
				changed = mergeSuspendedFinalizerContinuationsInBody(
					stmt.finalizer.body,
				) || changed;
				changed = wrapSuspendedFinalizerTail(stmt.finalizer.body) ||
					changed;
			}
		}
		if (i >= body.length - 1) continue;
		if (!t.isTryStatement(stmt) || !stmt.finalizer) {
			continue;
		}
		if (
			stmt.finalizer.body.length === 0 ||
			statementListEndsAbruptly(stmt.finalizer.body)
		) continue;
		const next = body[i + 1];
		if (!t.isTryStatement(next)) continue;
		const continuation = t.cloneNode(next, true);
		stripSyntheticRecoveredRethrow(continuation);
		stmt.finalizer.body.push(continuation);
		body.splice(i + 1, 1);
		i--;
		changed = true;
	}
	return changed;
}

function wrapSuspendedFinalizerTail(body: t.Statement[]): boolean {
	if (body.length < 4) return false;
	const yieldIndex = body.findIndex((stmt) =>
		yieldExpressionStatementValue(stmt) != null
	);
	if (yieldIndex === -1 || yieldIndex >= body.length - 2) return false;
	if (t.isTryStatement(body[yieldIndex + 1])) return false;
	const tail = body.slice(yieldIndex + 1);
	const finalizer = tail.at(-1);
	if (!finalizer || t.isTryStatement(finalizer)) return false;
	const tryBody = tail.slice(0, -1);
	if (tryBody.length === 0) return false;
	body.splice(
		yieldIndex + 1,
		tail.length,
		t.tryStatement(
			t.blockStatement(tryBody),
			null,
			t.blockStatement([finalizer]),
		),
	);
	return true;
}

function stripSyntheticRecoveredRethrow(stmt: t.TryStatement) {
	if (stmt.finalizer?.body.length) {
		const last = stmt.finalizer.body.at(-1);
		if (t.isThrowStatement(last)) stmt.finalizer.body.pop();
	}
	if (stmt.handler) {
		const last = stmt.handler.body.body.at(-1);
		if (t.isThrowStatement(last)) stmt.handler.body.body.pop();
	}
}

function recoverSuspendedFinalizerCatchClauses(
	func: IRFunction,
	model: LoweredGeneratorModel,
) {
	const protectedStates = analyseProtectedStates(
		model.cases,
		model.roles,
		model.remap,
		model.finalizerCopies,
	);
	const candidates: Array<{
		protectedStrings: Set<string>;
		protectedStateCount: number;
		catchBody: t.Statement[];
		catchStrings: Set<string>;
		catchActionStrings: Set<string>;
		finalizerStrings?: Set<string>;
	}> = [];

	for (
		const [catchState, states] of protectedStates
			.protectedStatesByCatchState
	) {
		const catchInfo = model.cases.get(catchState);
		if (!catchInfo || !caseReadsCaughtException(catchInfo, model.roles)) {
			continue;
		}
		const protectedStrings = new Set<string>();
		for (const state of states) {
			const info = model.cases.get(state);
			if (!info) continue;
			for (const value of stringsInStatements(info.body)) {
				protectedStrings.add(value);
			}
		}
		if (protectedStrings.size === 0) continue;

		const catchBody = stripLoweredGeneratorEnvironmentScaffolding(
			catchInfo.body.map((stmt) => t.cloneNode(stmt, true)),
			model.roles,
		).filter((stmt) =>
			!isRecoveredCatchAliasStatement(stmt) &&
			!isRecoveredCatchScaffoldingStatement(stmt)
		);
		const catchStrings = stringsInStatements(catchBody);
		if (catchStrings.size === 0) continue;
		candidates.push({
			protectedStrings,
			protectedStateCount: states.size,
			catchBody,
			catchStrings,
			catchActionStrings: catchStrings,
		});
	}
	for (const info of model.cases.values()) {
		if (!caseReadsCaughtException(info, model.roles)) continue;
		const catchBody = stripLoweredGeneratorEnvironmentScaffolding(
			info.body.map((stmt) => t.cloneNode(stmt, true)),
			model.roles,
		).filter((stmt) =>
			!isRecoveredCatchAliasStatement(stmt) &&
			!isRecoveredCatchScaffoldingStatement(stmt)
		);
		const catchStrings = stringsInStatements(catchBody);
		const actionStrings = catchLikeStrings(catchStrings);
		const finalizerStrings = finalizerLikeStrings(catchStrings);
		if (actionStrings.size === 0 || finalizerStrings.size === 0) continue;
		candidates.push({
			protectedStrings: new Set(),
			protectedStateCount: 1,
			catchBody,
			catchStrings,
			catchActionStrings: actionStrings,
			finalizerStrings,
		});
	}

	if (candidates.length === 0) return false;

	let changed = false;
	for (const block of func.blocks.values()) {
		changed = recoverSuspendedFinalizerCatchClausesInBody(
			block.body as t.Statement[],
			candidates,
		) || changed;
	}
	return changed;
}

function recoverSuspendedFinalizerCatchClausesInBody(
	body: t.Statement[],
	candidates: Array<{
		protectedStrings: Set<string>;
		protectedStateCount: number;
		catchBody: t.Statement[];
		catchStrings: Set<string>;
		catchActionStrings: Set<string>;
		finalizerStrings?: Set<string>;
	}>,
): boolean {
	let changed = false;
	for (const stmt of body) {
		if (!t.isTryStatement(stmt)) continue;
		changed = recoverSuspendedFinalizerCatchClausesInBody(
			stmt.block.body,
			candidates,
		) || changed;
		if (stmt.handler) {
			changed = recoverSuspendedFinalizerCatchClausesInBody(
				stmt.handler.body.body,
				candidates,
			) || changed;
		}
		if (stmt.finalizer) {
			changed = recoverSuspendedFinalizerCatchClausesInBody(
				stmt.finalizer.body,
				candidates,
			) || changed;
		}
		if (stmt.handler || !stmt.finalizer) continue;

		const tryStrings = stringsInStatements(stmt.block.body);
		if (tryStrings.size === 0) continue;
		const existingStrings = stringsInStatements([
			stmt,
		] as t.Statement[]);
		const finalizerStrings = stringsInStatements(stmt.finalizer.body);
		const candidate = candidates
			.filter((candidate) =>
				(
					setIsSubset(tryStrings, candidate.protectedStrings) ||
					(
						candidate.finalizerStrings != null &&
						setIntersects(
							candidate.finalizerStrings,
							finalizerStrings,
						)
					)
				) &&
				!setIntersects(candidate.catchActionStrings, existingStrings)
			)
			.sort((left, right) =>
				(Number(right.finalizerStrings != null) -
					Number(left.finalizerStrings != null)) ||
				(left.protectedStrings.size - right.protectedStrings.size) ||
				(left.protectedStateCount - right.protectedStateCount) ||
				(left.catchActionStrings.size - right.catchActionStrings.size)
			)[0];
		if (!candidate) continue;

		let catchBody = candidate.catchBody.map((child) =>
			t.cloneNode(child, true)
		);
		if (candidate.finalizerStrings) {
			catchBody = trimBeforeStringIntersection(
				catchBody,
				finalizerStrings,
			);
			catchBody = trimThroughLastStringIntersection(
				catchBody,
				candidate.catchActionStrings,
			).filter((stmt) => !isRecoveredCatchScaffoldingStatement(stmt));
		}
		stripStatementSuffix(catchBody, stmt.finalizer.body, true);
		stmt.handler = t.catchClause(
			t.identifier(`e_recovered_${candidate.catchActionStrings.size}`),
			t.blockStatement(catchBody),
		);
		changed = true;
	}
	return changed;
}

function catchLikeStrings(strings: Set<string>) {
	const result = new Set<string>();
	for (const value of strings) {
		if (/(^|\.)(catch)$/.test(value)) result.add(value);
	}
	return result;
}

function finalizerLikeStrings(strings: Set<string>) {
	const result = new Set<string>();
	for (const value of strings) {
		if (/(^|\.)finally(\.|$)/.test(value)) result.add(value);
	}
	return result;
}

function trimBeforeStringIntersection(
	statements: t.Statement[],
	strings: Set<string>,
) {
	const index = statements.findIndex((stmt) =>
		setIntersects(stringsInStatements([stmt]), strings)
	);
	return index < 0 ? statements : statements.slice(0, index);
}

function trimThroughLastStringIntersection(
	statements: t.Statement[],
	strings: Set<string>,
) {
	let index = -1;
	for (let i = statements.length - 1; i >= 0; i--) {
		if (setIntersects(stringsInStatements([statements[i]]), strings)) {
			index = i;
			break;
		}
	}
	return index < 0 ? statements : statements.slice(0, index + 1);
}

function stringsInStatements(statements: t.Statement[]): Set<string> {
	const strings = new Set<string>();
	for (const statement of statements) {
		t.traverseFast(statement, (node) => {
			if (t.isStringLiteral(node)) strings.add(node.value);
		});
	}
	return strings;
}

function isRecoveredCatchAliasStatement(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return false;
	return t.isIdentifier(stmt.expression) &&
		/^e_\d+$/.test(stmt.expression.name);
}

function isRecoveredCatchScaffoldingStatement(stmt: t.Statement) {
	if (t.isExpressionStatement(stmt)) {
		return isRecoveredCatchScaffoldingExpression(stmt.expression);
	}
	if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
		return false;
	}
	const init = stmt.declarations[0].init;
	return !!init && isRecoveredCatchScaffoldingExpression(init);
}

function isRecoveredCatchScaffoldingExpression(expr: t.Expression) {
	if (t.isMemberExpression(expr)) {
		const object = expr.object;
		if (
			t.isCallExpression(object) &&
			t.isV8IntrinsicIdentifier(object.callee, {
				name: 'expectEnvironment',
			})
		) {
			return true;
		}
	}
	return false;
}

function setIsSubset<T>(left: Set<T>, right: Set<T>) {
	for (const value of left) {
		if (!right.has(value)) return false;
	}
	return true;
}

function setIntersects<T>(left: Set<T>, right: Set<T>) {
	for (const value of left) {
		if (right.has(value)) return true;
	}
	return false;
}

function repairRecoveredAsyncIteratorYieldOperands(func: IRFunction) {
	for (const block of func.blocks.values()) {
		repairRecoveredAsyncIteratorYieldOperandsInBody(
			block.body as t.Statement[],
		);
	}
}

function repairRecoveredAsyncIteratorYieldOperandsInBody(body: t.Statement[]) {
	rewriteStructuredStatementLists(
		body,
		repairRecoveredAsyncIteratorYieldOperandsInList,
	);
}

function repairRecoveredAsyncIteratorYieldOperandsInList(
	body: t.Statement[],
): boolean {
	let changed = false;
	for (let i = 0; i < body.length - 2; i++) {
		const nextName = asyncIteratorNextDeclarationName(body[i]);
		if (!nextName) continue;
		if (!isEnsureObjectForName(body[i + 1], nextName)) continue;
		const assignment = body[i + 2];
		if (!t.isExpressionStatement(assignment)) continue;
		const expr = assignment.expression;
		if (
			!t.isAssignmentExpression(expr, { operator: '=' }) ||
			!t.isYieldExpression(expr.right) ||
			!t.isIdentifier(expr.right.argument) ||
			t.isIdentifier(expr.right.argument, { name: nextName })
		) continue;
		expr.right.argument = t.identifier(nextName);
		changed = true;
	}
	return changed;
}

function asyncIteratorNextDeclarationName(stmt: t.Statement) {
	if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
		return;
	}
	const [decl] = stmt.declarations;
	if (
		!t.isVariableDeclarator(decl) ||
		!t.isIdentifier(decl.id) ||
		!t.isCallExpression(decl.init)
	) return;
	const callee = decl.init.callee;
	if (
		t.isMemberExpression(callee) &&
		!callee.computed &&
		t.isIdentifier(callee.property, { name: 'next' })
	) return decl.id.name;
}

function isEnsureObjectForName(stmt: t.Statement, name: string) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	return t.isCallExpression(expr) &&
		t.isMemberExpression(expr.callee) &&
		t.isIdentifier(expr.callee.object, { name: 'HermesInternal' }) &&
		t.isIdentifier(expr.callee.property, { name: 'ensureObject' }) &&
		t.isIdentifier(expr.arguments[0], { name });
}
