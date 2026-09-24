import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import { isUndefinedNode } from '../../ast/utils.ts';
import { preserveDuplicateRegisterScopesInBody } from '../../ast/registerScope.ts';
import { loadEnvironmentCall } from './envAccess.ts';
import {
	reduceIteratorDestructuringDefaults,
	reduceIteratorDestructuringSequence,
	reduceOrChain,
	reduceSequence,
	reduceSimpleIf,
	reduceSwitch,
	reduceTryCatch,
} from '../cfg/mod.ts';
import {
	reduceDelegateYieldCFG,
	reduceDelegateYieldStructuredBodies,
} from '../cfg/delegateYield.ts';
import type { IRFunction } from '../mod.ts';
import { caseBodies, yieldExpressionStatementValue } from './caseUtils.ts';
import { debug, debugDupSSA, duplicateSSADebugEnabled } from './debug.ts';
import {
	environmentCallSlot,
	isLoadFromEnvironmentCall,
	stripLoweredGeneratorEnvironmentScaffolding,
} from './environmentScaffolding.ts';
import {
	caseReadsCaughtException,
	loweredComparableAst,
	loweredStatementsEqual,
} from './finalizerAnalysis.ts';
import type { LoweredGeneratorModel, StateRoles } from './types.ts';

export function reduceRecoveredFunction(func: IRFunction) {
	const pruneDanglingSuccessors = () => {
		let changed = false;
		for (const block of func.blocks.values()) {
			const successors = block.consequentAddresses.filter((addr) =>
				func.blocks.has(addr)
			);
			if (successors.length === block.consequentAddresses.length) {
				continue;
			}
			block.consequentAddresses = successors;
			if (successors.length < 2) block.branch = undefined;
			changed = true;
		}
		return changed;
	};

	let changed: boolean;
	do {
		changed = false;
		changed = reduceSequence(func) || changed;
		const destructuringChanged =
			reduceIteratorDestructuringSequence(func) ||
			reduceIteratorDestructuringDefaults(func);
		if (destructuringChanged) {
			changed = true;
			continue;
		}
		changed = reduceSwitch(func) || changed;
		changed = reduceOrChain(func) || changed;
		changed = reduceSimpleIf(func) || changed;
		changed = reduceDelegateYieldCFG(func) || changed;
		changed = reduceDelegateYieldStructuredBodies(func) || changed;
		const tryCatchChanged = reduceTryCatch(func, {
			preferProtectedRegionOrder: func.file.version >= 97,
			mergeSplitTryFinallyBody: func.file.version >= 97,
		});
		changed = tryCatchChanged || changed;
		if (tryCatchChanged) {
			changed = reduceDelegateYieldCFG(func) || changed;
			changed = reduceDelegateYieldStructuredBodies(func) || changed;
		}
		changed = pruneDanglingSuccessors() || changed;
		changed = func.pruneOrphanedBlocks() || changed;
		if (!changed) {
			changed = func.tryReduceCompleteNaturalLoop();
		}
	} while (changed);

	const reachable = new Set<BlockAddr>([0]);
	const stack: BlockAddr[] = [0];
	while (stack.length > 0) {
		const addr = stack.pop()!;
		const block = func.blocks.get(addr);
		if (!block) continue;
		for (const succ of block.consequentAddresses) {
			if (!func.blocks.has(succ) || reachable.has(succ)) continue;
			reachable.add(succ);
			stack.push(succ);
		}
	}
	for (const addr of [...func.blocks.keys()]) {
		if (!reachable.has(addr)) func.blocks.delete(addr);
	}
	pruneDanglingSuccessors();
}

export function statementContainsDelegateYield(stmt: t.Statement) {
	let found = false;
	const wrapped = t.file(t.program([t.cloneNode(stmt, true)]));
	traverse(wrapped, {
		CallExpression(path: NodePath<t.CallExpression>) {
			if (
				t.isV8IntrinsicIdentifier(path.node.callee, {
					name: 'DelegateYield',
				})
			) {
				found = true;
				path.stop();
			}
		},
	});
	return found;
}

function replaceCaughtExceptionLoads(
	body: t.Statement[],
	roles: StateRoles,
	catchParam: t.Identifier,
) {
	if (roles.caughtExceptionSlot == null) return body;
	const wrapped = t.file(t.program(body));
	traverse(wrapped, {
		MemberExpression(path: NodePath<t.MemberExpression>) {
			if (!isLoadFromEnvironmentCall(path.node)) return;
			const slot = environmentCallSlot(path.node);
			if (slot !== roles.caughtExceptionSlot) return;
			path.replaceWith(t.cloneNode(catchParam));
		},
	});
	return wrapped.program.body;
}

function stripMatchingStatement(
	body: t.Statement[],
	match: t.Statement,
	roles: StateRoles,
) {
	const index = body.findIndex((stmt) =>
		loweredStatementsEqual(stmt, match, roles)
	);
	if (index < 0) return false;
	if (!removedStatementBindingsAreDead(body, index, 1)) return false;
	body.splice(index, 1);
	return true;
}

function declaredNamesInStatements(statements: t.Statement[]) {
	const names = new Set<string>();
	for (const stmt of statements) {
		for (const name of Object.keys(t.getBindingIdentifiers(stmt))) {
			names.add(name);
		}
	}
	return names;
}

function statementsReferenceAny(statements: t.Statement[], names: Set<string>) {
	if (names.size === 0 || statements.length === 0) return false;
	let found = false;
	const wrapped = t.file(
		t.program(statements.map((stmt) => t.cloneNode(stmt, true))),
	);
	traverse(wrapped, {
		Identifier(path: NodePath<t.Identifier>) {
			if (!names.has(path.node.name)) return;
			if (!path.isReferencedIdentifier()) return;
			found = true;
			path.stop();
		},
	});
	return found;
}

function removedStatementBindingsAreDead(
	body: t.Statement[],
	start: number,
	count: number,
) {
	const removed = body.slice(start, start + count);
	const names = declaredNamesInStatements(removed);
	if (names.size === 0) return true;
	const remaining = [
		...body.slice(0, start),
		...body.slice(start + count),
	];
	return !statementsReferenceAny(remaining, names);
}

function loweredExpressionsEqual(
	left: t.Expression,
	right: t.Expression,
	roles: StateRoles,
) {
	return JSON.stringify(loweredComparableAst(left, roles)) ===
		JSON.stringify(loweredComparableAst(right, roles));
}

function globalCallStatement(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return;
	const expr = stmt.expression;
	if (!t.isCallExpression(expr)) return;
	if (!t.isIdentifier(expr.callee)) return;
	const args = expr.arguments;
	if (!args.every((arg): arg is t.Expression => t.isExpression(arg))) {
		return;
	}
	return { name: expr.callee.name, args };
}

function loweredGlobalGetterStatement(stmt: t.Statement) {
	if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
		return;
	}
	const decl = stmt.declarations[0];
	if (
		!t.isVariableDeclarator(decl) ||
		!t.isIdentifier(decl.id) ||
		!t.isCallExpression(decl.init) ||
		!t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'TryGetById' })
	) return;
	const [object, property] = decl.init.arguments;
	if (
		!t.isIdentifier(object, { name: 'global' }) ||
		!t.isStringLiteral(property)
	) return;
	return { binding: decl.id.name, name: property.value };
}

function loweredGlobalCallCopyStatement(
	stmt: t.Statement,
	binding: string,
	args: t.Expression[],
	roles: StateRoles,
) {
	let call: t.CallExpression | null = null;
	if (t.isExpressionStatement(stmt) && t.isCallExpression(stmt.expression)) {
		call = stmt.expression;
	} else if (
		t.isVariableDeclaration(stmt) && stmt.declarations.length === 1
	) {
		const decl = stmt.declarations[0];
		if (t.isVariableDeclarator(decl) && t.isCallExpression(decl.init)) {
			call = decl.init;
		}
	}
	if (!call) return false;
	if (
		!t.isMemberExpression(call.callee) ||
		!t.isIdentifier(call.callee.object, { name: binding }) ||
		!t.isIdentifier(call.callee.property, { name: 'call' }) ||
		call.callee.computed
	) return false;
	if (call.arguments.length !== args.length + 1) return false;
	if (!isUndefinedNode(call.arguments[0])) return false;
	for (let i = 0; i < args.length; i++) {
		const arg = call.arguments[i + 1];
		if (!t.isExpression(arg)) return false;
		if (!loweredExpressionsEqual(arg, args[i], roles)) return false;
	}
	return true;
}

function stripLoweredGlobalCallCopy(
	body: t.Statement[],
	match: t.Statement,
	roles: StateRoles,
) {
	const target = globalCallStatement(match);
	if (!target) return false;
	for (let i = 0; i < body.length - 1; i++) {
		const getter = loweredGlobalGetterStatement(body[i]);
		if (!getter || getter.name !== target.name) continue;
		if (
			!loweredGlobalCallCopyStatement(
				body[i + 1],
				getter.binding,
				target.args,
				roles,
			)
		) continue;
		if (!removedStatementBindingsAreDead(body, i, 2)) continue;
		body.splice(i, 2);
		return true;
	}
	return false;
}

function delegateYieldProtectedState(model: LoweredGeneratorModel) {
	for (const state of model.order) {
		const info = model.cases.get(state);
		if (
			!info ||
			!caseBodies(info).some((body) =>
				body.some(statementContainsDelegateYield)
			)
		) continue;
		if (info.activeHandlerIndex == null) continue;
		const catchState = model.roles.handlerIndexToState.get(
			info.activeHandlerIndex,
		);
		if (catchState != null && model.cases.has(catchState)) {
			return { state, catchState };
		}
	}

	const entry = model.cases.get(0);
	if (entry?.activeHandlerIndex == null) return;
	const catchState = model.roles.handlerIndexToState.get(
		entry.activeHandlerIndex,
	);
	if (catchState != null && model.cases.has(catchState)) {
		return { state: entry.state, catchState };
	}
}

export function recoverSubgraphDelegateTryCatch(
	func: IRFunction,
	model: LoweredGeneratorModel,
) {
	if (func.blocks.size !== 1 || !func.blocks.has(0)) {
		debug('delegate try/catch recovery skipped: non-single block');
		return false;
	}
	const entry = func.blocks.get(0)!;
	const body = entry.body as t.Statement[];
	const delegateIndex = body.findIndex(statementContainsDelegateYield);
	if (delegateIndex < 0) {
		debug('delegate try/catch recovery skipped: no delegate');
		return false;
	}
	const protectedState = delegateYieldProtectedState(model);
	if (!protectedState) {
		debug('delegate try/catch recovery skipped: no protected state');
		return false;
	}
	const catchInfo = model.cases.get(protectedState.catchState);
	if (!catchInfo || !caseReadsCaughtException(catchInfo, model.roles)) {
		debug(
			'delegate try/catch recovery skipped: no catch info',
			protectedState,
		);
		return false;
	}
	if (
		body.slice(0, delegateIndex).some((stmt) =>
			!t.isVariableDeclaration(stmt)
		)
	) {
		debug('delegate try/catch recovery skipped: non-decl prelude');
		return false;
	}
	const catchParam = t.identifier(`e_${func.id}_delegate`);
	let catchBody = catchInfo.body.map((stmt) => t.cloneNode(stmt, true));
	catchBody = replaceCaughtExceptionLoads(
		catchBody,
		model.roles,
		catchParam,
	);
	catchBody = stripLoweredGeneratorEnvironmentScaffolding(
		catchBody,
		model.roles,
	);
	let finalizerIndex = -1;
	let strippedCatchBody: t.Statement[] | null = null;
	for (let i = delegateIndex + 1; i < body.length; i++) {
		const candidateCatchBody = catchBody.map((stmt) =>
			t.cloneNode(stmt, true)
		);
		if (
			!stripMatchingStatement(candidateCatchBody, body[i], model.roles)
		) {
			stripLoweredGlobalCallCopy(
				candidateCatchBody,
				body[i],
				model.roles,
			);
		}
		if (candidateCatchBody.length === catchBody.length) continue;
		finalizerIndex = i;
		strippedCatchBody = candidateCatchBody;
		break;
	}
	if (finalizerIndex < 0 || !strippedCatchBody) {
		debug('delegate try/catch recovery skipped: no finalizer match');
		return false;
	}
	const finalizerStmt = body[finalizerIndex];
	catchBody = strippedCatchBody;
	if (catchBody.length === 0) {
		debug('delegate try/catch recovery skipped: empty catch body');
		return false;
	}

	const delegateStmt = body[delegateIndex];
	const tryBody: t.Statement[] = [];
	const prelude: t.Statement[] = [];
	if (t.isVariableDeclaration(delegateStmt)) {
		const decl = delegateStmt.declarations[0];
		if (
			!t.isVariableDeclarator(decl) ||
			!t.isIdentifier(decl.id) ||
			!t.isExpression(decl.init)
		) {
			debug('delegate try/catch recovery skipped: invalid delegate decl');
			return false;
		}
		prelude.push(t.variableDeclaration('let', [
			t.variableDeclarator(t.cloneNode(decl.id)),
		]));
		tryBody.push(t.expressionStatement(t.assignmentExpression(
			'=',
			t.cloneNode(decl.id),
			t.cloneNode(decl.init, true),
		)));
	} else {
		tryBody.push(t.cloneNode(delegateStmt, true));
	}
	tryBody.push(
		...body.slice(delegateIndex + 1, finalizerIndex).map((stmt) =>
			t.cloneNode(stmt, true)
		),
	);

	body.splice(
		delegateIndex,
		finalizerIndex - delegateIndex + 1,
		...prelude,
		t.tryStatement(
			t.blockStatement(tryBody),
			t.catchClause(catchParam, t.blockStatement(catchBody)),
			t.blockStatement([t.cloneNode(finalizerStmt, true)]),
		),
	);
	return true;
}

export function replaceRecoveredParameterLoads(func: IRFunction) {
	for (const block of func.blocks.values()) {
		const body = <t.Statement[]> block.body;
		for (let i = 0; i < body.length; i++) {
			const wrapped = t.file(t.program([body[i]]));
			traverse(wrapped, {
				MemberExpression: {
					exit(path: NodePath<t.MemberExpression>) {
						const load = loadEnvironmentCall(path.node);
						if (!load || load.slot >= func.params.length) return;
						const param = func.params[load.slot];
						if (!t.isExpression(param)) return;
						path.replaceWith(t.cloneNode(param, true));
					},
				},
			});
			body[i] = wrapped.program.body[0];
		}
	}
}

function normalizeRecoveredDuplicateRegisterDeclarationsInBody(
	body: t.Statement[],
	context = 'body',
): boolean {
	const declarations = new Map<string, t.VariableDeclaration>();
	let changed = false;

	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = normalizeRecoveredDuplicateRegisterDeclarationsInBody(
					stmt.consequent.body,
					`${context}.if.consequent`,
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = normalizeRecoveredDuplicateRegisterDeclarationsInBody(
					stmt.alternate.body,
					`${context}.if.alternate`,
				) || changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = normalizeRecoveredDuplicateRegisterDeclarationsInBody(
				stmt.body.body,
				`${context}.${stmt.type}.body`,
			) || changed;
		} else if (t.isTryStatement(stmt)) {
			changed = normalizeRecoveredDuplicateRegisterDeclarationsInBody(
				stmt.block.body,
				`${context}.try`,
			) || changed;
			if (stmt.handler) {
				changed = normalizeRecoveredDuplicateRegisterDeclarationsInBody(
					stmt.handler.body.body,
					`${context}.catch`,
				) || changed;
			}
			if (stmt.finalizer) {
				changed = normalizeRecoveredDuplicateRegisterDeclarationsInBody(
					stmt.finalizer.body,
					`${context}.finally`,
				) || changed;
			}
		}

		if (
			!t.isVariableDeclaration(stmt) ||
			stmt.declarations.length !== 1
		) continue;
		const decl = stmt.declarations[0];
		if (
			!t.isVariableDeclarator(decl) ||
			!t.isIdentifier(decl.id) ||
			!/^r\d+_\d+$/.test(decl.id.name)
		) continue;

		const previous = declarations.get(decl.id.name);
		if (!previous) {
			declarations.set(decl.id.name, stmt);
			continue;
		}

		debugDupSSA('rewrite recovered duplicate register', {
			context,
			name: decl.id.name,
			index: i,
			previousKind: previous.kind,
			currentKind: stmt.kind,
			previousInit: previous.declarations[0]?.init?.type ?? null,
			currentInit: decl.init?.type ?? null,
		});
		if (previous.kind === 'const') previous.kind = 'let';
		if (decl.init && t.isExpression(decl.init)) {
			body[i] = t.expressionStatement(t.assignmentExpression(
				'=',
				t.cloneNode(decl.id),
				t.cloneNode(decl.init, true),
			));
		} else {
			body.splice(i, 1);
			i--;
		}
		changed = true;
	}

	return changed;
}

export function normalizeRecoveredDuplicateRegisterDeclarations(
	func: IRFunction,
	stage = 'unknown',
): boolean {
	traceRecoveredDuplicateRegisterDeclarations(func, `${stage}:before`);
	let changed = false;
	for (const [addr, block] of func.blocks) {
		changed = normalizeRecoveredDuplicateRegisterDeclarationsInBody(
			<t.Statement[]> block.body,
			`func:${func.id}.block:${addr}.stage:${stage}`,
		) || changed;
	}
	if (changed) {
		traceRecoveredDuplicateRegisterDeclarations(func, `${stage}:after`);
	}
	return changed;
}

function traceDuplicateRegisterDeclarationsInBody(
	body: t.Statement[],
	context: string,
) {
	if (!duplicateSSADebugEnabled()) return;
	const declarations = new Map<
		string,
		{ index: number; kind: string; init: string | null }
	>();
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				traceDuplicateRegisterDeclarationsInBody(
					stmt.consequent.body,
					`${context}.if.consequent`,
				);
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				traceDuplicateRegisterDeclarationsInBody(
					stmt.alternate.body,
					`${context}.if.alternate`,
				);
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			traceDuplicateRegisterDeclarationsInBody(
				stmt.body.body,
				`${context}.${stmt.type}.body`,
			);
		} else if (t.isTryStatement(stmt)) {
			traceDuplicateRegisterDeclarationsInBody(
				stmt.block.body,
				`${context}.try`,
			);
			if (stmt.handler) {
				traceDuplicateRegisterDeclarationsInBody(
					stmt.handler.body.body,
					`${context}.catch`,
				);
			}
			if (stmt.finalizer) {
				traceDuplicateRegisterDeclarationsInBody(
					stmt.finalizer.body,
					`${context}.finally`,
				);
			}
		}
		if (
			!t.isVariableDeclaration(stmt) ||
			stmt.declarations.length !== 1
		) continue;
		const decl = stmt.declarations[0];
		if (
			!t.isVariableDeclarator(decl) ||
			!t.isIdentifier(decl.id) ||
			!/^r\d+_\d+$/.test(decl.id.name)
		) continue;
		const current = {
			index: i,
			kind: stmt.kind,
			init: decl.init?.type ?? null,
		};
		const previous = declarations.get(decl.id.name);
		if (!previous) {
			declarations.set(decl.id.name, current);
			continue;
		}
		debugDupSSA('found recovered duplicate register', {
			context,
			name: decl.id.name,
			previous,
			current,
		});
	}
}

export function traceRecoveredDuplicateRegisterDeclarations(
	func: IRFunction,
	stage: string,
) {
	if (!duplicateSSADebugEnabled()) return;
	for (const [addr, block] of func.blocks) {
		traceDuplicateRegisterDeclarationsInBody(
			<t.Statement[]> block.body,
			`func:${func.id}.block:${addr}.stage:${stage}.kind:${
				block.kind ?? 'unknown'
			}.state:${block.generatorState ?? 'none'}`,
		);
	}
}

export function preserveRecoveredDuplicateRegisterScopes(
	func: IRFunction,
): boolean {
	let changed = false;
	for (const block of func.blocks.values()) {
		changed = preserveDuplicateRegisterScopesInBody(
			<t.Statement[]> block.body,
			{
				context: `func:${func.id}.block:${block.address}.recovered`,
				onPreserve(event) {
					debugDupSSA(
						'preserve recovered duplicate register scope',
						event,
					);
				},
			},
		) || changed;
	}
	if (changed) {
		traceRecoveredDuplicateRegisterDeclarations(
			func,
			'after-preserve-duplicate-scopes',
		);
	}
	return changed;
}

export function statementDebugType(stmt: t.Statement) {
	if (t.isVariableDeclaration(stmt)) {
		const decl = stmt.declarations[0];
		if (t.isVariableDeclarator(decl) && t.isIdentifier(decl.id)) {
			return `VariableDeclaration:${decl.id.name}:${
				decl.init?.type ?? 'none'
			}`;
		}
		return stmt.type;
	}
	if (t.isExpressionStatement(stmt)) {
		const expr = stmt.expression;
		if (t.isYieldExpression(expr)) return 'YieldExpressionStatement';
		if (
			t.isCallExpression(expr) && t.isV8IntrinsicIdentifier(expr.callee)
		) {
			return `IntrinsicExpressionStatement:${expr.callee.name}`;
		}
		return `ExpressionStatement:${expr.type}`;
	}
	return stmt.type;
}
