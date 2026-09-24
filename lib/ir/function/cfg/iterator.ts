import * as t from '@babel/types';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import type { IRFunction } from '../mod.ts';
import type { IRBlock } from '../../ast/mod.ts';
import { AddressSet } from '../../../utils/set.ts';
import { LiftedAST } from '../../ast/mod.ts';
import { consumedDefinitionsAreDead } from './consumed.ts';
import { liftPhiNodesInBody } from '../../ast/phi.ts';
import { statementListEndsAbruptly } from '../../ast/completion.ts';
import { rewriteStructuredStatementLists } from '../../ast/statementLists.ts';

let DEBUG_ITERATOR = false;
try {
	DEBUG_ITERATOR = Deno.env.get('ARES_DEBUG_ITERATOR') === '1';
} catch { /**/ }
function debugIterator(...args: unknown[]) {
	if (DEBUG_ITERATOR) console.error('[iterator]', ...args);
}

type StructuredIteratorLoop = {
	loop: t.ForInStatement | t.ForOfStatement;
	exitStatements: t.Statement[];
	PNameArray?: t.Identifier;
};

type MultiIntrinsicDecl = {
	destinations: t.Identifier[];
	call: t.CallExpression;
};

function getMultiIntrinsicDecl(
	stmt: t.Statement | undefined,
	name: string,
): MultiIntrinsicDecl | undefined {
	if (!stmt) return;
	let destinationPattern: t.ArrayPattern;
	let call: t.CallExpression;
	if (
		t.isVariableDeclaration(stmt) &&
		stmt.declarations.length === 1 &&
		t.isArrayPattern(stmt.declarations[0].id) &&
		t.isCallExpression(stmt.declarations[0].init)
	) {
		destinationPattern = stmt.declarations[0].id;
		call = stmt.declarations[0].init;
	} else if (
		t.isExpressionStatement(stmt) &&
		t.isAssignmentExpression(stmt.expression, { operator: '=' }) &&
		t.isArrayPattern(stmt.expression.left) &&
		t.isCallExpression(stmt.expression.right)
	) {
		destinationPattern = stmt.expression.left;
		call = stmt.expression.right;
	} else {
		return;
	}
	if (!t.isV8IntrinsicIdentifier(call.callee, { name })) return;
	const destinations = destinationPattern.elements;
	if (!destinations.every(t.isIdentifier)) return;
	return { destinations, call };
}

function registersEqual(
	left: t.Expression | t.PrivateName,
	right: t.Expression | t.PrivateName,
): boolean {
	if (!t.isIdentifier(left) || !t.isIdentifier(right)) return false;
	return left.name == right.name;
}

function isSameGeneratedRegister(
	node: t.Node | undefined | null,
	name: string,
): boolean {
	if (!t.isIdentifier(node)) return false;
	if (node.name === name) return true;
	const left = /^r(\d+)_\d+$/.exec(node.name);
	const right = /^r(\d+)_\d+$/.exec(name);
	return !!left && !!right && left[1] === right[1];
}

function isGeneratedRegisterName(name: string): boolean {
	return /^r\d+_\d+$/.test(name);
}

function isRecoveredEnvironmentSSAIdentifier(
	node: t.Node | null | undefined,
): node is LiftedAST<t.Identifier> {
	return t.isIdentifier(node) &&
		(node as LiftedAST<t.Identifier>).extra?.recoveredEnvironmentSSA ===
			true;
}

function isSyntheticPhiPlumbing(stmt: t.Statement): boolean {
	if (
		t.isVariableDeclaration(stmt) && stmt.declarations.length === 1
	) {
		const declaration = stmt.declarations[0];
		return isRecoveredEnvironmentSSAIdentifier(declaration.id);
	}
	if (!t.isExpressionStatement(stmt)) return false;
	const assignment = stmt.expression;
	return t.isAssignmentExpression(assignment, { operator: '=' }) &&
		isRecoveredEnvironmentSSAIdentifier(assignment.left);
}

function getSingleIdentifierInit(
	stmt: t.Statement | undefined,
): { name: string; init: string } | undefined {
	if (!stmt || !t.isVariableDeclaration(stmt)) return;
	if (stmt.declarations.length !== 1) return;
	const [decl] = stmt.declarations;
	if (!t.isIdentifier(decl.id) || !t.isIdentifier(decl.init)) return;
	return { name: decl.id.name, init: decl.init.name };
}

function isUninitializedGeneratedLet(stmt: t.Statement | undefined): boolean {
	if (!stmt || !t.isVariableDeclaration(stmt, { kind: 'let' })) return false;
	return stmt.declarations.length > 0 &&
		stmt.declarations.every((decl) =>
			t.isIdentifier(decl.id) &&
			isGeneratedRegisterName(decl.id.name) &&
			decl.init == null
		);
}

function expressionStatementAssignsIdentifierAlias(
	stmt: t.Statement | undefined,
): { name: string; init: t.Expression } | undefined {
	if (!stmt || !t.isExpressionStatement(stmt)) return;
	const expr = stmt.expression;
	if (!t.isAssignmentExpression(expr, { operator: '=' })) return;
	if (!t.isIdentifier(expr.left) || !t.isExpression(expr.right)) return;
	return { name: expr.left.name, init: expr.right };
}

export function resolveIdentifierAlias(
	name: string,
	aliases: ReadonlyMap<string, string>,
): string {
	let current = name;
	const seen = new Set<string>();
	while (true) {
		const next = aliases.get(current);
		if (!next || seen.has(next)) return current;
		seen.add(current);
		current = next;
	}
}

function resolveExpressionAlias(
	expr: t.Expression,
	aliases: ReadonlyMap<string, string>,
): t.Expression {
	if (!t.isIdentifier(expr)) return expr;
	const resolved = resolveIdentifierAlias(expr.name, aliases);
	return resolved === expr.name ? expr : t.identifier(resolved);
}

function isSameGeneratedRegisterAny(
	node: t.Node | undefined | null,
	names: Iterable<string>,
): boolean {
	for (const name of names) {
		if (isSameGeneratedRegister(node, name)) return true;
	}
	return false;
}

function expressionsSameRegisterOrGeneratedVersion(
	left: t.Expression,
	right: t.Expression,
): boolean {
	return registersEqual(left, right) ||
		(t.isIdentifier(right) && isSameGeneratedRegister(left, right.name));
}

function expressionMatchesIdentifierOrGeneratedVersion(
	expr: t.Expression,
	id: t.Identifier,
): boolean {
	return t.isIdentifier(expr, { name: id.name }) ||
		isSameGeneratedRegister(expr, id.name);
}

function isPhiDeclaration(stmt: t.Statement | undefined): boolean {
	if (!stmt || !t.isVariableDeclaration(stmt, { kind: 'const' })) {
		return false;
	}
	if (stmt.declarations.length !== 1) return false;
	const [decl] = stmt.declarations;
	return t.isCallExpression(decl.init) &&
		t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' });
}

function countLeadingPhiDeclarations(stmts: t.Statement[]): number {
	let count = 0;
	for (const stmt of stmts) {
		if (!isPhiDeclaration(stmt)) break;
		count++;
	}
	return count;
}

function collectUndefinedNames(func: IRFunction): Set<string> {
	const names = new Set(['undefined']);
	let changed;
	do {
		changed = false;
		for (const block of func.blocks.values()) {
			for (const stmt of block.body) {
				const init = getSingleConstInit(<t.Statement> stmt);
				if (
					init && t.isIdentifier(init.init) &&
					names.has(init.init.name) && !names.has(init.name)
				) {
					names.add(init.name);
					changed = true;
				}
			}
		}
	} while (changed);
	return names;
}

function isUndefinedCheck(
	test: t.Expression,
	valueName: string,
	undefinedNames = new Set(['undefined']),
): boolean {
	if (!t.isBinaryExpression(test, { operator: '===' })) return false;
	return (
		t.isIdentifier(test.left, { name: valueName }) &&
		t.isIdentifier(test.right) && undefinedNames.has(test.right.name)
	) || (
		t.isIdentifier(test.right, { name: valueName }) &&
		t.isIdentifier(test.left) && undefinedNames.has(test.left.name)
	);
}
function isDefinedCheck(test: t.Expression, valueName: string): boolean {
	if (
		!t.isBinaryExpression(test) ||
		!['!=', '!=='].includes(test.operator)
	) return false;
	return (
		t.isIdentifier(test.left, { name: valueName }) &&
		t.isIdentifier(test.right, { name: 'undefined' })
	) || (
		t.isIdentifier(test.right, { name: valueName }) &&
		t.isIdentifier(test.left, { name: 'undefined' })
	);
}

function getExpressionStatementAssignment(
	stmt: t.Statement | undefined,
): t.AssignmentExpression | undefined {
	if (!stmt || !t.isExpressionStatement(stmt)) return;
	if (!t.isAssignmentExpression(stmt.expression, { operator: '=' })) return;
	return stmt.expression;
}

function replaceIdentifierInStatements(
	stmts: t.Statement[],
	from: string,
	to: string,
): void {
	for (const stmt of stmts) {
		t.traverseFast(stmt, (node) => {
			if (t.isIdentifier(node, { name: from })) {
				node.name = to;
			}
		});
	}
}

function statementReferencesAnyName(
	stmt: t.Statement,
	names: ReadonlySet<string>,
): boolean {
	let found = false;
	t.traverseFast(stmt, (node) => {
		if (found) return t.traverseFast.skip;
		if (t.isIdentifier(node) && names.has(node.name)) found = true;
	});
	return found;
}

function statementListReferencesAnyName(
	stmts: t.Statement[],
	names: ReadonlySet<string>,
): boolean {
	return stmts.some((stmt) => statementReferencesAnyName(stmt, names));
}

function replaceReturnWithBreakForName(
	stmts: t.Statement[],
	name: string,
): boolean {
	let changed = false;
	for (let i = 0; i < stmts.length; i++) {
		const stmt = stmts[i];
		if (
			t.isReturnStatement(stmt) &&
			t.isIdentifier(stmt.argument, { name })
		) {
			stmts[i] = t.breakStatement();
			changed = true;
			continue;
		}
		if (t.isBlockStatement(stmt)) {
			changed = replaceReturnWithBreakForName(stmt.body, name) ||
				changed;
		} else if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = replaceReturnWithBreakForName(
					stmt.consequent.body,
					name,
				) || changed;
			}
			if (t.isBlockStatement(stmt.alternate)) {
				changed = replaceReturnWithBreakForName(
					stmt.alternate.body,
					name,
				) || changed;
			}
		}
	}
	return changed;
}

function convertLoopExitReturnsToBreaks(
	func: IRFunction,
	loopBody: t.Statement[],
	loopExit: BlockAddr,
	loopExitBody?: t.Statement[],
): boolean {
	const exitBody = loopExitBody ?? (func.blocks.get(loopExit)?.body as
		| t.Statement[]
		| undefined);
	if (!exitBody || exitBody.length !== 1) return false;
	const exitReturn = exitBody[0];
	if (
		!t.isReturnStatement(exitReturn) || !t.isIdentifier(exitReturn.argument)
	) {
		return false;
	}
	return replaceReturnWithBreakForName(loopBody, exitReturn.argument.name);
}

function getSingleConstInit(
	stmt: t.Statement | undefined,
): { name: string; init: t.Expression } | undefined {
	if (!stmt || !t.isVariableDeclaration(stmt, { kind: 'const' })) return;
	if (stmt.declarations.length !== 1) return;
	const [decl] = stmt.declarations;
	if (!t.isIdentifier(decl.id)) return;
	if (!t.isExpression(decl.init)) return;
	return { name: decl.id.name, init: decl.init };
}

function isIteratorCloseForNames(
	stmt: t.Statement | undefined,
	names: string[],
	aliases: ReadonlyMap<string, string> = new Map(),
): boolean {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	if (
		!t.isCallExpression(expr) ||
		!t.isV8IntrinsicIdentifier(expr.callee, { name: 'IteratorClose' }) ||
		expr.arguments.length !== 2
	) return false;
	const [stateArg, ignoreArg] = expr.arguments;
	const resolvedStateArg = t.isExpression(stateArg)
		? resolveExpressionAlias(stateArg, aliases)
		: stateArg;
	return isSameGeneratedRegisterAny(resolvedStateArg, names) &&
		t.isBooleanLiteral(ignoreArg);
}

function isAbruptForOfExit(
	stmt: t.Statement | undefined,
	allowBreak: boolean,
): boolean {
	if (t.isReturnStatement(stmt) || t.isThrowStatement(stmt)) return true;
	return allowBreak && t.isBreakStatement(stmt) && !stmt.label;
}

function invertCondition(expr: t.Expression): t.Expression {
	if (
		t.isUnaryExpression(expr, { operator: '!' }) &&
		t.isExpression(expr.argument)
	) {
		return t.cloneNode(expr.argument, true);
	}
	if (t.isBinaryExpression(expr)) {
		const operator = expr.operator === '==='
			? '!=='
			: expr.operator === '!=='
			? '==='
			: expr.operator === '=='
			? '!='
			: expr.operator === '!='
			? '=='
			: null;
		if (operator) {
			return t.binaryExpression(
				operator,
				t.cloneNode(expr.left, true),
				t.cloneNode(expr.right, true),
			);
		}
	}
	return t.unaryExpression('!', t.cloneNode(expr, true), true);
}

function pNameListSemanticGuard(
	stmt: t.Statement | undefined,
	listName: string,
): {
	stmt: t.IfStatement;
	body: t.Statement[];
	test?: t.Expression;
} | null {
	if (
		!t.isIfStatement(stmt) ||
		!t.isBlockStatement(stmt.consequent)
	) return null;
	if (t.isBlockStatement(stmt.alternate)) {
		const test = stmt.test;
		if (
			t.isBinaryExpression(test, { operator: '===' }) &&
			t.isIdentifier(test.left, { name: listName }) &&
			t.isIdentifier(test.right, { name: 'undefined' }) &&
			stmt.consequent.body.every(isSyntheticPhiPlumbing)
		) return { stmt, body: stmt.alternate.body };
		if (
			t.isBinaryExpression(test, { operator: '!==' }) &&
			t.isIdentifier(test.left, { name: listName }) &&
			t.isIdentifier(test.right, { name: 'undefined' }) &&
			stmt.alternate.body.every(isSyntheticPhiPlumbing)
		) return { stmt, body: stmt.consequent.body };
		return null;
	}
	const test = stmt.test;
	if (
		t.isBinaryExpression(test, { operator: '!==' }) &&
		t.isIdentifier(test.left, { name: listName }) &&
		t.isIdentifier(test.right, { name: 'undefined' })
	) return { stmt, body: stmt.consequent.body };
	if (
		t.isUnaryExpression(test, { operator: '!' }) &&
		t.isBinaryExpression(test.argument, { operator: '===' }) &&
		t.isIdentifier(test.argument.left, { name: listName }) &&
		t.isIdentifier(test.argument.right, { name: 'undefined' })
	) return { stmt, body: stmt.consequent.body };
	if (
		t.isUnaryExpression(test, { operator: '!' }) &&
		t.isLogicalExpression(test.argument, { operator: '||' })
	) {
		const checks = [test.argument.left, test.argument.right];
		const listCheckIndex = checks.findIndex((check) =>
			t.isBinaryExpression(check, { operator: '===' }) &&
			t.isIdentifier(check.left, { name: listName }) &&
			t.isIdentifier(check.right, { name: 'undefined' })
		);
		if (listCheckIndex >= 0) {
			const semantic = checks[1 - listCheckIndex];
			if (t.isExpression(semantic)) {
				return {
					stmt,
					body: stmt.consequent.body,
					test: invertCondition(semantic),
				};
			}
		}
	}
	return null;
}

function isIteratorDoneBreak(
	stmt: t.Statement | undefined,
	keyName: string,
): boolean {
	if (
		!t.isIfStatement(stmt) ||
		stmt.alternate ||
		!t.isBlockStatement(stmt.consequent)
	) return false;
	if (!isUndefinedCheck(stmt.test, keyName)) return false;
	return stmt.consequent.body.length === 1 &&
		t.isBreakStatement(stmt.consequent.body[0]);
}

function stripIteratorCloseBeforeAbruptExit(
	stmts: t.Statement[],
	iteratorNames: Iterable<string>,
	allowBreak = true,
): boolean {
	const names = [...iteratorNames];
	let changed = false;
	for (let i = stmts.length - 2; i >= 0; i--) {
		const stmt = stmts[i];
		const next = stmts[i + 1];
		if (!isAbruptForOfExit(next, allowBreak)) continue;
		const aliases = iteratorCloseAliasesBefore(stmts, i, names);
		if (!isIteratorCloseForNames(stmt, names, aliases)) continue;
		stmts.splice(i, 1);
		changed = true;
		while (
			i > 0 &&
			isRedundantIteratorCloseAlias(stmts[i - 1], names, aliases)
		) {
			stmts.splice(i - 1, 1);
			changed = true;
			i--;
		}
	}

	for (const stmt of stmts) {
		if (t.isBlockStatement(stmt)) {
			changed = stripIteratorCloseBeforeAbruptExit(
				stmt.body,
				names,
				allowBreak,
			) || changed;
		} else if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = stripIteratorCloseBeforeAbruptExit(
					stmt.consequent.body,
					names,
					allowBreak,
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = stripIteratorCloseBeforeAbruptExit(
					stmt.alternate.body,
					names,
					allowBreak,
				) || changed;
			}
		} else if (t.isTryStatement(stmt)) {
			changed = stripIteratorCloseBeforeAbruptExit(
				stmt.block.body,
				names,
				allowBreak,
			) || changed;
			if (stmt.handler) {
				changed = stripIteratorCloseBeforeAbruptExit(
					stmt.handler.body.body,
					names,
					allowBreak,
				) || changed;
			}
			if (stmt.finalizer) {
				changed = stripIteratorCloseBeforeAbruptExit(
					stmt.finalizer.body,
					names,
					allowBreak,
				) || changed;
			}
		} else if (
			t.isWhileStatement(stmt) ||
			t.isForStatement(stmt) ||
			t.isForInStatement(stmt) ||
			t.isForOfStatement(stmt) ||
			t.isDoWhileStatement(stmt)
		) {
			if (t.isBlockStatement(stmt.body)) {
				changed = stripIteratorCloseBeforeAbruptExit(
					stmt.body.body,
					names,
					false,
				) || changed;
			}
		}
	}
	return changed;
}

function iteratorCloseAliasesBefore(
	stmts: t.Statement[],
	closeIndex: number,
	names: string[],
): Map<string, string> {
	const aliases = new Map<string, string>();
	for (let i = closeIndex - 1; i >= 0; i--) {
		const alias = getSingleIdentifierInit(stmts[i]);
		if (!alias || !isGeneratedRegisterName(alias.name)) break;
		const resolved = resolveIdentifierAlias(alias.init, aliases);
		if (!isSameGeneratedRegisterAny(t.identifier(resolved), names)) break;
		aliases.set(alias.name, resolved);
	}
	return aliases;
}

function isRedundantIteratorCloseAlias(
	stmt: t.Statement | undefined,
	names: string[],
	aliases: ReadonlyMap<string, string>,
): boolean {
	const alias = getSingleIdentifierInit(stmt);
	if (!alias || !isGeneratedRegisterName(alias.name)) return false;
	return isSameGeneratedRegisterAny(
		t.identifier(resolveIdentifierAlias(alias.init, aliases)),
		names,
	);
}

function removeIteratorHeaderStatements(
	stmts: t.Statement[],
	prefixLength: number,
	headerStatementCount: number,
): t.Statement[] {
	return [
		...stmts.slice(0, prefixLength),
		...stmts.slice(prefixLength + headerStatementCount),
	].map((stmt) => t.cloneNode(stmt, true));
}

function findPreheaderInit(
	func: IRFunction,
	header: BlockAddr,
	body: AddressSet<BlockAddr>,
	intrinsicName: string,
	predicate: (decl: MultiIntrinsicDecl) => boolean,
) {
	const candidates = new Set<BlockAddr>();
	for (const pred of func.predecessorsOf(header)) {
		const predBlock = func.blocks.get(pred);
		if (pred < 0 && predBlock && predBlock.body.length === 0) {
			for (const predPred of func.predecessorsOf(pred)) {
				if (predPred !== pred) candidates.add(predPred);
			}
		}
		candidates.add(pred);
	}
	for (const pred of candidates) {
		if (body.has(pred)) continue;
		const block = func.blocks.get(pred);
		if (!block) continue;
		for (let i = block.body.length - 1; i >= 0; i--) {
			const decl = getMultiIntrinsicDecl(
				<t.Statement> block.body[i],
				intrinsicName,
			);
			if (decl && predicate(decl)) {
				return { block, index: i, decl };
			}
		}
	}
}

function removePreheaderInitAndAliases(
	preheader: { block: { body: LiftedAST<t.Statement>[] }; index: number },
	names: Iterable<string>,
): void {
	const removableNames = new Set(names);
	const undefinedNames = new Set(['undefined']);
	preheader.block.body.splice(preheader.index, 1);
	let scanIndex = preheader.index;
	while (true) {
		const alias = getSingleIdentifierInit(
			<t.Statement> preheader.block.body[scanIndex],
		);
		if (!alias || !isGeneratedRegisterName(alias.name)) return;
		if (undefinedNames.has(alias.init)) {
			undefinedNames.add(alias.name);
			scanIndex++;
			continue;
		}
		if (
			!isGeneratedRegisterName(alias.init) ||
			!isSameGeneratedRegisterAny(
				t.identifier(alias.init),
				removableNames,
			)
		) return;
		removableNames.add(alias.name);
		preheader.block.body.splice(scanIndex, 1);
	}
}

function isIteratorCarryPhi(
	stmt: t.Statement,
	beginIterator: t.Identifier,
	nextIterator: t.Identifier,
): boolean {
	if (!t.isVariableDeclaration(stmt, { kind: 'const' })) return false;
	if (stmt.declarations.length !== 1) return false;
	const [decl] = stmt.declarations;
	if (!t.isIdentifier(decl.id) || !t.isCallExpression(decl.init)) {
		return false;
	}
	if (!t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })) {
		return false;
	}
	if (!isSameGeneratedRegister(decl.id, beginIterator.name)) return false;
	const args = decl.init.arguments;
	return args.some((arg) =>
		isSameGeneratedRegister(arg, beginIterator.name)
	) &&
		args.some((arg) => isSameGeneratedRegister(arg, nextIterator.name));
}

function isLoopCarriedRegisterPhi(
	stmt: t.Statement,
	register: t.Expression,
): boolean {
	if (!t.isIdentifier(register)) return false;
	if (!t.isVariableDeclaration(stmt, { kind: 'const' })) return false;
	if (stmt.declarations.length !== 1) return false;
	const [decl] = stmt.declarations;
	if (!t.isIdentifier(decl.id) || !t.isCallExpression(decl.init)) {
		return false;
	}
	if (!t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })) {
		return false;
	}
	return isSameGeneratedRegister(decl.id, register.name) &&
		decl.init.arguments.some((arg) =>
			isSameGeneratedRegister(arg, register.name)
		);
}

function consumePreheaderSourceAlias(
	preheader: { block: { body: LiftedAST<t.Statement>[] }; index: number },
	expr: t.Expression,
): t.Expression {
	let current = expr;
	while (t.isIdentifier(current) && isGeneratedRegisterName(current.name)) {
		let replaced = false;
		for (let i = preheader.index - 1; i >= 0; i--) {
			const stmt = <t.Statement> preheader.block.body[i];
			if (!t.isVariableDeclaration(stmt)) continue;
			if (stmt.declarations.length !== 1) continue;
			const [decl] = stmt.declarations;
			if (
				!t.isIdentifier(decl.id, { name: current.name }) ||
				!t.isExpression(decl.init)
			) continue;
			if (
				t.isArrayExpression(decl.init) ||
				t.isObjectExpression(decl.init) ||
				t.isNewExpression(decl.init) ||
				t.isFunctionExpression(decl.init) ||
				t.isArrowFunctionExpression(decl.init) ||
				t.isClassExpression(decl.init) ||
				t.isRegExpLiteral(decl.init)
			) {
				return current;
			}
			current = t.cloneNode(decl.init, true);
			preheader.block.body.splice(i, 1);
			if (i < preheader.index) preheader.index--;
			replaced = true;
			break;
		}
		if (!replaced) break;
	}
	return current;
}

function extractLoopBinding(
	stmts: t.Statement[],
	valueName: string,
): t.ForInStatement['left'] | t.ForOfStatement['left'] | undefined {
	let offset = 0;
	while (isPhiDeclaration(stmts[offset])) offset++;
	const first = stmts[offset];
	const firstAssign = getExpressionStatementAssignment(first);
	if (
		firstAssign && t.isIdentifier(firstAssign.right, { name: valueName }) &&
		t.isLVal(firstAssign.left)
	) {
		stmts.splice(offset, 1);
		if (t.isIdentifier(firstAssign.left)) {
			replaceIdentifierInStatements(
				stmts,
				valueName,
				firstAssign.left.name,
			);
		}
		return <t.LVal> firstAssign.left;
	}

	if (t.isVariableDeclaration(first) && first.declarations.length === 1) {
		const [decl] = first.declarations;
		if (
			decl.init && t.isIdentifier(decl.init, { name: valueName }) &&
			t.isLVal(decl.id)
		) {
			stmts.splice(offset, 1);
			if (t.isIdentifier(decl.id)) {
				replaceIdentifierInStatements(stmts, valueName, decl.id.name);
			}
			return t.variableDeclaration(first.kind, [
				t.variableDeclarator(decl.id),
			]);
		}
	}

	if (t.isTryStatement(first)) {
		return extractLoopBinding(first.block.body, valueName);
	}

	if (isGeneratedRegisterName(valueName)) {
		return t.variableDeclaration('const', [
			t.variableDeclarator(t.identifier(valueName)),
		]);
	}
}

function getConstIdentifierAlias(
	stmt: t.Statement | undefined,
	sourceName: string,
): string | undefined {
	const init = getSingleConstInit(stmt);
	if (!init) return;
	if (!t.isIdentifier(init.init, { name: sourceName })) return;
	return init.name;
}

function isIteratorDoneCheck(
	test: t.Expression,
	valueName: string,
	undefinedNames = new Set(['undefined']),
): boolean {
	if (isUndefinedCheck(test, valueName, undefinedNames)) return true;
	if (!t.isBinaryExpression(test, { operator: '===' })) return false;
	return (
		t.isIdentifier(test.left, { name: valueName }) &&
		t.isIdentifier(test.right)
	) || (
		t.isIdentifier(test.right, { name: valueName }) &&
		t.isIdentifier(test.left)
	);
}

function getIteratorDoneExitStatements(
	stmt: t.Statement | undefined,
	valueName: string,
	undefinedNames?: Set<string>,
): t.Statement[] | undefined {
	if (!stmt || !t.isIfStatement(stmt)) return;
	if (!isIteratorDoneCheck(stmt.test, valueName, undefinedNames)) return;
	if (stmt.alternate) return;
	const consequent = t.isBlockStatement(stmt.consequent)
		? stmt.consequent.body
		: [stmt.consequent];
	const exit = consequent.at(-1);
	if (consequent.length === 1 && t.isBreakStatement(exit)) return [];
	if (exit && t.isReturnStatement(exit)) {
		return consequent.map((stmt) => t.cloneNode(stmt, true));
	}
}

function getIteratorUndefinedExit(
	stmts: t.Statement[],
	start: number,
	valueName: string,
	undefinedNames: Set<string>,
	loopLocalNames = new Set<string>(),
) {
	let offset = start;
	let checkedName = valueName;
	const exitPrelude: t.Statement[] = [];
	const movedNames = new Set<string>();
	while (true) {
		const direct = getIteratorDoneExitStatements(
			stmts[offset],
			checkedName,
			undefinedNames,
		);
		if (direct != null) {
			return {
				exitStatements: [...exitPrelude, ...direct],
				headerStatementCount: (offset - start) + 2,
				movedNames,
			};
		}

		const declarationAlias = getSingleConstInit(stmts[offset]);
		const assignmentAlias = getExpressionStatementAssignment(stmts[offset]);
		const alias = declarationAlias && t.isIdentifier(declarationAlias.init)
			? {
				name: declarationAlias.name,
				init: declarationAlias.init.name,
				declaration: true,
			}
			: assignmentAlias && t.isIdentifier(assignmentAlias.left) &&
					t.isIdentifier(assignmentAlias.right)
			? {
				name: assignmentAlias.left.name,
				init: assignmentAlias.right.name,
				declaration: false,
			}
			: undefined;
		if (!alias) return;
		if (alias.declaration && alias.init === checkedName) {
			checkedName = alias.name;
			offset++;
			continue;
		}
		if (
			!isGeneratedRegisterName(alias.name) ||
			!isGeneratedRegisterName(alias.init) ||
			isSameGeneratedRegisterAny(
				t.identifier(alias.name),
				loopLocalNames,
			) ||
			isSameGeneratedRegisterAny(t.identifier(alias.init), loopLocalNames)
		) return;
		// Phi lowering can materialize an outer-loop carry beside the iterator
		// done check. It is pure and belongs on the exhaustion edge, after
		// for-of.
		exitPrelude.push(t.cloneNode(stmts[offset]!, true));
		movedNames.add(alias.name);
		offset++;
	}
}

function tryBuildForInStatement(
	func: IRFunction,
	header: BlockAddr,
	body: AddressSet<BlockAddr>,
	stmts: t.Statement[],
	_loopExit: BlockAddr,
): StructuredIteratorLoop | undefined {
	const fail = (reason: string) => {
		debugIterator('for-in fail', header.toString(16), reason);
		return undefined;
	};
	const prefixLength = countLeadingPhiDeclarations(stmts);
	let nextOffset = prefixLength;
	while (true) {
		const init = getSingleIdentifierInit(stmts[nextOffset]);
		if (
			init &&
			isGeneratedRegisterName(init.name) &&
			isGeneratedRegisterName(init.init)
		) {
			nextOffset++;
			continue;
		}
		const assign = expressionStatementAssignsIdentifierAlias(
			stmts[nextOffset],
		);
		if (
			assign &&
			isGeneratedRegisterName(assign.name) &&
			t.isIdentifier(assign.init) &&
			isGeneratedRegisterName(assign.init.name)
		) {
			nextOffset++;
			continue;
		}
		break;
	}
	const nextDecl = getMultiIntrinsicDecl(stmts[nextOffset], 'GetNextPName');
	if (
		!nextDecl || nextDecl.destinations.length !== 2 ||
		nextDecl.call.arguments.length !== 3
	) return fail('next');
	const [key] = nextDecl.destinations;
	const headerBranch = func.blocks.get(header)!.branch;
	const undefinedNames = collectUndefinedNames(func);
	const exit = getIteratorUndefinedExit(
		stmts,
		nextOffset + 1,
		key.name,
		undefinedNames,
	);
	if (
		!exit &&
		(!headerBranch ||
			!isUndefinedCheck(
				<t.Expression> headerBranch,
				key.name,
				undefinedNames,
			))
	) return fail('exit');

	const [iteratorArg, objectArg, indexArg] = nextDecl.call.arguments;
	if (
		!t.isExpression(iteratorArg) || !t.isExpression(objectArg) ||
		!t.isExpression(indexArg)
	) return fail('next args');
	const sizeArg = nextDecl.call.arguments[2];
	if (!t.isExpression(sizeArg)) return fail('size arg');

	// Phi nodes can alias GetNextPName's loop-carried arguments (e.g. the index counter
	// register reuses the original object register). Resolve each phi to its initial source
	// for the preheader-matching check, then compare generated register families so a
	// loop-carried rN_k version still matches the preheader's rN_j seed.
	const resolveInitialPhiArg = (arg: t.Expression): t.Expression => {
		if (!t.isIdentifier(arg)) return arg;
		for (let j = 0; j < prefixLength; j++) {
			const phiStmt = stmts[j];
			if (!t.isVariableDeclaration(phiStmt)) continue;
			const phiDecl = phiStmt.declarations[0];
			if (
				!t.isIdentifier(phiDecl.id, { name: arg.name }) ||
				!t.isCallExpression(phiDecl.init)
			) continue;
			if (
				!t.isV8IntrinsicIdentifier(phiDecl.init.callee, { name: 'Phi' })
			) continue;
			for (const a of phiDecl.init.arguments as t.Expression[]) {
				if (t.isIdentifier(a) && a.name !== arg.name) return a;
			}
		}
		return arg;
	};
	const resolvedIteratorArg = resolveInitialPhiArg(
		iteratorArg as t.Expression,
	);
	const resolvedObjectArg = resolveInitialPhiArg(objectArg as t.Expression);
	const resolvedIndexArg = resolveInitialPhiArg(indexArg as t.Expression);

	const preheader = findPreheaderInit(
		func,
		header,
		body,
		'GetPNameList',
		(decl) => {
			if (
				decl.destinations.length !== 3 ||
				decl.call.arguments.length !== 1
			) return false;
			const [propertyList, index] = decl.destinations;
			const [object] = decl.call.arguments;
			return expressionMatchesIdentifierOrGeneratedVersion(
				resolvedIteratorArg,
				propertyList,
			) &&
				expressionMatchesIdentifierOrGeneratedVersion(
					resolvedIndexArg,
					index,
				) &&
				t.isExpression(object) &&
				expressionsSameRegisterOrGeneratedVersion(
					resolvedObjectArg,
					object,
				);
		},
	);
	if (!preheader) return fail('preheader');

	const headerBlock = func.blocks.get(header) as IRBlock;
	const headerStatementCount = exit?.headerStatementCount ?? 2;
	const forInConsumed = stmts.slice(
		nextOffset,
		nextOffset + headerStatementCount,
	);
	const forInExitStmts = forInConsumed.slice(1);
	if (
		!consumedDefinitionsAreDead(
			func,
			headerBlock,
			forInConsumed,
			[
				iteratorArg as t.Expression,
				objectArg as t.Expression,
				indexArg as t.Expression,
				...forInExitStmts,
				t.identifier('undefined'),
				t.identifier('global'),
			],
			[],
			new Set(),
			true,
		)
	) return fail('live consumed');

	let loopBody = [
		...stmts.slice(0, nextOffset),
		...stmts.slice(nextOffset + headerStatementCount),
	].map((stmt) => t.cloneNode(stmt, true));
	loopBody = loopBody.filter((stmt) =>
		!isLoopCarriedRegisterPhi(stmt, resolvedObjectArg) &&
		!isLoopCarriedRegisterPhi(stmt, resolvedIndexArg)
	);
	const left = extractLoopBinding(loopBody, key.name);
	if (!left) return fail('binding');

	const object = consumePreheaderSourceAlias(preheader, resolvedObjectArg);
	preheader.block.body.splice(preheader.index, 1);
	const forIn = t.forInStatement(
		left,
		t.cloneNode(object, true),
		t.blockStatement(loopBody),
	);
	forIn.extra = { ...forIn.extra, fromCFGLoop: true };
	return {
		loop: forIn,
		exitStatements: exit?.exitStatements ?? [],
		PNameArray: preheader.decl.destinations[0],
	};
}

function tryBuildForOfStatement(
	func: IRFunction,
	header: BlockAddr,
	body: AddressSet<BlockAddr>,
	stmts: t.Statement[],
	loopExit: BlockAddr,
	loopExitBody?: t.Statement[],
): StructuredIteratorLoop | undefined {
	const fail = (reason: string) => {
		debugIterator('for-of fail', header.toString(16), reason);
		return undefined;
	};
	const prefixLength = countLeadingPhiDeclarations(stmts);
	const undefinedNames = collectUndefinedNames(func);
	let beginOffset = prefixLength;
	while (true) {
		const init = getSingleConstInit(stmts[beginOffset]);
		if (
			!init || !t.isIdentifier(init.init) ||
			!undefinedNames.has(init.init.name)
		) break;
		undefinedNames.add(init.name);
		beginOffset++;
	}
	const localBegin = getMultiIntrinsicDecl(
		stmts[beginOffset],
		'IteratorBegin',
	);
	let nextOffset = localBegin ? beginOffset + 1 : prefixLength;
	while (true) {
		const init = getSingleConstInit(stmts[nextOffset]);
		if (
			!init || !t.isIdentifier(init.init) ||
			!undefinedNames.has(init.init.name)
		) break;
		undefinedNames.add(init.name);
		nextOffset++;
	}
	const headerAliases = new Map<string, string>();
	const movableHeaderDeclarations: t.Statement[] = [];
	while (true) {
		const init = getSingleIdentifierInit(stmts[nextOffset]);
		if (init) {
			if (
				!isGeneratedRegisterName(init.name) ||
				!isGeneratedRegisterName(init.init)
			) break;
			headerAliases.set(
				init.name,
				resolveIdentifierAlias(init.init, headerAliases),
			);
			nextOffset++;
			continue;
		}
		if (!isUninitializedGeneratedLet(stmts[nextOffset])) break;
		movableHeaderDeclarations.push(stmts[nextOffset]);
		nextOffset++;
	}
	const nextDecl = getMultiIntrinsicDecl(stmts[nextOffset], 'IteratorNext');
	if (
		!nextDecl || nextDecl.destinations.length !== 2 ||
		nextDecl.call.arguments.length !== 2
	) return fail('next');
	const [value, nextIterator] = nextDecl.destinations;
	const [iteratorArg, sourceOrNextArg] = nextDecl.call.arguments;
	if (!t.isExpression(iteratorArg) || !t.isExpression(sourceOrNextArg)) {
		return fail('next args');
	}
	const resolvedIteratorArg = resolveExpressionAlias(
		iteratorArg,
		headerAliases,
	);
	const resolvedSourceOrNextArg = resolveExpressionAlias(
		sourceOrNextArg,
		headerAliases,
	);
	const preheader = localBegin
		? undefined
		: findPreheaderInit(func, header, body, 'IteratorBegin', (decl) => {
			if (
				decl.destinations.length !== 2 ||
				decl.call.arguments.length !== 1
			) return false;
			const [iterator, sourceOrNext] = decl.destinations;
			return isSameGeneratedRegister(
				resolvedIteratorArg,
				iterator.name,
			) &&
				isSameGeneratedRegister(
					resolvedSourceOrNextArg,
					sourceOrNext.name,
				);
		});
	if (!preheader && !localBegin) return fail('preheader');
	const beginDecl = localBegin ?? preheader!.decl;
	if (
		beginDecl.destinations.length !== 2 ||
		beginDecl.call.arguments.length !== 1
	) return fail('begin shape');
	const [beginIterator, beginSourceOrNext] = beginDecl.destinations;
	if (
		!isSameGeneratedRegister(resolvedIteratorArg, beginIterator.name) ||
		!isSameGeneratedRegister(
			resolvedSourceOrNextArg,
			beginSourceOrNext.name,
		)
	) return fail('begin args');
	const headerBranch = func.blocks.get(header)!.branch;
	const exit = getIteratorUndefinedExit(
		stmts,
		nextOffset + 1,
		nextIterator.name,
		undefinedNames,
		new Set([
			value.name,
			nextIterator.name,
			beginIterator.name,
			beginSourceOrNext.name,
			...headerAliases.keys(),
		]),
	);
	if (
		!exit &&
		(!headerBranch ||
			!isUndefinedCheck(
				<t.Expression> headerBranch,
				nextIterator.name,
				undefinedNames,
			))
	) {
		return fail('exit');
	}
	const [iterable] = beginDecl.call.arguments;
	if (!t.isExpression(iterable)) {
		return fail('iterable');
	}

	const forOfBlock = func.blocks.get(header) as IRBlock;
	const forOfConsumed = stmts.slice(
		prefixLength,
		nextOffset + (exit?.headerStatementCount ?? 2),
	);
	const forOfExitStmts = forOfConsumed.slice(nextOffset - prefixLength + 1);
	if (
		!consumedDefinitionsAreDead(
			func,
			forOfBlock,
			forOfConsumed,
			[
				iterable,
				iteratorArg,
				sourceOrNextArg,
				...forOfExitStmts,
				t.identifier('undefined'),
				t.identifier('global'),
			],
			[],
			new Set(),
			true,
		)
	) return fail('live consumed');

	const source = preheader
		? consumePreheaderSourceAlias(preheader, iterable)
		: iterable;

	let loopBody = removeIteratorHeaderStatements(
		stmts,
		prefixLength,
		(nextOffset - prefixLength) + (exit?.headerStatementCount ?? 2),
	);
	loopBody = [
		...movableHeaderDeclarations.map((stmt) => t.cloneNode(stmt, true)),
		...loopBody,
	];
	loopBody = loopBody.filter((stmt) =>
		!isIteratorCarryPhi(stmt, beginIterator, nextIterator)
	);
	if (
		exit &&
		statementListReferencesAnyName(loopBody, exit.movedNames)
	) return fail('exit prelude used in loop');
	const left = t.variableDeclaration('const', [
		t.variableDeclarator(t.identifier(value.name)),
	]);
	const closeNames = [
		beginIterator.name,
		beginSourceOrNext.name,
		nextIterator.name,
	];
	stripIteratorCloseBeforeAbruptExit(loopBody, closeNames);
	if (statementListReferencesAnyName(loopBody, new Set(closeNames))) {
		return fail('iterator carry leak');
	}
	if (t.isContinueStatement(loopBody.at(-1))) {
		loopBody.pop();
	}
	convertLoopExitReturnsToBreaks(func, loopBody, loopExit, loopExitBody);

	if (preheader) {
		removePreheaderInitAndAliases(preheader, [
			beginIterator.name,
			beginSourceOrNext.name,
		]);
	}
	const forOf = t.forOfStatement(
		left,
		t.cloneNode(source, true),
		t.blockStatement(loopBody),
		false,
	);
	forOf.extra = { ...forOf.extra, fromCFGLoop: true };
	const wrapped: t.Statement[] = [forOf];
	liftPhiNodesInBody(wrapped, { preserveLoopPhiDestinations: true });
	return {
		loop: wrapped[0] as t.ForOfStatement,
		exitStatements: exit?.exitStatements ?? [],
	};
}

export function tryBuildForInOrOfStatement(
	func: IRFunction,
	header: BlockAddr,
	body: AddressSet<BlockAddr>,
	stmts: t.Statement[],
	loopExit: BlockAddr,
	loopExitBody?: t.Statement[],
): StructuredIteratorLoop | undefined {
	const result =
		tryBuildForInStatement(func, header, body, stmts, loopExit) ??
			tryBuildForOfStatement(
				func,
				header,
				body,
				stmts,
				loopExit,
				loopExitBody,
			);
	return result;
}

function collectIteratorNextStateNames(
	node: t.Node,
	out: Set<string>,
): void {
	t.traverseFast(node, (child) => {
		if (!t.isVariableDeclarator(child)) return;
		if (!t.isArrayPattern(child.id)) return;
		if (!t.isCallExpression(child.init)) return;
		if (
			!t.isV8IntrinsicIdentifier(child.init.callee, {
				name: 'IteratorNext',
			})
		) return;
		const [, state] = child.id.elements;
		if (t.isIdentifier(state)) out.add(state.name);
	});
}

export function stripIteratorCloseBeforeIteratorAbruptExits(
	stmts: t.Statement[],
): boolean {
	const names = new Set<string>();
	for (const stmt of stmts) collectIteratorNextStateNames(stmt, names);
	if (names.size === 0) return false;
	return stripIteratorCloseBeforeAbruptExit(stmts, names, false);
}
function memberCallOnIdentifier(
	expression: t.Expression,
	objectName: string,
	propertyName: string,
): t.CallExpression | null {
	if (!t.isCallExpression(expression)) return null;
	const callee = expression.callee;
	if (!t.isMemberExpression(callee) || callee.computed) return null;
	if (!t.isIdentifier(callee.object, { name: objectName })) return null;
	if (!t.isIdentifier(callee.property, { name: propertyName })) return null;
	return expression;
}

function hermesInternalCall(
	expression: t.Expression,
	propertyName: string,
): t.CallExpression | null {
	if (!t.isCallExpression(expression)) return null;
	const callee = expression.callee;
	if (!t.isMemberExpression(callee) || callee.computed) return null;
	if (!t.isIdentifier(callee.object, { name: 'HermesInternal' })) {
		return null;
	}
	if (!t.isIdentifier(callee.property, { name: propertyName })) return null;
	return expression;
}

function singleVariableIdentifierInit(
	statement: t.Statement | undefined,
): {
	name: string;
	init: t.Expression;
	kind: t.VariableDeclaration['kind'];
} | null {
	if (!statement || !t.isVariableDeclaration(statement)) return null;
	if (statement.declarations.length !== 1) return null;
	const [declaration] = statement.declarations;
	if (!t.isIdentifier(declaration.id) || !t.isExpression(declaration.init)) {
		return null;
	}
	return {
		name: declaration.id.name,
		init: declaration.init,
		kind: statement.kind,
	};
}
function createThisForNewConstructor(
	statement: t.Statement | undefined,
): string | null {
	if (!statement || !t.isExpressionStatement(statement)) return null;
	const expression = statement.expression;
	if (!t.isCallExpression(expression)) return null;
	if (
		!t.isV8IntrinsicIdentifier(expression.callee, {
			name: 'CreateThisForNew',
		}) ||
		expression.arguments.length === 0
	) return null;
	const [constructor] = expression.arguments;
	return t.isIdentifier(constructor) ? constructor.name : null;
}

function expressionContainsNewConstructor(
	expression: t.Expression,
	constructorName: string,
): boolean {
	let found = false;
	t.traverseFast(expression, (node) => {
		if (
			t.isNewExpression(node) &&
			t.isIdentifier(node.callee, { name: constructorName })
		) found = true;
	});
	return found;
}

function isEnsureObjectStatement(
	statement: t.Statement | undefined,
	name: string,
): boolean {
	if (!statement || !t.isExpressionStatement(statement)) return false;
	const call = hermesInternalCall(statement.expression, 'ensureObject');
	if (!call || call.arguments.length === 0) return false;
	return t.isIdentifier(call.arguments[0], { name });
}

function suspendsIdentifier(
	expression: t.Expression,
	awaitedName: string,
): boolean {
	const argument = t.isAwaitExpression(expression)
		? expression.argument
		: t.isYieldExpression(expression) && !expression.delegate
		? expression.argument
		: null;
	if (t.isIdentifier(argument, { name: awaitedName })) return true;
	if (!t.isExpression(argument)) return false;
	const awaitAsyncIterator = hermesInternalCall(
		argument,
		'awaitAsyncIterator',
	);
	return !!awaitAsyncIterator &&
		t.isIdentifier(awaitAsyncIterator.arguments[0], {
			name: awaitedName,
		});
}

function awaitedIdentifierAssignment(
	statement: t.Statement | undefined,
	awaitedName: string,
): { name: string } | null {
	const suspendedIdentifier = (expression: t.Expression) =>
		suspendsIdentifier(expression, awaitedName);
	const declaration = singleVariableIdentifierInit(statement);
	if (declaration && suspendedIdentifier(declaration.init)) {
		return { name: declaration.name };
	}
	if (!statement || !t.isExpressionStatement(statement)) return null;
	const expression = statement.expression;
	if (
		!t.isAssignmentExpression(expression, { operator: '=' }) ||
		!t.isIdentifier(expression.left) ||
		!suspendedIdentifier(expression.right)
	) return null;
	return { name: expression.left.name };
}

function asyncIteratorDoneBreakResultName(
	statement: t.Statement | undefined,
): string | null {
	if (!statement || !t.isIfStatement(statement) || statement.alternate) {
		return null;
	}
	const test = statement.test;
	if (
		!t.isMemberExpression(test) || test.computed ||
		!t.isIdentifier(test.object) ||
		!t.isIdentifier(test.property, { name: 'done' })
	) return null;
	if (
		!t.isBreakStatement(statement.consequent) &&
		!(
			t.isBlockStatement(statement.consequent) &&
			statement.consequent.body.length === 1 &&
			t.isBreakStatement(statement.consequent.body[0])
		)
	) return null;
	return test.object.name;
}

function isAsyncIteratorDoneBreak(
	statement: t.Statement | undefined,
	resultName: string,
): boolean {
	return asyncIteratorDoneBreakResultName(statement) === resultName;
}

function isAsyncIteratorValue(
	expression: t.Expression | null | undefined,
	resultName: string,
): boolean {
	return !!expression && t.isMemberExpression(expression) &&
		!expression.computed &&
		t.isIdentifier(expression.object, { name: resultName }) &&
		t.isIdentifier(expression.property, { name: 'value' });
}
function isAsyncIteratorValueBindingStatement(
	statement: t.Statement,
	resultName: string,
): boolean {
	if (
		t.isVariableDeclaration(statement) &&
		statement.declarations.length === 1
	) {
		const [declaration] = statement.declarations;
		return isAsyncIteratorValue(
			t.isExpression(declaration.init) ? declaration.init : null,
			resultName,
		);
	}
	if (!t.isExpressionStatement(statement)) return false;
	const expression = statement.expression;
	return t.isAssignmentExpression(expression, { operator: '=' }) &&
		isAsyncIteratorValue(expression.right, resultName);
}

function replaceAsyncIteratorValues(
	statements: t.Statement[],
	resultName: string,
	valueName: string,
): t.Statement[] {
	return statements.map((statement) => {
		const clone = t.cloneNode(statement, true);
		t.traverseFast(clone, (node) => {
			if (
				t.isMemberExpression(node) && !node.computed &&
				t.isIdentifier(node.object, { name: resultName }) &&
				t.isIdentifier(node.property, { name: 'value' })
			) {
				Object.assign(node, t.identifier(valueName));
			}
		});
		return clone;
	});
}

function extractAsyncIteratorBinding(
	statements: t.Statement[],
	resultName: string,
): {
	left: t.ForOfStatement['left'];
	body: t.Statement[];
} {
	const [first, ...rest] = statements;
	if (t.isVariableDeclaration(first) && first.declarations.length === 1) {
		const [declaration] = first.declarations;
		if (
			t.isIdentifier(declaration.id) &&
			isAsyncIteratorValue(
				t.isExpression(declaration.init) ? declaration.init : null,
				resultName,
			)
		) {
			return {
				left: t.variableDeclaration(first.kind, [
					t.variableDeclarator(t.cloneNode(declaration.id)),
				]),
				body: rest,
			};
		}
	}
	if (
		t.isExpressionStatement(first) &&
		t.isAssignmentExpression(first.expression, { operator: '=' }) &&
		t.isLVal(first.expression.left) &&
		isAsyncIteratorValue(first.expression.right, resultName)
	) {
		return {
			left: t.cloneNode(first.expression.left, true),
			body: rest,
		};
	}

	const valueName = `${resultName}_value`;
	return {
		left: t.variableDeclaration('const', [
			t.variableDeclarator(t.identifier(valueName)),
		]),
		body: replaceAsyncIteratorValues(statements, resultName, valueName),
	};
}
function renameSuspensionTarget(
	statement: t.Statement,
	from: string,
	to: string,
	kind: t.VariableDeclaration['kind'],
): t.Statement | null {
	const clone = t.cloneNode(statement, true);
	if (
		t.isVariableDeclaration(clone) &&
		clone.declarations.length === 1 &&
		t.isIdentifier(clone.declarations[0].id, { name: from })
	) {
		clone.kind = kind;
		clone.declarations[0].id.name = to;
		return clone;
	}
	if (
		t.isExpressionStatement(clone) &&
		t.isAssignmentExpression(clone.expression, { operator: '=' }) &&
		t.isIdentifier(clone.expression.left, { name: from })
	) {
		clone.expression.left.name = to;
		return clone;
	}
	return null;
}

function statementBody(statement: t.Statement): t.Statement[] {
	return t.isBlockStatement(statement) ? statement.body : [statement];
}

function suspendedAsyncIteratorClose(
	statement: t.Statement,
	methodName: string,
	iteratorName: string,
) {
	const expression = t.isExpressionStatement(statement)
		? statement.expression
		: null;
	if (!expression) return false;
	const suspension = t.isAwaitExpression(expression)
		? expression
		: t.isYieldExpression(expression) && !expression.delegate
		? expression
		: null;
	if (!suspension || !t.isExpression(suspension.argument)) return false;
	const awaited = hermesInternalCall(
		suspension.argument,
		'awaitAsyncIterator',
	);
	if (!awaited || awaited.arguments.length !== 1) return false;
	const close = awaited.arguments[0];
	if (!t.isExpression(close)) return false;
	const call = memberCallOnIdentifier(close, methodName, 'call');
	return !!call &&
		t.isIdentifier(call.arguments[0], { name: iteratorName });
}
function conditionalAsyncIteratorAdvance(
	statement: t.Statement,
	iteratorName: string,
	resultName: string,
): { test: t.Expression; nextName: string } | null {
	if (
		!t.isIfStatement(statement) ||
		statement.alternate ||
		!t.isBlockStatement(statement.consequent)
	) return null;
	const body = statement.consequent.body.filter((candidate) =>
		!isSyntheticPhiPlumbing(candidate)
	);
	if (
		body.length !== 4 ||
		!t.isContinueStatement(body[3]) ||
		body[3].label
	) return null;
	const next = singleVariableIdentifierInit(body[0]);
	if (
		!next ||
		!memberCallOnIdentifier(next.init, iteratorName, 'next') ||
		!isEnsureObjectStatement(body[1], next.name)
	) return null;
	const result = awaitedIdentifierAssignment(body[2], next.name);
	if (!result || result.name !== resultName) return null;
	return { test: statement.test, nextName: next.name };
}

function asyncIteratorCloseResultName(
	statement: t.Statement,
	methodName: string,
	iteratorName: string,
): string | null {
	const declaration = singleVariableIdentifierInit(statement);
	let resultName = declaration?.name;
	let expression = declaration?.init;
	if (
		!expression &&
		t.isExpressionStatement(statement) &&
		t.isAssignmentExpression(statement.expression, { operator: '=' }) &&
		t.isIdentifier(statement.expression.left) &&
		t.isExpression(statement.expression.right)
	) {
		resultName = statement.expression.left.name;
		expression = statement.expression.right;
	}
	if (!resultName || !expression) return null;
	const suspension = t.isAwaitExpression(expression)
		? expression
		: t.isYieldExpression(expression) && !expression.delegate
		? expression
		: null;
	if (!suspension || !t.isExpression(suspension.argument)) return null;
	const awaited = hermesInternalCall(
		suspension.argument,
		'awaitAsyncIterator',
	);
	if (!awaited || awaited.arguments.length !== 1) return null;
	const close = awaited.arguments[0];
	if (!t.isExpression(close)) return null;
	const call = memberCallOnIdentifier(close, methodName, 'call');
	if (
		!call ||
		!t.isIdentifier(call.arguments[0], { name: iteratorName })
	) return null;
	return resultName;
}

function asyncIteratorBreakContinuation(
	statements: t.Statement[],
	iteratorName: string,
): { body: t.Statement[]; protocolNames: Set<string> } | null {
	if (statements.length !== 2) return null;
	const method = singleVariableIdentifierInit(statements[0]);
	if (!method) return null;
	const getMethod = hermesInternalCall(method.init, 'getMethod');
	if (
		!getMethod ||
		!t.isIdentifier(getMethod.arguments[0], { name: iteratorName }) ||
		!t.isStringLiteral(getMethod.arguments[1], { value: 'return' })
	) return null;
	const branch = statements[1];
	if (
		!t.isIfStatement(branch) ||
		branch.alternate ||
		!t.isBinaryExpression(branch.test) ||
		!['!=', '!=='].includes(branch.test.operator) ||
		!t.isIdentifier(branch.test.left, { name: method.name }) ||
		!t.isIdentifier(branch.test.right, { name: 'undefined' })
	) return null;
	const present = statementBody(branch.consequent).filter((statement) =>
		!isSyntheticPhiPlumbing(statement)
	);
	if (present.length < 3) return null;
	const closeResultName = asyncIteratorCloseResultName(
		present[0],
		method.name,
		iteratorName,
	);
	if (
		!closeResultName ||
		!isEnsureObjectStatement(present[1], closeResultName)
	) return null;
	const body = present.slice(2);
	if (!t.isReturnStatement(body.at(-1))) return null;
	return {
		body,
		protocolNames: new Set([method.name, closeResultName]),
	};
}

function asyncIteratorCloseRethrowHandler(
	handler: t.CatchClause,
	iteratorName: string,
) {
	if (!t.isIdentifier(handler.param)) return false;
	const body = handler.body.body.filter((statement) =>
		!isSyntheticPhiPlumbing(statement)
	);
	let caughtName = handler.param.name;
	let index = 0;
	const first = body[0];
	if (
		t.isExpressionStatement(first) &&
		t.isAssignmentExpression(first.expression, { operator: '=' }) &&
		t.isIdentifier(first.expression.left) &&
		t.isIdentifier(first.expression.right, { name: caughtName })
	) {
		caughtName = first.expression.left.name;
		index++;
	}
	const method = singleVariableIdentifierInit(body[index]);
	if (!method) return false;
	const getMethod = hermesInternalCall(method.init, 'getMethod');
	if (
		!getMethod ||
		!t.isIdentifier(getMethod.arguments[0], { name: iteratorName }) ||
		!t.isStringLiteral(getMethod.arguments[1], { value: 'return' })
	) return false;
	const branch = body[index + 1];
	if (index + 2 !== body.length || !t.isIfStatement(branch)) return false;
	if (
		!t.isBinaryExpression(branch.test) ||
		!['==', '==='].includes(branch.test.operator) ||
		!t.isIdentifier(branch.test.left, { name: method.name }) ||
		!t.isIdentifier(branch.test.right, { name: 'undefined' }) ||
		!branch.alternate
	) return false;
	const absent = statementBody(branch.consequent).filter((statement) =>
		!isSyntheticPhiPlumbing(statement)
	);
	const present = statementBody(branch.alternate).filter((statement) =>
		!isSyntheticPhiPlumbing(statement)
	);
	return absent.length === 1 &&
		t.isThrowStatement(absent[0]) &&
		t.isIdentifier(absent[0].argument, { name: caughtName }) &&
		present.length === 2 &&
		suspendedAsyncIteratorClose(present[0], method.name, iteratorName) &&
		t.isThrowStatement(present[1]) &&
		t.isIdentifier(present[1].argument, { name: caughtName });
}

function normalizeAsyncIteratorTryWrappers(
	statements: t.Statement[],
): boolean {
	for (let start = 0; start < statements.length; start++) {
		const iterator = singleVariableIdentifierInit(statements[start]);
		if (
			!iterator ||
			!hermesInternalCall(iterator.init, 'makeAsyncIterator')
		) continue;
		const tryIndex = statements.findIndex((statement, index) =>
			index > start && t.isTryStatement(statement)
		);
		if (tryIndex < 0) continue;
		const tryStatement = statements[tryIndex];
		if (!t.isTryStatement(tryStatement) || !tryStatement.handler) continue;
		const catchBody = tryStatement.handler.body.body.filter((statement) =>
			!isSyntheticPhiPlumbing(statement)
		);
		const trivialStateMachineCatch = catchBody.length === 1 &&
			t.isReturnStatement(catchBody[0]) &&
			catchBody[0].argument == null;
		const iteratorCloseCatch = asyncIteratorCloseRethrowHandler(
			tryStatement.handler,
			iterator.name,
		);
		if (!trivialStateMachineCatch && !iteratorCloseCatch) continue;
		if (
			tryStatement.finalizer &&
			tryStatement.finalizer.body.some((statement) =>
				!isSyntheticPhiPlumbing(statement)
			)
		) continue;

		const prefix = statements.slice(start + 1, tryIndex);
		if (prefix.length < 3) continue;
		const next = singleVariableIdentifierInit(prefix[0]);
		if (
			!next ||
			!memberCallOnIdentifier(next.init, iterator.name, 'next') ||
			!isEnsureObjectStatement(prefix[1], next.name)
		) continue;
		const initialResult = awaitedIdentifierAssignment(
			prefix.at(-1),
			next.name,
		);
		if (!initialResult) continue;
		const protectedBody = tryStatement.block.body;
		const aliasIndex = protectedBody.findIndex((statement) =>
			!isSyntheticPhiPlumbing(statement)
		);
		if (aliasIndex < 0) continue;
		const alias = singleVariableIdentifierInit(protectedBody[aliasIndex]);
		if (
			!alias ||
			!t.isIdentifier(alias.init, { name: initialResult.name })
		) continue;
		const renamedSuspension = renameSuspensionTarget(
			prefix.at(-1)!,
			initialResult.name,
			alias.name,
			alias.kind,
		);
		if (!renamedSuspension) continue;

		statements.splice(
			start + 1,
			tryIndex - start,
			...prefix.slice(0, -1),
			renamedSuspension,
			...protectedBody.slice(aliasIndex + 1),
		);
		return true;
	}
	return false;
}

function cleanupLocalAsyncIteratorForOfLoopsInBody(
	statements: t.Statement[],
): boolean {
	let changed = normalizeAsyncIteratorTryWrappers(statements);
	for (const statement of statements) {
		if (
			t.isBlockStatement(statement) ||
			t.isWhileStatement(statement) ||
			t.isDoWhileStatement(statement) ||
			t.isForStatement(statement) ||
			t.isForInStatement(statement) ||
			t.isForOfStatement(statement)
		) {
			const body = t.isBlockStatement(statement)
				? statement.body
				: t.isBlockStatement(statement.body)
				? statement.body.body
				: [statement.body];
			changed = cleanupLocalAsyncIteratorForOfLoopsInBody(body) ||
				changed;
		} else if (t.isIfStatement(statement)) {
			const consequent = t.isBlockStatement(statement.consequent)
				? statement.consequent.body
				: [statement.consequent];
			changed = cleanupLocalAsyncIteratorForOfLoopsInBody(consequent) ||
				changed;
			if (statement.alternate) {
				const alternate = t.isBlockStatement(statement.alternate)
					? statement.alternate.body
					: [statement.alternate];
				changed =
					cleanupLocalAsyncIteratorForOfLoopsInBody(alternate) ||
					changed;
			}
		} else if (t.isTryStatement(statement)) {
			changed = cleanupLocalAsyncIteratorForOfLoopsInBody(
				statement.block.body,
			) || changed;
			if (statement.handler) {
				changed = cleanupLocalAsyncIteratorForOfLoopsInBody(
					statement.handler.body.body,
				) || changed;
			}
			if (statement.finalizer) {
				changed = cleanupLocalAsyncIteratorForOfLoopsInBody(
					statement.finalizer.body,
				) || changed;
			}
		}
	}

	for (let start = 0; start < statements.length; start++) {
		const iteratorDeclaration = singleVariableIdentifierInit(
			statements[start],
		);
		if (!iteratorDeclaration) continue;
		const makeIterator = hermesInternalCall(
			iteratorDeclaration.init,
			'makeAsyncIterator',
		);
		if (!makeIterator || makeIterator.arguments.length !== 1) continue;
		const [source] = makeIterator.arguments;
		if (!t.isExpression(source)) continue;

		let loopIndex = start + 1;
		while (
			loopIndex < statements.length &&
			!t.isWhileStatement(statements[loopIndex])
		) loopIndex++;
		if (loopIndex >= statements.length) continue;
		const loop = statements[loopIndex] as t.WhileStatement;
		if (!t.isBooleanLiteral(loop.test, { value: true })) continue;
		if (!t.isBlockStatement(loop.body)) continue;

		const initial = statements.slice(start + 1, loopIndex);
		const headLoopBody = loop.body.body.filter((candidate) =>
			!isSyntheticPhiPlumbing(candidate)
		);
		const headNext = singleVariableIdentifierInit(headLoopBody[0]);
		const headResult = headNext
			? awaitedIdentifierAssignment(headLoopBody[2], headNext.name)
			: null;
		if (
			initial.every(isSyntheticPhiPlumbing) &&
			headLoopBody.length >= 4 &&
			headNext &&
			memberCallOnIdentifier(
				headNext.init,
				iteratorDeclaration.name,
				'next',
			) &&
			isEnsureObjectStatement(headLoopBody[1], headNext.name) &&
			headResult &&
			isAsyncIteratorDoneBreak(headLoopBody[3], headResult.name)
		) {
			const binding = extractAsyncIteratorBinding(
				headLoopBody.slice(4),
				headResult.name,
			);
			if (
				!statementListReferencesAnyName(
					binding.body,
					new Set([
						iteratorDeclaration.name,
						headNext.name,
						headResult.name,
					]),
				)
			) {
				const forAwait = t.forOfStatement(
					binding.left,
					t.cloneNode(source, true),
					t.blockStatement(binding.body),
					true,
				) as LiftedAST<t.ForOfStatement>;
				forAwait.extra = {
					...forAwait.extra,
					recoveredAsyncIteratorNames: [iteratorDeclaration.name],
				};
				const createThisConstructor = createThisForNewConstructor(
					statements[start - 1],
				);
				const replacementStart = createThisConstructor &&
						expressionContainsNewConstructor(
							source,
							createThisConstructor,
						)
					? start - 1
					: start;
				statements.splice(
					replacementStart,
					loopIndex - replacementStart + 1,
					forAwait,
				);
				changed = true;
				start = replacementStart - 1;
				continue;
			}
		}
		if (initial.length < 3) continue;
		const firstNext = singleVariableIdentifierInit(initial[0]);
		if (
			!firstNext ||
			!memberCallOnIdentifier(
				firstNext.init,
				iteratorDeclaration.name,
				'next',
			) ||
			!isEnsureObjectStatement(initial[1], firstNext.name)
		) continue;
		const initialResult = awaitedIdentifierAssignment(
			initial.at(-1),
			firstNext.name,
		);
		if (!initialResult) continue;

		const loopBody = loop.body.body.filter((candidate) =>
			!isSyntheticPhiPlumbing(candidate) ||
			isAsyncIteratorValueBindingStatement(candidate, initialResult.name)
		);
		if (
			loopBody.length < 4 ||
			!isAsyncIteratorDoneBreak(loopBody[0], initialResult.name)
		) continue;
		const conditionalAdvanceIndex = loopBody.findIndex((statement, index) =>
			index > 0 &&
			conditionalAsyncIteratorAdvance(
					statement,
					iteratorDeclaration.name,
					initialResult.name,
				) !== null
		);
		if (conditionalAdvanceIndex > 0) {
			const advance = conditionalAsyncIteratorAdvance(
				loopBody[conditionalAdvanceIndex],
				iteratorDeclaration.name,
				initialResult.name,
			)!;
			const continuation = asyncIteratorBreakContinuation(
				loopBody.slice(conditionalAdvanceIndex + 1),
				iteratorDeclaration.name,
			);
			if (continuation) {
				const binding = extractAsyncIteratorBinding(
					loopBody.slice(1, conditionalAdvanceIndex),
					initialResult.name,
				);
				const protocolNames = new Set([
					iteratorDeclaration.name,
					initialResult.name,
					firstNext.name,
					advance.nextName,
					...continuation.protocolNames,
				]);
				if (
					!statementListReferencesAnyName(
						binding.body,
						protocolNames,
					) &&
					!statementListReferencesAnyName(
						continuation.body,
						protocolNames,
					)
				) {
					binding.body.push(t.ifStatement(
						invertCondition(advance.test),
						t.breakStatement(),
					));
					const forAwait = t.forOfStatement(
						binding.left,
						t.cloneNode(source, true),
						t.blockStatement(binding.body),
						true,
					) as LiftedAST<t.ForOfStatement>;
					forAwait.extra = {
						...forAwait.extra,
						recoveredAsyncIteratorNames: [
							iteratorDeclaration.name,
						],
					};
					const createThisConstructor = createThisForNewConstructor(
						statements[start - 1],
					);
					const replacementStart = createThisConstructor &&
							expressionContainsNewConstructor(
								source,
								createThisConstructor,
							)
						? start - 1
						: start;
					statements.splice(
						replacementStart,
						loopIndex - replacementStart + 1,
						...initial.slice(2, -1),
						forAwait,
						...continuation.body.map((statement) =>
							t.cloneNode(statement, true)
						),
					);
					changed = true;
					start = replacementStart - 1;
					continue;
				}
			}
		}
		const nextDeclaration = singleVariableIdentifierInit(
			loopBody.at(-3),
		);
		if (
			!nextDeclaration ||
			!memberCallOnIdentifier(
				nextDeclaration.init,
				iteratorDeclaration.name,
				'next',
			) ||
			!isEnsureObjectStatement(loopBody.at(-2), nextDeclaration.name)
		) continue;
		const nextResult = awaitedIdentifierAssignment(
			loopBody.at(-1),
			nextDeclaration.name,
		);
		if (!nextResult || nextResult.name !== initialResult.name) continue;

		const binding = extractAsyncIteratorBinding(
			loopBody.slice(1, -3),
			initialResult.name,
		);
		if (
			statementListReferencesAnyName(
				binding.body,
				new Set([
					initialResult.name,
					firstNext.name,
					nextDeclaration.name,
				]),
			)
		) continue;
		const forAwait = t.forOfStatement(
			binding.left,
			t.cloneNode(source, true),
			t.blockStatement(binding.body),
			true,
		) as LiftedAST<t.ForOfStatement>;
		forAwait.extra = {
			...forAwait.extra,
			recoveredAsyncIteratorNames: [iteratorDeclaration.name],
		};
		const createThisConstructor = createThisForNewConstructor(
			statements[start - 1],
		);
		const replacementStart = createThisConstructor &&
				expressionContainsNewConstructor(source, createThisConstructor)
			? start - 1
			: start;
		statements.splice(
			replacementStart,
			loopIndex - replacementStart + 1,
			...initial.slice(2, -1),
			forAwait,
		);
		changed = true;
		start = replacementStart - 1;
	}
	return changed;
}

function recoveredForOfIteratorNames(
	statement: t.Statement,
): string[] {
	if (!t.isForOfStatement(statement)) return [];
	return (statement as LiftedAST<t.ForOfStatement>).extra
		?.recoveredIteratorNames ?? [];
}

function iteratorCloseRethrowHandler(
	handler: t.CatchClause,
	iteratorNames: ReadonlySet<string>,
): boolean {
	if (!t.isIdentifier(handler.param)) return false;
	const body = handler.body.body;
	return body.length === 2 &&
		isIteratorCloseForNames(body[0], [...iteratorNames]) &&
		t.isThrowStatement(body[1]) &&
		t.isIdentifier(body[1].argument, { name: handler.param.name });
}
function singleStepIteratorBody(
	statement: t.Statement | undefined,
	nextIteratorName: string,
): t.Statement[] | null {
	if (
		!t.isIfStatement(statement) ||
		statement.alternate ||
		!t.isBlockStatement(statement.consequent) ||
		!isDefinedCheck(statement.test, nextIteratorName)
	) return null;
	let body = statement.consequent.body;
	if (
		body.length === 1 &&
		t.isTryStatement(body[0]) &&
		!body[0].handler &&
		body[0].finalizer?.body.length === 0
	) body = body[0].block.body;
	return statementListEndsAbruptly(body) ? body : null;
}

function statementListEndsFunctionAbruptly(stmts: t.Statement[]): boolean {
	const last = stmts.at(-1);
	if (!last) return false;
	if (t.isReturnStatement(last) || t.isThrowStatement(last)) return true;
	if (t.isIfStatement(last)) {
		const consequent = t.isBlockStatement(last.consequent)
			? last.consequent.body
			: [last.consequent];
		const alternate = last.alternate
			? (t.isBlockStatement(last.alternate)
				? last.alternate.body
				: [last.alternate])
			: [];
		return alternate.length > 0 &&
			statementListEndsFunctionAbruptly(consequent) &&
			statementListEndsFunctionAbruptly(alternate);
	}
	if (t.isTryStatement(last)) {
		return statementListEndsFunctionAbruptly(last.block.body);
	}
	if (t.isSwitchStatement(last)) {
		return last.cases.length > 0 &&
			last.cases.every((c) =>
				statementListEndsFunctionAbruptly(c.consequent)
			);
	}
	return false;
}

function singleStepIteratorAlternateBody(
	statement: t.Statement | undefined,
	nextIteratorName: string,
): { valueBody: t.Statement[]; emptyBody: t.Statement[] } | null {
	if (
		!t.isIfStatement(statement) ||
		!t.isBlockStatement(statement.consequent) ||
		!t.isBlockStatement(statement.alternate) ||
		!isUndefinedCheck(statement.test, nextIteratorName)
	) return null;
	let valueBody = statement.alternate.body;
	if (
		valueBody.length === 1 &&
		t.isTryStatement(valueBody[0]) &&
		!valueBody[0].handler &&
		valueBody[0].finalizer?.body.length === 0
	) valueBody = valueBody[0].block.body;
	if (!statementListEndsFunctionAbruptly(valueBody)) return null;
	return {
		valueBody,
		emptyBody: statement.consequent.body,
	};
}

function cleanupLocalIteratorForOfLoopsInBody(
	stmts: t.Statement[],
): { changed: boolean; iteratorNames: Set<string> } {
	let changed = false;
	const iteratorNames = new Set<string>();

	for (let index = 0; index < stmts.length; index++) {
		const statement = stmts[index];
		for (const name of recoveredForOfIteratorNames(statement)) {
			iteratorNames.add(name);
		}
		if (t.isTryStatement(statement)) {
			const protectedResult = cleanupLocalIteratorForOfLoopsInBody(
				statement.block.body,
			);
			changed = protectedResult.changed || changed;
			if (statement.handler) {
				const catchResult = cleanupLocalIteratorForOfLoopsInBody(
					statement.handler.body.body,
				);
				changed = catchResult.changed || changed;
			}
			if (statement.finalizer) {
				const finalizerResult = cleanupLocalIteratorForOfLoopsInBody(
					statement.finalizer.body,
				);
				changed = finalizerResult.changed || changed;
			}
			if (
				!statement.finalizer && statement.handler &&
				protectedResult.iteratorNames.size > 0 &&
				iteratorCloseRethrowHandler(
					statement.handler,
					protectedResult.iteratorNames,
				)
			) {
				stmts.splice(index, 1, ...statement.block.body);
				for (const name of protectedResult.iteratorNames) {
					iteratorNames.add(name);
				}
				changed = true;
				index--;
			}
			continue;
		}
		const nestedBody = t.isBlockStatement(statement)
			? statement.body
			: (t.isWhileStatement(statement) ||
					t.isForStatement(statement) ||
					t.isForInStatement(statement) ||
					t.isForOfStatement(statement) ||
					t.isDoWhileStatement(statement)) &&
					t.isBlockStatement(statement.body)
			? statement.body.body
			: null;
		if (nestedBody) {
			const nested = cleanupLocalIteratorForOfLoopsInBody(nestedBody);
			changed = nested.changed || changed;
			for (const name of nested.iteratorNames) iteratorNames.add(name);
		}
	}

	for (let beginIndex = 0; beginIndex < stmts.length - 1; beginIndex++) {
		const begin = getMultiIntrinsicDecl(
			stmts[beginIndex],
			'IteratorBegin',
		);
		if (
			!begin || begin.destinations.length !== 2 ||
			begin.call.arguments.length !== 1
		) continue;
		const [beginIterator, beginSourceOrNext] = begin.destinations;
		const [iterable] = begin.call.arguments;
		if (!t.isExpression(iterable)) continue;

		const aliases = new Map<string, string>();
		const consumedSetupNames = new Set<string>();
		let loopIndex = beginIndex + 1;
		for (; loopIndex < stmts.length; loopIndex++) {
			if (t.isWhileStatement(stmts[loopIndex])) break;
			const alias = expressionStatementAssignsIdentifierAlias(
				stmts[loopIndex],
			) ?? (() => {
				const declaration = getSingleIdentifierInit(stmts[loopIndex]);
				return declaration
					? {
						name: declaration.name,
						init: t.identifier(declaration.init),
					}
					: undefined;
			})();
			if (!alias || !t.isIdentifier(alias.init)) break;
			const root = resolveIdentifierAlias(alias.init.name, aliases);
			if (
				root !== beginIterator.name &&
				root !== beginSourceOrNext.name
			) break;
			aliases.set(alias.name, root);
			consumedSetupNames.add(alias.name);
		}
		const loop = stmts[loopIndex];
		if (
			!t.isWhileStatement(loop) ||
			!t.isBooleanLiteral(loop.test, { value: true }) ||
			!t.isBlockStatement(loop.body)
		) continue;
		const loopBody = loop.body.body;
		const next = getMultiIntrinsicDecl(loopBody[0], 'IteratorNext');
		if (
			!next || next.destinations.length !== 2 ||
			next.call.arguments.length !== 2
		) continue;
		const [value, nextIterator] = next.destinations;
		const [iteratorArg, sourceOrNextArg] = next.call.arguments;
		if (
			!t.isIdentifier(iteratorArg) ||
			!t.isIdentifier(sourceOrNextArg) ||
			resolveIdentifierAlias(iteratorArg.name, aliases) !==
				beginIterator.name ||
			resolveIdentifierAlias(sourceOrNextArg.name, aliases) !==
				beginSourceOrNext.name
		) continue;

		let cursor = 1;
		const update = expressionStatementAssignsIdentifierAlias(
			loopBody[cursor],
		);
		if (
			!update || !t.isIdentifier(update.init, {
				name: nextIterator.name,
			}) ||
			resolveIdentifierAlias(update.name, aliases) !==
				beginIterator.name
		) continue;
		consumedSetupNames.add(update.name);
		cursor++;
		if (!isIteratorDoneBreak(loopBody[cursor], nextIterator.name)) {
			continue;
		}

		const forBody = loopBody.slice(cursor + 1).map((statement) =>
			t.cloneNode(statement, true)
		);
		const left = extractLoopBinding(forBody, value.name) ??
			t.variableDeclaration('const', [
				t.variableDeclarator(t.identifier(value.name)),
			]);
		const consumedNames = new Set([
			beginIterator.name,
			beginSourceOrNext.name,
			nextIterator.name,
			...consumedSetupNames,
		]);
		const forOf = t.forOfStatement(
			left,
			t.cloneNode(iterable, true),
			t.blockStatement(forBody),
		) as LiftedAST<t.ForOfStatement>;
		forOf.extra = {
			...forOf.extra,
			recoveredIteratorNames: [...consumedNames],
		};
		stmts.splice(beginIndex, loopIndex - beginIndex + 1, forOf);
		for (const name of consumedNames) iteratorNames.add(name);
		changed = true;
	}

	return { changed, iteratorNames };
}

function cleanupLocalTerminalIteratorForOfLoopsInBody(
	stmts: t.Statement[],
): boolean {
	let changed = false;
	for (let beginIndex = 0; beginIndex < stmts.length - 2; beginIndex++) {
		const begin = getMultiIntrinsicDecl(
			stmts[beginIndex],
			'IteratorBegin',
		);
		if (
			!begin || begin.destinations.length !== 2 ||
			begin.call.arguments.length !== 1
		) continue;
		const next = getMultiIntrinsicDecl(
			stmts[beginIndex + 1],
			'IteratorNext',
		);
		if (
			!next || next.destinations.length !== 2 ||
			next.call.arguments.length !== 2
		) continue;
		const [beginIterator, beginSourceOrNext] = begin.destinations;
		const [iteratorArg, sourceOrNextArg] = next.call.arguments;
		if (
			!t.isIdentifier(iteratorArg, { name: beginIterator.name }) ||
			!t.isIdentifier(sourceOrNextArg, {
				name: beginSourceOrNext.name,
			})
		) continue;
		const [value, nextIterator] = next.destinations;
		const body = singleStepIteratorBody(
			stmts[beginIndex + 2],
			nextIterator.name,
		);
		const alternate = body ? null : singleStepIteratorAlternateBody(
			stmts[beginIndex + 2],
			nextIterator.name,
		);
		if (!body && !alternate) continue;
		const consumedNames = new Set([
			beginIterator.name,
			beginSourceOrNext.name,
			nextIterator.name,
		]);
		const valueBody = body ?? alternate!.valueBody;
		if (statementListReferencesAnyName(valueBody, consumedNames)) {
			continue;
		}
		const emptyBody = alternate?.emptyBody ?? [];
		if (statementListReferencesAnyName(emptyBody, consumedNames)) {
			continue;
		}
		const [iterable] = begin.call.arguments;
		if (!t.isExpression(iterable)) continue;
		const forOf = t.forOfStatement(
			t.variableDeclaration('const', [
				t.variableDeclarator(t.identifier(value.name)),
			]),
			t.cloneNode(iterable, true),
			t.blockStatement(
				valueBody.map((statement) => t.cloneNode(statement, true)),
			),
		) as LiftedAST<t.ForOfStatement>;
		forOf.extra = {
			...forOf.extra,
			recoveredIteratorNames: [...consumedNames],
		};
		stmts.splice(
			beginIndex,
			3,
			forOf,
			...emptyBody.map((statement) => t.cloneNode(statement, true)),
		);
		changed = true;
	}
	return changed;
}

export function cleanupLocalSyncIteratorForOfLoops(
	stmts: t.Statement[],
): boolean {
	return rewriteStructuredStatementLists(
		stmts,
		(body) => {
			const terminalChanged =
				cleanupLocalTerminalIteratorForOfLoopsInBody(body);
			const structuredChanged =
				cleanupLocalIteratorForOfLoopsInBody(body).changed;
			return terminalChanged || structuredChanged;
		},
	);
}

export function cleanupLocalIteratorForOfLoops(
	stmts: t.Statement[],
): boolean {
	const asyncChanged = cleanupLocalAsyncIteratorForOfLoopsInBody(stmts);
	const syncChanged = cleanupLocalIteratorForOfLoopsInBody(stmts).changed;
	return asyncChanged || syncChanged;
}

function cleanupLocalPNameForInLoopsInBody(stmts: t.Statement[]): boolean {
	for (let i = 0; i < stmts.length - 1; i++) {
		const listDecl = getMultiIntrinsicDecl(stmts[i], 'GetPNameList');
		if (
			!listDecl ||
			listDecl.destinations.length !== 3 ||
			listDecl.call.arguments.length !== 1
		) continue;
		const [listId, indexId] = listDecl.destinations;
		const [source] = listDecl.call.arguments;
		if (!t.isExpression(source)) continue;

		const pNameNames = new Set(listDecl.destinations.map((id) => id.name));
		let guardIndex = -1;
		let guardInfo:
			| ReturnType<typeof pNameListSemanticGuard>
			| null = null;
		let ordinarySetupCount = 0;
		for (let j = i + 1; j < stmts.length; j++) {
			guardInfo = pNameListSemanticGuard(stmts[j], listId.name);
			if (guardInfo) {
				guardIndex = j;
				break;
			}
			if (isSyntheticPhiPlumbing(stmts[j])) continue;
			if (statementReferencesAnyName(stmts[j], pNameNames)) break;
			if (++ordinarySetupCount >= 5) break;
		}
		if (!guardInfo) continue;
		const preservedSetup = stmts.slice(i + 1, guardIndex)
			.filter((stmt) => !isSyntheticPhiPlumbing(stmt))
			.map((stmt) => t.cloneNode(stmt, true));
		const guardBody = guardInfo.body;
		const whileIndex = guardBody.findIndex((stmt) =>
			t.isWhileStatement(stmt) &&
			t.isBooleanLiteral(stmt.test, { value: true }) &&
			t.isBlockStatement(stmt.body)
		);
		if (whileIndex < 0) continue;
		const loopSetup = guardBody.slice(0, whileIndex);
		const loopAliases = new Map<string, string>();
		const protocolRoots = new Set(pNameNames);
		if (t.isIdentifier(source)) protocolRoots.add(source.name);
		const droppableLoopSetup = new Set<t.Statement>();
		let validLoopSetup = true;
		for (const statement of loopSetup) {
			if (isUninitializedGeneratedLet(statement)) continue;
			const declaration = getSingleIdentifierInit(statement);
			const assignment = expressionStatementAssignsIdentifierAlias(
				statement,
			);
			const alias = declaration ??
				(assignment && t.isIdentifier(assignment.init)
					? { name: assignment.name, init: assignment.init.name }
					: undefined);
			if (alias && isGeneratedRegisterName(alias.name)) {
				const root = resolveIdentifierAlias(alias.init, loopAliases);
				if (protocolRoots.has(root)) {
					loopAliases.set(alias.name, root);
					droppableLoopSetup.add(statement);
					continue;
				}
			}
			if (isSyntheticPhiPlumbing(statement)) {
				droppableLoopSetup.add(statement);
				continue;
			}
			validLoopSetup = false;
			break;
		}
		if (!validLoopSetup) continue;

		const loop = guardBody[whileIndex] as t.WhileStatement;
		if (!t.isBlockStatement(loop.body)) continue;
		const loopBody = loop.body.body;
		const nextIndex = loopBody.findIndex((stmt) => {
			const next = getMultiIntrinsicDecl(stmt, 'GetNextPName');
			if (
				!next ||
				next.destinations.length !== 2 ||
				next.call.arguments.length !== 3
			) return false;
			const list = next.call.arguments[0];
			const index = next.call.arguments[2];
			return t.isIdentifier(list) &&
				resolveIdentifierAlias(list.name, loopAliases) ===
					listId.name &&
				t.isIdentifier(index) &&
				resolveIdentifierAlias(index.name, loopAliases) ===
					indexId.name;
		});
		if (nextIndex < 0) continue;
		const next = getMultiIntrinsicDecl(
			loopBody[nextIndex],
			'GetNextPName',
		)!;
		const [keyId, nextIndexId] = next.destinations;
		if (!isIteratorDoneBreak(loopBody[nextIndex + 1], keyId.name)) {
			continue;
		}

		const protocolNames = new Set([
			...protocolRoots,
			...loopAliases.keys(),
			nextIndexId.name,
			keyId.name,
		]);
		let bodyStart = nextIndex + 2;
		while (bodyStart < loopBody.length) {
			const statement = loopBody[bodyStart];
			if (isSyntheticPhiPlumbing(statement)) {
				bodyStart++;
				continue;
			}
			const assignment = expressionStatementAssignsIdentifierAlias(
				statement,
			);
			if (
				!assignment ||
				!protocolNames.has(assignment.name) ||
				!t.isIdentifier(assignment.init) ||
				!protocolNames.has(assignment.init.name)
			) break;
			bodyStart++;
		}
		const preservedLoopSetup = loopSetup
			.filter((statement) => {
				if (droppableLoopSetup.has(statement)) return false;
				if (!t.isVariableDeclaration(statement)) return true;
				return !statement.declarations.every((declaration) =>
					t.isIdentifier(declaration.id) &&
					protocolNames.has(declaration.id.name)
				);
			})
			.map((statement) => t.cloneNode(statement, true));
		const forBody = [
			...loopBody.slice(0, nextIndex),
			...loopBody.slice(bodyStart),
		].filter((stmt) => !isSyntheticPhiPlumbing(stmt))
			.map((stmt) => t.cloneNode(stmt, true));
		const forIn = t.forInStatement(
			t.variableDeclaration('const', [
				t.variableDeclarator(t.identifier(keyId.name)),
			]),
			t.cloneNode(source, true),
			t.blockStatement(forBody),
		);
		forIn.extra = { ...forIn.extra, fromCFGLoop: true };

		const trailing = guardBody.slice(whileIndex + 1)
			.filter((stmt) => !isSyntheticPhiPlumbing(stmt))
			.map((stmt) => t.cloneNode(stmt, true));
		if (guardInfo.test) {
			stmts.splice(
				i,
				guardIndex - i + 1,
				...preservedSetup,
				t.ifStatement(
					guardInfo.test,
					t.blockStatement([
						...preservedLoopSetup,
						forIn,
						...trailing,
					]),
				),
			);
		} else {
			stmts.splice(
				i,
				guardIndex - i + 1,
				...preservedSetup,
				...preservedLoopSetup,
				forIn,
				...trailing,
			);
		}
		return true;
	}

	for (const stmt of stmts) {
		if (
			t.isBlockStatement(stmt) &&
			cleanupLocalPNameForInLoopsInBody(stmt.body)
		) return true;
		if (t.isIfStatement(stmt)) {
			if (
				t.isBlockStatement(stmt.consequent) &&
				cleanupLocalPNameForInLoopsInBody(stmt.consequent.body)
			) return true;
			if (
				t.isBlockStatement(stmt.alternate) &&
				cleanupLocalPNameForInLoopsInBody(stmt.alternate.body)
			) return true;
		}
		if (t.isWhileStatement(stmt) && t.isBlockStatement(stmt.body)) {
			if (cleanupLocalPNameForInLoopsInBody(stmt.body.body)) return true;
		}
		if (t.isTryStatement(stmt)) {
			if (cleanupLocalPNameForInLoopsInBody(stmt.block.body)) return true;
			if (
				stmt.handler &&
				cleanupLocalPNameForInLoopsInBody(stmt.handler.body.body)
			) return true;
			if (
				stmt.finalizer &&
				cleanupLocalPNameForInLoopsInBody(stmt.finalizer.body)
			) return true;
		}
	}
	return false;
}

export function cleanupLocalPNameForInLoops(stmts: t.Statement[]): boolean {
	return cleanupLocalPNameForInLoopsInBody(stmts);
}
