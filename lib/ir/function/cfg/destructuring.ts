import { env } from 'node:process';
import * as t from '@babel/types';
import traverse, { type NodePath } from '@babel/traverse';
import type { IRFunction } from '../mod.ts';
import type { IRBlock, LiftedAST } from '../../ast/mod.ts';
import { comparableAst, isUndefinedNode } from '../../ast/utils.ts';
import { statementListEndsAbruptly } from '../../ast/completion.ts';
import { locationKey, locationOf } from '../../ast/alias.ts';
import { rewriteStructuredStatementLists } from '../../ast/statementLists.ts';
import {
	consumedDefinitionsAreDead,
	expressionStatementAssignment,
} from './consumed.ts';
import { invertTest } from '../../ast/expression.ts';
import { AddressMap } from '../../../utils/map.ts';

let DEBUG_OBJ_DESTR = false;
try {
	DEBUG_OBJ_DESTR = env['ARES_DEBUG_OBJ_DESTR'] === '1';
} catch { /**/ }
function debugObjDestr(...args: unknown[]) {
	if (DEBUG_OBJ_DESTR) console.error('[obj-destr]', ...args);
}
let DEBUG_ARRAY_DESTR = false;
try {
	DEBUG_ARRAY_DESTR = env['ARES_DEBUG_ARRAY_DESTR'] === '1';
} catch { /**/ }
function debugArrayDestr(...args: unknown[]) {
	if (DEBUG_ARRAY_DESTR) console.error('[array-destr]', ...args);
}

function singleDeclarator(
	stmt: t.Statement | undefined,
	kind?: 'var' | 'let' | 'const',
): t.VariableDeclarator | null {
	if (!stmt || !t.isVariableDeclaration(stmt)) return null;
	if (kind && stmt.kind !== kind) return null;
	if (stmt.declarations.length !== 1) return null;
	return stmt.declarations[0];
}

function assignmentToTarget(
	stmt: t.Statement | undefined,
	target: t.Expression,
): t.AssignmentExpression | null {
	const assign = expressionStatementAssignment(stmt);
	if (!assign) return null;
	if (!t.isExpression(assign.left)) return null;
	if (!expressionsEqual(assign.left, target)) return null;
	return assign;
}

function assignmentToIdentifier(
	stmt: t.Statement | undefined,
	name: string,
): t.AssignmentExpression | null {
	const assign = expressionStatementAssignment(stmt);
	if (!assign || !t.isIdentifier(assign.left, { name })) return null;
	return assign;
}

function singleAssignmentInBlock(
	stmt: t.Statement | undefined,
	name: string,
): t.AssignmentExpression | null {
	if (!stmt || !t.isBlockStatement(stmt)) return null;
	const matches = stmt.body.flatMap((child) => {
		const assign = assignmentToIdentifier(child, name);
		return assign ? [assign] : [];
	});
	return matches.length === 1 ? matches[0] : null;
}

function isGeneratedName(name: string) {
	return /^(?:r\d+_\d+|e_\d+)$/.test(name);
}

function isDroppableDefaultInit(expr: t.Expression): boolean {
	if (
		t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, { name: 'Phi' })
	) return true;

	return t.isIdentifier(expr) ||
		t.isThisExpression(expr) ||
		t.isNullLiteral(expr) ||
		t.isStringLiteral(expr) ||
		t.isNumericLiteral(expr) ||
		t.isBooleanLiteral(expr) ||
		t.isBigIntLiteral(expr) ||
		(t.isUnaryExpression(expr) &&
			t.isExpression(expr.argument) &&
			expr.operator !== 'delete' &&
			isDroppableDefaultInit(expr.argument));
}

function countIdentifierUses(node: t.Node, name: string): number {
	if (t.isIdentifier(node, { name })) return 1;
	let count = 0;
	for (const key of t.VISITOR_KEYS[node.type] ?? []) {
		const child = node[key as keyof typeof node];
		if (Array.isArray(child)) {
			for (const element of child) {
				if (t.isNode(element)) {
					count += countIdentifierUses(element, name);
				}
			}
		} else if (t.isNode(child)) {
			count += countIdentifierUses(child, name);
		}
	}
	return count;
}

function generatedWrite(
	stmt: t.Statement,
): { name: string; value: t.Expression } | null {
	const decl = singleDeclarator(stmt);
	if (
		decl &&
		t.isIdentifier(decl.id) &&
		isGeneratedName(decl.id.name) &&
		t.isExpression(decl.init)
	) return { name: decl.id.name, value: decl.init };

	const assign = expressionStatementAssignment(stmt);
	if (
		assign &&
		t.isIdentifier(assign.left) &&
		isGeneratedName(assign.left.name) &&
		t.isExpression(assign.right)
	) return { name: assign.left.name, value: assign.right };

	return null;
}

function replaceIdentifierUse(
	node: t.Node,
	name: string,
	replacement: t.Expression,
): t.Node {
	if (t.isIdentifier(node, { name })) {
		return t.cloneNode(replacement, true);
	}

	const clone = t.cloneNode(node, false);
	for (const key of t.VISITOR_KEYS[clone.type] ?? []) {
		const child = clone[key as keyof typeof clone];
		if (Array.isArray(child)) {
			(clone as unknown as Record<string, unknown>)[key] = child.map((
				element,
			) => t.isNode(element)
				? replaceIdentifierUse(element, name, replacement)
				: element
			);
		} else if (t.isNode(child)) {
			(clone as unknown as Record<string, unknown>)[key] =
				replaceIdentifierUse(child, name, replacement);
		}
	}
	return clone;
}

function defaultAssignmentInBlock(
	stmt: t.Statement | undefined,
	name: string,
): { assign: t.AssignmentExpression; value: t.Expression } | null {
	if (!stmt || !t.isBlockStatement(stmt)) return null;
	if (stmt.body.length === 0) return null;

	const targetAssignments = stmt.body.flatMap((child, index) => {
		const assign = assignmentToIdentifier(child, name);
		return assign ? [{ assign, index }] : [];
	});
	if (targetAssignments.length !== 1) return null;
	const [{ assign: final, index: finalIndex }] = targetAssignments;
	if (!t.isExpression(final.right)) return null;

	let value = t.cloneNode(final.right, true) as t.Expression;
	for (let i = stmt.body.length - 1; i >= 0; i--) {
		if (i === finalIndex) continue;
		const write = generatedWrite(stmt.body[i]);
		if (!write || write.name === name) return null;

		const uses = countIdentifierUses(value, write.name);
		if (uses === 0) {
			if (!isDroppableDefaultInit(write.value)) return null;
			continue;
		}
		if (uses !== 1) return null;
		value = replaceIdentifierUse(
			value,
			write.name,
			write.value,
		) as t.Expression;
	}

	return { assign: final, value };
}

function expressionsEqual(left: t.Expression, right: t.Expression): boolean {
	return JSON.stringify(comparableAst(left)) ===
		JSON.stringify(comparableAst(right));
}

function getUndefinedCheckName(expr: t.Expression): string | null {
	if (!t.isBinaryExpression(expr, { operator: '===' })) return null;
	if (t.isIdentifier(expr.left) && isUndefinedNode(expr.right)) {
		return expr.left.name;
	}
	if (isUndefinedNode(expr.left) && t.isIdentifier(expr.right)) {
		return expr.right.name;
	}
	return null;
}

function intrinsicArrayDecl(
	stmt: t.Statement | undefined,
	name: string,
): { ids: t.Identifier[]; args: t.Expression[] } | null {
	const decl = singleDeclarator(stmt, 'const');
	if (!decl || !t.isArrayPattern(decl.id)) return null;
	const ids = decl.id.elements;
	if (!ids.every((element) => t.isIdentifier(element))) return null;
	if (!t.isCallExpression(decl.init)) return null;
	if (!t.isV8IntrinsicIdentifier(decl.init.callee, { name })) return null;
	if (!decl.init.arguments.every((arg) => t.isExpression(arg))) return null;
	return {
		ids: ids as t.Identifier[],
		args: decl.init.arguments as t.Expression[],
	};
}

function destructuringAssignmentTarget(
	stmt: t.Statement | undefined,
	initName: string,
	globalNames: Set<string>,
): { target: TargetPlan; name?: string } | null {
	const assign = expressionStatementAssignment(stmt);
	if (!assign || !t.isIdentifier(assign.right, { name: initName })) {
		return null;
	}
	if (!t.isLVal(assign.left)) return null;

	if (t.isIdentifier(assign.left)) {
		return {
			target: bindingTarget(assign.left.name, false),
			name: assign.left.name,
		};
	}

	if (
		t.isMemberExpression(assign.left, { computed: false }) &&
		t.isIdentifier(assign.left.object) &&
		globalNames.has(assign.left.object.name) &&
		t.isIdentifier(assign.left.property)
	) {
		return {
			target: bindingTarget(assign.left.property.name, true),
			name: assign.left.property.name,
		};
	}

	if (t.isMemberExpression(assign.left)) {
		return {
			target: {
				kind: 'assign',
				lval: t.cloneNode(assign.left, true) as t.LVal,
			},
		};
	}

	return null;
}

function collectGlobalNames(body: t.Statement[]) {
	const names = new Set(['global']);
	let changed = true;
	while (changed) {
		changed = false;
		for (const stmt of body) {
			const decl = singleDeclarator(stmt, 'const');
			if (!decl || !t.isIdentifier(decl.id)) continue;
			if (!t.isIdentifier(decl.init) || !names.has(decl.init.name)) {
				continue;
			}
			if (!names.has(decl.id.name)) {
				names.add(decl.id.name);
				changed = true;
			}
		}
	}
	return names;
}

function removeDeclaredGlobals(body: t.Statement[], names: Set<string>) {
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (!t.isVariableDeclaration(stmt, { kind: 'var' })) continue;
		const before = stmt.declarations.length;
		stmt.declarations = stmt.declarations.filter((decl) =>
			!(
				t.isIdentifier(decl.id) &&
				names.has(decl.id.name) &&
				decl.extra?.isDeclaredGlobal
			)
		);
		if (stmt.declarations.length === 0) {
			body.splice(i, 1);
			i--;
		} else if (stmt.declarations.length !== before) {
			return;
		}
	}
}

type TargetPlan =
	| { kind: 'binding'; id: t.Identifier; declaredGlobal: boolean }
	| { kind: 'assign'; lval: t.LVal };

type PatternPlan =
	| { kind: 'target'; target: TargetPlan; defaultValue?: t.Expression }
	| { kind: 'array'; pattern: t.ArrayPattern; defaultValue?: t.Expression }
	| { kind: 'object'; pattern: t.ObjectPattern; defaultValue?: t.Expression };

type AssignmentPatternLeft = Parameters<typeof t.assignmentPattern>[0];
type RestElementArgument = Parameters<typeof t.restElement>[0];

type DestructuringPlan = {
	pattern: t.ArrayPattern | t.ObjectPattern;
	source: t.Expression;
	declaredGlobals: Set<string>;
	consumed: t.Statement[];
	preservedInputs: t.Node[];
	inlineConsumedResults: t.Node[];
};

function bindingTarget(name: string, declaredGlobal: boolean): TargetPlan {
	return {
		kind: 'binding',
		id: t.identifier(name),
		declaredGlobal,
	};
}

function targetToPattern(target: TargetPlan): t.PatternLike {
	return target.kind === 'binding'
		? t.cloneNode(target.id, true)
		: t.cloneNode(target.lval, true) as unknown as t.PatternLike;
}

function planToPattern(plan: PatternPlan): t.PatternLike {
	let pattern: t.PatternLike;
	if (plan.kind === 'target') {
		pattern = targetToPattern(plan.target);
	} else {
		pattern = t.cloneNode(plan.pattern, true);
	}

	if (!plan.defaultValue) return pattern;
	return t.assignmentPattern(
		pattern as unknown as AssignmentPatternLeft,
		t.cloneNode(plan.defaultValue, true) as t.Expression,
	);
}

function patternHasAssignmentOnlyTargets(pattern: t.Node): boolean {
	if (t.isMemberExpression(pattern)) return true;
	if (t.isRestElement(pattern)) {
		return patternHasAssignmentOnlyTargets(pattern.argument);
	}
	if (t.isAssignmentPattern(pattern)) {
		return patternHasAssignmentOnlyTargets(pattern.left);
	}
	if (t.isArrayPattern(pattern)) {
		return pattern.elements.some((element) =>
			!!element && patternHasAssignmentOnlyTargets(element)
		);
	}
	if (t.isObjectPattern(pattern)) {
		return pattern.properties.some((property) =>
			t.isRestElement(property)
				? patternHasAssignmentOnlyTargets(property.argument)
				: patternHasAssignmentOnlyTargets(property.value)
		);
	}
	return false;
}

function emitDestructuringPlan(plan: DestructuringPlan): t.Statement {
	const pattern = t.cloneNode(plan.pattern, true);
	if (patternHasAssignmentOnlyTargets(pattern)) {
		const stmt = t.expressionStatement(
			t.assignmentExpression(
				'=',
				pattern as unknown as t.LVal,
				t.cloneNode(plan.source, true) as t.Expression,
			),
		);
		stmt.extra = { ...stmt.extra, fromDestructuring: true };
		return stmt;
	}

	const declarator = t.variableDeclarator(
		pattern,
		t.cloneNode(plan.source, true) as t.Expression,
	);
	if (plan.declaredGlobals.size > 0) {
		declarator.extra = { isDeclaredGlobal: true };
	}
	const stmt = t.variableDeclaration('var', [declarator]);
	stmt.extra = { ...stmt.extra, fromDestructuring: true };
	return stmt;
}

const EMPTY_OBJECT_DESTRUCTURING_ERROR =
	"Cannot destructure 'undefined' or 'null'.";

function nullishObjectGuard(
	test: t.Expression,
): { source: t.Identifier; nullishWhenTrue: boolean } | null {
	if (
		!t.isBinaryExpression(test) ||
		(test.operator !== '==' && test.operator !== '!=')
	) return null;
	const source = t.isIdentifier(test.left) && t.isNullLiteral(test.right)
		? test.left
		: t.isNullLiteral(test.left) && t.isIdentifier(test.right)
		? test.right
		: null;
	return source
		? {
			source: t.cloneNode(source),
			nullishWhenTrue: test.operator === '==',
		}
		: null;
}

function isEmptyObjectDestructuringThrow(
	statements: readonly t.Statement[],
	sourceName: string,
): boolean {
	if (statements.length !== 2) return false;
	const [callStatement, throwStatement] = statements;
	if (
		!callStatement || !t.isExpressionStatement(callStatement) ||
		!t.isCallExpression(callStatement.expression) ||
		!t.isMemberExpression(callStatement.expression.callee, {
			computed: false,
		}) ||
		!t.isIdentifier(callStatement.expression.callee.object, {
			name: 'HermesInternal',
		}) ||
		!t.isIdentifier(callStatement.expression.callee.property, {
			name: 'throwTypeError',
		})
	) return false;
	const [value, message] = callStatement.expression.arguments;
	return callStatement.expression.arguments.length === 2 &&
		t.isIdentifier(value, { name: sourceName }) &&
		t.isStringLiteral(message, {
			value: EMPTY_OBJECT_DESTRUCTURING_ERROR,
		}) &&
		!!throwStatement &&
		t.isThrowStatement(throwStatement) &&
		!!throwStatement.argument &&
		isUndefinedNode(throwStatement.argument);
}

type EmptyObjectGuardMatch = {
	source: t.Identifier;
	normal: t.Statement[];
	replacementNormal: t.Statement[];
	consumed: number;
};

function emptyObjectGuardAt(
	body: t.Statement[],
	index: number,
): EmptyObjectGuardMatch | null {
	const statement = body[index];
	if (!statement || !t.isIfStatement(statement)) return null;
	const guard = nullishObjectGuard(statement.test);
	if (!guard) return null;
	const consequent = t.isBlockStatement(statement.consequent)
		? statement.consequent.body
		: [statement.consequent];
	const alternate = statement.alternate
		? t.isBlockStatement(statement.alternate)
			? statement.alternate.body
			: [statement.alternate]
		: null;

	if (
		guard.nullishWhenTrue &&
		isEmptyObjectDestructuringThrow(consequent, guard.source.name)
	) {
		return {
			source: guard.source,
			normal: alternate ?? body.slice(index + 1),
			replacementNormal: alternate ?? [],
			consumed: 1,
		};
	}
	if (
		!guard.nullishWhenTrue &&
		alternate &&
		isEmptyObjectDestructuringThrow(alternate, guard.source.name)
	) {
		return {
			source: guard.source,
			normal: consequent,
			replacementNormal: consequent,
			consumed: 1,
		};
	}
	if (
		!guard.nullishWhenTrue &&
		!alternate &&
		isEmptyObjectDestructuringThrow(
			body.slice(index + 1, index + 3),
			guard.source.name,
		)
	) {
		return {
			source: guard.source,
			normal: consequent,
			replacementNormal: consequent,
			consumed: 3,
		};
	}
	return null;
}

function markedZeroExclusionCopy(
	path: NodePath<t.ObjectExpression>,
	sourceName: string,
): boolean {
	const expression = path.node as LiftedAST<t.ObjectExpression>;
	if (
		expression.extra?.copyDataPropertiesSpread !== true ||
		expression.properties.length !== 1
	) return false;
	const [property] = expression.properties;
	return t.isSpreadElement(property) &&
		t.isIdentifier(property.argument, { name: sourceName });
}

function freshRestBinding(
	body: readonly t.Statement[],
	functionId: number,
	sourceName: string,
): t.Identifier {
	const names = new Set<string>();
	for (const statement of body) {
		t.traverseFast(statement, (node) => {
			if (t.isIdentifier(node)) names.add(node.name);
		});
	}
	const parameter = /^_param_\d+_(\d+)_$/.exec(sourceName);
	const suffix = parameter?.[1] ?? sourceName.replaceAll('$', '_');
	const base = `_rest_${functionId}_${suffix}_`;
	let name = base;
	for (let serial = 1; names.has(name); serial++) {
		name = `${base}${serial}`;
	}
	return t.identifier(name);
}

function recoverGuardedObjectDestructuringInList(
	body: t.Statement[],
	functionId: number,
): boolean {
	for (let index = 0; index < body.length; index++) {
		const match = emptyObjectGuardAt(body, index);
		if (!match) continue;

		const wrapped = t.file(t.program(match.normal));
		const copies: NodePath<t.ObjectExpression>[] = [];
		traverse(wrapped, {
			Function(path) {
				path.skip();
			},
			ObjectExpression(path) {
				if (markedZeroExclusionCopy(path, match.source.name)) {
					copies.push(path);
				}
			},
		});

		let pattern: t.ObjectPattern = t.objectPattern([]);
		if (copies.length === 1) {
			const rest = freshRestBinding(body, functionId, match.source.name);
			copies[0]!.replaceWith(t.cloneNode(rest));
			pattern = t.objectPattern([t.restElement(rest)]);
		}
		const recovered = emitDestructuringPlan({
			pattern,
			source: match.source,
			declaredGlobals: new Set(),
			consumed: [],
			preservedInputs: [],
			inlineConsumedResults: [],
		});
		body.splice(
			index,
			match.consumed,
			recovered,
			...match.replacementNormal,
		);
		return true;
	}
	return false;
}

/**
 * Recover Hermes' explicit RequireObjectCoercible guard when the object
 * destructuring protocol has no named property probes. The exact builtin,
 * message, source, and trailing throw are required so ordinary user control
 * flow and genuine throwTypeError calls remain untouched.
 */
export function recoverGuardedObjectDestructuring(
	body: t.Statement[],
	functionId: number,
): boolean {
	return rewriteStructuredStatementLists(
		body,
		(statements) =>
			recoverGuardedObjectDestructuringInList(statements, functionId),
	);
}

function blockIteratorNextDecl(
	stmt: t.Statement | undefined,
	iteratorStateName: string,
) {
	if (!stmt || !t.isBlockStatement(stmt)) return null;
	for (const inner of stmt.body) {
		const next = intrinsicArrayDecl(inner, 'IteratorNext');
		if (
			next &&
			next.ids.length === 2 &&
			next.args.length === 2 &&
			t.isIdentifier(next.args[1], { name: iteratorStateName })
		) return next;
	}
	return null;
}

function statementContainsIteratorClose(stmt: t.Statement | undefined) {
	if (!stmt) return false;
	if (
		t.isExpressionStatement(stmt) &&
		t.isCallExpression(stmt.expression) &&
		t.isV8IntrinsicIdentifier(stmt.expression.callee, {
			name: 'IteratorClose',
		})
	) return true;
	if (t.isIfStatement(stmt) && t.isBlockStatement(stmt.consequent)) {
		return stmt.consequent.body.some(statementContainsIteratorClose);
	}
	return false;
}

function hasNonEmptyAlternate(stmt: t.IfStatement): boolean {
	return !!stmt.alternate &&
		(!t.isBlockStatement(stmt.alternate) ||
			stmt.alternate.body.length > 0);
}

function nextDefaultedArrayElement(
	body: t.Statement[],
	start: number,
	iteratorRecordName: string,
	globalNames: Set<string>,
) {
	for (let guardIndex = start; guardIndex < body.length - 1; guardIndex++) {
		if (statementContainsIteratorClose(body[guardIndex])) break;
		const guard = body[guardIndex];
		if (!t.isIfStatement(guard) || guard.alternate) continue;
		const next = blockIteratorNextDecl(
			guard.consequent,
			iteratorRecordName,
		);
		if (!next || next.ids.length !== 2) continue;

		for (
			let defaultIndex = guardIndex + 1;
			defaultIndex < body.length - 1;
			defaultIndex++
		) {
			if (statementContainsIteratorClose(body[defaultIndex])) break;
			const defaultBlock = body[defaultIndex];
			if (
				!t.isIfStatement(defaultBlock) ||
				defaultBlock.alternate ||
				!t.isBlockStatement(defaultBlock.consequent)
			) continue;

			for (
				let assignIndex = defaultIndex + 1;
				assignIndex < Math.min(body.length, defaultIndex + 3);
				assignIndex++
			) {
				const assign = expressionStatementAssignment(body[assignIndex]);
				if (!assign || !t.isIdentifier(assign.right)) continue;
				const defaultAssign = defaultAssignmentInBlock(
					defaultBlock.consequent,
					assign.right.name,
				);
				if (!defaultAssign) continue;
				const target = destructuringAssignmentTarget(
					body[assignIndex],
					assign.right.name,
					globalNames,
				);
				if (!target) continue;

				return {
					target: target.name,
					plan: {
						kind: 'target' as const,
						target: target.target,
						defaultValue: defaultAssign.value,
					},
					defaultValue: defaultAssign.value,
					end: assignIndex + 1,
					iteratorStateName: next.ids[1].name,
					declaredGlobal: target.target.kind === 'binding' &&
						target.target.declaredGlobal,
					intrinsic: 'IteratorNextWithDefault' as const,
				};
			}
		}
	}
	return null;
}

function isIteratorNotDoneCheck(
	expr: t.Expression,
	iteratorStateName: string,
): boolean {
	if (
		t.isBinaryExpression(expr, { operator: '!==' }) &&
		(
			(t.isIdentifier(expr.left, { name: iteratorStateName }) &&
				isUndefinedNode(expr.right)) ||
			(isUndefinedNode(expr.left) &&
				t.isIdentifier(expr.right, { name: iteratorStateName }))
		)
	) return true;
	return t.isUnaryExpression(expr, { operator: '!' }) &&
		t.isExpression(expr.argument) &&
		getUndefinedCheckName(expr.argument) === iteratorStateName;
}

function isRestCollectionGuard(
	expr: t.Expression,
	iteratorStateName: string,
): boolean {
	if (isIteratorNotDoneCheck(expr, iteratorStateName)) return true;
	return t.isUnaryExpression(expr, { operator: '!' }) &&
		t.isIdentifier(expr.argument);
}

function plainArrayElement(
	body: t.Statement[],
	start: number,
	valueName: string,
	iteratorStateName: string,
	globalNames: Set<string>,
	consumeFollowingAssignment = true,
) {
	const targetDecl = singleDeclarator(body[start], 'let');
	if (
		!targetDecl ||
		!t.isIdentifier(targetDecl.id) ||
		!isUndefinedNode(targetDecl.init)
	) return null;

	const guard = body[start + 1];
	if (
		!t.isIfStatement(guard) ||
		guard.alternate ||
		!t.isBlockStatement(guard.consequent) ||
		!isIteratorNotDoneCheck(guard.test, iteratorStateName)
	) return null;

	const assign = singleAssignmentInBlock(
		guard.consequent,
		targetDecl.id.name,
	);
	if (!assign || !t.isIdentifier(assign.right, { name: valueName })) {
		return null;
	}

	const target = consumeFollowingAssignment
		? destructuringAssignmentTarget(
			body[start + 2],
			targetDecl.id.name,
			globalNames,
		)
		: null;
	if (target) {
		return {
			target: target.name,
			plan: {
				kind: 'target' as const,
				target: target.target,
			},
			end: start + 3,
			declaredGlobal: target.target.kind === 'binding' &&
				target.target.declaredGlobal,
			intrinsic: 'IteratorNextValue' as const,
		};
	}

	return {
		target: targetDecl.id.name,
		plan: {
			kind: 'target' as const,
			target: bindingTarget(targetDecl.id.name, false),
		},
		end: start + 2,
		declaredGlobal: false,
		intrinsic: 'IteratorNextValue' as const,
	};
}

function emptyIteratorGuard(
	stmt: t.Statement | undefined,
	iteratorStateName: string,
) {
	return t.isIfStatement(stmt) &&
		!stmt.alternate &&
		t.isBlockStatement(stmt.consequent) &&
		stmt.consequent.body.length === 0 &&
		isIteratorNotDoneCheck(stmt.test, iteratorStateName);
}

function compactFirstArrayElement(
	body: t.Statement[],
	start: number,
	valueName: string,
	iteratorStateName: string,
) {
	if (!isGeneratedName(valueName)) return null;
	let end = start;
	if (emptyIteratorGuard(body[end], iteratorStateName)) end++;
	return {
		target: valueName,
		plan: {
			kind: 'target' as const,
			target: bindingTarget(valueName, false),
		},
		end,
		declaredGlobal: false,
		intrinsic: 'IteratorNextValue' as const,
	};
}

function elidedFirstThenPlainSecondElement(
	body: t.Statement[],
	start: number,
	firstIteratorStateName: string,
	iteratorRecordName: string,
): {
	element: DestructuringElement;
	end: number;
	iteratorStateName: string;
} | null {
	const doneDecl = singleDeclarator(body[start], 'let');
	if (
		!doneDecl ||
		!t.isIdentifier(doneDecl.id) ||
		getUndefinedCheckName(doneDecl.init as t.Expression) !==
			firstIteratorStateName
	) return null;
	const doneName = doneDecl.id.name;

	const targetDecl = singleDeclarator(body[start + 1], 'let');
	if (
		!targetDecl ||
		!t.isIdentifier(targetDecl.id) ||
		!isUndefinedNode(targetDecl.init)
	) return null;
	const targetName = targetDecl.id.name;

	const guard = body[start + 2];
	if (
		!t.isIfStatement(guard) ||
		guard.alternate ||
		!t.isBlockStatement(guard.consequent) ||
		!isIteratorNotDoneCheck(guard.test, firstIteratorStateName)
	) return null;
	const nested = guard.consequent.body;
	const next = intrinsicArrayDecl(nested[0], 'IteratorNext');
	if (
		!next ||
		next.ids.length !== 2 ||
		next.args.length !== 2 ||
		!t.isIdentifier(next.args[0], { name: firstIteratorStateName }) ||
		!t.isIdentifier(next.args[1], { name: iteratorRecordName })
	) return null;
	const [valueId, secondIteratorStateId] = next.ids;

	const resetAssign = assignmentToIdentifier(nested[1], targetName);
	if (!resetAssign || !isUndefinedNode(resetAssign.right)) return null;
	const doneAssign = assignmentToIdentifier(nested[2], doneName);
	if (
		!doneAssign ||
		getUndefinedCheckName(doneAssign.right as t.Expression) !==
			secondIteratorStateId.name
	) return null;

	const valueGuard = nested[3];
	if (
		!t.isIfStatement(valueGuard) ||
		valueGuard.alternate ||
		!t.isBlockStatement(valueGuard.consequent) ||
		!isIteratorNotDoneCheck(valueGuard.test, secondIteratorStateId.name)
	) return null;
	const valueAssign = assignmentToIdentifier(
		valueGuard.consequent.body[0],
		targetName,
	);
	if (
		!valueAssign ||
		!t.isIdentifier(valueAssign.right, { name: valueId.name })
	) return null;
	const nestedDoneAssign = assignmentToIdentifier(
		valueGuard.consequent.body[1],
		doneName,
	);
	if (
		!nestedDoneAssign ||
		getUndefinedCheckName(nestedDoneAssign.right as t.Expression) !==
			secondIteratorStateId.name
	) return null;

	return {
		element: {
			target: targetName,
			plan: {
				kind: 'target',
				target: bindingTarget(targetName, false),
			},
			declaredGlobal: false,
			intrinsic: 'IteratorNextValue',
		},
		end: start + 3,
		iteratorStateName: secondIteratorStateId.name,
	};
}

function firstDefaultedArrayElement(
	body: t.Statement[],
	start: number,
	valueName: string,
	iteratorStateName: string,
	globalNames: Set<string>,
) {
	const tempDecl = singleDeclarator(body[start], 'let');
	if (
		tempDecl &&
		t.isIdentifier(tempDecl.id) &&
		tempDecl.init == null
	) {
		const tempName = tempDecl.id.name;
		const guard = body[start + 1];
		if (
			!t.isIfStatement(guard) ||
			hasNonEmptyAlternate(guard) ||
			!t.isBlockStatement(guard.consequent) ||
			!isIteratorNotDoneCheck(guard.test, iteratorStateName)
		) return null;
		const valueAssign = assignmentToIdentifier(
			guard.consequent.body[0],
			tempName,
		);
		if (
			!valueAssign ||
			!t.isIdentifier(valueAssign.right, { name: valueName })
		) return null;
		const defaultGuard = guard.consequent.body[1];
		if (
			!t.isIfStatement(defaultGuard) ||
			defaultGuard.alternate ||
			!t.isBlockStatement(defaultGuard.consequent) ||
			getUndefinedCheckName(defaultGuard.test) !== valueName
		) return null;
		const defaultAssign = defaultAssignmentInBlock(
			defaultGuard.consequent,
			tempName,
		);
		if (!defaultAssign) return null;
		const target = destructuringAssignmentTarget(
			body[start + 2],
			tempName,
			globalNames,
		);
		if (!target) return null;
		return {
			target: target.name,
			plan: {
				kind: 'target' as const,
				target: target.target,
				defaultValue: defaultAssign.value,
			},
			defaultValue: defaultAssign.value,
			end: start + 3,
			declaredGlobal: target.target.kind === 'binding' &&
				target.target.declaredGlobal,
			intrinsic: 'IteratorNextWithDefault' as const,
		};
	}
	if (
		!tempDecl ||
		!t.isIdentifier(tempDecl.id) ||
		!t.isIdentifier(tempDecl.init, { name: valueName })
	) return null;
	const tempName = tempDecl.id.name;

	const guard = body[start + 1];
	if (!t.isIfStatement(guard) || guard.alternate) return null;
	if (
		!t.isLogicalExpression(guard.test, { operator: '||' }) ||
		![
			getUndefinedCheckName(guard.test.left),
			getUndefinedCheckName(guard.test.right),
		].includes(valueName)
	) return null;
	const assign = defaultAssignmentInBlock(
		guard.consequent,
		tempName,
	);
	if (!assign) return null;

	const target = destructuringAssignmentTarget(
		body[start + 2],
		tempName,
		globalNames,
	);
	if (!target) return null;

	return {
		target: target.name,
		plan: {
			kind: 'target' as const,
			target: target.target,
			defaultValue: assign.value,
		},
		defaultValue: assign.value,
		end: start + 3,
		declaredGlobal: target.target.kind === 'binding' &&
			target.target.declaredGlobal,
		intrinsic: 'IteratorNextWithDefault' as const,
	};
}

function nextPlainArrayElement(
	body: t.Statement[],
	start: number,
	iteratorRecordName: string,
	globalNames: Set<string>,
) {
	for (let guardIndex = start; guardIndex < body.length - 1; guardIndex++) {
		if (statementContainsIteratorClose(body[guardIndex])) break;
		const guard = body[guardIndex];
		if (!t.isIfStatement(guard) || guard.alternate) continue;

		const next = blockIteratorNextDecl(
			guard.consequent,
			iteratorRecordName,
		);
		if (!next || next.ids.length !== 2) continue;

		const element = plainArrayElement(
			body,
			guardIndex + 1,
			next.ids[0].name,
			next.ids[1].name,
			globalNames,
		);
		if (!element) continue;

		return {
			...element,
			iteratorStateName: next.ids[1].name,
		};
	}
	return null;
}

function nextPredeclaredPlainArrayElement(
	body: t.Statement[],
	start: number,
	iteratorStateName: string,
	iteratorRecordName: string,
): {
	target?: string;
	plan: PatternPlan;
	declaredGlobal: boolean;
	intrinsic: 'IteratorNextValue';
	end: number;
	iteratorStateName: string;
} | null {
	const targetDecl = singleDeclarator(body[start], 'let');
	if (
		!targetDecl ||
		!t.isIdentifier(targetDecl.id) ||
		!isUndefinedNode(targetDecl.init)
	) return null;
	const targetName = targetDecl.id.name;

	const doneDecl = singleDeclarator(body[start + 1], 'let');
	if (
		!doneDecl ||
		!t.isIdentifier(doneDecl.id) ||
		getUndefinedCheckName(doneDecl.init as t.Expression) !==
			iteratorStateName
	) return null;
	const doneName = doneDecl.id.name;

	const guard = body[start + 2];
	if (
		!t.isIfStatement(guard) ||
		guard.alternate ||
		!t.isBlockStatement(guard.consequent) ||
		!isIteratorNotDoneCheck(guard.test, iteratorStateName)
	) return null;
	const nested = guard.consequent.body;
	const next = intrinsicArrayDecl(nested[0], 'IteratorNext');
	if (
		!next ||
		next.ids.length !== 2 ||
		next.args.length !== 2 ||
		!t.isIdentifier(next.args[0], { name: iteratorStateName }) ||
		!t.isIdentifier(next.args[1], { name: iteratorRecordName })
	) return null;
	const [valueId, nextIteratorStateId] = next.ids;

	const resetAssign = assignmentToIdentifier(nested[1], targetName);
	if (!resetAssign || !isUndefinedNode(resetAssign.right)) return null;
	const doneAssign = assignmentToIdentifier(nested[2], doneName);
	if (
		!doneAssign ||
		getUndefinedCheckName(doneAssign.right as t.Expression) !==
			nextIteratorStateId.name
	) return null;

	const valueGuard = nested[3];
	if (
		!t.isIfStatement(valueGuard) ||
		valueGuard.alternate ||
		!t.isBlockStatement(valueGuard.consequent) ||
		!isIteratorNotDoneCheck(valueGuard.test, nextIteratorStateId.name)
	) return null;
	const valueAssign = assignmentToIdentifier(
		valueGuard.consequent.body[0],
		targetName,
	);
	if (
		!valueAssign ||
		!t.isIdentifier(valueAssign.right, { name: valueId.name })
	) return null;
	const nestedDoneAssign = assignmentToIdentifier(
		valueGuard.consequent.body[1],
		doneName,
	);
	if (
		!nestedDoneAssign ||
		getUndefinedCheckName(nestedDoneAssign.right as t.Expression) !==
			nextIteratorStateId.name
	) return null;

	return {
		target: targetName,
		plan: {
			kind: 'target',
			target: bindingTarget(targetName, false),
		},
		declaredGlobal: false,
		intrinsic: 'IteratorNextValue',
		end: start + 3,
		iteratorStateName: nextIteratorStateId.name,
	};
}

function nextDoneThenPredeclaredPlainArrayElement(
	body: t.Statement[],
	start: number,
	iteratorStateName: string,
	iteratorRecordName: string,
): {
	target?: string;
	plan: PatternPlan;
	declaredGlobal: boolean;
	intrinsic: 'IteratorNextValue';
	end: number;
	iteratorStateName: string;
} | null {
	const doneDecl = singleDeclarator(body[start], 'let');
	if (
		!doneDecl ||
		!t.isIdentifier(doneDecl.id) ||
		getUndefinedCheckName(doneDecl.init as t.Expression) !==
			iteratorStateName
	) return null;
	const doneName = doneDecl.id.name;

	const targetDecl = singleDeclarator(body[start + 1], 'let');
	if (
		!targetDecl ||
		!t.isIdentifier(targetDecl.id) ||
		!isUndefinedNode(targetDecl.init)
	) return null;
	const targetName = targetDecl.id.name;

	const guard = body[start + 2];
	if (
		!t.isIfStatement(guard) ||
		guard.alternate ||
		!t.isBlockStatement(guard.consequent) ||
		!isIteratorNotDoneCheck(guard.test, iteratorStateName)
	) return null;
	const nested = guard.consequent.body;
	const next = intrinsicArrayDecl(nested[0], 'IteratorNext');
	if (
		!next ||
		next.ids.length !== 2 ||
		next.args.length !== 2 ||
		!t.isIdentifier(next.args[0], { name: iteratorStateName }) ||
		!t.isIdentifier(next.args[1], { name: iteratorRecordName })
	) return null;
	const [valueId, nextIteratorStateId] = next.ids;

	const resetAssign = assignmentToIdentifier(nested[1], targetName);
	if (!resetAssign || !isUndefinedNode(resetAssign.right)) return null;
	const doneAssign = assignmentToIdentifier(nested[2], doneName);
	if (
		!doneAssign ||
		getUndefinedCheckName(doneAssign.right as t.Expression) !==
			nextIteratorStateId.name
	) return null;

	const valueGuard = nested[3];
	if (
		!t.isIfStatement(valueGuard) ||
		valueGuard.alternate ||
		!t.isBlockStatement(valueGuard.consequent) ||
		!isIteratorNotDoneCheck(valueGuard.test, nextIteratorStateId.name)
	) return null;
	const valueAssign = assignmentToIdentifier(
		valueGuard.consequent.body[0],
		targetName,
	);
	if (
		!valueAssign ||
		!t.isIdentifier(valueAssign.right, { name: valueId.name })
	) return null;
	const nestedDoneAssign = assignmentToIdentifier(
		valueGuard.consequent.body[1],
		doneName,
	);
	if (
		!nestedDoneAssign ||
		getUndefinedCheckName(nestedDoneAssign.right as t.Expression) !==
			nextIteratorStateId.name
	) return null;

	return {
		target: targetName,
		plan: {
			kind: 'target',
			target: bindingTarget(targetName, false),
		},
		declaredGlobal: false,
		intrinsic: 'IteratorNextValue',
		end: start + 3,
		iteratorStateName: nextIteratorStateId.name,
	};
}

function immediateNextThenPredeclaredPlainArrayElement(
	body: t.Statement[],
	start: number,
	iteratorStateName: string,
	iteratorRecordName: string,
): {
	target: string;
	plan: PatternPlan;
	declaredGlobal: false;
	intrinsic: 'IteratorNextValue';
	end: number;
	iteratorStateName: string;
	doneName: string;
} | null {
	const next = intrinsicArrayDecl(body[start], 'IteratorNext');
	if (
		!next ||
		next.ids.length !== 2 ||
		next.args.length !== 2 ||
		!t.isIdentifier(next.args[0], { name: iteratorStateName }) ||
		!t.isIdentifier(next.args[1], { name: iteratorRecordName })
	) return null;
	const [valueId, nextIteratorStateId] = next.ids;

	let doneDecl = singleDeclarator(body[start + 1], 'let');
	let targetDecl = singleDeclarator(body[start + 2], 'let');
	if (
		!(
			doneDecl &&
			t.isIdentifier(doneDecl.id) &&
			getUndefinedCheckName(doneDecl.init as t.Expression) ===
				iteratorStateName &&
			targetDecl &&
			t.isIdentifier(targetDecl.id) &&
			isUndefinedNode(targetDecl.init)
		)
	) {
		targetDecl = singleDeclarator(body[start + 1], 'let');
		doneDecl = singleDeclarator(body[start + 2], 'let');
	}
	if (
		!doneDecl ||
		!t.isIdentifier(doneDecl.id) ||
		getUndefinedCheckName(doneDecl.init as t.Expression) !==
			iteratorStateName
	) return null;
	const doneName = doneDecl.id.name;

	if (
		!targetDecl ||
		!t.isIdentifier(targetDecl.id) ||
		!isUndefinedNode(targetDecl.init)
	) return null;
	const targetName = targetDecl.id.name;

	const valueGuard = body[start + 3];
	if (
		!t.isIfStatement(valueGuard) ||
		valueGuard.alternate ||
		!t.isBlockStatement(valueGuard.consequent) ||
		!isIteratorNotDoneCheck(valueGuard.test, nextIteratorStateId.name)
	) return null;
	const valueAssign = assignmentToIdentifier(
		valueGuard.consequent.body[0],
		targetName,
	);
	if (
		!valueAssign ||
		!t.isIdentifier(valueAssign.right, { name: valueId.name })
	) return null;
	const doneAssign = assignmentToIdentifier(
		valueGuard.consequent.body[1],
		doneName,
	);
	if (
		!doneAssign ||
		getUndefinedCheckName(doneAssign.right as t.Expression) !==
			nextIteratorStateId.name
	) return null;

	return {
		target: targetName,
		plan: {
			kind: 'target',
			target: bindingTarget(targetName, false),
		},
		declaredGlobal: false,
		intrinsic: 'IteratorNextValue',
		end: start + 4,
		iteratorStateName: nextIteratorStateId.name,
		doneName,
	};
}

function nextDoneThenDefaultedArrayElement(
	body: t.Statement[],
	start: number,
	iteratorStateName: string,
	iteratorRecordName: string,
	globalNames: Set<string>,
): {
	target?: string;
	plan: PatternPlan;
	defaultValue: t.Expression;
	declaredGlobal: boolean;
	intrinsic: 'IteratorNextWithDefault';
	end: number;
	iteratorStateName: string;
} | null {
	const firstTargetDecl = singleDeclarator(body[start], 'let');
	const secondDoneDecl = singleDeclarator(body[start + 1], 'let');
	if (
		firstTargetDecl &&
		t.isIdentifier(firstTargetDecl.id) &&
		isUndefinedNode(firstTargetDecl.init) &&
		secondDoneDecl &&
		t.isIdentifier(secondDoneDecl.id) &&
		getUndefinedCheckName(secondDoneDecl.init as t.Expression) ===
			iteratorStateName
	) {
		const targetName = firstTargetDecl.id.name;
		const doneName = secondDoneDecl.id.name;
		const guard = body[start + 2];
		if (
			!t.isIfStatement(guard) ||
			guard.alternate ||
			!t.isBlockStatement(guard.consequent) ||
			!isIteratorNotDoneCheck(guard.test, iteratorStateName)
		) return null;
		const nested = guard.consequent.body;
		const next = intrinsicArrayDecl(nested[0], 'IteratorNext');
		if (
			!next ||
			next.ids.length !== 2 ||
			next.args.length !== 2 ||
			!t.isIdentifier(next.args[0], { name: iteratorStateName }) ||
			!t.isIdentifier(next.args[1], { name: iteratorRecordName })
		) return null;
		const [valueId, nextIteratorStateId] = next.ids;
		const doneAssign = assignmentToIdentifier(nested[1], doneName);
		if (
			!doneAssign ||
			getUndefinedCheckName(doneAssign.right as t.Expression) !==
				nextIteratorStateId.name
		) return null;
		const valueGuard = nested[2];
		if (
			!t.isIfStatement(valueGuard) ||
			valueGuard.alternate ||
			!t.isBlockStatement(valueGuard.consequent) ||
			!isIteratorNotDoneCheck(
				valueGuard.test,
				nextIteratorStateId.name,
			)
		) return null;
		const valueAssign = assignmentToIdentifier(
			valueGuard.consequent.body[0],
			targetName,
		);
		if (
			!valueAssign ||
			!t.isIdentifier(valueAssign.right, { name: valueId.name })
		) return null;
		const statePhiDecl = singleDeclarator(body[start + 3], 'const');
		if (
			!statePhiDecl ||
			!t.isIdentifier(statePhiDecl.id) ||
			!t.isCallExpression(statePhiDecl.init) ||
			!t.isV8IntrinsicIdentifier(statePhiDecl.init.callee, {
				name: 'Phi',
			})
		) return null;
		const statePhiName = statePhiDecl.id.name;
		const finalTargetDecl = singleDeclarator(body[start + 4], 'let');
		const finalDoneDecl = singleDeclarator(body[start + 5], 'let');
		const finalStateDecl = singleDeclarator(body[start + 6], 'let');
		if (
			!finalTargetDecl ||
			!t.isIdentifier(finalTargetDecl.id) ||
			!t.isIdentifier(finalTargetDecl.init, { name: targetName }) ||
			!finalDoneDecl ||
			!t.isIdentifier(finalDoneDecl.id) ||
			!t.isIdentifier(finalDoneDecl.init, { name: doneName }) ||
			!finalStateDecl ||
			!t.isIdentifier(finalStateDecl.id) ||
			!t.isCallExpression(finalStateDecl.init) ||
			!t.isV8IntrinsicIdentifier(finalStateDecl.init.callee, {
				name: 'Phi',
			})
		) return null;
		const finalTargetName = finalTargetDecl.id.name;
		const finalDoneName = finalDoneDecl.id.name;
		const finalStateName = finalStateDecl.id.name;
		const defaultGuard = body[start + 7];
		if (
			!t.isIfStatement(defaultGuard) ||
			defaultGuard.alternate ||
			!t.isBlockStatement(defaultGuard.consequent) ||
			getUndefinedCheckName(defaultGuard.test) !== targetName
		) return null;
		const finalDoneAssign = assignmentToIdentifier(
			defaultGuard.consequent.body[0],
			finalDoneName,
		);
		const finalStateAssign = assignmentToIdentifier(
			defaultGuard.consequent.body[1],
			finalStateName,
		);
		const defaultAssign = defaultAssignmentInBlock(
			defaultGuard.consequent,
			finalTargetName,
		);
		if (
			!finalDoneAssign ||
			!t.isIdentifier(finalDoneAssign.right, { name: doneName }) ||
			!finalStateAssign ||
			!t.isIdentifier(finalStateAssign.right, { name: statePhiName }) ||
			!defaultAssign
		) return null;
		const target = destructuringAssignmentTarget(
			body[start + 8],
			finalTargetName,
			globalNames,
		);
		if (!target) return null;
		return {
			target: target.name,
			plan: {
				kind: 'target',
				target: target.target,
				defaultValue: defaultAssign.value,
			},
			defaultValue: defaultAssign.value,
			declaredGlobal: target.target.kind === 'binding' &&
				target.target.declaredGlobal,
			intrinsic: 'IteratorNextWithDefault',
			end: start + 9,
			iteratorStateName: finalStateName,
		};
	}

	const doneDecl = singleDeclarator(body[start], 'let');
	if (
		!doneDecl ||
		!t.isIdentifier(doneDecl.id) ||
		getUndefinedCheckName(doneDecl.init as t.Expression) !==
			iteratorStateName
	) return null;
	const doneName = doneDecl.id.name;

	const targetDecl = singleDeclarator(body[start + 1], 'let');
	if (
		!targetDecl ||
		!t.isIdentifier(targetDecl.id) ||
		!isUndefinedNode(targetDecl.init)
	) return null;
	const targetName = targetDecl.id.name;

	const guard = body[start + 2];
	if (
		!t.isIfStatement(guard) ||
		guard.alternate ||
		!t.isBlockStatement(guard.consequent) ||
		!isIteratorNotDoneCheck(guard.test, iteratorStateName)
	) return null;
	const nested = guard.consequent.body;
	const next = intrinsicArrayDecl(nested[0], 'IteratorNext');
	if (
		!next ||
		next.ids.length !== 2 ||
		next.args.length !== 2 ||
		!t.isIdentifier(next.args[0], { name: iteratorStateName }) ||
		!t.isIdentifier(next.args[1], { name: iteratorRecordName })
	) return null;
	const [valueId, nextIteratorStateId] = next.ids;

	const valueGuard = nested[1];
	if (
		!t.isIfStatement(valueGuard) ||
		valueGuard.alternate ||
		!t.isBlockStatement(valueGuard.consequent) ||
		!isIteratorNotDoneCheck(valueGuard.test, nextIteratorStateId.name)
	) return null;
	const valueAssign = assignmentToIdentifier(
		valueGuard.consequent.body[0],
		targetName,
	);
	if (
		!valueAssign ||
		!t.isIdentifier(valueAssign.right, { name: valueId.name })
	) return null;
	const doneAssign = assignmentToIdentifier(
		valueGuard.consequent.body[1],
		doneName,
	);
	if (
		!doneAssign ||
		getUndefinedCheckName(doneAssign.right as t.Expression) !==
			nextIteratorStateId.name
	) return null;

	const statePhiDecl = singleDeclarator(body[start + 3], 'const');
	if (
		!statePhiDecl ||
		!t.isIdentifier(statePhiDecl.id) ||
		!t.isCallExpression(statePhiDecl.init) ||
		!t.isV8IntrinsicIdentifier(statePhiDecl.init.callee, { name: 'Phi' })
	) return null;
	const statePhiName = statePhiDecl.id.name;

	const finalDoneDecl = singleDeclarator(body[start + 4], 'let');
	if (
		!finalDoneDecl ||
		!t.isIdentifier(finalDoneDecl.id) ||
		!t.isIdentifier(finalDoneDecl.init, { name: doneName })
	) return null;
	const finalDoneName = finalDoneDecl.id.name;

	const finalTargetDecl = singleDeclarator(body[start + 5], 'let');
	if (
		!finalTargetDecl ||
		!t.isIdentifier(finalTargetDecl.id) ||
		!t.isIdentifier(finalTargetDecl.init, { name: targetName })
	) return null;
	const finalTargetName = finalTargetDecl.id.name;

	const finalStateDecl = singleDeclarator(body[start + 6], 'let');
	if (
		!finalStateDecl ||
		!t.isIdentifier(finalStateDecl.id) ||
		!t.isCallExpression(finalStateDecl.init) ||
		!t.isV8IntrinsicIdentifier(finalStateDecl.init.callee, {
			name: 'Phi',
		})
	) return null;
	const finalStateName = finalStateDecl.id.name;

	const defaultGuard = body[start + 7];
	if (
		!t.isIfStatement(defaultGuard) ||
		defaultGuard.alternate ||
		!t.isBlockStatement(defaultGuard.consequent) ||
		getUndefinedCheckName(defaultGuard.test) !== targetName
	) return null;
	const finalStateAssign = assignmentToIdentifier(
		defaultGuard.consequent.body[0],
		finalStateName,
	);
	if (
		!finalStateAssign ||
		!t.isIdentifier(finalStateAssign.right, { name: statePhiName })
	) return null;
	const defaultAssign = defaultAssignmentInBlock(
		defaultGuard.consequent,
		finalTargetName,
	);
	if (!defaultAssign) return null;
	const finalDoneAssign = assignmentToIdentifier(
		defaultGuard.consequent.body[2],
		finalDoneName,
	);
	if (
		!finalDoneAssign ||
		!t.isIdentifier(finalDoneAssign.right, { name: doneName })
	) return null;

	const target = destructuringAssignmentTarget(
		body[start + 8],
		finalTargetName,
		globalNames,
	);
	if (!target) return null;

	return {
		target: target.name,
		plan: {
			kind: 'target',
			target: target.target,
			defaultValue: defaultAssign.value,
		},
		defaultValue: defaultAssign.value,
		declaredGlobal: target.target.kind === 'binding' &&
			target.target.declaredGlobal,
		intrinsic: 'IteratorNextWithDefault',
		end: start + 9,
		iteratorStateName: finalStateName,
	};
}

type DestructuringElement = {
	elided?: boolean;
	target?: string;
	pattern?: t.PatternLike;
	defaultValue?: t.Expression;
	declaredGlobal: boolean;
	plan?: PatternPlan;
	rest?: boolean;
	iteratorStateName?: string;
	intrinsic:
		| 'IteratorElision'
		| 'IteratorNextValue'
		| 'IteratorNextWithDefault'
		| 'IteratorRest'
		| 'IteratorNestedArray';
};

type DestructuringMatch = {
	pattern: t.ArrayPattern;
	end: number;
	declaredGlobals: Set<string>;
};

function isPhiDeclaration(stmt: t.Statement | undefined): boolean {
	const decl = singleDeclarator(stmt, 'const');
	return !!decl &&
		t.isCallExpression(decl.init) &&
		t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' });
}

function isPhiExpression(stmt: t.Statement | undefined): boolean {
	return !!stmt &&
		t.isExpressionStatement(stmt) &&
		t.isCallExpression(stmt.expression) &&
		t.isV8IntrinsicIdentifier(stmt.expression.callee, { name: 'Phi' });
}

function isNotDoneOrChain(
	expr: t.Expression,
	names: Set<string>,
): boolean {
	if (!t.isUnaryExpression(expr, { operator: '!' })) return false;
	const inner = expr.argument;
	if (!t.isExpression(inner)) return false;
	const checks = t.isLogicalExpression(inner, { operator: '||' })
		? [inner.left, inner.right]
		: [inner];
	return checks.every((check) =>
		t.isExpression(check) &&
		(names.has(getUndefinedCheckName(check) ?? ''))
	);
}

function nextNestedArrayElement(
	body: t.Statement[],
	start: number,
	iteratorRecordName: string,
	globalNames: Set<string>,
) {
	const next = intrinsicArrayDecl(body[start], 'IteratorNext');
	if (
		!next ||
		next.ids.length !== 2 ||
		next.args.length !== 2 ||
		!t.isIdentifier(next.args[0]) ||
		!t.isIdentifier(next.args[1], { name: iteratorRecordName })
	) return null;
	const [valueId, nextIteratorStateId] = next.ids;
	const previousIteratorStateName = next.args[0].name;

	const doneDecl = singleDeclarator(body[start + 1], 'let');
	if (
		!doneDecl ||
		!t.isIdentifier(doneDecl.id) ||
		getUndefinedCheckName(doneDecl.init as t.Expression) !==
			previousIteratorStateName
	) return null;

	const targetDecl = singleDeclarator(body[start + 2], 'let');
	if (
		!targetDecl ||
		!t.isIdentifier(targetDecl.id) ||
		!isUndefinedNode(targetDecl.init)
	) return null;

	const guard = body[start + 3];
	if (
		!t.isIfStatement(guard) ||
		guard.alternate ||
		!t.isBlockStatement(guard.consequent) ||
		!isNotDoneOrChain(
			guard.test,
			new Set([previousIteratorStateName, nextIteratorStateId.name]),
		)
	) return null;

	const valueAssign = singleAssignmentInBlock(
		guard.consequent,
		targetDecl.id.name,
	);
	if (
		!valueAssign ||
		!t.isIdentifier(valueAssign.right, { name: valueId.name })
	) {
		return null;
	}

	const statePhi = isPhiDeclaration(body[start + 4])
		? singleDeclarator(body[start + 4], 'const')
		: null;
	const childStart = statePhi ? start + 5 : start + 4;
	const child = matchSequentialArrayDestructuring(
		body,
		childStart,
		globalNames,
		targetDecl.id.name,
	);
	if (!child) return null;

	return {
		pattern: child.pattern,
		plan: {
			kind: 'array' as const,
			pattern: child.pattern,
		},
		end: child.end,
		declaredGlobal: child.declaredGlobals.size > 0,
		declaredGlobals: child.declaredGlobals,
		iteratorStateName: statePhi && t.isIdentifier(statePhi.id)
			? statePhi.id.name
			: nextIteratorStateId.name,
		intrinsic: 'IteratorNestedArray' as const,
	};
}

function arrayIndexWrite(
	stmt: t.Statement | undefined,
	arrayName: string,
	indexName: string,
	valueName: string,
): boolean {
	const assign = expressionStatementAssignment(stmt);
	return !!assign &&
		t.isMemberExpression(assign.left, { computed: true }) &&
		t.isIdentifier(assign.left.object, { name: arrayName }) &&
		t.isIdentifier(assign.left.property, { name: indexName }) &&
		t.isIdentifier(assign.right, { name: valueName });
}

function indexIncrement(
	stmt: t.Statement | undefined,
	indexName: string,
): boolean {
	if (!stmt || !t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	if (
		!t.isAssignmentExpression(expr) ||
		!t.isIdentifier(expr.left, { name: indexName })
	) {
		return false;
	}
	const assign = expr;
	if (assign.operator === '+=') {
		return t.isNumericLiteral(assign.right, { value: 1 });
	}
	if (
		assign.operator !== '=' ||
		!t.isBinaryExpression(assign.right, { operator: '+' })
	) {
		return false;
	}
	return t.isIdentifier(assign.right.left, { name: indexName }) &&
		t.isNumericLiteral(assign.right.right, { value: 1 });
}

function tryBodyStatements(
	stmt: t.Statement | undefined,
): t.Statement[] | null {
	if (t.isTryStatement(stmt)) return stmt.block.body;
	if (t.isBlockStatement(stmt)) return stmt.body;
	return null;
}

function consumeRestAssignment(
	stmt: t.Statement | undefined,
	arrayName: string,
	globalNames: Set<string>,
): { target?: string; plan: PatternPlan; declaredGlobal: boolean } | null {
	const stmts = tryBodyStatements(stmt);
	if (!stmts) return null;

	for (let i = 0; i < stmts.length; i++) {
		const current = stmts[i];
		if (
			t.isExpressionStatement(current) &&
			t.isCallExpression(current.expression) &&
			t.isV8IntrinsicIdentifier(current.expression.callee, {
				name: 'Phi',
			})
		) continue;

		const assign = expressionStatementAssignment(current);
		if (!assign || !t.isIdentifier(assign.right, { name: arrayName })) {
			return null;
		}
		const target = destructuringAssignmentTarget(
			current,
			arrayName,
			globalNames,
		);
		if (!target) return null;
		stmts.splice(0, i + 1);
		return {
			target: target.name,
			plan: { kind: 'target', target: target.target },
			declaredGlobal: target.target.kind === 'binding' &&
				target.target.declaredGlobal,
		};
	}

	return null;
}

function consumeRestAssignmentAt(
	body: t.Statement[],
	start: number,
	arrayName: string,
	globalNames: Set<string>,
): {
	target?: string;
	plan: PatternPlan;
	declaredGlobal: boolean;
	end: number;
} | null {
	for (let i = start; i < body.length; i++) {
		if (isPhiExpression(body[i])) continue;

		const assign = expressionStatementAssignment(body[i]);
		if (!assign || !t.isIdentifier(assign.right, { name: arrayName })) {
			return null;
		}
		const target = destructuringAssignmentTarget(
			body[i],
			arrayName,
			globalNames,
		);
		if (!target) return null;
		return {
			target: target.name,
			plan: { kind: 'target', target: target.target },
			declaredGlobal: target.target.kind === 'binding' &&
				target.target.declaredGlobal,
			end: i + 1,
		};
	}

	return null;
}

function restArrayCollection(
	body: t.Statement[],
	start: number,
	iteratorStateName: string,
	iteratorRecordName: string,
	globalNames: Set<string>,
):
	| { blocked: true }
	| {
		target?: string;
		plan: PatternPlan;
		declaredGlobal: boolean;
		end: number;
	}
	| null {
	const arrayDecl = singleDeclarator(body[start], 'const');
	if (
		!arrayDecl ||
		!t.isIdentifier(arrayDecl.id) ||
		!t.isArrayExpression(arrayDecl.init) ||
		arrayDecl.init.elements.length !== 0
	) return null;
	const arrayName = arrayDecl.id.name;

	let guardIndex = start + 1;
	const doneDecl = singleDeclarator(body[guardIndex], 'let');
	if (
		doneDecl &&
		t.isIdentifier(doneDecl.id) &&
		t.isExpression(doneDecl.init) &&
		getUndefinedCheckName(doneDecl.init) === iteratorStateName
	) {
		guardIndex++;
	}

	const guard = body[guardIndex];
	if (
		!t.isIfStatement(guard) ||
		guard.alternate ||
		!t.isBlockStatement(guard.consequent) ||
		!isRestCollectionGuard(guard.test, iteratorStateName)
	) return null;

	const loopBody = guard.consequent.body;
	const firstLoopDecl = singleDeclarator(loopBody[0], 'let');
	const secondLoopDecl = singleDeclarator(loopBody[1], 'let');
	const loop = loopBody[2];
	const indexDecl = firstLoopDecl &&
			t.isIdentifier(firstLoopDecl.id) &&
			t.isNumericLiteral(firstLoopDecl.init, { value: 0 })
		? firstLoopDecl
		: secondLoopDecl &&
				t.isIdentifier(secondLoopDecl.id) &&
				t.isNumericLiteral(secondLoopDecl.init, { value: 0 })
		? secondLoopDecl
		: null;
	const carryDecl = firstLoopDecl &&
			t.isIdentifier(firstLoopDecl.id) &&
			t.isIdentifier(firstLoopDecl.init)
		? firstLoopDecl
		: secondLoopDecl &&
				t.isIdentifier(secondLoopDecl.id) &&
				t.isIdentifier(secondLoopDecl.init)
		? secondLoopDecl
		: null;
	if (
		!indexDecl ||
		!t.isIdentifier(indexDecl.id) ||
		!carryDecl ||
		!t.isIdentifier(carryDecl.id) ||
		!t.isWhileStatement(loop) ||
		!t.isBooleanLiteral(loop.test, { value: true }) ||
		!t.isBlockStatement(loop.body)
	) return { blocked: true };

	const next = intrinsicArrayDecl(loop.body.body[0], 'IteratorNext');
	if (
		!next ||
		next.ids.length !== 2 ||
		next.args.length !== 2 ||
		!t.isIdentifier(next.args[0], { name: carryDecl.id.name }) ||
		!t.isIdentifier(next.args[1], { name: iteratorRecordName })
	) return { blocked: true };
	const [valueId, nextIteratorStateId] = next.ids;

	let doneIndex = 1;
	const loopDoneAssign = expressionStatementAssignment(
		loop.body.body[doneIndex],
	);
	if (
		loopDoneAssign &&
		t.isIdentifier(loopDoneAssign.left) &&
		t.isExpression(loopDoneAssign.right) &&
		getUndefinedCheckName(loopDoneAssign.right) === nextIteratorStateId.name
	) {
		doneIndex++;
	}

	const done = loop.body.body[doneIndex];
	if (
		!t.isIfStatement(done) ||
		done.alternate ||
		getUndefinedCheckName(done.test) !== nextIteratorStateId.name ||
		!t.isBlockStatement(done.consequent) ||
		done.consequent.body.length !== 1 ||
		!t.isBreakStatement(done.consequent.body[0])
	) return { blocked: true };

	const writeContainer = loop.body.body[doneIndex + 1];
	const writeBody = t.isTryStatement(writeContainer)
		? writeContainer.block.body
		: t.isBlockStatement(writeContainer)
		? writeContainer.body
		: null;
	if (!writeBody || writeBody.length < 3) return { blocked: true };
	if (
		!arrayIndexWrite(
			writeBody[0],
			arrayName,
			indexDecl.id.name,
			valueId.name,
		)
	) return { blocked: true };
	if (!indexIncrement(writeBody[1], indexDecl.id.name)) {
		return { blocked: true };
	}
	if (!t.isContinueStatement(writeBody[2])) return { blocked: true };

	const bodyAssignment = consumeRestAssignmentAt(
		body,
		guardIndex + 1,
		arrayName,
		globalNames,
	);
	if (bodyAssignment) return bodyAssignment;

	const assignment = consumeRestAssignment(
		body[guardIndex + 1],
		arrayName,
		globalNames,
	);
	if (!assignment) return { blocked: true };

	return {
		...assignment,
		end: guardIndex + 1,
	};
}

function normalizeIteratorRest(
	body: t.Statement[],
	start: number,
	iteratorStateName: string,
	iteratorRecordName: string,
	globalNames: Set<string>,
):
	| { blocked: true }
	| {
		target?: string;
		plan: PatternPlan;
		declaredGlobal: boolean;
		end: number;
		intrinsic: 'IteratorRest';
	}
	| null {
	const rest = restArrayCollection(
		body,
		start,
		iteratorStateName,
		iteratorRecordName,
		globalNames,
	);
	if (!rest || 'blocked' in rest) return rest;
	return {
		...rest,
		intrinsic: 'IteratorRest',
	};
}

function consumeIteratorCloseStatePhi(
	body: t.Statement[],
	start: number,
	iteratorStateName: string,
): number | null {
	let end = start;
	const statePhi = isPhiDeclaration(body[end]) ? body[end] : null;
	if (statePhi) {
		const decl = singleDeclarator(statePhi, 'const');
		if (
			!decl ||
			!t.isIdentifier(decl.id) ||
			!t.isCallExpression(decl.init) ||
			!decl.init.arguments.some((arg) =>
				t.isIdentifier(arg, { name: iteratorStateName })
			)
		) return null;
		iteratorStateName = decl.id.name;
		end++;
	}

	const directCloseUsesState = (
		stmt: t.Statement | undefined,
		stateName: string,
	): boolean => {
		if (!t.isExpressionStatement(stmt)) return false;
		const expr = stmt.expression;
		if (
			!t.isCallExpression(expr) ||
			!t.isV8IntrinsicIdentifier(expr.callee, { name: 'IteratorClose' })
		) return false;
		const [stateArg] = expr.arguments;
		if (t.isIdentifier(stateArg, { name: stateName })) return true;
		return t.isCallExpression(stateArg) &&
			t.isV8IntrinsicIdentifier(stateArg.callee, { name: 'Phi' }) &&
			stateArg.arguments.some((arg) =>
				t.isIdentifier(arg, { name: stateName })
			);
	};

	if (directCloseUsesState(body[end], iteratorStateName)) return end + 1;

	const doneGuard = body[end];
	if (
		t.isIfStatement(doneGuard) &&
		!doneGuard.alternate &&
		t.isBlockStatement(doneGuard.consequent) &&
		statementListEndsAbruptly(doneGuard.consequent.body) &&
		directCloseUsesState(body[end + 1], iteratorStateName)
	) {
		return end + 2;
	}

	const closeStmt = body[end];
	if (
		t.isIfStatement(closeStmt) &&
		t.isBlockStatement(closeStmt.consequent) &&
		closeStmt.consequent.body.some((stmt) =>
			t.isExpressionStatement(stmt) &&
			t.isCallExpression(stmt.expression) &&
			t.isV8IntrinsicIdentifier(stmt.expression.callee, {
				name: 'IteratorClose',
			})
		)
	) return end + 1;

	return start;
}

function isIteratorCloseFalseStatement(stmt: t.Statement | undefined): boolean {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	return t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, { name: 'IteratorClose' }) &&
		expr.arguments.length === 2 &&
		t.isBooleanLiteral(expr.arguments[1], { value: false });
}

function suppressDuplicatedDoneContinuationForCheck(
	consumed: t.Statement[],
): (() => void) | null {
	const close = consumed.at(-1);
	const doneGuard = consumed.at(-2);
	if (
		!isIteratorCloseFalseStatement(close) ||
		!t.isIfStatement(doneGuard) ||
		doneGuard.alternate ||
		!t.isBlockStatement(doneGuard.consequent) ||
		!statementListEndsAbruptly(doneGuard.consequent.body)
	) return null;

	const consequent = doneGuard.consequent;
	const original = consequent.body;
	consequent.body = [];
	return () => {
		consequent.body = original;
	};
}

function patternFromElements(elements: DestructuringElement[]): t.ArrayPattern {
	return t.arrayPattern(
		elements.map((element) => {
			if (element.elided) return null;
			if (element.plan) {
				const pattern = planToPattern(element.plan);
				return element.rest
					? t.restElement(pattern as unknown as RestElementArgument)
					: pattern;
			}
			if (element.pattern) return element.pattern;
			const target = t.identifier(element.target!);
			if (element.rest) return t.restElement(target);
			if (!element.defaultValue) return target;
			return t.assignmentPattern(
				target,
				t.cloneNode(element.defaultValue, true) as t.Expression,
			);
		}),
	);
}

function matchSequentialArrayDestructuring(
	body: t.Statement[],
	i: number,
	globalNames: Set<string>,
	expectedSourceName?: string,
): DestructuringMatch | null {
	const begin = intrinsicArrayDecl(body[i], 'IteratorBegin');
	if (!begin || begin.ids.length !== 2 || begin.args.length !== 1) {
		return null;
	}
	if (
		expectedSourceName &&
		!t.isIdentifier(begin.args[0], { name: expectedSourceName })
	) return null;
	const [iteratorId, iteratorStateId] = begin.ids;

	const firstNext = intrinsicArrayDecl(body[i + 1], 'IteratorNext');
	if (
		!firstNext ||
		firstNext.ids.length !== 2 ||
		firstNext.args.length !== 2 ||
		!t.isIdentifier(firstNext.args[0], { name: iteratorId.name }) ||
		!t.isIdentifier(firstNext.args[1], { name: iteratorStateId.name })
	) return null;
	const [firstValue, firstIteratorState] = firstNext.ids;

	const firstDefaulted = firstDefaultedArrayElement(
		body,
		i + 2,
		firstValue.name,
		firstIteratorState.name,
		globalNames,
	);
	let firstPlain = firstDefaulted ?? plainArrayElement(
		body,
		i + 2,
		firstValue.name,
		firstIteratorState.name,
		globalNames,
	);

	const elements: DestructuringElement[] = [];
	const declaredGlobals = new Set<string>();
	if (!firstPlain) {
		const elided = elidedFirstThenPlainSecondElement(
			body,
			i + 2,
			firstIteratorState.name,
			iteratorStateId.name,
		);
		if (!elided) return null;
		elements.push({
			elided: true,
			declaredGlobal: false,
			intrinsic: 'IteratorElision',
		});
		const elidedElement = elided.element;
		elements.push(elidedElement);
		if (elidedElement.declaredGlobal && elidedElement.target) {
			declaredGlobals.add(elidedElement.target);
		}
		let end = elided.end;
		const iteratorRecordName = iteratorStateId.name;
		let iteratorStateName = elided.iteratorStateName;
		const statePhi = isPhiDeclaration(body[end]) ? body[end] : null;
		if (statePhi) {
			const decl = singleDeclarator(statePhi, 'const');
			if (
				decl &&
				t.isIdentifier(decl.id) &&
				t.isCallExpression(decl.init) &&
				decl.init.arguments.some((arg) =>
					t.isIdentifier(arg, { name: iteratorStateName })
				)
			) {
				iteratorStateName = decl.id.name;
				end++;
			}
		}
		const closeStmt = body[end];
		if (
			t.isIfStatement(closeStmt) &&
			t.isBlockStatement(closeStmt.consequent) &&
			closeStmt.consequent.body.some((stmt) =>
				t.isExpressionStatement(stmt) &&
				t.isCallExpression(stmt.expression) &&
				t.isV8IntrinsicIdentifier(stmt.expression.callee, {
					name: 'IteratorClose',
				})
			)
		) {
			end++;
		}
		return {
			pattern: patternFromElements(elements),
			end,
			declaredGlobals,
		};
	}
	firstPlain = firstPlain ?? compactFirstArrayElement(
		body,
		i + 2,
		firstValue.name,
		firstIteratorState.name,
	);
	if (!firstPlain) return null;

	elements.push(firstPlain);
	if (firstPlain.declaredGlobal && firstPlain.target) {
		declaredGlobals.add(firstPlain.target);
	}
	let end = firstPlain.end;
	const iteratorRecordName = iteratorStateId.name;
	let iteratorStateName = firstIteratorState.name;
	while (true) {
		const doneThenDefaulted = nextDoneThenDefaultedArrayElement(
			body,
			end,
			iteratorStateName,
			iteratorRecordName,
			globalNames,
		);
		const defaulted = doneThenDefaulted ? null : nextDefaultedArrayElement(
			body,
			end,
			iteratorRecordName,
			globalNames,
		);
		const predeclared = defaulted ? null : nextPredeclaredPlainArrayElement(
			body,
			end,
			iteratorStateName,
			iteratorRecordName,
		);
		const doneThenPredeclared = defaulted || predeclared
			? null
			: nextDoneThenPredeclaredPlainArrayElement(
				body,
				end,
				iteratorStateName,
				iteratorRecordName,
			);
		const element = defaulted ??
			predeclared ??
			doneThenPredeclared ??
			doneThenDefaulted ??
			nextPlainArrayElement(
				body,
				end,
				iteratorRecordName,
				globalNames,
			) ??
			nextNestedArrayElement(
				body,
				end,
				iteratorRecordName,
				globalNames,
			);
		if (!element) break;
		const defaultValue = 'defaultValue' in element
			? element.defaultValue as t.Expression
			: undefined;
		const nextElement: DestructuringElement = {
			target: 'target' in element ? element.target : undefined,
			pattern: 'pattern' in element ? element.pattern : undefined,
			plan: 'plan' in element ? element.plan : undefined,
			defaultValue,
			declaredGlobal: element.declaredGlobal,
			intrinsic: element.intrinsic,
		};
		elements.push(nextElement);
		if (element.declaredGlobal && 'target' in element && element.target) {
			declaredGlobals.add(element.target);
		}
		if ('declaredGlobals' in element) {
			for (const name of element.declaredGlobals) {
				declaredGlobals.add(name);
			}
		}
		if ('iteratorStateName' in element) {
			iteratorStateName = element.iteratorStateName;
		}
		end = element.end;
	}

	const rest = normalizeIteratorRest(
		body,
		end,
		iteratorStateName,
		iteratorRecordName,
		globalNames,
	);
	if (rest && 'blocked' in rest) return null;
	if (rest) {
		elements.push({
			target: rest.target,
			plan: rest.plan,
			declaredGlobal: rest.declaredGlobal,
			rest: true,
			intrinsic: rest.intrinsic,
		});
		if (rest.declaredGlobal && rest.target) {
			declaredGlobals.add(rest.target);
		}
		end = rest.end;
	}

	end = consumeIteratorCloseStatePhi(body, end, iteratorStateName) ?? end;

	return {
		pattern: patternFromElements(elements),
		end,
		declaredGlobals,
	};
}

function isUndefinedStrictEquality(expr: t.Expression, value: t.Expression) {
	if (!t.isBinaryExpression(expr, { operator: '===' })) return false;
	if (!t.isExpression(expr.left)) return false;
	return (
		expressionsEqual(expr.left, value) && isUndefinedNode(expr.right)
	) || (isUndefinedNode(expr.left) && expressionsEqual(expr.right, value));
}

function undefinedAliasNames(body: readonly t.Statement[]): Set<string> {
	const names = new Set(['undefined']);
	for (const statement of body) {
		if (!t.isVariableDeclaration(statement)) continue;
		for (const declaration of statement.declarations) {
			if (
				t.isIdentifier(declaration.id) && declaration.init &&
				isUndefinedNode(declaration.init)
			) names.add(declaration.id.name);
		}
	}
	return names;
}

function isUndefinedStrictEqualityWithAliases(
	expr: t.Expression,
	value: t.Expression,
	aliases: ReadonlySet<string>,
): boolean {
	if (!t.isBinaryExpression(expr, { operator: '===' })) return false;
	if (!t.isExpression(expr.left) || !t.isExpression(expr.right)) return false;
	const isUndefinedAlias = (candidate: t.Expression) =>
		t.isIdentifier(candidate) && aliases.has(candidate.name);
	return (expressionsEqual(expr.left, value) &&
		isUndefinedAlias(expr.right)) ||
		(isUndefinedAlias(expr.left) && expressionsEqual(expr.right, value));
}

function getObjectCreateNullName(stmt: t.Statement | undefined) {
	const decl = singleDeclarator(stmt, 'const');
	if (!decl || !t.isIdentifier(decl.id)) return null;
	if (!t.isCallExpression(decl.init)) return null;
	const callee = decl.init.callee;
	if (!t.isMemberExpression(callee, { computed: false })) return null;
	if (!t.isIdentifier(callee.object, { name: 'Object' })) return null;
	if (!t.isIdentifier(callee.property, { name: 'create' })) return null;
	if (
		decl.init.arguments.length !== 1 ||
		!t.isNullLiteral(decl.init.arguments[0])
	) return null;
	return decl.id.name;
}

interface LinearAliasValue {
	expression: t.Expression;
	/** Const declarations followed while resolving this value. */
	declarationIndices: number[];
	/** The generated binding whose non-alias initializer produced expression. */
	rootName?: string;
	rootIndex?: number;
}

function constDeclaratorBefore(
	body: t.Statement[],
	name: string,
	before: number,
): { declaration: t.VariableDeclarator; index: number } | null {
	for (let i = before - 1; i >= 0; i--) {
		const declaration = singleDeclarator(body[i], 'const');
		if (!declaration || !t.isIdentifier(declaration.id, { name })) continue;
		return { declaration, index: i };
	}
	return null;
}

/**
 * Follow only SSA identity aliases. This deliberately does not perform generic
 * expression inlining: the object-rest recognizer needs to see through the
 * register moves which are part of the bytecode protocol, while unrelated
 * declarations remain hard ordering barriers for the later alias pass.
 */
function resolveLinearAlias(
	body: t.Statement[],
	value: t.Expression,
	before: number,
): LinearAliasValue {
	const declarationIndices: number[] = [];
	const seen = new Set<string>();
	let expression = value;
	let rootName: string | undefined;
	let rootIndex: number | undefined;
	while (t.isIdentifier(expression) && isGeneratedName(expression.name)) {
		if (seen.has(expression.name)) break;
		seen.add(expression.name);
		const found = constDeclaratorBefore(body, expression.name, before);
		if (!found || !t.isExpression(found.declaration.init)) break;
		// A Phi is CFG metadata, not a value. Walking through it would consume
		// the declaration and inline the call as the destructuring source,
		// which leaves the emitter no target to lower the edge assignments
		// onto -- `%Phi` then reaches the program. Stop on the identifier that
		// names it: the recovery still runs, against a source the emitter can
		// still resolve.
		if (
			t.isCallExpression(found.declaration.init) &&
			t.isV8IntrinsicIdentifier(found.declaration.init.callee, {
				name: 'Phi',
			})
		) break;
		declarationIndices.push(found.index);
		rootName = expression.name;
		rootIndex = found.index;
		expression = found.declaration.init;
		before = found.index;
		if (!t.isIdentifier(expression)) break;
	}
	return { expression, declarationIndices, rootName, rootIndex };
}

interface ObjectRestKey {
	key: t.Expression;
	computed: boolean;
}

function staticPropertyName(key: t.Expression, computed: boolean) {
	if (t.isStringLiteral(key) || t.isNumericLiteral(key)) {
		return String(key.value);
	}
	if (!computed && t.isIdentifier(key)) return key.name;
	return null;
}

function objectRestKeysEqual(left: ObjectRestKey, right: ObjectRestKey) {
	const leftName = staticPropertyName(left.key, left.computed);
	const rightName = staticPropertyName(right.key, right.computed);
	if (leftName != null || rightName != null) return leftName === rightName;
	return left.computed === right.computed &&
		expressionsEqual(left.key, right.key);
}

function collectObjectRestLiteralKeys(
	object: t.ObjectExpression,
	keys: ObjectRestKey[],
): boolean {
	for (const property of object.properties) {
		if (nullPrototypeProperty(property)) continue;
		if (
			!t.isObjectProperty(property) ||
			!t.isExpression(property.key) ||
			!t.isNumericLiteral(property.value, { value: 0 })
		) return false;
		keys.push({
			key: property.key,
			computed: property.computed,
		});
	}
	return true;
}

function objectAssignNullPrototypeLiteral(
	body: t.Statement[],
	expression: t.CallExpression,
	before: number,
): { keys: ObjectRestKey[]; protocolIndices: Set<number> } | null {
	if (!callMatches(expression, 'Object', 'assign')) return null;
	if (
		expression.arguments.length !== 2 ||
		!t.isExpression(expression.arguments[0]) ||
		!t.isObjectExpression(expression.arguments[1]) ||
		!callMatches(expression.arguments[0], 'Object', 'create')
	) return null;
	const create = expression.arguments[0] as t.CallExpression;
	if (
		create.arguments.length !== 1 ||
		!t.isExpression(create.arguments[0])
	) return null;
	const parent = resolveLinearAlias(body, create.arguments[0], before);
	if (!t.isNullLiteral(parent.expression)) return null;
	const keys: ObjectRestKey[] = [];
	if (!collectObjectRestLiteralKeys(expression.arguments[1], keys)) {
		return null;
	}
	return {
		keys,
		protocolIndices: new Set(parent.declarationIndices),
	};
}

function nullPrototypeProperty(
	property: t.ObjectExpression['properties'][number],
): boolean {
	return t.isObjectProperty(property) && !property.computed &&
		t.isIdentifier(property.key, { name: '__proto__' }) &&
		t.isNullLiteral(property.value);
}

function callMatches(
	expression: t.Expression,
	object: string,
	property: string,
) {
	return t.isCallExpression(expression) &&
		t.isMemberExpression(expression.callee, { computed: false }) &&
		t.isIdentifier(expression.callee.object, { name: object }) &&
		t.isIdentifier(expression.callee.property, { name: property });
}

function copyDataPropertiesArguments(
	expression: t.Node,
): [t.Expression, t.Expression, t.Expression] | null {
	if (
		!t.isCallExpression(expression) ||
		!callMatches(
			expression,
			'HermesInternal',
			'copyDataProperties',
		) ||
		expression.arguments.length !== 3 ||
		!t.isExpression(expression.arguments[0]) ||
		!t.isExpression(expression.arguments[1]) ||
		!t.isExpression(expression.arguments[2])
	) return null;
	return expression.arguments as [t.Expression, t.Expression, t.Expression];
}

function copyDataPropertiesDeclaration(
	stmt: t.Statement | undefined,
): {
	result: t.Identifier;
	call: t.CallExpression;
	arguments: [t.Expression, t.Expression, t.Expression];
} | null {
	const declaration = singleDeclarator(stmt, 'const');
	if (
		!declaration || !t.isIdentifier(declaration.id) ||
		!t.isCallExpression(declaration.init)
	) return null;
	const args = copyDataPropertiesArguments(declaration.init);
	if (!args) return null;
	return {
		result: declaration.id,
		call: declaration.init,
		arguments: args,
	};
}

interface ObjectRestExclusionPlan {
	keys: ObjectRestKey[];
	mapNames: Set<string>;
	protocolIndices: Set<number>;
}

/**
 * Recover either exclusion-map encoding emitted by Hermes:
 *
 *   const map = Object.create(null); map.key = 0;
 *   const map = { key: 0 }; silentSetPrototypeOf(map, null);
 *   Object.assign(Object.create(null), { key: 0 })
 *
 * A `{ __proto__: null, key: 0 }` map is the same second form after the
 * null-prototype peephole has run once.
 */
function objectRestExclusionPlan(
	body: t.Statement[],
	excluded: t.Expression,
	helperIndex: number,
): ObjectRestExclusionPlan | null {
	if (t.isObjectExpression(excluded)) {
		const keys: ObjectRestKey[] = [];
		let hasNullPrototype = false;
		for (const property of excluded.properties) {
			if (nullPrototypeProperty(property)) {
				hasNullPrototype = true;
				continue;
			}
			if (
				!t.isObjectProperty(property) ||
				!t.isExpression(property.key) ||
				!t.isNumericLiteral(property.value, { value: 0 })
			) return null;
			keys.push({
				key: property.key,
				computed: property.computed,
			});
		}
		return hasNullPrototype && keys.length > 0
			? {
				keys,
				mapNames: new Set<string>(),
				protocolIndices: new Set<number>(),
			}
			: null;
	}
	if (t.isCallExpression(excluded)) {
		const assigned = objectAssignNullPrototypeLiteral(
			body,
			excluded,
			helperIndex,
		);
		return assigned && assigned.keys.length > 0
			? {
				keys: assigned.keys,
				mapNames: new Set<string>(),
				protocolIndices: assigned.protocolIndices,
			}
			: null;
	}
	if (!t.isIdentifier(excluded)) return null;
	const resolved = resolveLinearAlias(body, excluded, helperIndex);
	if (resolved.rootName == null || resolved.rootIndex == null) return null;
	const rootName = resolved.rootName;
	const mapNames = new Set<string>([rootName, excluded.name]);
	for (const index of resolved.declarationIndices) {
		const declaration = singleDeclarator(body[index], 'const');
		if (declaration && t.isIdentifier(declaration.id)) {
			mapNames.add(declaration.id.name);
		}
	}

	const protocolIndices = new Set<number>(resolved.declarationIndices);
	const keys: ObjectRestKey[] = [];
	let hasNullPrototype = false;
	if (t.isObjectExpression(resolved.expression)) {
		for (const property of resolved.expression.properties) {
			if (nullPrototypeProperty(property)) {
				hasNullPrototype = true;
				continue;
			}
			if (
				!t.isObjectProperty(property) ||
				!t.isExpression(property.key) ||
				!t.isNumericLiteral(property.value, { value: 0 })
			) return null;
			keys.push({
				key: property.key,
				computed: property.computed,
			});
		}
	} else if (
		t.isCallExpression(resolved.expression) &&
		callMatches(resolved.expression, 'Object', 'create') &&
		resolved.expression.arguments.length === 1 &&
		t.isExpression(resolved.expression.arguments[0])
	) {
		const parent = resolveLinearAlias(
			body,
			resolved.expression.arguments[0],
			resolved.rootIndex,
		);
		if (!t.isNullLiteral(parent.expression)) return null;
		hasNullPrototype = true;
		for (const index of parent.declarationIndices) {
			protocolIndices.add(index);
		}
	} else if (t.isCallExpression(resolved.expression)) {
		const assigned = objectAssignNullPrototypeLiteral(
			body,
			resolved.expression,
			resolved.rootIndex,
		);
		if (!assigned) return null;
		keys.push(...assigned.keys);
		for (const index of assigned.protocolIndices) {
			protocolIndices.add(index);
		}
		hasNullPrototype = true;
	} else return null;

	for (let i = resolved.rootIndex + 1; i < helperIndex; i++) {
		const assignment = expressionStatementAssignment(body[i]);
		if (
			assignment &&
			t.isMemberExpression(assignment.left) &&
			t.isIdentifier(assignment.left.object) &&
			mapNames.has(assignment.left.object.name) &&
			t.isExpression(assignment.left.property) &&
			t.isExpression(assignment.right)
		) {
			const zero = resolveLinearAlias(body, assignment.right, i);
			if (!t.isNumericLiteral(zero.expression, { value: 0 })) return null;
			keys.push({
				key: assignment.left.property,
				computed: assignment.left.computed,
			});
			protocolIndices.add(i);
			for (const index of zero.declarationIndices) {
				protocolIndices.add(index);
			}
			continue;
		}

		const stmt = body[i];
		if (!t.isExpressionStatement(stmt)) continue;
		const expression = stmt.expression;
		if (
			!callMatches(
				expression,
				'HermesInternal',
				'silentSetPrototypeOf',
			)
		) continue;
		const call = expression as t.CallExpression;
		if (
			call.arguments.length !== 2 ||
			!t.isIdentifier(call.arguments[0]) ||
			!mapNames.has(call.arguments[0].name) ||
			!t.isNullLiteral(call.arguments[1])
		) return null;
		hasNullPrototype = true;
		protocolIndices.add(i);
	}

	if (!hasNullPrototype || keys.length === 0) return null;
	return { keys, mapNames, protocolIndices };
}

function emptyCopyTargetPlan(
	body: t.Statement[],
	target: t.Expression,
	helperIndex: number,
) {
	if (t.isObjectExpression(target) && target.properties.length === 0) {
		// Generic register inlining can substitute the fresh helper target before
		// this protocol pass gets another turn, leaving its now-dead allocation
		// immediately before the call. Retain that exact provenance so the closed
		// span does not mistake the helper's own target for user computation.
		const priorIndex = helperIndex - 1;
		const prior = singleDeclarator(body[priorIndex], 'const');
		const priorName = prior && t.isIdentifier(prior.id)
			? prior.id.name
			: null;
		if (
			prior && priorName != null &&
			isGeneratedName(priorName) &&
			t.isObjectExpression(prior.init) &&
			prior.init.properties.length === 0 &&
			!body.some((statement, index) =>
				index !== priorIndex &&
				countIdentifierUses(statement, priorName) > 0
			)
		) {
			return {
				names: new Set<string>([priorName]),
				indices: new Set<number>([priorIndex]),
			};
		}
		return { names: new Set<string>(), indices: new Set<number>() };
	}
	if (!t.isIdentifier(target)) return null;
	const resolved = resolveLinearAlias(body, target, helperIndex);
	if (
		!t.isObjectExpression(resolved.expression) ||
		resolved.expression.properties.length !== 0
	) return null;
	const names = new Set<string>([target.name]);
	for (const index of resolved.declarationIndices) {
		const declaration = singleDeclarator(body[index], 'const');
		if (declaration && t.isIdentifier(declaration.id)) {
			names.add(declaration.id.name);
		}
	}
	return {
		names,
		indices: new Set<number>(resolved.declarationIndices),
	};
}

interface ClosedObjectRestProbe {
	index: number;
	declaration: t.VariableDeclarator;
	key: ObjectRestKey;
	patternValue: t.PatternLike;
	protocolIndices: Set<number>;
	replaceAfter?: Array<{
		from: string;
		to: string;
		startIndex: number;
	}>;
	keptIndices?: Set<number>;
}

/**
 * A composed environment-slot declaration can be the storage destination of
 * an extracted property.  It is safe to make that slot the pattern binding
 * when the declaration is an immutable, direct alias of the probe/default
 * value: the property is still read at exactly the same point, while the
 * otherwise-intervening slot store disappears.
 */
function closedObjectRestStorageAlias(
	body: t.Statement[],
	index: number,
	valueName: string,
): { id: t.Identifier; index: number } | null {
	const declaration = singleDeclarator(body[index], 'const');
	if (
		!declaration || !t.isIdentifier(declaration.id) ||
		!t.isIdentifier(declaration.init, { name: valueName }) ||
		locationOf(declaration.id)?.kind !== 'environment-slot'
	) return null;
	return { id: declaration.id, index };
}

/**
 * Before environment materialisation, captured properties are stored through
 * `%expectEnvironment(env)[slot] = value`.  The store is a real side effect and
 * must remain, but it is still part of the object-rest extraction span: the
 * preceding property probe can become the destructuring binding and the store
 * can keep writing that binding into the closure slot.
 */
function closedObjectRestEnvironmentStore(
	body: t.Statement[],
	index: number,
	valueName: string,
): number | null {
	const assignment = expressionStatementAssignment(body[index]);
	if (
		!assignment ||
		!t.isIdentifier(assignment.right, { name: valueName }) ||
		!t.isMemberExpression(assignment.left) ||
		!t.isCallExpression(assignment.left.object) ||
		!t.isV8IntrinsicIdentifier(assignment.left.object.callee, {
			name: 'expectEnvironment',
		})
	) return null;
	return index;
}

function conditionalDefaultValue(
	init: t.Expression,
	sourceName: string,
	aliases: ReadonlySet<string>,
): t.Expression | null {
	if (!t.isConditionalExpression(init)) return null;
	const source = t.identifier(sourceName);
	if (
		isUndefinedStrictEqualityWithAliases(init.test, source, aliases) &&
		t.isIdentifier(init.alternate, { name: sourceName }) &&
		countIdentifierUses(init.consequent, sourceName) === 0
	) return t.cloneNode(init.consequent, true);
	if (
		isNotUndefinedStrictEquality(init.test, source) &&
		t.isIdentifier(init.consequent, { name: sourceName }) &&
		countIdentifierUses(init.alternate, sourceName) === 0
	) return t.cloneNode(init.alternate, true);
	return null;
}

function closedObjectRestConditionalDefaultAlias(
	body: t.Statement[],
	start: number,
	probeName: string,
): {
	target: t.Identifier;
	defaultValue: t.Expression;
	endIndex: number;
	protocolIndices: Set<number>;
	replaceAfter: ClosedObjectRestProbe['replaceAfter'];
} | null {
	const aliases = undefinedAliasNames(body);
	let sourceName = probeName;
	let targetIndex = start;
	const protocolIndices = new Set<number>();
	const alias = singleDeclarator(body[start], 'const');
	if (
		alias &&
		t.isIdentifier(alias.id) &&
		isGeneratedName(alias.id.name) &&
		t.isIdentifier(alias.init, { name: probeName })
	) {
		sourceName = alias.id.name;
		protocolIndices.add(start);
		targetIndex++;
	}

	const target = singleDeclarator(body[targetIndex], 'const');
	if (
		!target ||
		!t.isIdentifier(target.id) ||
		locationOf(target.id)?.kind !== 'environment-slot' ||
		!t.isExpression(target.init)
	) return null;
	const defaultValue = conditionalDefaultValue(
		target.init,
		sourceName,
		aliases,
	);
	if (!defaultValue) return null;

	protocolIndices.add(targetIndex);
	const replaceAfter = [
		{
			from: probeName,
			to: target.id.name,
			startIndex: targetIndex + 1,
		},
	];
	if (sourceName !== probeName) {
		replaceAfter.push({
			from: sourceName,
			to: target.id.name,
			startIndex: targetIndex + 1,
		});
	}
	return {
		target: target.id,
		defaultValue,
		endIndex: targetIndex,
		protocolIndices,
		replaceAfter,
	};
}

function nameOccursOutside(
	body: t.Statement[],
	name: string,
	allowedIndices: ReadonlySet<number>,
): boolean {
	for (let i = 0; i < body.length; i++) {
		if (allowedIndices.has(i)) continue;
		if (countIdentifierUses(body[i], name) > 0) return true;
	}
	return false;
}
function nameOccursOutsideObjectRestProtocol(
	func: Pick<IRFunction, 'blocks'>,
	block: Pick<IRBlock, 'address' | 'branch'>,
	body: t.Statement[],
	name: string,
	allowedIndices: ReadonlySet<number>,
): boolean {
	if (
		nameOccursOutside(body, name, allowedIndices) ||
		(block.branch != null &&
			countIdentifierUses(block.branch as t.Node, name) > 0)
	) return true;
	for (const candidate of func.blocks.values()) {
		const candidateUses = candidate.body.reduce(
			(total, statement) =>
				total + countIdentifierUses(statement as t.Statement, name),
			candidate.branch == null
				? 0
				: countIdentifierUses(candidate.branch as t.Node, name),
		);
		if (candidate.address === block.address) {
			const protocolUses = [...allowedIndices].reduce(
				(total, index) =>
					total +
					(body[index] == null
						? 0
						: countIdentifierUses(body[index], name)),
				0,
			);
			if (candidateUses > protocolUses) return true;
			continue;
		}
		if (candidateUses > 0) return true;
	}
	return false;
}

function replaceIdentifierOutsideFunctions(
	node: t.Node,
	name: string,
	replacement: t.Identifier,
): t.Node {
	if (t.isIdentifier(node, { name })) return t.cloneNode(replacement);
	if (t.isFunction(node)) return node;
	const clone = t.cloneNode(node, false);
	for (const key of t.VISITOR_KEYS[clone.type] ?? []) {
		const child = clone[key as keyof typeof clone];
		if (Array.isArray(child)) {
			(clone as unknown as Record<string, unknown>)[key] = child.map(
				(element) =>
					t.isNode(element)
						? replaceIdentifierOutsideFunctions(
							element,
							name,
							replacement,
						)
						: element,
			);
		} else if (t.isNode(child)) {
			(clone as unknown as Record<string, unknown>)[key] =
				replaceIdentifierOutsideFunctions(child, name, replacement);
		}
	}
	return clone;
}

/** Recognize the SSA Phi form implementing one destructuring default. */
function closedObjectRestProbe(
	body: t.Statement[],
	index: number,
	declaration: t.VariableDeclarator,
	key: ObjectRestKey,
): ClosedObjectRestProbe {
	const direct: ClosedObjectRestProbe = {
		index,
		declaration,
		key,
		patternValue: t.cloneNode(declaration.id) as t.PatternLike,
		protocolIndices: new Set([index]),
	};
	if (
		!t.isIdentifier(declaration.id) ||
		!t.isMemberExpression(declaration.init)
	) {
		return direct;
	}
	const probeName = declaration.id.name;
	const conditionalDefault = closedObjectRestConditionalDefaultAlias(
		body,
		index + 1,
		probeName,
	);
	if (conditionalDefault) {
		return {
			...direct,
			patternValue: t.assignmentPattern(
				t.cloneNode(conditionalDefault.target),
				t.cloneNode(conditionalDefault.defaultValue, true),
			),
			protocolIndices: new Set([
				index,
				...conditionalDefault.protocolIndices,
			]),
			replaceAfter: conditionalDefault.replaceAfter,
		};
	}
	const keptStore = closedObjectRestEnvironmentStore(
		body,
		index + 1,
		probeName,
	);
	const carried = singleDeclarator(body[index + 1], 'let');
	if (!carried || !t.isIdentifier(carried.id)) {
		const storage = closedObjectRestStorageAlias(
			body,
			index + 1,
			probeName,
		);
		if (!storage) {
			return keptStore == null
				? direct
				: { ...direct, keptIndices: new Set([keptStore]) };
		}
		return {
			...direct,
			patternValue: t.cloneNode(storage.id),
			protocolIndices: new Set([index, storage.index]),
			replaceAfter: [{
				from: probeName,
				to: storage.id.name,
				startIndex: storage.index + 1,
			}],
		};
	}
	const carriedName = carried.id.name;
	let guardIndex = index + 2;
	if (carried.init == null) {
		const initial = assignmentToIdentifier(body[guardIndex], carriedName);
		if (!initial || !t.isIdentifier(initial.right, { name: probeName })) {
			return direct;
		}
		guardIndex++;
	} else if (!t.isIdentifier(carried.init, { name: probeName })) {
		return direct;
	}

	const guard = body[guardIndex];
	if (
		!t.isIfStatement(guard) || guard.alternate ||
		!t.isBlockStatement(guard.consequent) ||
		!(
			isUndefinedStrictEqualityWithAliases(
				guard.test,
				t.identifier(probeName),
				undefinedAliasNames(body),
			) ||
			(t.isExpression(declaration.init) &&
				isUndefinedStrictEqualityWithAliases(
					guard.test,
					declaration.init,
					undefinedAliasNames(body),
				))
		)
	) return direct;
	const fallback = defaultAssignmentInBlock(guard.consequent, carriedName);
	if (!fallback) return direct;

	const protocolIndices = new Set([index, index + 1, guardIndex]);
	if (guardIndex !== index + 2) protocolIndices.add(index + 2);
	const storage = closedObjectRestStorageAlias(
		body,
		guardIndex + 1,
		carriedName,
	);
	if (storage) protocolIndices.add(storage.index);
	return {
		index,
		declaration,
		key,
		patternValue: t.assignmentPattern(
			t.cloneNode(storage?.id ?? carried.id),
			t.cloneNode(fallback.value, true),
		),
		protocolIndices,
		replaceAfter: storage
			? [
				{
					from: probeName,
					to: storage.id.name,
					startIndex: storage.index + 1,
				},
				{
					from: carriedName,
					to: storage.id.name,
					startIndex: storage.index + 1,
				},
			]
			: [{
				from: probeName,
				to: carriedName,
				startIndex: guardIndex + 1,
			}],
	};
}

/**
 * Recover a closed object-rest protocol before generic register inlining can
 * erase its property probes. Besides direct probes, this consumes the exact
 * let/assignment/if Phi shape implementing a destructuring default. Only
 * compiler-owned identity aliases, zero/null constants, fresh helper targets,
 * exclusion-map operations and those property/default probes may occur in the
 * span. Any genuine declaration, assignment, call or control flow leaves the
 * helper untouched.
 */
function cleanupClosedObjectRestProtocol(
	func: Pick<IRFunction, 'blocks' | 'recordBindingCleanupObservation'>,
	block: Pick<IRBlock, 'address' | 'branch'>,
	body: t.Statement[],
): boolean {
	for (let helperIndex = 0; helperIndex < body.length; helperIndex++) {
		const helper = copyDataPropertiesDeclaration(body[helperIndex]);
		if (!helper) continue;
		const [targetArg, sourceArg, excludedArg] = helper.arguments;
		const target = emptyCopyTargetPlan(body, targetArg, helperIndex);
		if (!target) continue;
		const exclusion = objectRestExclusionPlan(
			body,
			excludedArg,
			helperIndex,
		);
		if (!exclusion) continue;
		const source = resolveLinearAlias(body, sourceArg, helperIndex);

		const probes: ClosedObjectRestProbe[] = [];
		for (let i = 0; i < helperIndex; i++) {
			const declaration = singleDeclarator(body[i], 'const');
			if (
				!declaration || !t.isIdentifier(declaration.id) ||
				!t.isMemberExpression(declaration.init) ||
				!t.isExpression(declaration.init.object) ||
				!t.isExpression(declaration.init.property)
			) continue;
			const probeSource = resolveLinearAlias(
				body,
				declaration.init.object,
				i,
			);
			if (!expressionsEqual(probeSource.expression, source.expression)) {
				continue;
			}
			const key = {
				key: declaration.init.property,
				computed: declaration.init.computed,
			};
			if (
				!exclusion.keys.some((candidate) =>
					objectRestKeysEqual(candidate, key)
				)
			) continue;
			probes.push(closedObjectRestProbe(body, i, declaration, key));
		}
		if (probes.length !== exclusion.keys.length || probes.length === 0) {
			continue;
		}
		if (
			exclusion.keys.some((key) =>
				probes.filter((probe) => objectRestKeysEqual(probe.key, key))
					.length !== 1
			)
		) continue;

		const allowedIndices = new Set<number>([
			helperIndex,
			...target.indices,
			...exclusion.protocolIndices,
			...source.declarationIndices,
			...probes.flatMap((probe) => [...probe.protocolIndices]),
			...probes.flatMap((probe) => [...(probe.keptIndices ?? [])]),
		]);
		const earliestProbe = probes[0].index;
		let closed = true;
		for (let i = earliestProbe; i <= helperIndex; i++) {
			if (allowedIndices.has(i)) continue;
			const statement = body[i];
			const declaration = t.isVariableDeclaration(statement)
				? statement
				: null;
			const expression = t.isExpressionStatement(statement)
				? statement.expression
				: null;
			const blocker = declaration
				? 'object-rest-intervening-declaration'
				: t.isIfStatement(statement) ||
						t.isSwitchStatement(statement) ||
						t.isTryStatement(statement) || t.isLoop(statement)
				? 'object-rest-intervening-control'
				: t.isAssignmentExpression(expression) ||
						t.isUpdateExpression(expression)
				? 'object-rest-intervening-storage-write'
				: t.isCallExpression(expression) ||
						t.isNewExpression(expression) ||
						t.isAwaitExpression(expression) ||
						t.isYieldExpression(expression)
				? 'object-rest-intervening-call'
				: 'object-rest-intervening-effect';
			func.recordBindingCleanupObservation(
				blocker,
				`${block.address}:${helperIndex}:${i}`,
			);
			debugObjDestr('closed object-rest blocker', {
				helperIndex,
				index: i,
				type: statement.type,
				declaration: declaration?.declarations.map((declarator) => ({
					name: t.isIdentifier(declarator.id)
						? declarator.id.name
						: declarator.id.type,
					init: declarator.init?.type,
				})),
			});
			closed = false;
			break;
		}
		if (!closed) continue;

		for (const name of [...target.names, ...exclusion.mapNames]) {
			if (
				nameOccursOutsideObjectRestProtocol(
					func,
					block,
					body,
					name,
					allowedIndices,
				)
			) {
				closed = false;
				break;
			}
		}
		if (!closed) continue;
		const removableSourceIndices = new Set<number>();
		for (const index of source.declarationIndices) {
			const declaration = singleDeclarator(body[index], 'const');
			if (
				declaration && t.isIdentifier(declaration.id) &&
				!nameOccursOutside(body, declaration.id.name, allowedIndices)
			) removableSourceIndices.add(index);
		}

		const properties = probes.map((probe) => {
			const property = t.objectProperty(
				t.cloneNode(probe.key.key, true),
				t.cloneNode(probe.patternValue, true),
				probe.key.computed,
			);
			if (
				!property.computed && t.isIdentifier(property.key) &&
				t.isIdentifier(property.value, { name: property.key.name })
			) property.shorthand = true;
			return property;
		});
		const pattern = t.objectPattern([
			...properties,
			t.restElement(t.cloneNode(helper.result)),
		]);
		for (const probe of probes) {
			if (!probe.replaceAfter) continue;
			for (const replacement of probe.replaceAfter) {
				for (let i = replacement.startIndex; i < body.length; i++) {
					body[i] = replaceIdentifierOutsideFunctions(
						body[i],
						replacement.from,
						t.identifier(replacement.to),
					) as t.Statement;
				}
			}
		}
		body[earliestProbe] = t.variableDeclaration('const', [
			t.variableDeclarator(
				pattern,
				t.cloneNode(source.expression, true),
			),
		]);

		const removableProtocolIndices = [...exclusion.protocolIndices].filter(
			(index) => {
				const statement = body[index];
				if (!t.isVariableDeclaration(statement)) return true;
				return statement.declarations.every((declaration) =>
					t.isIdentifier(declaration.id) &&
					!nameOccursOutsideObjectRestProtocol(
						func,
						block,
						body,
						declaration.id.name,
						allowedIndices,
					)
				);
			},
		);
		const remove = new Set<number>([
			helperIndex,
			...target.indices,
			...removableProtocolIndices,
			...removableSourceIndices,
			...probes.flatMap((probe) => [...probe.protocolIndices]),
		]);
		remove.delete(earliestProbe);
		for (const index of [...remove].sort((a, b) => b - a)) {
			body.splice(index, 1);
		}
		func.recordBindingCleanupObservation(
			'object-rest-recovered',
			`${block.address}:${helperIndex}`,
		);
		return true;
	}
	return false;
}

function statementNames(body: t.Statement[]): Set<string> {
	const names = new Set<string>();
	const visit = (node: t.Node): void => {
		if (t.isIdentifier(node)) names.add(node.name);
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const child = node[key as keyof typeof node];
			if (Array.isArray(child)) {
				for (const element of child) {
					if (t.isNode(element)) visit(element);
				}
			} else if (t.isNode(child)) {
				visit(child);
			}
		}
	};
	for (const statement of body) visit(statement);
	return names;
}

function uniqueObjectRestIdentifier(
	source: t.Expression,
	key: string,
	used: Set<string>,
): t.Identifier {
	const sourceMatch = t.isIdentifier(source)
		? /^_param_(\d+)_(\d+)_$/.exec(source.name)
		: null;
	const hint = t.toIdentifier(key) || 'property';
	const prefix = sourceMatch
		? `_${hint}_${sourceMatch[1]}_${sourceMatch[2]}_`
		: `_${hint}`;
	let name = prefix;
	let ordinal = 1;
	while (used.has(name)) name = `${prefix}${ordinal++}`;
	used.add(name);
	return t.identifier(name);
}

function uniqueObjectRestBinding(
	source: t.Expression,
	used: Set<string>,
): t.Identifier {
	const sourceMatch = t.isIdentifier(source)
		? /^_param_(\d+)_(\d+)_$/.exec(source.name)
		: null;
	const prefix = sourceMatch
		? `_rest_${sourceMatch[1]}_${sourceMatch[2]}_`
		: '_rest';
	let name = prefix;
	let ordinal = 1;
	while (used.has(name)) name = `${prefix}${ordinal++}`;
	used.add(name);
	return t.identifier(name);
}

function findEmbeddedObjectRestCopy(
	statement: t.Statement,
): {
	call: t.CallExpression;
	arguments: [t.Expression, t.Expression, t.Expression];
} | null {
	let found:
		| {
			call: t.CallExpression;
			arguments: [t.Expression, t.Expression, t.Expression];
		}
		| null = null;
	let count = 0;
	const visit = (node: t.Node, parent: t.Node | null): void => {
		if (t.isFunction(node)) return;
		const args = copyDataPropertiesArguments(node);
		if (args && parent && t.isSpreadElement(parent)) {
			found = { call: node as t.CallExpression, arguments: args };
			count++;
			return;
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const child = node[key as keyof typeof node];
			if (Array.isArray(child)) {
				for (const element of child) {
					if (t.isNode(element)) visit(element, node);
				}
			} else if (t.isNode(child)) {
				visit(child, node);
			}
		}
	};
	visit(statement, null);
	return count === 1 ? found : null;
}

function replaceSpecificNodeOutsideFunctions(
	node: t.Node,
	target: t.Node,
	replacement: t.Node,
): t.Node {
	if (node === target) return t.cloneNode(replacement, true);
	if (t.isFunction(node)) return node;
	const clone = t.cloneNode(node, false);
	for (const key of t.VISITOR_KEYS[clone.type] ?? []) {
		const child = clone[key as keyof typeof clone];
		if (Array.isArray(child)) {
			(clone as unknown as Record<string, unknown>)[key] = child.map(
				(element) =>
					t.isNode(element)
						? replaceSpecificNodeOutsideFunctions(
							element,
							target,
							replacement,
						)
						: element,
			);
		} else if (t.isNode(child)) {
			(clone as unknown as Record<string, unknown>)[key] =
				replaceSpecificNodeOutsideFunctions(child, target, replacement);
		}
	}
	return clone;
}

function replaceObjectRestMemberReads(
	node: t.Node,
	source: t.Expression,
	key: ObjectRestKey,
	replacement: t.Expression,
): { node: t.Node; replaced: number; unsafe: boolean } {
	let replaced = 0;
	let unsafe = false;
	const visit = (current: t.Node, parent: t.Node | null): t.Node => {
		if (t.isFunction(current)) return current;
		if (
			t.isMemberExpression(current) &&
			t.isExpression(current.object) &&
			t.isExpression(current.property) &&
			expressionsEqual(current.object, source) &&
			objectRestKeysEqual(
				{ key: current.property, computed: current.computed },
				key,
			)
		) {
			if (
				(t.isAssignmentExpression(parent) && parent.left === current) ||
				(t.isUpdateExpression(parent) && parent.argument === current) ||
				(t.isCallExpression(parent) && parent.callee === current)
			) {
				unsafe = true;
				return current;
			}
			replaced++;
			return t.cloneNode(replacement, true);
		}
		const clone = t.cloneNode(current, false);
		for (const childKey of t.VISITOR_KEYS[clone.type] ?? []) {
			const child = clone[childKey as keyof typeof clone];
			if (Array.isArray(child)) {
				(clone as unknown as Record<string, unknown>)[childKey] = child
					.map((element) =>
						t.isNode(element) ? visit(element, clone) : element
					);
			} else if (t.isNode(child)) {
				(clone as unknown as Record<string, unknown>)[childKey] = visit(
					child,
					clone,
				);
			}
		}
		return clone;
	};
	return { node: visit(node, null), replaced, unsafe };
}

function cleanupEmbeddedObjectRestProtocol(
	func: Pick<IRFunction, 'recordBindingCleanupObservation'>,
	block: Pick<IRBlock, 'address'>,
	body: t.Statement[],
): boolean {
	for (let helperIndex = 0; helperIndex < body.length; helperIndex++) {
		const helper = findEmbeddedObjectRestCopy(body[helperIndex]);
		if (!helper) continue;
		const [targetArg, sourceArg, excludedArg] = helper.arguments;
		if (
			!t.isObjectExpression(targetArg) ||
			targetArg.properties.length !== 0 ||
			!t.isIdentifier(sourceArg)
		) continue;
		const exclusion = objectRestExclusionPlan(
			body,
			excludedArg,
			helperIndex,
		);
		if (!exclusion) continue;

		const probes = new Map<string, ClosedObjectRestProbe>();
		let duplicateProbe = false;
		for (let i = 0; i < helperIndex; i++) {
			const declaration = singleDeclarator(body[i], 'const');
			if (
				!declaration || !t.isIdentifier(declaration.id) ||
				!t.isMemberExpression(declaration.init) ||
				!t.isExpression(declaration.init.object) ||
				!t.isExpression(declaration.init.property) ||
				!expressionsEqual(declaration.init.object, sourceArg)
			) continue;
			const key = {
				key: declaration.init.property,
				computed: declaration.init.computed,
			};
			const excluded = exclusion.keys.find((candidate) =>
				objectRestKeysEqual(candidate, key)
			);
			if (!excluded) continue;
			const name = staticPropertyName(excluded.key, excluded.computed);
			if (name == null || probes.has(name)) {
				duplicateProbe = true;
				break;
			}
			probes.set(name, closedObjectRestProbe(body, i, declaration, key));
		}
		if (duplicateProbe) continue;

		const allowedIndices = new Set<number>([
			helperIndex,
			...exclusion.protocolIndices,
			...Array.from(probes.values()).flatMap((probe) => [
				...probe.protocolIndices,
			]),
			...Array.from(probes.values()).flatMap((probe) => [
				...(probe.keptIndices ?? []),
			]),
		]);
		const probeIndices = Array.from(probes.values()).map((probe) =>
			probe.index
		);
		const insertIndex = probeIndices.length === 0
			? helperIndex
			: Math.min(...probeIndices);
		let closed = true;
		for (let i = insertIndex; i <= helperIndex; i++) {
			if (allowedIndices.has(i)) continue;
			const statement = body[i];
			const blocker = t.isVariableDeclaration(statement)
				? 'object-rest-embedded-intervening-declaration'
				: t.isIfStatement(statement) ||
						t.isSwitchStatement(statement) ||
						t.isTryStatement(statement) || t.isLoop(statement)
				? 'object-rest-embedded-intervening-control'
				: 'object-rest-embedded-intervening-effect';
			func.recordBindingCleanupObservation(
				blocker,
				`${block.address}:${helperIndex}:${i}`,
			);
			closed = false;
			break;
		}
		if (!closed) continue;

		const used = statementNames(body);
		const restBinding = uniqueObjectRestBinding(sourceArg, used);
		let transformed = replaceSpecificNodeOutsideFunctions(
			body[helperIndex],
			helper.call,
			restBinding,
		) as t.Statement;
		const laterReplacements = new Map<number, t.Statement>();
		const properties: t.ObjectPattern['properties'] = [];
		let invalid = false;
		for (const key of exclusion.keys) {
			const name = staticPropertyName(key.key, key.computed);
			if (name == null) {
				invalid = true;
				break;
			}
			const probe = probes.get(name);
			const binding = probe?.patternValue ??
				uniqueObjectRestIdentifier(sourceArg, name, used);
			if (t.isExpression(binding)) {
				const replacement = replaceObjectRestMemberReads(
					transformed,
					sourceArg,
					key,
					binding,
				);
				if (replacement.unsafe) {
					invalid = true;
					break;
				}
				transformed = replacement.node as t.Statement;
				for (let i = helperIndex + 1; i < body.length; i++) {
					const later = replaceObjectRestMemberReads(
						laterReplacements.get(i) ?? body[i],
						sourceArg,
						key,
						binding,
					);
					if (later.unsafe) {
						invalid = true;
						break;
					}
					laterReplacements.set(i, later.node as t.Statement);
				}
				if (invalid) break;
			}
			const property = t.objectProperty(
				t.cloneNode(key.key, true),
				t.cloneNode(binding, true),
				key.computed,
			);
			if (
				!property.computed && t.isIdentifier(property.key) &&
				t.isIdentifier(property.value, { name: property.key.name })
			) property.shorthand = true;
			properties.push(property);
		}
		if (invalid) continue;

		properties.push(t.restElement(restBinding));
		for (const probe of probes.values()) {
			if (!probe.replaceAfter) continue;
			for (const replacement of probe.replaceAfter) {
				for (let i = replacement.startIndex; i < body.length; i++) {
					const rewritten = replaceIdentifierOutsideFunctions(
						i === helperIndex
							? transformed
							: laterReplacements.get(i) ?? body[i],
						replacement.from,
						t.identifier(replacement.to),
					) as t.Statement;
					if (i === helperIndex) {
						transformed = rewritten;
					} else {
						laterReplacements.set(i, rewritten);
					}
				}
			}
		}

		for (const [index, statement] of laterReplacements) {
			body[index] = statement;
		}
		body[helperIndex] = transformed;
		const destructuring = t.variableDeclaration('const', [
			t.variableDeclarator(
				t.objectPattern(properties),
				t.cloneNode(sourceArg, true),
			),
		]);
		if (insertIndex === helperIndex) {
			body.splice(helperIndex, 0, destructuring);
		} else {
			body[insertIndex] = destructuring;
			const remove = new Set<number>(
				Array.from(probes.values()).flatMap((probe) => [
					...probe.protocolIndices,
				]),
			);
			remove.delete(insertIndex);
			for (const index of [...remove].sort((a, b) => b - a)) {
				body.splice(index, 1);
			}
		}
		func.recordBindingCleanupObservation(
			'object-rest-embedded-recovered',
			`${block.address}:${helperIndex}`,
		);
		return true;
	}
	return false;
}

/**
 * Re-run the closed object-rest recognizer after environment materialisation.
 * At this point `%expectEnvironment(handle)[slot] = value` has become a tagged
 * lexical declaration, so an immutable captured property can finally become
 * the destructuring binding itself. Function bodies are handled independently
 * by the caller; this helper only descends through structured statement lists.
 */
export function cleanupComposedObjectRestInBody(body: t.Statement[]): number {
	let recovered = 0;
	const block = {
		address: 0,
		body,
		consequentAddresses: [],
		kind: 'normal',
	} as IRBlock;
	const observer = {
		blocks: new AddressMap([[0, block]]),
		recordBindingCleanupObservation() {},
	};
	let changed = false;
	do {
		changed = rewriteStructuredStatementLists(body, (statements) => {
			if (cleanupClosedObjectRestProtocol(observer, block, statements)) {
				recovered++;
				return true;
			}
			if (
				cleanupEmbeddedObjectRestProtocol(observer, block, statements)
			) {
				recovered++;
				return true;
			}
			return false;
		});
	} while (changed);
	return recovered;
}

/**
 * Record the surface shape of object-rest helpers which remain in the selected
 * recursive-CFG program after all focused recovery passes have run.
 *
 * The closed-span recognizer above can explain a helper it actively rejects,
 * but some helpers have already been embedded into an object spread or a
 * target mutation by the time the final Region is selected. Recording that
 * boundary keeps those misses visible without making the recognizer accept
 * intervening declarations, writes, or calls.
 */
export function recordResidualObjectRestTelemetry(
	func: IRFunction,
	root: t.Node,
): void {
	let ordinal = 0;
	const walk = (node: t.Node, parent: t.Node | null): void => {
		if (
			t.isCallExpression(node) &&
			t.isMemberExpression(node.callee, { computed: false }) &&
			t.isIdentifier(node.callee.object, { name: 'HermesInternal' }) &&
			t.isIdentifier(node.callee.property, {
				name: 'copyDataProperties',
			})
		) {
			const identity = String(ordinal++);
			func.recordBindingCleanupObservation(
				'object-rest-residual',
				identity,
			);
			const context = t.isSpreadElement(parent)
				? 'object-rest-residual-embedded-spread'
				: t.isVariableDeclarator(parent) && parent.init === node
				? 'object-rest-residual-declaration'
				: t.isCallExpression(parent)
				? 'object-rest-residual-nested-helper'
				: t.isExpressionStatement(parent)
				? 'object-rest-residual-target-mutation'
				: 'object-rest-residual-expression';
			func.recordBindingCleanupObservation(context, identity);

			const exclusion = node.arguments[2];
			if (exclusion != null && !t.isSpreadElement(exclusion)) {
				func.recordBindingCleanupObservation(
					t.isObjectExpression(exclusion)
						? 'object-rest-residual-static-exclusion'
						: 'object-rest-residual-dynamic-exclusion',
					identity,
				);
			}
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const child of value) {
					if (t.isNode(child)) walk(child, node);
				}
			} else if (t.isNode(value)) walk(value, node);
		}
	};
	walk(root, null);
}

/**
 * SSA bindings belonging to a still split object-rest protocol. Keeping the
 * property probes and helper result until CFG reduction joins their blocks lets
 * cleanupClosedObjectRestProtocol materialize one pattern later. This is not a
 * general alias barrier: only bindings owned by a proven three-argument
 * exclusion-map protocol are retained.
 */
export function objectRestProtocolBindingNames(func: IRFunction): Set<string> {
	const protocols: Array<{
		source: t.Expression;
		keys: ObjectRestKey[];
		result: string;
	}> = [];
	for (const block of func.blocks.values()) {
		const body = block.body as t.Statement[];
		for (let i = 0; i < body.length; i++) {
			const helper = copyDataPropertiesDeclaration(body[i]);
			if (!helper) continue;
			const exclusion = objectRestExclusionPlan(
				body,
				helper.arguments[2],
				i,
			);
			if (!exclusion) continue;
			protocols.push({
				source: resolveLinearAlias(body, helper.arguments[1], i)
					.expression,
				keys: exclusion.keys,
				result: helper.result.name,
			});
		}
	}
	if (protocols.length === 0) return new Set();

	const names = new Set(protocols.map((protocol) => protocol.result));
	for (const block of func.blocks.values()) {
		const body = block.body as t.Statement[];
		for (let i = 0; i < body.length; i++) {
			const declaration = singleDeclarator(body[i], 'const');
			if (
				!declaration || !t.isIdentifier(declaration.id) ||
				!t.isMemberExpression(declaration.init) ||
				!t.isExpression(declaration.init.object) ||
				!t.isExpression(declaration.init.property)
			) continue;
			const rawSource = declaration.init.object;
			const source = resolveLinearAlias(
				body,
				rawSource,
				i,
			).expression;
			const key = {
				key: declaration.init.property,
				computed: declaration.init.computed,
			};
			if (
				protocols.some((protocol) =>
					(
						expressionsEqual(protocol.source, source) ||
						expressionsEqual(
							protocol.source,
							rawSource,
						)
					) &&
					protocol.keys.some((candidate) =>
						objectRestKeysEqual(candidate, key)
					)
				)
			) names.add(declaration.id.name);
		}
	}
	debugObjDestr('object-rest probe protection', {
		protocols: protocols.length,
		names: [...names],
	});
	return names;
}

function isExcludedKeyAssignment(
	stmt: t.Statement | undefined,
	excludedName: string,
	key: t.Expression,
) {
	const assign = expressionStatementAssignment(stmt);
	if (!assign) return false;
	if (!t.isMemberExpression(assign.left, { computed: true })) return false;
	if (!t.isIdentifier(assign.left.object, { name: excludedName })) {
		return false;
	}
	if (!t.isExpression(assign.left.property)) return false;
	if (!expressionsEqual(assign.left.property, key)) return false;
	return t.isNumericLiteral(assign.right, { value: 0 });
}

function getCopyDataPropertiesSource(
	expr: t.Expression,
	source: t.Expression,
	excludedName: string,
) {
	if (!t.isCallExpression(expr)) return null;
	const callee = expr.callee;
	if (!t.isMemberExpression(callee, { computed: false })) return null;
	if (!t.isIdentifier(callee.object, { name: 'HermesInternal' })) {
		return null;
	}
	if (!t.isIdentifier(callee.property, { name: 'copyDataProperties' })) {
		return null;
	}
	if (expr.arguments.length !== 3) return null;
	const [targetArg, sourceArg, excludedArg] = expr.arguments;
	if (!t.isObjectExpression(targetArg) || targetArg.properties.length !== 0) {
		return null;
	}
	if (!t.isExpression(sourceArg) || !expressionsEqual(sourceArg, source)) {
		return null;
	}
	if (!t.isIdentifier(excludedArg, { name: excludedName })) return null;
	return sourceArg;
}

function objectDestructureTargetPlan(
	stmt: t.Statement | undefined,
	probeName: string,
	globalNames: Set<string>,
): { plan: TargetPlan; writeTarget: t.Expression; name?: string } | null {
	const assign = expressionStatementAssignment(stmt);
	if (assign && t.isIdentifier(assign.right, { name: probeName })) {
		const target = destructuringAssignmentTarget(
			stmt,
			probeName,
			globalNames,
		);
		if (!target || !t.isExpression(assign.left)) return null;
		return {
			plan: target.target,
			writeTarget: assign.left,
			name: target.name,
		};
	}

	const decl = singleDeclarator(stmt, 'var');
	if (
		decl &&
		t.isIdentifier(decl.id) &&
		t.isIdentifier(decl.init, { name: probeName })
	) {
		return {
			plan: bindingTarget(decl.id.name, false),
			writeTarget: decl.id,
			name: decl.id.name,
		};
	}

	return null;
}

function targetPlansEqual(left: TargetPlan, right: TargetPlan): boolean {
	if (left.kind !== right.kind) return false;
	if (left.kind === 'binding' && right.kind === 'binding') {
		return left.id.name === right.id.name &&
			left.declaredGlobal === right.declaredGlobal;
	}
	if (left.kind === 'assign' && right.kind === 'assign') {
		return expressionsEqual(
			left.lval as unknown as t.Expression,
			right.lval as unknown as t.Expression,
		);
	}
	return false;
}

function cleanupDirectConditionalObjectRestDefault(
	func: IRFunction,
	block: IRBlock,
	body: t.Statement[],
	globalNames: Set<string>,
): boolean {
	const undefinedNames = undefinedAliasNames(body);
	for (let i = 0; i <= body.length - 6; i++) {
		const probe = singleDeclarator(body[i]);
		if (
			!probe || !t.isIdentifier(probe.id) ||
			!t.isMemberExpression(probe.init) ||
			!t.isExpression(probe.init.object) ||
			!t.isExpression(probe.init.property)
		) continue;

		const defaultTarget = assignmentTargetPlan(body[i + 1], globalNames);
		if (!defaultTarget) continue;
		const defaultValue = conditionalDefaultValue(
			defaultTarget.value,
			probe.id.name,
			undefinedNames,
		);
		if (!defaultValue) continue;

		const excludedName = getObjectCreateNullName(body[i + 2]);
		if (!excludedName) continue;
		if (
			!isExcludedKeyAssignment(
				body[i + 3],
				excludedName,
				probe.init.property,
			)
		) continue;
		const helper = copyDataPropertiesDeclaration(body[i + 4]);
		if (!helper) continue;
		if (
			!getCopyDataPropertiesSource(
				helper.call,
				probe.init.object,
				excludedName,
			)
		) continue;
		const restTarget = assignmentTargetPlan(body[i + 5], globalNames);
		if (
			!restTarget ||
			!t.isIdentifier(restTarget.value, { name: helper.result.name }) ||
			!targetPlansEqual(defaultTarget.target, restTarget.target)
		) continue;

		const property = t.objectProperty(
			t.cloneNode(probe.init.property, true) as t.Expression,
			planToPattern({
				kind: 'target',
				target: defaultTarget.target,
				defaultValue,
			}),
			probe.init.computed,
		);
		const pattern = t.objectPattern([
			property,
			t.restElement(
				targetToPattern(
					restTarget.target,
				) as unknown as RestElementArgument,
			),
		]);
		const consumed = body.slice(i, i + 6);
		const declaredGlobals = new Set<string>();
		for (const target of [defaultTarget, restTarget]) {
			if (
				target.target.kind === 'binding' &&
				target.target.declaredGlobal &&
				target.name
			) declaredGlobals.add(target.name);
		}
		if (
			!consumedDefinitionsAreDead(
				func,
				block,
				consumed,
				[
					probe.init.object,
					probe.init.property,
					defaultValue,
					targetToPattern(defaultTarget.target),
					targetToPattern(restTarget.target),
					t.identifier('undefined'),
					t.identifier('global'),
				],
				[helper.call],
				new Set([...declaredGlobals]),
				false,
				body,
			)
		) continue;

		body.splice(
			i,
			6,
			emitDestructuringPlan({
				pattern,
				source: probe.init.object,
				declaredGlobals,
				consumed,
				preservedInputs: [
					probe.init.object,
					probe.init.property,
					defaultValue,
					targetToPattern(defaultTarget.target),
					targetToPattern(restTarget.target),
				],
				inlineConsumedResults: [helper.call],
			}),
		);
		if (declaredGlobals.size > 0) {
			removeDeclaredGlobals(body, declaredGlobals);
		}
		return true;
	}
	return false;
}

type ObjectDestructurePart = {
	key: t.Expression;
	value: t.PatternLike;
	computed: boolean;
	declaredGlobal: boolean;
	defaultValue?: t.Expression;
};

function stripConsumedExcludedKeyAssignments(body: t.Statement[]): boolean {
	for (let i = 0; i < body.length; i++) {
		const exclName = getObjectCreateNullName(body[i]);
		if (!exclName) continue;

		// Collect all excl[key] = 0 entries that follow
		const entries: { key: t.Expression; idx: number }[] = [];
		let j = i + 1;
		while (j < body.length) {
			const assign = expressionStatementAssignment(body[j]);
			if (
				!assign ||
				!t.isMemberExpression(assign.left, { computed: true }) ||
				!t.isIdentifier(assign.left.object, { name: exclName }) ||
				!t.isExpression(assign.left.property) ||
				!t.isNumericLiteral(assign.right, { value: 0 })
			) break;
			entries.push({ key: assign.left.property, idx: j });
			j++;
		}

		// Only interesting when there's more than one key (single key is already handled)
		if (entries.length < 2) continue;

		// The copyDataProperties call must follow immediately to confirm the source
		const restAssignExpr = expressionStatementAssignment(body[j]);
		if (!restAssignExpr || !t.isExpression(restAssignExpr.right)) continue;
		const copyData = restAssignExpr.right;
		if (
			!t.isCallExpression(copyData) ||
			!t.isMemberExpression(copyData.callee, { computed: false }) ||
			!t.isIdentifier(copyData.callee.object, {
				name: 'HermesInternal',
			}) ||
			!t.isIdentifier(copyData.callee.property, {
				name: 'copyDataProperties',
			}) ||
			copyData.arguments.length !== 3 ||
			!t.isIdentifier(copyData.arguments[2], { name: exclName })
		) continue;
		const src = copyData.arguments[1];
		if (!t.isExpression(src)) continue;

		// Strip any excl[key] = 0 whose probe (let _ = src.key) is no longer in the body
		for (const { key, idx } of [...entries].reverse()) {
			const keyStr = t.isIdentifier(key)
				? key.name
				: t.isStringLiteral(key)
				? key.value
				: null;
			if (keyStr == null) continue;

			const hasProbe = body.slice(0, i).some((stmt) => {
				const decl = singleDeclarator(stmt, 'let');
				if (!decl || !t.isIdentifier(decl.id)) return false;
				if (
					!t.isMemberExpression(decl.init) ||
					!t.isExpression(decl.init.object)
				) {
					return false;
				}
				if (!expressionsEqual(decl.init.object, src as t.Expression)) {
					return false;
				}
				const prop = decl.init.property;
				const propKey = t.isIdentifier(prop)
					? prop.name
					: t.isStringLiteral(prop)
					? prop.value
					: null;
				return propKey === keyStr;
			});

			if (!hasProbe) {
				debugObjDestr('strip consumed excl key', {
					key: keyStr,
					exclName,
					idx,
				});
				body.splice(idx, 1);
				return true;
			}
		}
	}
	return false;
}

function isNotUndefinedStrictEquality(expr: t.Expression, value: t.Expression) {
	if (
		t.isUnaryExpression(expr, { operator: '!' }) &&
		t.isExpression(expr.argument)
	) {
		return isUndefinedStrictEquality(expr.argument, value);
	}
	if (!t.isBinaryExpression(expr, { operator: '!==' })) return false;
	if (!t.isExpression(expr.left)) return false;
	return (
		expressionsEqual(expr.left, value) && isUndefinedNode(expr.right)
	) || (isUndefinedNode(expr.left) && expressionsEqual(expr.right, value));
}

function cleanupSplitObjectRestDefault(
	func: IRFunction,
	block: IRBlock,
	body: t.Statement[],
	globalNames: Set<string>,
): boolean {
	for (let i = 0; i <= body.length - 8; i++) {
		const probeDecl = singleDeclarator(body[i]);
		if (!probeDecl || !t.isIdentifier(probeDecl.id)) continue;
		const probeName = probeDecl.id.name;
		if (!t.isMemberExpression(probeDecl.init)) continue;
		if (!t.isExpression(probeDecl.init.object)) continue;
		if (!t.isExpression(probeDecl.init.property)) continue;
		const sourceObject = probeDecl.init.object;

		let guardIndex = i + 1;
		let defaultValueIndex = i + 1;
		const tempDecl = singleDeclarator(body[guardIndex], 'let');
		if (tempDecl && t.isIdentifier(tempDecl.id) && tempDecl.init == null) {
			const tempName = tempDecl.id.name;
			const tempAssign = assignmentToIdentifier(
				body[guardIndex + 1],
				tempName,
			);
			if (
				!tempAssign ||
				!t.isIdentifier(tempAssign.right, { name: probeName })
			) continue;
			guardIndex += 2;
			defaultValueIndex = guardIndex + 1;
		}

		const guard = body[guardIndex];
		if (
			!t.isIfStatement(guard) ||
			guard.alternate ||
			!t.isBlockStatement(guard.consequent) ||
			!(
				isNotUndefinedStrictEquality(guard.test, probeDecl.init) ||
				isNotUndefinedStrictEquality(
					guard.test,
					t.identifier(probeName),
				)
			)
		) continue;
		const branch = guard.consequent.body;
		const branchTarget = objectDestructureTargetPlan(
			branch[0],
			probeName,
			globalNames,
		);
		if (!branchTarget) continue;
		const branchExcluded = getObjectCreateNullName(branch[1]);
		if (!branchExcluded) continue;
		if (
			!isExcludedKeyAssignment(
				branch[2],
				branchExcluded,
				probeDecl.init.property,
			)
		) continue;
		const branchRest = assignmentToTarget(
			branch[3],
			branchTarget.writeTarget,
		);
		if (!branchRest || !t.isExpression(branchRest.right)) continue;
		if (
			!getCopyDataPropertiesSource(
				branchRest.right,
				sourceObject,
				branchExcluded,
			)
		) continue;

		const defaultTempAssign = expressionStatementAssignment(
			body[defaultValueIndex],
		);
		const defaultTargetIndex = defaultTempAssign &&
				t.isIdentifier(defaultTempAssign.left)
			? defaultValueIndex + 1
			: defaultValueIndex;
		const defaultTargetAssign = assignmentToTarget(
			body[defaultTargetIndex],
			branchTarget.writeTarget,
		);
		if (
			!defaultTargetAssign || !t.isExpression(defaultTargetAssign.right)
		) {
			continue;
		}
		const defaultValue = defaultTargetAssign.right;
		if (
			defaultTempAssign &&
			!expressionsEqual(defaultTempAssign.right, defaultValue)
		) continue;

		const excludedName = getObjectCreateNullName(
			body[defaultTargetIndex + 1],
		);
		if (!excludedName) continue;
		if (
			!isExcludedKeyAssignment(
				body[defaultTargetIndex + 2],
				excludedName,
				probeDecl.init.property,
			)
		) continue;
		const restAssign = assignmentToTarget(
			body[defaultTargetIndex + 3],
			branchTarget.writeTarget,
		);
		if (!restAssign || !t.isExpression(restAssign.right)) continue;
		if (
			!getCopyDataPropertiesSource(
				restAssign.right,
				sourceObject,
				excludedName,
			)
		) continue;

		const objectProperty = t.objectProperty(
			t.cloneNode(probeDecl.init.property, true) as t.Expression,
			planToPattern({
				kind: 'target',
				target: branchTarget.plan,
				defaultValue,
			}),
			probeDecl.init.computed,
		);
		const pattern = t.objectPattern([
			objectProperty,
			t.restElement(
				targetToPattern(
					branchTarget.plan,
				) as unknown as RestElementArgument,
			),
		]);
		const consumedEnd = defaultTargetIndex + 4;
		const consumed = body.slice(i, consumedEnd);
		const originalBranchBody = branch.slice();
		guard.consequent.body = branch.slice(0, 4);
		const declaredGlobals = branchTarget.plan.kind === 'binding' &&
				branchTarget.plan.declaredGlobal && branchTarget.name
			? new Set([branchTarget.name])
			: new Set<string>();
		const consumedDead = consumedDefinitionsAreDead(
			func,
			block,
			consumed,
			[
				sourceObject,
				probeDecl.init.property,
				defaultValue,
				branchTarget.writeTarget,
				t.identifier('undefined'),
				t.identifier('global'),
			],
			[],
			branchTarget.name ? new Set([branchTarget.name]) : new Set(),
			false,
			body,
		);
		guard.consequent.body = originalBranchBody;
		if (!consumedDead) continue;

		body.splice(
			i,
			consumedEnd - i,
			emitDestructuringPlan({
				pattern,
				source: sourceObject,
				declaredGlobals,
				consumed,
				preservedInputs: [
					sourceObject,
					probeDecl.init.property,
					defaultValue,
					branchTarget.writeTarget,
					t.identifier('undefined'),
					t.identifier('global'),
				],
				inlineConsumedResults: [],
			}),
		);
		if (branchTarget.name) {
			removeDeclaredGlobals(body, new Set([branchTarget.name]));
		}
		return true;
	}
	return false;
}

/**
 * Recursive Region emission keeps the property probe separate from the
 * conditional-Phi target:
 *
 *     const probe = source.key;
 *     let value;
 *     value = probe;
 *     if (probe === undefined) value = fallback;
 *     target = value;
 *
 * The older object matcher starts with a mutable probe and therefore cannot
 * see this layout. Recover the same semantic plan while the five statements
 * are still adjacent; liveness proves that removing both generated values is
 * safe.
 */
function cleanupPhiObjectDefault(
	func: IRFunction,
	block: IRBlock,
	body: t.Statement[],
	globalNames: Set<string>,
): boolean {
	const undefinedNames = undefinedAliasNames(body);
	for (let i = 0; i < body.length; i++) {
		const probe = singleDeclarator(body[i]);
		if (
			!probe || !t.isIdentifier(probe.id) ||
			!t.isMemberExpression(probe.init) ||
			!t.isExpression(probe.init.object) ||
			!t.isExpression(probe.init.property)
		) continue;
		const conditionalDefault = closedObjectRestConditionalDefaultAlias(
			body,
			i + 1,
			probe.id.name,
		);
		if (conditionalDefault) {
			const property = t.objectProperty(
				t.cloneNode(probe.init.property, true) as t.Expression,
				t.assignmentPattern(
					t.cloneNode(conditionalDefault.target),
					t.cloneNode(conditionalDefault.defaultValue, true),
				),
				probe.init.computed,
			);
			const consumed = body.slice(i, conditionalDefault.endIndex + 1);
			if (
				!consumedDefinitionsAreDead(
					func,
					block,
					consumed,
					[
						probe.init.object,
						probe.init.property,
						conditionalDefault.defaultValue,
						conditionalDefault.target,
						t.identifier('undefined'),
						t.identifier('global'),
					],
					[],
					new Set([conditionalDefault.target.name]),
					false,
					body,
				)
			) continue;
			body.splice(
				i,
				conditionalDefault.endIndex - i + 1,
				emitDestructuringPlan({
					pattern: t.objectPattern([property]),
					source: probe.init.object,
					declaredGlobals: new Set(),
					consumed,
					preservedInputs: [
						probe.init.object,
						probe.init.property,
						conditionalDefault.defaultValue,
						conditionalDefault.target,
					],
					inlineConsumedResults: [],
				}),
			);
			return true;
		}

		const carried = singleDeclarator(body[i + 1], 'let');
		if (!carried || !t.isIdentifier(carried.id)) continue;
		let guardIndex = i + 2;
		if (carried.init == null) {
			const initial = assignmentToIdentifier(
				body[guardIndex],
				carried.id.name,
			);
			if (
				!initial ||
				!t.isIdentifier(initial.right, { name: probe.id.name })
			) continue;
			guardIndex++;
		} else if (!t.isIdentifier(carried.init, { name: probe.id.name })) {
			continue;
		}

		const guard = body[guardIndex];
		if (
			!t.isIfStatement(guard) || guard.alternate ||
			!t.isBlockStatement(guard.consequent) ||
			!(
				isUndefinedStrictEqualityWithAliases(
					guard.test,
					probe.init,
					undefinedNames,
				) ||
				isUndefinedStrictEqualityWithAliases(
					guard.test,
					t.identifier(probe.id.name),
					undefinedNames,
				)
			)
		) continue;
		const fallback = defaultAssignmentInBlock(
			guard.consequent,
			carried.id.name,
		);
		if (!fallback) continue;

		const targetIndex = guardIndex + 1;
		const target = objectDestructureTargetPlan(
			body[targetIndex],
			carried.id.name,
			globalNames,
		) ?? objectDestructureTargetPlan(
			body[targetIndex],
			probe.id.name,
			globalNames,
		);
		if (!target) continue;

		const property = t.objectProperty(
			t.cloneNode(probe.init.property, true) as t.Expression,
			planToPattern({
				kind: 'target',
				target: target.plan,
				defaultValue: fallback.value,
			}),
			probe.init.computed,
		);
		if (
			!property.computed && t.isIdentifier(property.key) &&
			t.isIdentifier(property.value, { name: property.key.name })
		) property.shorthand = true;

		const consumed = body.slice(i, targetIndex + 1);
		const declaredGlobals = target.plan.kind === 'binding' &&
				target.plan.declaredGlobal && target.name
			? new Set([target.name])
			: new Set<string>();
		if (
			!consumedDefinitionsAreDead(
				func,
				block,
				consumed,
				[
					probe.init.object,
					probe.init.property,
					fallback.value,
					target.writeTarget,
					t.identifier('undefined'),
					t.identifier('global'),
				],
				[],
				target.name ? new Set([target.name]) : new Set(),
				false,
				body,
			)
		) {
			debugObjDestr('phi-default live definitions', {
				probe: probe.id.name,
				carried: carried.id.name,
			});
			continue;
		}

		body.splice(
			i,
			targetIndex - i + 1,
			emitDestructuringPlan({
				pattern: t.objectPattern([property]),
				source: probe.init.object,
				declaredGlobals,
				consumed,
				preservedInputs: [
					probe.init.object,
					probe.init.property,
					fallback.value,
					target.writeTarget,
				],
				inlineConsumedResults: [],
			}),
		);
		if (target.name) removeDeclaredGlobals(body, new Set([target.name]));
		return true;
	}
	return false;
}

function stableDestructuringSource(source: t.Expression): boolean {
	return t.isIdentifier(source) ||
		t.isThisExpression(source) ||
		t.isNullLiteral(source) ||
		t.isStringLiteral(source) ||
		t.isNumericLiteral(source) ||
		t.isBooleanLiteral(source) ||
		t.isBigIntLiteral(source);
}

function recoveredObjectPattern(
	stmt: t.Statement | undefined,
): { pattern: t.ObjectPattern; source: t.Expression } | null {
	const declaration = singleDeclarator(stmt);
	if (
		declaration && t.isObjectPattern(declaration.id) &&
		declaration.init && t.isExpression(declaration.init)
	) {
		return { pattern: declaration.id, source: declaration.init };
	}
	const assign = expressionStatementAssignment(stmt);
	if (
		assign && t.isObjectPattern(assign.left) &&
		t.isExpression(assign.right)
	) {
		return { pattern: assign.left, source: assign.right };
	}
	return null;
}

/**
 * Join an already recovered property/default with Hermes' immediately
 * following object-rest protocol. This shape only becomes visible after the
 * late Phi cleanup, so the older all-at-once recognizer cannot consume it.
 */
function cleanupRecoveredObjectRest(
	body: t.Statement[],
	globalNames: Set<string>,
): boolean {
	for (let i = 0; i <= body.length - 4; i++) {
		const recovered = recoveredObjectPattern(body[i]);
		if (
			!recovered || recovered.pattern.properties.length !== 1 ||
			!stableDestructuringSource(recovered.source)
		) continue;
		const property = recovered.pattern.properties[0];
		if (!t.isObjectProperty(property) || !t.isExpression(property.key)) {
			continue;
		}

		const excludedName = getObjectCreateNullName(body[i + 1]);
		if (!excludedName) continue;
		if (
			!isExcludedKeyAssignment(
				body[i + 2],
				excludedName,
				property.key,
			)
		) continue;
		const rest = assignmentTargetPlan(body[i + 3], globalNames);
		if (!rest) continue;
		if (
			!getCopyDataPropertiesSource(
				rest.value,
				recovered.source,
				excludedName,
			)
		) continue;

		const pattern = t.objectPattern([
			t.cloneNode(property, true) as t.ObjectProperty,
			t.restElement(
				targetToPattern(rest.target) as unknown as RestElementArgument,
			),
		]);
		const declaredGlobals = rest.target.kind === 'binding' &&
				rest.target.declaredGlobal && rest.name
			? new Set([rest.name])
			: new Set<string>();
		body.splice(
			i,
			4,
			emitDestructuringPlan({
				pattern,
				source: recovered.source,
				declaredGlobals,
				consumed: body.slice(i, i + 4),
				preservedInputs: [
					recovered.source,
					property,
					targetToPattern(rest.target),
				],
				inlineConsumedResults: [rest.value],
			}),
		);
		if (rest.name) removeDeclaredGlobals(body, new Set([rest.name]));
		return true;
	}
	return false;
}

function cleanupSequentialObjectDestructuringInBody(
	func: IRFunction,
	block: IRBlock,
	body: t.Statement[],
): boolean {
	if (cleanupClosedObjectRestProtocol(func, block, body)) return true;
	if (cleanupEmbeddedObjectRestProtocol(func, block, body)) return true;
	if (stripConsumedExcludedKeyAssignments(body)) return true;
	const globalNames = collectGlobalNames(body);
	if (
		cleanupDirectConditionalObjectRestDefault(
			func,
			block,
			body,
			globalNames,
		)
	) {
		return true;
	}
	if (cleanupPhiObjectDefault(func, block, body, globalNames)) return true;
	if (cleanupRecoveredObjectRest(body, globalNames)) return true;
	if (cleanupSplitObjectRestDefault(func, block, body, globalNames)) {
		return true;
	}
	if (cleanupPlainObjectProjectionDestructuring(func, body)) return true;
	for (let i = 0; i <= body.length - 3; i++) {
		const probeDecl = singleDeclarator(body[i], 'let');
		if (!probeDecl || !t.isIdentifier(probeDecl.id)) continue;
		const probeName = probeDecl.id.name;
		if (!t.isMemberExpression(probeDecl.init)) continue;
		if (!t.isExpression(probeDecl.init.object)) continue;
		if (!t.isExpression(probeDecl.init.property)) continue;
		const sourceObject = probeDecl.init.object;

		const ifStmt = body[i + 1];
		if (!t.isIfStatement(ifStmt)) continue;
		if (!isUndefinedStrictEquality(ifStmt.test, probeDecl.init)) continue;
		if (!t.isBlockStatement(ifStmt.consequent)) continue;
		if (ifStmt.alternate) continue;
		const defaultAssign = defaultAssignmentInBlock(
			ifStmt.consequent,
			probeName,
		);
		if (!defaultAssign) continue;

		const target = objectDestructureTargetPlan(
			body[i + 2],
			probeName,
			globalNames,
		);
		if (!target) continue;

		const patternTarget = planToPattern({
			kind: 'target',
			target: target.plan,
			defaultValue: defaultAssign.value,
		});
		const objectProperty = t.objectProperty(
			t.cloneNode(probeDecl.init.property, true) as t.Expression,
			patternTarget,
			probeDecl.init.computed,
		);

		const excludedName = getObjectCreateNullName(body[i + 3]);
		if (!excludedName) {
			debugObjDestr('no-excl at', i, {
				probeName,
				probeKey: t.isIdentifier(probeDecl.init.property)
					? probeDecl.init.property.name
					: probeDecl.init.property.type,
				body_i3_type: body[i + 3]?.type ?? '(none)',
			});
			const consumed = body.slice(i, i + 3);
			const declaredGlobals = target.plan.kind === 'binding' &&
					target.plan.declaredGlobal && target.name
				? new Set([target.name])
				: new Set<string>();
			if (
				!consumedDefinitionsAreDead(
					func,
					block,
					consumed,
					[
						sourceObject,
						probeDecl.init.property,
						defaultAssign.value,
						target.writeTarget,
						t.identifier('undefined'),
						t.identifier('global'),
					],
					[],
					new Set(),
					false,
					body,
				)
			) continue;

			body.splice(
				i,
				3,
				emitDestructuringPlan({
					pattern: t.objectPattern([objectProperty]),
					source: sourceObject,
					declaredGlobals,
					consumed,
					preservedInputs: [
						sourceObject,
						probeDecl.init.property,
						defaultAssign.value,
						target.writeTarget,
						t.identifier('undefined'),
						t.identifier('global'),
					],
					inlineConsumedResults: [],
				}),
			);
			if (target.name) {
				removeDeclaredGlobals(body, new Set([target.name]));
			}
			return true;
		}
		// Count how many excluded-key assignments actually follow before copyDataProperties
		if (DEBUG_OBJ_DESTR) {
			const probeKey = t.isIdentifier(probeDecl.init.property)
				? probeDecl.init.property.name
				: probeDecl.init.property.type;
			let k = i + 4;
			const exclKeys: string[] = [];
			while (k < body.length) {
				const assign = expressionStatementAssignment(body[k]);
				if (
					!assign ||
					!t.isMemberExpression(assign.left, { computed: true }) ||
					!t.isIdentifier(assign.left.object, { name: excludedName })
				) break;
				const kExpr = assign.left.property;
				exclKeys.push(
					t.isIdentifier(kExpr)
						? kExpr.name
						: t.isStringLiteral(kExpr)
						? kExpr.value
						: kExpr.type,
				);
				k++;
			}
			const copyDataStmt = body[i + 4 + exclKeys.length];
			const copyDataType = copyDataStmt
				? (t.isExpressionStatement(copyDataStmt) &&
						t.isAssignmentExpression(copyDataStmt.expression)
					? `assign → ${
						(copyDataStmt.expression.right as t.Node).type
					}`
					: copyDataStmt.type)
				: '(end)';
			debugObjDestr('with-rest at', i, {
				probeName,
				probeKey,
				excludedName,
				exclKeys,
				body_i4_type: body[i + 4]?.type ?? '(none)',
				firstExclKeyMatchesProbe: isExcludedKeyAssignment(
					body[i + 4],
					excludedName,
					probeDecl.init.property,
				),
				copyDataStmtType: copyDataType,
			});
		}
		if (
			!isExcludedKeyAssignment(
				body[i + 4],
				excludedName,
				probeDecl.init.property,
			)
		) continue;

		const restAssign = assignmentToTarget(body[i + 5], target.writeTarget);
		if (!restAssign || !t.isExpression(restAssign.right)) continue;
		const source = getCopyDataPropertiesSource(
			restAssign.right,
			sourceObject,
			excludedName,
		);
		if (!source) continue;

		const consumed = body.slice(i, i + 6);
		if (
			!consumedDefinitionsAreDead(
				func,
				block,
				consumed,
				[
					sourceObject,
					probeDecl.init.property,
					defaultAssign.value,
					source,
					target.writeTarget,
					t.identifier('undefined'),
					t.identifier('global'),
				],
				[restAssign.right],
				new Set(),
				false,
				body,
			)
		) continue;

		const part: ObjectDestructurePart = {
			key: t.cloneNode(probeDecl.init.property, true) as t.Expression,
			value: patternTarget,
			computed: probeDecl.init.computed,
			declaredGlobal: target.plan.kind === 'binding' &&
				target.plan.declaredGlobal,
			defaultValue: defaultAssign.value,
		};
		const objectPattern = t.objectPattern([
			t.objectProperty(part.key, part.value, part.computed),
			t.restElement(
				targetToPattern(target.plan) as unknown as RestElementArgument,
			),
		]);
		const declaredGlobals = target.plan.kind === 'binding' &&
				target.plan.declaredGlobal && target.name
			? new Set([target.name])
			: new Set<string>();

		body.splice(
			i,
			6,
			emitDestructuringPlan({
				pattern: objectPattern,
				source,
				declaredGlobals,
				consumed,
				preservedInputs: [
					sourceObject,
					probeDecl.init.property,
					defaultAssign.value,
					source,
					target.writeTarget,
					t.identifier('undefined'),
					t.identifier('global'),
				],
				inlineConsumedResults: [restAssign.right],
			}),
		);
		if (target.name) removeDeclaredGlobals(body, new Set([target.name]));
		return true;
	}

	for (const stmt of body) {
		if (
			cleanupSequentialObjectDestructuringInStatement(func, block, stmt)
		) return true;
	}

	return false;
}

function cleanupSequentialObjectDestructuringInStatement(
	func: IRFunction,
	block: IRBlock,
	stmt: t.Statement,
): boolean {
	if (t.isBlockStatement(stmt)) {
		return cleanupSequentialObjectDestructuringInBody(
			func,
			block,
			stmt.body,
		);
	}
	if (t.isTryStatement(stmt)) {
		if (
			cleanupSequentialObjectDestructuringInBody(
				func,
				block,
				stmt.block.body,
			)
		) return true;
		if (
			stmt.handler &&
			cleanupSequentialObjectDestructuringInBody(
				func,
				block,
				stmt.handler.body.body,
			)
		) return true;
		return !!stmt.finalizer &&
			cleanupSequentialObjectDestructuringInBody(
				func,
				block,
				stmt.finalizer.body,
			);
	}
	if (t.isIfStatement(stmt)) {
		if (
			t.isBlockStatement(stmt.consequent) &&
			cleanupSequentialObjectDestructuringInBody(
				func,
				block,
				stmt.consequent.body,
			)
		) return true;
		return !!stmt.alternate &&
			t.isBlockStatement(stmt.alternate) &&
			cleanupSequentialObjectDestructuringInBody(
				func,
				block,
				stmt.alternate.body,
			);
	}
	if (t.isWhileStatement(stmt) && t.isBlockStatement(stmt.body)) {
		return cleanupSequentialObjectDestructuringInBody(
			func,
			block,
			stmt.body.body,
		);
	}
	if (
		(t.isForStatement(stmt) ||
			t.isForInStatement(stmt) ||
			t.isForOfStatement(stmt)) &&
		t.isBlockStatement(stmt.body)
	) {
		return cleanupSequentialObjectDestructuringInBody(
			func,
			block,
			stmt.body.body,
		);
	}
	return false;
}

export function cleanupSequentialObjectDestructuring(
	func: IRFunction,
): boolean {
	for (const block of func.blocks.values()) {
		if (
			cleanupSequentialObjectDestructuringInBody(
				func,
				block,
				<t.Statement[]> block.body,
			)
		) return true;
	}
	return false;
}

function irBlockContainsIntrinsic(block: IRBlock, name: string): boolean {
	return block.body.some((stmt) => {
		let found = false;
		t.traverseFast(stmt as t.Statement, (node) => {
			if (
				t.isCallExpression(node) &&
				t.isV8IntrinsicIdentifier(node.callee, { name })
			) found = true;
		});
		return found;
	});
}

function irBlockContainsPhi(block: IRBlock): boolean {
	return irBlockContainsIntrinsic(block, 'Phi');
}

function mergeDestructuringBlocksInto(
	func: IRFunction,
	target: number,
	blocks: number[],
): void {
	const targetBlock = func.blocks.get(target)!;
	for (const address of blocks) {
		const block = func.blocks.get(address)!;
		targetBlock.body.push(...block.body);
		func.markMergedBlocks(target, address);
	}
}

function blockHasIteratorDestructuringPrefix(block: IRBlock): boolean {
	return irBlockContainsIntrinsic(block, 'IteratorBegin') ||
		irBlockContainsIntrinsic(block, 'IteratorNext');
}

function blockContinuesIteratorDestructuring(
	func: IRFunction,
	block: IRBlock,
): boolean {
	if (irBlockContainsIntrinsic(block, 'IteratorNext')) return true;
	if (block.consequentAddresses.length !== 1) return false;
	const successorBlock = func.blocks.get(block.consequentAddresses[0]);
	return !!successorBlock &&
		irBlockContainsIntrinsic(successorBlock, 'IteratorNext');
}

function iteratorCloseInBlock(
	block: IRBlock,
	abrupt: boolean,
): t.Expression | null {
	for (const statement of block.body as t.Statement[]) {
		if (
			!t.isExpressionStatement(statement) ||
			!t.isCallExpression(statement.expression) ||
			!t.isV8IntrinsicIdentifier(statement.expression.callee, {
				name: 'IteratorClose',
			}) ||
			statement.expression.arguments.length !== 2 ||
			!t.isExpression(statement.expression.arguments[0]) ||
			!t.isBooleanLiteral(statement.expression.arguments[1], {
				value: abrupt,
			})
		) continue;
		return statement.expression.arguments[0];
	}
	return null;
}

function cfgGeneratedDefinitions(
	statements: readonly t.Statement[],
): Map<string, t.Expression[]> {
	const definitions = new Map<string, t.Expression[]>();
	const add = (name: string, value: t.Expression) => {
		const values = definitions.get(name) ?? [];
		values.push(value);
		definitions.set(name, values);
	};
	for (const statement of statements) {
		t.traverseFast(statement, (node) => {
			if (
				t.isVariableDeclarator(node) &&
				t.isIdentifier(node.id) && isGeneratedName(node.id.name) &&
				t.isExpression(node.init)
			) add(node.id.name, node.init);
			if (
				t.isAssignmentExpression(node, { operator: '=' }) &&
				t.isIdentifier(node.left) &&
				isGeneratedName(node.left.name) && t.isExpression(node.right)
			) add(node.left.name, node.right);
		});
	}
	return definitions;
}

function expressionUsesGeneratedName(
	expression: t.Expression,
	names: ReadonlySet<string>,
): boolean {
	let found = false;
	t.traverseFast(expression, (node) => {
		if (t.isIdentifier(node) && names.has(node.name)) found = true;
	});
	return found;
}

function cfgIteratorDerivedNames(
	definitions: ReadonlyMap<string, readonly t.Expression[]>,
	seeds: ReadonlySet<string>,
): Set<string> {
	const derived = new Set(seeds);
	let changed = true;
	while (changed) {
		changed = false;
		for (const [name, values] of definitions) {
			if (
				derived.has(name) ||
				!values.some((value) =>
					expressionUsesGeneratedName(value, derived)
				)
			) continue;
			derived.add(name);
			changed = true;
		}
	}
	return derived;
}

interface CFGDestructuredValue {
	defaultValue: t.Expression | null;
}

type CFGElementAccess = {
	element: number;
	path: Array<{ key: t.Expression; computed: boolean }>;
};

type CFGElementAccessResolution =
	| { kind: 'undefined' }
	| { kind: 'access'; access: CFGElementAccess }
	| { kind: 'invalid' };

function sameCFGElementAccess(
	left: CFGElementAccess,
	right: CFGElementAccess,
): boolean {
	return left.element === right.element &&
		left.path.length === right.path.length &&
		left.path.every((segment, index) => {
			const other = right.path[index]!;
			return segment.computed === other.computed &&
				expressionsEqual(segment.key, other.key);
		});
}

function mergeCFGElementAccesses(
	resolutions: readonly CFGElementAccessResolution[],
): CFGElementAccessResolution {
	if (resolutions.some(({ kind }) => kind === 'invalid')) {
		return { kind: 'invalid' };
	}
	const accesses = resolutions.flatMap((resolution) =>
		resolution.kind === 'access' ? [resolution.access] : []
	);
	if (accesses.length === 0) return { kind: 'undefined' };
	return accesses.every((access) =>
			sameCFGElementAccess(accesses[0]!, access)
		)
		? { kind: 'access', access: accesses[0]! }
		: { kind: 'invalid' };
}

/** Resolve an SSA expression to one iterator element and property path. */
function cfgElementAccess(
	expression: t.Expression,
	rawElementByName: ReadonlyMap<string, number>,
	definitions: ReadonlyMap<string, readonly t.Expression[]>,
	visiting = new Set<string>(),
): CFGElementAccessResolution {
	if (t.isIdentifier(expression)) {
		if (expression.name === 'undefined') return { kind: 'undefined' };
		const element = rawElementByName.get(expression.name);
		if (element != null) {
			return { kind: 'access', access: { element, path: [] } };
		}
		if (visiting.has(expression.name)) return { kind: 'invalid' };
		const values = definitions.get(expression.name);
		if (!values || values.length === 0) return { kind: 'invalid' };
		const nextVisiting = new Set(visiting);
		nextVisiting.add(expression.name);
		return mergeCFGElementAccesses(
			values.map((value) =>
				cfgElementAccess(
					value,
					rawElementByName,
					definitions,
					nextVisiting,
				)
			),
		);
	}
	if (isUndefinedNode(expression)) return { kind: 'undefined' };
	if (
		t.isCallExpression(expression) &&
		t.isV8IntrinsicIdentifier(expression.callee, { name: 'Phi' }) &&
		expression.arguments.every((argument) => t.isExpression(argument))
	) {
		return mergeCFGElementAccesses(
			(expression.arguments as t.Expression[]).map((argument) =>
				cfgElementAccess(
					argument,
					rawElementByName,
					definitions,
					new Set(visiting),
				)
			),
		);
	}
	if (
		t.isMemberExpression(expression) &&
		t.isExpression(expression.object) &&
		!t.isPrivateName(expression.property) &&
		t.isExpression(expression.property)
	) {
		const object = cfgElementAccess(
			expression.object,
			rawElementByName,
			definitions,
			new Set(visiting),
		);
		if (object.kind !== 'access') return { kind: 'invalid' };
		return {
			kind: 'access',
			access: {
				element: object.access.element,
				path: [...object.access.path, {
					key: t.cloneNode(expression.property, true),
					computed: expression.computed,
				}],
			},
		};
	}
	return { kind: 'invalid' };
}

type CFGProtectedElementCandidate = {
	statement: t.Statement;
	target: TargetPlan;
	name?: string;
	access: CFGElementAccess;
};

function isEnvironmentSlotAssignmentTarget(target: TargetPlan): boolean {
	if (target.kind !== 'assign' || !t.isMemberExpression(target.lval)) {
		return false;
	}
	const object = target.lval.object;
	return target.lval.computed && t.isCallExpression(object) &&
		t.isV8IntrinsicIdentifier(object.callee, {
			name: 'expectEnvironment',
		}) && t.isNumericLiteral(target.lval.property);
}

function cfgObjectPatternForLeaves(
	leaves: readonly CFGProtectedElementCandidate[],
	depth = 0,
): t.PatternLike | null {
	const direct = leaves.filter(({ access }) => access.path.length === depth);
	if (direct.length > 0) {
		return leaves.length === 1 && direct.length === 1
			? targetToPattern(direct[0]!.target)
			: null;
	}
	const groups: Array<{
		segment: CFGElementAccess['path'][number];
		leaves: CFGProtectedElementCandidate[];
	}> = [];
	for (const leaf of leaves) {
		const segment = leaf.access.path[depth];
		if (!segment) return null;
		let group = groups.find((candidate) =>
			candidate.segment.computed === segment.computed &&
			expressionsEqual(candidate.segment.key, segment.key)
		);
		if (!group) {
			group = { segment, leaves: [] };
			groups.push(group);
		}
		group.leaves.push(leaf);
	}
	const properties: t.ObjectProperty[] = [];
	for (const group of groups) {
		const value = cfgObjectPatternForLeaves(group.leaves, depth + 1);
		if (!value) return null;
		// Babel's builder type only admits binding Patterns here even though an
		// object assignment pattern may legally target a MemberExpression. Build
		// with a placeholder, then install the mechanically proven LVal.
		const property = t.objectProperty(
			t.cloneNode(group.segment.key, true),
			t.isMemberExpression(value) ? t.identifier('_target') : value,
			group.segment.computed,
		);
		if (t.isMemberExpression(value)) {
			(property as unknown as { value: t.Node }).value = value;
		}
		if (
			!property.computed && t.isIdentifier(property.key) &&
			t.isIdentifier(property.value, { name: property.key.name })
		) property.shorthand = true;
		properties.push(property);
	}
	const pattern = t.objectPattern([]);
	pattern.properties = properties;
	return pattern;
}

type PlainObjectProjectionCandidate = {
	statement: t.Statement;
	target: TargetPlan;
	targetName?: string;
	declarationKind?: 'var' | 'let' | 'const';
	source: t.Identifier;
	access: CFGElementAccess;
};

function plainGetByIdProjection(
	expression: t.Expression,
	provenSources: ReadonlySet<string> = new Set(),
	statementHasGetByIdProvenance = false,
): { source: t.Identifier; path: CFGElementAccess['path'] } | null {
	const reversed: CFGElementAccess['path'] = [];
	let hasCompleteProvenance = statementHasGetByIdProvenance;
	let current: t.Expression | t.Super = expression;
	while (t.isMemberExpression(current)) {
		// GetById is the provenance distinction between this lowering and a
		// generic AST member-read guess. The raw lifted declaration carries the
		// tag on its statement; nested/inlined forms may carry it on a member.
		if (current.extra?.instruction === 'GetById') {
			hasCompleteProvenance = true;
		}
		if (t.isPrivateName(current.property)) return null;
		if (
			current.computed &&
			!(t.isStringLiteral(current.property) ||
				t.isNumericLiteral(current.property))
		) return null;
		reversed.push({
			key: t.cloneNode(current.property, true) as t.Expression,
			computed: current.computed,
		});
		current = current.object;
	}
	if (!t.isIdentifier(current) || reversed.length === 0) return null;
	if (!hasCompleteProvenance && !provenSources.has(current.name)) return null;
	return { source: current, path: reversed.reverse() };
}

function plainObjectProjectionCandidate(
	statement: t.Statement | undefined,
	provenSources: ReadonlySet<string> = new Set(),
): PlainObjectProjectionCandidate | null {
	if (!statement) return null;
	let target: TargetPlan;
	let targetName: string | undefined;
	let value: t.Expression;
	let declarationKind: PlainObjectProjectionCandidate['declarationKind'];
	if (
		t.isVariableDeclaration(statement) &&
		['var', 'let', 'const'].includes(statement.kind) &&
		statement.declarations.length === 1
	) {
		const declaration = statement.declarations[0]!;
		if (
			!t.isIdentifier(declaration.id) || !t.isExpression(declaration.init)
		) {
			return null;
		}
		targetName = declaration.id.name;
		target = bindingTarget(targetName, false);
		value = declaration.init;
		declarationKind = statement.kind as 'var' | 'let' | 'const';
	} else {
		const assignment = assignmentTargetPlan(statement, new Set());
		if (!assignment) return null;
		target = assignment.target;
		targetName = assignment.name;
		value = assignment.value;
	}
	if (!t.isMemberExpression(value)) return null;
	const projection = plainGetByIdProjection(
		value,
		provenSources,
		statement.extra?.instruction === 'GetById',
	);
	if (!projection || projection.source.name === targetName) return null;
	return {
		statement,
		target,
		targetName,
		declarationKind,
		source: projection.source,
		access: { element: 0, path: projection.path },
	};
}

/** Preserve raw GetById evidence before CFG reduction and value inlining. */
export function capturePlainObjectProjectionSources(func: IRFunction): number {
	const counts = new Map<string, number>();
	for (const block of func.blocks.values()) {
		for (const statement of block.body as t.Statement[]) {
			const candidate = plainObjectProjectionCandidate(statement);
			if (!candidate) continue;
			counts.set(
				candidate.source.name,
				(counts.get(candidate.source.name) ?? 0) + 1,
			);
		}
	}
	const before = func.plainObjectProjectionSources.size;
	for (const [source, count] of counts) {
		if (count > 2) func.plainObjectProjectionSources.add(source);
	}
	return func.plainObjectProjectionSources.size - before;
}

function functionIdentifierReferences(
	func: IRFunction,
	name: string,
): t.Identifier[] {
	const references: t.Identifier[] = [];
	const visit = (statements: t.Statement[]) => {
		const wrapped = t.file(t.program(statements));
		// The recursive reducer can hold the same SSA spelling in disjoint
		// branch-local scopes until final binding repair. This scan only needs
		// reference nodes, so do not ask Babel to crawl/enforce scope bindings.
		traverse(wrapped, {
			noScope: true,
			Identifier(path) {
				if (path.isReferencedIdentifier({ name })) {
					references.push(path.node);
				}
			},
		});
	};
	for (const block of func.blocks.values()) {
		visit(block.body as t.Statement[]);
		if (block.branch) {
			visit([t.expressionStatement(block.branch as t.Expression)]);
		}
	}
	return references;
}

function functionGeneratedDefinitions(
	func: IRFunction,
): ReadonlyMap<string, readonly t.Expression[]> {
	const statements: t.Statement[] = [];
	for (const block of func.blocks.values()) {
		statements.push(...block.body as t.Statement[]);
		if (block.branch) {
			statements.push(
				t.expressionStatement(block.branch as t.Expression),
			);
		}
	}
	return cfgGeneratedDefinitions(statements);
}

function expressionIsParameterDerived(
	func: IRFunction,
	expression: t.Expression,
	definitions: ReadonlyMap<string, readonly t.Expression[]>,
	visiting = new Set<string>(),
): boolean {
	const location = locationOf(expression);
	if (location?.kind === 'parameter') return true;
	if (
		location &&
		(func.parameterPlan?.slots ?? []).some((slot) =>
			slot.rawLocations.some((raw) =>
				locationKey(raw) === locationKey(location)
			)
		)
	) return true;
	if (t.isIdentifier(expression)) {
		if (
			(func.parameterPlan?.slots ?? []).some((slot) =>
				t.isIdentifier(slot.binding, { name: expression.name })
			)
		) return true;
		if (visiting.has(expression.name)) return false;
		const values = definitions.get(expression.name);
		if (!values) return false;
		const next = new Set(visiting);
		next.add(expression.name);
		return values.some((value) =>
			expressionIsParameterDerived(func, value, definitions, next)
		);
	}
	if (
		t.isCallExpression(expression) &&
		t.isV8IntrinsicIdentifier(expression.callee, { name: 'Phi' })
	) {
		return expression.arguments.some((argument) =>
			t.isExpression(argument) &&
			expressionIsParameterDerived(
				func,
				argument,
				definitions,
				new Set(visiting),
			)
		);
	}
	if (t.isConditionalExpression(expression)) {
		return [expression.consequent, expression.alternate].some((value) =>
			expressionIsParameterDerived(
				func,
				value,
				definitions,
				new Set(visiting),
			)
		);
	}
	return false;
}

/**
 * Recover Hermes' plain object lowering for non-parameter sources:
 *
 *     const a = source.a;
 *     const b = source.b;
 *     const c = source.c;
 *
 * Unlike iterator and rest protocols, one or two GetById operations are
 * indistinguishable from ordinary source. Require a contiguous run of at
 * least three consequential writes, and require that run to account for every
 * reference to the source object before replacing it with one object pattern.
 */
function cleanupPlainObjectProjectionDestructuring(
	func: IRFunction,
	body: t.Statement[],
): boolean {
	let definitions: ReadonlyMap<string, readonly t.Expression[]> | null = null;
	const generatedDefinitions = () =>
		definitions ??= functionGeneratedDefinitions(func);
	const provenSources = func.plainObjectProjectionSources ??
		new Set<string>();
	const references = new Map<string, t.Identifier[]>();
	const referencesTo = (name: string): t.Identifier[] => {
		let found = references.get(name);
		if (!found) {
			found = functionIdentifierReferences(func, name);
			references.set(name, found);
		}
		return found;
	};
	for (let start = 0; start < body.length; start++) {
		const first = plainObjectProjectionCandidate(
			body[start],
			provenSources,
		);
		if (!first) continue;
		if (
			expressionIsParameterDerived(
				func,
				first.source,
				generatedDefinitions(),
			)
		) {
			debugObjDestr('plain projection parameter source', func.id, {
				source: first.source.name,
			});
			continue;
		}
		const candidates = [first];
		for (let index = start + 1; index < body.length; index++) {
			const candidate = plainObjectProjectionCandidate(
				body[index],
				provenSources,
			);
			if (
				!candidate || candidate.source.name !== first.source.name
			) break;
			candidates.push(candidate);
		}
		// This is deliberately a confidence threshold, not a syntax limitation.
		if (candidates.length <= 2) {
			debugObjDestr('plain projection short run', func.id, {
				source: first.source.name,
				count: candidates.length,
			});
			continue;
		}
		const bindingTargets = candidates.filter(({ target }) =>
			target.kind === 'binding'
		);
		const targetNames = new Set(
			bindingTargets.map(({ target }) =>
				target.kind === 'binding' ? target.id.name : ''
			),
		);
		if (targetNames.size !== bindingTargets.length) {
			debugObjDestr('plain projection duplicate targets', func.id, {
				source: first.source.name,
			});
			continue;
		}

		// Every recovered assignment must have a consequence outside the probe
		// sequence. Dead property loads are not evidence of destructuring.
		const unusedTargets = bindingTargets.filter(({ target }) =>
			target.kind === 'binding' &&
			referencesTo(target.id.name).length === 0
		).map(({ target }) => target.kind === 'binding' ? target.id.name : '');
		if (unusedTargets.length > 0) {
			debugObjDestr('plain projection inconsequential target', func.id, {
				source: first.source.name,
				targets: unusedTargets,
			});
			continue;
		}

		// Account for the complete source use-set. An escape, a method call, or a
		// projection separated from this run makes the inference ambiguous.
		const coveredSources = new Set(
			candidates.map(({ source }) => source),
		);
		const sourceReferences = referencesTo(first.source.name);
		if (
			sourceReferences.length !== coveredSources.size ||
			sourceReferences.some((reference) => !coveredSources.has(reference))
		) {
			debugObjDestr('plain projection incomplete source uses', func.id, {
				source: first.source.name,
				covered: coveredSources.size,
				references: sourceReferences.length,
			});
			continue;
		}

		const leaves: CFGProtectedElementCandidate[] = candidates.map(
			(candidate) => ({
				statement: candidate.statement,
				target: candidate.target,
				name: candidate.targetName,
				access: candidate.access,
			}),
		);
		const pattern = cfgObjectPatternForLeaves(leaves);
		if (!pattern || !t.isObjectPattern(pattern)) {
			debugObjDestr('plain projection conflicting pattern', func.id, {
				source: first.source.name,
			});
			continue;
		}

		const declarationKind = candidates[0]!.declarationKind;
		const oneDeclarationKind = declarationKind != null &&
			candidates.every((candidate) =>
				candidate.declarationKind === declarationKind
			);
		let replacement: t.Statement;
		const prelude: t.Statement[] = [];
		if (oneDeclarationKind && !patternHasAssignmentOnlyTargets(pattern)) {
			replacement = t.variableDeclaration(
				declarationKind,
				[t.variableDeclarator(
					t.cloneNode(pattern, true),
					t.cloneNode(first.source, true),
				)],
			);
		} else {
			for (const candidate of candidates) {
				if (!candidate.declarationKind || !candidate.targetName) {
					continue;
				}
				const declaration = t.variableDeclaration(
					candidate.declarationKind === 'const'
						? 'let'
						: candidate.declarationKind,
					[t.variableDeclarator(
						t.identifier(candidate.targetName),
					)],
				);
				declaration.extra = candidate.statement.extra;
				prelude.push(declaration);
			}
			replacement = t.expressionStatement(t.assignmentExpression(
				'=',
				t.cloneNode(pattern, true) as unknown as t.LVal,
				t.cloneNode(first.source, true),
			));
		}
		replacement.extra = {
			...first.statement.extra,
			fromDestructuring: true,
		};
		body.splice(start, candidates.length, ...prelude, replacement);
		return true;
	}
	return false;
}

/**
 * Recover the register-only form used by parameter destructuring. Its source
 * bindings are generated SSA names, so require each retained name to escape
 * the candidate-definition graph and recover protected property probes as a
 * nested native pattern.
 */
function cfgProtectedParameterArrayPattern(
	func: IRFunction,
	protocolStatements: readonly t.Statement[],
	iteratorDecls: readonly {
		kind: 'begin' | 'next';
		ids: t.Identifier[];
		args: t.Expression[];
	}[],
	removedBlocks: ReadonlySet<number>,
	startAddress: number,
	beginIndex: number,
): {
	pattern: t.ArrayPattern;
	prelude: t.Statement[];
	preserved: t.Statement[];
	aliases: Map<string, t.Expression>;
} | null {
	const nexts = iteratorDecls.filter(({ kind }) => kind === 'next');
	if (nexts.length === 0) return null;
	const rawElementByName = new Map(
		nexts.map(({ ids }, index) => [ids[0]!.name, index]),
	);
	const definitions = cfgGeneratedDefinitions(protocolStatements);
	const iteratorDerived = cfgIteratorDerivedNames(
		definitions,
		new Set(
			iteratorDecls.flatMap(({ ids }) => ids.map(({ name }) => name)),
		),
	);
	const candidates: CFGProtectedElementCandidate[] = [];
	for (const statement of protocolStatements) {
		const target = assignmentTargetPlan(statement, new Set());
		if (!target) continue;
		const generatedBinding = target.name != null &&
			target.target.kind === 'binding' && isGeneratedName(target.name);
		if (
			!generatedBinding &&
			!isEnvironmentSlotAssignmentTarget(target.target)
		) continue;
		const resolution = cfgElementAccess(
			target.value,
			rawElementByName,
			definitions,
		);
		if (resolution.kind !== 'access') continue;
		candidates.push({
			statement,
			target: target.target,
			name: generatedBinding ? target.name : undefined,
			access: resolution.access,
		});
	}
	if (candidates.length === 0) {
		debugArrayDestr('protected-param: no candidates', func.id);
		return null;
	}
	const candidateStatements = new Set(
		candidates.map(({ statement }) => statement),
	);
	const escapesCandidateGraph = (name: string): boolean => {
		for (const [address, block] of func.blocks) {
			const statements = block.body as t.Statement[];
			for (let index = 0; index < statements.length; index++) {
				const statement = statements[index]!;
				if (candidateStatements.has(statement)) continue;
				if (
					(address === startAddress && index >= beginIndex ||
						removedBlocks.has(address) ||
						address !== startAddress) &&
					countIdentifierUses(statement, name) > 0
				) return true;
			}
			if (
				block.branch &&
				countIdentifierUses(block.branch as t.Expression, name) > 0
			) return true;
		}
		return false;
	};
	let leaves = candidates.filter(({ name, target }) =>
		isEnvironmentSlotAssignmentTarget(target) ||
		(name != null && escapesCandidateGraph(name))
	);
	if (leaves.length === 0) {
		debugArrayDestr('protected-param: no escaping leaves', func.id, {
			candidates: candidates.map(({ name, target }) =>
				name ?? target.kind
			),
		});
		return null;
	}
	const aliases = new Map<string, t.Expression>();
	const usedOutsideRemovedRegion = (name: string): boolean =>
		[...func.blocks].some(([address, block]) =>
			!removedBlocks.has(address) && address !== startAddress &&
			(
				(block.body as t.Statement[]).some((statement) =>
					countIdentifierUses(statement, name) > 0
				) ||
				!!block.branch &&
					countIdentifierUses(block.branch as t.Expression, name) > 0
			)
		);
	const canonicalLeaves: CFGProtectedElementCandidate[] = [];
	for (const leaf of leaves) {
		const group = leaves.filter((candidate) =>
			sameCFGElementAccess(candidate.access, leaf.access)
		);
		if (group[0] !== leaf) continue;
		const environmentTargets = group.filter(({ target }) =>
			isEnvironmentSlotAssignmentTarget(target)
		);
		if (environmentTargets.length > 1) return null;
		const external = group.filter(({ name }) =>
			name != null && usedOutsideRemovedRegion(name)
		);
		if (environmentTargets.length === 0 && external.length > 1) return null;
		const canonical = environmentTargets[0] ?? external[0] ?? group.at(-1)!;
		canonicalLeaves.push(canonical);
		for (const candidate of group) {
			if (candidate !== canonical && candidate.name != null) {
				aliases.set(
					candidate.name,
					targetToPattern(canonical.target) as t.Expression,
				);
			}
		}
	}
	leaves = canonicalLeaves;
	const elements: Array<t.PatternLike | null> = [];
	const boundNames = new Set<string>();
	for (let element = 0; element < nexts.length; element++) {
		const elementLeaves = leaves.filter((leaf) =>
			leaf.access.element === element
		);
		if (elementLeaves.length === 0) {
			elements.push(null);
			continue;
		}
		const pattern = cfgObjectPatternForLeaves(elementLeaves);
		if (!pattern) {
			debugArrayDestr('protected-param: conflicting leaves', func.id, {
				element,
				leaves: elementLeaves.map(({ name, target, access }) => ({
					name: name ?? target.kind,
					path: access.path.length,
				})),
			});
			return null;
		}
		elements.push(pattern);
		for (const leaf of elementLeaves) {
			if (leaf.name != null) boundNames.add(leaf.name);
		}
	}

	const preserved: t.Statement[] = [];
	const preservedInputNames = new Set([
		...boundNames,
		...aliases.keys(),
	]);
	for (const statement of protocolStatements) {
		if (candidateStatements.has(statement)) continue;
		const write = generatedWrite(statement);
		if (write && !iteratorDerived.has(write.name)) {
			const escapesRemovedRegion = [...func.blocks].some(
				([address, block]) =>
					!removedBlocks.has(address) && address !== startAddress &&
					(block.body as t.Statement[]).some((candidate) =>
						countIdentifierUses(candidate, write.name) > 0
					),
			);
			if (escapesRemovedRegion) preserved.push(statement);
			continue;
		}
		const assignment = expressionStatementAssignment(statement);
		if (
			assignment && t.isMemberExpression(assignment.left) &&
			t.isExpression(assignment.right) &&
			[...preservedInputNames].some((name) =>
				countIdentifierUses(assignment.right, name) > 0
			)
		) {
			let preservedStatement = t.cloneNode(statement, true);
			for (const [from, to] of aliases) {
				preservedStatement = replaceIdentifierUse(
					preservedStatement,
					from,
					t.cloneNode(to, true),
				) as t.Statement;
			}
			preserved.push(preservedStatement);
			continue;
		}
		// A nested slot whose own protocol was already collapsed leaves a
		// recovered pattern declaration reading one of this pattern's
		// bindings. It survives verbatim as a follow-on statement.
		if (
			t.isVariableDeclaration(statement) &&
			statement.declarations.length > 0 &&
			statement.declarations.every(({ id, init }) =>
				(t.isArrayPattern(id) || t.isObjectPattern(id)) &&
				init != null &&
				[...preservedInputNames].some((name) =>
					countIdentifierUses(init, name) > 0
				)
			)
		) {
			let preservedStatement: t.Statement = t.cloneNode(
				statement,
				true,
			);
			for (const [from, to] of aliases) {
				preservedStatement = replaceIdentifierUse(
					preservedStatement,
					from,
					t.cloneNode(to, true),
				) as t.Statement;
			}
			preserved.push(preservedStatement);
			continue;
		}
		if (
			write ||
			intrinsicArrayDecl(statement, 'IteratorBegin') ||
			intrinsicArrayDecl(statement, 'IteratorNext') ||
			t.isThrowStatement(statement) ||
			(t.isExpressionStatement(statement) &&
				t.isCallExpression(statement.expression) &&
				t.isV8IntrinsicIdentifier(statement.expression.callee) &&
				['Catch', 'IteratorClose'].includes(
					statement.expression.callee.name,
				))
		) continue;
		debugArrayDestr('protected-param: retained statement', func.id, {
			type: statement.type,
		});
		return null;
	}

	const removedDefinitions = new Set(iteratorDerived);
	for (const name of boundNames) removedDefinitions.delete(name);
	for (const name of aliases.keys()) removedDefinitions.delete(name);
	for (const [address, block] of func.blocks) {
		if (removedBlocks.has(address) || address === startAddress) continue;
		if (
			[...removedDefinitions].some((name) =>
				(block.body as t.Statement[]).some((statement) =>
					countIdentifierUses(statement, name) > 0
				)
			)
		) {
			debugArrayDestr('protected-param: external intermediate', func.id, {
				address,
				names: [...removedDefinitions].filter((name) =>
					(block.body as t.Statement[]).some((statement) =>
						countIdentifierUses(statement, name) > 0
					)
				),
			});
			return null;
		}
	}
	const hasAssignmentTarget = leaves.some(({ target }) =>
		target.kind === 'assign'
	);
	const prelude = hasAssignmentTarget && boundNames.size > 0
		? [t.variableDeclaration(
			'let',
			[...boundNames].map((name) =>
				t.variableDeclarator(t.identifier(name))
			),
		)]
		: [];
	return {
		pattern: t.arrayPattern(elements),
		prelude,
		preserved,
		aliases,
	};
}

function cfgDestructuredValue(
	value: t.Expression,
	definitions: ReadonlyMap<string, readonly t.Expression[]>,
	iteratorDerived: ReadonlySet<string>,
): CFGDestructuredValue | null {
	const candidates: t.Expression[] = [];
	const visited = new Set<string>();
	let reachesIterator = false;
	const visit = (expression: t.Expression): void => {
		if (t.isIdentifier(expression)) {
			if (iteratorDerived.has(expression.name)) reachesIterator = true;
			if (visited.has(expression.name)) return;
			visited.add(expression.name);
			for (const definition of definitions.get(expression.name) ?? []) {
				visit(definition);
			}
			return;
		}
		if (
			t.isCallExpression(expression) &&
			t.isV8IntrinsicIdentifier(expression.callee, { name: 'Phi' })
		) {
			for (const argument of expression.arguments) {
				if (t.isExpression(argument)) visit(argument);
			}
			return;
		}
		if (expressionUsesGeneratedName(expression, iteratorDerived)) {
			reachesIterator = true;
			return;
		}
		if (isUndefinedNode(expression)) return;
		if (
			!candidates.some((candidate) =>
				expressionsEqual(candidate, expression)
			)
		) candidates.push(expression);
	};
	visit(value);
	if (!reachesIterator || candidates.length > 1) return null;
	return { defaultValue: candidates[0] ?? null };
}

function reachableWithout(
	func: IRFunction,
	start: number,
	stop: number,
): Set<number> {
	const reachable = new Set<number>();
	const pending = [start];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (address === stop || reachable.has(address)) continue;
		const block = func.blocks.get(address);
		if (!block) continue;
		reachable.add(address);
		pending.push(...block.consequentAddresses);
	}
	return reachable;
}

function allBlocksReachContinuation(
	func: IRFunction,
	region: ReadonlySet<number>,
	continuation: number,
): boolean {
	const reaching = new Set([continuation]);
	let changed = true;
	while (changed) {
		changed = false;
		for (const address of region) {
			if (reaching.has(address)) continue;
			const block = func.blocks.get(address);
			if (
				block?.consequentAddresses.some((successor) =>
					reaching.has(successor)
				)
			) {
				reaching.add(address);
				changed = true;
			}
		}
	}
	return [...region].every((address) => reaching.has(address));
}

/**
 * Hermes lowers one array-destructuring operation to straight-line diamonds:
 * every slot is an `IteratorNext` guarded by the previous done flag. A back
 * edge means the region is a loop -- `for..of`, or the rest-element collector
 * -- and therefore not a single fixed-arity pattern.
 */
function regionIsAcyclic(
	func: IRFunction,
	region: ReadonlySet<number>,
	start: number,
): boolean {
	const indegree = new Map<number, number>();
	for (const address of region) {
		indegree.set(
			address,
			[...func.predecessorsOf(address)].filter((predecessor) =>
				region.has(predecessor)
			).length,
		);
	}
	const pending = indegree.get(start) === 0 ? [start] : [];
	let settled = 0;
	while (pending.length > 0) {
		const address = pending.pop()!;
		settled++;
		for (const successor of func.blocks.get(address)!.consequentAddresses) {
			if (!region.has(successor)) continue;
			const remaining = indegree.get(successor)! - 1;
			indegree.set(successor, remaining);
			if (remaining === 0) pending.push(successor);
		}
	}
	return settled === region.size;
}

/**
 * Collapse Hermes' protected array-destructuring lowering before exception
 * edges become Region labels. Both default evaluation and target assignment
 * can throw, so their handlers carry iterator state to one abrupt close and
 * rethrow tail. Native destructuring has exactly those completion semantics.
 */
export function reduceProtectedArrayDestructuring(
	func: IRFunction,
): boolean {
	for (const [startAddress, startBlock] of func.blocks) {
		const beginIndex = (startBlock.body as t.Statement[]).findIndex((
			statement,
		) => intrinsicArrayDecl(statement, 'IteratorBegin') != null);
		if (beginIndex < 0) continue;
		const begin = intrinsicArrayDecl(
			startBlock.body[beginIndex] as t.Statement,
			'IteratorBegin',
		);
		if (!begin || begin.ids.length !== 2 || begin.args.length !== 1) {
			continue;
		}
		for (const [closeAddress, closeBlock] of func.blocks) {
			if (!iteratorCloseInBlock(closeBlock, false)) continue;
			if (closeBlock.consequentAddresses.length !== 1) continue;
			const continuation = closeBlock.consequentAddresses[0];
			const closePredecessors = func.predecessorsOf(closeAddress);
			if (closePredecessors.size !== 1) continue;
			const closeGuardAddress = [...closePredecessors][0];
			const closeGuard = func.blocks.get(closeGuardAddress);
			if (
				!closeGuard?.branch ||
				closeGuard.consequentAddresses.length !== 2 ||
				!closeGuard.consequentAddresses.includes(closeAddress) ||
				!closeGuard.consequentAddresses.includes(continuation)
			) continue;

			const region = reachableWithout(func, startAddress, continuation);
			if (
				!region.has(closeAddress) || !region.has(closeGuardAddress) ||
				!allBlocksReachContinuation(func, region, continuation)
			) continue;
			if (
				[...region].some((address) =>
					address !== startAddress &&
					[...func.predecessorsOf(address)].some((predecessor) =>
						!region.has(predecessor)
					)
				)
			) continue;

			const protocolStatements: t.Statement[] = [
				...(startBlock.body.slice(beginIndex) as t.Statement[]),
			];
			// Ascending address is program order for this lowering, and slot
			// order for the `IteratorNext` chain the recogniser indexes by.
			// `region` is a DFS set, so it must not be iterated directly.
			for (
				const address of [...region].sort((left, right) => left - right)
			) {
				if (address === startAddress) continue;
				const block = func.blocks.get(address);
				if (block) {
					protocolStatements.push(...block.body as t.Statement[]);
				}
			}

			const iteratorDecls: Array<{
				kind: 'begin' | 'next';
				ids: t.Identifier[];
				args: t.Expression[];
			}> = [];
			for (const statement of protocolStatements) {
				const foundBegin = intrinsicArrayDecl(
					statement,
					'IteratorBegin',
				);
				const foundNext = intrinsicArrayDecl(statement, 'IteratorNext');
				if (foundBegin) {
					iteratorDecls.push({
						kind: 'begin',
						...foundBegin,
					});
				}
				if (foundNext) {
					iteratorDecls.push({
						kind: 'next',
						...foundNext,
					});
				}
			}
			if (
				iteratorDecls.filter(({ kind }) => kind === 'begin').length !==
					1
			) continue;

			const handlers = [...func.exceptions.records].filter(([, record]) =>
				record.protectedBlocks.size > 0 &&
				[...record.protectedBlocks].every((address) =>
					region.has(address)
				)
			);
			// A handler-free region is the unprotected lowering Hermes emits
			// when no slot target can throw. Its shape is otherwise identical,
			// so the value-based recogniser below still applies -- but only
			// once no handler references the region at all and the region
			// carries no back edge.
			const unprotected = handlers.length === 0;
			if (unprotected && env['ARES_NO_UNPROTECTED_DESTR'] === '1') {
				continue;
			}
			if (
				unprotected &&
				([...func.exceptions.records].some(([, record]) =>
					[...record.protectedBlocks].some((address) =>
						region.has(address)
					)
				) || !regionIsAcyclic(func, region, startAddress))
			) continue;
			const handlerAddresses = new Set(
				handlers.map(([address]) => address),
			);
			if (
				handlers.some(([address]) =>
					!func.blocks.has(address) || region.has(address)
				)
			) continue;

			const abruptBlocks = new Set<number>();
			const abruptPending = unprotected ? [] : [...handlerAddresses];
			let abruptInvalid = false;
			while (abruptPending.length > 0) {
				const address = abruptPending.pop()!;
				if (abruptBlocks.has(address)) continue;
				if (region.has(address) || address === continuation) {
					abruptInvalid = true;
					break;
				}
				const block = func.blocks.get(address);
				if (!block) {
					abruptInvalid = true;
					break;
				}
				abruptBlocks.add(address);
				if (block.consequentAddresses.length === 0) {
					if (
						!t.isThrowStatement(
							(block.body as t.Statement[]).at(-1),
						)
					) {
						abruptInvalid = true;
						break;
					}
					continue;
				}
				abruptPending.push(...block.consequentAddresses);
			}
			if (abruptInvalid) continue;
			if (
				!unprotected && (
					[...handlerAddresses].some((address) =>
						!irBlockContainsIntrinsic(
							func.blocks.get(address)!,
							'Catch',
						)
					) ||
					[...abruptBlocks].filter((address) =>
							iteratorCloseInBlock(
								func.blocks.get(address)!,
								true,
							) != null
						).length !== 1 ||
					[...abruptBlocks].some((address) =>
						[...func.predecessorsOf(address)].some((predecessor) =>
							!abruptBlocks.has(predecessor) &&
							!(handlerAddresses.has(address) &&
								region.has(predecessor))
						)
					)
				)
			) continue;

			const globalNames = collectGlobalNames(
				startBlock.body as t.Statement[],
			);
			const targetEntries: Array<{
				address: number;
				target: NonNullable<ReturnType<typeof assignmentTargetPlan>>;
			}> = [];
			for (const [, handler] of handlers) {
				for (const address of handler.protectedBlocks) {
					const block = func.blocks.get(address)!;
					for (const statement of block.body as t.Statement[]) {
						const target = assignmentTargetPlan(
							statement,
							globalNames,
						);
						if (!target) continue;
						if (
							target.target.kind === 'binding' && target.name &&
							isGeneratedName(target.name)
						) continue;
						targetEntries.push({ address, target });
					}
				}
			}
			targetEntries.sort((left, right) => left.address - right.address);
			const ordinaryTargetsMatch = targetEntries.length > 0 &&
				handlers.length >= targetEntries.length &&
				iteratorDecls.filter(({ kind }) => kind === 'next').length ===
					targetEntries.length;

			const definitions = cfgGeneratedDefinitions(protocolStatements);
			const iteratorSeeds = new Set(
				iteratorDecls.flatMap(({ ids }) => ids.map(({ name }) => name)),
			);
			const derived = cfgIteratorDerivedNames(definitions, iteratorSeeds);
			const values = targetEntries.map(({ target }) =>
				cfgDestructuredValue(target.value, definitions, derived)
			);
			if (ordinaryTargetsMatch && values.some((value) => value == null)) {
				continue;
			}

			const removedBlocks = new Set([...region, ...abruptBlocks]);
			removedBlocks.delete(startAddress);
			const parameterPattern = ordinaryTargetsMatch
				? null
				: cfgProtectedParameterArrayPattern(
					func,
					protocolStatements,
					iteratorDecls,
					removedBlocks,
					startAddress,
					beginIndex,
				);
			if (!ordinaryTargetsMatch && !parameterPattern) continue;
			if (parameterPattern) {
				debugArrayDestr('protected-param: recovered', func.id, {
					elements: parameterPattern.pattern.elements.length,
				});
			}
			if (ordinaryTargetsMatch) {
				const removedDefinitions = new Set(definitions.keys());
				if (
					[...func.blocks].some(([address, block]) =>
						!removedBlocks.has(address) &&
						address !== startAddress &&
						[...removedDefinitions].some((name) =>
							(block.body as t.Statement[]).some((statement) =>
								countIdentifierUses(statement, name) > 0
							)
						)
					)
				) continue;
			}

			const declaredGlobals = new Set<string>();
			const pattern = parameterPattern?.pattern ?? t.arrayPattern(
				targetEntries.map(({ target }, index) => {
					if (
						target.target.kind === 'binding' &&
						target.target.declaredGlobal && target.name
					) declaredGlobals.add(target.name);
					const defaultValue = values[index]!.defaultValue;
					return planToPattern({
						kind: 'target',
						target: target.target,
						defaultValue: defaultValue ?? undefined,
					});
				}),
			);
			const replacement = emitDestructuringPlan({
				pattern,
				source: begin.args[0] as t.Expression,
				declaredGlobals,
				consumed: protocolStatements,
				preservedInputs: [
					begin.args[0] as t.Expression,
					...values.flatMap((value) =>
						value?.defaultValue ? [value.defaultValue] : []
					),
				],
				inlineConsumedResults: [begin.args[0] as t.Expression],
			});
			if (parameterPattern?.aliases.size) {
				for (const [address, block] of func.blocks) {
					if (removedBlocks.has(address)) continue;
					block.body = (block.body as t.Statement[]).map(
						(statement) => {
							let rewritten = statement;
							for (const [from, to] of parameterPattern.aliases) {
								rewritten = replaceIdentifierUse(
									rewritten,
									from,
									t.cloneNode(to, true),
								) as t.Statement;
							}
							return rewritten;
						},
					);
					if (block.branch) {
						let branch = block.branch as t.Expression;
						for (const [from, to] of parameterPattern.aliases) {
							branch = replaceIdentifierUse(
								branch,
								from,
								t.cloneNode(to, true),
							) as t.Expression;
						}
						block.branch = branch;
					}
				}
			}

			startBlock.body.splice(
				beginIndex,
				startBlock.body.length - beginIndex,
				...(parameterPattern?.prelude ?? []),
				replacement,
				...(parameterPattern?.preserved ?? []),
			);
			startBlock.branch = undefined;
			func.exceptions.removeHandlers(handlerAddresses);
			func.setSuccessors(startAddress, [continuation]);
			for (const address of removedBlocks) {
				func.markMergedBlocks(startAddress, address);
			}
			removeDeclaredGlobals(
				startBlock.body as t.Statement[],
				declaredGlobals,
			);
			return true;
		}
	}
	return false;
}

export function reduceIteratorDestructuringSequence(
	func: IRFunction,
): boolean {
	for (const [address, block] of func.blocks) {
		if (block.branch || block.consequentAddresses.length !== 1) continue;
		if (!blockHasIteratorDestructuringPrefix(block)) continue;

		const childAddress = block.consequentAddresses[0];
		const child = func.blocks.get(childAddress);
		if (!child) continue;
		if (func.exceptions.isCatchTarget(childAddress)) continue;
		if (func.predecessorsOf(childAddress).size !== 1) continue;
		if (!blockContinuesIteratorDestructuring(func, child)) continue;

		block.body.push(...child.body);
		block.branch = child.branch;
		block.consequentAddresses = child.consequentAddresses;
		func.markMergedBlocks(address, childAddress);
		return true;
	}
	return false;
}

export function reduceSequentialArrayDestructuring(
	func: IRFunction,
): boolean {
	for (const block of func.blocks.values()) {
		if (
			cleanupSequentialArrayDestructuring(
				func,
				block,
				block.body as t.Statement[],
			)
		) return true;
	}
	return false;
}

/**
 * Fold a recovered destructuring whose source is a binding of the pattern
 * declared immediately above it into that pattern.
 *
 * Hermes lowers `function f([a, [b]])` as two independent iterator protocols:
 * the outer one binds a temporary for the nested element, the inner one
 * consumes that temporary. Both are recovered separately, leaving
 * `var [a, r9_3] = src; var [b] = r9_3;`. Nesting belongs in the pattern the
 * source had -- `PatternPlan` already models nested array/object elements --
 * so this reduces the pair to `var [a, [b]] = src;` and every later consumer,
 * parameter attachment included, sees one semantic destructuring.
 *
 * The two statements must be adjacent and the temporary must have exactly its
 * outer binding and this one use: that proves nothing between them observes
 * the temporary and that moving the inner protocol to the outer statement's
 * position cannot drop an independently visible value.
 */
export function reduceNestedRecoveredDestructuring(
	func: IRFunction,
): boolean {
	for (const block of func.blocks.values()) {
		const body = block.body as t.Statement[];
		for (let index = 0; index + 1 < body.length; index++) {
			const parent = recoveredPatternDeclarator(body[index]);
			const child = recoveredPatternDeclarator(body[index + 1]);
			if (!parent || !child || !t.isIdentifier(child.init)) continue;
			const name = child.init.name;
			if (!isGeneratedName(name)) continue;
			if (countIdentifierUses(parent.id, name) !== 1) continue;
			if (functionIdentifierUses(func, name) !== 2) continue;
			const nested = t.cloneNode(child.id, true) as
				| t.ArrayPattern
				| t.ObjectPattern;
			if (!nestPatternAtBinding(parent.id, name, nested)) continue;
			body.splice(index + 1, 1);
			return true;
		}
	}
	return false;
}

function recoveredPatternDeclarator(
	statement: t.Statement | undefined,
): t.VariableDeclarator | null {
	if (!statement || statement.extra?.fromDestructuring !== true) return null;
	const declarator = singleDeclarator(statement);
	if (!declarator || declarator.extra?.isDeclaredGlobal === true) return null;
	return t.isArrayPattern(declarator.id) || t.isObjectPattern(declarator.id)
		? declarator
		: null;
}

function functionIdentifierUses(func: IRFunction, name: string): number {
	let uses = 0;
	for (const block of func.blocks.values()) {
		for (const statement of block.body as t.Statement[]) {
			uses += countIdentifierUses(statement, name);
		}
		if (block.branch) {
			uses += countIdentifierUses(block.branch as t.Node, name);
		}
	}
	return uses;
}

/** Replace the pattern's `name` binding with a nested pattern, in place. */
function nestPatternAtBinding(
	pattern: t.Node,
	name: string,
	nested: t.ArrayPattern | t.ObjectPattern,
): boolean {
	if (t.isArrayPattern(pattern)) {
		for (let index = 0; index < pattern.elements.length; index++) {
			const element = pattern.elements[index];
			if (!element) continue;
			if (t.isIdentifier(element, { name })) {
				pattern.elements[index] = nested;
				return true;
			}
			if (nestPatternAtBinding(element, name, nested)) return true;
		}
		return false;
	}
	if (t.isObjectPattern(pattern)) {
		for (const property of pattern.properties) {
			if (t.isRestElement(property)) {
				if (t.isIdentifier(property.argument, { name })) return false;
				continue;
			}
			if (t.isIdentifier(property.value, { name })) {
				property.value = nested;
				return true;
			}
			if (nestPatternAtBinding(property.value, name, nested)) return true;
		}
		return false;
	}
	if (t.isAssignmentPattern(pattern)) {
		if (t.isIdentifier(pattern.left, { name })) {
			pattern.left = nested;
			return true;
		}
		return nestPatternAtBinding(pattern.left, name, nested);
	}
	if (t.isRestElement(pattern)) return false;
	return false;
}

export function reduceSequentialObjectDestructuring(
	func: IRFunction,
): boolean {
	return cleanupSequentialObjectDestructuring(func);
}

export function reduceIteratorDestructuringDefaults(
	func: IRFunction,
): boolean {
	for (const [address, block] of func.blocks) {
		if (!block.branch || block.consequentAddresses.length !== 2) continue;
		const [left, right] = block.consequentAddresses;
		const leftBlock = func.blocks.get(left);
		const rightBlock = func.blocks.get(right);
		if (!leftBlock || !rightBlock) continue;

		if (
			irBlockContainsIntrinsic(block, 'IteratorNext') &&
			leftBlock.branch && leftBlock.consequentAddresses.length === 2 &&
			!rightBlock.branch && func.predecessorsOf(left).size === 1 &&
			func.predecessorsOf(right).size === 2 &&
			func.predecessorsOf(right).has(address) &&
			func.predecessorsOf(right).has(left) &&
			func.exceptions.activeHandlersEqual(address, left)
		) {
			const [defaultAddress, joinAddress] = leftBlock.consequentAddresses;
			if (defaultAddress !== right) continue;
			const joinBlock = func.blocks.get(joinAddress);
			if (
				!joinBlock || joinBlock.branch ||
				joinBlock.consequentAddresses.length !== 1 ||
				!irBlockContainsPhi(joinBlock) ||
				rightBlock.consequentAddresses.length !== 1 ||
				rightBlock.consequentAddresses[0] !== joinAddress
			) continue;
			const assignAddress = joinBlock.consequentAddresses[0];
			const assignBlock = func.blocks.get(assignAddress);
			if (
				!assignBlock || assignBlock.branch ||
				assignBlock.consequentAddresses.length !== 1 ||
				func.predecessorsOf(assignAddress).size !== 1
			) continue;

			block.body.push(...leftBlock.body);
			block.body.push(t.ifStatement(
				t.logicalExpression(
					'||',
					block.branch as t.Expression,
					invertTest(leftBlock.branch as t.Expression),
				),
				t.blockStatement(rightBlock.body as t.Statement[]),
			));
			mergeDestructuringBlocksInto(func, address, [
				joinAddress,
				assignAddress,
			]);
			block.branch = undefined;
			block.consequentAddresses = assignBlock.consequentAddresses;
			func.markMergedBlocks(address, left);
			func.markMergedBlocks(address, right);
			return true;
		}

		if (
			!irBlockContainsIntrinsic(leftBlock, 'IteratorNext') ||
			!leftBlock.branch || leftBlock.consequentAddresses.length !== 2 ||
			func.predecessorsOf(left).size !== 1 ||
			func.predecessorsOf(right).size !== 2 ||
			!func.predecessorsOf(right).has(address) ||
			!func.exceptions.activeHandlersEqual(address, left)
		) continue;
		const [valueAddress, defaultAddress] = leftBlock.consequentAddresses;
		const valueBlock = func.blocks.get(valueAddress);
		const defaultBlock = func.blocks.get(defaultAddress);
		if (
			!valueBlock || valueBlock.branch ||
			valueBlock.consequentAddresses.length !== 1 ||
			valueBlock.consequentAddresses[0] !== right ||
			!defaultBlock || defaultBlock.branch ||
			defaultBlock.consequentAddresses.length !== 1
		) continue;
		if (
			!rightBlock.branch || rightBlock.consequentAddresses.length !== 2 ||
			rightBlock.consequentAddresses[0] !== defaultAddress ||
			!irBlockContainsPhi(rightBlock)
		) continue;
		const afterAddress = rightBlock.consequentAddresses[1];
		if (defaultBlock.consequentAddresses[0] !== afterAddress) continue;
		const afterBlock = func.blocks.get(afterAddress);
		if (
			!afterBlock || afterBlock.branch ||
			afterBlock.consequentAddresses.length !== 1 ||
			func.predecessorsOf(afterAddress).size !== 2
		) continue;

		block.body.push(t.ifStatement(
			invertTest(block.branch as t.Expression),
			t.blockStatement([
				...(leftBlock.body as t.Statement[]),
				t.ifStatement(
					invertTest(leftBlock.branch as t.Expression),
					t.blockStatement(valueBlock.body as t.Statement[]),
				),
			]),
		));
		block.body.push(...rightBlock.body);
		block.body.push(t.ifStatement(
			invertTest(rightBlock.branch as t.Expression),
			t.blockStatement(defaultBlock.body as t.Statement[]),
		));
		mergeDestructuringBlocksInto(func, address, [afterAddress]);
		block.branch = undefined;
		block.consequentAddresses = afterBlock.consequentAddresses;
		for (const merged of [left, valueAddress, right, defaultAddress]) {
			func.markMergedBlocks(address, merged);
		}
		return true;
	}
	return false;
}

function collectPatternPreservedNodes(
	pattern: t.ArrayPattern,
	out: t.Node[],
) {
	for (const element of pattern.elements) {
		if (!element) continue;
		const unwrapped = t.isRestElement(element) ? element.argument : element;
		if (t.isAssignmentPattern(unwrapped)) {
			out.push(unwrapped.right as t.Expression);
		} else if (t.isArrayPattern(unwrapped)) {
			collectPatternPreservedNodes(unwrapped, out);
		}
	}
}

function collectPatternBindingNames(pattern: t.Node, out: Set<string>) {
	if (t.isIdentifier(pattern)) {
		out.add(pattern.name);
	} else if (t.isRestElement(pattern)) {
		collectPatternBindingNames(pattern.argument, out);
	} else if (t.isAssignmentPattern(pattern)) {
		collectPatternBindingNames(pattern.left, out);
	} else if (t.isArrayPattern(pattern)) {
		for (const element of pattern.elements) {
			if (element) collectPatternBindingNames(element, out);
		}
	} else if (t.isObjectPattern(pattern)) {
		for (const property of pattern.properties) {
			if (t.isRestElement(property)) {
				collectPatternBindingNames(property.argument, out);
			} else if (
				t.isIdentifier(property.value) ||
				t.isRestElement(property.value) ||
				t.isAssignmentPattern(property.value) ||
				t.isArrayPattern(property.value) ||
				t.isObjectPattern(property.value)
			) {
				collectPatternBindingNames(property.value, out);
			}
		}
	}
}

function singleReturnInBody(body: t.Statement[]): t.ReturnStatement | null {
	return body.length === 1 && t.isReturnStatement(body[0]) ? body[0] : null;
}

function directIteratorCloseUsesState(
	stmt: t.Statement | undefined,
	stateName: string,
): boolean {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	if (
		!t.isCallExpression(expr) ||
		!t.isV8IntrinsicIdentifier(expr.callee, { name: 'IteratorClose' })
	) return false;
	const [stateArg] = expr.arguments;
	if (t.isIdentifier(stateArg, { name: stateName })) return true;
	return t.isCallExpression(stateArg) &&
		t.isV8IntrinsicIdentifier(stateArg.callee, { name: 'Phi' }) &&
		stateArg.arguments.some((arg) =>
			t.isIdentifier(arg, { name: stateName })
		);
}

function generatedRegisterCoordinates(
	name: string,
): { index: number; version: number } | null {
	const match = /^r(\d+)_(\d+)$/.exec(name);
	return match
		? { index: Number(match[1]), version: Number(match[2]) }
		: null;
}

function identifierResolvesToRegisterName(
	identifier: t.Identifier,
	expectedName: string,
): boolean {
	if (identifier.name === expectedName) return true;
	const expected = generatedRegisterCoordinates(expectedName);
	const location = locationOf(identifier);
	return !!expected && location?.kind === 'register' &&
		location.register.index === expected.index &&
		location.register.version === expected.version;
}

function generatedRegisterIndexMatches(
	identifier: t.Identifier,
	expectedName: string,
): boolean {
	if (identifier.name === expectedName) return true;
	const actual = generatedRegisterCoordinates(identifier.name);
	const expected = generatedRegisterCoordinates(expectedName);
	return !!actual && !!expected && actual.index === expected.index;
}

function directIteratorCloseResolvesState(
	stmt: t.Statement | undefined,
	stateName: string,
): boolean {
	if (!t.isExpressionStatement(stmt)) return false;
	const expression = stmt.expression;
	if (
		!t.isCallExpression(expression) ||
		!t.isV8IntrinsicIdentifier(expression.callee, {
			name: 'IteratorClose',
		})
	) return false;
	const [state] = expression.arguments;
	return t.isIdentifier(state) &&
		identifierResolvesToRegisterName(state, stateName);
}

function preferredCarriedBindingName(
	statements: readonly t.Statement[],
	carrierName: string,
): string {
	const expected = generatedRegisterCoordinates(carrierName);
	if (!expected) return carrierName;
	const aliases = new Set<string>();
	for (const statement of statements) {
		t.traverseFast(statement, (node) => {
			if (!t.isIdentifier(node)) return;
			const location = locationOf(node);
			if (
				location?.kind === 'register' &&
				location.register.index === expected.index &&
				location.register.version === expected.version
			) aliases.add(node.name);
		});
	}
	return aliases.size === 1 ? [...aliases][0] : carrierName;
}

function terminalIteratorEmptyGuardReturn(
	stmt: t.Statement | undefined,
	stateName: string,
): t.ReturnStatement | null {
	if (
		!t.isIfStatement(stmt) ||
		stmt.alternate ||
		!t.isBlockStatement(stmt.consequent) ||
		getUndefinedCheckName(stmt.test) !== stateName
	) return null;

	const body = stmt.consequent.body;
	const directReturn = singleReturnInBody(body);
	if (directReturn) return directReturn;

	if (body.length !== 3) return null;
	const nested = body[0];
	if (
		!t.isIfStatement(nested) ||
		nested.alternate ||
		!t.isBlockStatement(nested.consequent) ||
		getUndefinedCheckName(nested.test) !== stateName
	) return null;
	const nestedReturn = singleReturnInBody(nested.consequent.body);
	if (!nestedReturn) return null;
	if (!directIteratorCloseUsesState(body[1], stateName)) return null;
	const trailingReturn = t.isReturnStatement(body[2]) ? body[2] : null;
	if (!trailingReturn) return null;
	return returnsEquivalent(nestedReturn, trailingReturn)
		? nestedReturn
		: null;
}

function returnArgument(
	stmt: t.ReturnStatement,
): t.Expression {
	return stmt.argument && t.isExpression(stmt.argument)
		? stmt.argument
		: t.identifier('undefined');
}

function returnsEquivalent(
	left: t.ReturnStatement,
	right: t.ReturnStatement,
): boolean {
	return expressionsEqual(returnArgument(left), returnArgument(right));
}

function returnEquivalentAfterReplacing(
	actual: t.ReturnStatement,
	expected: t.ReturnStatement,
	name: string,
	replacement: t.Expression,
): boolean {
	const expectedArg = replaceIdentifierUse(
		returnArgument(expected),
		name,
		replacement,
	) as t.Expression;
	return expressionsEqual(returnArgument(actual), expectedArg);
}

function terminalDoneGuardReturn(
	stmt: t.Statement | undefined,
	doneName: string,
): t.ReturnStatement | null {
	if (
		!t.isIfStatement(stmt) ||
		stmt.alternate ||
		!t.isIdentifier(stmt.test, { name: doneName }) ||
		!t.isBlockStatement(stmt.consequent)
	) return null;
	return singleReturnInBody(stmt.consequent.body);
}

function normalizeTerminalStatements(
	stmts: t.Statement[],
	allowImplicitUndefinedReturn: boolean,
): t.Statement[] | null {
	if (stmts.length === 0) return null;
	if (!statementListEndsAbruptly(stmts)) {
		if (!allowImplicitUndefinedReturn) return null;
		const out = stmts.map((stmt) => t.cloneNode(stmt, true));
		out.push(t.returnStatement(t.identifier('undefined')));
		return out;
	}

	const out = stmts.map((stmt) => t.cloneNode(stmt, true));
	const last = out.at(-1);
	if (t.isReturnStatement(last) && !last.argument) {
		last.argument = t.identifier('undefined');
	}
	return out;
}

function terminalStatementsEquivalent(
	left: t.Statement[],
	right: t.Statement[],
): boolean {
	const normalizedLeft = normalizeTerminalStatements(left, false);
	const normalizedRight = normalizeTerminalStatements(right, false);
	if (!normalizedLeft || !normalizedRight) return false;
	return JSON.stringify(comparableAst(normalizedLeft)) ===
		JSON.stringify(comparableAst(normalizedRight));
}

function terminalStatementsEquivalentAfterReplacing(
	actual: t.Statement[],
	expected: t.Statement[],
	name: string,
	replacement: t.Expression,
): boolean {
	const normalizedActual = normalizeTerminalStatements(actual, false);
	const normalizedExpected = normalizeTerminalStatements(expected, false);
	if (!normalizedActual || !normalizedExpected) return false;
	const replacedExpected = normalizedExpected.map((stmt) =>
		replaceIdentifierUse(stmt, name, replacement) as t.Statement
	);
	return JSON.stringify(comparableAst(normalizedActual)) ===
		JSON.stringify(comparableAst(replacedExpected));
}

function terminalIteratorEmptyGuardStatements(
	stmt: t.Statement | undefined,
	stateName: string,
): t.Statement[] | null {
	if (
		!t.isIfStatement(stmt) ||
		stmt.alternate ||
		!t.isBlockStatement(stmt.consequent) ||
		getUndefinedCheckName(stmt.test) !== stateName
	) return null;

	const body = stmt.consequent.body;
	if (body.length >= 3) {
		const nested = body[0];
		if (
			t.isIfStatement(nested) &&
			!nested.alternate &&
			t.isBlockStatement(nested.consequent) &&
			getUndefinedCheckName(nested.test) === stateName &&
			statementListEndsAbruptly(nested.consequent.body) &&
			directIteratorCloseUsesState(body[1], stateName)
		) {
			const trailing = body.slice(2);
			return terminalStatementsEquivalent(
					nested.consequent.body,
					trailing,
				)
				? nested.consequent.body
				: null;
		}
	}

	if (body.length >= 2) {
		const nested = body[0];
		if (
			t.isIfStatement(nested) &&
			!nested.alternate &&
			t.isBlockStatement(nested.consequent) &&
			nested.consequent.body.length === 1 &&
			directIteratorCloseUsesState(
				nested.consequent.body[0],
				stateName,
			)
		) {
			const trailing = body.slice(1);
			return statementListEndsAbruptly(trailing) ? trailing : null;
		}
		if (
			t.isIfStatement(nested) &&
			!nested.alternate &&
			t.isBlockStatement(nested.consequent) &&
			getUndefinedCheckName(nested.test) === stateName &&
			statementListEndsAbruptly(nested.consequent.body) &&
			!body.some((child) => statementContainsIteratorClose(child))
		) {
			const trailing = body.slice(1);
			return terminalStatementsEquivalent(
					nested.consequent.body,
					trailing,
				)
				? nested.consequent.body
				: null;
		}
	}

	if (body.some((child) => statementContainsIteratorClose(child))) {
		return null;
	}
	return statementListEndsAbruptly(body) ? body : null;
}

function terminalDoneGuardStatements(
	stmt: t.Statement | undefined,
	doneName: string,
): t.Statement[] | null {
	if (
		!t.isIfStatement(stmt) ||
		stmt.alternate ||
		!t.isIdentifier(stmt.test, { name: doneName }) ||
		!t.isBlockStatement(stmt.consequent) ||
		!statementListEndsAbruptly(stmt.consequent.body)
	) return null;
	return stmt.consequent.body;
}

function finalTerminalStatements(
	body: t.Statement[],
	start: number,
): t.Statement[] | null {
	if (t.isReturnStatement(body[start])) return [body[start]];
	if (
		start === body.length - 2 &&
		t.isExpressionStatement(body[start]) &&
		t.isReturnStatement(body[start + 1])
	) return [body[start], body[start + 1]];
	if (start === body.length - 1 && t.isExpressionStatement(body[start])) {
		return normalizeTerminalStatements([body[start]], true);
	}
	const tail = body.slice(start);
	if (statementListEndsAbruptly(tail)) return tail;
	return null;
}

function collectGeneratedStatementDefinitions(
	stmt: t.Statement,
	out: Set<string>,
): void {
	if (t.isVariableDeclaration(stmt)) {
		for (const decl of stmt.declarations) {
			if (t.isIdentifier(decl.id) && isGeneratedName(decl.id.name)) {
				out.add(decl.id.name);
			} else if (t.isArrayPattern(decl.id)) {
				for (const element of decl.id.elements) {
					if (
						t.isIdentifier(element) && isGeneratedName(element.name)
					) {
						out.add(element.name);
					}
				}
			}
		}
		return;
	}

	const assign = expressionStatementAssignment(stmt);
	if (
		assign &&
		t.isIdentifier(assign.left) &&
		isGeneratedName(assign.left.name)
	) {
		out.add(assign.left.name);
		return;
	}

	if (t.isIfStatement(stmt)) {
		if (t.isBlockStatement(stmt.consequent)) {
			for (const child of stmt.consequent.body) {
				collectGeneratedStatementDefinitions(child, out);
			}
		}
		if (t.isBlockStatement(stmt.alternate)) {
			for (const child of stmt.alternate.body) {
				collectGeneratedStatementDefinitions(child, out);
			}
		}
	}
}

function collectGeneratedDefinitionsInStatements(
	stmts: t.Statement[],
): Set<string> {
	const out = new Set<string>();
	for (const stmt of stmts) collectGeneratedStatementDefinitions(stmt, out);
	return out;
}

function assignmentTargetPlan(
	stmt: t.Statement | undefined,
	globalNames: ReadonlySet<string>,
): { target: TargetPlan; name?: string; value: t.Expression } | null {
	const declaration = singleDeclarator(stmt);
	if (
		declaration && t.isIdentifier(declaration.id) &&
		declaration.init && t.isExpression(declaration.init)
	) {
		return {
			target: bindingTarget(
				declaration.id.name,
				declaration.extra?.isDeclaredGlobal === true,
			),
			name: declaration.id.name,
			value: declaration.init,
		};
	}
	const assign = expressionStatementAssignment(stmt);
	if (!assign || !t.isExpression(assign.right) || !t.isLVal(assign.left)) {
		return null;
	}
	if (t.isIdentifier(assign.left)) {
		return {
			target: bindingTarget(assign.left.name, false),
			name: assign.left.name,
			value: assign.right,
		};
	}
	if (
		t.isMemberExpression(assign.left, { computed: false }) &&
		t.isIdentifier(assign.left.object) &&
		globalNames.has(assign.left.object.name) &&
		t.isIdentifier(assign.left.property)
	) {
		return {
			target: bindingTarget(assign.left.property.name, true),
			name: assign.left.property.name,
			value: assign.right,
		};
	}
	if (!t.isMemberExpression(assign.left)) return null;
	return {
		target: {
			kind: 'assign',
			lval: t.cloneNode(assign.left, true) as t.LVal,
		},
		value: assign.right,
	};
}

function compactIteratorDefault(
	expr: t.Expression,
	valueName: string,
	stateName: string,
): t.Expression | null {
	if (
		!t.isConditionalExpression(expr) ||
		getUndefinedCheckName(expr.test) !== stateName ||
		!t.isConditionalExpression(expr.alternate) ||
		getUndefinedCheckName(expr.alternate.test) !== valueName ||
		!t.isIdentifier(expr.alternate.alternate, { name: valueName }) ||
		!expressionsEqual(expr.consequent, expr.alternate.consequent)
	) return null;
	return expr.consequent;
}

function singleGeneratedDeclaration(
	stmt: t.Statement | undefined,
): { name: string; init: t.Expression | null } | null {
	const decl = singleDeclarator(stmt);
	if (!decl || !t.isIdentifier(decl.id) || !isGeneratedName(decl.id.name)) {
		return null;
	}
	return {
		name: decl.id.name,
		init: t.isExpression(decl.init) ? decl.init : null,
	};
}

function phiContainsNames(
	expr: t.Expression,
	names: ReadonlySet<string>,
): boolean {
	return t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, { name: 'Phi' }) &&
		[...names].every((name) =>
			expr.arguments.some((arg) => t.isIdentifier(arg, { name }))
		);
}

function assignmentMatches(
	stmt: t.Statement | undefined,
	target: string,
	value: string,
): boolean {
	const assign = assignmentToIdentifier(stmt, target);
	return !!assign && t.isIdentifier(assign.right, { name: value });
}

/** Recover V96's two-default array pattern after the iterator state has been
 * carried through SSA joins. The mechanically distinctive trailer is
 * `if (done) terminal; IteratorClose(state); terminal`, which proves that the
 * close and both completion copies belong to the destructuring operation. */
function cleanupPhiCarriedTwoDefaultArrayDestructuring(
	func: IRFunction,
	block: IRBlock,
	body: t.Statement[],
	globalNames: Set<string>,
): boolean {
	debugArrayDestr('phi-two-default scan', body.length);
	for (let i = 0; i <= body.length - 14; i++) {
		const begin = intrinsicArrayDecl(body[i], 'IteratorBegin');
		const firstNext = intrinsicArrayDecl(body[i + 1], 'IteratorNext');
		if (
			!begin || begin.ids.length !== 2 || begin.args.length !== 1 ||
			!firstNext || firstNext.ids.length !== 2 ||
			firstNext.args.length !== 2 ||
			!t.isIdentifier(firstNext.args[0], { name: begin.ids[0].name }) ||
			!t.isIdentifier(firstNext.args[1], { name: begin.ids[1].name })
		) continue;
		const fail = (stage: string) => {
			debugArrayDestr('phi-two-default fail', i, stage);
			return false;
		};

		const firstTarget = assignmentTargetPlan(body[i + 2], globalNames);
		if (!firstTarget) {
			fail('first-target');
			continue;
		}
		const firstDefault = compactIteratorDefault(
			firstTarget.value,
			firstNext.ids[0].name,
			firstNext.ids[1].name,
		);
		if (!firstDefault) {
			fail('first-default');
			continue;
		}

		const secondValue = singleGeneratedDeclaration(body[i + 3]);
		const done = singleGeneratedDeclaration(body[i + 4]);
		if (
			!secondValue || !isUndefinedNode(secondValue.init) ||
			!done?.init ||
			getUndefinedCheckName(done.init) !== firstNext.ids[1].name
		) {
			fail('initial-carries');
			continue;
		}

		let state = singleGeneratedDeclaration(body[i + 5]);
		const hasInitialState = !!state?.init &&
			t.isIdentifier(state.init, { name: firstNext.ids[1].name });
		const advance = body[i + (hasInitialState ? 6 : 5)];
		if (
			!t.isIfStatement(advance) || advance.alternate ||
			!t.isBlockStatement(advance.consequent) ||
			!isIteratorNotDoneCheck(advance.test, firstNext.ids[1].name)
		) {
			fail('advance-guard');
			continue;
		}
		const advanceBody = advance.consequent.body;
		const secondNext = intrinsicArrayDecl(advanceBody[0], 'IteratorNext');
		const doneAssignmentIndex = hasInitialState ? 2 : 1;
		const valueGuardIndex = hasInitialState ? 3 : 2;
		if (
			!secondNext || secondNext.ids.length !== 2 ||
			secondNext.args.length !== 2 ||
			!t.isIdentifier(secondNext.args[0], {
				name: firstNext.ids[1].name,
			}) ||
			!t.isIdentifier(secondNext.args[1], { name: begin.ids[1].name }) ||
			(hasInitialState && (!state || !assignmentMatches(
				advanceBody[1],
				state.name,
				secondNext.ids[1].name,
			)))
		) {
			fail('advance');
			continue;
		}
		const doneAssign = assignmentToIdentifier(
			advanceBody[doneAssignmentIndex],
			done.name,
		);
		if (
			!doneAssign || !t.isExpression(doneAssign.right) ||
			getUndefinedCheckName(doneAssign.right) !== secondNext.ids[1].name
		) {
			fail('done-assign');
			continue;
		}
		const valueGuard = advanceBody[valueGuardIndex];
		if (
			!t.isIfStatement(valueGuard) || valueGuard.alternate ||
			!t.isBlockStatement(valueGuard.consequent) ||
			!isIteratorNotDoneCheck(valueGuard.test, secondNext.ids[1].name) ||
			!assignmentMatches(
				valueGuard.consequent.body[0],
				secondValue.name,
				secondNext.ids[0].name,
			)
		) {
			fail('value-guard');
			continue;
		}
		if (!hasInitialState) {
			state = singleGeneratedDeclaration(body[i + 6]);
			if (
				!state?.init ||
				!phiContainsNames(
					state.init,
					new Set([
						firstNext.ids[1].name,
						secondNext.ids[1].name,
					]),
				)
			) {
				fail('state-phi');
				continue;
			}
		}
		if (!state) continue;

		const finalValue = singleGeneratedDeclaration(body[i + 7]);
		const finalDone = singleGeneratedDeclaration(body[i + 8]);
		const finalState = singleGeneratedDeclaration(body[i + 9]);
		if (
			!finalValue?.init ||
			!t.isIdentifier(finalValue.init, { name: secondValue.name }) ||
			!finalDone?.init ||
			!t.isIdentifier(finalDone.init, { name: done.name }) ||
			!finalState?.init ||
			!(t.isIdentifier(finalState.init, { name: state.name }) ||
				phiContainsNames(finalState.init, new Set([state.name])) ||
				(state.init != null &&
					expressionsEqual(finalState.init, state.init)))
		) {
			fail('final-carries');
			continue;
		}

		const defaultGuard = body[i + 10];
		if (
			!t.isIfStatement(defaultGuard) || defaultGuard.alternate ||
			!t.isBlockStatement(defaultGuard.consequent) ||
			getUndefinedCheckName(defaultGuard.test) !== secondValue.name
		) {
			fail('default-guard');
			continue;
		}
		const defaultBody = defaultGuard.consequent.body;
		if (
			!assignmentMatches(defaultBody[0], finalDone.name, done.name) ||
			!assignmentMatches(defaultBody[1], finalState.name, state.name)
		) {
			fail('default-carries');
			continue;
		}
		const secondDefaultAssign = assignmentToIdentifier(
			defaultBody[2],
			finalValue.name,
		);
		if (
			!secondDefaultAssign || !t.isExpression(secondDefaultAssign.right)
		) {
			fail('second-default');
			continue;
		}

		const secondTarget = assignmentTargetPlan(body[i + 11], globalNames);
		if (
			!secondTarget ||
			!t.isIdentifier(secondTarget.value, { name: finalValue.name })
		) {
			fail('second-target');
			continue;
		}
		const doneGuard = body[i + 12];
		if (
			!t.isIfStatement(doneGuard) || doneGuard.alternate ||
			!t.isIdentifier(doneGuard.test, { name: finalDone.name }) ||
			!t.isBlockStatement(doneGuard.consequent) ||
			!statementListEndsAbruptly(doneGuard.consequent.body)
		) {
			fail('done-guard');
			continue;
		}
		const closeEnd = consumeIteratorCloseStatePhi(
			body,
			i + 13,
			finalState.name,
		);
		if (closeEnd !== i + 14) {
			fail('close');
			continue;
		}
		const finalTail = finalTerminalStatements(body, closeEnd);
		if (
			!finalTail ||
			!terminalStatementsEquivalent(doneGuard.consequent.body, finalTail)
		) {
			fail('terminal-equivalence');
			continue;
		}

		const source = begin.args[0];
		const pattern = t.arrayPattern([
			planToPattern({
				kind: 'target',
				target: firstTarget.target,
				defaultValue: firstDefault,
			}),
			planToPattern({
				kind: 'target',
				target: secondTarget.target,
				defaultValue: secondDefaultAssign.right,
			}),
		]);
		const consumed = body.slice(i, closeEnd);
		const declaredGlobals = new Set(
			[firstTarget, secondTarget].flatMap((target) =>
				target.target.kind === 'binding' &&
					target.target.declaredGlobal &&
					target.name
					? [target.name]
					: []
			),
		);
		const escapedNames = new Set(
			[firstTarget.name, secondTarget.name].filter(
				(name): name is string => !!name,
			),
		);
		if (
			!consumedDefinitionsAreDead(
				func,
				block,
				consumed,
				[
					source,
					firstDefault,
					secondDefaultAssign.right,
					...finalTail,
					t.identifier('undefined'),
					t.identifier('global'),
				],
				[source],
				escapedNames,
				false,
				body,
			)
		) {
			fail('liveness');
			continue;
		}

		body.splice(
			i,
			closeEnd - i,
			emitDestructuringPlan({
				pattern,
				source,
				declaredGlobals,
				consumed,
				preservedInputs: [
					source,
					firstDefault,
					secondDefaultAssign.right,
				],
				inlineConsumedResults: [source],
			}),
		);
		removeDeclaredGlobals(body, declaredGlobals);
		return true;
	}
	return false;
}

function catchCopiesTo(
	clause: t.CatchClause | null | undefined,
	targetName: string,
): boolean {
	if (
		!clause || !t.isIdentifier(clause.param) ||
		clause.body.body.length !== 1
	) return false;
	const assign = assignmentToIdentifier(clause.body.body[0], targetName);
	return !!assign && t.isIdentifier(assign.right, {
		name: clause.param.name,
	});
}

function throwOf(
	stmt: t.Statement | undefined,
	name: string,
): boolean {
	return t.isThrowStatement(stmt) &&
		t.isIdentifier(stmt.argument, { name });
}

function conditionalThrowOf(
	stmt: t.Statement | undefined,
	testName: string,
	errorName: string,
): boolean {
	if (
		!t.isIfStatement(stmt) || stmt.alternate ||
		!t.isIdentifier(stmt.test, { name: testName }) ||
		!t.isBlockStatement(stmt.consequent) ||
		stmt.consequent.body.length !== 1
	) return false;
	return throwOf(stmt.consequent.body[0], errorName);
}

function removeDirectDeclarators(
	body: t.Statement[],
	names: ReadonlySet<string>,
): void {
	for (let i = 0; i < body.length; i++) {
		const statement = body[i];
		if (!t.isVariableDeclaration(statement)) continue;
		statement.declarations = statement.declarations.filter((declaration) =>
			!t.isIdentifier(declaration.id) || !names.has(declaration.id.name)
		);
		if (statement.declarations.length === 0) {
			body.splice(i, 1);
			i--;
		}
	}
}

function generatedNamesUsedInStatements(
	statements: readonly t.Statement[],
	names: ReadonlySet<string>,
): boolean {
	return statements.some((statement) =>
		[...names].some((name) => countIdentifierUses(statement, name) > 0)
	);
}

/**
 * Recover the protected V96/V99 two-default lowering as one array pattern.
 * The surrounding nested catches and duplicated throw trailer are the
 * compiler's abrupt IteratorClose machinery. Matching the wrapper as well as
 * the protocol body lets the replacement rely on JavaScript destructuring to
 * provide exactly that close-on-abrupt behavior.
 */
function cleanupProtectedTwoDefaultArrayDestructuring(
	func: IRFunction,
	block: IRBlock,
	body: t.Statement[],
): boolean {
	const globalNames = collectGlobalNames(body);
	for (let wrapperIndex = 0; wrapperIndex < body.length - 2; wrapperIndex++) {
		const outer = body[wrapperIndex];
		if (
			!t.isTryStatement(outer) || outer.finalizer ||
			outer.block.body.length !== 1
		) continue;
		const inner = outer.block.body[0];
		if (
			!t.isTryStatement(inner) || inner.finalizer ||
			inner.block.body.length === 0
		) continue;

		const outerCatchAssign = inner.handler && outer.handler
			? expressionStatementAssignment(outer.handler.body.body[0])
			: null;
		if (
			!outerCatchAssign || !t.isIdentifier(outerCatchAssign.left) ||
			!catchCopiesTo(outer.handler, outerCatchAssign.left.name) ||
			!catchCopiesTo(inner.handler, outerCatchAssign.left.name)
		) continue;
		const errorName = outerCatchAssign.left.name;

		const innerBody = inner.block.body;
		for (let i = 0; i < innerBody.length - 12; i++) {
			const begin = intrinsicArrayDecl(innerBody[i], 'IteratorBegin');
			const firstNext = intrinsicArrayDecl(
				innerBody[i + 1],
				'IteratorNext',
			);
			if (
				!begin || begin.ids.length !== 2 || begin.args.length !== 1 ||
				!firstNext || firstNext.ids.length !== 2 ||
				firstNext.args.length !== 2 ||
				!t.isIdentifier(firstNext.args[0], {
					name: begin.ids[0].name,
				}) ||
				!t.isIdentifier(firstNext.args[1], {
					name: begin.ids[1].name,
				})
			) continue;

			const initialDone = assignmentTargetPlan(
				innerBody[i + 2],
				globalNames,
			);
			if (
				!initialDone?.name || initialDone.target.kind !== 'binding' ||
				getUndefinedCheckName(initialDone.value) !==
					firstNext.ids[1].name
			) continue;
			const firstTarget = assignmentTargetPlan(
				innerBody[i + 3],
				globalNames,
			);
			if (!firstTarget) continue;
			const firstDefault = compactIteratorDefault(
				firstTarget.value,
				firstNext.ids[0].name,
				firstNext.ids[1].name,
			);
			if (!firstDefault) continue;

			const secondValue = singleGeneratedDeclaration(innerBody[i + 4]);
			const done = singleGeneratedDeclaration(innerBody[i + 5]);
			const state = singleGeneratedDeclaration(innerBody[i + 6]);
			if (
				!secondValue || !isUndefinedNode(secondValue.init) ||
				!done?.init ||
				getUndefinedCheckName(done.init) !== firstNext.ids[1].name ||
				!state?.init || !t.isIdentifier(state.init, {
					name: firstNext.ids[1].name,
				})
			) continue;

			const advance = innerBody[i + 7];
			if (
				!t.isIfStatement(advance) || advance.alternate ||
				!t.isUnaryExpression(advance.test, { operator: '!' }) ||
				!t.isIdentifier(advance.test.argument, {
					name: initialDone.name,
				}) ||
				!t.isBlockStatement(advance.consequent)
			) continue;
			const advanceBody = advance.consequent.body;
			const secondNext = intrinsicArrayDecl(
				advanceBody[0],
				'IteratorNext',
			);
			if (
				!secondNext || secondNext.ids.length !== 2 ||
				secondNext.args.length !== 2 ||
				!t.isIdentifier(secondNext.args[0], {
					name: firstNext.ids[1].name,
				}) ||
				!t.isIdentifier(secondNext.args[1], {
					name: begin.ids[1].name,
				}) ||
				!assignmentMatches(
					advanceBody[1],
					state.name,
					secondNext.ids[1].name,
				)
			) continue;
			const doneAssign = assignmentToIdentifier(
				advanceBody[2],
				done.name,
			);
			const valueGuard = advanceBody[3];
			if (
				!doneAssign || !t.isExpression(doneAssign.right) ||
				getUndefinedCheckName(doneAssign.right) !==
					secondNext.ids[1].name ||
				!t.isIfStatement(valueGuard) || valueGuard.alternate ||
				!t.isBlockStatement(valueGuard.consequent) ||
				!isIteratorNotDoneCheck(
					valueGuard.test,
					secondNext.ids[1].name,
				) ||
				!assignmentMatches(
					valueGuard.consequent.body[0],
					secondValue.name,
					secondNext.ids[0].name,
				)
			) continue;

			const finalValue = singleGeneratedDeclaration(innerBody[i + 8]);
			const carryDone = assignmentToIdentifier(
				innerBody[i + 9],
				initialDone.name,
			);
			const carryState =
				assignmentToIdentifier(innerBody[i + 10], state.name) ??
					expressionStatementAssignment(innerBody[i + 10]);
			if (
				!finalValue?.init || !t.isIdentifier(finalValue.init, {
					name: secondValue.name,
				}) ||
				!carryDone || !t.isIdentifier(carryDone.right, {
					name: done.name,
				}) ||
				!carryState || !t.isIdentifier(carryState.left)
			) continue;
			const finalStateName = carryState.left.name;
			if (
				!t.isExpression(carryState.right) ||
				!(t.isIdentifier(carryState.right, { name: state.name }) ||
					phiContainsNames(
						carryState.right,
						new Set([
							firstNext.ids[1].name,
							secondNext.ids[1].name,
						]),
					))
			) continue;

			const defaultGuard = innerBody[i + 11];
			if (
				!t.isIfStatement(defaultGuard) || defaultGuard.alternate ||
				!t.isBlockStatement(defaultGuard.consequent) ||
				getUndefinedCheckName(defaultGuard.test) !== secondValue.name
			) continue;
			const defaultBody = defaultGuard.consequent.body;
			const secondDefaultAssign = defaultBody
				.map((statement) =>
					assignmentToIdentifier(statement, finalValue.name)
				)
				.find((assignment) => assignment != null);
			if (
				!secondDefaultAssign ||
				!t.isExpression(secondDefaultAssign.right)
			) {
				continue;
			}

			const secondTarget = assignmentTargetPlan(
				innerBody[i + 12],
				globalNames,
			);
			if (
				!secondTarget || !t.isIdentifier(secondTarget.value, {
					name: finalValue.name,
				})
			) continue;
			const closeGuard = innerBody[i + 13];
			if (
				!t.isIfStatement(closeGuard) || closeGuard.alternate ||
				!t.isUnaryExpression(closeGuard.test, { operator: '!' }) ||
				!t.isIdentifier(closeGuard.test.argument, {
					name: initialDone.name,
				}) ||
				!t.isBlockStatement(closeGuard.consequent) ||
				closeGuard.consequent.body.length !== 1
			) continue;
			const close = closeGuard.consequent.body[0];
			if (
				!t.isExpressionStatement(close) ||
				!t.isCallExpression(close.expression) ||
				!t.isV8IntrinsicIdentifier(close.expression.callee, {
					name: 'IteratorClose',
				}) ||
				!t.isIdentifier(close.expression.arguments[0], {
					name: finalStateName,
				})
			) continue;

			if (
				!conditionalThrowOf(
					body[wrapperIndex + 1],
					initialDone.name,
					errorName,
				) ||
				!throwOf(body[wrapperIndex + 2], errorName)
			) continue;

			const protocolNames = new Set([
				...begin.ids.map((id) => id.name),
				...firstNext.ids.map((id) => id.name),
				...secondNext.ids.map((id) => id.name),
				initialDone.name,
				secondValue.name,
				done.name,
				state.name,
				finalValue.name,
				finalStateName,
				errorName,
			]);
			if (
				generatedNamesUsedInStatements(
					innerBody.slice(i + 14),
					protocolNames,
				)
			) continue;

			const pattern = t.arrayPattern([
				planToPattern({
					kind: 'target',
					target: firstTarget.target,
					defaultValue: firstDefault,
				}),
				planToPattern({
					kind: 'target',
					target: secondTarget.target,
					defaultValue: secondDefaultAssign.right,
				}),
			]);
			const declaredGlobals = new Set(
				[firstTarget, secondTarget].flatMap((target) =>
					target.target.kind === 'binding' &&
						target.target.declaredGlobal && target.name
						? [target.name]
						: []
				),
			);
			innerBody.splice(
				i,
				14,
				emitDestructuringPlan({
					pattern,
					source: begin.args[0] as t.Expression,
					declaredGlobals,
					consumed: [],
					preservedInputs: [
						begin.args[0] as t.Expression,
						firstDefault,
						secondDefaultAssign.right,
					],
					inlineConsumedResults: [begin.args[0] as t.Expression],
				}),
			);

			body.splice(
				wrapperIndex,
				3,
				...innerBody.map((statement) => t.cloneNode(statement, true)),
			);
			removeDirectDeclarators(body, protocolNames);
			removeDeclaredGlobals(body, declaredGlobals);
			return true;
		}
	}
	return false;
}

function identifierAssignments(
	body: readonly t.Statement[],
): Map<string, t.Expression> | null {
	const assignments = new Map<string, t.Expression>();
	for (const statement of body) {
		const assignment = expressionStatementAssignment(statement);
		if (
			!assignment || !t.isIdentifier(assignment.left) ||
			!t.isExpression(assignment.right) ||
			assignments.has(assignment.left.name)
		) return null;
		assignments.set(assignment.left.name, assignment.right);
	}
	return assignments;
}

function assignmentNameWithValue(
	assignments: ReadonlyMap<string, t.Expression>,
	predicate: (value: t.Expression) => boolean,
): string | null {
	const matches = [...assignments].filter(([, value]) => predicate(value));
	return matches.length === 1 ? matches[0][0] : null;
}

function returnsIdentifier(
	statement: t.Statement | undefined,
	name: string,
): boolean {
	return t.isReturnStatement(statement) &&
		t.isIdentifier(statement.argument, { name });
}

interface TerminalArrayDestructuringCandidate {
	start: number;
	end: number;
	pattern: t.ArrayPattern;
	source: t.Expression;
	preservedInputs: t.Node[];
	followingStatements?: t.Statement[];
}

/** Describe the compact terminal form used for `([value]) => use(value)`. */
function recoverNestedTerminalSingleArrayDestructuring(
	body: t.Statement[],
): TerminalArrayDestructuringCandidate | null {
	for (let i = 1; i <= body.length - 5; i++) {
		const predecl = body[i - 1];
		if (
			!t.isVariableDeclaration(predecl, { kind: 'let' }) ||
			!predecl.declarations.every((declaration) =>
				t.isIdentifier(declaration.id) && declaration.init == null
			)
		) {
			continue;
		}
		const begin = intrinsicArrayDecl(body[i], 'IteratorBegin');
		const next = intrinsicArrayDecl(body[i + 1], 'IteratorNext');
		if (
			!begin || begin.ids.length !== 2 || begin.args.length !== 1 ||
			!next || next.ids.length !== 2 || next.args.length !== 2 ||
			!t.isIdentifier(next.args[0], { name: begin.ids[0].name }) ||
			!t.isIdentifier(next.args[1], { name: begin.ids[1].name })
		) continue;

		const select = body[i + 2];
		const valueName = selectedIteratorValueName(
			select,
			next.ids[0].name,
			next.ids[1].name,
		);
		if (!valueName) continue;
		const retainedDeclarators = predecl.declarations.filter((declaration) =>
			!t.isIdentifier(declaration.id, { name: valueName })
		);
		if (
			retainedDeclarators.length + 1 !== predecl.declarations.length ||
			body.slice(i, i + 4).some((statement) =>
				retainedDeclarators.some((declaration) =>
					countIdentifierUses(
						statement,
						(declaration.id as t.Identifier).name,
					) > 0
				)
			)
		) continue;

		const closeGuard = body[i + 3];
		if (
			!t.isIfStatement(closeGuard) || closeGuard.alternate ||
			!isIteratorNotDoneCheck(closeGuard.test, next.ids[1].name) ||
			!t.isBlockStatement(closeGuard.consequent) ||
			closeGuard.consequent.body.length < 1 ||
			!directIteratorCloseUsesState(
				closeGuard.consequent.body[0],
				next.ids[1].name,
			)
		) continue;
		const finalTail = body.slice(i + 4);
		if (
			!statementListEndsAbruptly(finalTail) ||
			(closeGuard.consequent.body.length > 1 &&
				!terminalStatementsEquivalent(
					closeGuard.consequent.body.slice(1),
					finalTail,
				))
		) continue;
		const protocolNames = new Set([
			...begin.ids.map((identifier) => identifier.name),
			...next.ids.map((identifier) => identifier.name),
		]);
		if (
			finalTail.some((statement) =>
				[...protocolNames].some((name) =>
					countIdentifierUses(statement, name) > 0
				)
			)
		) continue;

		const source = begin.args[0] as t.Expression;
		return {
			start: i - 1,
			end: i + 4,
			pattern: t.arrayPattern([t.identifier(valueName)]),
			source,
			preservedInputs: [source, ...finalTail],
			followingStatements: retainedDeclarators.length > 0
				? [t.variableDeclaration(
					'let',
					retainedDeclarators.map((declaration) =>
						t.cloneNode(declaration, true)
					),
				)]
				: undefined,
		};
	}
	return null;
}

function selectedIteratorValueName(
	statement: t.Statement | undefined,
	valueName: string,
	stateName: string,
): string | null {
	if (
		!t.isIfStatement(statement) ||
		getUndefinedCheckName(statement.test) !== stateName ||
		!t.isBlockStatement(statement.consequent) ||
		!t.isBlockStatement(statement.alternate)
	) return null;

	const empty = identifierAssignments(statement.consequent.body);
	const present = identifierAssignments(statement.alternate.body);
	if (!empty || !present) return null;
	const matches = [...empty].flatMap(([target, emptyValue]) => {
		const presentValue = present.get(target);
		return isUndefinedNode(emptyValue) &&
				!!presentValue &&
				t.isIdentifier(presentValue, { name: valueName })
			? [target]
			: [];
	});
	return matches.length === 1 ? matches[0] : null;
}

function createFunctionEnvironmentName(
	stmt: t.Statement | undefined,
): string | null {
	const environment = singleDeclarator(stmt, 'const');
	if (
		!environment || !t.isIdentifier(environment.id) ||
		!t.isCallExpression(environment.init) ||
		!t.isV8IntrinsicIdentifier(environment.init.callee, {
			name: 'CreateFunctionEnvironment',
		})
	) return null;
	return environment.id.name;
}

function capturedValueEnvironmentStoreStatement(
	stmt: t.Statement | undefined,
	environmentName: string,
	valueName: string,
): t.Statement[] | null {
	const capture = expressionStatementAssignment(stmt);
	if (
		!capture || !t.isMemberExpression(capture.left, { computed: true }) ||
		!t.isCallExpression(capture.left.object) ||
		!t.isV8IntrinsicIdentifier(capture.left.object.callee, {
			name: 'expectEnvironment',
		}) ||
		capture.left.object.arguments.length !== 1 ||
		!t.isIdentifier(capture.left.object.arguments[0], {
			name: environmentName,
		}) ||
		!t.isIdentifier(capture.right, { name: valueName })
	) return null;
	return [t.cloneNode(stmt!, true)];
}

function capturedValueEnvironmentPrelude(
	body: t.Statement[],
	start: number,
	valueName: string,
): t.Statement[] | null {
	const environmentName = createFunctionEnvironmentName(body[start]);
	if (!environmentName) return null;
	const capture = capturedValueEnvironmentStoreStatement(
		body[start + 1],
		environmentName,
		valueName,
	);
	if (!capture) return null;
	return [
		t.cloneNode(body[start], true),
		...capture,
	];
}

interface CarriedIteratorElement {
	end: number;
	targetName?: string;
	doneName: string;
	stateName: string;
	protocolNames: string[];
}

function recoverCarriedIteratorElement(
	body: t.Statement[],
	start: number,
	inputStateName: string,
	iteratorRecordName: string,
	inputDoneName?: string,
): CarriedIteratorElement | null {
	const branch = body[start];
	if (
		!t.isIfStatement(branch) ||
		!t.isBlockStatement(branch.consequent) ||
		!t.isBlockStatement(branch.alternate) ||
		(inputDoneName
			? !t.isIdentifier(branch.test, { name: inputDoneName })
			: getUndefinedCheckName(branch.test) !== inputStateName)
	) return null;

	const empty = identifierAssignments(branch.consequent.body);
	if (!empty || (empty.size !== 2 && empty.size !== 3)) return null;
	const doneName = assignmentNameWithValue(
		empty,
		(value) =>
			inputDoneName
				? t.isIdentifier(value, { name: inputDoneName })
				: getUndefinedCheckName(value) === inputStateName,
	);
	const stateName = assignmentNameWithValue(
		empty,
		(value) => t.isIdentifier(value, { name: inputStateName }),
	);
	const targetName = assignmentNameWithValue(empty, isUndefinedNode) ??
		undefined;
	if (
		!doneName || !stateName ||
		empty.size !== (targetName ? 3 : 2)
	) return null;

	const nonEmpty = branch.alternate.body;
	const next = intrinsicArrayDecl(nonEmpty[0], 'IteratorNext');
	if (
		!next || next.ids.length !== 2 || next.args.length !== 2 ||
		!t.isIdentifier(next.args[0], { name: inputStateName }) ||
		!t.isIdentifier(next.args[1], { name: iteratorRecordName })
	) return null;

	const validAssignments = (
		assignments: ReadonlyMap<string, t.Expression>,
		value?: t.Expression,
	) => assignments.size === (targetName ? 3 : 2) &&
		getUndefinedCheckName(assignments.get(doneName)!) ===
			next.ids[1].name &&
		t.isIdentifier(assignments.get(stateName), {
			name: next.ids[1].name,
		}) &&
		(!targetName ||
			(!!value && !!assignments.get(targetName) &&
				expressionsEqual(assignments.get(targetName)!, value)));

	if (targetName) {
		const nextBranch = nonEmpty[1];
		if (
			nonEmpty.length !== 2 || !t.isIfStatement(nextBranch) ||
			getUndefinedCheckName(nextBranch.test) !== next.ids[1].name ||
			!t.isBlockStatement(nextBranch.consequent) ||
			!t.isBlockStatement(nextBranch.alternate)
		) return null;
		const nextEmpty = identifierAssignments(nextBranch.consequent.body);
		const nextValue = identifierAssignments(nextBranch.alternate.body);
		if (
			!nextEmpty || !nextValue ||
			!validAssignments(nextEmpty, t.identifier('undefined')) ||
			!validAssignments(nextValue, next.ids[0])
		) return null;
	} else {
		const nextAssignments = identifierAssignments(nonEmpty.slice(1));
		if (!nextAssignments || !validAssignments(nextAssignments)) return null;
	}

	return {
		end: start + 1,
		targetName,
		doneName,
		stateName,
		protocolNames: next.ids.map((identifier) => identifier.name),
	};
}

function equivalentIdentifierAssignments(
	body: readonly t.Statement[],
	allowedNames: ReadonlySet<string>,
): Map<string, t.Expression> | null {
	const assignments = new Map<string, t.Expression>();
	for (const statement of body) {
		const assignment = expressionStatementAssignment(statement);
		if (
			!assignment || !t.isIdentifier(assignment.left) ||
			!t.isExpression(assignment.right) ||
			!allowedNames.has(assignment.left.name)
		) return null;
		const previous = assignments.get(assignment.left.name);
		if (previous && !expressionsEqual(previous, assignment.right)) {
			return null;
		}
		assignments.set(assignment.left.name, assignment.right);
	}
	return assignments;
}

/**
 * Recover Region's preinitialised carried-state form for a later array slot:
 * the empty-path values are declared before a one-sided guard, then the guard
 * advances the iterator and overwrites those carriers on the non-empty path.
 */
function recoverInitializedCarriedIteratorElement(
	body: t.Statement[],
	start: number,
	inputStateName: string,
	iteratorRecordName: string,
	inputDoneName?: string,
): CarriedIteratorElement | null {
	let cursor = start;
	const initialValues = new Map<string, t.Expression>();
	const declaredNames = new Set<string>();
	const grouped = body[cursor];
	if (
		t.isVariableDeclaration(grouped, { kind: 'let' }) &&
		(grouped.declarations.length === 2 ||
			grouped.declarations.length === 3) &&
		grouped.declarations.every((declaration) =>
			t.isIdentifier(declaration.id) && declaration.init == null
		)
	) {
		for (const declaration of grouped.declarations) {
			declaredNames.add((declaration.id as t.Identifier).name);
		}
		cursor++;
		while (cursor < body.length) {
			const assignment = expressionStatementAssignment(body[cursor]);
			if (
				!assignment || !t.isIdentifier(assignment.left) ||
				!t.isExpression(assignment.right) ||
				!declaredNames.has(assignment.left.name)
			) break;
			const previous = initialValues.get(assignment.left.name);
			if (previous && !expressionsEqual(previous, assignment.right)) {
				return null;
			}
			initialValues.set(assignment.left.name, assignment.right);
			cursor++;
		}
	} else {
		for (let count = 0; count < 3; count++) {
			const declaration = singleDeclarator(body[cursor], 'let');
			if (
				!declaration || !t.isIdentifier(declaration.id) ||
				!t.isExpression(declaration.init)
			) break;
			declaredNames.add(declaration.id.name);
			initialValues.set(declaration.id.name, declaration.init);
			cursor++;
		}
	}
	if (declaredNames.size < 2 || declaredNames.size > 3) return null;
	const initialTargetName =
		assignmentNameWithValue(initialValues, isUndefinedNode) ??
			undefined;

	const guard = body[cursor];
	const checksInputNotDone = t.isIfStatement(guard) &&
		(inputDoneName
			? t.isUnaryExpression(guard.test, { operator: '!' }) &&
				t.isIdentifier(guard.test.argument, { name: inputDoneName })
			: isIteratorNotDoneCheck(guard.test, inputStateName));
	if (
		!t.isIfStatement(guard) || guard.alternate ||
		!t.isBlockStatement(guard.consequent) ||
		!checksInputNotDone
	) return null;
	const nested = guard.consequent.body;
	const next = intrinsicArrayDecl(nested[0], 'IteratorNext');
	if (
		!next || next.ids.length !== 2 || next.args.length !== 2 ||
		!t.isIdentifier(next.args[0], { name: inputStateName }) ||
		!t.isIdentifier(next.args[1], { name: iteratorRecordName })
	) return null;
	const [valueId, nextStateId] = next.ids;

	let directEnd = nested.length;
	let valueGuard: t.IfStatement | undefined;
	if (initialTargetName && t.isIfStatement(nested.at(-1))) {
		valueGuard = nested.at(-1) as t.IfStatement;
		directEnd--;
	}
	const direct = equivalentIdentifierAssignments(
		nested.slice(1, directEnd),
		declaredNames,
	);
	if (!direct) return null;
	const doneName = assignmentNameWithValue(
		direct,
		(value) => getUndefinedCheckName(value) === nextStateId.name,
	) ?? undefined;
	const stateName = assignmentNameWithValue(
		direct,
		(value) => t.isIdentifier(value, { name: nextStateId.name }),
	) ?? undefined;
	const targetName = initialTargetName ??
		assignmentNameWithValue(direct, isUndefinedNode) ?? undefined;
	if (
		!doneName || !stateName ||
		!declaredNames.has(doneName) || !declaredNames.has(stateName) ||
		(targetName != null && !declaredNames.has(targetName)) ||
		declaredNames.size !== (targetName ? 3 : 2) ||
		getUndefinedCheckName(direct.get(doneName)!) !== nextStateId.name ||
		!t.isIdentifier(direct.get(stateName), { name: nextStateId.name }) ||
		(targetName && !isUndefinedNode(direct.get(targetName)) &&
			!(t.isIdentifier(direct.get(targetName)) &&
				generatedRegisterIndexMatches(
					direct.get(targetName) as t.Identifier,
					targetName,
				)))
	) return null;
	const initialDone = initialValues.get(doneName);
	if (
		initialDone &&
		(inputDoneName
			? !t.isIdentifier(initialDone, { name: inputDoneName })
			: getUndefinedCheckName(initialDone) !== inputStateName)
	) return null;
	const initialState = initialValues.get(stateName);
	if (
		initialState &&
		!t.isIdentifier(initialState, { name: inputStateName })
	) return null;
	if (targetName && !isUndefinedNode(initialValues.get(targetName))) {
		return null;
	}

	if (targetName) {
		if (
			!valueGuard || valueGuard.alternate ||
			!t.isBlockStatement(valueGuard.consequent) ||
			!isIteratorNotDoneCheck(valueGuard.test, nextStateId.name)
		) return null;
		const selected = equivalentIdentifierAssignments(
			valueGuard.consequent.body,
			declaredNames,
		);
		if (
			!selected ||
			!t.isIdentifier(selected.get(targetName), { name: valueId.name }) ||
			(selected.has(doneName) &&
				getUndefinedCheckName(selected.get(doneName)!) !==
					nextStateId.name &&
				!(t.isIdentifier(selected.get(doneName)) &&
					generatedRegisterIndexMatches(
						selected.get(doneName) as t.Identifier,
						doneName,
					))) ||
			(selected.has(stateName) &&
				!t.isIdentifier(selected.get(stateName), {
					name: nextStateId.name,
				}) &&
				!(t.isIdentifier(selected.get(stateName)) &&
					generatedRegisterIndexMatches(
						selected.get(stateName) as t.Identifier,
						stateName,
					)))
		) return null;
	}

	return {
		end: cursor + 1,
		targetName,
		doneName,
		stateName,
		protocolNames: next.ids.map((identifier) => identifier.name),
	};
}

function recoverSelectedFirstIteratorElement(
	body: t.Statement[],
	start: number,
	valueName: string,
	stateName: string,
	globalNames: Set<string>,
): { target: string; end: number } | null {
	const plain = plainArrayElement(
		body,
		start,
		valueName,
		stateName,
		globalNames,
		false,
	);
	if (plain?.target && !plain.declaredGlobal) {
		return { target: plain.target, end: plain.end };
	}

	const declaration = body[start];
	if (
		!t.isVariableDeclaration(declaration, { kind: 'let' }) ||
		declaration.declarations.length !== 1 ||
		!t.isIdentifier(declaration.declarations[0].id) ||
		declaration.declarations[0].init != null
	) return null;
	const target = declaration.declarations[0].id.name;
	const initial = assignmentToIdentifier(body[start + 1], target);
	if (!initial || !isUndefinedNode(initial.right)) return null;
	const guard = body[start + 2];
	if (
		!t.isIfStatement(guard) || guard.alternate ||
		!t.isBlockStatement(guard.consequent) ||
		!isIteratorNotDoneCheck(guard.test, stateName)
	) return null;
	const selected = singleAssignmentInBlock(guard.consequent, target);
	if (!selected || !t.isIdentifier(selected.right, { name: valueName })) {
		return null;
	}
	return { target, end: start + 3 };
}

function capturedValueEnvironmentStore(
	statement: t.Statement | undefined,
	valueName: string,
): t.Identifier | null {
	const assignment = expressionStatementAssignment(statement);
	return assignment &&
			t.isIdentifier(assignment.right, { name: valueName }) &&
			t.isMemberExpression(assignment.left, { computed: true }) &&
			t.isCallExpression(assignment.left.object) &&
			t.isV8IntrinsicIdentifier(assignment.left.object.callee, {
				name: 'expectEnvironment',
			})
		? assignment.right
		: null;
}

function recoverInitializedCarriedArrayDestructuring(
	body: t.Statement[],
): TerminalArrayDestructuringCandidate | null {
	const globalNames = collectGlobalNames(body);
	for (let i = 0; i <= body.length - 7; i++) {
		const begin = intrinsicArrayDecl(body[i], 'IteratorBegin');
		const firstNext = intrinsicArrayDecl(body[i + 1], 'IteratorNext');
		if (
			!begin || begin.ids.length !== 2 || begin.args.length !== 1 ||
			!firstNext || firstNext.ids.length !== 2 ||
			firstNext.args.length !== 2 ||
			!t.isIdentifier(firstNext.args[0], { name: begin.ids[0].name }) ||
			!t.isIdentifier(firstNext.args[1], { name: begin.ids[1].name })
		) continue;
		const first = recoverSelectedFirstIteratorElement(
			body,
			i + 2,
			firstNext.ids[0].name,
			firstNext.ids[1].name,
			globalNames,
		);
		let cursor = first?.end ?? i + 2;
		if (!first && emptyIteratorGuard(body[cursor], firstNext.ids[1].name)) {
			cursor++;
		}
		const followingStatements: t.Statement[] = [];
		let firstBinding = first ? t.identifier(first.target) : null;
		let firstStore: t.Identifier | null;
		while (
			first &&
			(firstStore = capturedValueEnvironmentStore(
					body[cursor],
					first.target,
				)) != null
		) {
			firstBinding = t.cloneNode(firstStore, true);
			followingStatements.push(t.cloneNode(body[cursor], true));
			cursor++;
		}

		const elements: Array<t.Identifier | null> = [
			firstBinding,
		];
		let stateName = firstNext.ids[1].name;
		let doneName: string | undefined;
		const protocolNames = new Set([
			...begin.ids.map((identifier) => identifier.name),
			...firstNext.ids.map((identifier) => identifier.name),
		]);
		for (;;) {
			const element = recoverInitializedCarriedIteratorElement(
				body,
				cursor,
				stateName,
				begin.ids[1].name,
				doneName,
			);
			if (!element) break;
			elements.push(
				element.targetName ? t.identifier(element.targetName) : null,
			);
			stateName = element.stateName;
			doneName = element.doneName;
			for (const name of element.protocolNames) protocolNames.add(name);
			protocolNames.add(element.doneName);
			protocolNames.add(element.stateName);
			cursor = element.end;
			let elementStore: t.Identifier | null;
			while (
				element.targetName &&
				(elementStore = capturedValueEnvironmentStore(
						body[cursor],
						element.targetName,
					)) != null
			) {
				elements[elements.length - 1] = t.cloneNode(
					elementStore,
					true,
				);
				followingStatements.push(t.cloneNode(body[cursor], true));
				cursor++;
			}
		}
		if ((!first && elements.length < 2) || (first && elements.length < 1)) {
			continue;
		}

		const close = body[cursor];
		if (
			!t.isIfStatement(close) || close.alternate ||
			!t.isBlockStatement(close.consequent) ||
			close.consequent.body.length !== 1
		) continue;
		const closeTestMatches = doneName
			? t.isUnaryExpression(close.test, { operator: '!' }) &&
				t.isIdentifier(close.test.argument) &&
				generatedRegisterIndexMatches(close.test.argument, doneName)
			: isIteratorNotDoneCheck(close.test, stateName);
		if (
			!closeTestMatches ||
			!directIteratorCloseResolvesState(
				close.consequent.body[0],
				stateName,
			)
		) continue;

		const finalTail = body.slice(cursor + 1);
		if (
			finalTail.some((statement) =>
				[...protocolNames].some((name) =>
					countIdentifierUses(statement, name) > 0
				)
			)
		) continue;
		for (let index = 0; index < elements.length; index++) {
			const element = elements[index];
			if (!element) continue;
			const preferred = preferredCarriedBindingName(
				finalTail,
				element.name,
			);
			if (preferred !== element.name) {
				elements[index] = t.identifier(preferred);
			}
		}

		const source = begin.args[0] as t.Expression;
		return {
			start: i,
			end: cursor + 1,
			pattern: t.arrayPattern(elements),
			source,
			preservedInputs: [source, ...followingStatements, ...finalTail],
			followingStatements,
		};
	}
	return null;
}

function recoverNestedTerminalThreeSlotArrayDestructuring(
	body: t.Statement[],
): TerminalArrayDestructuringCandidate | null {
	for (let i = 1; i <= body.length - 7; i++) {
		const fail = (reason: string) => {
			debugArrayDestr('terminal-three-slot fail', i, reason);
			return null;
		};
		const predecl = body[i - 1];
		if (
			!t.isVariableDeclaration(predecl, { kind: 'let' }) ||
			!predecl.declarations.every((declaration) =>
				t.isIdentifier(declaration.id) && declaration.init == null
			)
		) continue;
		const begin = intrinsicArrayDecl(body[i], 'IteratorBegin');
		const firstNext = intrinsicArrayDecl(body[i + 1], 'IteratorNext');
		if (
			!begin || begin.ids.length !== 2 || begin.args.length !== 1 ||
			!firstNext || firstNext.ids.length !== 2 ||
			firstNext.args.length !== 2 ||
			!t.isIdentifier(firstNext.args[0], { name: begin.ids[0].name }) ||
			!t.isIdentifier(firstNext.args[1], { name: begin.ids[1].name })
		) {
			fail('prefix');
			continue;
		}
		const firstTarget = selectedIteratorValueName(
			body[i + 2],
			firstNext.ids[0].name,
			firstNext.ids[1].name,
		);
		if (!firstTarget) {
			fail('first target');
			continue;
		}

		const second = recoverCarriedIteratorElement(
			body,
			i + 3,
			firstNext.ids[1].name,
			begin.ids[1].name,
		);
		if (!second) {
			fail('second');
			continue;
		}
		const third = recoverCarriedIteratorElement(
			body,
			second.end,
			second.stateName,
			begin.ids[1].name,
			second.doneName,
		);
		if (!third?.targetName) {
			fail('third');
			continue;
		}

		const closeGuard = body[third.end];
		if (
			!t.isIfStatement(closeGuard) || closeGuard.alternate ||
			!t.isUnaryExpression(closeGuard.test, { operator: '!' }) ||
			!t.isIdentifier(closeGuard.test.argument, {
				name: third.doneName,
			}) ||
			!t.isBlockStatement(closeGuard.consequent) ||
			closeGuard.consequent.body.length !== 1 ||
			!directIteratorCloseUsesState(
				closeGuard.consequent.body[0],
				third.stateName,
			)
		) {
			fail('close');
			continue;
		}

		const declaredNames = new Set(
			predecl.declarations.map((declaration) =>
				(declaration.id as t.Identifier).name
			),
		);
		const expectedNames = [
			firstTarget,
			second.targetName,
			second.doneName,
			second.stateName,
			third.targetName,
			third.doneName,
			third.stateName,
		].filter((name): name is string => !!name);
		if (
			declaredNames.size !== expectedNames.length ||
			!expectedNames.every((name) => declaredNames.has(name))
		) {
			fail('declarations');
			continue;
		}

		const protocolNames = new Set([
			...begin.ids.map((identifier) => identifier.name),
			...firstNext.ids.map((identifier) => identifier.name),
			...second.protocolNames,
			...third.protocolNames,
			second.doneName,
			second.stateName,
			third.doneName,
			third.stateName,
		]);
		const finalTail = body.slice(third.end + 1);
		if (
			finalTail.some((statement) =>
				[...protocolNames].some((name) =>
					countIdentifierUses(statement, name) > 0
				)
			)
		) {
			fail('live protocol');
			continue;
		}

		const source = begin.args[0] as t.Expression;
		return {
			start: i - 1,
			end: third.end + 1,
			pattern: t.arrayPattern([
				t.identifier(firstTarget),
				second.targetName ? t.identifier(second.targetName) : null,
				t.identifier(third.targetName),
			]),
			source,
			preservedInputs: [source, ...finalTail],
		};
	}
	return null;
}

/**
 * Recover the compact Region form used for two-slot array destructuring.
 * A three-value join carries the second value, done flag, and close state out
 * of nested empty/non-empty arms. The first iterator value may either be
 * selected by the preceding branch or deliberately elided.
 */
function recoverNestedTerminalCarriedArrayDestructuring(
	body: t.Statement[],
): TerminalArrayDestructuringCandidate | null {
	for (let i = 1; i <= body.length - 5; i++) {
		const predecl = body[i - 1];
		if (!t.isVariableDeclaration(predecl, { kind: 'let' })) continue;
		if (
			(predecl.declarations.length !== 3 &&
				predecl.declarations.length !== 4) ||
			!predecl.declarations.every((declaration) =>
				t.isIdentifier(declaration.id) && declaration.init == null
			)
		) continue;

		let beginIndex = i;
		const preBeginEnvironmentName = createFunctionEnvironmentName(
			body[beginIndex],
		);
		const preBeginEnvironment = preBeginEnvironmentName
			? [t.cloneNode(body[beginIndex]!, true)]
			: null;
		if (preBeginEnvironmentName) beginIndex++;

		const begin = intrinsicArrayDecl(body[beginIndex], 'IteratorBegin');
		const firstNext = intrinsicArrayDecl(
			body[beginIndex + 1],
			'IteratorNext',
		);
		if (
			!begin || begin.ids.length !== 2 || begin.args.length !== 1 ||
			!firstNext || firstNext.ids.length !== 2 ||
			firstNext.args.length !== 2 ||
			!t.isIdentifier(firstNext.args[0], { name: begin.ids[0].name }) ||
			!t.isIdentifier(firstNext.args[1], { name: begin.ids[1].name })
		) continue;

		let branchIndex = beginIndex + 2;
		const firstValueName = selectedIteratorValueName(
			body[branchIndex],
			firstNext.ids[0].name,
			firstNext.ids[1].name,
		);
		if (firstValueName) branchIndex++;
		let followingStatements: t.Statement[] | undefined;
		if (firstValueName && preBeginEnvironmentName) {
			const capture = capturedValueEnvironmentStoreStatement(
				body[branchIndex],
				preBeginEnvironmentName,
				firstValueName,
			);
			if (capture) {
				followingStatements = [...preBeginEnvironment!, ...capture];
				branchIndex += capture.length;
			}
		} else if (firstValueName) {
			const environmentPrelude = capturedValueEnvironmentPrelude(
				body,
				branchIndex,
				firstValueName,
			);
			if (environmentPrelude) {
				followingStatements = environmentPrelude;
				branchIndex += environmentPrelude.length;
			}
		}

		const branch = body[branchIndex];
		if (
			!t.isIfStatement(branch) ||
			getUndefinedCheckName(branch.test) !== firstNext.ids[1].name ||
			!t.isBlockStatement(branch.consequent) ||
			!t.isBlockStatement(branch.alternate)
		) continue;
		const emptyAssignments = identifierAssignments(branch.consequent.body);
		if (!emptyAssignments || emptyAssignments.size !== 3) continue;
		const doneName = assignmentNameWithValue(
			emptyAssignments,
			(value) => getUndefinedCheckName(value) === firstNext.ids[1].name,
		);
		const stateName = assignmentNameWithValue(
			emptyAssignments,
			(value) => t.isIdentifier(value, { name: firstNext.ids[1].name }),
		);
		const valueName = assignmentNameWithValue(
			emptyAssignments,
			isUndefinedNode,
		);
		if (!doneName || !stateName || !valueName) continue;
		const declaredNames = new Set(
			predecl.declarations.map((declaration) =>
				(declaration.id as t.Identifier).name
			),
		);
		if (
			declaredNames.size !== (firstValueName ? 4 : 3) ||
			![doneName, stateName, valueName, firstValueName]
				.filter((name): name is string => !!name)
				.every((name) => declaredNames.has(name))
		) continue;

		const nonEmpty = branch.alternate.body;
		const secondNext = intrinsicArrayDecl(nonEmpty[0], 'IteratorNext');
		const secondBranch = nonEmpty[1];
		if (
			nonEmpty.length !== 2 || !secondNext ||
			secondNext.ids.length !== 2 || secondNext.args.length !== 2 ||
			!t.isIdentifier(secondNext.args[0], {
				name: firstNext.ids[1].name,
			}) ||
			!t.isIdentifier(secondNext.args[1], { name: begin.ids[1].name }) ||
			!t.isIfStatement(secondBranch) ||
			getUndefinedCheckName(secondBranch.test) !==
				secondNext.ids[1].name ||
			!t.isBlockStatement(secondBranch.consequent) ||
			!t.isBlockStatement(secondBranch.alternate)
		) continue;
		const secondEmpty = identifierAssignments(secondBranch.consequent.body);
		const secondValue = identifierAssignments(secondBranch.alternate.body);
		if (!secondEmpty || !secondValue) continue;
		const validArm = (
			assignments: ReadonlyMap<string, t.Expression>,
			value: t.Expression,
		) => assignments.size === 3 &&
			getUndefinedCheckName(assignments.get(doneName)!) ===
				secondNext.ids[1].name &&
			t.isIdentifier(assignments.get(stateName), {
				name: secondNext.ids[1].name,
			}) &&
			!!assignments.get(valueName) &&
			expressionsEqual(assignments.get(valueName)!, value);
		if (
			!validArm(secondEmpty, t.identifier('undefined')) ||
			!validArm(secondValue, secondNext.ids[0])
		) continue;

		const closeIndex = branchIndex + 1;
		const closeGuard = body[closeIndex];
		if (
			!t.isIfStatement(closeGuard) || closeGuard.alternate ||
			!t.isUnaryExpression(closeGuard.test, { operator: '!' }) ||
			!t.isIdentifier(closeGuard.test.argument, { name: doneName }) ||
			!t.isBlockStatement(closeGuard.consequent) ||
			closeGuard.consequent.body.length < 1 ||
			!directIteratorCloseUsesState(
				closeGuard.consequent.body[0],
				stateName,
			)
		) continue;
		const finalTail = body.slice(closeIndex + 1);
		const closeTail = closeGuard.consequent.body.slice(1);
		if (
			closeTail.length > 0 &&
			(!statementListEndsAbruptly(finalTail) ||
				!terminalStatementsEquivalent(closeTail, finalTail))
		) continue;
		const protocolNames = new Set([
			doneName,
			stateName,
			...begin.ids.map((identifier) => identifier.name),
			...firstNext.ids.map((identifier) => identifier.name),
			...secondNext.ids.map((identifier) => identifier.name),
		]);
		if (
			finalTail.some((statement) =>
				[...protocolNames].some((name) =>
					countIdentifierUses(statement, name) > 0
				)
			)
		) continue;

		const source = begin.args[0] as t.Expression;
		return {
			start: i - 1,
			end: closeIndex + 1,
			pattern: t.arrayPattern([
				firstValueName ? t.identifier(firstValueName) : null,
				t.identifier(valueName),
			]),
			source,
			preservedInputs: [source, ...finalTail, ...closeTail],
			followingStatements,
		};
	}
	return null;
}

function normalizeDuplicatedTerminalCarriedArrayTail(
	body: t.Statement[],
): boolean {
	for (let index = 0; index < body.length; index++) {
		const branch = body[index];
		if (
			!t.isIfStatement(branch) ||
			!t.isBlockStatement(branch.consequent) ||
			!t.isBlockStatement(branch.alternate)
		) continue;
		const inputStateName = getUndefinedCheckName(branch.test);
		if (!inputStateName) continue;

		const empty = branch.consequent.body;
		const nonEmpty = branch.alternate.body;
		const emptyCloseIndex = empty.findIndex(statementContainsIteratorClose);
		const nonEmptyCloseIndex = nonEmpty.findIndex(
			statementContainsIteratorClose,
		);
		debugArrayDestr(
			'duplicated terminal carried tail',
			index,
			inputStateName,
			emptyCloseIndex,
			nonEmptyCloseIndex,
		);
		if (emptyCloseIndex !== 0 || nonEmptyCloseIndex <= 0) continue;
		const next = intrinsicArrayDecl(nonEmpty[0], 'IteratorNext');
		if (
			!next || next.ids.length !== 2 || next.args.length !== 2 ||
			!t.isIdentifier(next.args[0], { name: inputStateName })
		) continue;
		const emptyTail = empty.slice(emptyCloseIndex + 1);
		const nonEmptyTail = nonEmpty.slice(nonEmptyCloseIndex + 1);
		if (
			emptyTail.length === 0 ||
			JSON.stringify(comparableAst(emptyTail)) !==
				JSON.stringify(comparableAst(nonEmptyTail))
		) continue;

		body.splice(
			index,
			1,
			t.ifStatement(
				invertTest(t.cloneNode(branch.test, true)),
				t.blockStatement(
					nonEmpty.slice(0, nonEmptyCloseIndex).map((statement) =>
						t.cloneNode(statement, true)
					),
				),
			),
			t.cloneNode(nonEmpty[nonEmptyCloseIndex], true),
			...emptyTail.map((statement) => t.cloneNode(statement, true)),
		);
		return true;
	}
	return false;
}

function cleanupNestedTerminalArrayDestructuring(
	body: t.Statement[],
): boolean {
	const normalizedTerminalTail = normalizeDuplicatedTerminalCarriedArrayTail(
		body,
	);
	const candidate = recoverInitializedCarriedArrayDestructuring(body) ??
		recoverNestedTerminalSingleArrayDestructuring(body) ??
		recoverNestedTerminalCarriedArrayDestructuring(body) ??
		recoverNestedTerminalThreeSlotArrayDestructuring(body);
	if (!candidate) return normalizedTerminalTail;
	const consumed = body.slice(candidate.start, candidate.end);
	body.splice(
		candidate.start,
		candidate.end - candidate.start,
		emitDestructuringPlan({
			pattern: candidate.pattern,
			source: candidate.source,
			declaredGlobals: new Set(),
			consumed,
			preservedInputs: candidate.preservedInputs,
			inlineConsumedResults: [candidate.source],
		}),
		...(candidate.followingStatements ?? []),
	);
	return true;
}

function cleanupTerminalTwoSlotArrayDestructuring(
	func: IRFunction,
	block: IRBlock,
	body: t.Statement[],
	globalNames: Set<string>,
): boolean {
	for (let i = 0; i <= body.length - 9; i++) {
		const fail = (reason: string) => {
			debugArrayDestr('terminal-two-slot fail', i, reason);
			return false;
		};
		const begin = intrinsicArrayDecl(body[i], 'IteratorBegin');
		if (!begin || begin.ids.length !== 2 || begin.args.length !== 1) {
			continue;
		}
		const firstNext = intrinsicArrayDecl(body[i + 1], 'IteratorNext');
		if (
			!firstNext ||
			firstNext.ids.length !== 2 ||
			firstNext.args.length !== 2 ||
			!t.isIdentifier(firstNext.args[0], { name: begin.ids[0].name }) ||
			!t.isIdentifier(firstNext.args[1], { name: begin.ids[1].name })
		) continue;

		const first = plainArrayElement(
			body,
			i + 2,
			firstNext.ids[0].name,
			firstNext.ids[1].name,
			globalNames,
		);
		const firstEnd = first ? first.end : i + 2;
		if (first?.declaredGlobal) {
			fail('first declared global');
			continue;
		}

		const emptyReturn = terminalIteratorEmptyGuardReturn(
			body[firstEnd],
			firstNext.ids[1].name,
		);
		const emptyTail = terminalIteratorEmptyGuardStatements(
			body[firstEnd],
			firstNext.ids[1].name,
		);
		if (!emptyReturn && !emptyTail) {
			fail('empty tail');
			continue;
		}

		const second = immediateNextThenPredeclaredPlainArrayElement(
			body,
			firstEnd + 1,
			firstNext.ids[1].name,
			begin.ids[1].name,
		);
		if (!second) {
			fail('second');
			continue;
		}

		const doneReturn = terminalDoneGuardReturn(
			body[second.end],
			second.doneName,
		);
		const doneTail = terminalDoneGuardStatements(
			body[second.end],
			second.doneName,
		);
		const hasExplicitDoneTail = !!doneReturn || !!doneTail;
		const end = consumeIteratorCloseStatePhi(
			body,
			second.end + (hasExplicitDoneTail ? 1 : 0),
			second.iteratorStateName,
		);
		if (
			end == null ||
			end === second.end + (hasExplicitDoneTail ? 1 : 0)
		) {
			fail('close');
			continue;
		}
		const finalReturn = t.isReturnStatement(body[end]) ? body[end] : null;
		const finalTail = finalTerminalStatements(body, end);
		if (!finalTail) {
			fail('final tail');
			continue;
		}
		if (
			hasExplicitDoneTail &&
			(doneTail
				? !terminalStatementsEquivalent(doneTail, finalTail)
				: !finalReturn || !doneReturn ||
					!returnsEquivalent(doneReturn, finalReturn))
		) {
			fail('done equiv');
			continue;
		}
		if (
			emptyTail
				? !terminalStatementsEquivalentAfterReplacing(
					emptyTail,
					finalTail,
					second.target,
					t.identifier('undefined'),
				)
				: !finalReturn || !emptyReturn ||
					!returnEquivalentAfterReplacing(
						emptyReturn,
						finalReturn,
						second.target,
						t.identifier('undefined'),
					)
		) {
			fail('empty equiv');
			continue;
		}

		const source = begin.args[0] as t.Expression;
		const pattern = t.arrayPattern([
			first?.target ? t.identifier(first.target) : null,
			t.identifier(second.target),
		]);
		const consumed = body.slice(i, end);
		const preservedInputs: t.Node[] = [
			source,
			t.identifier('undefined'),
			t.identifier('global'),
			...finalTail,
			...(doneTail ?? []),
			...(emptyTail ?? []),
		];
		const inlineConsumedResults: t.Node[] = [source];
		if (first?.target && isGeneratedName(first.target)) {
			inlineConsumedResults.push(t.identifier(first.target));
		}
		if (isGeneratedName(second.target)) {
			inlineConsumedResults.push(t.identifier(second.target));
		}
		const escapedNames = new Set(
			[
				first?.target,
				second.target,
			].filter((name): name is string => !!name),
		);
		for (
			const name of collectGeneratedDefinitionsInStatements(finalTail)
		) {
			escapedNames.add(name);
		}
		if (
			!consumedDefinitionsAreDead(
				func,
				block,
				consumed,
				preservedInputs,
				inlineConsumedResults,
				escapedNames,
				false,
				body,
			)
		) {
			fail('live consumed');
			continue;
		}

		body.splice(
			i,
			end - i,
			emitDestructuringPlan({
				pattern,
				source,
				declaredGlobals: new Set(),
				consumed,
				preservedInputs,
				inlineConsumedResults,
			}),
		);
		return true;
	}

	return false;
}

export function cleanupSequentialArrayDestructuring(
	func: IRFunction,
	block: IRBlock,
	body: t.Statement[],
): boolean {
	const globalNames = collectGlobalNames(body);
	if (cleanupNestedTerminalArrayDestructuring(body)) return true;
	if (cleanupProtectedTwoDefaultArrayDestructuring(func, block, body)) {
		return true;
	}
	if (
		cleanupPhiCarriedTwoDefaultArrayDestructuring(
			func,
			block,
			body,
			globalNames,
		)
	) return true;
	if (
		cleanupTerminalTwoSlotArrayDestructuring(
			func,
			block,
			body,
			globalNames,
		)
	) return true;

	for (let i = 0; i <= body.length - 8; i++) {
		const begin = intrinsicArrayDecl(body[i], 'IteratorBegin');
		if (!begin || begin.ids.length !== 2 || begin.args.length !== 1) {
			continue;
		}
		const firstNext = intrinsicArrayDecl(body[i + 1], 'IteratorNext');
		if (
			!firstNext ||
			firstNext.ids.length !== 2 ||
			firstNext.args.length !== 2 ||
			!t.isIdentifier(firstNext.args[0], { name: begin.ids[0].name }) ||
			!t.isIdentifier(firstNext.args[1], { name: begin.ids[1].name })
		) continue;
		const first = plainArrayElement(
			body,
			i + 2,
			firstNext.ids[0].name,
			firstNext.ids[1].name,
			globalNames,
		);
		if (!first || !first.target || first.declaredGlobal) continue;

		let secondStart = first.end;
		while (
			secondStart < body.length &&
			!nextDoneThenPredeclaredPlainArrayElement(
				body,
				secondStart,
				firstNext.ids[1].name,
				begin.ids[1].name,
			)
		) {
			if (statementContainsIteratorClose(body[secondStart])) break;
			secondStart++;
		}
		if (secondStart === first.end || secondStart >= body.length) continue;
		const second = nextDoneThenPredeclaredPlainArrayElement(
			body,
			secondStart,
			firstNext.ids[1].name,
			begin.ids[1].name,
		);
		if (!second || !second.target || second.declaredGlobal) continue;
		const end = consumeIteratorCloseStatePhi(
			body,
			second.end,
			second.iteratorStateName,
		);
		if (end == null || end === second.end) continue;

		const source = begin.args[0] as t.Expression;
		const pattern = t.arrayPattern([
			t.identifier(first.target),
			t.identifier(second.target),
		]);
		const setup = body.slice(first.end, secondStart);
		const consumed = [
			...body.slice(i, first.end),
			...body.slice(secondStart, end),
		];
		const preservedInputs: t.Node[] = [
			source,
			t.identifier('undefined'),
			t.identifier('global'),
		];
		const inlineConsumedResults: t.Node[] = [source];
		const escapedNames = new Set([first.target, second.target]);
		if (
			!consumedDefinitionsAreDead(
				func,
				block,
				consumed,
				preservedInputs,
				inlineConsumedResults,
				escapedNames,
				false,
				body,
			)
		) continue;

		body.splice(
			i,
			end - i,
			emitDestructuringPlan({
				pattern,
				source,
				declaredGlobals: new Set(),
				consumed,
				preservedInputs,
				inlineConsumedResults,
			}),
			...setup,
		);
		return true;
	}

	for (let i = 0; i <= body.length - 4; i++) {
		const match = matchSequentialArrayDestructuring(
			body,
			i,
			globalNames,
		);
		if (!match) continue;
		const begin = intrinsicArrayDecl(body[i], 'IteratorBegin');
		if (!begin || begin.ids.length !== 2 || begin.args.length !== 1) {
			continue;
		}

		const source = begin.args[0] as t.Expression;
		const preservedInputs: t.Node[] = [
			source,
			t.identifier('undefined'),
			t.identifier('global'),
		];
		const inlineConsumedResults: t.Node[] = [source];
		if (t.isArrayPattern(match.pattern)) {
			for (const element of match.pattern.elements) {
				if (t.isIdentifier(element) && isGeneratedName(element.name)) {
					inlineConsumedResults.push(element);
				}
			}
		}
		collectPatternPreservedNodes(match.pattern, preservedInputs);
		const escapedNames = new Set<string>();
		collectPatternBindingNames(match.pattern, escapedNames);

		const consumed = body.slice(i, match.end);
		const restoreSuppressedDoneContinuation =
			suppressDuplicatedDoneContinuationForCheck(consumed);
		const consumedDead = consumedDefinitionsAreDead(
			func,
			block,
			consumed,
			preservedInputs,
			inlineConsumedResults,
			escapedNames,
			false,
			body,
		);
		restoreSuppressedDoneContinuation?.();
		if (!consumedDead) continue;

		body.splice(
			i,
			match.end - i,
			emitDestructuringPlan({
				pattern: match.pattern,
				source,
				declaredGlobals: match.declaredGlobals,
				consumed,
				preservedInputs,
				inlineConsumedResults,
			}),
		);
		removeDeclaredGlobals(
			body,
			match.declaredGlobals,
		);
		return true;
	}

	for (const stmt of body) {
		if (cleanupSequentialArrayDestructuringInStatement(func, block, stmt)) {
			return true;
		}
	}

	return false;
}

function cleanupSequentialArrayDestructuringInStatement(
	func: IRFunction,
	block: IRBlock,
	stmt: t.Statement,
): boolean {
	if (t.isBlockStatement(stmt)) {
		return cleanupSequentialArrayDestructuring(func, block, stmt.body);
	}
	if (t.isTryStatement(stmt)) {
		if (cleanupSequentialArrayDestructuring(func, block, stmt.block.body)) {
			return true;
		}
		if (
			stmt.handler &&
			cleanupSequentialArrayDestructuring(
				func,
				block,
				stmt.handler.body.body,
			)
		) return true;
		return !!stmt.finalizer &&
			cleanupSequentialArrayDestructuring(
				func,
				block,
				stmt.finalizer.body,
			);
	}
	if (t.isIfStatement(stmt)) {
		if (
			t.isBlockStatement(stmt.consequent) &&
			cleanupSequentialArrayDestructuring(
				func,
				block,
				stmt.consequent.body,
			)
		) return true;
		return !!stmt.alternate &&
			t.isBlockStatement(stmt.alternate) &&
			cleanupSequentialArrayDestructuring(
				func,
				block,
				stmt.alternate.body,
			);
	}
	if (t.isWhileStatement(stmt) && t.isBlockStatement(stmt.body)) {
		return cleanupSequentialArrayDestructuring(
			func,
			block,
			stmt.body.body,
		);
	}
	if (
		(t.isForStatement(stmt) ||
			t.isForInStatement(stmt) ||
			t.isForOfStatement(stmt)) &&
		t.isBlockStatement(stmt.body)
	) {
		return cleanupSequentialArrayDestructuring(
			func,
			block,
			stmt.body.body,
		);
	}
	return false;
}
