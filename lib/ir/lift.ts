import { reportProgress } from '../utils/progress.ts';
import { env } from 'node:process';
import { assert } from 'node:console';
import * as t from '@babel/types';
import { copyFunctionForSSA, SSAFunction, type SSARegister } from '../ssa.ts';
import {
	buildBytecodeDerivedPlan,
	type BytecodeDerivedPlan,
	type EnvironmentCreationSite,
	environmentCreationSiteKey,
	type EnvironmentSiteId,
	environmentSiteKey,
	readColdPlan,
} from '../coldstore/plan.ts';
import type { IRFunctionStore } from './function/store.ts';
import {
	type ColdSession,
	type ColdSessionOptions,
	markSnapshotsComplete,
	openColdSession,
} from '../coldstore/session.ts';
import { readColdFile } from '../coldstore/file.ts';
import type { ColdStore } from '../coldstore/mod.ts';
import {
	clearLiftFailures,
	deleteColdSnapshot,
	hasColdSnapshot,
	readColdRecursiveSummaries,
	readColdSnapshotHead,
	readLiftFailures,
	recordLiftFailures,
} from '../coldstore/snapshot.ts';
import { ColdIRFunctionStore } from '../coldstore/store.ts';
import generate from '@babel/generator';
import traverse, { type Binding, NodePath, Scope } from '@babel/traverse';
import { HBCFile } from '../parser/file.ts';
import type {
	ParallelComposeUnit,
	ParallelWorkerMessage,
	ParallelWorkerRequest,
} from './parallel_worker.ts';
import { LiftedExtra } from './ast/mod.ts';
import {
	coalesceStableStorageAliases,
	destructureGeneratedObjectPropertyAliases,
	locationOf,
	tagStorageLocation,
} from './ast/alias.ts';
import { placeEnvironmentSlotsInTree } from './ast/environmentPlacement.ts';
import {
	comparableAst,
	extractFunctionRef,
	isReadOnlyEnvironmentLookup,
	isUndefinedNode,
} from './ast/utils.ts';
import {
	foldConditionalValuesInBody,
	refoldConditionalValues,
} from './ast/phi.ts';
import { LiftError } from './error.ts';
import {
	IRFunction,
	type IRFunctionOptions,
	IRFunctionSnapshot,
	type RecursiveCFGSummary,
} from './function/mod.ts';
import type { CFGReducerOptions } from './function/cfg/options.ts';
import {
	destructuringSourceDefault,
	destructuringUndefinedAliases,
	identifierOccurrences,
} from './function/cfg/destructuringPlan.ts';
import { registerName } from './function/cfg/phi.ts';
import { cleanupComposedObjectRestInBody } from './function/cfg/destructuring.ts';
import { adoptRecoveredFunctionParameters } from './function/cfg/parameterPlan.ts';
import { isDuplicableScalarExpression } from './function/utils.ts';
import { FunctionId } from '../hbc/disassembly/instruction.ts';
import { cleanupEnvironmentBody } from './ast/module/environment.ts';
import {
	buildEnvironmentGraph,
	capturedEnvironment,
	type ElidedWrapperEnvironmentCapture,
	Environment,
	isEnvironmentSlotName,
} from './environment.ts';
import {
	cleanupClassDefinitionClosure,
	cleanupClassSuper,
	liftHermesES6Class,
} from './ast/module/class/transpiled.ts';
import {
	assignmentUpdateExpression,
	inlineBranchArrayConstructionsToFixpoint,
	inlineObjectConstructionsToFixpoint,
	inlineSequenceArrayConstruction,
	inlineSequenceMemberCalls,
	liftHermesApplyCalls,
	liftHermesConcatCalls,
	liftHermesTaggedTemplateCalls,
	lowerResidualArraySpreadCalls,
	postfixUpdateFromToNumericTemp,
	toCompoundAssignment,
} from './ast/expression.ts';
import { unhoistDeclaredGlobals } from './ast/module/binding.ts';
import {
	createIncrementalMetroExtractor,
	extractMetroModules,
	extractMetroModulesParallel,
	type IncrementalMetroExtractor,
	type MetroDefineStatement,
	type MetroModuleExtractionOptions,
} from './ast/module/metro.ts';
import { cleanupGuardedNaturalLoops } from './ast/loop.ts';
import {
	analyseLoweredGeneratorClosure,
	applyLoweredGeneratorWrapperSlotAliases,
	recordLoweredGeneratorWrapperSlotAliases,
} from './function/loweredGenerator/mod.ts';
import { cleanupLocalPNameForInLoops } from './function/cfg/iterator.ts';
import { inlineAdjacentClassMethods } from './ast/module/class/native.ts';
import {
	isRegisterTempName,
	preserveDuplicateRegisterScopesInBody,
} from './ast/registerScope.ts';
import {
	statementAlwaysTerminates,
	statementListMatchesFinalizerPrefix,
	stripStatementSuffix,
} from './function/finalizer.ts';

let DEBUG_DUP_SSA = false;
try {
	DEBUG_DUP_SSA = env['ARES_DEBUG_DUP_SSA'] === '1';
} catch {
	DEBUG_DUP_SSA = false;
}

function debugDupSSA(...args: unknown[]) {
	if (DEBUG_DUP_SSA) console.error('[dup-ssa]', ...args);
}

function identifiersInPattern(pattern: t.Node): t.Identifier[] {
	if (t.isIdentifier(pattern)) return [pattern];
	if (t.isRestElement(pattern)) return identifiersInPattern(pattern.argument);
	if (t.isAssignmentPattern(pattern)) {
		return identifiersInPattern(pattern.left);
	}
	if (t.isArrayPattern(pattern)) {
		return pattern.elements.flatMap((element) =>
			element ? identifiersInPattern(element) : []
		);
	}
	if (t.isObjectPattern(pattern)) {
		return pattern.properties.flatMap((property) => {
			if (t.isRestElement(property)) {
				return identifiersInPattern(property.argument);
			}
			return identifiersInPattern(property.value as t.LVal);
		});
	}
	if (t.isMemberExpression(pattern)) return [];
	return [];
}

function isEnvironmentCreationStatement(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	return t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee) &&
		(
			expr.callee.name === 'CreateFunctionEnvironment' ||
			expr.callee.name === 'CreateTopLevelEnvironment'
		);
}

function normalizeDuplicateRegisterDeclarationsInBody(
	...args: Parameters<
		typeof normalizeDuplicateRegisterDeclarationsInBodyInner
	>
): ReturnType<typeof normalizeDuplicateRegisterDeclarationsInBodyInner> {
	return normalizeDuplicateRegisterDeclarationsInBodyInner(...args);
}

function normalizeDuplicateRegisterDeclarationsInBodyInner(
	body: t.Statement[],
	context = 'body',
	predeclaredNames: Iterable<string> = [],
) {
	preserveDuplicateRegisterScopesInBody(body, {
		context,
		onPreserve(event) {
			debugDupSSA('preserve lifted duplicate register scope', event);
		},
	});
	const declarations = new Map<string, t.VariableDeclaration | null>(
		[...predeclaredNames].map((name) => [name, null]),
	);
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (t.isSwitchStatement(stmt)) {
			const hoisted = normalizeDuplicateSwitchRegisterDeclarations(
				stmt,
				`${context}.switch@${i}`,
			);
			if (hoisted.length > 0) {
				body.splice(i, 0, ...hoisted);
				i += hoisted.length;
			}
			for (const switchCase of stmt.cases) {
				normalizeDuplicateRegisterDeclarationsInBody(
					switchCase.consequent,
					`${context}.switch@${i}.case:${
						switchCase.test?.type ?? 'default'
					}`,
				);
			}
		}
		if (!t.isVariableDeclaration(stmt)) continue;
		if (stmt.declarations.length !== 1) {
			const names = new Set(declarations.keys());
			let conflicts = false;
			for (const declarator of stmt.declarations) {
				for (const id of identifiersInPattern(declarator.id)) {
					if (!isRegisterTempName(id.name)) continue;
					if (names.has(id.name)) conflicts = true;
					names.add(id.name);
				}
			}
			if (!conflicts) continue;
			body.splice(
				i,
				1,
				...stmt.declarations.map((declarator) =>
					t.variableDeclaration(stmt.kind, [
						t.cloneNode(declarator, true),
					])
				),
			);
			i--;
			continue;
		}
		const decl = stmt.declarations[0];
		if (
			t.isVariableDeclarator(decl) &&
			t.isPatternLike(decl.id) &&
			decl.init &&
			t.isExpression(decl.init)
		) {
			const ids = identifiersInPattern(decl.id).filter((id) =>
				isRegisterTempName(id.name)
			);
			const duplicates = ids.filter((id) => declarations.has(id.name));
			if (duplicates.length > 0) {
				for (const id of duplicates) {
					const previous = declarations.get(id.name);
					if (previous?.kind === 'const') previous.kind = 'let';
				}
				const newIds = ids.filter((id) => !declarations.has(id.name));
				if (newIds.length > 0) {
					const hoisted = t.variableDeclaration(
						'let',
						newIds.map((id) =>
							t.variableDeclarator(t.cloneNode(id))
						),
					);
					body.splice(i, 0, hoisted);
					for (const id of newIds) {
						declarations.set(id.name, hoisted);
					}
					i++;
				}
				body[i] = t.expressionStatement(t.assignmentExpression(
					'=',
					t.cloneNode(decl.id) as t.LVal,
					t.cloneNode(decl.init, true),
				));
				continue;
			}
			for (const id of ids) {
				if (!declarations.has(id.name)) {
					declarations.set(id.name, stmt);
				}
			}
			continue;
		}
		if (
			!t.isVariableDeclarator(decl) ||
			!t.isIdentifier(decl.id) ||
			!isRegisterTempName(decl.id.name)
		) continue;
		if (!declarations.has(decl.id.name)) {
			declarations.set(decl.id.name, stmt);
			continue;
		}
		const previous = declarations.get(decl.id.name);
		debugDupSSA('rewrite lifted duplicate register', {
			context,
			name: decl.id.name,
			index: i,
			previousKind: previous?.kind ?? 'parameter',
			currentKind: stmt.kind,
			previousInit: previous?.declarations[0]?.init?.type ?? null,
			currentInit: decl.init?.type ?? null,
		});
		if (previous?.kind === 'const') previous.kind = 'let';
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
	}
}

function normalizeDuplicateSwitchRegisterDeclarations(
	stmt: t.SwitchStatement,
	context = 'switch',
) {
	const counts = new Map<string, number>();
	for (const switchCase of stmt.cases) {
		for (const consequent of switchCase.consequent) {
			if (
				!t.isVariableDeclaration(consequent) ||
				consequent.declarations.length !== 1
			) continue;
			const decl = consequent.declarations[0];
			if (
				!t.isVariableDeclarator(decl) ||
				!t.isIdentifier(decl.id) ||
				!isRegisterTempName(decl.id.name)
			) continue;
			counts.set(decl.id.name, (counts.get(decl.id.name) ?? 0) + 1);
		}
	}
	const duplicateNames = new Set(
		[...counts].filter(([, count]) => count > 1).map(([name]) => name),
	);
	if (duplicateNames.size === 0) return [];
	debugDupSSA('rewrite lifted switch duplicate registers', {
		context,
		names: [...duplicateNames].toSorted(),
		cases: stmt.cases.length,
	});

	for (const switchCase of stmt.cases) {
		for (let i = 0; i < switchCase.consequent.length; i++) {
			const consequent = switchCase.consequent[i];
			if (
				!t.isVariableDeclaration(consequent) ||
				consequent.declarations.length !== 1
			) continue;
			const decl = consequent.declarations[0];
			if (
				!t.isVariableDeclarator(decl) ||
				!t.isIdentifier(decl.id) ||
				!duplicateNames.has(decl.id.name)
			) continue;
			if (decl.init && t.isExpression(decl.init)) {
				switchCase.consequent[i] = t.expressionStatement(
					t.assignmentExpression(
						'=',
						t.cloneNode(decl.id),
						t.cloneNode(decl.init, true),
					),
				);
			} else {
				switchCase.consequent.splice(i, 1);
				i--;
			}
		}
	}

	return [...duplicateNames].toSorted().map((name) =>
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier(name)),
		])
	);
}

export function normalizeDuplicateRegisterDeclarations(
	node: t.Node,
	context = node.type,
) {
	return normalizeDuplicateRegisterDeclarationsInner(node, context);
}

function normalizeDuplicateRegisterDeclarationsInner(
	node: t.Node,
	context = node.type,
) {
	if (t.isProgram(node) || t.isBlockStatement(node)) {
		normalizeDuplicateRegisterDeclarationsInBody(node.body, context);
	}
	if (
		(t.isFunctionDeclaration(node) || t.isFunctionExpression(node) ||
			t.isArrowFunctionExpression(node) || t.isObjectMethod(node) ||
			t.isClassMethod(node)) &&
		t.isBlockStatement(node.body)
	) {
		normalizeDuplicateRegisterDeclarationsInBody(
			node.body.body,
			`${context}.${node.type}.body`,
			node.params.flatMap((param) =>
				identifiersInPattern(param).map((id) => id.name)
			).filter(isRegisterTempName),
		);
	}
	t.traverseFast(node, (child) => {
		if (
			(t.isFunctionDeclaration(child) ||
				t.isFunctionExpression(child) ||
				t.isArrowFunctionExpression(child) ||
				t.isObjectMethod(child) ||
				t.isClassMethod(child)) &&
			t.isBlockStatement(child.body)
		) {
			normalizeDuplicateRegisterDeclarationsInBody(
				child.body.body,
				`${context}.traverseFast.${child.type}.body`,
				child.params.flatMap((param) =>
					identifiersInPattern(param).map((id) => id.name)
				).filter(isRegisterTempName),
			);
		} else if (t.isProgram(child) || t.isBlockStatement(child)) {
			normalizeDuplicateRegisterDeclarationsInBody(
				child.body,
				`${context}.traverseFast.${child.type}`,
			);
		}
	});
	traverse.cache.clear();
}

function rewriteYieldExpressionsToAwait(node: t.Node): void {
	const root = node;
	t.traverseFast(node, (child) => {
		if (
			child !== root &&
			(t.isFunctionDeclaration(child) || t.isFunctionExpression(child) ||
				t.isArrowFunctionExpression(child) || t.isObjectMethod(child) ||
				t.isClassMethod(child))
		) {
			return t.traverseFast.skip;
		}
		if (!t.isYieldExpression(child)) return;

		const replacement = t.awaitExpression(
			child.argument ?? t.identifier('undefined'),
		);
		for (const key of Object.keys(child)) {
			delete (child as unknown as Record<string, unknown>)[key];
		}
		Object.assign(child, replacement);
		return t.traverseFast.skip;
	});
}

function awaitAsyncIteratorArgument(
	expr: t.Expression,
): t.Expression | undefined {
	if (!t.isCallExpression(expr)) return;
	if (
		!t.matchesPattern(expr.callee, [
			'HermesInternal',
			'awaitAsyncIterator',
		])
	) return;
	if (expr.arguments.length !== 1) return t.cloneNode(expr, true);
	const [argument] = expr.arguments;
	if (!t.isExpression(argument)) return t.cloneNode(expr, true);
	return t.cloneNode(argument, true);
}

function rewriteAwaitAsyncIteratorYieldsToAwait(node: t.Node): void {
	const root = node;
	t.traverseFast(node, (child) => {
		if (
			child !== root &&
			(t.isFunctionDeclaration(child) || t.isFunctionExpression(child) ||
				t.isArrowFunctionExpression(child) || t.isObjectMethod(child) ||
				t.isClassMethod(child))
		) {
			return t.traverseFast.skip;
		}
		if (!t.isYieldExpression(child, { delegate: false })) return;
		if (!child.argument || !t.isExpression(child.argument)) return;

		const awaited = awaitAsyncIteratorArgument(child.argument);
		if (!awaited) return;

		const replacement = t.awaitExpression(awaited);
		for (const key of Object.keys(child)) {
			delete (child as unknown as Record<string, unknown>)[key];
		}
		Object.assign(child, replacement);
		return t.traverseFast.skip;
	});
}

function referencedIdentifierUseCount(
	func: t.FunctionExpression | t.FunctionDeclaration,
	name: string,
) {
	let count = 0;
	const wrapped = t.file(t.program([
		t.isFunctionDeclaration(func) ? func : t.expressionStatement(func),
	]));
	normalizeDuplicateRegisterDeclarations(wrapped);
	traverse(wrapped, {
		Function(path) {
			if (path.node !== func) path.skip();
		},
		Identifier(path) {
			if (!path.isReferencedIdentifier({ name })) return;
			count++;
		},
	});
	return count;
}

type StaticMemberPath = NodePath<
	t.MemberExpression | t.OptionalMemberExpression
>;

function staticMemberKeyName(
	member: t.MemberExpression | t.OptionalMemberExpression,
): string | null {
	if (member.computed) {
		if (
			t.isStringLiteral(member.property) ||
			t.isNumericLiteral(member.property)
		) return String(member.property.value);
		return null;
	}
	return t.isIdentifier(member.property) ? member.property.name : null;
}

function staticMemberPath(
	ref: NodePath<t.Identifier>,
): StaticMemberPath | null {
	const parent = ref.parentPath;
	if (
		(parent?.isMemberExpression() ||
			parent?.isOptionalMemberExpression()) &&
		parent.node.object === ref.node
	) {
		return parent as StaticMemberPath;
	}
	return null;
}

function functionNodeStatement(
	func: t.FunctionExpression | t.FunctionDeclaration,
): t.Statement {
	return t.isFunctionDeclaration(func) ? func : t.expressionStatement(func);
}

function patternFromParameter(
	param: t.FunctionParameter,
): t.ObjectPattern | null {
	if (t.isObjectPattern(param)) return param;
	if (t.isAssignmentPattern(param) && t.isObjectPattern(param.left)) {
		return param.left;
	}
	return null;
}

function isDirectIdentifierWrite(path: NodePath<t.Identifier>): boolean {
	const parent = path.parentPath;
	return parent?.isAssignmentExpression() &&
			parent.node.left === path.node ||
		parent?.isUpdateExpression() &&
			parent.node.argument === path.node;
}

/**
 * A parameter initializer is evaluated outside the function body's lexical
 * environment. Moving an expression there must not retain a read or write of a
 * binding declared in that body.
 */
function defaultUsesFunctionBodyBinding(
	expression: t.Expression,
	path: NodePath<t.Expression>,
	func: t.FunctionExpression | t.FunctionDeclaration,
): boolean {
	const freeNames = new Set<string>();
	const wrapped = t.file(t.program([
		t.expressionStatement(t.cloneNode(expression, true)),
	]));
	traverse(wrapped, {
		Identifier(identifier) {
			if (
				!identifier.isReferencedIdentifier() &&
				!isDirectIdentifierWrite(identifier)
			) return;
			if (!identifier.scope.getBinding(identifier.node.name)) {
				freeNames.add(identifier.node.name);
			}
		},
	});
	for (const name of freeNames) {
		const binding = path.scope.getBinding(name);
		if (
			binding?.kind !== 'param' &&
			binding?.path.getFunctionParent()?.node === func
		) return true;
	}
	return false;
}

function conditionalDefaultPath(
	path: NodePath<t.ConditionalExpression>,
	sourceName: string,
): NodePath<t.Expression> | null {
	const consequent = path.get('consequent');
	const alternate = path.get('alternate');
	if (alternate.isIdentifier({ name: sourceName })) return consequent;
	if (consequent.isIdentifier({ name: sourceName })) return alternate;
	return null;
}

function promoteObjectPatternBindingDefaults(
	func: t.FunctionExpression | t.FunctionDeclaration,
): boolean {
	const undefinedAliases = destructuringUndefinedAliases(func.body);
	let changed = false;
	const promoteIdentifier = (identifier: t.Identifier) => {
		const defaultValue = rewriteRepeatedGeneratorBindingDefault(
			func,
			identifier,
			undefinedAliases,
		);
		if (!defaultValue) return identifier;
		changed = true;
		return t.assignmentPattern(
			t.cloneNode(identifier, true),
			defaultValue,
		);
	};
	const promote = (pattern: t.Node): void => {
		if (t.isAssignmentPattern(pattern)) {
			if (!t.isIdentifier(pattern.left)) promote(pattern.left);
			return;
		}
		if (t.isArrayPattern(pattern)) {
			pattern.elements = pattern.elements.map((element) => {
				if (!element) return element;
				if (t.isIdentifier(element)) return promoteIdentifier(element);
				promote(element);
				return element;
			});
			return;
		}
		if (!t.isObjectPattern(pattern)) return;
		for (const property of pattern.properties) {
			if (t.isRestElement(property)) {
				promote(property.argument);
				continue;
			}
			if (!t.isObjectProperty(property)) continue;
			if (!t.isIdentifier(property.value)) {
				promote(property.value);
				continue;
			}
			property.value = promoteIdentifier(property.value);
		}
	};
	for (const param of func.params) {
		const pattern = !t.isTSParameterProperty(param)
			? patternFromParameter(param)
			: null;
		if (pattern) promote(pattern);
	}
	for (const statement of func.body.body) {
		const declaration = singleVariableDeclarator(statement);
		if (!declaration || !t.isObjectPattern(declaration.id)) continue;
		promote(declaration.id);
	}
	if (changed) traverse.cache.clear();
	return changed;
}

/**
 * Whether the member expression is being written through rather than read.
 *
 * A write is not a projection of the object's value, it is an observation of
 * the object's identity: `module.exports = f` stores into the caller's object,
 * while a destructured `{ exports }` binds a copy, so folding one into the
 * other silently drops the store.
 */
function memberIsWriteTarget(member: StaticMemberPath): boolean {
	const parent = member.parentPath;
	if (!parent) return false;
	if (
		parent.isAssignmentExpression() && parent.node.left === member.node
	) return true;
	if (parent.isUpdateExpression()) return true;
	if (parent.isUnaryExpression({ operator: 'delete' })) return true;
	return parent.isMemberExpression() &&
		parent.node.object === member.node &&
		memberIsWriteTarget(parent as StaticMemberPath);
}

/**
 * Whether evaluating this node can be observed.
 *
 * Property reads count as pure here, matching the rest of the pipeline: a
 * getter is possible in principle but Hermes-lowered register loads are not
 * evidence of one, and treating every member read as effectful would refuse
 * every recovery.
 */
function statementHasObservableEffect(statement: t.Statement): boolean {
	let effectful = false;
	t.traverseFast(statement, (node) => {
		if (
			t.isCallExpression(node) || t.isOptionalCallExpression(node) ||
			t.isNewExpression(node) || t.isAwaitExpression(node) ||
			t.isYieldExpression(node) || t.isAssignmentExpression(node) ||
			t.isUpdateExpression(node) || t.isThrowStatement(node) ||
			t.isTaggedTemplateExpression(node) ||
			t.isUnaryExpression(node, { operator: 'delete' })
		) effectful = true;
	});
	return effectful;
}

/**
 * How far into `body` a property read of the parameter is still an *initial*
 * read.
 *
 * Hermes emits a source-level parameter pattern as property loads at function
 * entry, before anything can change the object. Past the first observable
 * effect the object may already have been mutated through the caller's own
 * reference, so folding a read from there into the signature moves it to call
 * time and changes what it sees.
 */
function initialParameterReadLimit(body: t.Statement[]): number {
	const barrier = body.findIndex(statementHasObservableEffect);
	return barrier === -1 ? body.length : barrier;
}

/** Every key the pattern binds through, at any depth. */
function patternPropertyKeys(
	properties: t.ObjectPattern['properties'],
): Array<{ key: t.Node; computed: boolean }> {
	return properties.flatMap((property) => {
		if (!t.isObjectProperty(property)) return [];
		const nested = t.isObjectPattern(property.value)
			? patternPropertyKeys(property.value.properties)
			: [];
		return [{ key: property.key, computed: property.computed }, ...nested];
	});
}

function hoistObjectParameterMemberAliases(
	func: t.FunctionExpression | t.FunctionDeclaration,
): boolean {
	let changed = false;
	const wrapped = t.file(t.program([functionNodeStatement(func)]));
	traverse(wrapped, {
		Function(path) {
			if (path.node !== func) return;
			for (
				let paramIndex = 0;
				paramIndex < func.params.length;
				paramIndex++
			) {
				const param = func.params[paramIndex];
				if (
					!t.isIdentifier(param) ||
					!/^_param_\d+_\d+_$/.test(param.name)
				) {
					continue;
				}
				const binding = path.scope.getBinding(param.name);
				if (!binding || binding.referencePaths.length === 0) continue;
				const properties = new Map<
					string,
					{
						member: StaticMemberPath;
						refs: StaticMemberPath[];
						value?: t.Identifier | t.ObjectPattern;
						remove?: NodePath;
					}
				>();
				const readLimit = initialParameterReadLimit(func.body.body);
				const initialStatements = new Set<t.Statement>(
					func.body.body.slice(0, readLimit),
				);
				let escaped = false;
				for (const reference of binding.referencePaths) {
					const member = staticMemberPath(
						reference as NodePath<t.Identifier>,
					);
					const name = member
						? staticMemberKeyName(member.node)
						: null;
					if (!member || name == null) {
						escaped = true;
						break;
					}
					// A write through the parameter, or a read past the first
					// observable effect, is a use of the object itself. Neither
					// can become a pattern property, and a parameter has one
					// binding form, so either declines the whole parameter.
					if (memberIsWriteTarget(member)) {
						escaped = true;
						break;
					}
					const statement = member.getStatementParent();
					if (
						!statement ||
						!initialStatements.has(statement.node as t.Statement)
					) {
						escaped = true;
						break;
					}
					let property = properties.get(name);
					if (!property) {
						property = { member, refs: [] };
						properties.set(name, property);
					}
					property.refs.push(member);
				}
				if (escaped || properties.size === 0) continue;
				const patternProperties: t.ObjectPattern['properties'] = [];
				for (const [name, property] of properties) {
					const first = property.refs[0];
					const parent = first.parentPath;
					if (
						parent?.isVariableDeclarator() &&
						parent.node.init === first.node
					) {
						const id = parent.get('id');
						const declaration = parent.parentPath;
						if (
							declaration?.isVariableDeclaration() &&
							declaration.node.declarations.length === 1
						) {
							if (id.isIdentifier()) {
								property.value = t.cloneNode(id.node, true);
								property.remove = declaration;
							} else if (id.isObjectPattern()) {
								property.value = t.cloneNode(id.node, true);
								property.remove = declaration;
							}
						}
					}
					if (!property.value) {
						const hint = t.isValidIdentifier(name, false)
							? name
							: t.toIdentifier(name);
						property.value = path.scope.generateUidIdentifier(hint);
					}
					const patternProperty = t.objectProperty(
						t.cloneNode(first.node.property, true),
						t.cloneNode(property.value, true),
						first.node.computed,
					);
					if (
						!patternProperty.computed &&
						t.isIdentifier(patternProperty.key) &&
						t.isIdentifier(patternProperty.value, {
							name: patternProperty.key.name,
						})
					) patternProperty.shorthand = true;
					patternProperties.push(patternProperty);
				}
				const keys = patternPropertyKeys(patternProperties);
				// One property read is bytecode-identical to source-level
				// `obj.k`, so a lone projection is not evidence of a pattern,
				// and keys that are all computed numeric literals are array
				// indexing spelled as destructuring.
				if (
					keys.length < 2 ||
					keys.every((entry) =>
						entry.computed && t.isNumericLiteral(entry.key)
					)
				) continue;
				for (const property of properties.values()) {
					for (const ref of property.refs) {
						if (
							property.remove &&
							ref.findParent((p) => p === property.remove)
						) {
							continue;
						}
						if (!t.isIdentifier(property.value)) continue;
						ref.replaceWith(t.cloneNode(property.value, true));
					}
				}
				const removals = new Set(
					[...properties.values()].flatMap((property) =>
						property.remove ? [property.remove] : []
					),
				);
				for (const removal of removals) removal.remove();
				func.params[paramIndex] = t.objectPattern(patternProperties);
				changed = true;
			}
			path.stop();
		},
	});
	if (changed) traverse.cache.clear();
	return changed;
}

interface ObjectMemberRead {
	source: t.Identifier;
	key: t.Expression | t.PrivateName;
	value: t.Identifier;
	computed: boolean;
}

function objectMemberAliasDeclaration(
	statement: t.Statement,
): ObjectMemberRead | null {
	const declaration = singleVariableDeclarator(statement);
	if (
		!declaration ||
		!t.isIdentifier(declaration.id) ||
		!t.isMemberExpression(declaration.init) ||
		!t.isIdentifier(declaration.init.object)
	) return null;
	const key = staticMemberKeyName(declaration.init);
	if (key == null) return null;
	return {
		source: declaration.init.object,
		key: declaration.init.property,
		value: declaration.id,
		computed: declaration.init.computed,
	};
}

function isSSARegisterValue(value: unknown): value is SSARegister {
	if (typeof value !== 'object' || value === null) return false;
	if (!('type' in value) || !('index' in value) || !('version' in value)) {
		return false;
	}
	return value.type === 'register' &&
		typeof value.index === 'number' &&
		typeof value.version === 'number';
}

function memberReadDestinationIdentifier(
	member: t.MemberExpression,
): t.Identifier | null {
	const destination = (member.property as t.Node).extra
		?.memberReadDestination ??
		member.extra?.memberReadDestination;
	return isSSARegisterValue(destination)
		? t.identifier(registerName(destination))
		: null;
}

function objectMemberReadStatement(
	statement: t.Statement,
): ObjectMemberRead | null {
	const alias = objectMemberAliasDeclaration(statement);
	if (alias) return alias;
	if (
		!t.isExpressionStatement(statement) ||
		!t.isMemberExpression(statement.expression) ||
		!t.isIdentifier(statement.expression.object)
	) return null;
	const key = staticMemberKeyName(statement.expression);
	if (key == null) return null;
	const value = memberReadDestinationIdentifier(statement.expression);
	if (!value) return null;
	return {
		source: statement.expression.object,
		key: statement.expression.property,
		value,
		computed: statement.expression.computed,
	};
}

function hoistObjectMemberAliasesInBody(
	func: t.FunctionExpression | t.FunctionDeclaration,
): boolean {
	let changed = false;
	const body = func.body.body;

	for (let i = 0; i < body.length; i++) {
		const first = objectMemberReadStatement(body[i]);
		if (!first) continue;
		const reads = [first];
		let end = i + 1;
		for (; end < body.length; end++) {
			const next = objectMemberReadStatement(body[end]);
			if (!next || next.source.name !== first.source.name) break;
			reads.push(next);
		}
		const singleUnreferencedIndexAlias = reads.length === 1 &&
			first.value != null &&
			first.computed &&
			isRegisterTempName(first.value.name) &&
			referencedIdentifierUseCount(func, first.value.name) === 0;
		if (reads.length < 2 && !singleUnreferencedIndexAlias) continue;
		const keys = new Set<string>();
		const bindingNames = new Set<string>();
		const properties: t.ObjectPattern['properties'] = [];
		let duplicate = false;
		for (const read of reads) {
			const keyName = staticMemberKeyName({
				type: 'MemberExpression',
				object: read.source,
				property: read.key,
				computed: read.computed,
			} as t.MemberExpression);
			if (
				keyName == null ||
				keys.has(keyName) ||
				bindingNames.has(read.value.name)
			) {
				duplicate = true;
				break;
			}
			keys.add(keyName);
			bindingNames.add(read.value.name);
			const property = t.objectProperty(
				t.cloneNode(read.key, true),
				t.cloneNode(read.value, true),
				read.computed,
			);
			if (
				!property.computed &&
				t.isIdentifier(property.key) &&
				t.isIdentifier(property.value, { name: property.key.name })
			) property.shorthand = true;
			properties.push(property);
		}
		if (duplicate) continue;
		body.splice(
			i,
			reads.length,
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.objectPattern(properties),
					t.cloneNode(first.source, true),
				),
			]),
		);
		changed = true;
	}
	if (changed) traverse.cache.clear();
	return changed;
}

export function hoistDestructuredFunctionParams(
	func: t.FunctionExpression | t.FunctionDeclaration,
) {
	const undefinedAliases = destructuringUndefinedAliases(func.body);
	for (let i = 0; i < func.body.body.length;) {
		const stmt = func.body.body[i];
		if (isEnvironmentCreationStatement(stmt)) {
			i++;
			continue;
		}
		if (
			t.isVariableDeclaration(stmt, { kind: 'const' }) &&
			stmt.declarations.length === 1 &&
			t.isIdentifier(stmt.declarations[0].id) &&
			isEnvironmentSlotName(stmt.declarations[0].id.name) &&
			t.isThisExpression(stmt.declarations[0].init)
		) {
			i++;
			continue;
		}
		if (
			t.isVariableDeclaration(stmt) &&
			stmt.declarations.every((decl) =>
				t.isVariableDeclarator(decl) && decl.init == null
			)
		) {
			i++;
			continue;
		}
		if (stmt.extra?.retainParameterSource === true) break;
		const decl = t.isVariableDeclaration(stmt) &&
				stmt.declarations.length === 1
			? stmt.declarations[0]
			: null;
		if (
			decl && t.isVariableDeclarator(decl) &&
			t.isIdentifier(decl.id) &&
			t.isIdentifier(decl.init)
		) {
			const sourceName = decl.init.name;
			const restIndex = func.params.findIndex((param) =>
				t.isRestElement(param) &&
				t.isIdentifier(param.argument, { name: sourceName })
			);
			if (
				restIndex >= 0 &&
				referencedIdentifierUseCount(func, sourceName) === 1
			) {
				// Hermes generator bodies commonly materialise `arguments` as a
				// synthetic rest parameter and immediately copy it to the first SSA
				// register. Make that register the parameter binding itself. Besides
				// removing a redundant alias, this keeps the binding at invocation
				// time and exposes a following initial `yield undefined` to the
				// generator-wrapper recogniser.
				func.params[restIndex] = t.restElement(
					t.cloneNode(decl.id, true),
				);
				func.body.body.splice(i, 1);
				continue;
			}
		}
		let pattern: t.ArrayPattern | t.ObjectPattern | t.AssignmentPattern;
		let init: t.Expression;
		let assignmentForm = false;
		if (
			decl && t.isVariableDeclarator(decl) &&
			(
				t.isArrayPattern(decl.id) ||
				t.isObjectPattern(decl.id) ||
				t.isAssignmentPattern(decl.id)
			) && t.isExpression(decl.init)
		) {
			pattern = decl.id;
			init = decl.init;
		} else if (
			stmt.extra?.fromDestructuring === true &&
			t.isExpressionStatement(stmt) &&
			t.isAssignmentExpression(stmt.expression, { operator: '=' }) &&
			(
				t.isArrayPattern(stmt.expression.left) ||
				t.isObjectPattern(stmt.expression.left)
			) && t.isExpression(stmt.expression.right) &&
			patternHasOnlyBindingTargets(stmt.expression.left)
		) {
			pattern = stmt.expression.left;
			init = stmt.expression.right;
			assignmentForm = true;
		} else break;
		const directSource = t.isIdentifier(init) ? init : null;
		const defaultCandidates = func.params.flatMap((param, index) => {
			if (!t.isIdentifier(param)) return [];
			const sourceDefault = destructuringSourceDefault(
				init,
				param.name,
				undefinedAliases,
			);
			return sourceDefault ? [{ index, param, sourceDefault }] : [];
		});
		const defaulted = defaultCandidates.length === 1
			? defaultCandidates[0]
			: null;
		const paramIndex = defaulted?.index ??
			func.params.findIndex((param) =>
				directSource != null &&
				t.isIdentifier(param, { name: directSource.name })
			);
		if (paramIndex < 0) break;
		const sourceName = defaulted?.param.name ?? directSource!.name;
		if (
			referencedIdentifierUseCount(func, sourceName) !==
				identifierOccurrences(init, sourceName)
		) break;

		func.params[paramIndex] = defaulted
			? t.assignmentPattern(
				pattern as Parameters<typeof t.assignmentPattern>[0],
				defaulted.sourceDefault.defaultValue,
			)
			: pattern;
		func.body.body.splice(i, 1);
		if (assignmentForm) {
			removePromotedPatternDeclarations(func.body.body, i, pattern);
			i = 0;
		}
	}
	hoistObjectParameterMemberAliases(func);
	hoistObjectMemberAliasesInBody(func);
	promoteObjectPatternBindingDefaults(func);
}

interface PrimedGeneratorObjectParamPart {
	property: t.ObjectPattern['properties'][number];
	statementIndex: number;
	sourceOccurrences: number;
	defaultValue?: t.Expression;
}

function indexedArgumentsLoad(node: t.Node): number | undefined {
	if (
		!t.isMemberExpression(node, { computed: true }) ||
		!t.isIdentifier(node.object, { name: 'arguments' }) ||
		!t.isNumericLiteral(node.property) ||
		!Number.isSafeInteger(node.property.value) || node.property.value < 0
	) return;
	return node.property.value;
}

function initialYieldUndefinedIndex(body: t.Statement[]): number {
	return body.findIndex((statement) =>
		t.isExpressionStatement(statement) &&
		t.isYieldExpression(statement.expression, { delegate: false }) &&
		isUndefinedNode(statement.expression.argument)
	);
}

function primedGeneratorStatementList(
	func: t.FunctionExpression,
): t.Statement[] | undefined {
	if (initialYieldUndefinedIndex(func.body.body) >= 0) return func.body.body;
	for (const statement of func.body.body) {
		if (
			t.isTryStatement(statement) &&
			initialYieldUndefinedIndex(statement.block.body) >= 0
		) return statement.block.body;
	}
}

function generatorParamIdentifier(
	param: t.FunctionParameter,
): { identifier: t.Identifier; defaultValue?: t.Expression } | undefined {
	if (t.isIdentifier(param)) return { identifier: param };
	if (
		t.isAssignmentPattern(param) && t.isIdentifier(param.left) &&
		t.isExpression(param.right)
	) return { identifier: param.left, defaultValue: param.right };
}

function cloneFunctionParameter(
	param: t.FunctionParameter,
): t.FunctionParameter {
	return t.cloneNode(param, true) as t.FunctionParameter;
}

/**
 * Merge the source-facing wrapper signature into a primed generator body.
 *
 * The recovered body parameter owns the binding: its identifiers are the SSA
 * values referenced by the generator body, and replacing them with the
 * wrapper's canonical placeholder leaves those references unbound. The
 * wrapper remains authoritative for invocation semantics which the body does
 * not already express, notably an outer default or rest marker.
 */
export function mergeRecoveredGeneratorWrapperParams(
	recoveredParams: t.Function['params'],
	wrapperParams: t.Function['params'],
	owner?: t.FunctionExpression | t.FunctionDeclaration,
): t.FunctionParameter[] {
	const params: t.FunctionParameter[] = [];
	const count = Math.max(recoveredParams.length, wrapperParams.length);
	for (let index = 0; index < count; index++) {
		const recoveredCandidate = recoveredParams[index];
		const wrapperCandidate = wrapperParams[index];
		const recovered = recoveredCandidate &&
				!t.isTSParameterProperty(recoveredCandidate)
			? recoveredCandidate
			: undefined;
		const wrapper = wrapperCandidate &&
				!t.isTSParameterProperty(wrapperCandidate)
			? wrapperCandidate
			: undefined;
		if (!recovered) {
			if (wrapper) params.push(cloneFunctionParameter(wrapper));
			continue;
		}
		if (
			!wrapper || t.isAssignmentPattern(recovered) ||
			t.isRestElement(recovered)
		) {
			params.push(cloneFunctionParameter(recovered));
			continue;
		}
		if (t.isIdentifier(recovered) && t.isIdentifier(wrapper)) {
			const recoveredUses = owner
				? referencedIdentifierUseCount(owner, recovered.name)
				: 1;
			const wrapperUses = owner
				? referencedIdentifierUseCount(owner, wrapper.name)
				: 0;
			params.push(
				cloneFunctionParameter(
					recoveredUses === 0 && wrapperUses > 0
						? wrapper
						: recovered,
				),
			);
			continue;
		}
		if (t.isAssignmentPattern(wrapper) && t.isExpression(wrapper.right)) {
			params.push(t.assignmentPattern(
				cloneFunctionParameter(recovered) as t.LVal,
				t.cloneNode(wrapper.right, true),
			));
			continue;
		}
		if (t.isRestElement(wrapper)) {
			params.push(t.restElement(
				cloneFunctionParameter(recovered) as t.LVal,
			));
			continue;
		}
		params.push(cloneFunctionParameter(recovered));
	}
	return params;
}

function argumentsAliasStatement(statement: t.Statement) {
	const declaration = singleVariableDeclarator(statement);
	if (
		declaration && t.isIdentifier(declaration.id) && declaration.init &&
		indexedArgumentsLoad(declaration.init) != null
	) {
		return { identifier: declaration.id, value: declaration.init };
	}
	if (!t.isExpressionStatement(statement)) return;
	const expression = statement.expression;
	if (
		!t.isAssignmentExpression(expression, { operator: '=' }) ||
		!t.isIdentifier(expression.left) ||
		indexedArgumentsLoad(expression.right) == null
	) return;
	return { identifier: expression.left, value: expression.right };
}

function structuredGeneratorParamDefault(
	func: t.FunctionExpression,
	body: t.Statement[],
	aliasIndex: number,
	aliasName: string,
	undefinedAliases: ReadonlySet<string>,
) {
	const declaration = singleVariableDeclarator(body[aliasIndex + 1]);
	if (
		!declaration || !t.isIdentifier(declaration.id) ||
		declaration.init != null
	) return;
	const initial = singleIdentifierAssignment(body[aliasIndex + 2]);
	if (
		!initial || !t.isIdentifier(initial.left, {
			name: declaration.id.name,
		}) || !t.isIdentifier(initial.right, { name: aliasName })
	) return;
	const conditional = body[aliasIndex + 3];
	if (
		!t.isIfStatement(conditional) || conditional.alternate != null ||
		!t.isBlockStatement(conditional.consequent) ||
		conditional.consequent.body.length !== 1
	) return;
	const fallback = singleIdentifierAssignment(
		conditional.consequent.body[0],
	);
	if (
		!fallback || !t.isIdentifier(fallback.left, {
			name: declaration.id.name,
		})
	) return;
	const selected = t.conditionalExpression(
		t.cloneNode(conditional.test, true),
		t.cloneNode(fallback.right, true),
		t.identifier(aliasName),
	);
	const sourceDefault = destructuringSourceDefault(
		selected,
		aliasName,
		undefinedAliases,
	);
	if (!sourceDefault) return;
	const consumed = body.slice(aliasIndex + 2, aliasIndex + 4);
	if (
		consumed.reduce(
			(count, statement) =>
				count + identifierOccurrences(statement, aliasName),
			0,
		) !== referencedIdentifierUseCount(func, aliasName)
	) return;
	return {
		target: declaration.id,
		defaultValue: sourceDefault.defaultValue,
		statementCount: 4,
	};
}

function rewriteRepeatedGeneratorBindingDefault(
	func: t.FunctionExpression | t.FunctionDeclaration,
	identifier: t.Identifier,
	undefinedAliases: ReadonlySet<string>,
): t.Expression | undefined {
	const wrapped = t.file(t.program([functionNodeStatement(func)]));
	let binding: ReturnType<Scope['getBinding']> | undefined;
	traverse(wrapped, {
		Function(path) {
			if (path.node === func) {
				binding = path.scope.getBinding(identifier.name);
				return;
			}
		},
	});
	if (!binding || binding.referencePaths.length === 0) return;

	const candidates = new Map<t.ConditionalExpression, t.Expression>();
	for (const reference of binding.referencePaths) {
		let current: NodePath | null = reference;
		let matched = false;
		while (current && current.node !== func) {
			if (current.isConditionalExpression()) {
				const sourceDefault = destructuringSourceDefault(
					current.node,
					identifier.name,
					undefinedAliases,
				);
				if (sourceDefault) {
					const defaultPath = conditionalDefaultPath(
						current,
						identifier.name,
					);
					if (
						!defaultPath ||
						defaultUsesFunctionBodyBinding(
							sourceDefault.defaultValue,
							defaultPath,
							func,
						)
					) return;
					candidates.set(
						current.node,
						sourceDefault.defaultValue,
					);
					matched = true;
					break;
				}
			}
			current = current.parentPath;
		}
		if (!matched) return;
	}
	if (candidates.size === 0) return;
	const [firstDefault] = candidates.values();
	const fingerprint = JSON.stringify(comparableAst(firstDefault));
	if (
		[...candidates.values()].some((candidate) =>
			JSON.stringify(comparableAst(candidate)) !== fingerprint
		)
	) return;

	traverse(wrapped, {
		ConditionalExpression(path) {
			if (!candidates.has(path.node)) return;
			path.replaceWith(t.cloneNode(identifier, true));
			path.skip();
		},
	});
	return t.cloneNode(firstDefault, true);
}

function promoteRepeatedGeneratorParamDefault(
	func: t.FunctionExpression,
	paramIndex: number,
	undefinedAliases: ReadonlySet<string>,
): boolean {
	const info = generatorParamIdentifier(func.params[paramIndex]);
	if (!info || info.defaultValue) return false;
	const defaultValue = rewriteRepeatedGeneratorBindingDefault(
		func,
		info.identifier,
		undefinedAliases,
	);
	if (!defaultValue) return false;
	func.params[paramIndex] = t.assignmentPattern(
		t.cloneNode(info.identifier, true),
		defaultValue,
	);
	return true;
}

/** Promote Hermes' omitted optional formals from the primed generator prefix. */
export function hoistPrimedGeneratorArgumentsParams(
	func: t.FunctionExpression,
): boolean {
	const body = primedGeneratorStatementList(func);
	if (!body) return false;
	const undefinedAliases = destructuringUndefinedAliases(func.body);
	let changed = false;
	for (let index = 0; index < body.length;) {
		if (index === initialYieldUndefinedIndex(body)) break;
		const alias = argumentsAliasStatement(body[index]);
		if (!alias) {
			index++;
			continue;
		}
		const argumentIndex = indexedArgumentsLoad(alias.value)!;
		const existingParam = func.params[argumentIndex];
		const existingIdentifier = existingParam
			? generatorParamIdentifier(existingParam)
			: undefined;
		// Existing formals are real source bindings. Only materialise the omitted
		// optional suffix, and only in order, so explicit source uses of
		// `arguments[n]` are not rewritten as declarations.
		const extendsParams = argumentIndex === func.params.length;
		const repeatsParam = existingIdentifier?.identifier.name ===
			alias.identifier.name;
		if (!extendsParams && !repeatsParam) {
			index++;
			continue;
		}
		const structuredDefault = structuredGeneratorParamDefault(
			func,
			body,
			index,
			alias.identifier.name,
			undefinedAliases,
		);
		if (structuredDefault) {
			const replacement = t.assignmentPattern(
				t.cloneNode(structuredDefault.target, true),
				t.cloneNode(structuredDefault.defaultValue, true),
			);
			if (extendsParams) func.params.push(replacement);
			else func.params[argumentIndex] = replacement;
			body.splice(index, structuredDefault.statementCount);
			changed = true;
			continue;
		}

		let defaultIndex = -1;
		let defaultDeclaration: t.VariableDeclarator | undefined;
		const yieldIndex = initialYieldUndefinedIndex(body);
		for (
			let candidateIndex = index + 1;
			candidateIndex < yieldIndex;
			candidateIndex++
		) {
			const candidate = singleVariableDeclarator(body[candidateIndex]);
			if (
				!candidate || !t.isIdentifier(candidate.id) ||
				!t.isExpression(candidate.init)
			) continue;
			const sourceDefault = destructuringSourceDefault(
				candidate.init,
				alias.identifier.name,
				undefinedAliases,
			);
			if (
				sourceDefault &&
				referencedIdentifierUseCount(func, alias.identifier.name) ===
					identifierOccurrences(
						candidate.init,
						alias.identifier.name,
					)
			) {
				defaultIndex = candidateIndex;
				defaultDeclaration = candidate;
				break;
			}
		}

		let replacement: t.FunctionParameter = t.cloneNode(
			alias.identifier,
			true,
		);
		if (defaultDeclaration && t.isExpression(defaultDeclaration.init)) {
			const sourceDefault = destructuringSourceDefault(
				defaultDeclaration.init,
				alias.identifier.name,
				undefinedAliases,
			)!;
			replacement = t.assignmentPattern(
				t.cloneNode(defaultDeclaration.id as t.Identifier, true),
				t.cloneNode(sourceDefault.defaultValue, true),
			);
		}
		if (extendsParams) func.params.push(replacement);
		else func.params[argumentIndex] = replacement;
		if (defaultIndex >= 0) body.splice(defaultIndex, 1);
		body.splice(index, 1);
		if (!defaultDeclaration) {
			promoteRepeatedGeneratorParamDefault(
				func,
				argumentIndex,
				undefinedAliases,
			);
		}
		changed = true;
	}
	return changed;
}

/**
 * Recover object parameters which Hermes lowers into property probes before a
 * native generator's synthetic initial yield.
 *
 * A sequence such as `const x = param.x; yield undefined` is not, by itself,
 * evidence of destructuring: ordinary source code can cache a property in the
 * same form. Callers therefore use this only after recognising the enclosing
 * CreateGenerator wrapper and its discarded `.next()`. That protocol proves
 * the prefix is invocation-time parameter initialisation rather than the
 * generator's user-visible body.
 */
export function hoistPrimedGeneratorObjectParams(
	func: t.FunctionExpression,
): boolean {
	const body = primedGeneratorStatementList(func);
	if (!body) return false;
	const yieldIndex = initialYieldUndefinedIndex(body);
	if (yieldIndex < 0) return false;
	const paramInfo = func.params.flatMap((param, index) => {
		const info = generatorParamIdentifier(param);
		return info ? [{ ...info, index }] : [];
	});
	const undefinedAliases = destructuringUndefinedAliases(func.body);
	const parts = new Map<string, PrimedGeneratorObjectParamPart[]>();
	let lastParamIndex = -1;
	for (let index = 0; index < yieldIndex; index++) {
		const statement = body[index];
		const declaration = singleVariableDeclarator(statement);
		if (!declaration || !t.isExpression(declaration.init)) continue;

		if (
			t.isIdentifier(declaration.id) &&
			t.isMemberExpression(declaration.init) &&
			t.isExpression(declaration.init.object) &&
			t.isExpression(declaration.init.property)
		) {
			const member = declaration.init;
			const memberObject = member.object;
			if (!t.isExpression(memberObject)) break;
			const directSource = t.isIdentifier(memberObject)
				? memberObject
				: null;
			const defaultCandidates = paramInfo.flatMap((param) => {
				const sourceDefault = destructuringSourceDefault(
					memberObject,
					param.identifier.name,
					undefinedAliases,
				);
				return sourceDefault ? [{ param, sourceDefault }] : [];
			});
			const defaulted = defaultCandidates.length === 1
				? defaultCandidates[0]
				: null;
			const sourceName = defaulted?.param.identifier.name ??
				directSource?.name;
			if (sourceName == null) continue;
			const paramIndex = defaulted?.param.index ??
				paramInfo.find((param) => param.identifier.name === sourceName)
					?.index ??
				-1;
			if (paramIndex < lastParamIndex) return false;
			if (paramIndex < 0) continue;
			lastParamIndex = paramIndex;
			const property = t.objectProperty(
				t.cloneNode(member.property, true),
				t.cloneNode(declaration.id, true),
				member.computed,
			);
			const sourceParts = parts.get(sourceName) ?? [];
			sourceParts.push({
				property,
				statementIndex: index,
				sourceOccurrences: identifierOccurrences(
					memberObject,
					sourceName,
				),
				defaultValue: defaulted?.sourceDefault.defaultValue,
			});
			parts.set(sourceName, sourceParts);
			continue;
		}

		const directPatternSource = t.isIdentifier(declaration.init)
			? paramInfo.find((param) =>
				param.identifier.name ===
					(declaration.init as t.Identifier).name
			)
			: undefined;
		const patternDefaults = paramInfo.flatMap((param) => {
			const sourceDefault = destructuringSourceDefault(
				declaration.init as t.Expression,
				param.identifier.name,
				undefinedAliases,
			);
			return sourceDefault ? [{ param, sourceDefault }] : [];
		});
		const defaultPatternSource = patternDefaults.length === 1
			? patternDefaults[0]
			: undefined;
		if (
			t.isObjectPattern(declaration.id) &&
			(directPatternSource || defaultPatternSource) &&
			patternHasOnlyBindingTargets(declaration.id)
		) {
			const source = defaultPatternSource?.param ?? directPatternSource!;
			const sourceName = source.identifier.name;
			const paramIndex = source.index;
			if (paramIndex < lastParamIndex) return false;
			lastParamIndex = paramIndex;
			const sourceParts = parts.get(sourceName) ?? [];
			for (const property of declaration.id.properties) {
				sourceParts.push({
					property: t.cloneNode(property, true),
					statementIndex: index,
					sourceOccurrences: property === declaration.id.properties[0]
						? identifierOccurrences(
							declaration.init,
							sourceName,
						)
						: 0,
					defaultValue: defaultPatternSource?.sourceDefault
						.defaultValue,
				});
			}
			parts.set(sourceName, sourceParts);
			continue;
		}
	}

	if (parts.size === 0) return false;
	const eligible = new Set<string>();
	for (const [sourceName, sourceParts] of parts) {
		if (
			referencedIdentifierUseCount(func, sourceName) !==
				sourceParts.reduce(
					(sum, part) => sum + part.sourceOccurrences,
					0,
				)
		) continue;
		const defaults = sourceParts.filter((part) =>
			part.defaultValue != null
		);
		if (defaults.length > 1) continue;
		eligible.add(sourceName);
	}
	if (eligible.size === 0) return false;

	for (let paramIndex = 0; paramIndex < func.params.length; paramIndex++) {
		const info = generatorParamIdentifier(func.params[paramIndex]);
		if (!info || !eligible.has(info.identifier.name)) continue;
		const sourceParts = parts.get(info.identifier.name);
		if (!sourceParts) continue;
		const pattern = t.objectPattern(
			sourceParts.map((part) => part.property),
		);
		const defaultValue = sourceParts.find((part) =>
			part.defaultValue != null
		)
			?.defaultValue ?? info.defaultValue;
		func.params[paramIndex] = defaultValue
			? t.assignmentPattern(pattern, t.cloneNode(defaultValue, true))
			: pattern;
	}
	const consumed = [...eligible].flatMap((sourceName) =>
		parts.get(sourceName)!.map((part) => part.statementIndex)
	);
	for (const index of [...new Set(consumed)].toSorted((a, b) => b - a)) {
		body.splice(index, 1);
	}
	for (const param of func.params) {
		const pattern = t.isObjectPattern(param)
			? param
			: t.isAssignmentPattern(param) && t.isObjectPattern(param.left)
			? param.left
			: undefined;
		if (!pattern) continue;
		for (const property of pattern.properties) {
			if (
				!t.isObjectProperty(property) ||
				!t.isIdentifier(property.value)
			) continue;
			const defaultValue = rewriteRepeatedGeneratorBindingDefault(
				func,
				property.value,
				undefinedAliases,
			);
			if (!defaultValue) continue;
			property.value = t.assignmentPattern(
				t.cloneNode(property.value, true),
				defaultValue,
			);
		}
	}
	return true;
}

function isDiscardedGeneratorNext(
	statement: t.Statement,
	generatorName: string,
): boolean {
	if (!t.isExpressionStatement(statement)) return false;
	const expression = statement.expression;
	return t.isCallExpression(expression) &&
		expression.arguments.length === 0 &&
		t.isMemberExpression(expression.callee, { computed: false }) &&
		t.isIdentifier(expression.callee.object, { name: generatorName }) &&
		t.isIdentifier(expression.callee.property, { name: 'next' });
}

/**
 * Finish a native-generator composition which could only expose its body during
 * the late CreateGenerator sweep. This is the AST form of Hermes' exact
 * priming protocol, not a generic immediately-invoked-generator rewrite.
 */
export function collapsePrimedNativeGeneratorWrapper(
	wrapper: t.FunctionExpression,
): t.FunctionExpression | undefined {
	if (wrapper.generator || wrapper.async || wrapper.body.body.length < 3) {
		return;
	}
	const protocolStart = wrapper.body.body.length - 3;
	if (
		!wrapper.body.body.slice(0, protocolStart).every((statement) =>
			isEnvironmentCreationStatement(statement) ||
			(t.isVariableDeclaration(statement) &&
				statement.declarations.every((declaration) =>
					t.isVariableDeclarator(declaration) &&
					(declaration.init == null ||
						isUndefinedNode(declaration.init))
				))
		)
	) return;
	const [declarationStatement, nextStatement, returnStatement] = wrapper.body
		.body.slice(protocolStart);
	const declaration = singleVariableDeclarator(declarationStatement);
	if (
		!declaration || !t.isIdentifier(declaration.id) ||
		!t.isCallExpression(declaration.init) ||
		declaration.init.arguments.length !== 0 ||
		!t.isFunctionExpression(declaration.init.callee, {
			generator: true,
		}) ||
		!isDiscardedGeneratorNext(nextStatement, declaration.id.name) ||
		!t.isReturnStatement(returnStatement) ||
		!t.isIdentifier(returnStatement.argument, {
			name: declaration.id.name,
		})
	) return;

	const generator = declaration.init.callee;
	hoistPrimedGeneratorArgumentsParams(generator);
	hoistPrimedGeneratorObjectParams(generator);
	hoistDestructuredFunctionParams(generator);
	removeRedundantIteratorParamExpansion(generator);
	removeInitialYieldUndefined(generator);
	if (wrapper.id) generator.id = t.cloneNode(wrapper.id, true);
	t.inheritsComments(generator, wrapper);
	return generator;
}

function patternHasOnlyBindingTargets(pattern: t.Node): boolean {
	if (t.isIdentifier(pattern)) return true;
	if (t.isRestElement(pattern)) {
		return patternHasOnlyBindingTargets(pattern.argument);
	}
	if (t.isAssignmentPattern(pattern)) {
		return patternHasOnlyBindingTargets(pattern.left);
	}
	if (t.isArrayPattern(pattern)) {
		return pattern.elements.every((element) =>
			element == null || patternHasOnlyBindingTargets(element)
		);
	}
	if (t.isObjectPattern(pattern)) {
		return pattern.properties.every((property) =>
			t.isRestElement(property)
				? patternHasOnlyBindingTargets(property.argument)
				: patternHasOnlyBindingTargets(property.value)
		);
	}
	return false;
}

function removePromotedPatternDeclarations(
	body: t.Statement[],
	before: number,
	pattern: t.Node,
): void {
	const names = new Set<string>();
	patternParamNames(pattern, names);
	for (let index = before - 1; index >= 0; index--) {
		const statement = body[index];
		if (!t.isVariableDeclaration(statement)) continue;
		statement.declarations = statement.declarations.filter((declaration) =>
			!(
				declaration.init == null && t.isIdentifier(declaration.id) &&
				names.has(declaration.id.name)
			)
		);
		if (statement.declarations.length === 0) body.splice(index, 1);
	}
}

// Collect the identifier names bound by a destructuring parameter pattern.
function patternParamNames(param: t.Node, into: Set<string>) {
	if (t.isIdentifier(param)) {
		into.add(param.name);
		return;
	}
	if (t.isAssignmentPattern(param)) {
		patternParamNames(param.left, into);
		return;
	}
	if (t.isRestElement(param)) {
		patternParamNames(param.argument, into);
		return;
	}
	if (t.isArrayPattern(param)) {
		for (const element of param.elements) {
			if (element) patternParamNames(element, into);
		}
		return;
	}
	if (t.isObjectPattern(param)) {
		for (const property of param.properties) {
			if (t.isRestElement(property)) {
				patternParamNames(property.argument, into);
			} else patternParamNames(property.value, into);
		}
	}
}

function statementContainsIteratorBegin(stmt: t.Statement): boolean {
	let found = false;
	t.traverseFast(stmt, (node) => {
		if (found) return t.traverseFast.skip;
		if (t.isV8IntrinsicIdentifier(node, { name: 'IteratorBegin' })) {
			found = true;
		}
	});
	return found;
}

// When a generator parameter is already a destructuring pattern (e.g. `[r4_3]`), the
// recursive structurer may additionally emit a redundant iterator-protocol expansion
// of that pattern at the top of the body (`let r4_3; [a,b] = IteratorBegin(p); [c,d] =
// IteratorNext(...); if (done) { r4_3 = c } else { r4_3 = undefined }; if (done) {
// IteratorClose(...) }`). It re-derives the already-bound value from a now-free register
// and its `let` collides with the pattern binding. Strip that leading prologue so the
// parameter pattern is the sole binding (matching the legacy reducer's output).
function removeRedundantIteratorParamExpansion(
	func: t.FunctionExpression | t.FunctionDeclaration,
) {
	const boundNames = new Set<string>();
	for (const param of func.params) {
		if (t.isIdentifier(param)) continue;
		patternParamNames(param, boundNames);
	}
	if (boundNames.size === 0) return;

	let end = 0;
	let sawIteratorBegin = false;
	while (end < func.body.body.length) {
		const stmt = func.body.body[end];
		if (isEnvironmentCreationStatement(stmt)) {
			end++;
			continue;
		}
		if (
			t.isVariableDeclaration(stmt) &&
			stmt.declarations.length === 1 &&
			t.isVariableDeclarator(stmt.declarations[0]) &&
			t.isIdentifier(stmt.declarations[0].id) &&
			stmt.declarations[0].init == null &&
			boundNames.has(stmt.declarations[0].id.name)
		) {
			end++;
			continue;
		}
		if (isInitialAsyncParamDestructuringStatement(stmt)) {
			if (statementContainsIteratorBegin(stmt)) sawIteratorBegin = true;
			end++;
			continue;
		}
		break;
	}
	if (!sawIteratorBegin) return;

	const kept = func.body.body.slice(0, end).filter((stmt) =>
		isEnvironmentCreationStatement(stmt)
	);
	func.body.body.splice(0, end, ...kept);
}

function iteratorArrayDecl(stmt: t.Statement | undefined, name: string) {
	const decl = singleVariableDeclarator(stmt);
	if (
		!decl ||
		!t.isArrayPattern(decl.id) ||
		decl.id.elements.length !== 2 ||
		!t.isCallExpression(decl.init) ||
		!t.isV8IntrinsicIdentifier(decl.init.callee, { name })
	) return;
	const ids = decl.id.elements;
	if (!t.isIdentifier(ids[0]) || !t.isIdentifier(ids[1])) return;
	return { ids: [ids[0], ids[1]] as const, args: decl.init.arguments };
}

function isIteratorCloseGuard(
	stmt: t.Statement | undefined,
	stateName: string,
) {
	if (
		!t.isIfStatement(stmt) ||
		stmt.alternate != null ||
		!t.isBlockStatement(stmt.consequent) ||
		stmt.consequent.body.length !== 1
	) return false;
	const test = stmt.test;
	const checksNotDone = (t.isBinaryExpression(test, { operator: '!==' }) &&
		t.isIdentifier(test.left, { name: stateName }) &&
		isUndefinedNode(test.right)) ||
		(t.isUnaryExpression(test, { operator: '!' }) &&
			t.isBinaryExpression(test.argument, { operator: '===' }) &&
			t.isIdentifier(test.argument.left, { name: stateName }) &&
			isUndefinedNode(test.argument.right));
	if (!checksNotDone) return false;

	const [inner] = stmt.consequent.body;
	if (!t.isExpressionStatement(inner)) return false;
	const expr = inner.expression;
	return t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, { name: 'IteratorClose' }) &&
		expr.arguments.length === 2 &&
		t.isIdentifier(expr.arguments[0], { name: stateName }) &&
		t.isBooleanLiteral(expr.arguments[1], { value: false });
}

function singleIdentifierAssignment(
	statement: t.Statement | undefined,
): t.AssignmentExpression | undefined {
	if (!t.isExpressionStatement(statement)) return;
	const expression = statement.expression;
	if (
		!t.isAssignmentExpression(expression, { operator: '=' }) ||
		!t.isIdentifier(expression.left) ||
		!t.isExpression(expression.right)
	) return;
	return expression;
}

function conditionalFirstIteratorValue(
	statement: t.Statement | undefined,
	valueName: string,
	stateName: string,
): t.Identifier | undefined {
	if (
		!t.isIfStatement(statement) ||
		!t.isBlockStatement(statement.consequent) ||
		!t.isBlockStatement(statement.alternate) ||
		statement.consequent.body.length !== 1 ||
		statement.alternate.body.length !== 1
	) return;
	const consequent = singleIdentifierAssignment(
		statement.consequent.body[0],
	);
	const alternate = singleIdentifierAssignment(statement.alternate.body[0]);
	if (
		!consequent || !alternate ||
		!t.isIdentifier(consequent.left) ||
		!t.isIdentifier(alternate.left) ||
		consequent.left.name !== alternate.left.name
	) return;

	const test = statement.test;
	const checksDone = t.isBinaryExpression(test, { operator: '===' }) &&
		t.isIdentifier(test.left, { name: stateName }) &&
		isUndefinedNode(test.right);
	const checksNotDone = (t.isBinaryExpression(test, { operator: '!==' }) &&
		t.isIdentifier(test.left, { name: stateName }) &&
		isUndefinedNode(test.right)) ||
		(t.isUnaryExpression(test, { operator: '!' }) &&
			t.isBinaryExpression(test.argument, { operator: '===' }) &&
			t.isIdentifier(test.argument.left, { name: stateName }) &&
			isUndefinedNode(test.argument.right));
	const doneValue = checksDone ? consequent.right : alternate.right;
	const presentValue = checksDone ? alternate.right : consequent.right;
	if (
		(!checksDone && !checksNotDone) ||
		!isUndefinedNode(doneValue) ||
		!t.isIdentifier(presentValue, { name: valueName })
	) return;
	return t.identifier(consequent.left.name);
}

export function hoistInitialIteratorDestructuredFunctionParams(
	func: t.FunctionExpression | t.FunctionDeclaration,
) {
	for (let paramIndex = 0; paramIndex < func.params.length; paramIndex++) {
		const param = func.params[paramIndex];
		const paramInfo = generatorParamIdentifier(param);
		if (!paramInfo) continue;
		if (
			referencedIdentifierUseCount(func, paramInfo.identifier.name) !== 1
		) continue;

		let i = 0;
		while (i < func.body.body.length) {
			const stmt = func.body.body[i];
			if (isEnvironmentCreationStatement(stmt)) {
				i++;
				continue;
			}
			if (
				t.isVariableDeclaration(stmt) &&
				stmt.declarations.every((decl) =>
					t.isVariableDeclarator(decl) &&
					(decl.init == null || isUndefinedNode(decl.init))
				)
			) {
				i++;
				continue;
			}
			break;
		}

		const begin = iteratorArrayDecl(func.body.body[i], 'IteratorBegin');
		const next = iteratorArrayDecl(func.body.body[i + 1], 'IteratorNext');
		if (
			!begin ||
			begin.args.length !== 1 ||
			!t.isIdentifier(begin.args[0], {
				name: paramInfo.identifier.name,
			}) ||
			!next ||
			next.args.length !== 2 ||
			!t.isIdentifier(next.args[0], { name: begin.ids[0].name }) ||
			!t.isIdentifier(next.args[1], { name: begin.ids[1].name })
		) continue;

		let closeIndex = i + 2;
		let patternName = next.ids[0].name;
		const maybeCopy = func.body.body[closeIndex];
		if (
			t.isExpressionStatement(maybeCopy) &&
			t.isAssignmentExpression(maybeCopy.expression, { operator: '=' }) &&
			t.isIdentifier(maybeCopy.expression.left) &&
			t.isIdentifier(maybeCopy.expression.right, {
				name: next.ids[0].name,
			})
		) {
			patternName = maybeCopy.expression.left.name;
			closeIndex++;
		} else {
			const conditionalTarget = conditionalFirstIteratorValue(
				maybeCopy,
				next.ids[0].name,
				next.ids[1].name,
			);
			if (conditionalTarget) {
				patternName = conditionalTarget.name;
				closeIndex++;
			}
		}
		if (
			!isIteratorCloseGuard(func.body.body[closeIndex], next.ids[1].name)
		) {
			continue;
		}

		const pattern = t.arrayPattern([
			t.identifier(patternName),
		]);
		func.params[paramIndex] = paramInfo.defaultValue
			? t.assignmentPattern(
				pattern,
				t.cloneNode(paramInfo.defaultValue, true),
			)
			: pattern;
		func.body.body.splice(i, closeIndex - i + 1);
		for (let prefix = i - 1; prefix >= 0; prefix--) {
			const statement = func.body.body[prefix];
			if (!t.isVariableDeclaration(statement)) continue;
			const declarationIndex = statement.declarations.findIndex((
				declaration,
			) => t.isIdentifier(declaration.id, { name: patternName }) &&
				(declaration.init == null || isUndefinedNode(declaration.init))
			);
			if (declarationIndex < 0) continue;
			if (statement.declarations.length === 1) {
				func.body.body.splice(prefix, 1);
			} else {
				statement.declarations.splice(declarationIndex, 1);
			}
			break;
		}
	}
}

function isInitialAsyncParamDestructuringStatement(stmt: t.Statement): boolean {
	if (t.isVariableDeclaration(stmt)) {
		return stmt.declarations.every((decl) => {
			if (!t.isVariableDeclarator(decl)) return false;
			if (t.isArrayPattern(decl.id) || t.isObjectPattern(decl.id)) {
				return true;
			}
			if (!t.isArrayPattern(decl.id) || !t.isCallExpression(decl.init)) {
				return false;
			}
			return t.isV8IntrinsicIdentifier(decl.init.callee, {
				name: 'IteratorBegin',
			}) ||
				t.isV8IntrinsicIdentifier(decl.init.callee, {
					name: 'IteratorNext',
				});
		});
	}
	if (t.isIfStatement(stmt)) {
		if (
			!t.isBlockStatement(stmt.consequent) ||
			!stmt.consequent.body.every(
				isInitialAsyncParamDestructuringStatement,
			)
		) return false;
		// The recursive structurer emits the destructuring done-check as
		// `if (done) { target = value } else { target = undefined }`; accept an
		// `else` arm made of the same destructuring statements (the legacy reducer
		// produces a bare `if (done) {}` with no alternate).
		if (stmt.alternate == null) return true;
		return t.isBlockStatement(stmt.alternate) &&
			stmt.alternate.body.every(
				isInitialAsyncParamDestructuringStatement,
			);
	}
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	if (t.isAssignmentExpression(expr, { operator: '=' })) return true;
	return t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, { name: 'IteratorClose' });
}

function removeInitialYieldUndefined(func: t.FunctionExpression) {
	// Both callers have already proven Hermes' CreateGenerator + discarded
	// `.next()` protocol. Everything before this top-level yield is therefore
	// invocation-time setup: parameters, environment initialisation and hoisted
	// declarations may be interleaved, and must be preserved rather than used as
	// reasons to miss the synthetic yield.
	const body = primedGeneratorStatementList(func);
	if (!body) return false;
	const index = initialYieldUndefinedIndex(body);
	if (index < 0) return false;
	body.splice(index, 1);
	return true;
}

function envSlotNameOwner(name: string) {
	const match = /^_env_(\d+)_/.exec(name);
	if (!match) return;
	return Number(match[1]);
}

function directDeclaredNames(body: t.Statement[]) {
	const names = new Set<string>();
	for (const stmt of body) {
		if (!t.isVariableDeclaration(stmt)) continue;
		for (const decl of stmt.declarations) {
			for (const id of identifiersInPattern(decl.id)) {
				names.add(id.name);
			}
		}
	}
	return names;
}

function insertDeferredEnvironmentDeclarations(wrapped: t.File) {
	const bodyPaths = new Map<
		FunctionId,
		NodePath<t.Program | t.BlockStatement>
	>();
	const envNames = new Map<FunctionId, Set<string>>();
	const addEnvName = (name: string) => {
		const functionId = envSlotNameOwner(name);
		if (functionId == null) return;
		const names = envNames.get(functionId) ?? new Set<string>();
		names.add(name);
		envNames.set(functionId, names);
	};

	traverse(wrapped, {
		Program(path) {
			bodyPaths.set(0, path);
		},
		Function(path) {
			const functionId = (path.node.extra as LiftedExtra | undefined)
				?.parentFunctionId;
			const bodyPath = path.get('body');
			if (functionId == null || !bodyPath.isBlockStatement()) return;
			bodyPaths.set(functionId, bodyPath);
		},
		Identifier(path) {
			addEnvName(path.node.name);
		},
	});

	for (const [functionId, names] of envNames) {
		const bodyPath = bodyPaths.get(functionId);
		if (!bodyPath) continue;
		const body = bodyPath.node.body;
		const declared = directDeclaredNames(body);
		const declarators = [...names].toSorted()
			.filter((name) => !declared.has(name))
			.map((name) => t.variableDeclarator(t.identifier(name)));
		if (declarators.length === 0) continue;
		body.unshift(t.variableDeclaration('var', declarators));
	}
}

function memberName(member: t.MemberExpression) {
	if (!member.computed && t.isIdentifier(member.property)) {
		return member.property.name;
	}
	if (member.computed && t.isStringLiteral(member.property)) {
		return member.property.value;
	}
	return null;
}

function singleVariableDeclarator(stmt: t.Statement | undefined) {
	if (!stmt || !t.isVariableDeclaration(stmt)) return;
	if (stmt.declarations.length !== 1) return;
	const [decl] = stmt.declarations;
	return t.isVariableDeclarator(decl) ? decl : undefined;
}

function isMemberCall(
	expr: t.Expression | null | undefined,
	objectName: string,
	propertyName: string,
) {
	if (!t.isCallExpression(expr)) return false;
	const callee = expr.callee;
	return t.isMemberExpression(callee) &&
		t.isIdentifier(callee.object, { name: objectName }) &&
		memberName(callee) === propertyName;
}

function asyncIteratorPrelude(
	body: t.Statement[],
	index: number,
) {
	const iterDecl = singleVariableDeclarator(body[index]);
	if (
		!iterDecl ||
		!t.isIdentifier(iterDecl.id) ||
		!t.isCallExpression(iterDecl.init) ||
		!t.matchesPattern(iterDecl.init.callee, [
			'HermesInternal',
			'makeAsyncIterator',
		]) ||
		iterDecl.init.arguments.length !== 1 ||
		!t.isExpression(iterDecl.init.arguments[0])
	) return;

	const nextDecl = singleVariableDeclarator(body[index + 1]);
	if (
		!nextDecl ||
		!t.isIdentifier(nextDecl.id) ||
		!isMemberCall(nextDecl.init, iterDecl.id.name, 'next')
	) return;

	const ensureStmt = body[index + 2];
	if (
		!t.isExpressionStatement(ensureStmt) ||
		!t.isCallExpression(ensureStmt.expression) ||
		!t.matchesPattern(ensureStmt.expression.callee, [
			'HermesInternal',
			'ensureObject',
		]) ||
		!t.isIdentifier(ensureStmt.expression.arguments[0], {
			name: nextDecl.id.name,
		})
	) return;

	const awaitStmt = body[index + 3];
	if (!t.isExpressionStatement(awaitStmt)) return;
	const awaitExpr = awaitStmt.expression;
	let resultName: string | undefined;
	if (
		t.isAssignmentExpression(awaitExpr, { operator: '=' }) &&
		t.isIdentifier(awaitExpr.left) &&
		t.isAwaitExpression(awaitExpr.right) &&
		t.isIdentifier(awaitExpr.right.argument, { name: nextDecl.id.name })
	) {
		resultName = awaitExpr.left.name;
	} else if (
		t.isAwaitExpression(awaitExpr) &&
		t.isIdentifier(awaitExpr.argument, { name: nextDecl.id.name })
	) {
		resultName = nextDecl.id.name;
	} else return;

	return {
		iterName: iterDecl.id.name,
		nextName: nextDecl.id.name,
		resultName,
		source: iterDecl.init.arguments[0],
	};
}

function isDoneCheck(stmt: t.Statement | undefined, resultName: string) {
	if (!stmt || !t.isIfStatement(stmt)) return;
	const test = stmt.test;
	if (
		!t.isMemberExpression(test) ||
		!t.isIdentifier(test.object, { name: resultName }) ||
		memberName(test) !== 'done'
	) return;
	const consequent = t.isBlockStatement(stmt.consequent)
		? stmt.consequent.body
		: [stmt.consequent];
	const terminal = consequent.at(-1);
	if (consequent.length === 1 && t.isBreakStatement(terminal)) {
		return { exitStatements: [] as t.Statement[], requiresBody: false };
	}
	if (
		terminal &&
		(t.isReturnStatement(terminal) || t.isThrowStatement(terminal))
	) {
		return {
			exitStatements: consequent.map((s) => t.cloneNode(s, true)),
			requiresBody: true,
		};
	}
}

function isAsyncIteratorUpdateTail(
	stmts: t.Statement[],
	start: number,
	iterName: string,
	nextName: string,
) {
	const nextDecl = singleVariableDeclarator(stmts[start]);
	if (
		!nextDecl ||
		!t.isIdentifier(nextDecl.id, { name: nextName }) ||
		!isMemberCall(nextDecl.init, iterName, 'next')
	) return false;
	const ensureStmt = stmts[start + 1];
	if (
		!t.isExpressionStatement(ensureStmt) ||
		!t.isCallExpression(ensureStmt.expression) ||
		!t.matchesPattern(ensureStmt.expression.callee, [
			'HermesInternal',
			'ensureObject',
		]) ||
		!t.isIdentifier(ensureStmt.expression.arguments[0], { name: nextName })
	) return false;
	const awaitStmt = stmts[start + 2];
	if (!t.isExpressionStatement(awaitStmt)) return false;
	const expr = awaitStmt.expression;
	if (t.isAwaitExpression(expr)) {
		return t.isIdentifier(expr.argument, { name: nextName });
	}
	return t.isAssignmentExpression(expr, { operator: '=' }) &&
		t.isAwaitExpression(expr.right) &&
		t.isIdentifier(expr.right.argument, { name: nextName });
}

function asyncIteratorReadSequence(
	stmts: t.Statement[],
	start: number,
	iterName: string,
) {
	const nextDecl = singleVariableDeclarator(stmts[start]);
	if (
		!nextDecl ||
		!t.isIdentifier(nextDecl.id) ||
		!isMemberCall(nextDecl.init, iterName, 'next')
	) return;

	const ensureStmt = stmts[start + 1];
	if (
		!t.isExpressionStatement(ensureStmt) ||
		!t.isCallExpression(ensureStmt.expression) ||
		!t.matchesPattern(ensureStmt.expression.callee, [
			'HermesInternal',
			'ensureObject',
		]) ||
		!t.isIdentifier(ensureStmt.expression.arguments[0], {
			name: nextDecl.id.name,
		})
	) return;

	const awaitStmt = stmts[start + 2];
	if (!t.isExpressionStatement(awaitStmt)) return;
	const awaitExpr = awaitStmt.expression;
	let resultName: string | undefined;
	if (
		t.isAssignmentExpression(awaitExpr, { operator: '=' }) &&
		t.isIdentifier(awaitExpr.left) &&
		t.isAwaitExpression(awaitExpr.right) &&
		t.isIdentifier(awaitExpr.right.argument, { name: nextDecl.id.name })
	) {
		resultName = awaitExpr.left.name;
	} else if (
		t.isAwaitExpression(awaitExpr) &&
		t.isIdentifier(awaitExpr.argument, { name: nextDecl.id.name })
	) {
		resultName = nextDecl.id.name;
	} else return;

	return {
		nextName: nextDecl.id.name,
		resultName,
	};
}

function generatedAsyncIteratorBody(stmts: t.Statement[]) {
	if (stmts.length !== 1) return stmts;
	const [stmt] = stmts;
	if (
		!t.isTryStatement(stmt) ||
		stmt.block.body.length !== 0 ||
		!stmt.finalizer ||
		stmt.finalizer.body.length === 0
	) return stmts;
	return stmt.finalizer.body.map((bodyStmt) => t.cloneNode(bodyStmt, true));
}

function extractAsyncIteratorValueBinding(
	stmts: t.Statement[],
	resultName: string,
) {
	if (stmts.length === 0) return;
	const firstDecl = singleVariableDeclarator(stmts[0]);
	if (
		firstDecl &&
		t.isIdentifier(firstDecl.id) &&
		t.isMemberExpression(firstDecl.init) &&
		t.isIdentifier(firstDecl.init.object, { name: resultName }) &&
		memberName(firstDecl.init) === 'value'
	) {
		return {
			valueName: firstDecl.id.name,
			bodyStart: 1,
			existingBinding: false,
		};
	}

	const firstStmt = stmts[0];
	if (
		t.isExpressionStatement(firstStmt) &&
		t.isAssignmentExpression(firstStmt.expression, { operator: '=' }) &&
		t.isIdentifier(firstStmt.expression.left) &&
		t.isMemberExpression(firstStmt.expression.right) &&
		t.isIdentifier(firstStmt.expression.right.object, {
			name: resultName,
		}) &&
		memberName(firstStmt.expression.right) === 'value'
	) {
		return {
			valueName: firstStmt.expression.left.name,
			bodyStart: 1,
			existingBinding: true,
		};
	}
}

function replaceResultValueReads(
	stmts: t.Statement[],
	resultName: string,
	valueName: string,
) {
	for (const stmt of stmts) {
		t.traverseFast(stmt, (node) => {
			if (
				t.isMemberExpression(node) &&
				t.isIdentifier(node.object, { name: resultName }) &&
				memberName(node) === 'value'
			) {
				for (const key of Object.keys(node)) {
					delete (node as unknown as Record<string, unknown>)[key];
				}
				Object.assign(node, t.identifier(valueName));
				return t.traverseFast.skip;
			}
		});
	}
}

function asyncIteratorCloseCatchOnly(
	stmt: t.TryStatement,
	iterName: string,
) {
	if (!stmt.handler) return false;
	if (stmt.finalizer && stmt.finalizer.body.length > 0) return false;
	let hasReturnMethod = false;
	let hasAwaitReturnCall = false;
	for (const catchStmt of stmt.handler.body.body) {
		t.traverseFast(catchStmt, (node) => {
			if (
				t.isCallExpression(node) &&
				t.matchesPattern(node.callee, [
					'HermesInternal',
					'getMethod',
				]) &&
				t.isIdentifier(node.arguments[0], { name: iterName }) &&
				t.isStringLiteral(node.arguments[1], { value: 'return' })
			) {
				hasReturnMethod = true;
			}
			if (
				t.isAwaitExpression(node) &&
				t.isCallExpression(node.argument) &&
				t.isMemberExpression(node.argument.callee) &&
				memberName(node.argument.callee) === 'call' &&
				t.isIdentifier(node.argument.arguments[0], { name: iterName })
			) {
				hasAwaitReturnCall = true;
			}
		});
	}
	return hasReturnMethod && hasAwaitReturnCall;
}

function statementListReferencesIdentifier(
	stmts: t.Statement[],
	name: string,
) {
	let referenced = false;
	const wrapped = t.file(
		t.program(stmts.map((stmt) => t.cloneNode(stmt, true))),
	);
	traverse(wrapped, {
		Identifier(path) {
			if (!path.isReferencedIdentifier({ name })) return;
			referenced = true;
			path.stop();
		},
	});
	return referenced;
}

function buildForAwaitStatement(
	prelude: ReturnType<typeof asyncIteratorPrelude>,
	done: NonNullable<ReturnType<typeof isDoneCheck>>,
	loopBody: t.Statement[],
	trailing: t.Statement[],
	following: t.Statement[],
) {
	if (!prelude) return;
	let valueName = `${prelude.resultName}_value`;
	let useExistingBinding = false;
	const binding = extractAsyncIteratorValueBinding(
		loopBody,
		prelude.resultName,
	);
	if (binding) {
		valueName = binding.valueName;
		useExistingBinding = binding.existingBinding;
		loopBody = loopBody.slice(binding.bodyStart);
	}
	if (done.requiresBody && loopBody.length === 0) return;
	replaceResultValueReads(loopBody, prelude.resultName, valueName);
	const trailingClones = trailing.map((stmt) => t.cloneNode(stmt, true));
	const valueUsedAfterLoop = statementListReferencesIdentifier(
		[
			...done.exitStatements,
			...trailingClones,
			...following,
		],
		valueName,
	);
	const forAwait = t.forOfStatement(
		useExistingBinding || valueUsedAfterLoop
			? t.identifier(valueName)
			: t.variableDeclaration('const', [
				t.variableDeclarator(t.identifier(valueName)),
			]),
		t.cloneNode(prelude.source, true),
		t.blockStatement(loopBody),
		true,
	);
	forAwait.extra = { ...forAwait.extra, fromCFGLoop: true };
	return [
		...(valueUsedAfterLoop && !useExistingBinding
			? [
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier(valueName)),
				]),
			]
			: []),
		forAwait,
		...done.exitStatements,
		...trailingClones,
	];
}

function buildForAwaitReplacement(
	prelude: ReturnType<typeof asyncIteratorPrelude>,
	loop: t.WhileStatement,
	trailing: t.Statement[],
	following: t.Statement[],
) {
	if (!prelude || !t.isBooleanLiteral(loop.test, { value: true })) return;
	if (!t.isBlockStatement(loop.body)) return;
	const loopStmts = loop.body.body.map((stmt) => t.cloneNode(stmt, true));
	const done = isDoneCheck(loopStmts[0], prelude.resultName);
	if (!done) return;
	let bodyStart = 1;
	let payload = generatedAsyncIteratorBody(loopStmts.slice(bodyStart));
	if (
		payload.length < 3 ||
		!isAsyncIteratorUpdateTail(
			payload,
			payload.length - 3,
			prelude.iterName,
			prelude.nextName,
		)
	) {
		return;
	}
	const loopBody = payload.slice(0, -3);
	return buildForAwaitStatement(
		prelude,
		done,
		loopBody,
		trailing,
		following,
	);
}

function buildForAwaitEarlyBreakReplacement(
	prelude: ReturnType<typeof asyncIteratorPrelude>,
	loop: t.WhileStatement,
) {
	if (!prelude || !t.isBooleanLiteral(loop.test, { value: true })) return;
	if (!t.isBlockStatement(loop.body)) return;
	const loopStmts = loop.body.body.map((stmt) => t.cloneNode(stmt, true));
	if (!isDoneCheck(loopStmts[0], prelude.resultName)) return;
	let valueName: string | undefined;
	let valueIsExistingBinding = false;
	const valueDecl = singleVariableDeclarator(loopStmts[1]);
	if (valueDecl) {
		if (
			!t.isIdentifier(valueDecl.id) ||
			!t.isMemberExpression(valueDecl.init) ||
			!t.isIdentifier(valueDecl.init.object, {
				name: prelude.resultName,
			}) ||
			memberName(valueDecl.init) !== 'value'
		) return;
		valueName = valueDecl.id.name;
	} else {
		const valueStmt = loopStmts[1];
		if (
			!t.isExpressionStatement(valueStmt) ||
			!t.isAssignmentExpression(valueStmt.expression, {
				operator: '=',
			}) ||
			!t.isIdentifier(valueStmt.expression.left) ||
			!t.isMemberExpression(valueStmt.expression.right) ||
			!t.isIdentifier(valueStmt.expression.right.object, {
				name: prelude.resultName,
			}) ||
			memberName(valueStmt.expression.right) !== 'value'
		) return;
		valueName = valueStmt.expression.left.name;
		valueIsExistingBinding = true;
	}
	const pushStmt = loopStmts[2];
	if (!t.isExpressionStatement(pushStmt)) return;
	const pushExpr = pushStmt.expression;
	if (
		!t.isCallExpression(pushExpr) ||
		!t.isMemberExpression(pushExpr.callee) ||
		memberName(pushExpr.callee) !== 'push' ||
		pushExpr.arguments.length !== 1 ||
		!t.isIdentifier(pushExpr.arguments[0], { name: valueName }) ||
		!t.isIdentifier(pushExpr.callee.object)
	) return;
	const resultsName = pushExpr.callee.object.name;
	const breakIf = loopStmts[3];
	if (!t.isIfStatement(breakIf) || !t.isBlockStatement(breakIf.consequent)) {
		return;
	}
	if (
		breakIf.consequent.body.length !== 1 ||
		!t.isBreakStatement(breakIf.consequent.body[0])
	) return;
	if (!breakIf.alternate || !t.isBlockStatement(breakIf.alternate)) return;
	const alternate = breakIf.alternate.body;
	if (alternate.length !== 4) return;
	if (
		!isAsyncIteratorUpdateTail(
			alternate,
			0,
			prelude.iterName,
			prelude.nextName,
		) ||
		!t.isBreakStatement(alternate[3])
	) return;

	const forAwait = t.forOfStatement(
		valueIsExistingBinding
			? t.identifier(valueName)
			: t.variableDeclaration('const', [
				t.variableDeclarator(t.identifier(valueName)),
			]),
		t.cloneNode(prelude.source, true),
		t.blockStatement([
			t.cloneNode(pushStmt, true),
			t.ifStatement(
				t.cloneNode(breakIf.test, true),
				t.blockStatement([t.breakStatement()]),
			),
		]),
		true,
	);
	forAwait.extra = { ...forAwait.extra, fromCFGLoop: true };
	return [
		forAwait,
		t.expressionStatement(t.yieldExpression(t.identifier(resultsName))),
	];
}

function asyncIteratorDeclarationPrelude(
	body: t.Statement[],
	index: number,
) {
	const iterDecl = singleVariableDeclarator(body[index]);
	if (
		!iterDecl ||
		!t.isIdentifier(iterDecl.id) ||
		!t.isCallExpression(iterDecl.init) ||
		!t.matchesPattern(iterDecl.init.callee, [
			'HermesInternal',
			'makeAsyncIterator',
		]) ||
		iterDecl.init.arguments.length !== 1 ||
		!t.isExpression(iterDecl.init.arguments[0])
	) return;

	return {
		iterName: iterDecl.id.name,
		source: iterDecl.init.arguments[0],
	};
}

function buildForAwaitLoopLocalReadReplacement(
	prelude: ReturnType<typeof asyncIteratorDeclarationPrelude>,
	loop: t.WhileStatement,
	following: t.Statement[],
) {
	if (!prelude || !t.isBooleanLiteral(loop.test, { value: true })) return;
	if (!t.isBlockStatement(loop.body)) return;
	const loopStmts = loop.body.body.map((stmt) => t.cloneNode(stmt, true));
	const read = asyncIteratorReadSequence(loopStmts, 0, prelude.iterName);
	if (!read) return;
	const done = isDoneCheck(loopStmts[3], read.resultName);
	if (!done) return;
	const bodyPrelude = {
		iterName: prelude.iterName,
		nextName: read.nextName,
		resultName: read.resultName,
		source: prelude.source,
	};
	const loopBody = generatedAsyncIteratorBody(loopStmts.slice(4));
	return buildForAwaitStatement(
		bodyPrelude,
		done,
		loopBody,
		[],
		following,
	);
}

function buildForAwaitSingleReadTryReplacement(
	prelude: ReturnType<typeof asyncIteratorDeclarationPrelude>,
	tryStmt: t.TryStatement,
	following: t.Statement[],
) {
	if (!prelude || !tryStmt.finalizer || !tryStmt.handler) return;
	const tryBody = tryStmt.block.body.map((stmt) => t.cloneNode(stmt, true));
	const read = asyncIteratorReadSequence(tryBody, 0, prelude.iterName);
	if (!read) return;
	if (tryBody.length !== 4) return;
	const done = isDoneCheck(tryBody[3], read.resultName);
	if (!done || !done.requiresBody) return;

	const loopBody = tryStmt.finalizer.body.map((stmt) =>
		t.cloneNode(stmt, true)
	);
	if (!extractAsyncIteratorValueBinding(loopBody, read.resultName)) return;
	const bodyPrelude = {
		iterName: prelude.iterName,
		nextName: read.nextName,
		resultName: read.resultName,
		source: prelude.source,
	};
	return buildForAwaitStatement(
		bodyPrelude,
		done,
		loopBody,
		[],
		following,
	);
}

function reduceForAwaitLoopsInBody(body: t.Statement[]): boolean {
	let changed = false;
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (t.isBlockStatement(stmt)) {
			changed = reduceForAwaitLoopsInBody(stmt.body) || changed;
			continue;
		}
		if (t.isTryStatement(stmt)) {
			changed = reduceForAwaitLoopsInBody(stmt.block.body) || changed;
			if (stmt.handler) {
				changed = reduceForAwaitLoopsInBody(stmt.handler.body.body) ||
					changed;
			}
			if (stmt.finalizer) {
				changed = reduceForAwaitLoopsInBody(stmt.finalizer.body) ||
					changed;
			}
			continue;
		}
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = reduceForAwaitLoopsInBody(stmt.consequent.body) ||
					changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = reduceForAwaitLoopsInBody(stmt.alternate.body) ||
					changed;
			}
			continue;
		}
	}

	for (let i = 0; i < body.length; i++) {
		const iterOnlyPrelude = asyncIteratorDeclarationPrelude(body, i);
		if (iterOnlyPrelude && t.isWhileStatement(body[i + 1])) {
			const replacement = buildForAwaitLoopLocalReadReplacement(
				iterOnlyPrelude,
				body[i + 1] as t.WhileStatement,
				body.slice(i + 2),
			);
			if (replacement) {
				body.splice(i, 2, ...replacement);
				changed = true;
				i += replacement.length - 1;
				continue;
			}
		}
		if (iterOnlyPrelude && t.isTryStatement(body[i + 1])) {
			const replacement = buildForAwaitSingleReadTryReplacement(
				iterOnlyPrelude,
				body[i + 1] as t.TryStatement,
				body.slice(i + 2),
			);
			if (replacement) {
				body.splice(i, 2, ...replacement);
				changed = true;
				i += replacement.length - 1;
				continue;
			}
		}

		const prelude = asyncIteratorPrelude(body, i);
		if (!prelude) continue;
		const candidate = body[i + 4];
		if (t.isWhileStatement(candidate)) {
			const earlyBreakReplacement = buildForAwaitEarlyBreakReplacement(
				prelude,
				candidate,
			);
			if (earlyBreakReplacement) {
				body.splice(i, 5, ...earlyBreakReplacement);
				changed = true;
				i += earlyBreakReplacement.length - 1;
				continue;
			}
			const replacement = buildForAwaitReplacement(
				prelude,
				candidate,
				[],
				body.slice(i + 5),
			);
			if (!replacement) continue;
			body.splice(i, 5, ...replacement);
			changed = true;
			i += replacement.length - 1;
			continue;
		}
		if (
			t.isTryStatement(candidate) &&
			candidate.block.body.length >= 1 &&
			t.isWhileStatement(candidate.block.body[0]) &&
			asyncIteratorCloseCatchOnly(candidate, prelude.iterName)
		) {
			const replacement = buildForAwaitReplacement(
				prelude,
				candidate.block.body[0],
				candidate.block.body.slice(1),
				body.slice(i + 5),
			);
			if (!replacement) continue;
			body.splice(i, 5, ...replacement);
			changed = true;
			i += replacement.length - 1;
		}
	}
	return changed;
}

function replacePhiValueReadsInStatements(
	body: t.Statement[],
	start: number,
	name: string,
) {
	let changed = false;
	const wrapped = t.file(t.program(body.slice(start)));
	normalizeDuplicateRegisterDeclarations(wrapped);
	traverse(wrapped, {
		MemberExpression(path) {
			if (
				!t.isIdentifier(path.node.property, { name: 'value' }) ||
				path.node.computed
			) return;
			const object = path.node.object;
			if (
				!t.isCallExpression(object) ||
				!t.isV8IntrinsicIdentifier(object.callee, { name: 'Phi' })
			) return;
			path.replaceWith(t.identifier(name));
			changed = true;
		},
	});
	return changed;
}

function hoistYieldStarCompletion(body: t.Statement[]) {
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (!t.isTryStatement(stmt) || !stmt.finalizer) continue;
		if (stmt.block.body.length !== 1) continue;
		const [tryStmt] = stmt.block.body;
		if (!t.isExpressionStatement(tryStmt)) continue;
		const expr = tryStmt.expression;
		if (!t.isYieldExpression(expr, { delegate: true })) continue;

		const completionName = `r${i}_delegate`;
		if (!replacePhiValueReadsInStatements(body, i + 1, completionName)) {
			continue;
		}
		stmt.block.body = [
			t.expressionStatement(
				t.assignmentExpression(
					'=',
					t.identifier(completionName),
					t.cloneNode(expr, true),
				),
			),
		];
		body.splice(
			i,
			0,
			t.variableDeclaration('let', [
				t.variableDeclarator(t.identifier(completionName)),
			]),
		);
		i++;
	}
}

export interface LiftFileOptions {
	metroModules?: MetroModuleExtractionOptions;
	cfgReducer?: CFGReducerOptions;
	functionIds?: readonly FunctionId[];
	compose?: boolean;
	/**
	 * Compose each of these functions as its own root, inlining the descendants
	 * it owns, instead of emitting the selection standalone.
	 *
	 * Composition is where environment resolution, slot placement and alias
	 * coalescing happen, so a function emitted standalone is missing every
	 * transform that needs its children. Picking a subtree gives those
	 * transforms a corpus small enough to iterate on.
	 */
	composeRoots?: readonly FunctionId[];
	retainRecursiveCFGSummaries?: boolean;
	/**
	 * Receive generated code incrementally. When supplied, `code` in the result
	 * is empty so the complete output is never duplicated in memory.
	 */
	outputSink?: (chunk: string) => void;
}

export interface LiftFileParallelOptions extends LiftFileOptions {
	workers?: number;
	/** Where the run's cold store lives, and whether it survives the run. */
	spill?: ColdSessionOptions & {
		/** Decoded functions the paged `HBCFile` keeps resident. */
		fileCacheLimit?: number;
		/** Functions handed to a lift worker per batch. */
		liftBatchSize?: number;
		/** Batches a lift worker handles before being retired and replaced. */
		recycleAfterBatches?: number;
		/**
		 * Approximate heap budget for all parallel workers. Defaults to
		 * 512MiB per requested worker; ARES_PARALLEL_MEMORY_BUDGET_MB
		 * overrides it for measurement runs.
		 */
		memoryBudgetMiB?: number;
	};
	/**
	 * Read every function's recursive-CFG summary back out of the store.
	 *
	 * Heads only, but on a large bundle that is still one live object per
	 * function held until the run ends -- and the plain decompile path
	 * discards the result. Left on by default so the analysis entry points
	 * keep working; turned off by callers that only want the code.
	 */
	collectRecursiveSummaries?: boolean;
}

/**
 * How environment creation sites were identified during composition.
 *
 * Every site key feeds `_env_<fn>_x<index>` naming, so a key that depends on
 * traversal order makes the emitted names depend on it too. These count the
 * paths where that can happen, so the fallbacks can be retired against a
 * measurement rather than an assumption. See `BINDING-TODO.md` Phase 1.
 */
export interface EnvironmentIdentityDiagnostics {
	/** Keyed by `${functionId}:${kind}:0x${address}` -- stable. */
	byAddress: number;
	/** Keyed by traversal position because `extra.address` was absent. */
	positional: number;
	/** Not indexed at all: the call carried no `parentFunctionId`. */
	unowned: number;
	/**
	 * `environmentCreationIndex` found no key for a call. Reachable for a node
	 * cloned after indexing, since the site map is keyed on node identity, and
	 * the index then comes from a mutable per-function counter.
	 */
	unkeyedIndexLookups: number;
	slotsTagged: number;
	slotsWithoutSite: number;
	/** `localEnvironmentForCreate` resolved to the function's primary env. */
	resolvedPrimary: number;
	/** Resolved to an environment already claimed by the same site key. */
	resolvedClaimed: number;
	/** Resolved to a namespaced `_env_<fn>_x<index>` environment. */
	resolvedNamespaced: number;
	/** Of those, how many had no site key at all. */
	resolvedNamespacedUnkeyed: number;
	/** Environment operands resolved to a structured creation site. */
	resolvedHandles: number;
	/** Environment operands with competing/non-constant definitions. */
	ambiguousHandles: number;
	/** Resolutions which still needed Babel assignment recovery. */
	scopeRecoveredHandles: number;
	/** Environment operands for which no structured identity was available. */
	unresolvedHandles: number;
	/** Slot accesses tagged with `(EnvironmentSiteId, slot)`. */
	resolvedSlots: number;
	/** Slot accesses lowered textually but lacking a creation-site identity. */
	unresolvedSlots: number;
	/** Handle declarations dropped once resolution left them unread. */
	deadLookupHandlesRemoved: number;
	/** Structured slots considered by function-root lexical placement. */
	slotPlacementAnalysed: number;
	/** Slots already declared in their creation function. */
	slotPlacementLocalized: number;
	/** Missing/duplicate/misplaced declarations consolidated at their owner. */
	slotPlacementPlaced: number;
	/** Slots whose creation owner or defining declaration could not be proved. */
	slotPlacementUnresolved: number;
	/** Placed slots referenced by a nested function owner. */
	slotPlacementCaptured: number;
	/** Untagged IR declarations joined to one structured slot identity. */
	slotDeclarationsTagged: number;
	/** Textual declarations which did not map to exactly one slot identity. */
	slotDeclarationsUnresolved: number;
	/** Generated aliases whose source was a parameter/environment slot. */
	storageAliasesAnalysed: number;
	/** Stable source aliases removed after composition. */
	storageAliasesCoalesced: number;
	/** Register-to-parameter/environment aliases removed. */
	storageRegisterAliasesCoalesced: number;
	/** Environment-slot-to-parameter aliases removed. */
	storageEnvironmentSlotAliasesCoalesced: number;
	/** Alias folds refused because the source location is written. */
	storageAliasesBlockedByWrite: number;
	/** Alias folds refused because the source binding was not lexically proven. */
	storageAliasesBlockedByVisibility: number;
	/** Alias folds refused because the generated local itself is mutable. */
	storageAliasesBlockedByLocalMutation: number;
	/** Object buffers folded after removing a blocking storage alias. */
	postAliasObjectFolds: number;
	/** Closed object-rest protocols recovered after slot materialisation. */
	storageObjectRestsRecovered: number;
}

export function emptyEnvironmentIdentityDiagnostics(): EnvironmentIdentityDiagnostics {
	return {
		byAddress: 0,
		positional: 0,
		unowned: 0,
		unkeyedIndexLookups: 0,
		slotsTagged: 0,
		slotsWithoutSite: 0,
		resolvedPrimary: 0,
		resolvedClaimed: 0,
		resolvedNamespaced: 0,
		resolvedNamespacedUnkeyed: 0,
		resolvedHandles: 0,
		ambiguousHandles: 0,
		scopeRecoveredHandles: 0,
		unresolvedHandles: 0,
		resolvedSlots: 0,
		unresolvedSlots: 0,
		deadLookupHandlesRemoved: 0,
		slotPlacementAnalysed: 0,
		slotPlacementLocalized: 0,
		slotPlacementPlaced: 0,
		slotPlacementUnresolved: 0,
		slotPlacementCaptured: 0,
		slotDeclarationsTagged: 0,
		slotDeclarationsUnresolved: 0,
		storageAliasesAnalysed: 0,
		storageAliasesCoalesced: 0,
		storageRegisterAliasesCoalesced: 0,
		storageEnvironmentSlotAliasesCoalesced: 0,
		storageAliasesBlockedByWrite: 0,
		storageAliasesBlockedByVisibility: 0,
		storageAliasesBlockedByLocalMutation: 0,
		postAliasObjectFolds: 0,
		storageObjectRestsRecovered: 0,
	};
}

function addEnvironmentIdentityDiagnostics(
	target: EnvironmentIdentityDiagnostics,
	source: EnvironmentIdentityDiagnostics,
): void {
	for (
		const key of Object.keys(
			source,
		) as (keyof EnvironmentIdentityDiagnostics)[]
	) {
		target[key] += source[key];
	}
}

export interface LiftAnalysisResult {
	code: string;
	recursiveCFGSummaries: RecursiveCFGSummary[];
	environmentIdentity?: EnvironmentIdentityDiagnostics;
}

export interface LiftedFunctionSummary {
	functionId: FunctionId;
	name: string | null;
	functionKind: number;
	paramCount: number;
	frameSize: number;
	environmentSize: number;
	createdEnvironments: Array<{
		kind: 'function' | 'top-level' | 'inner';
		size: number | null;
	}>;
	exceptionHandlerCount: number;
	structured: boolean;
	remainingBlocks: Array<{
		address: number;
		successors: number[];
	}>;
	referencedFunctions: Array<{
		functionId: FunctionId;
		count: number;
	}>;
	recursiveCFG: {
		blockCount: number;
		normalEdgeCount: number;
		exceptionalEdgeCount: number;
		sccCount: number;
		loopCount: number;
		phiCount: number;
		switchCount: number;
		delegateYieldCount: number;
		emissionStatus: RecursiveCFGSummary['emissionStatus'];
		regionKind: string | null;
		misses: string[];
		emitDiagnostics: string[];
		selection: RecursiveCFGSummary['selection'];
		postReductionMisses: string[] | null;
		postReductionAvailable: boolean;
		postReductionProgramAvailable: boolean;
		migrationAudit: RecursiveCFGSummary['migrationAudit'] | null;
	} | null;
}

export interface LiftedFunctionArtifact {
	summary: LiftedFunctionSummary;
	code: string;
}

export interface LiftFunctionsIncrementalOptions {
	cfgReducer?: CFGReducerOptions;
	functionIds?: readonly FunctionId[];
	retainSummaries?: boolean;
}

export interface RecursiveCFGMigrationFunctionSummary {
	functionId: FunctionId;
	selection: RecursiveCFGSummary['selection'] | null;
	migrationAudit: RecursiveCFGSummary['migrationAudit'] | null;
	postReductionAvailable: boolean;
	postReductionProgramAvailable: boolean;
	skippedReason: 'no-entry-block' | 'recursive-summary-unavailable' | null;
}

function selectedFunctionIds(
	file: HBCFile,
	functionIds?: readonly FunctionId[],
): FunctionId[] {
	const selected = functionIds ??
		Array.from({ length: file.functions.length }, (_, id) => id);
	const seen = new Set<FunctionId>();
	const result: FunctionId[] = [];
	for (const id of selected) {
		if (!Number.isInteger(id) || id < 0 || id >= file.functions.length) {
			throw new RangeError(
				`Function #${id} is outside 0-${file.functions.length - 1}`,
			);
		}
		if (seen.has(id)) continue;
		seen.add(id);
		result.push(id);
	}
	return result;
}

function buildIRFunctionsSerial(
	file: HBCFile,
	options: IRFunctionOptions = {},
	functionIds?: readonly FunctionId[],
) {
	const functions = new Map<FunctionId, IRFunction>();
	for (const id of selectedFunctionIds(file, functionIds)) {
		reportProgress(`currently lifting function #${id}`);
		functions.set(
			id,
			new IRFunction(file, new SSAFunction(file.functions[id]), options),
		);
	}
	return functions;
}

function workerCountFor(
	functionCount: number,
	options: LiftFileParallelOptions,
) {
	const requested = options.workers ??
		Math.max(1, (navigator.hardwareConcurrency ?? 2) - 1);
	return Math.max(
		1,
		Math.min(functionCount, Math.floor(requested) || 1),
	);
}

const MiB = 1024 ** 2;
const MIN_LIFT_JOB_BYTES = 32 * MiB;
const MIN_COMPOSE_JOB_BYTES = 128 * MiB;
// Heap per byte of bytecode while a function is lifted, structured and
// emitted. Measured on the largest single-block Metro module of a 127k-function
// bundle: 49 KB of bytecode costs 347 MB of heap, so a batch of sixteen such
// functions is 5.5 GB and dies on V8's 4 GB limit. The old multiplier of 64
// described bytecode-shaped cost only and underestimated by two orders of
// magnitude.
const LIFT_BYTECODE_MULTIPLIER = 8192;
const COMPOSE_BYTECODE_MULTIPLIER = 96;

function parallelMemoryBudget(
	workerCount: number,
	options: LiftFileParallelOptions,
): number {
	const explicit = options.spill?.memoryBudgetMiB;
	if (explicit != null && Number.isFinite(explicit) && explicit > 0) {
		return explicit * MiB;
	}
	const configured = Number(env['ARES_PARALLEL_MEMORY_BUDGET_MB'] ?? NaN);
	if (Number.isFinite(configured) && configured > 0) return configured * MiB;
	return workerCount * 512 * MiB;
}

function bytecodeLength(
	functionId: FunctionId,
	functionBytecodeLengths: readonly number[],
): number {
	const length = functionBytecodeLengths[functionId];
	return Number.isFinite(length) && length > 0 ? length : 1;
}

function estimateLiftBatchBytes(
	functionIds: readonly FunctionId[],
	functionBytecodeLengths: readonly number[],
): number {
	let bytecodeBytes = 0;
	for (const id of functionIds) {
		bytecodeBytes += bytecodeLength(id, functionBytecodeLengths);
	}
	return Math.max(
		MIN_LIFT_JOB_BYTES,
		MIN_LIFT_JOB_BYTES + bytecodeBytes * LIFT_BYTECODE_MULTIPLIER,
	);
}

function estimateComposeBatchBytes(
	readable: readonly FunctionId[],
	functionBytecodeLengths: readonly number[],
): number {
	let bytecodeBytes = 0;
	for (const id of readable) {
		bytecodeBytes += bytecodeLength(id, functionBytecodeLengths);
	}
	return Math.max(
		MIN_COMPOSE_JOB_BYTES,
		MIN_COMPOSE_JOB_BYTES + bytecodeBytes * COMPOSE_BYTECODE_MULTIPLIER,
	);
}

interface ComposeWorkerResult {
	fragments: FunctionId[];
	consumed: FunctionId[];
	failed: { functionId: FunctionId; message: string }[];
	environmentIdentity: EnvironmentIdentityDiagnostics;
}

type QueuedWork =
	| { kind: 'lift'; functionId: FunctionId }
	| {
		kind: 'compose';
		request: Extract<ParallelWorkerRequest, { type: 'compose' }>;
		estimateBytes: number;
		totalModules: number;
		resolve(result: ComposeWorkerResult): void;
		reject(error: unknown): void;
	};

type ActiveWork =
	| {
		kind: 'lift';
		functionIds: FunctionId[];
		estimateBytes: number;
	}
	| {
		kind: 'compose';
		request: Extract<ParallelWorkerRequest, { type: 'compose' }>;
		estimateBytes: number;
		totalModules: number;
		resolve(result: ComposeWorkerResult): void;
		reject(error: unknown): void;
	};

/**
 * A memory-aware pool whose queue holds both lifting and composition work.
 *
 * Lifting still wakes composition bottom-up: `onWritten` fires only after a
 * snapshot batch is committed, and the caller may enqueue newly-ready compose
 * jobs from that callback. The pool then chooses from the single ready queue by
 * memory fit, preferring composition so finished module closures do not wait
 * behind unrelated lifting.
 */
class ParallelWorkPool {
	#queue: QueuedWork[] = [];
	#queuedLiftIds = new Set<FunctionId>();
	#workers = new Set<Worker>();
	#idle: Worker[] = [];
	#age = new Map<Worker, number>();
	#busy = new Set<Worker>();
	#active = new Map<Worker, ActiveWork>();
	#workerHeap = new Map<Worker, number>();
	#busyEstimate = new Map<Worker, number>();
	peakWorkerHeap = 0;
	#failure: Error | undefined;
	#settle: (() => void) | undefined;
	readonly liftFailures = new Map<FunctionId, string>();
	readonly liftFailureFrames = new Map<FunctionId, string[]>();

	constructor(
		readonly spillPath: string,
		readonly options: IRFunctionOptions,
		readonly workerCount: number,
		readonly batchSize: number,
		readonly recycleAfterBatches: number,
		readonly functionBytecodeLengths: readonly number[],
		readonly memoryBudget: number,
		readonly onWritten: (
			functionIds: FunctionId[],
			failed: readonly FunctionId[],
		) => void,
	) {}

	enqueue(functionIds: Iterable<FunctionId>): void {
		for (const id of functionIds) {
			if (this.#queuedLiftIds.has(id)) continue;
			this.#queuedLiftIds.add(id);
			this.#queue.push({ kind: 'lift', functionId: id });
		}
		this.#pump();
	}

	enqueueCompose(
		units: readonly ParallelComposeUnit[],
		readable: FunctionId[],
		globalNames: readonly string[],
		totalModules: number,
	): Promise<ComposeWorkerResult> {
		const { promise, resolve, reject } = Promise.withResolvers<
			ComposeWorkerResult
		>();
		this.#queue.push({
			kind: 'compose',
			request: {
				type: 'compose',
				spillPath: this.spillPath,
				units: units.map(({ functionId, envArg }) => ({
					functionId,
					envArg,
				})),
				readable,
				globalNames: [...globalNames],
				options: this.options,
			},
			estimateBytes: estimateComposeBatchBytes(
				readable,
				this.functionBytecodeLengths,
			),
			totalModules,
			resolve,
			reject,
		});
		this.#pump();
		return promise;
	}

	/**
	 * Move lift ids to the front, keeping their requested relative order.
	 * Compose jobs stay queued as jobs; this method is only about lifting the
	 * closures that make later compose jobs ready.
	 */
	prioritise(first: Iterable<FunctionId>): void {
		const rank = new Map<FunctionId, number>();
		for (const id of first) if (!rank.has(id)) rank.set(id, rank.size);
		if (rank.size === 0) return;
		const head: QueuedWork[] = [];
		const tail: QueuedWork[] = [];
		for (const job of this.#queue) {
			if (job.kind === 'lift' && rank.has(job.functionId)) head.push(job);
			else tail.push(job);
		}
		if (head.length === 0) return;
		head.sort((left, right) => {
			if (left.kind !== 'lift' || right.kind !== 'lift') return 0;
			return rank.get(left.functionId)! - rank.get(right.functionId)!;
		});
		this.#queue = [...head, ...tail];
		this.#pump();
	}

	async run(): Promise<void> {
		if (this.#queue.length === 0) return;
		const liftCount = this.#queue.filter((job) => job.kind === 'lift')
			.length;
		const batches = Math.ceil(liftCount / this.batchSize);
		const count = Math.max(
			1,
			Math.min(this.workerCount, Math.max(batches, this.#queue.length)),
		);
		for (let i = 0; i < count; i++) this.#spawn();
		const { promise, resolve } = Promise.withResolvers<void>();
		this.#settle = resolve;
		this.#pump();
		await promise;
		await this.#shutdown();
		if (this.#failure) throw this.#failure;
	}

	#spawn(): void {
		const worker = new Worker(
			new URL('./parallel_worker.ts', import.meta.url).href,
			{ type: 'module' },
		);
		worker.onmessage = (event: MessageEvent<ParallelWorkerMessage>) => {
			this.#handleMessage(worker, event.data);
		};
		worker.onerror = (event) => {
			this.#handleWorkerError(
				worker,
				event.error ?? new Error(event.message),
			);
		};
		this.#workers.add(worker);
		this.#age.set(worker, 0);
		this.#workerHeap.set(worker, 0);
		this.#idle.push(worker);
	}

	#handleMessage(worker: Worker, message: ParallelWorkerMessage): void {
		const active = this.#active.get(worker);
		if (message.type === 'progress') {
			reportProgress(
				message.phase === 'lift'
					? `currently lifting function #${message.functionId}`
					: `currently composing module #${message.functionId}` +
						(active?.kind === 'compose'
							? ` of ${active.totalModules}`
							: ''),
			);
			return;
		}
		if (message.type === 'closed') return;
		if (message.type === 'written') {
			this.#recordHeap(worker, message.heapUsed);
			for (const failure of message.failed) {
				const { functionId, frames } = failure;
				if (this.liftFailures.has(functionId)) continue;
				this.liftFailures.set(functionId, failure.message);
				if (frames.length > 0) {
					this.liftFailureFrames.set(functionId, frames);
				}
				writeDiagnostic(
					`[lift] function #${functionId} could not be lifted ` +
						`and will be left uninlined: ${failure.message}`,
				);
				for (const frame of frames) {
					writeDiagnostic(`[lift]     at ${frame}`);
				}
			}
			try {
				this.onWritten(
					message.functionIds,
					message.failed.map((f) => f.functionId),
				);
			} catch (error) {
				const cause = error instanceof Error
					? error
					: new Error(String(error));
				this.#fail(
					new Error(
						`scheduling after ${message.functionIds.length} ` +
							`written function(s): ${cause.message}`,
						{ cause },
					),
				);
			}
			this.#finishWorker(worker);
			return;
		}
		if (message.type === 'composed') {
			if (active?.kind !== 'compose') {
				this.#fail(new Error('compose result without compose work'));
				return;
			}
			this.#recordHeap(worker, message.heapUsed);
			active.resolve({
				fragments: message.fragments,
				consumed: message.consumed,
				failed: message.failed,
				environmentIdentity: message.environmentIdentity,
			});
			this.#finishWorker(worker);
			return;
		}
		const error = new Error(
			message.functionId == null
				? `parallel worker failed: ${message.message}`
				: `parallel worker failed while processing function ` +
					`#${message.functionId}: ${message.message}`,
		);
		if (message.stack) error.stack = message.stack;
		this.#handleWorkerError(worker, error);
	}

	#handleWorkerError(worker: Worker, error: Error): void {
		const active = this.#active.get(worker);
		this.#busy.delete(worker);
		this.#busyEstimate.delete(worker);
		this.#active.delete(worker);
		if (active?.kind === 'compose') {
			active.reject(error);
			this.#retire(worker);
			this.#pump();
			return;
		}
		this.#fail(error);
	}

	#recordHeap(worker: Worker, heapUsed: number): void {
		this.#workerHeap.set(worker, heapUsed);
		if (heapUsed > this.peakWorkerHeap) {
			this.peakWorkerHeap = heapUsed;
		}
	}

	#finishWorker(worker: Worker): void {
		this.#busy.delete(worker);
		this.#busyEstimate.delete(worker);
		this.#active.delete(worker);
		const age = (this.#age.get(worker) ?? 0) + 1;
		this.#age.set(worker, age);
		if (age >= this.recycleAfterBatches && this.#queue.length > 0) {
			this.#retire(worker);
		} else {
			this.#idle.push(worker);
		}
		this.#pump();
	}

	#retire(worker: Worker): void {
		if (!this.#workers.has(worker)) return;
		this.#workers.delete(worker);
		this.#age.delete(worker);
		this.#workerHeap.delete(worker);
		this.#busyEstimate.delete(worker);
		this.#active.delete(worker);
		worker.onmessage = (event: MessageEvent<ParallelWorkerMessage>) => {
			if (event.data.type !== 'closed') return;
			worker.terminate();
		};
		worker.onerror = () => worker.terminate();
		worker.postMessage({ type: 'close' } satisfies ParallelWorkerRequest);
		if (this.#queue.length > 0 && !this.#failure) this.#spawn();
	}

	#fail(error: Error): void {
		if (!this.#failure) {
			this.#failure = error;
			writeDiagnostic(`[lift] worker pool failed: ${error.message}`);
			if (error.stack) writeDiagnostic(error.stack);
			writeDiagnostic(
				'[lift] no further batches will be dispatched; waiting for ' +
					`${this.#busy.size} in-flight job(s) to finish`,
			);
		}
		for (const job of this.#queue) {
			if (job.kind === 'compose') job.reject(error);
		}
		this.#queue = [];
		this.#pump();
	}

	#currentPressure(): number {
		let pressure = 0;
		for (const worker of this.#workers) {
			pressure += Math.max(
				this.#workerHeap.get(worker) ?? 0,
				this.#busyEstimate.get(worker) ?? 0,
			);
		}
		return pressure;
	}

	#fits(worker: Worker, estimateBytes: number): boolean {
		const retained = this.#workerHeap.get(worker) ?? 0;
		const additional = Math.max(0, estimateBytes - retained);
		return this.#currentPressure() + additional <= this.memoryBudget ||
			this.#busy.size === 0;
	}

	#takeDispatch(worker: Worker): ActiveWork | undefined {
		for (let i = 0; i < this.#queue.length; i++) {
			const job = this.#queue[i];
			if (job.kind !== 'compose') continue;
			if (!this.#fits(worker, job.estimateBytes)) continue;
			this.#queue.splice(i, 1);
			return {
				kind: 'compose',
				request: job.request,
				estimateBytes: job.estimateBytes,
				totalModules: job.totalModules,
				resolve: job.resolve,
				reject: job.reject,
			};
		}

		const ids: FunctionId[] = [];
		const indices: number[] = [];
		// The budget is shared, but the heap that dies is one worker's. A batch
		// may therefore claim at most this worker's share of the budget; a single
		// function is always admitted, because nothing smaller exists to run.
		const share = Math.max(
			MIN_LIFT_JOB_BYTES,
			Math.floor(this.memoryBudget / this.workerCount),
		);
		for (let i = 0; i < this.#queue.length; i++) {
			const job = this.#queue[i];
			if (job.kind !== 'lift') continue;
			const nextIds = [...ids, job.functionId];
			const estimate = estimateLiftBatchBytes(
				nextIds,
				this.functionBytecodeLengths,
			);
			if (ids.length > 0 && estimate > share) break;
			if (ids.length > 0 && !this.#fits(worker, estimate)) break;
			if (ids.length === 0 && !this.#fits(worker, estimate)) continue;
			ids.push(job.functionId);
			indices.push(i);
			if (ids.length >= this.batchSize) break;
		}
		if (ids.length === 0) return undefined;
		for (let i = indices.length - 1; i >= 0; i--) {
			this.#queue.splice(indices[i], 1);
		}
		return {
			kind: 'lift',
			functionIds: ids,
			estimateBytes: estimateLiftBatchBytes(
				ids,
				this.functionBytecodeLengths,
			),
		};
	}

	#pump(): void {
		for (let i = this.#idle.length - 1; i >= 0; i--) {
			if (this.#failure || this.#queue.length === 0) break;
			const worker = this.#idle[i];
			const active = this.#takeDispatch(worker);
			if (!active) continue;
			this.#idle.splice(i, 1);
			this.#busy.add(worker);
			this.#busyEstimate.set(worker, active.estimateBytes);
			this.#active.set(worker, active);
			if (active.kind === 'lift') {
				worker.postMessage(
					{
						type: 'lift',
						spillPath: this.spillPath,
						functionIds: active.functionIds,
						options: this.options,
					} satisfies ParallelWorkerRequest,
				);
			} else {
				worker.postMessage(active.request);
			}
		}
		if (this.#queue.length === 0 && this.#busy.size === 0) {
			this.#settle?.();
			this.#settle = undefined;
		}
	}

	async #shutdown(): Promise<void> {
		await Promise.all(
			[...this.#workers].map((worker) => {
				const { promise, resolve } = Promise.withResolvers<void>();
				const done = () => {
					worker.terminate();
					resolve();
				};
				worker.onmessage = (
					event: MessageEvent<ParallelWorkerMessage>,
				) => {
					if (event.data.type === 'closed') done();
				};
				worker.onerror = () => done();
				worker.postMessage(
					{ type: 'close' } satisfies ParallelWorkerRequest,
				);
				return promise;
			}),
		);
		this.#workers.clear();
		this.#age.clear();
		this.#idle = [];
	}
}

/**
 * Lift every selected function into the cold store.
 *
 * Nothing comes back but the ids. Workers write their snapshots directly, so
 * this no longer accumulates a map of every snapshot and then a second map of
 * every rehydrated `IRFunction` -- the two structures that made the main thread
 * hold the whole program at once.
 */
/**
 * Which of these still need lifting.
 *
 * Snapshots are committed batch by batch, so a run that dies partway leaves
 * real work on disk -- 39,360 functions of it, in the first attempt at the
 * 127k-function bundle. The `snap` phase marker only says "all of them are
 * here", which is the right thing for `--spill-reuse` to trust wholesale, but
 * it is far too coarse to be the only question asked: without this, a crash at
 * 31% throws away 31%.
 */
function unliftedFunctionIds(
	cold: ColdStore,
	functionIds: readonly FunctionId[],
): FunctionId[] {
	return functionIds.filter((id) => !hasColdSnapshot(cold, id));
}

async function liftIntoColdStore(
	file: HBCFile,
	cold: ColdStore,
	spillPath: string,
	functionBytecodeLengths: readonly number[],
	options: LiftFileParallelOptions = {},
	onWritten: (functionIds: FunctionId[]) => void = () => {},
): Promise<{ functionIds: FunctionId[]; failed: number }> {
	const functionIds = selectedFunctionIds(file, options.functionIds);
	const outstanding = unliftedFunctionIds(cold, functionIds);
	if (outstanding.length < functionIds.length) {
		reportProgress(
			`[lift] resuming: ${
				functionIds.length - outstanding.length
			} of ${functionIds.length} functions already in the cold store`,
		);
	}
	const workerCount = workerCountFor(outstanding.length, options);
	const pool = new ParallelWorkPool(
		spillPath,
		{ cfgReducer: options.cfgReducer },
		workerCount,
		liftBatchSize(options),
		recycleAfterBatches(options),
		functionBytecodeLengths,
		parallelMemoryBudget(workerCount, options),
		(written) => {
			// Workers commit their batches from other threads. This thread's
			// read transaction is a snapshot of the store as it stood when the
			// transaction began, so a batch committed after that is invisible
			// to every later read here -- whole batches of snapshot heads look
			// absent, which is what made their recursive summaries go missing.
			cold.releaseReader();
			onWritten(written);
		},
	);
	pool.enqueue(outstanding);
	await pool.run();
	await reportLiftFailures(pool, cold, outstanding);
	return { functionIds, failed: pool.liftFailures.size };
}

/**
 * Write a diagnostic that nothing can silence.
 *
 * Straight to the file descriptor, because `src/ares.ts` replaces
 * `console.error` with a no-op under `--no-progress` and with a progress
 * renderer otherwise. Progress is noise and may be suppressed; a report that a
 * function could not be lifted is the run's actual output, and suppressing it
 * turns "one closure was left raw" into "the run looked clean".
 *
 * This has caught the same reporting three times now: the cold-store occupancy
 * stats, and then both halves of the lift/compose failure reporting.
 */
function writeDiagnostic(message: string): void {
	Deno.stderr.writeSync(new TextEncoder().encode(`${message}\n`));
}

/**
 * Summarise what could not be lifted.
 *
 * Printed as a block at the end as well as inline, because on a bundle this
 * size the inline notices scroll past long before the run finishes, and the
 * list is the actionable output: each entry is a reproducible single-function
 * bug (`--function <id>` reproduces it in seconds).
 */
async function reportLiftFailures(
	pool: ParallelWorkPool,
	cold: ColdStore,
	attempted: readonly FunctionId[],
): Promise<void> {
	// Anything attempted and not failed this time has succeeded, so its old
	// record goes: otherwise a fixed function stays on the list forever.
	if (pool.peakWorkerHeap > 0) {
		writeDiagnostic(
			`[lift] peak lift-worker heap: ${
				(pool.peakWorkerHeap / 1048576).toFixed(0)
			}MB (recycled every ${pool.recycleAfterBatches} batches)`,
		);
	}
	const succeeded = attempted.filter((id) => !pool.liftFailures.has(id));
	await clearLiftFailures(cold, succeeded);
	await recordLiftFailures(cold, pool.liftFailures);
	if (pool.liftFailures.size === 0) return;
	const ids = [...pool.liftFailures.keys()].toSorted((a, b) => a - b);
	writeDiagnostic(
		`[lift] ${ids.length} function(s) could not be lifted and are left ` +
			'uninlined in the output:',
	);
	for (const id of ids) {
		writeDiagnostic(`[lift]   #${id}: ${pool.liftFailures.get(id)}`);
		for (const frame of pool.liftFailureFrames.get(id) ?? []) {
			writeDiagnostic(`[lift]       at ${frame}`);
		}
		writeDiagnostic(
			`[lift]       reproduce: --cfg-reducer=recursive -f ${id}`,
		);
	}
}

/**
 * Batches a lift worker handles before it is retired and replaced.
 *
 * Sixteen batches is ~256 functions, against a reopen measured at ~0.1s -- so
 * well under a percent of the time those functions take to lift, in exchange
 * for bounding a heap that otherwise only ever grows.
 */
function recycleAfterBatches(options: LiftFileParallelOptions): number {
	return Math.max(1, options.spill?.recycleAfterBatches ?? 16);
}

function liftBatchSize(options: LiftFileParallelOptions): number {
	return Math.max(1, options.spill?.liftBatchSize ?? 16);
}

interface FunctionReferencePlan {
	soleFunctionParents: Map<FunctionId, FunctionId | null>;
	nonSoleFunctionReferences: Set<FunctionId>;
}

interface CompositionPlan extends FunctionReferencePlan {
	safelyNestedFunctions: Set<FunctionId>;
	parentFunctions: Map<FunctionId, FunctionId>;
	funcEnvs: Map<FunctionId, Environment>;
	/** Every environment creation site, per function, in address order. */
	environmentCreationSites: Map<FunctionId, EnvironmentCreationSite[]>;
}

function conditionOutcomeExecutesAssignment(
	condition: NodePath,
	assignment: NodePath<t.AssignmentExpression>,
	outcome: boolean,
): boolean {
	const descendants: NodePath[] = [];
	let cursor: NodePath | null = assignment;
	while (cursor && cursor.node !== condition.node) {
		descendants.push(cursor);
		cursor = cursor.parentPath;
	}
	if (!cursor) return false;
	descendants.reverse();

	let parent = condition;
	let requiredOutcome: boolean | undefined = outcome;
	for (const child of descendants) {
		if (parent.isLogicalExpression()) {
			if (child.key === 'right') {
				if (
					(parent.node.operator === '&&' &&
						requiredOutcome === true) ||
					(parent.node.operator === '||' && requiredOutcome === false)
				) {
					requiredOutcome = parent.node.operator === '&&';
				} else {
					return false;
				}
			} else if (child.key === 'left') {
				requiredOutcome =
					parent.node.operator === '&&' && requiredOutcome === true
						? true
						: parent.node.operator === '||' &&
								requiredOutcome === false
						? false
						: undefined;
			} else {
				return false;
			}
		} else if (parent.isUnaryExpression({ operator: '!' })) {
			if (child.key !== 'argument') return false;
			requiredOutcome = requiredOutcome == null
				? undefined
				: !requiredOutcome;
		} else if (parent.isSequenceExpression()) {
			const expressions = parent.get('expressions');
			if (child.node !== expressions.at(-1)?.node) {
				requiredOutcome = undefined;
			}
		} else if (parent.isConditionalExpression()) {
			if (child.key !== 'test') return false;
			requiredOutcome = undefined;
		} else if (
			(parent.isOptionalCallExpression() ||
				parent.isOptionalMemberExpression()) && parent.node.optional
		) {
			return false;
		} else if (!parent.isExpression() && !parent.isSpreadElement()) {
			return false;
		} else {
			// Ordinary expression operands are eager, but their value is not
			// implied by the enclosing condition's outcome.
			requiredOutcome = undefined;
		}
		parent = child;
	}
	return true;
}

function assignmentExecutesBeforeUse(
	assignment: NodePath<t.AssignmentExpression>,
	use: NodePath,
): boolean {
	if (
		(assignment.getFunctionParent()?.node ?? null) !==
			(use.getFunctionParent()?.node ?? null)
	) return false;

	const assignmentAncestors: NodePath[] = [];
	for (let path: NodePath | null = assignment; path; path = path.parentPath) {
		assignmentAncestors.push(path);
	}
	const useAncestors: NodePath[] = [];
	const useIndex = new Map<t.Node, number>();
	for (let path: NodePath | null = use; path; path = path.parentPath) {
		useIndex.set(path.node, useAncestors.length);
		useAncestors.push(path);
	}

	let common: NodePath | undefined;
	let assignmentBranch: NodePath | undefined;
	let useBranch: NodePath | undefined;
	for (let i = 0; i < assignmentAncestors.length; i++) {
		const path = assignmentAncestors[i];
		const rightIndex = useIndex.get(path.node);
		if (rightIndex == null) continue;
		common = path;
		assignmentBranch = assignmentAncestors[i - 1];
		useBranch = useAncestors[rightIndex - 1];
		break;
	}
	if (!common || !assignmentBranch || !useBranch) return false;

	const assignmentIsUnconditionalWithin = (boundary: NodePath) => {
		let child: NodePath = assignment;
		while (child.node !== boundary.node) {
			const parent: NodePath | null = child.parentPath;
			if (!parent) return false;
			if (
				(parent.isIfStatement() && child.key !== 'test') ||
				(parent.isConditionalExpression() && child.key !== 'test') ||
				(parent.isLogicalExpression() && child.key !== 'left') ||
				parent.isSwitchStatement() || parent.isSwitchCase() ||
				parent.isTryStatement() || parent.isCatchClause() ||
				parent.isLoop() || parent.isFunction()
			) return false;
			if (
				(parent.isOptionalCallExpression() ||
					parent.isOptionalMemberExpression()) &&
				parent.node.optional
			) return false;
			child = parent;
		}
		return true;
	};

	const precedesInList = (listKey: string) =>
		assignmentBranch!.listKey === listKey &&
		useBranch!.listKey === listKey &&
		typeof assignmentBranch!.key === 'number' &&
		typeof useBranch!.key === 'number' &&
		assignmentBranch!.key < useBranch!.key &&
		assignmentIsUnconditionalWithin(assignmentBranch!);

	if (common.isProgram() || common.isBlockStatement()) {
		return precedesInList('body');
	}
	// A case's `consequent` is an ordinary statement list. Falling through from
	// an earlier case enters it at the top, never in the middle, so a statement
	// earlier in the list still runs before a later one -- which is what the
	// `isSwitchCase()` rejection in `assignmentIsUnconditionalWithin` is about,
	// and it does not apply once both sides are inside the same case.
	if (common.isSwitchCase()) {
		return precedesInList('consequent');
	}
	if (common.isSequenceExpression()) {
		return precedesInList('expressions');
	}
	if (
		(common.isIfStatement() || common.isConditionalExpression()) &&
		assignmentBranch.key === 'test' &&
		(useBranch.key === 'consequent' || useBranch.key === 'alternate')
	) {
		return conditionOutcomeExecutesAssignment(
			assignmentBranch,
			assignment,
			useBranch.key === 'consequent',
		);
	}
	if (
		common.isLogicalExpression() && assignmentBranch.key === 'left' &&
		useBranch.key === 'right'
	) {
		if (common.node.operator === '??') return false;
		return conditionOutcomeExecutesAssignment(
			assignmentBranch,
			assignment,
			common.node.operator === '&&',
		);
	}
	if (
		common.isWhileStatement() &&
		assignmentBranch.key === 'test' && useBranch.key === 'body'
	) {
		return conditionOutcomeExecutesAssignment(
			assignmentBranch,
			assignment,
			true,
		);
	}
	if (common.isForStatement() && useBranch.key === 'body') {
		if (assignmentBranch.key === 'init') {
			return assignmentIsUnconditionalWithin(assignmentBranch);
		}
		if (assignmentBranch.key === 'test') {
			return conditionOutcomeExecutesAssignment(
				assignmentBranch,
				assignment,
				true,
			);
		}
	}
	if (
		common.isSwitchStatement() && assignmentBranch.key === 'discriminant' &&
		useBranch.listKey === 'cases'
	) return assignmentIsUnconditionalWithin(assignmentBranch);
	return false;
}

function handlerTriesForUse(
	use: NodePath,
): NodePath<t.TryStatement>[] {
	const tries: NodePath<t.TryStatement>[] = [];
	let child: NodePath = use;
	for (
		let parent: NodePath | null = use.parentPath;
		parent;
		child = parent, parent = parent.parentPath
	) {
		if (parent.isFunction()) break;
		if (
			parent.isCatchClause() &&
			parent.parentPath?.isTryStatement()
		) tries.push(parent.parentPath);
		if (parent.isTryStatement() && child.key === 'finalizer') {
			tries.push(parent);
		}
	}
	return tries;
}

function generatedBindingReadCannotThrow(node: t.Node): boolean {
	if (
		t.isIdentifier(node) &&
		(
			node.name === 'undefined' ||
			/^r\d+_\d+$/.test(node.name) ||
			/^_param_\d+_\d+_$/.test(node.name) ||
			/^_env_\d+_(?:x\d+_)?\d+$/.test(node.name)
		)
	) return true;
	return t.isThisExpression(node) ||
		t.isStringLiteral(node) ||
		t.isNumericLiteral(node) ||
		t.isBooleanLiteral(node) ||
		t.isNullLiteral(node) ||
		t.isBigIntLiteral(node) ||
		t.isRegExpLiteral(node) ||
		t.isFunctionExpression(node) ||
		t.isArrowFunctionExpression(node);
}

function protectedPrefixExpressionCannotThrow(node: t.Expression): boolean {
	if (generatedBindingReadCannotThrow(node)) return true;
	if (isReadOnlyEnvironmentLookup(node)) {
		return node.arguments.every((argument) =>
			t.isExpression(argument) &&
			generatedBindingReadCannotThrow(argument)
		);
	}
	if (
		t.isUnaryExpression(node) &&
		['void', 'typeof', '!'].includes(node.operator)
	) return protectedPrefixExpressionCannotThrow(node.argument);
	if (t.isSequenceExpression(node)) {
		return node.expressions.every(protectedPrefixExpressionCannotThrow);
	}
	if (
		t.isAssignmentExpression(node, { operator: '=' }) &&
		t.isIdentifier(node.left) &&
		/^((r\d+_\d+)|(_env_\d+_(?:x\d+_)?\d+))$/.test(node.left.name)
	) return protectedPrefixExpressionCannotThrow(node.right);
	return false;
}

function protectedPrefixStatementCannotThrow(node: t.Statement): boolean {
	if (t.isEmptyStatement(node) || t.isFunctionDeclaration(node)) return true;
	if (t.isVariableDeclaration(node)) {
		return node.declarations.every((declaration) =>
			t.isIdentifier(declaration.id) &&
			(declaration.init == null ||
				(t.isExpression(declaration.init) &&
					protectedPrefixExpressionCannotThrow(declaration.init)))
		);
	}
	return t.isExpressionStatement(node) &&
		protectedPrefixExpressionCannotThrow(node.expression);
}

/**
 * A catch/finally entry is not ordinarily dominated by an assignment in its
 * protected body. It is dominated when that assignment is a direct statement
 * in the body's non-throwing prefix: no exceptional edge can reach the handler
 * before the pure environment lookup has initialized the generated register.
 */
function environmentLookupInitializesHandlerUse(
	assignment: NodePath<t.AssignmentExpression>,
	use: NodePath,
): boolean {
	return handlerTriesForUse(use).some((tryPath) => {
		let statement: NodePath = assignment;
		while (
			statement.parentPath &&
			statement.parentPath.node !== tryPath.node.block
		) {
			if (statement.parentPath.isFunction()) return false;
			statement = statement.parentPath;
		}
		if (
			statement.parentPath?.node !== tryPath.node.block ||
			!statement.isExpressionStatement() ||
			statement.node.expression !== assignment.node ||
			typeof statement.key !== 'number'
		) return false;

		return tryPath.node.block.body.slice(0, statement.key).every(
			protectedPrefixStatementCannotThrow,
		);
	});
}

/**
 * Every expression a handle register can be bound to.
 *
 * Wider than `isReadOnlyEnvironmentLookup`, which covers only the read-only
 * lookups that are safe to *substitute*. Deciding which environment a handle
 * denotes does not move any code, so a creation site answers that question too.
 */
function isEnvironmentValuedExpression(
	node: t.Node | null | undefined,
): node is t.CallExpression {
	if (!t.isCallExpression(node) || !t.isV8IntrinsicIdentifier(node.callee)) {
		return false;
	}
	return [
		'GetParentEnvironment',
		'GetEnvironment',
		'GetClosureEnvironment',
		'CreateFunctionEnvironment',
		'CreateTopLevelEnvironment',
		'CreateEnvironment',
	].includes(node.callee.name);
}

/**
 * Recover a pure environment lookup split from its generated declaration.
 *
 * Reducer materialization can turn `const env = %GetParentEnvironment(n)` into
 * `let env; ... env = %GetParentEnvironment(n)`. Babel then correctly marks
 * the binding non-constant, so the ordinary composition resolver cannot chase
 * it. Accept the split form only when every write is the same read-only lookup
 * and one of those writes structurally dominates this particular use.
 */
export function assignedEnvironmentLookupForUse(
	environmentPath: NodePath<t.Identifier>,
	onProtectedHandlerRecovery?: (
		assignment: NodePath<t.AssignmentExpression>,
	) => void,
): t.Expression | undefined {
	const { name } = environmentPath.node;
	const binding = environmentPath.scope.getBinding(name);
	if (!binding?.path.isVariableDeclarator()) return;
	const owner = environmentPath.getFunctionParent()?.node ?? null;
	if ((binding.path.getFunctionParent()?.node ?? null) !== owner) return;

	const candidates: t.Expression[] = [];
	const init = binding.path.node.init;
	if (init != null) {
		if (!isReadOnlyEnvironmentLookup(init)) return;
		candidates.push(init);
	}

	let hasDominatingAssignment = false;
	const protectedHandlerAssignments: NodePath<t.AssignmentExpression>[] = [];
	for (const violation of binding.constantViolations) {
		if (
			!violation.isAssignmentExpression({ operator: '=' }) ||
			!t.isIdentifier(violation.node.left, { name }) ||
			!isReadOnlyEnvironmentLookup(violation.node.right) ||
			(violation.getFunctionParent()?.node ?? null) !== owner
		) return;
		candidates.push(violation.node.right);
		const assignment = violation as NodePath<t.AssignmentExpression>;
		const ordinaryDominance = assignmentExecutesBeforeUse(
			assignment,
			environmentPath,
		);
		const protectedHandlerDominance =
			environmentLookupInitializesHandlerUse(
				assignment,
				environmentPath,
			);
		hasDominatingAssignment ||= ordinaryDominance ||
			protectedHandlerDominance;
		if (protectedHandlerDominance) {
			protectedHandlerAssignments.push(assignment);
		}
	}
	if (candidates.length === 0) return;
	if (init == null && !hasDominatingAssignment) return;
	const [candidate] = candidates;
	if (!candidates.every((node) => t.isNodesEquivalent(node, candidate))) {
		return;
	}
	for (const assignment of protectedHandlerAssignments) {
		onProtectedHandlerRecovery?.(assignment);
	}
	return t.cloneNode(candidate, true);
}

/**
 * Remove a split environment lookup only when protected-handler recovery
 * consumed every reference to its generated register. The WeakSet limits this
 * to assignments proven by environmentLookupInitializesHandlerUse; ordinary
 * dead-code elimination remains outside this pass.
 */
export function removeDeadRecoveredProtectedEnvironmentHandles(
	file: t.File,
	recoveredAssignments: WeakSet<t.AssignmentExpression>,
): number {
	traverse(file, {
		Program(path) {
			path.scope.crawl();
			path.stop();
		},
	});
	const bindings = new Set<Binding>();
	traverse(file, {
		AssignmentExpression(path) {
			if (!recoveredAssignments.has(path.node)) return;
			if (!t.isIdentifier(path.node.left)) return;
			const binding = path.scope.getBinding(path.node.left.name);
			if (binding) bindings.add(binding);
		},
	});

	let removed = 0;
	for (const binding of bindings) {
		if (binding.referencePaths.length > 0) continue;
		if (
			!binding.path.isVariableDeclarator() ||
			binding.path.node.init != null ||
			!binding.constantViolations.every((violation) =>
				violation.isAssignmentExpression({ operator: '=' }) &&
				recoveredAssignments.has(violation.node) &&
				isReadOnlyEnvironmentLookup(violation.node.right) &&
				expressionResultIsDiscarded(
					violation as NodePath<t.AssignmentExpression>,
				)
			)
		) continue;

		for (const violation of binding.constantViolations.toReversed()) {
			if (
				removeDiscardedExpression(
					violation as NodePath<t.AssignmentExpression>,
				)
			) removed++;
		}
		const declaration = binding.path.parentPath;
		binding.path.remove();
		if (
			declaration?.isVariableDeclaration() &&
			declaration.node.declarations.length === 0
		) declaration.remove();
	}
	return removed;
}

function expressionResultIsDiscarded(path: NodePath<t.Expression>): boolean {
	const parent = path.parentPath;
	if (parent?.isExpressionStatement()) return true;
	if (!parent?.isSequenceExpression()) return false;
	const expressions = parent.get('expressions');
	if (expressions.at(-1)?.node !== path.node) return true;
	return expressionResultIsDiscarded(
		parent as NodePath<t.SequenceExpression>,
	);
}

function removeDiscardedExpression(path: NodePath<t.Expression>): boolean {
	if (!expressionResultIsDiscarded(path)) return false;
	const parent = path.parentPath!;
	if (parent.isExpressionStatement()) {
		parent.remove();
		return true;
	}
	if (!parent.isSequenceExpression()) return false;
	const expressions = parent.get('expressions');
	if (expressions.length === 2) {
		const remaining = expressions.find((expression) =>
			expression.node !== path.node
		);
		if (!remaining?.isExpression()) return false;
		parent.replaceWith(t.cloneNode(remaining.node, true));
		return true;
	}
	path.remove();
	return true;
}

function isDiscardableEnvironmentAssignment(
	path: NodePath,
	name: string,
): boolean {
	return path.isAssignmentExpression({ operator: '=' }) &&
		t.isIdentifier(path.node.left, { name }) &&
		isReadOnlyEnvironmentLookup(path.node.right) &&
		expressionResultIsDiscarded(
			path as NodePath<t.AssignmentExpression>,
		);
}

function generatedIdentifierUseCount(node: t.Node, name: string): number {
	let count = 0;
	t.traverseFast(node, (child) => {
		if (t.isIdentifier(child, { name })) count++;
	});
	return count;
}

function replaceGeneratedIdentifier(
	node: t.Node,
	name: string,
	replacement: t.Expression,
): t.Node {
	if (t.isIdentifier(node, { name })) {
		return t.cloneNode(replacement, true);
	}
	const clone = t.cloneNode(node, false);
	for (const key of t.VISITOR_KEYS[clone.type] ?? []) {
		const child = (clone as unknown as Record<string, unknown>)[key];
		if (Array.isArray(child)) {
			(clone as unknown as Record<string, unknown>)[key] = child.map((
				element,
			) => t.isNode(element)
				? replaceGeneratedIdentifier(element, name, replacement)
				: element
			);
		} else if (t.isNode(child)) {
			(clone as unknown as Record<string, unknown>)[key] =
				replaceGeneratedIdentifier(child, name, replacement);
		}
	}
	return clone;
}

function substitutionPointPreservesOrder(
	node: t.Expression,
	name: string,
): boolean {
	if (t.isIdentifier(node, { name })) return true;
	if (t.isUnaryExpression(node) && t.isExpression(node.argument)) {
		return substitutionPointPreservesOrder(node.argument, name);
	}
	if (
		t.isAssignmentExpression(node, { operator: '=' }) &&
		t.isIdentifier(node.left) &&
		node.left.name !== name &&
		/^r\d+_\d+$/.test(node.left.name)
	) {
		return substitutionPointPreservesOrder(node.right, name);
	}
	if (t.isArrayExpression(node)) {
		for (const element of node.elements) {
			if (element === null) continue;
			const value = t.isSpreadElement(element)
				? element.argument
				: element;
			if (!t.isExpression(value)) return false;
			if (generatedIdentifierUseCount(value, name) > 0) {
				return substitutionPointPreservesOrder(value, name);
			}
			// Iterating a preceding spread is observable even when its argument
			// is a scalar, so only ordinary scalar elements may be crossed.
			if (
				t.isSpreadElement(element) ||
				!isDuplicableScalarExpression(value)
			) return false;
		}
		return false;
	}
	if (t.isTemplateLiteral(node)) {
		for (const expression of node.expressions) {
			if (!t.isExpression(expression)) return false;
			if (generatedIdentifierUseCount(expression, name) > 0) {
				return substitutionPointPreservesOrder(expression, name);
			}
			if (!isDuplicableScalarExpression(expression)) return false;
		}
		return false;
	}
	if (t.isBinaryExpression(node)) {
		if (!t.isExpression(node.left)) return false;
		if (generatedIdentifierUseCount(node.left, name) > 0) {
			return substitutionPointPreservesOrder(node.left, name);
		}
		return isDuplicableScalarExpression(node.left) &&
			substitutionPointPreservesOrder(node.right, name);
	}
	if (t.isMemberExpression(node)) {
		if (
			t.isExpression(node.object) &&
			generatedIdentifierUseCount(node.object, name) > 0
		) return substitutionPointPreservesOrder(node.object, name);
		return node.computed &&
			t.isExpression(node.object) &&
			isDuplicableScalarExpression(node.object) &&
			t.isExpression(node.property) &&
			substitutionPointPreservesOrder(node.property, name);
	}
	if (t.isCallExpression(node) || t.isNewExpression(node)) {
		const callee = node.callee;
		if (
			t.isExpression(callee) &&
			generatedIdentifierUseCount(callee, name) > 0
		) return substitutionPointPreservesOrder(callee, name);
		if (
			!t.isExpression(callee) ||
			!isDuplicableScalarExpression(callee)
		) return false;
		for (const argument of node.arguments) {
			if (!t.isExpression(argument)) return false;
			if (generatedIdentifierUseCount(argument, name) > 0) {
				return substitutionPointPreservesOrder(argument, name);
			}
			if (!isDuplicableScalarExpression(argument)) return false;
		}
		return false;
	}
	return false;
}

function isImmutableGeneratedScalar(node: t.Expression): boolean {
	return t.isNullLiteral(node) ||
		t.isStringLiteral(node) ||
		t.isNumericLiteral(node) ||
		t.isBooleanLiteral(node) ||
		t.isBigIntLiteral(node) ||
		(t.isUnaryExpression(node) &&
			t.isExpression(node.argument) &&
			isImmutableGeneratedScalar(node.argument));
}

function sequenceOperandCanBeCrossed(node: t.Expression): boolean {
	return isDuplicableScalarExpression(node) ||
		(t.isAssignmentExpression(node, { operator: '=' }) &&
			t.isIdentifier(node.left) &&
			/^r\d+_\d+$/.test(node.left.name) &&
			t.isExpression(node.right) &&
			isImmutableGeneratedScalar(node.right));
}

function simplifyGeneratedAssignmentsInSequence(
	path: NodePath<t.SequenceExpression>,
): number {
	const expressions = path.node.expressions;
	let simplified = 0;
	for (let index = expressions.length - 2; index >= 0; index--) {
		const assignment = expressions[index];
		if (
			!assignment ||
			!t.isAssignmentExpression(assignment, { operator: '=' }) ||
			!t.isIdentifier(assignment.left) ||
			!/^r\d+_\d+$/.test(assignment.left.name) ||
			!t.isExpression(assignment.right)
		) continue;
		const name = assignment.left.name;
		const binding = path.scope.getBinding(name);
		if (
			!binding?.path.isVariableDeclarator() ||
			binding.path.node.init != null ||
			binding.referencePaths.length !== 1 ||
			binding.constantViolations.length !== 1 ||
			binding.constantViolations[0]?.node !== assignment
		) continue;

		const later = expressions.slice(index + 1);
		if (
			later.reduce(
				(count, expression) =>
					count + generatedIdentifierUseCount(expression, name),
				0,
			) !== 1
		) continue;
		const targetOffset = later.findIndex((expression) =>
			generatedIdentifierUseCount(expression, name) > 0
		);
		if (targetOffset < 0) continue;
		const targetIndex = index + 1 + targetOffset;
		if (
			!expressions.slice(index + 1, targetIndex).every(
				sequenceOperandCanBeCrossed,
			) ||
			!substitutionPointPreservesOrder(
				expressions[targetIndex]!,
				name,
			)
		) continue;

		expressions[targetIndex] = replaceGeneratedIdentifier(
			expressions[targetIndex]!,
			name,
			assignment.right,
		) as t.Expression;
		expressions.splice(index, 1);
		const declaration = binding.path.parentPath;
		binding.path.remove();
		if (
			declaration?.isVariableDeclaration() &&
			declaration.node.declarations.length === 0
		) declaration.remove();
		simplified++;
	}
	if (expressions.length === 1) {
		path.replaceWith(expressions[0]!);
	}
	return simplified;
}

/**
 * Inline generated assignments after composition has resolved their RHS.
 * Restrict effectful values to one later sequence use, and only move them to
 * the exact evaluation point when no unrelated effect is crossed.
 */
export function simplifyGeneratedSequenceAssignments(file: t.File): number {
	let simplified = 0;
	let sequenceChanges: number;
	do {
		traverse.cache.clear();
		traverse(file, {
			Program(path) {
				path.scope.crawl();
				path.stop();
			},
		});
		sequenceChanges = 0;
		traverse(file, {
			SequenceExpression: {
				enter(path) {
					sequenceChanges += inlineSequenceMemberCalls(path);
					sequenceChanges += inlineSequenceArrayConstruction(path);
				},
				exit(path) {
					sequenceChanges += simplifyGeneratedAssignmentsInSequence(
						path,
					);
				},
			},
		});
		simplified += sequenceChanges;
	} while (sequenceChanges > 0);
	traverse.cache.clear();

	const immutableSplitBindings: NodePath<t.VariableDeclarator>[] = [];
	traverse(file, {
		VariableDeclarator(path) {
			if (
				path.node.init != null ||
				!path.get('id').isIdentifier() ||
				!/^r\d+_\d+$/.test((path.node.id as t.Identifier).name)
			) return;
			const name = (path.node.id as t.Identifier).name;
			const binding = path.scope.getBinding(name);
			const [violation] = binding?.constantViolations ?? [];
			if (
				!binding || binding.path.node !== path.node ||
				binding.constantViolations.length !== 1 ||
				!violation?.isAssignmentExpression({ operator: '=' }) ||
				!t.isIdentifier(violation.node.left, { name }) ||
				!t.isExpression(violation.node.right) ||
				!isImmutableGeneratedScalar(violation.node.right)
			) return;
			immutableSplitBindings.push(path);
		},
	});
	for (const path of immutableSplitBindings) {
		if (!path.node || !t.isIdentifier(path.node.id)) continue;
		const binding = path.scope.getBinding(path.node.id.name);
		const assignment = binding?.constantViolations[0];
		if (
			!binding ||
			!assignment?.isAssignmentExpression({ operator: '=' }) ||
			!t.isExpression(assignment.node.right)
		) continue;
		const declarationNode = path.node;
		// Removing an earlier assignment can rebuild its enclosing sequence and
		// invalidate Babel's cached reference paths for later bindings. Traverse
		// the current tree for each split binding rather than retaining those paths.
		traverse(file, {
			ReferencedIdentifier(reference) {
				if (
					!reference.isIdentifier() ||
					reference.node.name !==
						(declarationNode.id as t.Identifier).name ||
					reference.scope.getBinding(reference.node.name)?.path
							.node !==
						declarationNode
				) return;
				reference.replaceWith(
					t.cloneNode(assignment.node.right as t.Expression, true),
				);
			},
		});
		if (
			!removeDiscardedExpression(
				assignment as NodePath<t.AssignmentExpression>,
			)
		) assignment.replaceWith(t.cloneNode(assignment.node.right, true));
		const declaration = path.parentPath;
		path.remove();
		if (
			declaration?.isVariableDeclaration() &&
			declaration.node.declarations.length === 0
		) declaration.remove();
		simplified++;
	}
	return simplified;
}

function liftGeneratedCallProtocols(file: t.File): void {
	simplifyGeneratedSequenceAssignments(file);
	let helpersLifted: number;
	do {
		helpersLifted = liftHermesApplyCalls(file) +
			liftHermesTaggedTemplateCalls(file) +
			liftHermesConcatCalls(file);
		if (helpersLifted > 0) {
			simplifyGeneratedSequenceAssignments(file);
		}
	} while (helpersLifted > 0);
}

/**
 * Drop environment handles nothing reads any more.
 *
 * Resolution is what kills them: while `%expectEnvironment(handle)[slot]` uses
 * exist the handle has readers, and once every one of those is rewritten to an
 * `_env_*` name the declaration is left behind with none. Recursive CFG
 * emission may place a split handle assignment inside a short-circuit sequence,
 * so discarded expression positions are removed as well as whole statements.
 *
 * Restricted to the read-only lookups. A `%Create*Environment` allocates, and
 * even with no readers left that is not obviously unobservable, so those are
 * left alone.
 */
export function removeDeadEnvironmentLookupHandles(file: t.File): number {
	traverse(file, {
		Program(path) {
			path.scope.crawl();
			path.stop();
		},
	});

	const dead: NodePath<t.VariableDeclarator>[] = [];
	const deadSplitAssignments: NodePath<t.AssignmentExpression>[] = [];
	const queuedAssignments = new Set<t.AssignmentExpression>();
	traverse(file, {
		VariableDeclarator(path) {
			if (!t.isIdentifier(path.node.id)) return;
			const idName = path.node.id.name;
			if (!/^r\d+_/.test(idName)) return;
			const binding = path.scope.getBinding(idName);
			if (
				!binding || binding.path.node !== path.node ||
				binding.referencePaths.length > 0
			) return;
			if (isReadOnlyEnvironmentLookup(path.node.init)) {
				if (binding.constantViolations.length > 0) return;
				dead.push(path);
				return;
			}
			if (path.node.init != null) return;

			for (const violation of binding.constantViolations) {
				if (!isDiscardableEnvironmentAssignment(violation, idName)) {
					continue;
				}
				const assignment = violation as NodePath<
					t.AssignmentExpression
				>;
				if (queuedAssignments.has(assignment.node)) continue;
				queuedAssignments.add(assignment.node);
				deadSplitAssignments.push(assignment);
			}
			if (
				binding.constantViolations.length > 0 &&
				binding.constantViolations.every((violation) =>
					isDiscardableEnvironmentAssignment(violation, idName)
				)
			) dead.push(path);
		},
	});

	let removed = 0;
	for (const assignment of deadSplitAssignments.toReversed()) {
		if (removeDiscardedExpression(assignment)) removed++;
	}
	for (const path of dead) {
		const declaration = path.parentPath;
		path.remove();
		if (
			declaration?.isVariableDeclaration() &&
			declaration.node.declarations.length === 0
		) declaration.remove();
		removed++;
	}

	const discardedLookups: NodePath<t.CallExpression>[] = [];
	traverse(file, {
		CallExpression(path) {
			if (!isReadOnlyEnvironmentLookup(path.node)) return;
			if (
				path.parentPath?.isAssignmentExpression() ||
				path.parentPath?.isVariableDeclarator()
			) return;
			if (
				expressionResultIsDiscarded(
					path as NodePath<t.CallExpression>,
				)
			) discardedLookups.push(path);
		},
	});
	for (const lookup of discardedLookups.toReversed()) {
		if (removeDiscardedExpression(lookup)) removed++;
	}
	return removed;
}

function staticObjectRestKeyName(
	key: t.Expression,
	computed: boolean,
): string | null {
	if (t.isStringLiteral(key) || t.isNumericLiteral(key)) {
		return String(key.value);
	}
	if (!computed && t.isIdentifier(key)) return key.name;
	return null;
}

function staticObjectRestExclusionKeys(
	excluded: t.Expression,
): Map<string, { key: t.Expression; computed: boolean }> | null {
	if (!t.isObjectExpression(excluded)) return null;
	const keys = new Map<string, { key: t.Expression; computed: boolean }>();
	let hasNullPrototype = false;
	for (const property of excluded.properties) {
		if (
			t.isObjectProperty(property) &&
			!property.computed &&
			(t.isIdentifier(property.key, { name: '__proto__' }) ||
				t.isStringLiteral(property.key, { value: '__proto__' })) &&
			t.isNullLiteral(property.value)
		) {
			hasNullPrototype = true;
			continue;
		}
		if (
			!t.isObjectProperty(property) ||
			!t.isExpression(property.key) ||
			!t.isNumericLiteral(property.value, { value: 0 })
		) return null;
		const name = staticObjectRestKeyName(property.key, property.computed);
		if (name == null || keys.has(name)) return null;
		keys.set(name, { key: property.key, computed: property.computed });
	}
	return hasNullPrototype && keys.size > 0 ? keys : null;
}

function embeddedObjectRestCopy(
	node: t.Node,
	sourceName: string,
): {
	call: t.CallExpression;
	keys: Map<string, { key: t.Expression; computed: boolean }>;
} | null {
	if (!t.isCallExpression(node)) return null;
	const callee = node.callee;
	if (
		!t.isMemberExpression(callee, { computed: false }) ||
		!t.isIdentifier(callee.object, { name: 'HermesInternal' }) ||
		!t.isIdentifier(callee.property, { name: 'copyDataProperties' }) ||
		node.arguments.length !== 3
	) return null;
	const [target, source, excluded] = node.arguments;
	if (!t.isObjectExpression(target) || target.properties.length !== 0) {
		return null;
	}
	if (!t.isIdentifier(source, { name: sourceName })) return null;
	if (!t.isExpression(excluded)) return null;
	const keys = staticObjectRestExclusionKeys(excluded);
	return keys ? { call: node, keys } : null;
}

function memberKeyName(member: t.MemberExpression): string | null {
	if (member.computed) {
		if (
			t.isStringLiteral(member.property) ||
			t.isNumericLiteral(member.property)
		) {
			return String(member.property.value);
		}
		return null;
	}
	return t.isIdentifier(member.property) ? member.property.name : null;
}

function objectRestMemberBindingTarget(
	ref: NodePath<t.MemberExpression>,
): { id: t.Identifier; remove: NodePath } | null {
	const parent = ref.parentPath;
	if (parent?.isVariableDeclarator() && parent.node.init === ref.node) {
		const id = parent.get('id');
		if (!id.isIdentifier()) return null;
		const declaration = parent.parentPath;
		if (
			!declaration?.isVariableDeclaration() ||
			declaration.node.declarations.length !== 1
		) return null;
		return { id: t.cloneNode(id.node), remove: declaration };
	}
	if (parent?.isAssignmentExpression({ operator: '=' })) {
		if (parent.node.right !== ref.node) return null;
		const left = parent.get('left');
		if (!left.isIdentifier()) return null;
		const existing = left.scope.getBinding(left.node.name);
		if (existing && existing.kind !== 'var') return null;
		const statement = parent.parentPath;
		if (!statement?.isExpressionStatement()) return null;
		return { id: t.cloneNode(left.node), remove: statement };
	}
	return null;
}

function objectRestDefaultedMemberBindingTarget(
	scope: Scope,
	source: t.Identifier,
	undefinedAliases: ReadonlySet<string>,
): { id: t.Identifier; value: t.AssignmentPattern; remove: NodePath } | null {
	const binding = scope.getBinding(source.name);
	if (!binding || !binding.constant || binding.referencePaths.length === 0) {
		return null;
	}

	let defaultPath: NodePath<t.ConditionalExpression> | null = null;
	for (const reference of binding.referencePaths) {
		let current: NodePath | null = reference;
		while (current && !current.isFunction()) {
			if (
				current.isConditionalExpression() &&
				destructuringSourceDefault(
					current.node,
					source.name,
					undefinedAliases,
				)
			) {
				break;
			}
			current = current.parentPath;
		}
		if (!current?.isConditionalExpression()) return null;
		if (defaultPath && defaultPath.node !== current.node) return null;
		defaultPath = current;
	}
	if (!defaultPath) return null;
	const sourceDefault = destructuringSourceDefault(
		defaultPath.node,
		source.name,
		undefinedAliases,
	);
	if (!sourceDefault) return null;

	let id: t.Identifier;
	let remove: NodePath | undefined;
	const parent = defaultPath.parentPath;
	if (
		parent?.isVariableDeclarator() && parent.node.init === defaultPath.node
	) {
		const declaratorId = parent.get('id');
		if (!declaratorId.isIdentifier()) return null;
		const declaration = parent.parentPath;
		if (
			!declaration?.isVariableDeclaration() ||
			declaration.node.declarations.length !== 1
		) return null;
		id = t.cloneNode(declaratorId.node);
		remove = declaration;
	} else if (
		parent?.isAssignmentExpression({ operator: '=' }) &&
		parent.node.right === defaultPath.node
	) {
		const left = parent.get('left');
		if (!left.isIdentifier()) return null;
		const existing = left.scope.getBinding(left.node.name);
		if (existing && existing.kind !== 'var') return null;
		const statement = parent.parentPath;
		if (!statement?.isExpressionStatement()) return null;
		id = t.cloneNode(left.node);
		remove = statement;
	} else {
		return null;
	}

	return {
		id,
		value: t.assignmentPattern(
			t.cloneNode(id),
			t.cloneNode(sourceDefault.defaultValue, true),
		),
		remove: remove!,
	};
}

function promoteDefaultedPatternBindingTargets(
	value: t.Expression | t.PatternLike,
	scope: Scope,
	undefinedAliases: ReadonlySet<string>,
	removals: Set<NodePath>,
): t.Expression | t.PatternLike {
	if (t.isIdentifier(value)) {
		const defaulted = objectRestDefaultedMemberBindingTarget(
			scope,
			value,
			undefinedAliases,
		);
		if (!defaulted) return value;
		removals.add(defaulted.remove);
		return defaulted.value;
	}
	if (t.isAssignmentPattern(value)) {
		if (t.isIdentifier(value.left)) return value;
		const left = promoteDefaultedPatternBindingTargets(
			value.left,
			scope,
			undefinedAliases,
			removals,
		);
		if (
			!t.isIdentifier(left) &&
			!t.isPatternLike(left) &&
			!t.isMemberExpression(left)
		) return value;
		return t.assignmentPattern(
			left as Parameters<typeof t.assignmentPattern>[0],
			value.right,
		);
	}
	if (t.isObjectPattern(value)) {
		for (const property of value.properties) {
			if (t.isRestElement(property)) continue;
			if (!t.isObjectProperty(property)) continue;
			property.value = promoteDefaultedPatternBindingTargets(
				property.value,
				scope,
				undefinedAliases,
				removals,
			) as t.ObjectProperty['value'];
		}
		return value;
	}
	if (t.isArrayPattern(value)) {
		value.elements = value.elements.map((element) =>
			element == null ? element : promoteDefaultedPatternBindingTargets(
				element,
				scope,
				undefinedAliases,
				removals,
			) as t.ArrayPattern['elements'][number]
		);
		return value;
	}
	return value;
}

function sourceObjectPatternCapture(
	ref: NodePath<t.Identifier>,
): { pattern: t.ObjectPattern; remove: NodePath } | null {
	const parent = ref.parentPath;
	if (parent?.isAssignmentExpression({ operator: '=' })) {
		if (parent.node.right !== ref.node) return null;
		const left = parent.get('left');
		if (!left.isObjectPattern()) return null;
		const statement = parent.parentPath;
		if (!statement?.isExpressionStatement()) return null;
		return { pattern: left.node, remove: statement };
	}
	if (parent?.isVariableDeclarator() && parent.node.init === ref.node) {
		const id = parent.get('id');
		if (!id.isObjectPattern()) return null;
		const declaration = parent.parentPath;
		if (
			!declaration?.isVariableDeclaration() ||
			declaration.node.declarations.length !== 1
		) return null;
		return { pattern: id.node, remove: declaration };
	}
	return null;
}

function patternBindingReference(
	value: t.Expression | t.PatternLike,
): t.Identifier | null {
	if (t.isIdentifier(value)) return value;
	if (t.isAssignmentPattern(value) && t.isIdentifier(value.left)) {
		return value.left;
	}
	return null;
}

function objectRestPatternProperties(
	capture: { pattern: t.ObjectPattern; remove: NodePath },
	keys: ReadonlyMap<string, { key: t.Expression; computed: boolean }>,
): Map<string, { property: t.ObjectProperty; remove: NodePath }> | null {
	const result = new Map<
		string,
		{ property: t.ObjectProperty; remove: NodePath }
	>();
	for (const property of capture.pattern.properties) {
		if (!t.isObjectProperty(property)) return null;
		if (!t.isExpression(property.key)) return null;
		const name = staticObjectRestKeyName(property.key, property.computed);
		if (name == null || !keys.has(name) || result.has(name)) return null;
		result.set(name, {
			property,
			remove: capture.remove,
		});
	}
	return result;
}

export function recoverEmbeddedObjectRestForFunction(
	path: NodePath<t.Function>,
): boolean {
	if (!t.isBlockStatement(path.node.body)) return false;
	let changed = false;
	const undefinedAliases = destructuringUndefinedAliases(path.node.body);
	for (const paramPath of path.get('params')) {
		if (!paramPath.isIdentifier()) continue;
		const sourceName = paramPath.node.name;
		const match = /^_param_(\d+)_(\d+)_$/.exec(sourceName);
		if (!match) continue;
		const binding = path.scope.getBinding(sourceName);
		if (!binding) continue;

		const restCopies: {
			path: NodePath<t.CallExpression>;
			keys: Map<string, { key: t.Expression; computed: boolean }>;
		}[] = [];
		const memberRefs = new Map<string, NodePath<t.MemberExpression>[]>();
		const patternCaptures: {
			pattern: t.ObjectPattern;
			remove: NodePath;
		}[] = [];
		let directEscape = false;
		for (const ref of binding.referencePaths) {
			const parent = ref.parentPath;
			if (
				parent?.isMemberExpression() && parent.node.object === ref.node
			) {
				const name = memberKeyName(parent.node);

				if (name == null) {
					directEscape = true;
					break;
				}
				const refs = memberRefs.get(name) ?? [];
				refs.push(parent as NodePath<t.MemberExpression>);
				memberRefs.set(name, refs);
				continue;
			}
			const copy = parent?.isCallExpression()
				? embeddedObjectRestCopy(parent.node, sourceName)
				: null;
			if (copy) {
				restCopies.push({
					path: parent as NodePath<t.CallExpression>,
					keys: copy.keys,
				});
				continue;
			}
			const patternCapture = ref.isIdentifier()
				? sourceObjectPatternCapture(ref)
				: null;
			if (patternCapture) {
				patternCaptures.push(patternCapture);
				continue;
			}
			directEscape = true;
			break;
		}
		if (directEscape || restCopies.length !== 1 || !restCopies[0]) continue;
		const { path: restCopyPath, keys } = restCopies[0];

		const removals = new Set<NodePath>();
		const properties: t.ObjectPattern['properties'] = [];
		let invalidBindingTarget = false;
		const patternProperties = new Map<
			string,
			{ property: t.ObjectProperty; remove: NodePath }
		>();
		for (const capture of patternCaptures) {
			const captured = objectRestPatternProperties(capture, keys);
			if (!captured) {
				invalidBindingTarget = true;
				break;
			}
			for (const [name, property] of captured) {
				if (patternProperties.has(name)) {
					invalidBindingTarget = true;
					break;
				}
				patternProperties.set(name, property);
			}
			if (invalidBindingTarget) break;
		}
		if (invalidBindingTarget) continue;
		for (const [name, key] of keys) {
			const refs = memberRefs.get(name) ?? [];
			const patternProperty = patternProperties.get(name);
			let bindingTarget:
				| {
					id: t.Identifier;
					remove: NodePath;
					ref: NodePath<t.MemberExpression>;
				}
				| null = null;
			let conflictingTarget = false;
			for (const ref of refs) {
				const target = objectRestMemberBindingTarget(ref);
				if (!target) continue;
				if (bindingTarget) {
					conflictingTarget = true;
					break;
				}
				bindingTarget = { ...target, ref };
			}
			if (conflictingTarget) {
				invalidBindingTarget = true;
				break;
			}
			let value: t.Expression | t.PatternLike;
			let refReplacement: t.Expression | null = null;
			if (patternProperty) {
				const cloned = t.cloneNode(
					patternProperty.property.value,
					true,
				);
				if (!t.isExpression(cloned) && !t.isPatternLike(cloned)) {
					invalidBindingTarget = true;
					break;
				}
				value = refs.length === 0
					? promoteDefaultedPatternBindingTargets(
						cloned,
						path.scope,
						undefinedAliases,
						removals,
					)
					: cloned;
				const reference = patternBindingReference(value);
				if (!reference && refs.length > 0) {
					invalidBindingTarget = true;
					break;
				}
				if (reference) refReplacement = reference;
			} else {
				const defaultedBinding = bindingTarget && refs.length === 1
					? objectRestDefaultedMemberBindingTarget(
						bindingTarget.ref.scope,
						bindingTarget.id,
						undefinedAliases,
					)
					: null;
				if (defaultedBinding) {
					value = defaultedBinding.value;
					refReplacement = defaultedBinding.id;
					removals.add(defaultedBinding.remove);
				} else {
					const hint = t.isValidIdentifier(name, false)
						? name
						: t.toIdentifier(name);
					value = bindingTarget?.id ??
						path.scope.generateUidIdentifier(hint);
					refReplacement = t.isExpression(value) ? value : null;
				}
			}
			if (!refReplacement && refs.length > 0) {
				invalidBindingTarget = true;
				break;
			}
			for (const ref of refs) {
				if (ref === bindingTarget?.ref) continue;
				ref.replaceWith(t.cloneNode(refReplacement!, true));
			}
			if (bindingTarget) removals.add(bindingTarget.remove);
			if (patternProperty) removals.add(patternProperty.remove);
			const property = t.objectProperty(
				t.cloneNode(key.key, true),
				value,
				key.computed,
			);
			if (
				!property.computed && t.isIdentifier(property.key) &&
				t.isIdentifier(property.value, { name: property.key.name })
			) property.shorthand = true;
			properties.push(property);
		}
		if (invalidBindingTarget) continue;
		const restBinding = t.identifier(`_rest_${match[1]}_${match[2]}_`);
		properties.push(t.restElement(restBinding));

		const declarator = restCopyPath.parentPath;
		if (
			declarator?.isVariableDeclarator() &&
			declarator.node.init === restCopyPath.node &&
			t.isIdentifier(declarator.node.id)
		) {
			const aliasName = declarator.node.id.name;
			const aliasBinding = path.scope.getBinding(aliasName);
			if (!aliasBinding) continue;
			for (const ref of aliasBinding.referencePaths) {
				ref.replaceWith(t.cloneNode(restBinding, true));
			}
			const declaration = declarator.parentPath;
			if (
				declaration?.isVariableDeclaration() &&
				declaration.node.declarations.length === 1
			) {
				declaration.remove();
			} else {
				declarator.remove();
			}
		} else {
			restCopyPath.replaceWith(t.cloneNode(restBinding, true));
		}
		for (const removal of removals) {
			removal.remove();
		}
		paramPath.replaceWith(t.objectPattern(properties));
		changed = true;
	}
	if (changed) traverse.cache.clear();
	return changed;
}
export function recoverDirectObjectDefaultAliasesInBody(
	body: t.Statement[],
): number {
	let recovered = 0;
	for (let index = 0; index < body.length - 1; index++) {
		const probeStatement = body[index];
		if (!t.isVariableDeclaration(probeStatement, { kind: 'const' })) {
			continue;
		}
		const probe = singleVariableDeclarator(probeStatement);
		if (
			!probe ||
			!t.isIdentifier(probe.id) ||
			!isRegisterTempName(probe.id.name) ||
			!t.isMemberExpression(probe.init) ||
			!t.isExpression(probe.init.object) ||
			!t.isExpression(probe.init.property)
		) continue;
		const probeName = probe.id.name;

		const targetStatement = body[index + 1];
		if (!t.isVariableDeclaration(targetStatement, { kind: 'var' })) {
			continue;
		}
		const target = singleVariableDeclarator(targetStatement);
		if (
			!target ||
			!t.isIdentifier(target.id) ||
			!target.init ||
			!t.isExpression(target.init)
		) continue;

		const sourceDefault = destructuringSourceDefault(
			target.init,
			probeName,
			destructuringUndefinedAliases(t.blockStatement(body)),
		);
		if (!sourceDefault) continue;
		if (
			body.some((statement, statementIndex) =>
				statementIndex !== index &&
				statementIndex !== index + 1 &&
				identifierOccurrences(statement, probeName) > 0
			)
		) continue;

		const property = t.objectProperty(
			t.cloneNode(probe.init.property, true),
			t.assignmentPattern(
				t.cloneNode(target.id),
				t.cloneNode(sourceDefault.defaultValue, true),
			),
			probe.init.computed,
		);
		if (
			!property.computed &&
			t.isIdentifier(property.key) &&
			t.isAssignmentPattern(property.value) &&
			t.isIdentifier(property.value.left, { name: property.key.name })
		) property.shorthand = true;

		body.splice(
			index,
			2,
			t.variableDeclaration('var', [
				t.variableDeclarator(
					t.objectPattern([property]),
					t.cloneNode(probe.init.object, true),
				),
			]),
		);
		recovered++;
	}
	return recovered;
}

function hasDeclaredGlobalHoists(
	body: t.Statement[],
	names: ReadonlySet<string>,
	beforeIndex: number,
): boolean {
	const found = new Set<string>();
	for (let index = 0; index < beforeIndex; index++) {
		const statement = body[index];
		if (!t.isVariableDeclaration(statement, { kind: 'var' })) continue;
		for (const declaration of statement.declarations) {
			if (
				t.isIdentifier(declaration.id) &&
				declaration.init == null &&
				declaration.extra?.isDeclaredGlobal === true &&
				names.has(declaration.id.name)
			) found.add(declaration.id.name);
		}
	}
	return found.size === names.size;
}

function removeDeclaredGlobalHoists(
	body: t.Statement[],
	names: ReadonlySet<string>,
	beforeIndex: number,
): number {
	let removedStatements = 0;
	for (let index = beforeIndex - 1; index >= 0; index--) {
		const statement = body[index];
		if (!t.isVariableDeclaration(statement, { kind: 'var' })) continue;
		statement.declarations = statement.declarations.filter((declaration) =>
			!(
				t.isIdentifier(declaration.id) &&
				declaration.init == null &&
				declaration.extra?.isDeclaredGlobal === true &&
				names.has(declaration.id.name)
			)
		);
		if (statement.declarations.length === 0) {
			body.splice(index, 1);
			removedStatements++;
		}
	}
	return removedStatements;
}

function localBindingsInBody(body: t.Statement[]): Set<string> {
	const names = new Set<string>();
	for (const statement of body) {
		if (t.isFunctionDeclaration(statement) && statement.id) {
			names.add(statement.id.name);
			continue;
		}
		if (!t.isVariableDeclaration(statement)) continue;
		for (const declaration of statement.declarations) {
			if (declaration.extra?.isDeclaredGlobal === true) continue;
			for (const id of identifiersInPattern(declaration.id)) {
				names.add(id.name);
			}
		}
	}
	return names;
}

export function recoverDeclaredGlobalDestructuringAssignments(
	body: t.Statement[],
	declaredGlobals: Set<string>,
): number {
	const localBindings = localBindingsInBody(body);
	let recovered = 0;
	for (let index = 0; index < body.length; index++) {
		const statement = body[index];
		if (
			!t.isExpressionStatement(statement) ||
			!t.isAssignmentExpression(statement.expression, {
				operator: '=',
			}) ||
			!(
				t.isArrayPattern(statement.expression.left) ||
				t.isObjectPattern(statement.expression.left)
			) ||
			!t.isExpression(statement.expression.right)
		) continue;

		const identifiers = identifiersInPattern(statement.expression.left);
		if (identifiers.length === 0) continue;
		const names = new Set(identifiers.map((identifier) => identifier.name));
		const hasHoists = hasDeclaredGlobalHoists(body, names, index);
		if (
			!hasHoists &&
			[...names].some((name) =>
				!declaredGlobals.has(name) && localBindings.has(name)
			)
		) continue;

		const declarator = t.variableDeclarator(
			t.cloneNode(statement.expression.left, true),
			t.cloneNode(statement.expression.right, true),
		);
		declarator.extra = { isDeclaredGlobal: true };
		const declaration = t.variableDeclaration('var', [declarator]);
		declaration.extra = { ...statement.extra };
		body[index] = declaration;
		if (hasHoists) {
			index -= removeDeclaredGlobalHoists(body, names, index);
		}
		for (const name of names) {
			declaredGlobals.add(name);
			localBindings.add(name);
		}
		recovered++;
	}
	return recovered;
}

/** Canonicalize conditional values after final storage-alias coalescing. */
export function refoldPostAliasConditionalValues(file: t.File): void {
	refoldConditionalValues(file);
	traverse(file, {
		Program(path) {
			foldConditionalValuesInBody(path.node.body);
		},
		Function(path) {
			const body = path.node.body;
			if (t.isBlockStatement(body)) {
				foldConditionalValuesInBody(body.body);
			}
		},
	});
	traverse(file, {
		ExpressionStatement(path) {
			const expression = path.get('expression');
			if (!expression.isBinaryExpression()) return;
			if (
				!['==', '!=', '===', '!=='].includes(
					expression.node.operator,
				) ||
				!(t.isNullLiteral(expression.node.left) ||
					t.isNullLiteral(expression.node.right))
			) return;
			if (expression.isPure()) path.remove();
		},
	});
}

/**
 * Compose-time plans, from the one bytecode pass rather than three more.
 *
 * Everything here used to walk `file.functions` again. Against a cold-store
 * file those walks would page the whole bundle back in, and in a compose worker
 * they were repeated work on top of that, so the scan happens once in
 * `buildBytecodeDerivedPlan` and this only reshapes the result.
 */
export function buildCompositionPlan(
	derived: BytecodeDerivedPlan,
): CompositionPlan {
	const { soleFunctionParents, nonSoleFunctionReferences } = derived;
	const safelyNestedFunctions = new Set<FunctionId>();
	const parentFunctions = new Map<FunctionId, FunctionId>();
	for (const [child, parent] of soleFunctionParents) {
		if (nonSoleFunctionReferences.has(child) || parent == null) continue;
		safelyNestedFunctions.add(child);
		parentFunctions.set(child, parent);
	}
	return {
		soleFunctionParents,
		nonSoleFunctionReferences,
		safelyNestedFunctions,
		parentFunctions,
		funcEnvs: buildEnvironmentGraph(
			derived.environmentCreators,
			derived.functionCount,
			parentFunctions,
			derived.environmentCreationSites,
		),
		environmentCreationSites: derived.environmentCreationSites,
	};
}

/**
 * A store over functions that were all lifted up front.
 *
 * It exists so the eager paths track consumption the same way the lazy one
 * does: a bare `Map` forgets that a deleted function was consumed rather than
 * absent, and composition cannot then tell a consumed function from one it
 * should never rebuild.
 */
class EagerIRFunctionStore implements IRFunctionStore {
	#consumed = new Set<FunctionId>();

	constructor(
		readonly file: HBCFile,
		readonly functions: Map<FunctionId, IRFunction>,
		readonly options: IRFunctionOptions,
	) {}

	has(functionId: FunctionId): boolean {
		return this.functions.has(functionId);
	}

	get(functionId: FunctionId): IRFunction | undefined {
		return this.functions.get(functionId);
	}

	delete(functionId: FunctionId): boolean {
		if (!this.functions.has(functionId)) return false;
		this.#consumed.add(functionId);
		return this.functions.delete(functionId);
	}

	set(functionId: FunctionId, func: IRFunction): void {
		this.#consumed.delete(functionId);
		this.functions.set(functionId, func);
	}

	relift(functionId: FunctionId): IRFunction | undefined {
		if (!this.#consumed.has(functionId)) return;
		return new IRFunction(
			this.file,
			new SSAFunction(
				copyFunctionForSSA(this.file.functions[functionId]),
			),
			this.options,
		);
	}
}

class LazyIRFunctionStore implements IRFunctionStore {
	#consumed = new Set<FunctionId>();
	#cache = new Map<FunctionId, IRFunction>();
	#recursiveSummaries = new Map<FunctionId, RecursiveCFGSummary>();

	constructor(
		readonly file: HBCFile,
		readonly options: IRFunctionOptions,
		readonly retainRecursiveCFGSummaries: boolean,
		readonly cacheLimit = 32,
	) {}

	has(functionId: FunctionId): boolean {
		return functionId >= 0 &&
			functionId < this.file.functions.length &&
			!this.#consumed.has(functionId);
	}

	get(functionId: FunctionId): IRFunction | undefined {
		if (!this.has(functionId)) return;
		const cached = this.#cache.get(functionId);
		if (cached) {
			this.#cache.delete(functionId);
			this.#cache.set(functionId, cached);
			return cached;
		}

		reportProgress(`currently lifting function #${functionId}`);
		const ssa = new SSAFunction(
			copyFunctionForSSA(this.file.functions[functionId]),
		);
		const func = new IRFunction(this.file, ssa, this.options);
		this.#recordRecursiveSummary(func);
		this.#cache.set(functionId, func);
		this.#evict();
		return func;
	}

	relift(functionId: FunctionId): IRFunction | undefined {
		if (!this.#consumed.has(functionId)) return;
		// Deliberately neither un-consumes nor caches: the function has already
		// been placed once, and the rebuilt copy belongs to whichever
		// composition asked for it.
		return new IRFunction(
			this.file,
			new SSAFunction(
				copyFunctionForSSA(this.file.functions[functionId]),
			),
			this.options,
		);
	}

	delete(functionId: FunctionId): boolean {
		if (!this.has(functionId)) return false;
		this.#consumed.add(functionId);
		this.#cache.delete(functionId);
		return true;
	}

	set(functionId: FunctionId, func: IRFunction): void {
		this.#consumed.delete(functionId);
		this.#recordRecursiveSummary(func);
		this.#cache.delete(functionId);
		this.#cache.set(functionId, func);
		this.#evict();
	}

	ensureRecursiveSummaries(): void {
		if (!this.retainRecursiveCFGSummaries) return;
		for (
			let functionId = 0;
			functionId < this.file.functions.length;
			functionId++
		) {
			if (this.#recursiveSummaries.has(functionId)) continue;
			const wasAvailable = this.has(functionId);
			if (!wasAvailable) {
				this.#consumed.delete(functionId);
			}
			const func = this.get(functionId);
			if (!wasAvailable) {
				this.#consumed.add(functionId);
				this.#cache.delete(functionId);
			} else if (func) {
				this.#cache.delete(functionId);
			}
		}
	}

	recursiveSummaries(): RecursiveCFGSummary[] {
		return [...this.#recursiveSummaries.values()]
			.toSorted((left, right) => left.functionId - right.functionId);
	}

	#recordRecursiveSummary(func: IRFunction): void {
		if (
			this.retainRecursiveCFGSummaries &&
			func.recursiveCFGSummary &&
			!this.#recursiveSummaries.has(func.id)
		) {
			this.#recursiveSummaries.set(func.id, func.recursiveCFGSummary);
		}
	}

	#evict(): void {
		const limit = Math.max(1, this.cacheLimit);
		while (this.#cache.size > limit) {
			const oldest = this.#cache.keys().next().value as
				| FunctionId
				| undefined;
			if (oldest == null) break;
			this.#cache.delete(oldest);
		}
	}
}

function composeLiftedFile(
	file: HBCFile,
	functions: IRFunctionStore,
	plan: CompositionPlan,
	root: {
		functionId: FunctionId;
		kind: 'file' | 'function';
		creationEnv?: { envArg: t.Node; callerFuncId: FunctionId };
		globalNames?: ReadonlySet<string>;
		blockedFunctionIds?: ReadonlySet<FunctionId> | undefined;
	} = { functionId: 0, kind: 'file' },
	/**
	 * Filled in as sites are identified. Accumulates across calls, so one
	 * record handed to every composition in a run totals the run.
	 */
	identityDiagnostics: EnvironmentIdentityDiagnostics =
		emptyEnvironmentIdentityDiagnostics(),
) {
	const { safelyNestedFunctions, parentFunctions } = plan;
	// Synthetic ids start at `file.functions.length` for every independent
	// composition unit. They are local identities, not additions to the
	// bytecode-derived plan. Sharing the plan's map across a worker batch made
	// module B reuse module A's synthetic Environment and then either claim it
	// for a second creation site or look up site metadata belonging to the wrong
	// clone. Original environments are immutable after plan construction, so a
	// shallow map copy isolates synthetic additions without rebuilding the graph.
	const funcEnvs = new Map(plan.funcEnvs);

	// For each inlined function, records the env argument from the closure-creation
	// instruction (CreateClosure / CreateGeneratorClosure / CreateGenerator) and the
	// funcId of the function that issued that instruction. Used as a fallback when
	// capturedEnvironment can't resolve GetParentEnvironment because an intermediate
	// function isn't in parentFunctions.
	type ElidedEnvironmentStep =
		| { kind: 'local'; functionId: FunctionId }
		| { kind: 'parent'; depth: number };
	interface FunctionCreationEnvironment {
		envArg: t.Node;
		callerFuncId: FunctionId;
		steps: ElidedEnvironmentStep[];
	}
	const funcCreationEnvArgs = new Map<
		FunctionId,
		FunctionCreationEnvironment
	>();
	if (root.creationEnv) {
		funcCreationEnvArgs.set(root.functionId, {
			...root.creationEnv,
			steps: [],
		});
	}
	const explicitCreateEnvironments = new WeakMap<
		t.CallExpression,
		Environment
	>();
	const environmentByCreationSite = new Map<string, Environment>();
	const primaryEnvironmentSiteByFunction = new Map<FunctionId, string>();
	const explicitEnvironmentIndexBySite = new Map<string, number>();
	/** Site lists for synthetic clones, which the bytecode plan cannot have. */
	const clonedEnvironmentCreationSites = new Map<
		FunctionId,
		readonly EnvironmentCreationSite[]
	>();
	const environmentIdentity = identityDiagnostics;
	const recoveredProtectedEnvironmentAssignments = new WeakSet<
		t.AssignmentExpression
	>();
	let nextSyntheticFunctionId = file.functions.length;
	const reusableFunctionExpressions = new Map<
		FunctionId,
		t.FunctionExpression
	>();
	const reusableFunctionExpressionLimit = 64;

	function rememberReusableFunctionExpression(
		functionId: FunctionId | null | undefined,
		funcExpr: t.FunctionExpression,
	) {
		if (functionId == null) return;
		reusableFunctionExpressions.delete(functionId);
		reusableFunctionExpressions.set(
			functionId,
			t.cloneNode(funcExpr, true),
		);
		while (
			reusableFunctionExpressions.size >
				reusableFunctionExpressionLimit
		) {
			const oldest = reusableFunctionExpressions.keys().next()
				.value as FunctionId | undefined;
			if (oldest == null) break;
			reusableFunctionExpressions.delete(oldest);
		}
	}

	function reusableFunctionExpression(functionId: FunctionId) {
		const funcExpr = reusableFunctionExpressions.get(functionId);
		if (!funcExpr) return;
		reusableFunctionExpressions.delete(functionId);
		reusableFunctionExpressions.set(functionId, funcExpr);
		return funcExpr;
	}

	const rootFunction = functions.get(root.functionId);
	assert(rootFunction);
	functions.delete(root.functionId);
	const fileBody = rootFunction!.blocks.get(0)!;
	// Composition takes the entry block as the whole file, which is only sound
	// once the root has been reduced to one block. When it has not, every other
	// block is code that would silently vanish from the output -- on
	// `v99/destructuring-init` that was 11 of 12 blocks, and the result still
	// passed generated-output validation because the intrinsics it would have
	// reported were in the part that disappeared. Losing the program quietly is
	// worse than not producing one.
	// Not in the analysis-only modes: `--cfg-recursive-ast` and friends disable
	// materialization on purpose, so an unstructured root is the state they
	// exist to inspect rather than a lost program.
	const materializes =
		(rootFunction!.options.cfgReducer?.materialize ?? true) !== false;
	if (root.kind === 'file' && materializes && rootFunction!.blocks.size > 1) {
		throw new LiftError(
			`Cannot compose unstructured root function #${root.functionId}: ` +
				`${rootFunction!.blocks.size} blocks remain after reduction`,
			{ functionId: root.functionId },
		);
	}
	const rootExpression = root.kind === 'function'
		? rootFunction!.tryGetFunctionExpr()
		: undefined;
	if (root.kind === 'function' && !rootExpression) {
		throw new LiftError(
			`Cannot compose unstructured Metro factory #${root.functionId}`,
		);
	}
	const wrapped = rootExpression
		? t.file(t.program([t.expressionStatement(rootExpression)]))
		: t.file(t.program(<t.Statement[]> fileBody.body));

	function isBlockedFunctionId(functionId: FunctionId | null | undefined) {
		return functionId != null && root.blockedFunctionIds?.has(functionId);
	}

	function popNestedFunction(functionId?: number) {
		if (functionId == null) return;
		if (isBlockedFunctionId(functionId)) return;
		if (!safelyNestedFunctions.has(functionId)) return;
		if (!functions.has(functionId)) return;
		const func = functions.get(functionId);
		functions.delete(functionId);

		return func;
	}

	function inlineNestedFunctionRef(funcRef: t.Node) {
		return popNestedFunction(extractFunctionRef(funcRef));
	}

	function containsFunctionRef(
		root: t.Node,
		functionId: FunctionId,
	): boolean {
		let found = false;
		t.traverseFast(root, (node) => {
			if (found) return t.traverseFast.skip;
			if (
				t.isCallExpression(node) &&
				extractFunctionRef(node) === functionId
			) {
				found = true;
				return t.traverseFast.skip;
			}
		});
		return found;
	}

	function retargetParentFunctionId(
		root: t.Node,
		from: FunctionId,
		to: FunctionId,
	) {
		t.traverseFast(root, (node) => {
			const extra = node.extra as LiftedExtra | undefined;
			if (extra?.parentFunctionId === from) {
				node.extra = { ...extra, parentFunctionId: to };
			}
		});
	}

	function cloneNestedFunctionRef(
		functionId: FunctionId | null | undefined,
		envArg: t.Node | undefined,
		callerFuncId: FunctionId | null | undefined,
		activeFunctionIds: Set<FunctionId>,
		allowGeneratorBody = false,
	) {
		if (functionId == null || isBlockedFunctionId(functionId)) return;
		if (activeFunctionIds.has(functionId)) return;
		let funcExpr = reusableFunctionExpression(functionId);
		if (!funcExpr) {
			// The remembered expression can be evicted -- the cache is bounded --
			// and consumption is irreversible, so without the rebuild the raw
			// `%CreateClosure` intrinsic reaches the output.
			const irFunc = functions.get(functionId) ??
				functions.relift(functionId);
			if (!irFunc || irFunc.isAsync) return;
			if (!allowGeneratorBody) {
				if (irFunc.analyseGeneratorClosure()) return;
				if (irFunc.analyseAsyncGeneratorClosure()) return;
				if (analyseLoweredGeneratorClosure(irFunc) != null) return;
			}

			funcExpr = irFunc.tryGetFunctionExpr();
			if (!funcExpr) return;
		}

		const replacement = t.cloneNode(funcExpr, true);
		const syntheticFunctionId = nextSyntheticFunctionId++;
		recordFunctionCreationEnv(
			syntheticFunctionId,
			envArg,
			callerFuncId,
		);
		retargetParentFunctionId(
			replacement,
			functionId,
			syntheticFunctionId,
		);
		cloneEnvironmentCreationSites(functionId, syntheticFunctionId);
		inheritParentFunction(functionId, syntheticFunctionId);
		if (containsFunctionRef(replacement, functionId) && !replacement.id) {
			replacement.id = t.identifier(`_func_${functionId}`);
		}
		inlineNestedClosuresInFunction(
			replacement,
			new Set([...activeFunctionIds, functionId]),
			true,
		);
		normalizeDuplicateRegisterDeclarations(replacement);
		return replacement;
	}

	function isPlainCloneableFunctionRef(
		functionId: FunctionId | null | undefined,
	): boolean {
		if (functionId == null || isBlockedFunctionId(functionId)) return false;
		const irFunc = functions.get(functionId);
		if (!irFunc || irFunc.isAsync) return false;
		if (irFunc.analyseGeneratorClosure()) return false;
		if (irFunc.analyseAsyncGeneratorClosure()) return false;
		if (analyseLoweredGeneratorClosure(irFunc) != null) return false;
		if (irFunc.referencedFunctionIds.size !== 0) return false;
		return !!irFunc.tryGetFunctionExpr();
	}

	function functionForGeneratorClosureAnalysis(
		generatorAnalysis: ReturnType<IRFunction['analyseGeneratorClosure']>,
		requireSafelyNested: boolean,
		wrapperFunc?: IRFunction,
		cloneResult = false,
	) {
		if (generatorAnalysis == null) return;
		if (
			'functionId' in generatorAnalysis &&
			isBlockedFunctionId(generatorAnalysis.functionId)
		) return;

		if ('skipInitialYieldUndefined' in generatorAnalysis) {
			if (
				requireSafelyNested &&
				!generatorAnalysis.inlineThroughWrapper &&
				!safelyNestedFunctions.has(generatorAnalysis.functionId)
			) return;
			// A bottom-up composition unit may already have consumed the body even
			// though its CreateGenerator wrapper is still being composed. Rebuild
			// that body here as well as on explicit clone paths; otherwise the late
			// raw-intrinsic sweep can only produce `function* (...) {}()` followed
			// by the wrapper's discarded `.next()`, losing the wrapper/body
			// invocation boundary.
			const genIRFunc = functions.get(generatorAnalysis.functionId) ??
				functions.relift(generatorAnalysis.functionId);
			if (genIRFunc) {
				applyLoweredGeneratorWrapperSlotAliases(genIRFunc);
			}
			const source = genIRFunc?.tryGetFunctionExpr();
			if (!source) return;
			const genFunc = cloneResult ? t.cloneNode(source, true) : source;
			normalizeDuplicateRegisterDeclarations(genFunc);
			if (generatorAnalysis.inlineThroughWrapper && wrapperFunc) {
				genFunc.params = mergeRecoveredGeneratorWrapperParams(
					genFunc.params,
					wrapperFunc.params,
					genFunc,
				);
			}
			if (generatorAnalysis.skipInitialYieldUndefined) {
				hoistPrimedGeneratorArgumentsParams(genFunc);
				hoistPrimedGeneratorObjectParams(genFunc);
				hoistInitialIteratorDestructuredFunctionParams(genFunc);
			}
			hoistDestructuredFunctionParams(genFunc);
			removeRedundantIteratorParamExpansion(genFunc);
			if (
				generatorAnalysis.skipInitialYieldUndefined &&
				!removeInitialYieldUndefined(genFunc)
			) return;
			if (
				generatorAnalysis.inlineThroughWrapper &&
				wrapperFunc
			) {
				genFunc.params = mergeRecoveredGeneratorWrapperParams(
					genFunc.params,
					wrapperFunc.params,
					genFunc,
				);
			}
			while (cleanupLocalPNameForInLoops(genFunc.body.body)) {
				// Recover nested iterator loops to a fixed point.
			}
			if (!cloneResult && genIRFunc) {
				adoptRecoveredFunctionParameters(
					genIRFunc.parameterPlan,
					genIRFunc.id,
					genFunc.params,
				);
				genIRFunc.params = genFunc.params.map((param) =>
					t.cloneNode(param, true)
				);
			}
			if (!cloneResult) functions.delete(generatorAnalysis.functionId);
			return genFunc;
		}

		if ('functionId' in generatorAnalysis) {
			const genIRFunc = cloneResult
				? functions.get(generatorAnalysis.functionId) ??
					functions.relift(generatorAnalysis.functionId)
				: requireSafelyNested
				? popNestedFunction(generatorAnalysis.functionId)
				: functions.get(generatorAnalysis.functionId);
			if (!genIRFunc) return;
			const directAnalysis = genIRFunc.analyseGeneratorClosure();
			const source = genIRFunc.tryGetFunctionExpr() ??
				(directAnalysis != null &&
						typeof directAnalysis !== 'number' &&
						!('functionId' in directAnalysis)
					? directAnalysis
					: undefined);
			if (!source) return;
			const genFunc = cloneResult ? t.cloneNode(source, true) : source;
			normalizeDuplicateRegisterDeclarations(genFunc);
			while (cleanupLocalPNameForInLoops(genFunc.body.body)) {
				// Recover nested iterator loops to a fixed point.
			}
			if (!cloneResult && !requireSafelyNested) {
				functions.delete(generatorAnalysis.functionId);
			}
			return genFunc;
		}

		return cloneResult
			? t.cloneNode(generatorAnalysis, true)
			: generatorAnalysis;
	}

	function functionIdFromGeneratorAnalysis(
		generatorAnalysis: ReturnType<IRFunction['analyseGeneratorClosure']>,
	) {
		return typeof generatorAnalysis === 'number'
			? generatorAnalysis
			: (generatorAnalysis != null && 'functionId' in generatorAnalysis
				? generatorAnalysis.functionId
				: null);
	}

	function environmentStepsForCapture(
		capture: ElidedWrapperEnvironmentCapture,
		wrapperFunctionId: FunctionId,
	): ElidedEnvironmentStep[] {
		return capture.kind === 'local'
			? [{ kind: 'local', functionId: wrapperFunctionId }]
			: capture.depth === 0
			? []
			: [{ kind: 'parent', depth: capture.depth }];
	}

	function environmentStepsForGeneratorAnalysis(
		generatorAnalysis: ReturnType<IRFunction['analyseGeneratorClosure']>,
		wrapperFunctionId: FunctionId | null | undefined,
	): ElidedEnvironmentStep[] {
		if (
			wrapperFunctionId == null || generatorAnalysis == null ||
			!('functionId' in generatorAnalysis)
		) return [];
		return environmentStepsForCapture(
			generatorAnalysis.environmentCapture,
			wrapperFunctionId,
		);
	}

	/**
	 * Rebuild a generator closure after its consumable IR was already used by a
	 * bottom-up composition unit or its reusable expression was evicted.
	 *
	 * A generator wrapper cannot go through `cloneNestedFunctionRef`: cloning the
	 * wrapper would preserve the `%CreateGenerator` protocol instead of producing
	 * the `function*` represented by it. Re-run the wrapper analysis, clone the
	 * resolved generator body, and give that clone its own creation-site identity
	 * so environment resolution remains independent for repeated closures.
	 */
	function cloneGeneratorClosureRef(
		closureFuncId: FunctionId | null | undefined,
		envArg: t.Node | undefined,
		callerFuncId: FunctionId | null | undefined,
		activeFunctionIds: Set<FunctionId>,
	): t.FunctionExpression | undefined {
		if (
			closureFuncId == null ||
			isBlockedFunctionId(closureFuncId) ||
			activeFunctionIds.has(closureFuncId)
		) return;
		const wrapper = functions.get(closureFuncId) ??
			functions.relift(closureFuncId);
		if (!wrapper || wrapper.isAsync) return;

		const analysis = wrapper.analyseGeneratorClosure();
		if (analysis == null) return;
		const generatorFuncId = functionIdFromGeneratorAnalysis(analysis);
		if (
			generatorFuncId != null &&
			(isBlockedFunctionId(generatorFuncId) ||
				activeFunctionIds.has(generatorFuncId))
		) return;

		const replacement = functionForGeneratorClosureAnalysis(
			analysis,
			false,
			wrapper,
			true,
		);
		if (!replacement) return;

		if (wrapper.name) replacement.id = t.identifier(wrapper.name);
		const syntheticFunctionId = nextSyntheticFunctionId++;
		recordFunctionCreationEnv(
			syntheticFunctionId,
			envArg,
			callerFuncId,
			environmentStepsForGeneratorAnalysis(
				analysis,
				closureFuncId,
			),
		);
		retargetParentFunctionId(
			replacement,
			closureFuncId,
			syntheticFunctionId,
		);
		// `replacement` is normally the resolved generator body's AST, not the
		// shortcut wrapper's AST. Its creation calls therefore retain the body's
		// addresses/provenance until the retarget below. Index the sites from the
		// function that actually supplied the replacement; copying the wrapper's
		// sites left body-owned CreateEnvironment calls unkeyed.
		cloneEnvironmentCreationSites(
			generatorFuncId ?? closureFuncId,
			syntheticFunctionId,
		);
		if (generatorFuncId != null && generatorFuncId !== closureFuncId) {
			retargetParentFunctionId(
				replacement,
				generatorFuncId,
				syntheticFunctionId,
			);
		}
		inheritParentFunction(closureFuncId, syntheticFunctionId);
		const active = new Set(activeFunctionIds);
		active.add(closureFuncId);
		if (generatorFuncId != null) active.add(generatorFuncId);
		inlineNestedClosuresInFunction(replacement, active, true);
		normalizeDuplicateRegisterDeclarations(replacement);
		return replacement;
	}

	function recordFunctionCreationEnv(
		functionId: FunctionId | null | undefined,
		envArg: t.Node | undefined,
		callerFuncId: FunctionId | null | undefined,
		steps: readonly ElidedEnvironmentStep[] = [],
	) {
		if (functionId == null || envArg == null || callerFuncId == null) {
			return;
		}
		funcCreationEnvArgs.set(functionId, {
			envArg,
			callerFuncId,
			steps: steps.map((step) => ({ ...step })),
		});
	}

	function callerFunctionIdForCall(call: NodePath<t.CallExpression>) {
		return (<LiftedExtra | undefined> call.node.extra)?.parentFunctionId;
	}

	function localEnvironmentForFunction(
		funcId: FunctionId,
		creationSiteParent?: Environment,
	) {
		const existing = funcEnvs.get(funcId);
		if (existing) return existing;
		const parent = creationSiteParent ??
			capturedEnvironment(
				funcId,
				0,
				funcEnvs,
				parentFunctions,
			) ?? null;
		const env = new Environment(funcId, parent);
		funcEnvs.set(funcId, env);
		return env;
	}

	/**
	 * Build the per-function site tables from the bytecode plan.
	 *
	 * This used to traverse the composed tree. That traversal ran once, before
	 * child functions were inlined, so it only ever saw the root's creation
	 * calls -- on TestApp, 30 sites out of a bundle whose output names 322
	 * functions' worth of namespaced environments. It also keyed sites on AST
	 * node identity, which a clone does not share, and fell back to a
	 * traversal counter for anything it had not seen. The plan has every site,
	 * keyed by address, before any of that happens.
	 */
	function indexEnvironmentCreationSites() {
		for (const [functionId, sites] of plan.environmentCreationSites) {
			indexFunctionCreationSites(functionId, sites);
		}
	}

	function indexFunctionCreationSites(
		functionId: FunctionId,
		sites: readonly EnvironmentCreationSite[],
	) {
		// Already address-ordered by `buildBytecodeDerivedPlan`.
		const primary = sites.find((site) =>
			site.kind === 'CreateFunctionEnvironment' ||
			site.kind === 'CreateTopLevelEnvironment'
		);
		if (primary) {
			primaryEnvironmentSiteByFunction.set(
				functionId,
				environmentCreationSiteKey(
					functionId,
					primary.kind,
					primary.address,
				),
			);
		}
		let explicitIndex = 0;
		for (const site of sites) {
			environmentIdentity.byAddress++;
			if (site === primary) continue;
			explicitEnvironmentIndexBySite.set(
				environmentCreationSiteKey(
					functionId,
					site.kind,
					site.address,
				),
				explicitIndex++,
			);
		}
	}

	/**
	 * Give a clone the same creation sites as the function it was cloned from.
	 *
	 * `retargetParentFunctionId` rewrites every `extra.parentFunctionId` in the
	 * clone to its synthetic id, so its creation calls key themselves under an
	 * id the bytecode plan has never heard of. Without this the clone's own
	 * primary environment is not recognised as primary and it is emitted in the
	 * `_x<index>` namespace instead of under the bare prefix its children's
	 * `GetParentEnvironment` resolves to.
	 *
	 * Addresses are unchanged by cloning, so the original's site list transfers
	 * as-is under the new id.
	 */
	/**
	 * Give a clone the original's place in the static environment chain.
	 *
	 * `retargetParentFunctionId` rewrites the clone's instructions to a
	 * synthetic id, which the bytecode-derived `parentFunctions` graph has
	 * never heard of. `capturedEnvironment` then walks an empty chain, so every
	 * `%GetParentEnvironment(d)` inside the clone resolves to nothing and is
	 * emitted raw -- on TestApp that was every unresolved lookup in the output,
	 * all of them in synthetic functions and all with an empty chain.
	 *
	 * A clone stands exactly where its original stood, so it inherits the
	 * original's parent and `GetParentEnvironment` counts through the same
	 * ancestors at the same depths.
	 */
	function inheritParentFunction(fromId: FunctionId, toId: FunctionId) {
		const parent = parentFunctions.get(fromId);
		if (parent != null) parentFunctions.set(toId, parent);
	}

	function cloneEnvironmentCreationSites(
		fromId: FunctionId,
		toId: FunctionId,
	) {
		const sites = plan.environmentCreationSites.get(fromId) ??
			clonedEnvironmentCreationSites.get(fromId);
		if (!sites) return;
		clonedEnvironmentCreationSites.set(toId, sites);
		indexFunctionCreationSites(toId, sites);
	}

	/**
	 * The site key for a creation call, read from its own provenance.
	 *
	 * No node-identity map: a clone carries the same `extra`, and a call that
	 * only appears after its function is inlined answers the same as one
	 * present from the start.
	 */
	function creationSiteOf(
		call: t.CallExpression,
	): { key: string; functionId: FunctionId; id: EnvironmentSiteId } | null {
		const extra = call.extra as LiftedExtra | undefined;
		const functionId = extra?.parentFunctionId;
		if (functionId == null) {
			environmentIdentity.unowned++;
			return null;
		}
		if (typeof extra?.address !== 'number') {
			environmentIdentity.positional++;
			return null;
		}
		const kind = t.isV8IntrinsicIdentifier(call.callee)
			? call.callee.name
			: null;
		if (kind == null) return null;
		const id: EnvironmentSiteId = {
			functionId,
			kind: kind as EnvironmentCreationSite['kind'],
			address: extra.address,
		};
		return {
			key: environmentCreationSiteKey(functionId, kind, extra.address),
			functionId,
			id,
		};
	}

	function creationSiteKeyOf(call: t.CallExpression): string | null {
		return creationSiteOf(call)?.key ?? null;
	}

	function reportEnvironmentIdentity() {
		if (Deno.env.get('ARES_DEBUG_ENV_IDENTITY') !== '1') return;
		console.error('[env-identity]', JSON.stringify(environmentIdentity));
	}

	function environmentCreationIndex(
		call: t.CallExpression,
		funcId: FunctionId,
	) {
		const site = creationSiteKeyOf(call);
		if (site != null) {
			const existing = explicitEnvironmentIndexBySite.get(site);
			if (existing != null) return existing;
		}
		environmentIdentity.unkeyedIndexLookups++;
		throw new LiftError(
			`Missing bytecode-derived environment creation site for function #${funcId}`,
		);
	}

	function walkEnvironmentParents(
		env: Environment | null | undefined,
		depth: number,
	) {
		let current: Environment | null | undefined = env;
		for (let i = 0; i < depth; i++) {
			current = current?.parent;
			if (current == null) return undefined;
		}
		return current ?? undefined;
	}

	function inlineLoweredGeneratorFunction(
		call: NodePath<t.CallExpression>,
		wrapperFunc: IRFunction,
		analysis: ReturnType<typeof analyseLoweredGeneratorClosure>,
		envArg: t.Node | undefined,
		callerFuncId: FunctionId | null | undefined,
		requireSafelyNested: boolean,
	) {
		if (analysis == null) return false;
		const loweredGeneratorId = analysis.functionId;
		if (
			requireSafelyNested &&
			!safelyNestedFunctions.has(loweredGeneratorId)
		) return false;
		const innerGenerator = functions.get(loweredGeneratorId);
		if (!innerGenerator) return false;

		recordFunctionCreationEnv(
			loweredGeneratorId,
			envArg,
			callerFuncId,
			environmentStepsForCapture(
				analysis.environmentCapture,
				wrapperFunc.id,
			),
		);
		applyLoweredGeneratorWrapperSlotAliases(innerGenerator);
		const lowered = innerGenerator.tryGetFunctionExpr();
		if (!lowered) return false;

		inlineNestedClosuresInFunction(lowered);
		if (wrapperFunc.name) lowered.id = t.identifier(wrapperFunc.name);
		functions.delete(loweredGeneratorId);
		call.replaceWith(normalizedFunctionExpr(lowered));
		call.skip();
		return true;
	}

	function inlineGeneratorClosureFunction(
		call: NodePath<t.CallExpression>,
		genIRClosure: IRFunction,
		closureFuncId: FunctionId | null | undefined,
		envArg: t.Node | undefined,
		callerFuncId: FunctionId | null | undefined,
		requireSafelyNested: boolean,
		activeFunctionIds = new Set<FunctionId>(),
	) {
		recordFunctionCreationEnv(closureFuncId, envArg, callerFuncId);

		const genAnalysis = genIRClosure.analyseGeneratorClosure();
		recordFunctionCreationEnv(
			functionIdFromGeneratorAnalysis(genAnalysis),
			envArg,
			callerFuncId,
			environmentStepsForGeneratorAnalysis(
				genAnalysis,
				closureFuncId,
			),
		);

		const genFunc = functionForGeneratorClosureAnalysis(
			genAnalysis,
			requireSafelyNested,
			genIRClosure,
		);
		if (genFunc) {
			if (genIRClosure.name) {
				genFunc.id = t.identifier(genIRClosure.name);
			}
			rememberReusableFunctionExpression(closureFuncId, genFunc);
			inlineNestedClosuresInFunction(genFunc);
			call.replaceWith(normalizedFunctionExpr(genFunc));
			call.skip();
			return true;
		}

		const rebuilt = cloneGeneratorClosureRef(
			closureFuncId,
			envArg,
			callerFuncId,
			activeFunctionIds,
		);
		if (rebuilt) {
			call.replaceWith(normalizedFunctionExpr(rebuilt));
			call.skip();
			return true;
		}

		if (
			inlineLoweredGeneratorFunction(
				call,
				genIRClosure,
				analyseLoweredGeneratorClosure(genIRClosure),
				envArg,
				callerFuncId,
				requireSafelyNested,
			)
		) return true;

		const fallback = normalizedFunctionExpr(
			genIRClosure.getFunctionExpr(),
		);
		rememberReusableFunctionExpression(closureFuncId, fallback);
		call.replaceWith(fallback);
		call.skip();
		return true;
	}

	function inlineAsyncClosureFunction(
		call: NodePath<t.CallExpression>,
		closureRef: NodePath,
		asyncIRClosure: IRFunction,
		asGenerator: boolean,
		envArg?: t.Node,
		callerFuncId?: FunctionId | null,
	) {
		if (envArg != null && callerFuncId != null) {
			recordFunctionCreationEnv(
				asyncIRClosure.id,
				envArg,
				callerFuncId,
			);
		}
		const outerCreation = funcCreationEnvArgs.get(asyncIRClosure.id);
		const asyncAnalysis = asGenerator
			? asyncIRClosure.analyseAsyncGeneratorClosure()
			: asyncIRClosure.analyseAsyncClosure();
		const genIRClosure = popNestedFunction(
			asyncAnalysis?.functionId,
		);
		if (!genIRClosure) {
			closureRef.replaceWith(
				normalizedFunctionExpr(asyncIRClosure.getFunctionExpr()),
			);
			return true;
		}
		const asyncSteps = asyncAnalysis
			? environmentStepsForCapture(
				asyncAnalysis.environmentCapture,
				asyncIRClosure.id,
			)
			: [];
		if (outerCreation && asyncAnalysis) {
			recordFunctionCreationEnv(
				asyncAnalysis.functionId,
				outerCreation.envArg,
				outerCreation.callerFuncId,
				[...outerCreation.steps, ...asyncSteps],
			);
		}

		const generatorAnalysis = genIRClosure.analyseGeneratorClosure();
		const generatorFunctionId = functionIdFromGeneratorAnalysis(
			generatorAnalysis,
		);
		if (outerCreation && generatorFunctionId != null) {
			recordFunctionCreationEnv(
				generatorFunctionId,
				outerCreation.envArg,
				outerCreation.callerFuncId,
				[
					...outerCreation.steps,
					...asyncSteps,
					...environmentStepsForGeneratorAnalysis(
						generatorAnalysis,
						genIRClosure.id,
					),
				],
			);
		}
		const innerGenIRFunc = functionForGeneratorClosureAnalysis(
			generatorAnalysis,
			true,
			genIRClosure,
		);
		if (!innerGenIRFunc) {
			closureRef.replaceWith(
				normalizedFunctionExpr(genIRClosure.getFunctionExpr()),
			);
			return true;
		}

		inlineNestedClosuresInFunction(innerGenIRFunc);
		innerGenIRFunc.generator = asGenerator;
		innerGenIRFunc.async = true;
		if (asyncIRClosure.name) {
			innerGenIRFunc.id = t.identifier(asyncIRClosure.name);
		}
		normalizeDuplicateRegisterDeclarations(innerGenIRFunc);
		const [replacementPath] = call.replaceWith(innerGenIRFunc);
		normalizeDuplicateRegisterDeclarations(replacementPath.node);
		if (!asGenerator) {
			rewriteYieldExpressionsToAwait(replacementPath.node);
		} else {
			rewriteAwaitAsyncIteratorYieldsToAwait(replacementPath.node);
			call.skip();
		}
		return true;
	}

	function inlineCreateGeneratorObject(
		call: NodePath<t.CallExpression>,
	) {
		const hasEnvironmentArgument = call.node.arguments.length === 2;
		const funcRef = call.get(
			hasEnvironmentArgument ? 'arguments.1' : 'arguments.0',
		);
		const functionId = extractFunctionRef(funcRef.node);
		if (
			functionId == null
		) return false;
		const callerFuncId = callerFunctionIdForCall(call);
		const envArg = hasEnvironmentArgument
			? call.node.arguments[0]
			: undefined;
		recordFunctionCreationEnv(functionId, envArg, callerFuncId);
		if (!safelyNestedFunctions.has(functionId)) {
			const replacement = cloneNestedFunctionRef(
				functionId,
				envArg,
				callerFuncId,
				new Set(),
				true,
			);
			if (!replacement) return false;
			call.replaceWith(t.callExpression(replacement, []));
			call.skip();
			return true;
		}
		const genIRFunc = functions.get(functionId);
		if (!genIRFunc) {
			const replacement = cloneNestedFunctionRef(
				functionId,
				envArg,
				callerFuncId,
				new Set(),
				true,
			);
			if (!replacement) return false;
			call.replaceWith(t.callExpression(replacement, []));
			call.skip();
			return true;
		}
		const blockParent = call.findParent((path) => path.isBlockStatement());
		if (blockParent?.isBlockStatement() && envArg) {
			recordLoweredGeneratorWrapperSlotAliases(
				genIRFunc.file,
				functionId,
				blockParent.node.body,
				envArg,
			);
		}
		applyLoweredGeneratorWrapperSlotAliases(genIRFunc);
		const genFunc = genIRFunc.tryGetFunctionExpr();
		if (!genFunc) return false;
		rememberReusableFunctionExpression(functionId, genFunc);
		inlineNestedClosuresInFunction(genFunc);
		functions.delete(functionId);
		normalizeDuplicateRegisterDeclarations(genFunc);

		call.replaceWith(t.callExpression(
			genFunc,
			[],
		));
		call.skip();
		return true;
	}

	function inlineNestedClosuresInFunction(
		funcExpr: t.FunctionExpression,
		activeFunctionIds = new Set<FunctionId>(),
		cloneNestedRefs = false,
	) {
		const wrapped = t.file(t.program([t.expressionStatement(funcExpr)]));
		normalizeDuplicateRegisterDeclarations(wrapped);
		traverse(wrapped, {
			CallExpression(call) {
				if (
					!t.isV8IntrinsicIdentifier(call.node.callee)
				) return;

				if (call.node.callee.name === 'CreateGenerator') {
					inlineCreateGeneratorObject(call);
					return;
				}

				if (call.node.callee.name === 'CreateGeneratorClosure') {
					const closureRef = call.get('arguments.0');
					const closureFuncId = extractFunctionRef(closureRef.node);
					const genIRClosure = inlineNestedFunctionRef(
						closureRef.node,
					);
					if (genIRClosure == null) {
						const replacement = cloneGeneratorClosureRef(
							closureFuncId,
							call.node.arguments[1],
							callerFunctionIdForCall(call),
							activeFunctionIds,
						);
						if (replacement) {
							call.replaceWith(replacement);
							call.skip();
						}
						return;
					}
					inlineGeneratorClosureFunction(
						call,
						genIRClosure,
						closureFuncId,
						call.node.arguments[1],
						callerFunctionIdForCall(call),
						true,
						activeFunctionIds,
					);
					return;
				}

				if (call.node.callee.name !== 'CreateClosure') return;

				const closureRef = call.get('arguments.0');
				const functionId = extractFunctionRef(closureRef.node);
				if (
					functionId != null &&
					activeFunctionIds.has(functionId)
				) {
					if (funcExpr.id) {
						call.replaceWith(t.identifier(funcExpr.id.name));
						call.skip();
					}
					return;
				}
				if (cloneNestedRefs) {
					const replacement = cloneGeneratorClosureRef(
						functionId,
						call.node.arguments[1],
						callerFunctionIdForCall(call),
						activeFunctionIds,
					) ?? cloneNestedFunctionRef(
						functionId,
						call.node.arguments[1],
						callerFunctionIdForCall(call),
						activeFunctionIds,
					);
					if (replacement) {
						call.replaceWith(replacement);
						call.skip();
						return;
					}
				}
				let irFunc = inlineNestedFunctionRef(closureRef.node);
				if (!irFunc && functionId != null) {
					const replacement = cloneGeneratorClosureRef(
						functionId,
						call.node.arguments[1],
						callerFunctionIdForCall(call),
						activeFunctionIds,
					) ?? cloneNestedFunctionRef(
						functionId,
						call.node.arguments[1],
						callerFunctionIdForCall(call),
						activeFunctionIds,
					);
					if (replacement) {
						call.replaceWith(replacement);
						call.skip();
					}
					return;
				}
				if (!irFunc) return;
				recordFunctionCreationEnv(
					functionId,
					call.node.arguments[1],
					callerFunctionIdForCall(call),
				);

				const genAnalysis = irFunc.analyseGeneratorClosure();
				const genFunc = functionForGeneratorClosureAnalysis(
					genAnalysis,
					false,
					irFunc,
				);
				if (genFunc) {
					if (irFunc.name) genFunc.id = t.identifier(irFunc.name);
					rememberReusableFunctionExpression(functionId, genFunc);
					inlineNestedClosuresInFunction(
						genFunc,
						functionId == null
							? activeFunctionIds
							: new Set([...activeFunctionIds, functionId]),
					);
					normalizeDuplicateRegisterDeclarations(genFunc);
					call.replaceWith(genFunc);
					call.skip();
					return;
				}
				if (genAnalysis != null) {
					const replacement = cloneGeneratorClosureRef(
						functionId,
						call.node.arguments[1],
						callerFunctionIdForCall(call),
						activeFunctionIds,
					);
					if (replacement) {
						call.replaceWith(replacement);
						call.skip();
						return;
					}
				}

				const loweredGeneratorId = analyseLoweredGeneratorClosure(
					irFunc,
				);
				if (
					inlineLoweredGeneratorFunction(
						call,
						irFunc,
						loweredGeneratorId,
						undefined,
						undefined,
						false,
					)
				) return;

				if (irFunc.analyseAsyncGeneratorClosure()) {
					inlineAsyncClosureFunction(
						call,
						closureRef,
						irFunc,
						true,
						call.node.arguments[1],
						callerFunctionIdForCall(call),
					);
					return;
				}

				const replacement = irFunc.tryGetFunctionExpr();
				if (!replacement) {
					if (functionId != null) functions.set(functionId, irFunc);
					return;
				}
				rememberReusableFunctionExpression(functionId, replacement);
				inlineNestedClosuresInFunction(
					replacement,
					functionId == null
						? activeFunctionIds
						: new Set([...activeFunctionIds, functionId]),
				);
				normalizeDuplicateRegisterDeclarations(replacement);
				call.replaceWith(replacement);
				call.skip();
			},
		});
		traverse(wrapped, {
			CallExpression(call) {
				const callee = call.get('callee');
				if (!callee.isMemberExpression()) return;
				const property = callee.get('property');
				if (
					!property.isIdentifier() ||
					!['forEach', 'map', 'reduce'].includes(property.node.name)
				) return;
				const callback = call.get('arguments.0');
				if (!callback.isCallExpression()) return;
				if (
					!callback.get('callee').isV8IntrinsicIdentifier({
						name: 'CreateClosure',
					})
				) return;
				const closureRef = callback.get('arguments.0');
				const functionId = extractFunctionRef(closureRef.node);
				if (!isPlainCloneableFunctionRef(functionId)) return;
				const replacement = cloneNestedFunctionRef(
					functionId,
					callback.node.arguments[1],
					callerFunctionIdForCall(callback),
					activeFunctionIds,
				);
				if (!replacement) return;
				callback.replaceWith(replacement);
				callback.skip();
			},
		});
	}
	const normalizedFunctionExpr = (funcExpr: t.FunctionExpression) => {
		normalizeDuplicateRegisterDeclarations(funcExpr);
		return funcExpr;
	};

	normalizeDuplicateRegisterDeclarations(wrapped);
	const inlineTopLevelClosureCall = (
		call: NodePath<t.CallExpression>,
	) => {
		if (!t.isV8IntrinsicIdentifier(call.node.callee)) return;
		if (call.node.callee.name == 'CreateClosure') {
			const closureRef = call.get('arguments.0');
			const closureFuncId = extractFunctionRef(closureRef.node);
			const callerFuncId = callerFunctionIdForCall(call);
			const irFunc = inlineNestedFunctionRef(closureRef.node);
			if (!irFunc) {
				const replacement = cloneGeneratorClosureRef(
					closureFuncId,
					call.node.arguments[1],
					callerFuncId,
					new Set(),
				) ?? cloneNestedFunctionRef(
					closureFuncId,
					call.node.arguments[1],
					callerFuncId,
					new Set(),
				);
				if (replacement) {
					call.replaceWith(normalizedFunctionExpr(replacement));
					call.skip();
				}
				return;
			}
			recordFunctionCreationEnv(
				closureFuncId,
				call.node.arguments[1],
				callerFuncId,
			);

			if (irFunc.isAsync) {
				inlineAsyncClosureFunction(
					call,
					closureRef,
					irFunc,
					false,
					call.node.arguments[1],
					callerFuncId,
				);
				return;
			}

			const genAnalysis = irFunc.analyseGeneratorClosure();
			recordFunctionCreationEnv(
				functionIdFromGeneratorAnalysis(genAnalysis),
				call.node.arguments[1],
				callerFuncId,
				environmentStepsForGeneratorAnalysis(
					genAnalysis,
					closureFuncId,
				),
			);
			const genFunc = functionForGeneratorClosureAnalysis(
				genAnalysis,
				true,
				irFunc,
			);
			if (genFunc) {
				if (irFunc.name) genFunc.id = t.identifier(irFunc.name);
				rememberReusableFunctionExpression(closureFuncId, genFunc);
				inlineNestedClosuresInFunction(
					genFunc,
					closureFuncId == null
						? new Set()
						: new Set([closureFuncId]),
				);
				call.replaceWith(normalizedFunctionExpr(genFunc));
				call.skip();
				return;
			}
			if (genAnalysis != null) {
				const replacement = cloneGeneratorClosureRef(
					closureFuncId,
					call.node.arguments[1],
					callerFuncId,
					new Set(),
				);
				if (replacement) {
					call.replaceWith(normalizedFunctionExpr(replacement));
					call.skip();
					return;
				}
			}

			const loweredGeneratorId = analyseLoweredGeneratorClosure(
				irFunc,
			);
			if (
				inlineLoweredGeneratorFunction(
					call,
					irFunc,
					loweredGeneratorId,
					call.node.arguments[1],
					callerFuncId,
					true,
				)
			) return;

			const asyncGenFunc = irFunc.analyseAsyncGeneratorClosure();
			if (asyncGenFunc) {
				inlineAsyncClosureFunction(
					call,
					closureRef,
					irFunc,
					true,
					call.node.arguments[1],
					callerFuncId,
				);
				return;
			}

			const funcExpr = irFunc.tryGetFunctionExpr();
			if (!funcExpr) {
				if (closureFuncId != null) {
					functions.set(closureFuncId, irFunc);
				}
				return;
			}
			rememberReusableFunctionExpression(closureFuncId, funcExpr);
			inlineNestedClosuresInFunction(
				funcExpr,
				closureFuncId == null ? new Set() : new Set([closureFuncId]),
			);
			call.replaceWith(normalizedFunctionExpr(funcExpr));
			call.skip();
		} else if (call.node.callee.name == 'CreateGeneratorClosure') {
			const closureRef = call.get('arguments.0');
			const closureFuncId = extractFunctionRef(closureRef.node);
			const genIRClosure = inlineNestedFunctionRef(
				closureRef.node,
			);
			if (genIRClosure == null) {
				const replacement = cloneGeneratorClosureRef(
					closureFuncId,
					call.node.arguments[1],
					callerFunctionIdForCall(call),
					new Set(),
				);
				if (replacement) {
					call.replaceWith(replacement);
					call.skip();
				}
				return;
			}
			inlineGeneratorClosureFunction(
				call,
				genIRClosure,
				closureFuncId,
				call.node.arguments[1],
				callerFunctionIdForCall(call),
				true,
			);
		} else if (call.node.callee.name == 'CreateAsyncClosure') {
			const closureRef = call.get('arguments.0');
			const asyncIRClosure = inlineNestedFunctionRef(
				closureRef.node,
			);
			if (!asyncIRClosure) return;
			inlineAsyncClosureFunction(
				call,
				closureRef,
				asyncIRClosure,
				false,
				call.node.arguments[1],
				callerFunctionIdForCall(call),
			);
		} else if (call.node.callee.name == 'CreateGenerator') {
			inlineCreateGeneratorObject(call);
		}
	};
	const topLevelBody = wrapped.program.body;
	const inliningChunkSize = 256;
	for (
		let start = 0;
		start < topLevelBody.length;
		start += inliningChunkSize
	) {
		const end = Math.min(start + inliningChunkSize, topLevelBody.length);
		const chunk = t.file(t.program(topLevelBody.slice(start, end)));
		traverse(chunk, {
			CallExpression: inlineTopLevelClosureCall,
		});
		topLevelBody.splice(start, end - start, ...chunk.program.body);
		// The root program can contain tens of thousands of closure sites. Each
		// chunk is independent during inlining, so release its NodePaths before
		// composing the next set of functions.
		traverse.cache.clear();
	}

	// Replacements made by the primary traversal can insert a complete function
	// expression beneath a path which is then skipped. Most replacement paths
	// recursively compose their own bodies, but generator-wrapper fallbacks can
	// still expose a raw CreateGenerator afterwards. Sweep only that intrinsic
	// once all primary replacements are present. Keep the sweep chunked: the
	// file root can contain tens of thousands of Metro module definitions.
	for (
		let start = 0;
		start < topLevelBody.length;
		start += inliningChunkSize
	) {
		const end = Math.min(start + inliningChunkSize, topLevelBody.length);
		const chunk = t.file(t.program(topLevelBody.slice(start, end)));
		traverse(chunk, {
			CallExpression(call) {
				if (
					!t.isV8IntrinsicIdentifier(call.node.callee, {
						name: 'CreateGenerator',
					})
				) return;
				inlineCreateGeneratorObject(call);
			},
		});
		topLevelBody.splice(start, end - start, ...chunk.program.body);
		traverse.cache.clear();
	}

	// The raw CreateGenerator sweep above can be the first point at which a
	// consumed native-generator body is available. Re-run the enclosing priming
	// protocol now that its intrinsic has become a concrete function expression;
	// otherwise the synthetic wrapper, initial yield and discarded `.next()` all
	// survive composition.
	for (
		let start = 0;
		start < topLevelBody.length;
		start += inliningChunkSize
	) {
		const end = Math.min(start + inliningChunkSize, topLevelBody.length);
		const chunk = t.file(t.program(topLevelBody.slice(start, end)));
		traverse(chunk, {
			FunctionExpression(path) {
				const replacement = collapsePrimedNativeGeneratorWrapper(
					path.node,
				);
				if (!replacement) return;
				path.replaceWith(replacement);
				path.skip();
			},
		});
		topLevelBody.splice(start, end - start, ...chunk.program.body);
		traverse.cache.clear();
	}

	function resolveEnvToEnvironment(
		envArg: t.Node,
		funcId: FunctionId,
		scope: Scope,
		seen = new Set<string>(),
	): Environment | undefined {
		const tagged = locationOf(envArg);
		if (tagged?.kind === 'environment-handle') {
			const resolved = environmentByCreationSite.get(
				environmentSiteKey(tagged.environment),
			);
			if (resolved) return resolved;
		}
		function resolveClosureEnvironment(
			closure: t.Node,
		): Environment | undefined {
			if (t.isIdentifier(closure)) {
				const key = `closure:${closure.name}`;
				if (seen.has(key)) return undefined;
				const binding = scope.getBinding(closure.name);
				if (
					!binding?.constant || !binding.path.isVariableDeclarator()
				) {
					return undefined;
				}
				const init = binding.path.node.init;
				if (!init) return undefined;
				seen.add(key);
				const resolved = resolveClosureEnvironment(init);
				seen.delete(key);
				return resolved;
			}

			if (t.isFunction(closure)) {
				const closureFunctionId =
					(closure.extra as LiftedExtra | undefined)
						?.parentFunctionId;
				if (closureFunctionId == null) return undefined;
				const key = `closure-function:${closureFunctionId}`;
				if (seen.has(key)) return undefined;
				const creation = funcCreationEnvArgs.get(closureFunctionId);
				if (!creation) return undefined;
				seen.add(key);
				const resolved = resolveEnvToEnvironment(
					creation.envArg,
					creation.callerFuncId,
					scope,
					seen,
				);
				seen.delete(key);
				return resolved;
			}

			if (
				t.isCallExpression(closure) &&
				t.isV8IntrinsicIdentifier(closure.callee) &&
				[
					'CreateClosure',
					'CreateGeneratorClosure',
					'CreateAsyncClosure',
				].includes(closure.callee.name)
			) {
				const envArg = closure.arguments[1];
				if (!envArg || !t.isNode(envArg)) return undefined;
				return resolveEnvToEnvironment(
					envArg,
					funcId,
					scope,
					seen,
				);
			}

			return undefined;
		}

		function resolveCreationEnvironment(depth: number) {
			const key = `creation:${funcId}`;
			if (seen.has(key)) return undefined;
			const creation = funcCreationEnvArgs.get(funcId);
			if (creation == null) return undefined;
			seen.add(key);
			let baseEnv: Environment | null | undefined = isUndefinedNode(
					creation.envArg,
				)
				? null
				: resolveEnvToEnvironment(
					creation.envArg,
					creation.callerFuncId,
					scope,
					seen,
				);
			for (const step of creation.steps) {
				if (step.kind === 'parent') {
					baseEnv = walkEnvironmentParents(baseEnv, step.depth);
					if (baseEnv == null) break;
					continue;
				}
				if (baseEnv === undefined) break;
				baseEnv = new Environment(step.functionId, baseEnv);
			}
			seen.delete(key);
			return walkEnvironmentParents(baseEnv, depth);
		}

		/**
		 * A further environment created by the same function.
		 *
		 * `CreateFunctionEnvironment` and `CreateTopLevelEnvironment` all
		 * resolved to the function's single `Environment`, so a function that
		 * creates several -- an optimized IIFE inlined into its parent, most
		 * visibly -- wrote every one of them through the same
		 * `_env_<fn>_<slot>` names. Distinct runtime environments then shared a
		 * slot, which reads as an assignment from nowhere.
		 *
		 * The first creation keeps the bare prefix, because that is what a
		 * child's `GetParentEnvironment` resolves to; the rest are namespaced
		 * like `CreateEnvironment` already is. Their parent is the function's
		 * own enclosing environment, which is what the instruction captures at
		 * runtime.
		 */
		function localEnvironmentForCreate(call: t.CallExpression) {
			const existing = explicitCreateEnvironments.get(call);
			if (existing) return existing;
			// Synthetic IDs represent a particular clone at a particular creation
			// site and therefore have no entry in the bytecode-derived parent graph.
			// Its captured creation environment is the parent of the clone's local
			// function environment. Without this edge, nested closures can resolve
			// the clone's own slots but every GetParentEnvironment depth above it
			// leaks into the generated output.
			const creationSiteParent = funcId >= file.functions.length
				? resolveCreationEnvironment(0)
				: undefined;
			// Primacy is a property of the function the site belongs to, not of
			// the function resolving it. They differ for a clone, whose
			// synthetic id has no plan entry while its instructions still carry
			// the original's `parentFunctionId`; comparing against `funcId`
			// there would deny a clone its own primary environment and push it
			// into the `_x<index>` namespace.
			const creationSite = creationSiteOf(call);
			const site = creationSite?.key ?? null;
			if (
				creationSite != null &&
				primaryEnvironmentSiteByFunction.get(
						creationSite.functionId,
					) === site
			) {
				environmentIdentity.resolvedPrimary++;
				const primary = localEnvironmentForFunction(
					funcId,
					creationSiteParent,
				);
				primary.claimSite(creationSite.id);
				explicitCreateEnvironments.set(call, primary);
				environmentByCreationSite.set(site, primary);
				return primary;
			}
			if (site != null) {
				const claimed = environmentByCreationSite.get(site);
				if (claimed) {
					environmentIdentity.resolvedClaimed++;
					explicitCreateEnvironments.set(call, claimed);
					return claimed;
				}
			}
			environmentIdentity.resolvedNamespaced++;
			if (site == null) environmentIdentity.resolvedNamespacedUnkeyed++;
			const index = environmentCreationIndex(call, funcId);
			const functionEnvironment = localEnvironmentForFunction(
				funcId,
				creationSiteParent,
			);
			const env = new Environment(
				funcId,
				functionEnvironment.parent,
				`_env_${funcId}_x${index}`,
				creationSite?.id ?? null,
			);
			explicitCreateEnvironments.set(call, env);
			if (site != null) environmentByCreationSite.set(site, env);
			return env;
		}

		function explicitEnvironmentForCreate(call: t.CallExpression) {
			const existing = explicitCreateEnvironments.get(call);
			if (existing) return existing;
			const [parentArg] = call.arguments;
			const parent = parentArg && t.isNode(parentArg)
				? resolveEnvToEnvironment(parentArg, funcId, scope, seen) ??
					null
				: null;
			const creationSite = creationSiteOf(call);
			const site = creationSite?.key ?? null;
			if (site != null) {
				const claimed = environmentByCreationSite.get(site);
				if (claimed) {
					explicitCreateEnvironments.set(call, claimed);
					return claimed;
				}
			}
			const index = environmentCreationIndex(call, funcId);
			const env = new Environment(
				funcId,
				parent,
				`_env_${funcId}_x${index}`,
				creationSite?.id ?? null,
			);
			explicitCreateEnvironments.set(call, env);
			if (site != null) environmentByCreationSite.set(site, env);
			return env;
		}

		if (
			t.isCallExpression(envArg) &&
			t.isV8IntrinsicIdentifier(envArg.callee)
		) {
			const name = envArg.callee.name;
			if (name === 'GetParentEnvironment') {
				const [depthNode] = envArg.arguments;
				if (!t.isNumericLiteral(depthNode)) return;
				const localEnv = (envArg.extra as LiftedExtra | undefined)
					?.localEnvironment;
				if (localEnv) return localEnv;
				const creationEnv = resolveCreationEnvironment(
					depthNode.value,
				);
				if (creationEnv != null) return creationEnv;
				const env = capturedEnvironment(
					funcId,
					depthNode.value,
					funcEnvs,
					parentFunctions,
				);
				if (env != null) return env;
				return undefined;
			}
			if (name === 'GetEnvironment') {
				const [parentArg, depthNode] = envArg.arguments;
				if (!parentArg || !t.isNode(parentArg)) return;
				if (!t.isNumericLiteral(depthNode)) return;
				const baseEnv = resolveEnvToEnvironment(
					parentArg,
					funcId,
					scope,
					seen,
				);
				return walkEnvironmentParents(baseEnv, depthNode.value);
			}
			if (name === 'GetClosureEnvironment') {
				const [closure] = envArg.arguments;
				if (!closure || !t.isNode(closure)) return;
				return resolveClosureEnvironment(closure);
			}
			if (
				name === 'CreateFunctionEnvironment' ||
				name === 'CreateTopLevelEnvironment'
			) {
				return localEnvironmentForCreate(envArg);
			}
			if (name === 'CreateEnvironment') {
				return explicitEnvironmentForCreate(envArg);
			}
		}
		if (t.isIdentifier(envArg)) {
			if (seen.has(envArg.name)) return;
			seen.add(envArg.name);
			const binding = scope.getBinding(envArg.name);
			if (!binding?.path.isVariableDeclarator()) return;
			const init = agreedEnvironmentBinding(binding);
			if (!init) return;
			const resolved = resolveEnvToEnvironment(init, funcId, scope, seen);
			if (resolved?.site != null) {
				tagStorageLocation(envArg, {
					kind: 'environment-handle',
					environment: resolved.site,
				});
			}
			return resolved;
		}
	}

	/**
	 * The expression a handle register is bound to, across all of its writes.
	 *
	 * A constant `const env = <expr>` is the easy case. Reducer materialization
	 * also produces the split form -- `let env; … env = <expr>` -- which Babel
	 * marks non-constant, and which the previous `binding.constant` test
	 * rejected outright. On TestApp every unresolved environment lookup was one
	 * of these: the binding was found, and it simply had no initializer to
	 * follow.
	 *
	 * Identity, not substitution, is the question here, so a write does not have
	 * to dominate the use -- but every write has to agree, or the handle denotes
	 * different environments on different paths and no single answer is right.
	 */
	function agreedEnvironmentBinding(
		binding: Binding,
	): t.Expression | null {
		const candidates: t.Expression[] = [];
		const init = binding.path.isVariableDeclarator()
			? binding.path.node.init
			: null;
		if (init) candidates.push(init);
		for (const violation of binding.constantViolations) {
			if (
				!violation.isAssignmentExpression({ operator: '=' }) ||
				!t.isExpression(violation.node.right)
			) return null;
			candidates.push(violation.node.right);
		}
		const [first] = candidates;
		if (!first) return null;
		// An identifier is chased recursively by the caller; anything else has
		// to be an environment-valued expression to mean anything here.
		if (!t.isIdentifier(first) && !isEnvironmentValuedExpression(first)) {
			return null;
		}
		if (
			!candidates.every((candidate) =>
				t.isNodesEquivalent(candidate, first)
			)
		) return null;
		return first;
	}

	function localEnvironmentCall(env: Environment) {
		const localEnv = t.callExpression(
			t.v8IntrinsicIdentifier('GetParentEnvironment'),
			[t.numericLiteral(0)],
		);
		localEnv.extra = { localEnvironment: env };
		return env.site == null ? localEnv : tagStorageLocation(localEnv, {
			kind: 'environment-handle',
			environment: env.site,
		});
	}

	function recordEnvironmentHandleOutcome(
		path: NodePath | undefined,
		env: Environment | undefined,
	): void {
		if (env?.site != null) {
			environmentIdentity.resolvedHandles++;
			return;
		}
		if (path?.isIdentifier()) {
			const binding = path.scope.getBinding(path.node.name);
			if (
				binding != null &&
				(!binding.constant || binding.constantViolations.length > 0)
			) {
				environmentIdentity.ambiguousHandles++;
				return;
			}
		}
		environmentIdentity.unresolvedHandles++;
	}

	function retargetRecordedCreationEnvironment(
		functionId: FunctionId,
		name: string,
		env: Environment,
	) {
		for (const [createdFunctionId, creation] of funcCreationEnvArgs) {
			if (creation.callerFuncId !== functionId) continue;
			if (!t.isIdentifier(creation.envArg, { name })) continue;
			funcCreationEnvArgs.set(createdFunctionId, {
				...creation,
				envArg: localEnvironmentCall(env),
			});
		}
	}

	const declaredGlobals = new Set<string>();
	const inferredFunctionGlobals = new Set<string>();
	const referencedGlobals = new Set<string>();
	for (const name of root.globalNames ?? []) referencedGlobals.add(name);
	normalizeDuplicateRegisterDeclarations(wrapped);
	indexEnvironmentCreationSites();
	traverse(wrapped, {
		CallExpression: {
			exit(call) {
				if (!t.isV8IntrinsicIdentifier(call.node.callee)) {
					return;
				} else if (call.node.callee.name == 'TryGetById') {
					const args = call.node.arguments;
					if (args.length !== 2) return;
					const [object, property] = args;
					if (!t.isStringLiteral(property)) return;
					const objectIdentifier = t.isIdentifier(object)
						? object
						: null;
					const isGlobalObject =
						objectIdentifier?.name === 'global' ||
						(
							objectIdentifier != null &&
							/^r\d+_\d+$/.test(objectIdentifier.name) &&
							call.scope.getBinding(objectIdentifier.name) ==
								null
						);
					if (!isGlobalObject) return;
					call.replaceWith(t.identifier(property.value));
					call.node.extra = { isReferencedGlobal: true };
				} else if (call.node.callee.name == 'DelegateYield') {
					const [arg] = call.node.arguments;
					if (!t.isExpression(arg)) {
						throw new LiftError(
							'Invalid DelegateYield argument',
						);
					}
					call.replaceWith(t.yieldExpression(arg, true));
				} else if (
					call.node.callee.name == 'CreateFunctionEnvironment' ||
					call.node.callee.name == 'CreateTopLevelEnvironment' ||
					call.node.callee.name == 'CreateEnvironment'
				) {
					const functionId =
						(<LiftedExtra | undefined> call.node.extra)
							?.parentFunctionId;
					if (functionId == null) {
						throw new LiftError('Missing extra data');
					}
					const env = resolveEnvToEnvironment(
						call.node,
						functionId,
						call.scope,
					);
					if (!env) return;

					const decl = call.parentPath;
					if (
						decl.isAssignmentExpression({ operator: '=' }) &&
						call.key === 'right' &&
						t.isIdentifier(decl.node.left)
					) {
						// Label/deferred-exit emission may hoist an environment declaration
						// while leaving its original initializer as `env = %Create...()`.
						// Treat that mechanically split form as the same environment binding
						// as a variable-declarator initializer.
						const id = decl.node.left;
						const binding = decl.scope.getBinding(id.name);
						if (
							!binding?.path.isVariableDeclarator() ||
							binding.path.node.init != null ||
							(binding.path.getFunctionParent()?.node ??
									null) !==
								(decl.getFunctionParent()?.node ?? null)
						) return;
						const owner = decl.getFunctionParent()?.node ??
							null;
						const belongsToOwner = (path: NodePath) =>
							(path.getFunctionParent()?.node ?? null) ===
								owner;
						if (
							binding.constantViolations.some((path) =>
								belongsToOwner(path) &&
								path.node !== decl.node
							)
						) return;
						for (
							const ref of binding.referencePaths.filter(
								belongsToOwner,
							)
						) {
							ref.replaceWith(localEnvironmentCall(env));
						}
						for (const path of binding.referencePaths) {
							const foreignOwner = path.getFunctionParent();
							if (
								!foreignOwner ||
								foreignOwner.node === owner ||
								foreignOwner.scope.hasOwnBinding(id.name)
							) continue;
							foreignOwner.scope.push({
								id: t.identifier(id.name),
								kind: 'let',
							});
						}
						retargetRecordedCreationEnvironment(
							functionId,
							id.name,
							env,
						);
						if (decl.parentPath.isExpressionStatement()) {
							decl.parentPath.remove();
						} else {
							decl.replaceWith(localEnvironmentCall(env));
						}
						binding.path.remove();
						return;
					}
					if (
						!decl.isVariableDeclarator() || call.key != 'init'
					) {
						if (decl.isExpressionStatement()) {
							decl.remove();
						} else {
							call.replaceWith(localEnvironmentCall(env));
						}
						return;
					}
					const id = decl.node.id;
					if (!t.isIdentifier(id)) return;
					const binding = decl.scope.getBinding(id.name);
					if (
						!binding ||
						!binding.path.isVariableDeclarator() ||
						binding.scope !== decl.scope
					) return;
					const owner = decl.getFunctionParent()?.node ?? null;
					const belongsToOwner = (path: NodePath) =>
						(path.getFunctionParent()?.node ?? null) === owner;
					const references = binding.referencePaths.filter(
						belongsToOwner,
					);
					if (binding.constantViolations.some(belongsToOwner)) {
						return;
					}
					const foreignOwners = new Map<
						t.Function,
						NodePath<t.Function>
					>();
					for (
						const path of [
							...binding.referencePaths,
							...binding.constantViolations,
						]
					) {
						const foreignOwner = path.getFunctionParent();
						if (!foreignOwner || foreignOwner.node === owner) {
							continue;
						}
						foreignOwners.set(foreignOwner.node, foreignOwner);
					}
					for (const foreignOwner of foreignOwners.values()) {
						if (foreignOwner.scope.hasOwnBinding(id.name)) {
							continue;
						}
						foreignOwner.scope.push({
							id: t.identifier(id.name),
							kind: 'let',
						});
					}

					// Capture and replace the binding while the creation call is still its
					// initializer. Removing the call first invalidates its NodePath key in
					// snapshot-restored trees, leaving `const env;` and all environment
					// references unresolved during parallel composition. Only references
					// owned by this function belong to the environment register: an inlined
					// nested function can temporarily contain the same unbound register name.
					// Give those functions an explicit local binding before removing the outer
					// one so they cannot become accidental captures or unbound globals.
					for (const ref of references) {
						ref.replaceWith(localEnvironmentCall(env));
					}
					retargetRecordedCreationEnvironment(
						functionId,
						id.name,
						env,
					);

					decl.remove();
				} else if (call.node.callee.name == 'CreateBaseClass') {
					const classRef = call.get('arguments.0');
					const irFunc = inlineNestedFunctionRef(classRef.node);
					if (!irFunc) return;

					const klass = call.replaceWith(
						irFunc.classExpressionFromFunction(null),
					)[0];
					inlineAdjacentClassMethods(klass);
				} else if (call.node.callee.name == 'CreateDerivedClass') {
					const classRef = call.get('arguments.0');
					const superClass = call.get('arguments.2');
					const irFunc = inlineNestedFunctionRef(classRef.node);
					if (!irFunc || !superClass.isExpression()) return;

					const klass = call.replaceWith(
						irFunc.classExpressionFromFunction(
							t.cloneNode(superClass.node, true),
						),
					)[0];
					inlineAdjacentClassMethods(klass);
				}
			},
		},
		MemberExpression: {
			exit(member: NodePath<t.MemberExpression>) {
				if (!member.node.computed) return;
				const obj = member.node.object;
				if (
					!t.isCallExpression(obj) ||
					!t.isV8IntrinsicIdentifier(obj.callee, {
						name: 'expectEnvironment',
					})
				) return;
				if (
					member.parentPath?.isAssignmentExpression({
						operator: '=',
					}) &&
					member.key === 'left'
				) return;
				const slotNode = member.node.property;
				if (!t.isNumericLiteral(slotNode)) {
					throw new LiftError('Non-numeric environment slot');
				}
				const funcId = (obj.extra as LiftedExtra | undefined)
					?.parentFunctionId;
				if (funcId == null) {
					throw new LiftError(
						'Missing parentFunctionId on %expectEnvironment',
					);
				}
				const objectPath = member.get('object');
				if (!objectPath.isCallExpression()) return;
				const [envArgPath] = objectPath.get('arguments');
				const [envArg] = obj.arguments;
				const recoveredEnvArg = envArgPath?.isIdentifier()
					? assignedEnvironmentLookupForUse(
						envArgPath,
						(assignment) =>
							recoveredProtectedEnvironmentAssignments.add(
								assignment.node,
							),
					)
					: undefined;
				if (recoveredEnvArg != null) {
					environmentIdentity.scopeRecoveredHandles++;
				}
				const resolvedEnvArg = recoveredEnvArg ?? envArg;
				const env = resolveEnvToEnvironment(
					resolvedEnvArg,
					funcId,
					member.scope,
				);
				recordEnvironmentHandleOutcome(envArgPath, env);
				if (!env) {
					environmentIdentity.unresolvedSlots++;
					return;
				}
				if (env.site == null) environmentIdentity.unresolvedSlots++;
				else {
					environmentIdentity.resolvedSlots++;
					if (t.isNode(resolvedEnvArg)) {
						tagStorageLocation(resolvedEnvArg, {
							kind: 'environment-handle',
							environment: env.site,
						});
					}
					if (t.isNode(envArg)) {
						tagStorageLocation(envArg, {
							kind: 'environment-handle',
							environment: env.site,
						});
					}
				}
				const slot = t.identifier(env.slotName(slotNode.value));
				if (env.site == null) environmentIdentity.slotsWithoutSite++;
				else environmentIdentity.slotsTagged++;
				member.replaceWith(
					env.site == null ? slot : tagStorageLocation(slot, {
						kind: 'environment-slot',
						environment: env.site,
						slot: slotNode.value,
					}),
				);
			},
		},
		AssignmentExpression: {
			exit(assign: NodePath<t.AssignmentExpression>) {
				if (assign.node.operator !== '=') return;
				if (!t.isMemberExpression(assign.node.left)) return;
				const lhs = assign.node.left;
				if (!lhs.computed) return;
				if (
					!t.isCallExpression(lhs.object) ||
					!t.isV8IntrinsicIdentifier(lhs.object.callee, {
						name: 'expectEnvironment',
					})
				) return;
				const slotNode = lhs.property;
				if (!t.isNumericLiteral(slotNode)) {
					throw new LiftError('Non-numeric environment slot');
				}
				const funcId = (lhs.object.extra as LiftedExtra | undefined)
					?.parentFunctionId;
				if (funcId == null) {
					throw new LiftError(
						'Missing parentFunctionId on %expectEnvironment',
					);
				}
				const leftPath = assign.get('left');
				if (!leftPath.isMemberExpression()) return;
				const objectPath = leftPath.get('object');
				if (!objectPath.isCallExpression()) return;
				const [envArgPath] = objectPath.get('arguments');
				const [envArg] = lhs.object.arguments;
				const recoveredEnvArg = envArgPath?.isIdentifier()
					? assignedEnvironmentLookupForUse(
						envArgPath,
						(assignment) =>
							recoveredProtectedEnvironmentAssignments.add(
								assignment.node,
							),
					)
					: undefined;
				if (recoveredEnvArg != null) {
					environmentIdentity.scopeRecoveredHandles++;
				}
				const resolvedEnvArg = recoveredEnvArg ?? envArg;
				const env = resolveEnvToEnvironment(
					resolvedEnvArg,
					funcId,
					assign.scope,
				);
				recordEnvironmentHandleOutcome(envArgPath, env);
				if (!env) {
					environmentIdentity.unresolvedSlots++;
					return;
				}
				if (env.site == null) environmentIdentity.unresolvedSlots++;
				else {
					environmentIdentity.resolvedSlots++;
					if (t.isNode(resolvedEnvArg)) {
						tagStorageLocation(resolvedEnvArg, {
							kind: 'environment-handle',
							environment: env.site,
						});
					}
					if (t.isNode(envArg)) {
						tagStorageLocation(envArg, {
							kind: 'environment-handle',
							environment: env.site,
						});
					}
				}
				const slot = t.identifier(env.slotName(slotNode.value));
				if (env.site == null) environmentIdentity.slotsWithoutSite++;
				else environmentIdentity.slotsTagged++;
				assign.replaceWith(
					t.assignmentExpression(
						'=',
						env.site == null ? slot : tagStorageLocation(slot, {
							kind: 'environment-slot',
							environment: env.site,
							slot: slotNode.value,
						}),
						assign.node.right,
					),
				);
			},
		},
		VariableDeclaration(decn) {
			if (decn.node.kind != 'var') return;
			for (const decl of decn.get('declarations')) {
				if (!decl.node.extra?.isDeclaredGlobal) continue;
				for (const id of identifiersInPattern(decl.node.id)) {
					const binding = decl.scope.getBinding(id.name);
					if (!binding) continue;

					declaredGlobals.add(id.name);
				}
			}
		},
		Identifier(id) {
			if (id.node.extra?.isReferencedGlobal) {
				referencedGlobals.add(id.node.name);
			}
		},
		ExpressionStatement(stmt) {
			const rawExpression = stmt.node.expression;
			if (
				stmt.parentPath?.isProgram() &&
				t.isAssignmentExpression(rawExpression, {
					operator: '=',
				}) &&
				t.isMemberExpression(rawExpression.left, {
					computed: false,
				}) &&
				t.isIdentifier(rawExpression.left.object, {
					name: 'global',
				}) &&
				t.isIdentifier(rawExpression.left.property) &&
				t.isFunctionExpression(rawExpression.right) &&
				rawExpression.right.id?.name ===
					rawExpression.left.property.name
			) {
				const name = rawExpression.left.property.name;
				declaredGlobals.add(name);
				inferredFunctionGlobals.add(name);
			}
			if (
				t.isCallExpression(rawExpression) &&
				t.isV8IntrinsicIdentifier(rawExpression.callee, {
					name: 'ThrowIfThisInitialized',
				})
			) {
				const [arg] = rawExpression.arguments;
				if (t.isIdentifier(arg, { name: '__hermes_empty__' })) {
					stmt.remove();
					return;
				}
			}

			const expression = stmt.get('expression');
			if (!expression.isAssignmentExpression()) return;
			const update = assignmentUpdateExpression(expression.node);
			if (update) {
				expression.replaceWith(update);
				return;
			}

			const compound = toCompoundAssignment(
				expression.node as t.AssignmentExpression,
			);
			if (compound) {
				expression.replaceWith(compound);
				return;
			}
		},
	});
	removeDeadRecoveredProtectedEnvironmentHandles(
		wrapped,
		recoveredProtectedEnvironmentAssignments,
	);
	const slotPlacement = placeEnvironmentSlotsInTree(wrapped.program);
	environmentIdentity.slotPlacementAnalysed += slotPlacement.analysed;
	environmentIdentity.slotPlacementLocalized += slotPlacement.localized;
	environmentIdentity.slotPlacementPlaced += slotPlacement.placed;
	environmentIdentity.slotPlacementUnresolved += slotPlacement.unresolved;
	environmentIdentity.slotPlacementCaptured += slotPlacement.captured;
	environmentIdentity.slotDeclarationsTagged +=
		slotPlacement.declarationsTagged;
	environmentIdentity.slotDeclarationsUnresolved +=
		slotPlacement.textualDeclarationsUnresolved;

	normalizeDuplicateRegisterDeclarations(wrapped);
	traverse(wrapped, {
		Program(path) {
			reduceForAwaitLoopsInBody(path.node.body);
			cleanupEnvironmentBody(path);
		},
		Function(path) {
			const bodyPath = path.get('body');
			if (bodyPath.isBlockStatement()) {
				hoistYieldStarCompletion(bodyPath.node.body);
				reduceForAwaitLoopsInBody(bodyPath.node.body);
				cleanupEnvironmentBody(bodyPath);
				if (
					path.isFunctionExpression() ||
					path.isFunctionDeclaration()
				) {
					hoistInitialIteratorDestructuredFunctionParams(
						path.node,
					);
					hoistDestructuredFunctionParams(path.node);
				}
			}
		},
		CallExpression(call) {
			liftHermesES6Class(call);
		},
		ObjectProperty: {
			exit(prop) {
				const key = prop.get('key');
				const value = prop.get('value');

				if (value.isFunctionExpression()) {
					const id = value.get('id');
					if (
						key.isIdentifier() &&
						(!id.hasNode() ||
							id.isIdentifier({ name: key.node.name }))
					) {
						prop.replaceWith(t.objectMethod(
							'method',
							key.node,
							value.node.params,
							value.node.body,
							false,
							value.node.generator,
							value.node.async,
						));
						return;
					} else if (!id.hasNode() && key.isExpression()) {
						prop.replaceWith(t.objectMethod(
							'method',
							key.node,
							value.node.params,
							value.node.body,
							prop.node.computed,
							value.node.generator,
							value.node.async,
						));
					}
				}

				if (!key.isExpression() && !key.isIdentifier()) return;

				if (!value.isCallExpression()) return;
				if (
					value.get('callee').isV8IntrinsicIdentifier({
						name: 'asGetterSetter',
					})
				) {
					const args = value.get('arguments');
					if (args.length !== 2) return;
					const [getter, setter] = args;
					if (
						!getter.isFunctionExpression() &&
						!isUndefinedNode(getter.node)
					) return;
					if (
						!setter.isFunctionExpression() &&
						!isUndefinedNode(setter.node)
					) return;
					const replacement = [];
					if (getter.isFunctionExpression()) {
						replacement.push(t.objectMethod(
							'get',
							t.cloneNode(key.node, true),
							getter.node.params.map((param) =>
								t.cloneNode(param, true)
							),
							t.cloneNode(getter.node.body, true),
							prop.node.computed,
							getter.node.generator,
							getter.node.async,
						));
					}
					if (setter.isFunctionExpression()) {
						replacement.push(t.objectMethod(
							'set',
							t.cloneNode(key.node, true),
							setter.node.params.map((param) =>
								t.cloneNode(param, true)
							),
							t.cloneNode(setter.node.body, true),
							prop.node.computed,
							setter.node.generator,
							setter.node.async,
						));
					}

					prop.replaceWithMultiple(replacement);
				} else if (
					value.get('callee').isV8IntrinsicIdentifier({
						name: 'asNamedObjectMethod',
					})
				) {
					const args = value.get('arguments');
					if (args.length !== 1) return;
					const [func] = args;
					if (!func.isFunctionExpression()) return;
					prop.replaceWith(t.objectMethod(
						'method',
						key.node,
						func.node.params,
						func.node.body,
						prop.node.computed,
						func.node.generator,
						func.node.async,
					));
				}
			},
		},
	});

	traverse.cache.clear();

	normalizeDuplicateRegisterDeclarations(wrapped);
	traverse(wrapped, {
		MemberExpression(memberExpr) {
			if (
				!memberExpr.get('object').isIdentifier({ name: 'global' })
			) {
				return;
			}

			const id = memberExpr.get('property');
			if (!id.isIdentifier()) return;
			if (
				!declaredGlobals.has(id.node.name) &&
				!referencedGlobals.has(id.node.name)
			) return;

			memberExpr.replaceWith(id.node);
		},
		CallExpression: {
			exit: cleanupClassDefinitionClosure,
		},
		VariableDeclarator: cleanupClassSuper,
		IfStatement: cleanupGuardedNaturalLoops,
	});

	normalizeDuplicateRegisterDeclarations(wrapped);
	environmentIdentity.postAliasObjectFolds +=
		destructureGeneratedObjectPropertyAliases(wrapped);

	normalizeDuplicateRegisterDeclarations(wrapped);
	insertDeferredEnvironmentDeclarations(wrapped);
	traverse(wrapped, {
		Program(path) {
			cleanupEnvironmentBody(path);
		},
		Function(path) {
			const bodyPath = path.get('body');
			if (bodyPath.isBlockStatement()) {
				cleanupEnvironmentBody(bodyPath);
			}
		},
	});
	const stableAliases = coalesceStableStorageAliases(wrapped);
	environmentIdentity.storageAliasesAnalysed += stableAliases.analysed;
	environmentIdentity.storageAliasesCoalesced += stableAliases.coalesced;
	environmentIdentity.storageRegisterAliasesCoalesced +=
		stableAliases.registerAliasesCoalesced;
	environmentIdentity.storageEnvironmentSlotAliasesCoalesced +=
		stableAliases.environmentSlotAliasesCoalesced;
	environmentIdentity.storageAliasesBlockedByWrite +=
		stableAliases.blockedByWrite;
	environmentIdentity.storageAliasesBlockedByVisibility +=
		stableAliases.blockedByVisibility;
	environmentIdentity.storageAliasesBlockedByLocalMutation +=
		stableAliases.blockedByLocalMutation;
	// Conditional Phis can fold before storage alias coalescing proves that the
	// tested and carried values are one binding. Re-run the same canonical
	// folder now that aliases have their final names (for example `x ?? this`,
	// rather than `x == null ? this : x`).
	refoldPostAliasConditionalValues(wrapped);
	liftGeneratedCallProtocols(wrapped);
	// Last, because the passes above are what strand a handle: while an
	// `%expectEnvironment(handle)[slot]` use survives the handle still has a
	// reader, and only slot placement and alias coalescing rewrite the last of
	// them to an `_env_*` name.
	environmentIdentity.deadLookupHandlesRemoved +=
		removeDeadEnvironmentLookupHandles(wrapped);
	traverse(wrapped, {
		Program(path) {
			environmentIdentity.storageObjectRestsRecovered +=
				cleanupComposedObjectRestInBody(path.node.body);
		},
		Function(path) {
			const body = path.node.body;
			if (!t.isBlockStatement(body)) return;
			environmentIdentity.storageObjectRestsRecovered +=
				cleanupComposedObjectRestInBody(body.body);
		},
	});
	traverse.cache.clear();
	inlineBranchArrayConstructionsToFixpoint(wrapped);
	traverse.cache.clear();
	traverse(wrapped, {
		Program(path) {
			foldConditionalValuesInBody(path.node.body);
		},
		Function(path) {
			const body = path.node.body;
			if (t.isBlockStatement(body)) {
				foldConditionalValuesInBody(body.body);
			}
		},
		CallExpression(path) {
			if (
				t.isV8IntrinsicIdentifier(path.node.callee, {
					name: 'CoerceThisNS',
				}) &&
				path.node.arguments.length === 1 &&
				t.isThisExpression(path.node.arguments[0])
			) {
				path.replaceWith(t.thisExpression());
			}
		},
	});
	traverse.cache.clear();

	// A source buffer can be folded after its consumer has already been visited
	// in statement order (for example #98661). Revisit construction sites until
	// no fold remains rather than leaving an immediately-adjacent helper behind.
	environmentIdentity.postAliasObjectFolds +=
		inlineObjectConstructionsToFixpoint(wrapped);
	traverse.cache.clear();
	inlineBranchArrayConstructionsToFixpoint(wrapped);
	traverse.cache.clear();
	traverse(wrapped, {
		Program(path) {
			foldConditionalValuesInBody(path.node.body);
		},
		Function(path) {
			const body = path.node.body;
			if (t.isBlockStatement(body)) {
				foldConditionalValuesInBody(body.body);
			}
		},
	});
	traverse.cache.clear();
	environmentIdentity.postAliasObjectFolds +=
		inlineObjectConstructionsToFixpoint(wrapped);
	lowerResidualArraySpreadCalls(wrapped);
	traverse.cache.clear();
	traverse(wrapped, {
		Function(path) {
			if (recoverEmbeddedObjectRestForFunction(path)) {
				environmentIdentity.storageObjectRestsRecovered++;
			}
		},
	});
	normalizeDuplicateRegisterDeclarations(wrapped);
	traverse(wrapped, {
		VariableDeclaration(decn) {
			if (postfixUpdateFromToNumericTemp(decn)) {
				return;
			}
		},
		VariableDeclarator(decl) {
			unhoistDeclaredGlobals(decl);
		},
		ExpressionStatement(stmt) {
			if (!stmt.parentPath?.isProgram()) return;
			const expression = stmt.node.expression;
			if (!t.isAssignmentExpression(expression, { operator: '=' })) {
				return;
			}
			if (!t.isIdentifier(expression.left)) return;
			if (!inferredFunctionGlobals.has(expression.left.name)) return;
			if (!t.isFunctionExpression(expression.right)) return;
			if (expression.right.id?.name !== expression.left.name) return;
			stmt.replaceWith(t.functionDeclaration(
				t.cloneNode(expression.left),
				expression.right.params,
				expression.right.body,
				expression.right.generator,
				expression.right.async,
			));
		},
	});
	traverse(wrapped, {
		Program(path) {
			recoverDirectObjectDefaultAliasesInBody(path.node.body);
		},
		Function(path) {
			const body = path.node.body;
			if (t.isBlockStatement(body)) {
				recoverDirectObjectDefaultAliasesInBody(body.body);
			}
		},
	});
	let recoveredDeclaredGlobalDestructuring = 0;
	traverse(wrapped, {
		Program(path) {
			recoveredDeclaredGlobalDestructuring +=
				recoverDeclaredGlobalDestructuringAssignments(
					path.node.body,
					declaredGlobals,
				);
		},
	});
	if (recoveredDeclaredGlobalDestructuring > 0) {
		traverse(wrapped, {
			MemberExpression(memberExpr) {
				if (
					!memberExpr.get('object').isIdentifier({ name: 'global' })
				) {
					return;
				}
				const id = memberExpr.get('property');
				if (!id.isIdentifier()) return;
				if (!declaredGlobals.has(id.node.name)) return;
				memberExpr.replaceWith(id.node);
			},
		});
	}

	// Recursive region emission can expose bytecode-only completion values and
	// copied finalizer continuations at the composed-AST boundary. A bare SSA or
	// environment identifier has no source-level side effect, and statements
	// following an always-abrupt construct are unreachable by construction.
	// Remove both after all binding/environment rewrites so the decision is made
	// on the final syntax rather than on sample-specific text.
	repairPerIterationEnvironmentBindings(wrapped);
	repairCopiedFinalizerContinuations(wrapped);
	declareUnboundGeneratedAssignments(wrapped);
	traverse(wrapped, {
		CallExpression: {
			exit(path) {
				const callee = path.node.callee;
				if (
					!t.isMemberExpression(callee, { computed: false }) ||
					!t.isIdentifier(callee.object) ||
					!t.isIdentifier(callee.property, { name: 'call' })
				) return;
				const receiver = path.node.arguments[0];
				if (
					!t.isIdentifier(receiver) ||
					!isRegisterTempName(receiver.name) ||
					path.scope.getBinding(receiver.name)
				) return;
				path.replaceWith(t.callExpression(
					t.cloneNode(callee.object),
					path.node.arguments.slice(1).map((argument) =>
						t.cloneNode(argument, true)
					),
				));
			},
		},
		ExpressionStatement(path) {
			const expression = path.node.expression;
			if (
				t.isIdentifier(expression) &&
				(
					isRegisterTempName(expression.name) ||
					/^e_\d+$/.test(expression.name) ||
					isEnvironmentSlotName(expression.name)
				)
			) path.remove();
		},
		IfStatement(path) {
			if (!unboundGeneratedUndefinedGuard(path)) return;
			path.remove();
		},
		Program: {
			exit(path) {
				stripUnreachableStatementTail(path.node.body);
			},
		},
		BlockStatement: {
			exit(path) {
				stripUnreachableStatementTail(path.node.body);
			},
		},
	});
	// Receiver cleanup above can make two bytecode copies structurally identical
	// (one may have been emitted as `fn.call(temp, ...)`, the other as `fn(...)`).
	// Re-run the copy repair once on that normalized call shape.
	repairCopiedFinalizerContinuations(wrapped);
	traverse(wrapped, {
		Program: {
			exit(path) {
				stripUnreachableStatementTail(path.node.body);
			},
		},
		BlockStatement: {
			exit(path) {
				stripUnreachableStatementTail(path.node.body);
			},
		},
	});

	if (root.kind === 'file') {
		lowerProgramCompletionReturns(wrapped.program);
		const rootBody = wrapped.program.body as t.Statement[];
		const ret = rootBody.at(-1);
		if (t.isReturnStatement(ret) && ret.argument) {
			rootBody[rootBody.length - 1] = t.expressionStatement(
				ret.argument,
			);
		}
		const completion = rootBody.at(-1);
		if (
			t.isExpressionStatement(completion) &&
			t.isIdentifier(completion.expression) &&
			(
				isRegisterTempName(completion.expression.name) ||
				isEnvironmentSlotName(completion.expression.name)
			)
		) rootBody.pop();
		reportEnvironmentIdentity();
		return wrapped.program;
	}
	reportEnvironmentIdentity();
	return wrapped.program;
}

function statementList(
	statement: t.Statement | null | undefined,
): t.Statement[] {
	if (!statement) return [];
	return t.isBlockStatement(statement) ? statement.body : [statement];
}

function containsConditionalScriptCompletion(
	statements: readonly t.Statement[],
): boolean {
	return statements.some((statement) => {
		if (t.isReturnStatement(statement)) return true;
		if (!t.isIfStatement(statement)) return false;
		return containsConditionalScriptCompletion(
			statementList(statement.consequent),
		) || containsConditionalScriptCompletion(
			statementList(statement.alternate),
		);
	});
}

function cloneStatements(statements: readonly t.Statement[]): t.Statement[] {
	return statements.map((statement) => t.cloneNode(statement, true));
}

/**
 * Lower Hermes script-completion returns without introducing a wrapper scope.
 *
 * A root function is emitted as a Program, but Hermes still terminates it with
 * `Ret`. Conditional returns therefore mean "do not execute the remaining
 * root continuation", not a source-level function return. Distribute that
 * continuation into the non-returning conditional arms and replace the
 * completion return with evaluation of its value.
 *
 * This deliberately handles only straight-line/conditional completion trees.
 * Returns below loops, switches, or exception statements require CFG-level
 * structuring rather than an AST wrapper which would change top-level lexical
 * scope.
 */
export function lowerProgramCompletionReturns(program: t.Program): boolean {
	function lowerList(
		statements: readonly t.Statement[],
		continuation: readonly t.Statement[] = [],
	): t.Statement[] | undefined {
		for (let i = 0; i < statements.length; i++) {
			const statement = statements[i];
			if (t.isReturnStatement(statement)) {
				const prefix = cloneStatements(statements.slice(0, i));
				if (statement.argument) {
					prefix.push(t.expressionStatement(
						t.cloneNode(statement.argument, true),
					));
				}
				return prefix;
			}
			if (!t.isIfStatement(statement)) continue;

			const consequent = statementList(statement.consequent);
			const alternate = statementList(statement.alternate);
			const consequentCompletes = containsConditionalScriptCompletion(
				consequent,
			);
			const alternateCompletes = containsConditionalScriptCompletion(
				alternate,
			);
			if (!consequentCompletes && !alternateCompletes) continue;

			const tail = [
				...cloneStatements(statements.slice(i + 1)),
				...cloneStatements(continuation),
			];
			const continuingConsequent = [
				...cloneStatements(consequent),
				...cloneStatements(tail),
			];
			const continuingAlternate = [
				...cloneStatements(alternate),
				...cloneStatements(tail),
			];
			const loweredConsequent = consequentCompletes
				? lowerList(consequent, tail)
				: lowerList(continuingConsequent) ?? continuingConsequent;
			const loweredAlternate = alternateCompletes
				? lowerList(alternate, tail)
				: lowerList(continuingAlternate) ?? continuingAlternate;
			if (!loweredConsequent || !loweredAlternate) return undefined;

			return [
				...cloneStatements(statements.slice(0, i)),
				t.ifStatement(
					t.cloneNode(statement.test, true),
					t.blockStatement(loweredConsequent),
					t.blockStatement(loweredAlternate),
				),
			];
		}
		return undefined;
	}

	const lowered = lowerList(program.body as t.Statement[]);
	if (!lowered) return false;
	program.body = lowered;
	return true;
}

const metroFragmentPlaceholderPattern = /\b__ARES_METRO_FRAGMENT_(\d+)__\b/g;

/**
 * Globals shared across the whole program.
 *
 * Two halves with different provenance: the bytecode half (`TryGetById` and
 * `DeclareGlobalVar` across every function) is a pure function of the bytes and
 * arrives precomputed, while the second half depends on how the root function
 * happened to lift and has to be walked here.
 */
function collectSharedGlobalNames(
	derived: BytecodeDerivedPlan,
	root: IRFunction,
): Set<string> {
	const names = new Set<string>(derived.bytecodeGlobalNames);

	const entry = root.blocks.get(root.entryAddress);
	if (!entry) return names;

	t.traverseFast(t.program(entry.body as t.Statement[]), (node) => {
		if (
			t.isCallExpression(node) &&
			t.isV8IntrinsicIdentifier(node.callee, { name: 'TryGetById' })
		) {
			const property = node.arguments[1];
			if (t.isStringLiteral(property)) names.add(property.value);
			return;
		}
		if (
			t.isMemberExpression(node) &&
			t.isIdentifier(node.object, { name: 'global' })
		) {
			const property = node.property;
			if (!node.computed && t.isIdentifier(property)) {
				names.add(property.name);
			} else if (node.computed && t.isStringLiteral(property)) {
				names.add(property.value);
			}
			return;
		}
		if (t.isVariableDeclarator(node) && node.extra?.isDeclaredGlobal) {
			for (const id of identifiersInPattern(node.id)) names.add(id.name);
		}
	});
	return names;
}

function isMetroFactoryCall(node: t.CallExpression): boolean {
	return t.isIdentifier(node.callee, { name: '__d' }) &&
		node.arguments.length >= 2 &&
		(t.isNumericLiteral(node.arguments[1]) ||
			t.isStringLiteral(node.arguments[1]));
}

/**
 * A store restricted to one composition unit's subtree.
 *
 * The composition forest gives each function a single parent, so the subtree
 * under a Metro factory is disjoint from every other factory's. Restricting a
 * unit to its own subtree is what makes units independent enough to run apart:
 * a unit that reaches outside its subtree would be reading state another unit
 * owns.
 *
 * Consumption still propagates to the shared store, because a function inlined
 * into one module must not also be inlined into the root program.
 */
class SubtreeIRFunctionStore implements IRFunctionStore {
	#consumed = new Set<FunctionId>();

	constructor(
		readonly inner: IRFunctionStore,
		readonly owned: ReadonlySet<FunctionId>,
	) {}

	has(functionId: FunctionId): boolean {
		return this.inner.has(functionId);
	}

	get(functionId: FunctionId): IRFunction | undefined {
		return this.inner.get(functionId);
	}

	/**
	 * Consuming is what has to stay local. Reading does not: a function
	 * referenced from more than one place is never consumed -- it is cloned
	 * through `cloneNestedFunctionRef` -- and belongs to no single subtree, so
	 * restricting reads would leave those closures uncomposed.
	 */
	delete(functionId: FunctionId): boolean {
		if (!this.owned.has(functionId)) {
			return false;
		}
		if (!this.inner.has(functionId)) return false;
		this.#consumed.add(functionId);
		return this.inner.delete(functionId);
	}

	set(functionId: FunctionId, func: IRFunction): void {
		this.#consumed.delete(functionId);
		this.inner.set(functionId, func);
	}

	relift(functionId: FunctionId): IRFunction | undefined {
		return this.inner.relift(functionId);
	}

	/** The functions this unit consumed, for a caller that owns the store. */
	get consumedIds(): ReadonlySet<FunctionId> {
		return this.#consumed;
	}
}

/** Everything composing `functionId` can reach, owned or merely read. */
function referenceClosure(
	functionId: FunctionId,
	references: ReadonlyMap<FunctionId, FunctionId[]>,
): Set<FunctionId> {
	const reachable = new Set<FunctionId>([functionId]);
	const pending = [functionId];
	while (pending.length > 0) {
		for (const target of references.get(pending.pop()!) ?? []) {
			if (reachable.has(target)) continue;
			reachable.add(target);
			pending.push(target);
		}
	}
	return reachable;
}

/** The functions a composition unit rooted at `functionId` owns. */
function subtreeFunctionIds(
	functionId: FunctionId,
	childrenByParent: ReadonlyMap<FunctionId, FunctionId[]>,
): Set<FunctionId> {
	const owned = new Set<FunctionId>([functionId]);
	const pending = [functionId];
	while (pending.length > 0) {
		for (const child of childrenByParent.get(pending.pop()!) ?? []) {
			if (owned.has(child)) continue;
			owned.add(child);
			pending.push(child);
		}
	}
	return owned;
}

/** Invert `parentFunctions` so a subtree can be walked downwards. */
function compositionChildren(
	plan: CompositionPlan,
): Map<FunctionId, FunctionId[]> {
	const children = new Map<FunctionId, FunctionId[]>();
	for (const [child, parent] of plan.parentFunctions) {
		const siblings = children.get(parent);
		if (siblings) siblings.push(child);
		else children.set(parent, [child]);
	}
	return children;
}

/** What a Metro `__d` factory call composes. */
interface MetroFactoryUnit {
	/** The function the factory closure creates. */
	functionId: FunctionId;
	/** The environment the closure captures at its creation site. */
	envArg: t.Node;
}

/**
 * Resolve a Metro factory call to the function it composes, or null when the
 * call is not one this pipeline can compose on its own.
 *
 * Separate from the composing so that a caller can enumerate the units of work
 * without doing any of it -- which is what distributing composition needs.
 */
function resolveMetroFactoryUnit(
	node: t.CallExpression,
	plan: CompositionPlan,
	functions: IRFunctionStore,
): MetroFactoryUnit | null {
	if (!isMetroFactoryCall(node)) return null;
	const factoryCreation = node.arguments[0];
	if (
		!t.isCallExpression(factoryCreation) ||
		!t.isV8IntrinsicIdentifier(factoryCreation.callee, {
			name: 'CreateClosure',
		})
	) return null;
	const functionId = extractFunctionRef(factoryCreation.arguments[0]);
	if (
		functionId == null ||
		!plan.safelyNestedFunctions.has(functionId) ||
		!functions.has(functionId)
	) return null;
	const factory = functions.get(functionId);
	// A factory whose own body did not reduce to a single block is not a module
	// boundary this pass can take apart.
	if (
		!factory ||
		[...factory.reachableBlocksFromEntry()].some((address) =>
			address !== factory.entryAddress
		)
	) return null;
	const envArg = factoryCreation.arguments[1];
	if (!envArg || !t.isNode(envArg)) return null;
	return { functionId, envArg };
}

/**
 * Visit every Metro factory call under the entry body, in the order the spill
 * composes them: top-level statements first, then any nested call the first
 * pass did not claim.
 *
 * `visit` returns whether it claimed the call. An unclaimed one is offered
 * again by the nested sweep, which is what the original two-phase walk did.
 * The sweep runs after the first pass has already rewritten the body, so it
 * sees exactly the calls that survived it.
 */
function forEachMetroFactoryCall(
	entryBody: t.Statement[],
	visit: (call: t.CallExpression, statementIndex: number | null) => boolean,
): void {
	const processed = new WeakSet<t.CallExpression>();
	for (let index = 0; index < entryBody.length; index++) {
		const statement = entryBody[index];
		if (!t.isExpressionStatement(statement)) continue;
		const node = statement.expression;
		if (!t.isCallExpression(node) || !isMetroFactoryCall(node)) continue;
		if (visit(node, index)) processed.add(node);
	}
	t.traverseFast(t.program(entryBody), (node) => {
		if (
			!t.isCallExpression(node) ||
			processed.has(node) ||
			!isMetroFactoryCall(node)
		) return;
		visit(node, null);
	});
}

/**
 * A Metro factory call that *might* be a composition unit.
 *
 * Splitting candidate collection from resolution is what lets composition start
 * before lifting finishes. Everything here is decided from the entry body and
 * the bytecode-derived plan, so it is known as soon as function #0 is lifted --
 * whereas the last condition a real unit has to meet, that the factory's own
 * body reduced to a single block, needs the factory itself lifted and is
 * checked at dispatch.
 */
interface MetroFactoryCandidate extends MetroFactoryUnit {
	call: t.CallExpression;
}

/**
 * Collect candidates in the order the spill composes them.
 *
 * Order and de-duplication match the original single-pass enumeration exactly:
 * top-level statements first, then a nested sweep, first occurrence of a
 * function id wins. That equivalence holds because resolution is deterministic
 * for a given function id -- a candidate that fails the deferred check would
 * have failed on every occurrence, and one that passes is claimed at its first.
 */
function collectMetroFactoryCandidates(
	entryBody: t.Statement[],
	plan: CompositionPlan,
): MetroFactoryCandidate[] {
	const byFunctionId = new Map<FunctionId, MetroFactoryCandidate>();
	const order: MetroFactoryCandidate[] = [];
	forEachMetroFactoryCall(entryBody, (node) => {
		if (!isMetroFactoryCall(node)) return false;
		const factoryCreation = node.arguments[0];
		if (
			!t.isCallExpression(factoryCreation) ||
			!t.isV8IntrinsicIdentifier(factoryCreation.callee, {
				name: 'CreateClosure',
			})
		) return false;
		const functionId = extractFunctionRef(factoryCreation.arguments[0]);
		if (
			functionId == null ||
			!plan.safelyNestedFunctions.has(functionId) ||
			byFunctionId.has(functionId)
		) return false;
		const envArg = factoryCreation.arguments[1];
		if (!envArg || !t.isNode(envArg)) return false;
		const candidate: MetroFactoryCandidate = {
			functionId,
			envArg,
			call: node,
		};
		byFunctionId.set(functionId, candidate);
		order.push(candidate);
		return true;
	});
	return order;
}

/**
 * The condition a candidate can only be judged on once it is lifted.
 *
 * A factory whose own body did not reduce to a single block is not a module
 * boundary this pass can take apart; it stays in the root program.
 */
function candidateComposes(
	candidate: MetroFactoryCandidate,
	functions: IRFunctionStore,
): boolean {
	if (!functions.has(candidate.functionId)) return false;
	const factory = functions.get(candidate.functionId);
	if (!factory) return false;
	return ![...factory.reachableBlocksFromEntry()].some((address) =>
		address !== factory.entryAddress
	);
}

/**
 * Lift the file and compose its Metro modules at the same time.
 *
 * The two phases used to be separated by a barrier: every function in the
 * bundle was lifted, and only then did composition begin. That barrier was
 * never a dependency -- a module needs its own reference closure lifted and
 * nothing else -- it was just the shape the code had. On a bundle where lifting
 * runs for hours, it meant every core sat idle through a composition phase that
 * could have been overlapping with the lifting all along.
 *
 * So: function #0 is lifted first, because enumerating the modules needs it.
 * Its module boundaries then reorder the remaining lift queue so each module's
 * dependencies complete early, and a module is dispatched to a compose worker
 * the moment the last id in its closure is committed to the store.
 *
 * Fragment indices still follow source order regardless of completion order,
 * and the placeholder rewrite still happens here, because it mutates the entry
 * body that only this thread owns.
 */
async function liftAndComposeMetroParallel(
	coldFile: HBCFile,
	cold: ColdStore,
	spillPath: string,
	functions: IRFunctionStore,
	plan: CompositionPlan,
	derived: BytecodeDerivedPlan,
	options: LiftFileParallelOptions,
	/**
	 * True when the store already holds every snapshot, so there is no lifting
	 * to overlap with and every module is composable immediately.
	 */
	alreadyLifted: boolean,
	composeBatchSize = 8,
): Promise<
	{
		functionIds: FunctionId[];
		fragments: MetroFragmentSource;
		failed: number;
		environmentIdentity: EnvironmentIdentityDiagnostics;
		blockedFunctionIds: ReadonlySet<FunctionId>;
	}
> {
	const functionIds = selectedFunctionIds(coldFile, options.functionIds);
	// Seeded from the store, not from a flag: a resumed run has to treat
	// already-committed functions as satisfied dependencies, or every module
	// waits forever on ids no worker is going to lift again.
	const outstanding = alreadyLifted
		? []
		: unliftedFunctionIds(cold, functionIds);
	// Set difference, not `outstanding.includes` -- that is O(n^2), which on
	// 127k functions is 16 billion comparisons before a single lift starts.
	const pending = new Set<FunctionId>(outstanding);
	const written = new Set<FunctionId>(
		functionIds.filter((id) => !pending.has(id)),
	);
	if (!alreadyLifted && written.size > 0) {
		reportProgress(
			`[lift] resuming: ${written.size} of ${functionIds.length} ` +
				'functions already in the cold store',
		);
		const previous = readLiftFailures(cold);
		if (previous.size > 0) {
			writeDiagnostic(
				`[lift] ${previous.size} function(s) failed to lift on a ` +
					'previous run and will be re-attempted: ' +
					[...previous.keys()].toSorted((a, b) => a - b)
						.map((id) => `#${id}`).join(', '),
			);
		}
	}

	let candidates: MetroFactoryCandidate[] = [];
	let globalNames: string[] = [];
	/**
	 * The root, captured at enumeration and restored at the end.
	 *
	 * Held rather than re-read, because the consumption replay above it deletes
	 * ids from the store, and re-reading afterwards would quietly turn "root was
	 * consumed" into "root is gone" instead of putting it back.
	 */
	let rootFunction: IRFunction | undefined;
	/** Closure ids a candidate is still waiting on. */
	const waitingOn = new Map<FunctionId, Set<FunctionId>>();
	/** Reverse index, so a written id only touches the candidates that want it. */
	const wantedBy = new Map<FunctionId, FunctionId[]>();
	const candidateById = new Map<FunctionId, MetroFactoryCandidate>();
	const ready: MetroFactoryCandidate[] = [];

	const results: {
		fragments: FunctionId[];
		consumed: FunctionId[];
		environmentIdentity: EnvironmentIdentityDiagnostics;
	}[] = [];
	const composing = new Set<Promise<void>>();
	/** Modules whose worker-side composition failed, with the reason. */
	const composeFailures = new Map<FunctionId, string>();
	let liftFinished = false;
	let enumerated = false;

	const dispatchReady = (drain: boolean) => {
		void drain;
		while (ready.length > 0) {
			const batch = ready.splice(0, composeBatchSize);
			const readable: FunctionId[] = [];
			const shipped = new Set<FunctionId>();
			for (const candidate of batch) {
				for (
					const id of referenceClosure(
						candidate.functionId,
						derived.closureReferences,
					)
				) {
					if (shipped.has(id)) continue;
					shipped.add(id);
					readable.push(id);
				}
			}
			const run = pool.enqueueCompose(
				batch.map(({ functionId, envArg }) => ({
					functionId,
					envArg,
				})),
				readable,
				globalNames,
				candidates.length,
			)
				.then((result) => {
					results.push(result);
					for (const failure of result.failed) {
						composeFailures.set(
							failure.functionId,
							`parallel worker failed: ${failure.message}`,
						);
					}
				})
				.catch((error: unknown) => {
					// Worker-side splitting handles ordinary batch-local state
					// collisions. Reaching this catch means the worker could not
					// recover at unit granularity, so keep the affected roots raw
					// and let final root composition skip those factory ids.
					const reason = error instanceof Error
						? error.message
						: String(error);
					const ids = batch.map((c) => c.functionId);
					writeDiagnostic(
						`[lift] compose batch [${
							ids.map((id) => `#${id}`).join(', ')
						}] failed and will be left uncomposed: ${reason}`,
					);
					for (const id of ids) composeFailures.set(id, reason);
				})
				.finally(() => {
					composing.delete(run);
				});
			composing.add(run);
		}
	};

	const enumerate = () => {
		enumerated = true;
		const root = functions.get(0);
		const entry = root?.blocks.get(0);
		if (!root || !entry) return;
		rootFunction = root;
		candidates = collectMetroFactoryCandidates(
			entry.body as t.Statement[],
			plan,
		);
		if (candidates.length === 0) return;
		globalNames = [...collectSharedGlobalNames(derived, root)];

		const closureOrder: FunctionId[] = [];
		for (const candidate of candidates) {
			candidateById.set(candidate.functionId, candidate);
			const closure = referenceClosure(
				candidate.functionId,
				derived.closureReferences,
			);
			const outstanding = new Set<FunctionId>();
			for (const id of closure) {
				closureOrder.push(id);
				if (written.has(id)) continue;
				outstanding.add(id);
				let wanters = wantedBy.get(id);
				if (!wanters) wantedBy.set(id, wanters = []);
				wanters.push(candidate.functionId);
			}
			waitingOn.set(candidate.functionId, outstanding);
			if (
				outstanding.size === 0 &&
				candidateComposes(candidate, functions)
			) {
				ready.push(candidate);
			}
		}
		// Module dependencies first, in module order, so modules become
		// composable roughly as fast as the bundle can produce them.
		pool.prioritise(closureOrder);
	};

	const workerCount = workerCountFor(functionIds.length, options);
	const pool = new ParallelWorkPool(
		spillPath,
		{ cfgReducer: options.cfgReducer },
		workerCount,
		liftBatchSize(options),
		recycleAfterBatches(options),
		derived.functionBytecodeLengths,
		parallelMemoryBudget(workerCount, options),
		(ids: FunctionId[], failed: readonly FunctionId[]) => {
			// Committed by another thread, so this thread's read snapshot
			// predates it: refresh before anything here reads the store, or a
			// batch is invisible to composition and to the summary collector.
			cold.releaseReader();
			// A function that could not be lifted still *resolves*: modules
			// waiting on it must be released, or one unliftable function
			// silently hangs every module whose closure reaches it. It simply
			// resolves to absent, and composition leaves the closure raw.
			const settled = failed.length === 0 ? ids : [...ids, ...failed];
			for (const id of settled) written.add(id);
			if (!enumerated && written.has(0)) enumerate();
			for (const id of settled) {
				const wanters = wantedBy.get(id);
				if (!wanters) continue;
				wantedBy.delete(id);
				for (const wanter of wanters) {
					const outstanding = waitingOn.get(wanter);
					if (!outstanding) continue;
					outstanding.delete(id);
					if (outstanding.size > 0) continue;
					waitingOn.delete(wanter);
					const candidate = candidateById.get(wanter)!;
					if (candidateComposes(candidate, functions)) {
						ready.push(candidate);
					}
				}
			}
			dispatchReady(liftFinished);
		},
	);

	if (alreadyLifted) {
		enumerate();
		dispatchReady(true);
	} else {
		pool.enqueue(outstanding);
		// Enumeration needs the entry body, so #0 jumps the queue; everything
		// else keeps lifting behind it rather than waiting for it. On a resumed
		// run #0 is usually already committed, and `enumerate` then fires off
		// the first `written` batch instead.
		pool.prioritise([0]);
		if (written.has(0)) enumerate();
	}
	await pool.run();
	await reportLiftFailures(pool, cold, outstanding);
	liftFinished = true;

	// Anything still waiting was outside every module's closure, or the module
	// was never composable; drain whatever is ready and let the root program
	// take the rest.
	dispatchReady(true);
	while (composing.size > 0) {
		await Promise.race(composing);
		dispatchReady(true);
	}
	if (composeFailures.size > 0) {
		writeDiagnostic(
			`[lift] ${composeFailures.size} module(s) could not be composed ` +
				'in a worker and will be left uncomposed:',
		);
		for (
			const id of [...composeFailures.keys()].toSorted((a, b) => a - b)
		) {
			writeDiagnostic(
				`[lift]   module #${id}: ${composeFailures.get(id)}`,
			);
		}
	}

	const composedIds = new Set(results.flatMap((result) => result.fragments));
	const fragmentIds: FunctionId[] = [];
	for (const candidate of candidates) {
		if (!composedIds.has(candidate.functionId)) continue;
		const index = fragmentIds.length;
		fragmentIds.push(candidate.functionId);
		candidate.call.arguments[0] = t.identifier(
			`__ARES_METRO_FRAGMENT_${index}__`,
		);
	}
	for (const result of results) {
		for (const functionId of result.consumed) functions.delete(functionId);
	}
	if (rootFunction) functions.set(0, rootFunction);
	const environmentIdentity = emptyEnvironmentIdentityDiagnostics();
	for (const result of results) {
		addEnvironmentIdentityDiagnostics(
			environmentIdentity,
			result.environmentIdentity,
		);
	}

	return {
		functionIds,
		failed: pool.liftFailures.size,
		environmentIdentity,
		blockedFunctionIds: new Set(composeFailures.keys()),
		fragments: {
			get length() {
				return fragmentIds.length;
			},
			take(index) {
				const functionId = fragmentIds[index];
				if (functionId == null) return undefined;
				return cold.frag.get(functionId) as string | undefined;
			},
		},
	};
}

/**
 * Compose already-lifted Metro modules into fragment source.
 *
 * Takes the units and a store that already holds their functions, so it does no
 * lifting of its own: a worker is given the subtree it needs rather than
 * rebuilding it, which is the difference between moving the work and doing it
 * twice.
 */
export function composeMetroModuleUnits(
	file: HBCFile,
	units: readonly MetroFactoryUnit[],
	functions: IRFunctionStore,
	plan: CompositionPlan,
	globalNames: ReadonlySet<string>,
	onProgress?: (functionId: FunctionId) => void,
): {
	fragments: [FunctionId, string][];
	consumed: FunctionId[];
	environmentIdentity: EnvironmentIdentityDiagnostics;
} {
	const childrenByParent = compositionChildren(plan);
	const fragments: [FunctionId, string][] = [];
	const consumed = new Set<FunctionId>();
	const environmentIdentity = emptyEnvironmentIdentityDiagnostics();
	for (const unit of units) {
		const unitStore = new SubtreeIRFunctionStore(
			functions,
			subtreeFunctionIds(unit.functionId, childrenByParent),
		);
		const program = composeLiftedFile(
			file,
			unitStore,
			plan,
			{
				functionId: unit.functionId,
				kind: 'function',
				creationEnv: {
					envArg: t.cloneNode(unit.envArg as t.Node, true),
					callerFuncId: 0,
				},
				globalNames,
			},
			environmentIdentity,
		);
		const factoryExpression = program.body
			.filter(t.isExpressionStatement)
			.map((statement) => statement.expression)
			.find(t.isFunctionExpression);
		if (!factoryExpression) {
			throw new LiftError(
				`Metro factory #${unit.functionId} did not compose to a function`,
			);
		}
		fragments.push([unit.functionId, generate(factoryExpression).code]);
		for (const id of unitStore.consumedIds) consumed.add(id);
		// Per module, not per batch: the path cache is what makes composition
		// memory-hungry, and a worker holding a batch's worth of it is what
		// multiplied into an out-of-memory kill.
		traverse.cache.clear();
		onProgress?.(unit.functionId);
	}
	return {
		fragments,
		consumed: [...consumed],
		environmentIdentity,
	};
}

/** Rebuild a store from snapshots a caller shipped in. */
export function storeFromSnapshots(
	file: HBCFile,
	snapshots: readonly [FunctionId, IRFunctionSnapshot][],
	options: IRFunctionOptions,
): IRFunctionStore {
	const functions = new Map<FunctionId, IRFunction>();
	for (const [functionId, snapshot] of snapshots) {
		functions.set(functionId, IRFunction.fromSnapshot(file, snapshot));
	}
	return new EagerIRFunctionStore(file, functions, options);
}

function spillMetroModuleFactories(
	file: HBCFile,
	functions: IRFunctionStore,
	plan: CompositionPlan,
	derived: BytecodeDerivedPlan,
	extractor?: IncrementalMetroExtractor,
): string[] {
	const root = functions.get(0);
	const entry = root?.blocks.get(0);
	if (!root || !entry) return [];
	const globalNames = collectSharedGlobalNames(derived, root);

	const childrenByParent = compositionChildren(plan);
	const fragments: string[] = [];
	const composeFactory = (
		node: t.CallExpression,
	): t.FunctionExpression | undefined => {
		const unit = resolveMetroFactoryUnit(node, plan, functions);
		if (!unit) return;
		const { functionId, envArg } = unit;
		const unitStore = new SubtreeIRFunctionStore(
			functions,
			subtreeFunctionIds(functionId, childrenByParent),
		);
		const program = composeLiftedFile(file, unitStore, plan, {
			functionId,
			kind: 'function',
			creationEnv: {
				envArg: t.cloneNode(envArg, true),
				callerFuncId: 0,
			},
			globalNames,
		});
		const factoryExpression = program.body
			.filter(t.isExpressionStatement)
			.map((statement) => statement.expression)
			.find(t.isFunctionExpression);
		if (!factoryExpression) {
			throw new LiftError(
				`Metro factory #${functionId} did not compose to a function`,
			);
		}
		return factoryExpression;
	};

	const replaceWithFragment = (
		node: t.CallExpression,
		factoryExpression: t.FunctionExpression,
	) => {
		const index = fragments.length;
		fragments.push(
			generate(factoryExpression).code,
		);
		node.arguments[0] = t.identifier(
			`__ARES_METRO_FRAGMENT_${index}__`,
		);
	};

	forEachMetroFactoryCall(entry.body as t.Statement[], (node, index) => {
		const factoryExpression = composeFactory(node);
		if (!factoryExpression) return false;

		if (index != null && extractor) {
			const composedCall = t.cloneNode(node, true);
			composedCall.arguments[0] = factoryExpression;
			const composedStatement = t.expressionStatement(
				composedCall,
			) as MetroDefineStatement;
			const result = extractor.extractStatement(composedStatement);
			if (result.extracted && result.replacement !== composedStatement) {
				(entry.body as t.Statement[])[index] = result.replacement;
				return true;
			}
			if (result.extracted) {
				node.extra = {
					...node.extra,
					incrementalMetroExtracted: true,
				};
			}
		}
		replaceWithFragment(node, factoryExpression);
		return true;
	});
	traverse.cache.clear();
	functions.set(0, root);
	return fragments;
}

/**
 * Where composed module fragments come from at emit time.
 *
 * An indirection rather than an array because on the parallel path the
 * fragments are never in this process's memory: compose workers write them
 * into the cold store and the emitter streams them straight back out, so the
 * main thread never holds a program's worth of generated source at once.
 *
 * `take` rather than `get`: each fragment is emitted exactly once, and the
 * array-backed implementation drops its reference on the way out for the same
 * reason it always did.
 */
export interface MetroFragmentSource {
	readonly length: number;
	take(index: number): string | undefined;
}

export function arrayFragments(fragments: string[]): MetroFragmentSource {
	return {
		get length() {
			return fragments.length;
		},
		take(index) {
			const fragment = fragments[index];
			fragments[index] = '';
			return fragment;
		},
	};
}

function insertMetroFragments(code: string, fragments: MetroFragmentSource) {
	if (fragments.length === 0) return code;
	return code.replace(
		metroFragmentPlaceholderPattern,
		(_placeholder, index: string) => {
			const fragment = fragments.take(Number(index));
			if (fragment == null) {
				throw new LiftError(`Missing Metro fragment #${index}`);
			}
			return fragment;
		},
	);
}

function emitGeneratedCode(
	code: string,
	fragments: MetroFragmentSource,
	outputSink: ((chunk: string) => void) | undefined,
): string {
	if (!outputSink) return insertMetroFragments(code, fragments);
	if (fragments.length === 0) {
		outputSink(code);
		return '';
	}

	metroFragmentPlaceholderPattern.lastIndex = 0;
	let offset = 0;
	for (
		let match = metroFragmentPlaceholderPattern.exec(code);
		match;
		match = metroFragmentPlaceholderPattern.exec(code)
	) {
		outputSink(code.slice(offset, match.index));
		const index = Number(match[1]);
		const fragment = fragments.take(index);
		if (fragment == null) {
			throw new LiftError(`Missing Metro fragment #${index}`);
		}
		outputSink(fragment);
		offset = match.index + match[0].length;
	}
	outputSink(code.slice(offset));
	metroFragmentPlaceholderPattern.lastIndex = 0;
	return '';
}

function repairCopiedFinalizerContinuations(file: t.File) {
	traverse(file, {
		Program: {
			exit(path) {
				repairCopiedFinalizersInBody(path.node.body);
			},
		},
		BlockStatement: {
			exit(path) {
				repairCopiedFinalizersInBody(path.node.body);
			},
		},
	});
}

function repairCopiedFinalizersInBody(body: t.Statement[]) {
	for (let i = 0; i < body.length; i++) {
		const statement = body[i];
		if (!t.isTryStatement(statement)) continue;

		if (statement.finalizer) {
			repairSuspendedNestedFinalizerCopy(body, i, statement);
			const repairedDisplacedCatch = repairDisplacedNestedFinalizerCatch(
				statement,
			);
			const finalizer = statement.finalizer.body;
			stripFlattenedFinalizerTail(statement.block.body, finalizer);
			if (statement.handler) {
				stripStatementSuffix(
					statement.handler.body.body,
					finalizer,
					true,
				);
				stripFlattenedFinalizerTail(
					statement.handler.body.body,
					finalizer,
					true,
				);
			}

			const removedCompleteCopy =
				body.length >= i + 1 + finalizer.length &&
				statementListMatchesFinalizerPrefix(
					body.slice(i + 1, i + 1 + finalizer.length),
					finalizer,
				);
			if (removedCompleteCopy) {
				body.splice(i + 1, finalizer.length);
			}
			if (repairedDisplacedCatch) {
				const nested = finalizer[0];
				const nestedFinalizer = t.isTryStatement(nested)
					? nested.finalizer?.body ?? []
					: [];
				if (
					nestedFinalizer.length > 0 &&
					statementListMatchesFinalizerPrefix(
						body.slice(i + 1, i + 1 + nestedFinalizer.length),
						nestedFinalizer,
					)
				) body.splice(i + 1, nestedFinalizer.length);
			}
			// A copied abrupt path can rejoin part-way through a structured
			// finalizer, leaving only its terminal suffix after the try. That suffix
			// has already executed on every completion of the try.
			for (
				let length = removedCompleteCopy
					? 0
					: Math.min(finalizer.length, body.length - i - 1);
				length > 0;
				length--
			) {
				if (
					!statementListMatchesFinalizerPrefix(
						body.slice(i + 1, i + 1 + length),
						finalizer.slice(finalizer.length - length),
					)
				) continue;
				body.splice(i + 1, length);
				break;
			}
			continue;
		}

		const handler = statement.handler;
		if (!handler || !t.isIdentifier(handler.param)) continue;
		const catchBody = handler.body.body;
		const rethrow = catchBody.at(-1);
		if (
			!t.isThrowStatement(rethrow) ||
			!t.isIdentifier(rethrow.argument, { name: handler.param.name })
		) continue;

		const finalizer = catchBody.slice(0, -1);
		if (
			finalizer.length === 0 ||
			body.length < i + 1 + finalizer.length ||
			!statementListMatchesFinalizerPrefix(
				body.slice(i + 1, i + 1 + finalizer.length),
				finalizer,
			)
		) continue;

		statement.handler = null;
		statement.finalizer = t.blockStatement(
			finalizer.map((entry) => t.cloneNode(entry, true)),
		);
		body.splice(i + 1, finalizer.length);
	}
}

function repairSuspendedNestedFinalizerCopy(
	body: t.Statement[],
	index: number,
	statement: t.TryStatement,
) {
	if (!statement.finalizer || !statement.handler) return false;
	const trailer = body[index + 1];
	if (
		!trailer || !t.isTryStatement(trailer) ||
		trailer.block.body.length !== 0 || !trailer.handler ||
		!trailer.finalizer
	) return false;

	const catchBody = trailer.handler.body.body;
	const finalizerBody = trailer.finalizer.body;
	let sharedLength = 0;
	const maxSharedLength = Math.min(catchBody.length, finalizerBody.length);
	for (let length = maxSharedLength; length > 0; length--) {
		if (
			statementListMatchesFinalizerPrefix(
				catchBody.slice(catchBody.length - length),
				finalizerBody.slice(0, length),
			)
		) {
			sharedLength = length;
			break;
		}
	}
	if (sharedLength === 0) return false;

	const canonicalPrefix = statement.finalizer.body;
	const sharedFinalizer = finalizerBody.slice(0, sharedLength);
	const copiedExpansion = findCopiedNestedFinalizerExpansion(
		statement.handler.body,
		canonicalPrefix,
		sharedFinalizer,
	);
	if (!copiedExpansion) return false;

	const nestedCatch = t.cloneNode(trailer.handler, true);
	nestedCatch.body.body.splice(
		nestedCatch.body.body.length - sharedLength,
		sharedLength,
		t.returnStatement(),
	);
	statement.finalizer.body.push(t.tryStatement(
		t.blockStatement(
			copiedExpansion.nestedBody.map((entry) => t.cloneNode(entry, true)),
		),
		nestedCatch,
		t.blockStatement(
			sharedFinalizer.map((entry) => t.cloneNode(entry, true)),
		),
	));
	copiedExpansion.owner.splice(
		copiedExpansion.offset,
		copiedExpansion.owner.length - copiedExpansion.offset,
		t.returnStatement(),
	);
	const continuation = finalizerBody.slice(sharedLength);
	const continuationAlreadyFollows = continuation.length > 0 &&
		statementListMatchesFinalizerPrefix(
			body.slice(index + 2, index + 2 + continuation.length),
			continuation,
		);
	body.splice(
		index + 1,
		1,
		...(continuationAlreadyFollows
			? []
			: continuation.map((entry) => t.cloneNode(entry, true))),
	);
	return true;
}

function findCopiedNestedFinalizerExpansion(
	root: t.BlockStatement,
	canonicalPrefix: t.Statement[],
	sharedFinalizer: t.Statement[],
): { owner: t.Statement[]; offset: number; nestedBody: t.Statement[] } | null {
	let result: {
		owner: t.Statement[];
		offset: number;
		nestedBody: t.Statement[];
	} | null = null;
	t.traverseFast(root, (node) => {
		if (result || !t.isBlockStatement(node)) return;
		const statements = node.body;
		for (
			let offset = 0;
			offset + canonicalPrefix.length + sharedFinalizer.length <=
				statements.length;
			offset++
		) {
			if (
				!statementListMatchesFinalizerPrefix(
					statements.slice(offset, offset + canonicalPrefix.length),
					canonicalPrefix,
				)
			) continue;
			const expansion = statements.slice(offset + canonicalPrefix.length);
			if (expansion.length <= sharedFinalizer.length) continue;
			if (
				!statementListMatchesFinalizerPrefix(
					expansion.slice(expansion.length - sharedFinalizer.length),
					sharedFinalizer,
				)
			) continue;
			result = {
				owner: statements,
				offset,
				nestedBody: expansion.slice(
					0,
					expansion.length - sharedFinalizer.length,
				),
			};
			return;
		}
	});
	return result;
}

function repairDisplacedNestedFinalizerCatch(statement: t.TryStatement) {
	if (!statement.finalizer || !statement.handler) return false;
	const finalizer = statement.finalizer.body;
	if (finalizer.length < 2) return false;
	const catchBody = statement.handler.body.body;
	const displaced = catchBody.at(-1);
	if (
		!t.isTryStatement(displaced) ||
		displaced.block.body.length !== 0 ||
		!displaced.handler ||
		displaced.handler.body.body.length === 0
	) return false;

	const nested = t.tryStatement(
		t.blockStatement(
			finalizer.slice(0, -1).map((entry) => t.cloneNode(entry, true)),
		),
		t.cloneNode(displaced.handler, true),
		t.blockStatement([t.cloneNode(finalizer.at(-1)!, true)]),
	);
	statement.finalizer.body = [nested];
	catchBody.pop();
	return true;
}

function stripFlattenedFinalizerTail(
	body: t.Statement[],
	finalizer: t.Statement[],
	preserveAbruptCompletion = false,
) {
	if (finalizer.length < 2 || body.length === 0) return false;
	const nestedStatements: t.Statement[] = [];
	for (const statement of finalizer) {
		t.traverseFast(statement, (child) => {
			if (t.isStatement(child)) nestedStatements.push(child);
		});
	}

	for (let offset = 0; offset < body.length; offset++) {
		const tail = body.slice(offset);
		if (!statementAlwaysTerminates(t.blockStatement(tail))) continue;
		if (
			!statementListMatchesFinalizerPrefix(
				[tail[0]],
				[finalizer[0]],
			)
		) continue;
		if (
			!tail.every((candidate) =>
				nestedStatements.some((nested) =>
					statementListMatchesFinalizerPrefix(
						[candidate],
						[nested],
					)
				)
			)
		) continue;

		body.splice(
			offset,
			body.length - offset,
			...(preserveAbruptCompletion ? [t.returnStatement()] : []),
		);
		return true;
	}
	return false;
}

function unboundGeneratedUndefinedGuard(path: NodePath<t.IfStatement>) {
	if (path.node.alternate) return false;
	const consequent = path.node.consequent;
	if (!statementAlwaysTerminates(consequent)) return false;
	const test = path.node.test;
	if (
		!t.isBinaryExpression(test) ||
		!['===', '=='].includes(test.operator)
	) return false;
	const generated = t.isIdentifier(test.left) && isUndefinedNode(test.right)
		? test.left
		: t.isIdentifier(test.right) && isUndefinedNode(test.left)
		? test.right
		: null;
	return !!generated && isRegisterTempName(generated.name) &&
		!path.scope.getBinding(generated.name);
}

function repairPerIterationEnvironmentBindings(file: t.File) {
	traverse(file, {
		WhileStatement(path) {
			const body = path.get('body');
			if (!body.isBlockStatement()) return;
			const statements = body.node.body;
			for (let i = 0; i < statements.length - 1; i++) {
				const reset = generatedIdentifierAssignment(statements[i]);
				const value = generatedIdentifierAssignment(statements[i + 1]);
				if (
					!reset || !value || reset.name !== value.name ||
					!isEnvironmentSlotName(reset.name) ||
					!isUndefinedNode(reset.value)
				) continue;
				const binding = path.scope.getBinding(reset.name);
				if (
					!binding || !binding.path.isVariableDeclarator() ||
					binding.path.node.init != null ||
					!binding.path.parentPath?.isVariableDeclaration({
						kind: 'var',
					})
				) continue;
				if (
					!binding.referencePaths.every((reference) =>
						path.isAncestor(reference)
					) ||
					!binding.constantViolations.every((violation) =>
						path.isAncestor(violation)
					)
				) continue;

				statements.splice(
					i,
					2,
					t.variableDeclaration('const', [
						t.variableDeclarator(
							t.identifier(reset.name),
							t.cloneNode(value.value, true),
						),
					]),
				);
				const declaration = binding.path.parentPath;
				if (declaration.node.declarations.length === 1) {
					declaration.remove();
				} else {
					binding.path.remove();
				}
				return;
			}
		},
	});
}

function generatedIdentifierAssignment(statement: t.Statement): {
	name: string;
	value: t.Expression;
} | null {
	if (!t.isExpressionStatement(statement)) return null;
	const expression = statement.expression;
	if (
		!t.isAssignmentExpression(expression, { operator: '=' }) ||
		!t.isIdentifier(expression.left) ||
		!t.isExpression(expression.right)
	) return null;
	return { name: expression.left.name, value: expression.right };
}

function declareUnboundGeneratedAssignments(file: t.File) {
	const declarations = new Map<t.Program | t.BlockStatement, Set<string>>();
	traverse(file, {
		AssignmentExpression(path) {
			if (!t.isIdentifier(path.node.left)) return;
			const name = path.node.left.name;
			if (!isRegisterTempName(name)) return;
			if (path.scope.getBinding(name)) return;
			const functionParent = path.getFunctionParent();
			let body: t.Program | t.BlockStatement | undefined;
			if (functionParent) {
				const owner = functionParent.get('body');
				// Body declarations cannot bind an assignment in a parameter
				// initializer. Do not turn that unresolved reference into a
				// duplicate declaration which is still in the wrong scope.
				if (!owner.isBlockStatement() || !owner.isAncestor(path)) {
					return;
				}
				body = owner.node;
			} else {
				const program = path.findParent((parent) => parent.isProgram());
				if (program?.isProgram()) body = program.node;
			}
			if (!body) return;
			const names = declarations.get(body) ?? new Set<string>();
			names.add(name);
			declarations.set(body, names);
		},
	});
	for (const [body, names] of declarations) {
		const declaration = t.variableDeclaration(
			'let',
			[...names].toSorted().map((name) =>
				t.variableDeclarator(t.identifier(name))
			),
		);
		body.body.unshift(declaration);
	}
}

function stripUnreachableStatementTail(body: t.Statement[]) {
	for (let i = 0; i < body.length - 1; i++) {
		if (!statementAlwaysTerminates(body[i])) continue;
		body.splice(i + 1);
		return;
	}
}

function startPhase(name: string) {
	reportProgress(`[lift] ${name}…`);
	const start = performance.now();
	return () => {
		const seconds = ((performance.now() - start) / 1000).toFixed(2);
		reportProgress(`[lift] ${name} done in ${seconds}s`);
	};
}

function effectiveRecursiveSummaryMisses(
	summary: RecursiveCFGSummary,
): string[] {
	if (
		summary.selectedEmission?.source === 'reduced-fallback' &&
		summary.reducedFallbackEmission?.status === 'emitted' &&
		summary.reducedFallbackEmission.diagnostics.length === 0
	) {
		return [];
	}
	return summary.postReductionAnalysis?.misses ?? summary.misses;
}

function lightweightFunctionSummary(
	file: HBCFile,
	func: IRFunction,
	structured: boolean,
): LiftedFunctionSummary {
	const source = file.functions[func.id];
	const recursive = func.recursiveCFGSummary;
	const createdEnvironments: LiftedFunctionSummary['createdEnvironments'] =
		[];
	for (const block of source.basicBlocks.values()) {
		for (const instruction of block.instructions) {
			if (instruction.instruction === 'CreateFunctionEnvironment') {
				createdEnvironments.push({
					kind: 'function',
					size: instruction.envSize ?? null,
				});
			} else if (
				instruction.instruction === 'CreateTopLevelEnvironment'
			) {
				createdEnvironments.push({
					kind: 'top-level',
					size: instruction.envSize,
				});
			} else if (
				instruction.instruction === 'CreateEnvironment' ||
				instruction.instruction === 'CreateInnerEnvironment'
			) {
				createdEnvironments.push({
					kind: 'inner',
					size: 'envSize' in instruction ? instruction.envSize : null,
				});
			}
		}
	}
	return {
		functionId: func.id,
		name: source.name ?? null,
		functionKind: source.functionKind,
		paramCount: source.paramCount,
		frameSize: source.frameSize,
		environmentSize: source.envSize,
		createdEnvironments,
		exceptionHandlerCount: source.exceptionHandlers.length,
		structured,
		remainingBlocks: [...func.blocks.values()]
			.map((block) => ({
				address: block.address,
				successors: block.consequentAddresses.slice(),
			}))
			.toSorted((left, right) => left.address - right.address),
		referencedFunctions: [...func.referencedFunctionIds]
			.map(([functionId, count]) => ({ functionId, count }))
			.toSorted((left, right) => left.functionId - right.functionId),
		recursiveCFG: recursive
			? {
				blockCount: recursive.blockCount,
				normalEdgeCount: recursive.normalEdgeCount,
				exceptionalEdgeCount: recursive.exceptionalEdgeCount,
				sccCount: recursive.sccCount,
				loopCount: recursive.loopCount,
				phiCount: recursive.phiCount,
				switchCount: recursive.switchCount,
				delegateYieldCount: recursive.delegateYieldCount,
				emissionStatus: recursive.emissionStatus,
				regionKind: recursive.regionKind ?? null,
				misses: effectiveRecursiveSummaryMisses(recursive).slice(),
				emitDiagnostics: recursive.emitDiagnostics.slice(),
				selection: { ...recursive.selection },
				postReductionMisses:
					recursive.postReductionAnalysis?.misses.slice() ?? null,
				postReductionAvailable: recursive.postReductionAnalysis != null,
				postReductionProgramAvailable:
					recursive.postReductionAnalysis?.rawEmission.program !=
						null,
				migrationAudit: recursive.migrationAudit ?? null,
			}
			: null,
	};
}

function standaloneFunctionArtifact(
	file: HBCFile,
	func: IRFunction,
): LiftedFunctionArtifact {
	const expression = func.tryGetFunctionExpr();
	if (!expression) {
		const blocks = [...func.blocks.values()]
			.toSorted((left, right) => left.address - right.address);
		const code = blocks.map((block) => {
			const address = `0x${block.address.toString(16)}`;
			const successors = block.consequentAddresses.length === 0
				? 'none'
				: block.consequentAddresses.map((successor) =>
					`0x${successor.toString(16)}`
				).join(',');
			const body = generate(t.program(
				block.body.map((statement) =>
					t.cloneNode(statement as t.Statement, true)
				),
			)).code;
			return `/* block ${address} successors=${successors} */\n${body}`;
		}).join('\n\n');
		return {
			summary: lightweightFunctionSummary(file, func, false),
			code,
		};
	}
	normalizeDuplicateRegisterDeclarations(expression);
	const program = t.file(t.program([
		t.expressionStatement(expression),
	]));
	liftGeneratedCallProtocols(program);
	return {
		summary: lightweightFunctionSummary(file, func, true),
		code: generate(program).code,
	};
}

/**
 * Compose each requested function as its own root.
 *
 * One store per root: `composeLiftedFile` consumes what it inlines, so sharing
 * a store between roots would leave the second one missing whichever
 * descendants the first had already claimed. Lifting is lazy, so a root only
 * pays for the subtree it actually owns.
 */
function composeFunctionSubtrees(
	file: HBCFile,
	options: LiftFileOptions,
): LiftAnalysisResult {
	const roots = selectedFunctionIds(file, options.composeRoots);
	if (options.metroModules) {
		throw new Error(
			'Metro module extraction requires whole-file composition',
		);
	}
	let end = startPhase('planning bottom-up composition');
	const plan = buildCompositionPlan(buildBytecodeDerivedPlan(file));
	end();

	const environmentIdentity = emptyEnvironmentIdentityDiagnostics();
	const recursiveCFGSummaries: RecursiveCFGSummary[] = [];
	const parts: string[] = [];
	end = startPhase('composing function subtrees');
	for (const root of roots) {
		reportProgress(`currently composing function #${root}`);
		const functions = new LazyIRFunctionStore(
			file,
			{ cfgReducer: options.cfgReducer },
			options.retainRecursiveCFGSummaries ?? true,
		);
		// Function 0 is the file body rather than a function expression, so it
		// is the one root that composes as a program.
		const program = composeLiftedFile(
			file,
			functions,
			plan,
			{
				functionId: root,
				kind: root === 0 ? 'file' : 'function',
			},
			environmentIdentity,
		);
		recursiveCFGSummaries.push(...functions.recursiveSummaries());
		parts.push(
			`/* Function #${root} composed with its descendants */\n` +
				generate(program).code,
		);
	}
	end();

	end = startPhase('generating code');
	const code = emitGeneratedCode(
		parts.join('\n\n'),
		arrayFragments([]),
		options.outputSink,
	);
	end();
	return { code, recursiveCFGSummaries, environmentIdentity };
}

function recursiveSummaries(functions: Map<FunctionId, IRFunction>) {
	return [...functions.values()].flatMap((func) =>
		func.recursiveCFGSummary ? [func.recursiveCFGSummary] : []
	);
}

function generateStandaloneFunctions(
	file: HBCFile,
	functions: Map<FunctionId, IRFunction>,
) {
	return [...functions.values()]
		.map((func) => standaloneFunctionArtifact(file, func).code)
		.join('\n\n');
}

export function liftFunctionsIncrementally(
	file: HBCFile,
	options: LiftFunctionsIncrementalOptions,
	onFunction: (artifact: LiftedFunctionArtifact) => void,
): LiftedFunctionSummary[] {
	const summaries: LiftedFunctionSummary[] = [];
	const ids = selectedFunctionIds(file, options.functionIds);
	const end = startPhase('lifting standalone IR functions');
	try {
		for (const id of ids) {
			reportProgress(`currently lifting function #${id}`);
			const func = new IRFunction(
				file,
				new SSAFunction(file.functions[id]),
				{ cfgReducer: options.cfgReducer },
			);
			const artifact = standaloneFunctionArtifact(file, func);
			if (options.retainSummaries !== false) {
				summaries.push(artifact.summary);
			}
			onFunction(artifact);
		}
	} finally {
		end();
	}
	return summaries;
}

/**
 * Build only the compact data needed by the gated CFG migration report. Unlike
 * standalone lifting, this never generates per-function code or retains Region
 * ASTs across functions.
 */
function recursiveCFGMigrationFunctionSummary(
	file: HBCFile,
	functionId: FunctionId,
	recursive: RecursiveCFGSummary | undefined,
): RecursiveCFGMigrationFunctionSummary {
	const audit = recursive?.migrationAudit;
	if (!recursive?.selection || !audit) {
		return {
			functionId,
			selection: null,
			migrationAudit: null,
			postReductionAvailable: false,
			postReductionProgramAvailable: false,
			skippedReason: file.functions[functionId].basicBlocks.has(0)
				? 'recursive-summary-unavailable'
				: 'no-entry-block',
		};
	}
	return {
		functionId,
		selection: { ...recursive.selection },
		migrationAudit: audit,
		postReductionAvailable: recursive.postReductionAnalysis != null,
		postReductionProgramAvailable:
			recursive.postReductionAnalysis?.rawEmission.program != null,
		skippedReason: null,
	};
}

export function collectRecursiveCFGMigrationSummaries(
	file: HBCFile,
	options: LiftFunctionsIncrementalOptions,
	onSummary?: (summary: RecursiveCFGMigrationFunctionSummary) => void,
): RecursiveCFGMigrationFunctionSummary[] {
	const summaries: RecursiveCFGMigrationFunctionSummary[] = [];
	const ids = selectedFunctionIds(file, options.functionIds);
	const end = startPhase('collecting recursive CFG migration summaries');
	try {
		for (const id of ids) {
			reportProgress(`currently lifting function #${id}`);
			const func = new IRFunction(
				file,
				new SSAFunction(file.functions[id]),
				{ cfgReducer: options.cfgReducer },
			);
			const summary = recursiveCFGMigrationFunctionSummary(
				file,
				id,
				func.recursiveCFGSummary,
			);
			onSummary?.(summary);
			if (options.retainSummaries !== false) summaries.push(summary);
		}
	} finally {
		end();
	}
	return summaries;
}

export type ParallelRecursiveCFGMigrationSummaryOptions =
	& LiftFunctionsIncrementalOptions
	& Pick<LiftFileParallelOptions, 'workers' | 'spill'>;

export async function collectRecursiveCFGMigrationSummariesParallel(
	file: HBCFile,
	options: ParallelRecursiveCFGMigrationSummaryOptions,
	onSummary?: (summary: RecursiveCFGMigrationFunctionSummary) => void,
): Promise<RecursiveCFGMigrationFunctionSummary[]> {
	const summaries: RecursiveCFGMigrationFunctionSummary[] = [];
	const ids = selectedFunctionIds(file, options.functionIds);
	const emitted = new Set<FunctionId>();
	const emitSummary = (
		functionId: FunctionId,
		recursive: RecursiveCFGSummary | undefined,
	) => {
		if (emitted.has(functionId)) return;
		emitted.add(functionId);
		const summary = recursiveCFGMigrationFunctionSummary(
			file,
			functionId,
			recursive,
		);
		onSummary?.(summary);
		if (options.retainSummaries !== false) summaries.push(summary);
	};
	const recursiveSummaryFromSnapshot = (
		store: ColdStore,
		functionId: FunctionId,
	): RecursiveCFGSummary | undefined => {
		const recursive = readColdSnapshotHead(store, functionId)
			?.recursiveCFGSummary;
		return recursive?.selection && recursive.migrationAudit
			? recursive
			: undefined;
	};
	const cfgReducer = options.cfgReducer == null ? undefined : {
		...options.cfgReducer,
		retainArtifacts: options.cfgReducer.retainArtifacts ?? true,
	};
	let end = startPhase('preparing cold store');
	const session = await openColdSession(
		file,
		{ cfgReducer },
		options.spill,
		(message) => reportProgress(`[lift] ${message}`),
	);
	end();

	try {
		const { file: coldFile } = readColdFile(session.store, {
			cacheLimit: options.spill?.fileCacheLimit,
		});
		file.adoptPartsFrom(coldFile);
		let failed = 0;
		const staleSnapshots = ids.filter((id) =>
			hasColdSnapshot(session.store, id) &&
			recursiveSummaryFromSnapshot(session.store, id) == null
		);
		if (staleSnapshots.length > 0) {
			await session.store.root.transaction(() => {
				for (const id of staleSnapshots) {
					deleteColdSnapshot(session.store, id);
				}
			});
		}
		const reusedSnapshots = session.reusedSnapshots &&
			staleSnapshots.length === 0;
		end = startPhase(
			reusedSnapshots
				? 'reusing lifted IR functions from cold store'
				: 'lifting IR functions (parallel)',
		);
		try {
			if (!reusedSnapshots) {
				const alreadyLifted = ids.filter((id) =>
					hasColdSnapshot(session.store, id)
				);
				for (const id of alreadyLifted) {
					emitSummary(
						id,
						recursiveSummaryFromSnapshot(session.store, id),
					);
				}
				const derived = readColdPlan(session.store);
				const lifted = await liftIntoColdStore(
					coldFile,
					session.store,
					session.path,
					derived.functionBytecodeLengths,
					{ ...options, functionIds: ids, cfgReducer },
					(written) => {
						for (const id of written) {
							emitSummary(
								id,
								recursiveSummaryFromSnapshot(
									session.store,
									id,
								),
							);
						}
					},
				);
				failed = lifted.failed;
			}
		} finally {
			end();
		}
		if (
			!reusedSnapshots &&
			options.functionIds == null &&
			failed === 0
		) {
			await markSnapshotsComplete(session);
		}

		if (reusedSnapshots) {
			end = startPhase('collecting recursive CFG migration summaries');
			try {
				for (const id of ids) {
					emitSummary(
						id,
						recursiveSummaryFromSnapshot(session.store, id),
					);
				}
			} finally {
				end();
			}
		} else {
			for (const id of ids) {
				if (!emitted.has(id)) emitSummary(id, undefined);
			}
		}
	} finally {
		await session.release();
	}
	return summaries;
}

export function liftFile(file: HBCFile, options: LiftFileOptions = {}) {
	return liftFileWithAnalysis(file, {
		...options,
		retainRecursiveCFGSummaries: options.retainRecursiveCFGSummaries ??
			false,
	}).code;
}

export function liftFileWithAnalysis(
	file: HBCFile,
	options: LiftFileOptions = {},
): LiftAnalysisResult {
	if (options.composeRoots?.length) {
		return composeFunctionSubtrees(file, options);
	}
	const compose = options.compose ?? (options.functionIds == null);
	if (!compose) {
		if (options.metroModules) {
			throw new Error(
				'Metro module extraction requires whole-file composition',
			);
		}
		let end = startPhase('lifting IR functions');
		const functions = buildIRFunctionsSerial(file, {
			cfgReducer: options.cfgReducer,
		}, options.functionIds);
		const recursiveCFGSummaries = recursiveSummaries(functions);
		end();
		end = startPhase('generating standalone functions');
		const generated = generateStandaloneFunctions(file, functions);
		const code = emitGeneratedCode(
			generated,
			arrayFragments([]),
			options.outputSink,
		);
		end();
		return {
			code,
			recursiveCFGSummaries,
		};
	}

	let end = startPhase('planning bottom-up composition');
	const derived = buildBytecodeDerivedPlan(file);
	end();

	const retainRecursiveCFGSummaries = options.retainRecursiveCFGSummaries ??
		true;
	const functions = new LazyIRFunctionStore(
		file,
		{ cfgReducer: options.cfgReducer },
		retainRecursiveCFGSummaries,
	);
	const compositionPlan = buildCompositionPlan(derived);
	let metroFragments: string[] = [];
	const incrementalMetroExtractor = options.metroModules &&
			file.functions.length >= 1_000
		? createIncrementalMetroExtractor(options.metroModules)
		: undefined;
	if (file.functions.length >= 1_000) {
		end = startPhase('spilling Metro module fragments');
		metroFragments = spillMetroModuleFactories(
			file,
			functions,
			compositionPlan,
			derived,
			incrementalMetroExtractor,
		);
		end();
	}
	end = startPhase('composing lifted file bottom-up');
	const environmentIdentity = emptyEnvironmentIdentityDiagnostics();
	const program = composeLiftedFile(
		file,
		functions,
		compositionPlan,
		undefined,
		environmentIdentity,
	);
	end();

	if (retainRecursiveCFGSummaries) {
		end = startPhase('completing recursive CFG summaries');
		functions.ensureRecursiveSummaries();
		end();
	}
	const recursiveCFGSummaries = functions.recursiveSummaries();

	if (options.metroModules) {
		end = startPhase('extracting Metro modules');
		if (incrementalMetroExtractor) {
			incrementalMetroExtractor.extractProgram(program);
			incrementalMetroExtractor.finish();
		} else {
			extractMetroModules(program, options.metroModules);
		}
		end();
	}

	end = startPhase('generating code');
	const code = emitGeneratedCode(
		generate(program).code,
		arrayFragments(metroFragments),
		options.outputSink,
	);
	end();
	return {
		code,
		recursiveCFGSummaries,
		environmentIdentity,
	};
}

export async function liftFileParallel(
	file: HBCFile,
	options: LiftFileParallelOptions = {},
) {
	// Only the code is returned, so collecting the summaries would be work
	// whose whole result is dropped -- and on a 127k-function bundle that
	// alone is enough to push the main thread past the isolate's heap cap.
	return (await liftFileParallelWithAnalysis(file, {
		...options,
		cfgReducer: options.cfgReducer == null ? undefined : {
			...options.cfgReducer,
			retainArtifacts: options.cfgReducer.retainArtifacts ?? false,
		},
		collectRecursiveSummaries: false,
	})).code;
}

export async function liftFileParallelWithAnalysis(
	file: HBCFile,
	options: LiftFileParallelOptions = {},
): Promise<LiftAnalysisResult> {
	const end = startPhase('preparing cold store');
	const session = await openColdSession(
		file,
		{ cfgReducer: options.cfgReducer },
		options.spill,
		(message) => reportProgress(`[lift] ${message}`),
	);
	end();

	try {
		return await liftFileParallelWithColdSession(file, session, options);
	} finally {
		await session.release();
	}
}

async function liftFileParallelWithColdSession(
	file: HBCFile,
	session: ColdSession,
	options: LiftFileParallelOptions,
): Promise<LiftAnalysisResult> {
	// Everything past this point reads the bundle through the store, so the
	// eagerly parsed copy the caller handed in is no longer the source of
	// truth. Workers get a path instead of bytes, and never build their own.
	const { file: coldFile } = readColdFile(session.store, {
		cacheLimit: options.spill?.fileCacheLimit,
	});
	// The caller's file filled the store and is now redundant, but only the
	// caller holds it, so it has to give up its own parts to become
	// collectable. After this the main thread pages like everyone else.
	file.adoptPartsFrom(coldFile);

	// The plans and the store come first now, because the Metro path lifts and
	// composes together and needs both before a single function is lifted.
	let end = startPhase('planning bottom-up composition');
	const derived = readColdPlan(session.store);
	const plan = buildCompositionPlan(derived);
	end();

	const store = new ColdIRFunctionStore(coldFile, session.store, {
		cfgReducer: options.cfgReducer,
	});

	const compose = options.compose ?? (options.functionIds == null);
	const configuredPipelineThreshold = Number(
		env['ARES_PIPELINED_METRO_THRESHOLD'] ?? NaN,
	);
	const pipelineThreshold = Number.isFinite(configuredPipelineThreshold) &&
			configuredPipelineThreshold > 0
		? configuredPipelineThreshold
		: 1_000;
	// A Metro bundle is the only shape with independent composition units, so
	// it is the only one where lifting and composing can overlap. Everything
	// else lifts to completion and composes once.
	const pipelineMetro = compose && !options.metroModules &&
		coldFile.functions.length >= pipelineThreshold;

	let functionIds: FunctionId[];
	let liftFailures = 0;
	let metroFragments: MetroFragmentSource = arrayFragments([]);
	let blockedFunctionIds: ReadonlySet<FunctionId> | undefined;
	const environmentIdentity = emptyEnvironmentIdentityDiagnostics();
	if (pipelineMetro) {
		end = startPhase(
			session.reusedSnapshots
				? 'composing Metro modules from cold store'
				: 'lifting and composing Metro modules (pipelined)',
		);
		const pipelined = await liftAndComposeMetroParallel(
			coldFile,
			session.store,
			session.path,
			store,
			plan,
			derived,
			options,
			session.reusedSnapshots,
		);
		functionIds = pipelined.functionIds;
		metroFragments = pipelined.fragments;
		blockedFunctionIds = pipelined.blockedFunctionIds;
		liftFailures = pipelined.failed;
		addEnvironmentIdentityDiagnostics(
			environmentIdentity,
			pipelined.environmentIdentity,
		);
		end();
	} else {
		end = startPhase(
			session.reusedSnapshots
				? 'reusing lifted IR functions from cold store'
				: 'lifting IR functions (parallel)',
		);
		if (session.reusedSnapshots) {
			functionIds = selectedFunctionIds(coldFile, options.functionIds);
		} else {
			const lifted = await liftIntoColdStore(
				coldFile,
				session.store,
				session.path,
				derived.functionBytecodeLengths,
				options,
			);
			functionIds = lifted.functionIds;
			liftFailures = lifted.failed;
		}
		end();
	}
	if (
		!session.reusedSnapshots && options.functionIds == null &&
		liftFailures === 0
	) {
		// Only a run that lifted the whole file may declare the phase done. A
		// `--function` range writes perfectly good snapshots for the ids it
		// touched, and a later run is welcome to find them, but marking the
		// phase complete would tell that run every other function is present
		// too -- and it would then compose against functions that are simply
		// missing.
		//
		// Nor may a run that left functions unlifted: marking complete would
		// tell a later run -- possibly one with the offending bug fixed -- that
		// there is nothing left to attempt.
		await markSnapshotsComplete(session);
	}

	let recursiveCFGSummaries: RecursiveCFGSummary[] = [];
	if (options.collectRecursiveSummaries !== false) {
		end = startPhase('collecting recursive CFG summaries');
		// Every worker batch was committed on another thread, so read from a
		// snapshot taken now rather than whenever this thread last started a
		// read transaction.
		session.store.releaseReader();
		// From the snapshot heads, not from materialised functions: the
		// summaries live in the small half of each record, so this reads every
		// function without paging in a single block AST.
		recursiveCFGSummaries = readColdRecursiveSummaries(
			session.store,
			coldFile.functions.length,
		);
		end();
	}

	if (!compose) {
		if (options.metroModules) {
			throw new Error(
				'Metro module extraction requires whole-file composition',
			);
		}
		end = startPhase('generating standalone functions');
		const functions = new Map<FunctionId, IRFunction>();
		for (const id of functionIds) {
			const func = store.get(id);
			if (func) functions.set(id, func);
		}
		const generated = generateStandaloneFunctions(coldFile, functions);
		const code = emitGeneratedCode(
			generated,
			arrayFragments([]),
			options.outputSink,
		);
		end();
		return {
			code,
			recursiveCFGSummaries,
		};
	}

	end = startPhase('composing lifted file');
	const program = composeLiftedFile(
		coldFile,
		store,
		plan,
		{
			functionId: 0,
			kind: 'file',
			blockedFunctionIds,
		},
		environmentIdentity,
	);
	end();

	if (options.metroModules) {
		end = startPhase('extracting Metro modules (parallel)');
		await extractMetroModulesParallel(
			program,
			options.metroModules,
			options.workers,
		);
		end();
	}

	end = startPhase('generating code');
	const code = emitGeneratedCode(
		generate(program).code,
		metroFragments,
		options.outputSink,
	);
	end();
	if (Deno.env.get('ARES_COLDSTORE_STATS')) store.logStats('main thread');
	return {
		code,
		recursiveCFGSummaries,
		environmentIdentity,
	};
}
