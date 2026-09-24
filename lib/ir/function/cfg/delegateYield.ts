import * as t from '@babel/types';
import { memberName } from './descriptors/delegateYield.ts';
import traverse, { NodePath } from '@babel/traverse';
import { isUndefinedNode } from '../../ast/utils.ts';
import type { IRFunction } from '../mod.ts';
import { phiContext, registerName } from './phi.ts';

function normalizeDelegateArgumentGlobals(
	expr: t.Expression,
	globalNames: Set<string>,
) {
	const root = t.cloneNode(expr, true);
	const wrapped = t.file(t.program([t.expressionStatement(root)]));
	traverse(wrapped, {
		CallExpression(path) {
			if (
				!t.isV8IntrinsicIdentifier(path.node.callee, {
					name: 'TryGetById',
				})
			) return;
			if (path.node.arguments.length !== 2) return;
			const [object, property] = path.node.arguments;
			if (!t.isIdentifier(object) || !globalNames.has(object.name)) {
				return;
			}
			if (!t.isStringLiteral(property)) return;
			const replacement = t.identifier(property.value);
			replacement.extra = { isReferencedGlobal: true };
			path.replaceWith(replacement);
		},
	});
	const stmt = wrapped.program.body[0];
	if (!t.isExpressionStatement(stmt)) return root;
	return stmt.expression;
}

function normalizeLoweredDelegateExpression(expr: t.Expression): t.Expression {
	if (
		t.isCallExpression(expr) &&
		t.isMemberExpression(expr.callee) &&
		memberName(expr.callee) === 'call'
	) {
		const called = expr.callee.object;
		if (t.isExpression(called)) {
			const args = expr.arguments.slice(1).filter((arg) =>
				t.isExpression(arg) && !isUndefinedNode(arg)
			) as t.Expression[];
			if (
				t.isMemberExpression(called) &&
				t.isIdentifier(called.object) &&
				/^r\d+_\d+$/.test(called.object.name) &&
				!called.computed &&
				t.isIdentifier(called.property)
			) {
				return t.callExpression(
					t.identifier(called.property.name),
					args.map((arg) => t.cloneNode(arg)),
				);
			}
			return t.callExpression(
				t.cloneNode(called),
				args.map((arg) => t.cloneNode(arg)),
			);
		}
	}
	return t.cloneNode(expr);
}

function delegateExpressionFromIteratorAcquisition(
	expr: t.Expression,
	globalNames = new Set<string>(),
): t.Expression | null {
	if (!t.isCallExpression(expr)) return null;
	const callee = expr.callee;
	if (!t.isMemberExpression(callee)) return null;
	const property = callee.property;
	const isIteratorProperty = t.isMemberExpression(property)
		? memberName(property) === 'iterator'
		: memberName(callee) === 'iterator';
	if (!isIteratorProperty) return null;
	const receiver = callee.object;
	if (!t.isExpression(receiver)) return null;
	return normalizeDelegateArgumentGlobals(
		normalizeLoweredDelegateExpression(receiver),
		globalNames,
	);
}

function delegateYieldIntrinsic(argument: t.Expression) {
	return t.callExpression(t.v8IntrinsicIdentifier('DelegateYield'), [
		t.cloneNode(argument, true),
	]);
}

function singleDeclarator(stmt: t.Statement) {
	if (!t.isVariableDeclaration(stmt)) return null;
	if (stmt.declarations.length !== 1) return null;
	const [decl] = stmt.declarations;
	return t.isVariableDeclarator(decl) ? decl : null;
}

function declaratorIdentifier(stmt: t.Statement) {
	const decl = singleDeclarator(stmt);
	return decl && t.isIdentifier(decl.id) ? decl.id.name : null;
}

function iteratorAcquisitionDeclaration(stmt: t.Statement) {
	const decl = singleDeclarator(stmt);
	if (!decl || !t.isIdentifier(decl.id) || !t.isExpression(decl.init)) {
		return null;
	}
	const argument = delegateExpressionFromIteratorAcquisition(decl.init);
	return argument ? { iteratorName: decl.id.name, argument } : null;
}

function iteratorNextPropertyReadName(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return null;
	const expression = stmt.expression;
	const value = t.isAssignmentExpression(expression, { operator: '=' }) &&
			t.isExpression(expression.right)
		? expression.right
		: expression;
	if (
		!t.isMemberExpression(value) ||
		!t.isIdentifier(value.object) ||
		memberName(value) !== 'next'
	) return null;
	return value.object.name;
}

function iteratorNextPropertyDeclarationName(
	stmt: t.Statement | undefined,
	iteratorName: string,
): string | null {
	if (!stmt) return null;
	const decl = singleDeclarator(stmt);
	if (
		!decl || !t.isIdentifier(decl.id) ||
		!t.isMemberExpression(decl.init) ||
		!t.isIdentifier(decl.init.object, { name: iteratorName }) ||
		memberName(decl.init) !== 'next'
	) return null;
	return decl.id.name;
}

function skipIteratorNextPropertyReads(
	body: readonly t.Statement[],
	cursor: number,
	iteratorName: string,
): number {
	while (
		iteratorNextPropertyReadName(body[cursor]) === iteratorName ||
		iteratorNextPropertyDeclarationName(body[cursor], iteratorName) != null
	) {
		cursor++;
	}
	return cursor;
}

export function blockEndsWithDelegateIteratorAcquisition(
	body: t.Statement[],
) {
	let ignoredIteratorName: string | null = null;
	for (let i = body.length - 1; i >= 0; i--) {
		const acquisition = iteratorAcquisitionDeclaration(body[i]);
		if (acquisition) return acquisition;
		const readName = iteratorNextPropertyReadName(body[i]);
		if (
			readName != null &&
			(ignoredIteratorName == null || ignoredIteratorName === readName)
		) {
			ignoredIteratorName = readName;
			continue;
		}
		if (ignoredIteratorName == null) {
			const maybeDecl = singleDeclarator(body[i]);
			if (maybeDecl && t.isIdentifier(maybeDecl.id)) {
				ignoredIteratorName = maybeDecl.id.name;
			}
		}
		if (!t.isVariableDeclaration(body[i])) break;
	}
	return null;
}

interface DelegateYieldLoopStart {
	completionName: string | null;
}

function weakDelegateYieldLoopStart(
	stmt: t.Statement,
	iteratorName: string,
): DelegateYieldLoopStart | null {
	if (
		!t.isWhileStatement(stmt) || !t.isBooleanLiteral(stmt.test, {
			value: true,
		}) || !t.isBlockStatement(stmt.body)
	) return null;
	const body = stmt.body.body;
	const nextDecl = singleDeclarator(body[0]);
	if (
		!nextDecl ||
		!t.isIdentifier(nextDecl.id) ||
		!isIteratorNextCallWithSentValue(nextDecl.init, iteratorName)
	) return null;
	const nextName = nextDecl.id.name;
	let cursor = 1;
	if (!isEnsureObjectStatement(body[cursor], nextName)) return null;
	cursor++;

	// Natural-loop materialization can expose the SSA completion accumulator
	// inside the loop rather than in the surrounding delegate prelude:
	//
	//   let completion;
	//   completion = next;
	//   if (next.done) break;
	//
	// This is the same value that `yield*` returns to its caller. Keep its name so
	// the CFG reducer can bind `%DelegateYield(...)` when the completion is used
	// after the loop.
	let completionName: string | null = null;
	const completionDecl = singleDeclarator(body[cursor]);
	if (
		completionDecl && t.isIdentifier(completionDecl.id) &&
		completionDecl.init == null
	) {
		const candidate = completionDecl.id.name;
		if (assignmentStatement(body[cursor + 1], candidate, nextName)) {
			completionName = candidate;
			cursor += 2;
		}
	} else if (
		completionDecl && t.isIdentifier(completionDecl.id) &&
		t.isIdentifier(completionDecl.init, { name: nextName })
	) {
		completionName = completionDecl.id.name;
		cursor++;
	}

	if (!isDoneBreak(body[cursor], nextName)) return null;
	cursor++;
	if (!isGeneratorSetDelegatedStatement(body[cursor])) return null;
	cursor++;
	return yieldResultOrAssignmentStatement(body[cursor], nextName)
		? { completionName }
		: null;
}

function materializedDelegateYieldLoopStart(
	stmt: t.Statement,
): DelegateYieldLoopStart | null {
	if (
		!t.isWhileStatement(stmt) || !t.isBooleanLiteral(stmt.test, {
			value: true,
		}) || !t.isBlockStatement(stmt.body)
	) return null;
	const body = stmt.body.body;
	const completionDecl = singleDeclarator(body[0]);
	if (
		!completionDecl || !t.isIdentifier(completionDecl.id) ||
		completionDecl.init != null
	) return null;
	const completionName = completionDecl.id.name;
	const completionAssignment = body[1];
	if (!t.isExpressionStatement(completionAssignment)) return null;
	const assignment = completionAssignment.expression;
	if (
		!t.isAssignmentExpression(assignment, { operator: '=' }) ||
		!t.isIdentifier(assignment.left, { name: completionName }) ||
		!t.isIdentifier(assignment.right)
	) return null;
	const nextName = assignment.right.name;

	const done = body[2];
	if (
		!t.isIfStatement(done) || !t.isIdentifier(done.test) ||
		done.alternate != null
	) return null;
	const doneBody = t.isBlockStatement(done.consequent)
		? done.consequent.body
		: [done.consequent];
	if (doneBody.length !== 1 || !t.isBreakStatement(doneBody[0])) return null;
	if (!isGeneratorSetDelegatedStatement(body[3])) return null;

	const yielded = body[4];
	const yieldedExpression = t.isExpressionStatement(yielded)
		? yielded.expression
		: singleDeclarator(yielded)?.init;
	const yieldExpression = t.isAssignmentExpression(yieldedExpression, {
			operator: '=',
		})
		? yieldedExpression.right
		: yieldedExpression;
	if (
		!t.isYieldExpression(yieldExpression, { delegate: false }) ||
		!t.isIdentifier(yieldExpression.argument, { name: nextName })
	) return null;

	// The only tolerated trailer is register-to-register generator resume state.
	// It is part of SaveGenerator/ResumeGenerator bookkeeping, not user code.
	if (
		!body.slice(5).every((trailer) => {
			const decl = singleDeclarator(trailer);
			return decl != null && t.isIdentifier(decl.id) &&
				/^r\d+_\d+$/.test(decl.id.name) && t.isIdentifier(decl.init) &&
				/^r\d+_\d+$/.test(decl.init.name);
		})
	) return null;

	return { completionName };
}

function delegateYieldLoopStart(
	body: t.Statement[],
	iteratorName: string,
): DelegateYieldLoopStart | null {
	const direct = weakDelegateYieldLoopStart(body[0], iteratorName);
	if (direct) return direct;

	if (body.length >= 2) {
		const sentDecl = singleDeclarator(body[0]);
		if (
			sentDecl &&
			t.isIdentifier(sentDecl.id) &&
			t.isIdentifier(sentDecl.init) &&
			matchDelegateYieldLoop(
				body[1],
				iteratorName,
				sentDecl.id.name,
				'',
			)
		) return { completionName: null };
	}

	let cursor = 0;
	if (isEnsureObjectStatement(body[cursor], iteratorName)) cursor++;
	const sentName = isUndefinedDeclaration(body[cursor]);
	const resultName = declaratorIdentifier(body[cursor + 1]);
	const loop = body[cursor + 2];
	return (
			sentName &&
			resultName &&
			loop &&
			matchDelegateYieldLoop(loop, iteratorName, sentName, resultName)
		)
		? { completionName: resultName! }
		: null;
}

export function blockStartsWithDelegateYieldLoop(
	body: t.Statement[],
	iteratorName: string,
) {
	return delegateYieldLoopStart(body, iteratorName) != null;
}

export interface DelegateIteratorAcquisition {
	index: number;
	iteratorName: string;
	argument: t.Expression;
	consumedNames: Set<string>;
}

interface ScannedDelegateIteratorAcquisition
	extends DelegateIteratorAcquisition {
	statement: t.Statement;
}

function scanDelegateIteratorAcquisitions(
	body: t.Statement[],
	stopAfterFirst = false,
): ScannedDelegateIteratorAcquisition[] {
	const acquisitions: ScannedDelegateIteratorAcquisition[] = [];
	const initializers = new Map<string, t.Expression | null | undefined>();
	let consumedNames = new Set<string>();
	const finishAcquisition = (
		acquisition: Omit<ScannedDelegateIteratorAcquisition, 'consumedNames'>,
		names: Set<string>,
	) => {
		acquisitions.push({ ...acquisition, consumedNames: names });
		for (const name of names) initializers.delete(name);
		consumedNames = new Set<string>();
		return stopAfterFirst;
	};
	const resolveExpression = (
		expr: t.Expression,
		seen = new Set<string>(),
	): t.Expression => {
		if (t.isIdentifier(expr)) {
			if (seen.has(expr.name)) return t.cloneNode(expr, true);
			const init = initializers.get(expr.name);
			// Preserve the identity of a locally constructed iterable. Replacing it
			// with the object literal would discard property writes (most importantly
			// its Symbol.iterator method) that occur before the delegate acquisition.
			if (t.isObjectExpression(init)) return t.cloneNode(expr, true);
			if (init && t.isExpression(init)) {
				consumedNames.add(expr.name);
				return resolveExpression(
					normalizeLoweredDelegateExpression(init),
					new Set([...seen, expr.name]),
				);
			}
		}
		if (t.isCallExpression(expr)) {
			if (
				t.isMemberExpression(expr.callee) &&
				memberName(expr.callee) === 'call'
			) {
				return resolveExpression(
					normalizeLoweredDelegateExpression(expr),
					seen,
				);
			}
			const callee = t.isExpression(expr.callee)
				? resolveExpression(expr.callee, seen)
				: t.cloneNode(expr.callee, true);
			return t.callExpression(
				callee,
				expr.arguments.map((arg) =>
					t.isExpression(arg)
						? resolveExpression(arg, seen)
						: t.cloneNode(arg, true)
				),
			);
		}
		return t.cloneNode(expr, true);
	};
	const loweredIteratorAcquisition = (expr: t.Expression) => {
		if (!t.isCallExpression(expr)) return null;
		if (!t.isMemberExpression(expr.callee)) return null;
		if (memberName(expr.callee) !== 'call') return null;
		const methodRef = expr.callee.object;
		if (!t.isIdentifier(methodRef)) return null;
		const methodInit = initializers.get(methodRef.name);
		if (!methodInit || !t.isMemberExpression(methodInit)) return null;
		consumedNames.add(methodRef.name);
		const property = methodInit.property;
		let isIteratorProperty = t.isMemberExpression(property)
			? memberName(property) === 'iterator'
			: false;
		if (!isIteratorProperty && t.isIdentifier(property)) {
			consumedNames.add(property.name);
			const propertyInit = initializers.get(property.name);
			if (
				t.isMemberExpression(propertyInit) &&
				t.isIdentifier(propertyInit.object)
			) {
				consumedNames.add(propertyInit.object.name);
			}
			isIteratorProperty = t.isMemberExpression(propertyInit) &&
				memberName(propertyInit) === 'iterator';
		}
		if (!isIteratorProperty) return null;
		const receiver = expr.arguments[0];
		return t.isExpression(receiver) ? resolveExpression(receiver) : null;
	};
	for (let i = 0; i < body.length; i++) {
		const statement = body[i]!;
		const acquisitionDecl = singleDeclarator(statement);
		if (
			acquisitionDecl &&
			t.isIdentifier(acquisitionDecl.id) &&
			t.isExpression(acquisitionDecl.init)
		) {
			const argument = delegateExpressionFromIteratorAcquisition(
				acquisitionDecl.init,
			);
			if (
				argument &&
				finishAcquisition(
					{
						index: i,
						statement,
						iteratorName: acquisitionDecl.id.name,
						argument: resolveExpression(argument),
					},
					consumedNames,
				)
			) break;
			if (argument) continue;
		}
		const acquisition = iteratorAcquisitionDeclaration(statement);
		if (
			acquisition &&
			finishAcquisition(
				{ index: i, statement, ...acquisition },
				new Set<string>(),
			)
		) break;
		if (acquisition) continue;
		const decl = singleDeclarator(statement);
		if (decl && t.isIdentifier(decl.id)) {
			if (t.isExpression(decl.init)) {
				const loweredArgument = loweredIteratorAcquisition(decl.init);
				if (
					loweredArgument &&
					finishAcquisition(
						{
							index: i,
							statement,
							iteratorName: decl.id.name,
							argument: loweredArgument,
						},
						consumedNames,
					)
				) break;
				if (loweredArgument) continue;
			}
			initializers.set(
				decl.id.name,
				t.isExpression(decl.init) ? decl.init : null,
			);
		}
	}
	return acquisitions;
}

export function findDelegateIteratorAcquisition(
	body: t.Statement[],
): DelegateIteratorAcquisition | null {
	return scanDelegateIteratorAcquisitions(body, true)[0] ?? null;
}

function isUnusedDelegateCompletionBlock(body: t.Statement[]) {
	if (body.length === 0) return true;
	const last = body.at(-1);
	if (!t.isReturnStatement(last)) return false;
	if (
		last.argument != null &&
		!isUndefinedNode(last.argument) &&
		!t.isIdentifier(last.argument)
	) return false;
	return body.slice(0, -1).every((stmt) => {
		if (!t.isExpressionStatement(stmt)) return false;
		const expr = stmt.expression;
		return t.isMemberExpression(expr) && memberName(expr) === 'value';
	});
}

function removeConsumedPreludeDeclarations(
	body: t.Statement[],
	beforeIndex: number,
	consumedNames: Set<string>,
) {
	if (consumedNames.size === 0 || beforeIndex === 0) return beforeIndex;
	const retained: t.Statement[] = [];
	for (let i = 0; i < beforeIndex; i++) {
		const statement = body[i]!;
		const declaration = singleDeclarator(statement);
		if (
			declaration && t.isIdentifier(declaration.id) &&
			consumedNames.has(declaration.id.name)
		) continue;
		retained.push(statement);
	}
	if (retained.length !== beforeIndex) {
		body.splice(0, beforeIndex, ...retained);
	}
	return retained.length;
}

function resolveFromDeclarations(
	expr: t.Expression,
	initializers: Map<string, t.Expression>,
	consumedNames: Set<string>,
	seen = new Set<string>(),
): t.Expression {
	if (t.isIdentifier(expr)) {
		if (seen.has(expr.name)) return t.cloneNode(expr, true);
		const init = initializers.get(expr.name);
		if (init) {
			consumedNames.add(expr.name);
			return resolveFromDeclarations(
				init,
				initializers,
				consumedNames,
				new Set([...seen, expr.name]),
			);
		}
	}
	if (t.isCallExpression(expr)) {
		const callee = t.isExpression(expr.callee)
			? resolveFromDeclarations(
				expr.callee,
				initializers,
				consumedNames,
				seen,
			)
			: t.cloneNode(expr.callee, true);
		return t.callExpression(
			callee,
			expr.arguments.map((arg) =>
				t.isExpression(arg)
					? resolveFromDeclarations(
						arg,
						initializers,
						consumedNames,
						seen,
					)
					: t.cloneNode(arg, true)
			),
		);
	}
	return t.cloneNode(expr, true);
}

interface DelegateReferenceFacts {
	counts: Map<string, number>;
	referencedOutsideRegion: Set<string>;
}

function delegateReferenceFacts(
	func: IRFunction,
	names: ReadonlySet<string>,
	excludedBlocks: ReadonlySet<number>,
): DelegateReferenceFacts {
	const counts = new Map<string, number>();
	const referencedOutsideRegion = new Set<string>();
	if (names.size === 0) return { counts, referencedOutsideRegion };

	for (const [address, block] of func.blocks) {
		const statements = [...block.body] as t.Statement[];
		if (block.branch) {
			statements.push(
				t.expressionStatement(block.branch as t.Expression),
			);
		}
		const wrapped = t.file(t.program(statements));
		traverse(wrapped, {
			Identifier(path) {
				const name = path.node.name;
				if (!names.has(name) || !path.isReferencedIdentifier()) return;
				const count = counts.get(name) ?? 0;
				if (count < 2) counts.set(name, count + 1);
				if (!excludedBlocks.has(address)) {
					referencedOutsideRegion.add(name);
				}
			},
		});
	}
	return { counts, referencedOutsideRegion };
}

function locallyConsumedDelegateNames(
	names: ReadonlySet<string>,
	facts: DelegateReferenceFacts,
) {
	return new Set(
		[...names].filter((name) => !facts.referencedOutsideRegion.has(name)),
	);
}

function sharedClosureArgument(
	acquisition: DelegateIteratorAcquisition,
	body: t.Statement[],
	referenceCounts: ReadonlyMap<string, number>,
): { argument: t.CallExpression; preservedNames: Set<string> } | null {
	const declarations = new Map<string, t.Expression>();
	for (const stmt of body.slice(0, acquisition.index)) {
		const decl = singleDeclarator(stmt);
		if (
			decl && t.isIdentifier(decl.id) && t.isExpression(decl.init)
		) declarations.set(decl.id.name, decl.init);
	}
	const candidates = [...acquisition.consumedNames].filter((name) => {
		const init = declarations.get(name);
		return t.isCallExpression(init) &&
			t.isV8IntrinsicIdentifier(init.callee) &&
			[
				'CreateClosure',
				'CreateGeneratorClosure',
				'CreateAsyncClosure',
			].includes(init.callee.name) &&
			(referenceCounts.get(name) ?? 0) > 1;
	});
	if (candidates.length !== 1) return null;

	const [closureName] = candidates;
	const preservedNames = new Set<string>();
	const preserveDependencies = (name: string) => {
		if (preservedNames.has(name)) return;
		preservedNames.add(name);
		const init = declarations.get(name);
		if (!init) return;
		const expression = t.file(t.program([
			t.expressionStatement(t.cloneNode(init, true)),
		]));
		traverse(expression, {
			Identifier(path) {
				if (!path.isReferencedIdentifier()) return;
				if (!declarations.has(path.node.name)) return;
				preserveDependencies(path.node.name);
			},
		});
	};
	preserveDependencies(closureName);
	return {
		argument: t.callExpression(t.identifier(closureName), []),
		preservedNames,
	};
}

function resolveDelegateArgumentFromPredecessor(
	func: IRFunction,
	blockAddress: number,
	argument: t.Expression,
) {
	const predecessors = [...func.predecessorsOf(blockAddress)];
	if (predecessors.length !== 1) return argument;
	const predecessor = func.blocks.get(predecessors[0]);
	if (!predecessor) return argument;

	const initializers = new Map<string, t.Expression>();
	for (const stmt of predecessor.body) {
		const decl = singleDeclarator(stmt as t.Statement);
		if (
			decl &&
			t.isIdentifier(decl.id) &&
			t.isExpression(decl.init)
		) {
			initializers.set(decl.id.name, decl.init);
		}
	}
	if (initializers.size === 0) {
		const [stmt] = predecessor.body as t.Statement[];
		if (
			predecessor.body.length === 1 &&
			t.isExpressionStatement(stmt) &&
			t.isCallExpression(stmt.expression) &&
			t.isV8IntrinsicIdentifier(stmt.expression.callee, {
				name: 'CreateGeneratorClosure',
			}) &&
			t.isCallExpression(argument) &&
			t.isIdentifier(argument.callee)
		) {
			(predecessor.body as t.Statement[]).splice(0, 1);
			return t.callExpression(
				t.cloneNode(stmt.expression, true),
				argument.arguments.map((arg) => t.cloneNode(arg, true)),
			);
		}
		return argument;
	}

	const consumedNames = new Set<string>();
	const resolved = resolveFromDeclarations(
		argument,
		initializers,
		consumedNames,
	);
	const referenceFacts = delegateReferenceFacts(
		func,
		consumedNames,
		new Set([predecessor.address, blockAddress]),
	);
	removeConsumedPreludeDeclarations(
		predecessor.body as t.Statement[],
		predecessor.body.length,
		locallyConsumedDelegateNames(consumedNames, referenceFacts),
	);
	return resolved;
}

function isUndefinedDeclaration(stmt: t.Statement) {
	const decl = singleDeclarator(stmt);
	if (!decl || !t.isIdentifier(decl.id)) return null;
	if (decl.init == null || isUndefinedNode(decl.init)) return decl.id.name;
	return null;
}

function undefinedResetName(stmt: t.Statement | undefined) {
	const declaration = stmt && isUndefinedDeclaration(stmt);
	if (declaration) return declaration;
	if (!t.isExpressionStatement(stmt)) return null;
	const expression = stmt.expression;
	return t.isAssignmentExpression(expression, { operator: '=' }) &&
			t.isIdentifier(expression.left) &&
			isUndefinedNode(expression.right)
		? expression.left.name
		: null;
}

function isEnsureObjectStatement(stmt: t.Statement, objectName: string) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	if (!t.isCallExpression(expr)) return false;
	const callee = expr.callee;
	return t.isMemberExpression(callee) &&
		t.isIdentifier(callee.object, { name: 'HermesInternal' }) &&
		t.isIdentifier(callee.property, { name: 'ensureObject' }) &&
		t.isIdentifier(expr.arguments[0], { name: objectName });
}

function isGeneratorSetDelegatedStatement(stmt: t.Statement) {
	const expr = t.isExpressionStatement(stmt)
		? stmt.expression
		: singleDeclarator(stmt)?.init;
	if (!t.isCallExpression(expr)) return false;
	const callee = expr.callee;
	return t.isMemberExpression(callee) &&
		t.isIdentifier(callee.object, { name: 'HermesInternal' }) &&
		t.isIdentifier(callee.property, { name: 'generatorSetDelegated' });
}

function isIteratorNextCall(
	expr: t.Expression | null | undefined,
	iteratorName: string,
	sentName: string,
) {
	if (!t.isCallExpression(expr)) return false;
	const callee = expr.callee;
	if (
		t.isMemberExpression(callee) &&
		memberName(callee) === 'call' &&
		expr.arguments.length === 2 &&
		t.isIdentifier(expr.arguments[0], { name: iteratorName }) &&
		t.isIdentifier(expr.arguments[1], { name: sentName })
	) {
		return true;
	}
	return t.isMemberExpression(callee) &&
		t.isIdentifier(callee.object, { name: iteratorName }) &&
		t.isIdentifier(callee.property, { name: 'next' }) &&
		expr.arguments.length === 1 &&
		t.isIdentifier(expr.arguments[0], { name: sentName });
}

function assignmentStatement(
	stmt: t.Statement,
	leftName: string,
	rightName: string,
) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	return t.isAssignmentExpression(expr, { operator: '=' }) &&
		t.isIdentifier(expr.left, { name: leftName }) &&
		t.isIdentifier(expr.right, { name: rightName });
}

function identifierAliasName(
	stmt: t.Statement | undefined,
	rightName: string,
): string | null {
	if (!stmt) return null;
	const declaration = singleDeclarator(stmt);
	if (
		declaration && t.isIdentifier(declaration.id) &&
		t.isIdentifier(declaration.init, { name: rightName })
	) return declaration.id.name;
	if (!t.isExpressionStatement(stmt)) return null;
	const expression = stmt.expression;
	return t.isAssignmentExpression(expression, { operator: '=' }) &&
			t.isIdentifier(expression.left) &&
			t.isIdentifier(expression.right, { name: rightName })
		? expression.left.name
		: null;
}

function iteratorProtocolPrelude(
	body: readonly t.Statement[],
	start: number,
	iteratorName: string,
) {
	let cursor = start;
	let receiverName = iteratorName;
	const consumedNames = new Set<string>();
	while (cursor < body.length) {
		const alias = identifierAliasName(body[cursor], receiverName);
		if (alias) {
			receiverName = alias;
			consumedNames.add(alias);
			cursor++;
			continue;
		}
		if (
			isEnsureObjectStatement(body[cursor], iteratorName) ||
			isEnsureObjectStatement(body[cursor], receiverName)
		) {
			cursor++;
			continue;
		}
		const next = skipIteratorNextPropertyReads(
			body,
			cursor,
			iteratorName,
		);
		if (next !== cursor) {
			for (let index = cursor; index < next; index++) {
				const statement = body[index];
				const declaration = singleDeclarator(statement);
				if (declaration && t.isIdentifier(declaration.id)) {
					consumedNames.add(declaration.id.name);
					continue;
				}
				const expression = t.isExpressionStatement(statement)
					? statement.expression
					: null;
				if (
					t.isAssignmentExpression(expression, { operator: '=' }) &&
					t.isIdentifier(expression.left)
				) consumedNames.add(expression.left.name);
			}
			cursor = next;
			continue;
		}
		break;
	}
	return { cursor, receiverName, consumedNames };
}

function isDoneBreak(stmt: t.Statement, nextName: string) {
	if (!t.isIfStatement(stmt)) return false;
	const test = stmt.test;
	if (
		!t.isMemberExpression(test) ||
		!t.isIdentifier(test.object, { name: nextName }) ||
		!t.isIdentifier(test.property, { name: 'done' })
	) return false;
	const consequent = t.isBlockStatement(stmt.consequent)
		? stmt.consequent.body[0]
		: stmt.consequent;
	return t.isBreakStatement(consequent);
}

function yieldAssignmentStatement(
	stmt: t.Statement,
	sentName: string,
	nextName: string,
) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	return t.isAssignmentExpression(expr, { operator: '=' }) &&
		t.isIdentifier(expr.left, { name: sentName }) &&
		t.isYieldExpression(expr.right, { delegate: false }) &&
		t.isIdentifier(expr.right.argument, { name: nextName });
}

function yieldResultStatement(stmt: t.Statement, nextName: string) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	return t.isYieldExpression(expr, { delegate: false }) &&
		t.isIdentifier(expr.argument, { name: nextName });
}

function yieldResultOrAssignmentStatement(stmt: t.Statement, nextName: string) {
	return yieldResultStatement(stmt, nextName) ||
		yieldedAssignmentTarget(stmt, nextName) != null;
}

function yieldedAssignmentTarget(stmt: t.Statement, nextName: string) {
	if (!t.isExpressionStatement(stmt)) return null;
	const expr = stmt.expression;
	if (
		!t.isAssignmentExpression(expr, { operator: '=' }) ||
		!t.isIdentifier(expr.left) ||
		!t.isYieldExpression(expr.right, { delegate: false }) ||
		!t.isIdentifier(expr.right.argument, { name: nextName })
	) return null;
	return expr.left.name;
}

function isIteratorNextCallWithSentValue(
	expr: t.Expression | null | undefined,
	iteratorName: string,
) {
	if (!t.isCallExpression(expr)) return false;
	const callee = expr.callee;
	if (
		t.isMemberExpression(callee) &&
		memberName(callee) === 'call' &&
		expr.arguments.length >= 1 &&
		t.isIdentifier(expr.arguments[0], { name: iteratorName })
	) return true;
	return t.isMemberExpression(callee) &&
		t.isIdentifier(callee.object, { name: iteratorName }) &&
		t.isIdentifier(callee.property, { name: 'next' }) &&
		expr.arguments.length === 1;
}

function isIteratorNextCallWithOptionalSentValue(
	expr: t.Expression | null | undefined,
	iteratorName: string,
	sentName: string | null,
) {
	if (!t.isCallExpression(expr)) return false;
	const callee = expr.callee;
	const matchesSent = (arg: t.CallExpression['arguments'][number]) =>
		sentName == null
			? isUndefinedNode(arg)
			: t.isIdentifier(arg, { name: sentName });
	if (
		t.isMemberExpression(callee) &&
		memberName(callee) === 'call' &&
		expr.arguments.length === 2 &&
		t.isIdentifier(expr.arguments[0], { name: iteratorName }) &&
		matchesSent(expr.arguments[1])
	) return true;
	return t.isMemberExpression(callee) &&
		t.isIdentifier(callee.object, { name: iteratorName }) &&
		t.isIdentifier(callee.property, { name: 'next' }) &&
		expr.arguments.length === 1 &&
		matchesSent(expr.arguments[0]);
}

function doneBranchStatements(stmt: t.Statement, nextName: string) {
	if (!t.isIfStatement(stmt)) return null;
	const test = stmt.test;
	if (
		!t.isMemberExpression(test) ||
		!t.isIdentifier(test.object, { name: nextName }) ||
		memberName(test) !== 'done' ||
		!t.isBlockStatement(stmt.consequent)
	) return null;
	return stmt.consequent.body;
}

function doneBranchStatementsOrBreak(stmt: t.Statement, nextName: string) {
	const doneBody = doneBranchStatements(stmt, nextName);
	if (doneBody) return doneBody;
	return isDoneBreak(stmt, nextName) ? [] : null;
}

function doneBranchStatementsForAnyObject(stmt: t.Statement) {
	if (!t.isIfStatement(stmt)) return null;
	const test = stmt.test;
	if (
		!t.isMemberExpression(test) ||
		memberName(test) !== 'done' ||
		!t.isBlockStatement(stmt.consequent)
	) return null;
	return stmt.consequent.body;
}

function alternateYieldTarget(stmt: t.Statement, nextName: string) {
	if (!t.isIfStatement(stmt) || !stmt.alternate) return null;
	const alternate = t.isBlockStatement(stmt.alternate)
		? stmt.alternate.body
		: [stmt.alternate];
	if (alternate.length !== 1) return null;
	return yieldedAssignmentTarget(alternate[0], nextName);
}

function isEmptyReturn(stmt: t.Statement) {
	return t.isReturnStatement(stmt) &&
		(stmt.argument == null || isUndefinedNode(stmt.argument));
}

function removeObsoleteYieldTargetDeclaration(
	body: t.Statement[],
	beforeIndex: number,
	targetName: string,
) {
	for (let i = beforeIndex - 1; i >= 0; i--) {
		const decl = singleDeclarator(body[i]);
		if (!decl || !t.isIdentifier(decl.id, { name: targetName })) {
			continue;
		}
		body.splice(i, 1);
		return i;
	}
	return beforeIndex;
}

function matchDelegateYieldLoop(
	stmt: t.Statement,
	iteratorName: string,
	sentName: string,
	resultName: string,
) {
	if (
		!t.isWhileStatement(stmt) || !t.isBooleanLiteral(stmt.test, {
			value: true,
		})
	) return false;
	if (!t.isBlockStatement(stmt.body)) return false;
	const body = stmt.body.body;
	// TODO: workaround. Natural-loop reduction should not leave an explicit
	// terminal `continue` at the end of a loop body; tolerate it here so delegate
	// yield recognition is not blocked by that structuring artifact.
	const hasTerminalContinue = t.isContinueStatement(body.at(-1));
	const effectiveBody = hasTerminalContinue ? body.slice(0, -1) : body;

	const nextDecl = singleDeclarator(effectiveBody[0]);
	if (
		!nextDecl ||
		!t.isIdentifier(nextDecl.id) ||
		!isIteratorNextCall(nextDecl.init, iteratorName, sentName)
	) return false;
	const nextName = nextDecl.id.name;

	if (effectiveBody.length === 6) {
		return isEnsureObjectStatement(effectiveBody[1], nextName) &&
			assignmentStatement(effectiveBody[2], resultName, nextName) &&
			isDoneBreak(effectiveBody[3], nextName) &&
			isGeneratorSetDelegatedStatement(effectiveBody[4]) &&
			yieldAssignmentStatement(effectiveBody[5], sentName, nextName);
	}

	if (effectiveBody.length === 5) {
		return isEnsureObjectStatement(effectiveBody[1], nextName) &&
			isDoneBreak(effectiveBody[2], nextName) &&
			isGeneratorSetDelegatedStatement(effectiveBody[3]) &&
			yieldAssignmentStatement(effectiveBody[4], sentName, nextName);
	}

	return false;
}

function matchBreakDelegateYieldLoop(
	stmt: t.Statement,
	iteratorName: string,
	sentName: string,
) {
	if (
		!t.isWhileStatement(stmt) || !t.isBooleanLiteral(stmt.test, {
			value: true,
		})
	) return null;
	if (!t.isBlockStatement(stmt.body)) return null;
	const body = stmt.body.body;
	const hasTerminalContinue = t.isContinueStatement(body.at(-1));
	const effectiveBody = hasTerminalContinue ? body.slice(0, -1) : body;
	if (effectiveBody.length !== 4) return null;

	const nextDecl = singleDeclarator(effectiveBody[0]);
	if (
		!nextDecl ||
		!t.isIdentifier(nextDecl.id) ||
		!isIteratorNextCall(nextDecl.init, iteratorName, sentName)
	) return null;
	const nextName = nextDecl.id.name;
	return isEnsureObjectStatement(effectiveBody[1], nextName) &&
			isDoneBreak(effectiveBody[2], nextName) &&
			yieldResultStatement(effectiveBody[3], nextName)
		? { nextName }
		: null;
}

function isDiscardedCompletionValueRead(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	if (!t.isMemberExpression(expr) || memberName(expr) !== 'value') {
		return false;
	}
	return t.isCallExpression(expr.object) &&
		t.isV8IntrinsicIdentifier(expr.object.callee, { name: 'Phi' });
}

function removeDiscardedCompletionValueReads(body: t.Statement[]) {
	let write = 0;
	for (let read = 0; read < body.length; read++) {
		const statement = body[read]!;
		if (isDiscardedCompletionValueRead(statement)) continue;
		body[write++] = statement;
	}
	if (write === body.length) return false;
	body.length = write;
	return true;
}

function matchProtectedDelegateYieldLoop(
	stmt: t.Statement,
	iteratorName: string,
	sentName: string,
) {
	if (
		!t.isWhileStatement(stmt) || !t.isBooleanLiteral(stmt.test, {
			value: true,
		})
	) return null;
	if (!t.isBlockStatement(stmt.body)) return null;
	const body = stmt.body.body;
	const hasTerminalContinue = t.isContinueStatement(body.at(-1));
	const effectiveBody = hasTerminalContinue ? body.slice(0, -1) : body;
	if (effectiveBody.length !== 4) return null;

	const nextDecl = singleDeclarator(effectiveBody[0]);
	if (
		!nextDecl ||
		!t.isIdentifier(nextDecl.id) ||
		!isIteratorNextCall(nextDecl.init, iteratorName, sentName)
	) return null;
	const nextName = nextDecl.id.name;
	if (!isEnsureObjectStatement(effectiveBody[1], nextName)) return null;
	if (!isDoneBreak(effectiveBody[2], nextName)) return null;

	const tryStmt = effectiveBody[3];
	if (!t.isTryStatement(tryStmt) || !tryStmt.handler || tryStmt.finalizer) {
		return null;
	}
	if (!containsLoweredDelegateCatchMachinery(tryStmt.handler.body.body)) {
		return null;
	}
	const tryBody = tryStmt.block.body;
	if (
		tryBody.length < 3 ||
		!isGeneratorSetDelegatedStatement(tryBody[0]) ||
		!yieldAssignmentStatement(tryBody[1], sentName, nextName) ||
		!t.isContinueStatement(tryBody[2])
	) return null;

	for (const catchStmt of tryStmt.handler.body.body) {
		const doneBody = doneBranchStatementsForAnyObject(catchStmt);
		if (!doneBody) continue;
		const trailing = doneBody.map((doneStmt) =>
			t.cloneNode(doneStmt, true)
		);
		removeDiscardedCompletionValueReads(trailing);
		return trailing;
	}
	return null;
}

function rewriteCompletionValueReads(
	body: t.Statement[],
	start: number,
	resultName: string,
	replacementName = resultName,
) {
	let meaningfulValueRead = false;
	let invalidUse = false;
	const valueReads: NodePath<t.MemberExpression>[] = [];
	const wrapped = t.file(t.program(body.slice(start)));
	traverse(wrapped, {
		MemberExpression(path: NodePath<t.MemberExpression>) {
			if (
				t.isIdentifier(path.node.object, { name: resultName }) &&
				memberName(path.node) === 'value'
			) {
				if (!path.parentPath.isExpressionStatement()) {
					meaningfulValueRead = true;
				}
				valueReads.push(path);
				path.skip();
			}
		},
		Identifier(path: NodePath<t.Identifier>) {
			if (
				path.node.name === resultName &&
				path.isReferencedIdentifier()
			) {
				invalidUse = true;
				path.stop();
			}
		},
	});
	if (invalidUse) return null;
	for (const path of valueReads) {
		path.replaceWith(t.identifier(replacementName));
	}

	let write = start;
	for (let read = start; read < body.length; read++) {
		const statement = body[read]!;
		if (
			t.isExpressionStatement(statement) &&
			t.isIdentifier(statement.expression, { name: resultName })
		) continue;
		body[write++] = statement;
	}
	body.length = write;
	return meaningfulValueRead;
}

function delegateYieldExpressionStatement(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return null;
	const expr = stmt.expression;
	if (
		!t.isCallExpression(expr) ||
		!t.isV8IntrinsicIdentifier(expr.callee, { name: 'DelegateYield' }) ||
		expr.arguments.length !== 1 ||
		!t.isExpression(expr.arguments[0])
	) return null;
	return t.expressionStatement(delegateYieldIntrinsic(expr.arguments[0]));
}

function delegateYieldCallExpression(stmt: t.Statement | undefined) {
	if (!t.isExpressionStatement(stmt)) return null;
	const expr = stmt.expression;
	if (
		t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, { name: 'DelegateYield' })
	) return expr;
	return null;
}

function replacePhiValueReadsWithIdentifier(
	body: t.Statement[],
	start: number,
	name: string,
) {
	let changed = false;
	const wrapped = t.file(t.program(body.slice(start)));
	traverse(wrapped, {
		MemberExpression(path) {
			if (memberName(path.node) !== 'value') return;
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

function hoistStructuredDelegateCompletion(body: t.Statement[]) {
	let suffixHasPhiValueRead = false;
	let candidateIndex = -1;
	let candidateCall: t.CallExpression | null = null;
	for (let i = body.length - 1; i >= 0; i--) {
		const stmt = body[i]!;
		if (
			suffixHasPhiValueRead &&
			t.isTryStatement(stmt) &&
			stmt.finalizer &&
			stmt.block.body.length === 1
		) {
			const delegateYield = delegateYieldCallExpression(
				stmt.block.body[0],
			);
			if (delegateYield) {
				candidateIndex = i;
				candidateCall = delegateYield;
			}
		}
		if (suffixHasPhiValueRead) continue;
		t.traverseFast(stmt, (node) => {
			if (
				t.isMemberExpression(node) &&
				memberName(node) === 'value' &&
				t.isCallExpression(node.object) &&
				t.isV8IntrinsicIdentifier(node.object.callee, {
					name: 'Phi',
				})
			) {
				suffixHasPhiValueRead = true;
				return t.traverseFast.skip;
			}
		});
	}
	if (candidateIndex < 0 || !candidateCall) return false;

	const completionName = `r${candidateIndex}_delegate`;
	if (
		!replacePhiValueReadsWithIdentifier(
			body,
			candidateIndex + 1,
			completionName,
		)
	) return false;
	const candidate = body[candidateIndex];
	if (!t.isTryStatement(candidate)) return false;
	candidate.block.body = [
		t.expressionStatement(
			t.assignmentExpression(
				'=',
				t.identifier(completionName),
				t.cloneNode(candidateCall, true),
			),
		),
	];
	body.splice(
		candidateIndex,
		0,
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier(completionName)),
		]),
	);
	return true;
}

function containsLoweredDelegateCatchMachinery(body: t.Statement[]) {
	for (const statement of body) {
		let found = false;
		t.traverseFast(statement, (node) => {
			if (found) return t.traverseFast.skip;
			if (
				t.isCallExpression(node) &&
				t.isMemberExpression(node.callee) &&
				(t.matchesPattern(node.callee, [
					'HermesInternal',
					'getMethod',
				]) ||
					t.matchesPattern(node.callee, [
						'HermesInternal',
						'generatorSetDelegated',
					]))
			) {
				found = true;
				return t.traverseFast.skip;
			}
		});
		if (found) return true;
	}
	return false;
}

function handlerContainsLoweredDelegateCatchMachinery(
	func: IRFunction,
	handler: number,
) {
	const entry = func.blocks.get(handler);
	if (!entry) return false;
	return [handler, ...entry.consequentAddresses].some((address) => {
		const block = func.blocks.get(address);
		return block != null && containsLoweredDelegateCatchMachinery(
			block.body as t.Statement[],
		);
	});
}

function isUnconditionalBreakIf(stmt: t.Statement | undefined) {
	return t.isIfStatement(stmt) &&
		t.isBooleanLiteral(stmt.test, { value: true }) &&
		t.isBlockStatement(stmt.consequent) &&
		stmt.consequent.body.length === 1 &&
		t.isBreakStatement(stmt.consequent.body[0]) &&
		stmt.alternate == null;
}

function isUndefinedDeclarationList(stmt: t.Statement | undefined) {
	return t.isVariableDeclaration(stmt) && stmt.declarations.length > 0 &&
		stmt.declarations.every((decl) =>
			t.isVariableDeclarator(decl) &&
			(decl.init == null || isUndefinedNode(decl.init))
		);
}

function isDiscardedMemberValueRead(stmt: t.Statement | undefined) {
	return t.isExpressionStatement(stmt) &&
		t.isMemberExpression(stmt.expression) &&
		memberName(stmt.expression) === 'value';
}

function reduceLoopCarriedProtectedDelegateLoop(
	body: t.Statement[],
	acquisition: DelegateAcquisition,
	cursor: number,
) {
	if (!isUndefinedDeclarationList(body[cursor])) return false;
	const stmt = body[cursor + 1];
	if (
		!t.isWhileStatement(stmt) ||
		!t.isBooleanLiteral(stmt.test, { value: true }) ||
		!t.isBlockStatement(stmt.body)
	) return false;
	const loopBody = stmt.body.body;
	if (loopBody.length < 3) return false;
	const doneBranch = loopBody.find((loopStmt) =>
		t.isIfStatement(loopStmt) && t.isBlockStatement(loopStmt.consequent) &&
		isDiscardedMemberValueRead(loopStmt.consequent.body[0])
	);
	if (
		!t.isIfStatement(doneBranch) ||
		!t.isBlockStatement(doneBranch.consequent)
	) {
		return false;
	}
	const tryStmt = loopBody.find((loopStmt) => t.isTryStatement(loopStmt));
	if (
		!t.isTryStatement(tryStmt) ||
		!tryStmt.handler ||
		!containsLoweredDelegateCatchMachinery(tryStmt.handler.body.body) ||
		!tryStmt.block.body.some(isGeneratorSetDelegatedStatement)
	) return false;

	const trailing = doneBranch.consequent.body.slice(1).map((doneStmt) =>
		t.cloneNode(doneStmt, true)
	);
	const start = removeConsumedPreludeDeclarations(
		body,
		acquisition.index,
		acquisition.consumedNames,
	);
	cursor -= acquisition.index - start;
	body.splice(
		start,
		cursor + 2 - start,
		t.expressionStatement(delegateYieldIntrinsic(acquisition.argument)),
		...trailing,
	);
	return true;
}

type DelegateAcquisition = NonNullable<
	ReturnType<typeof findDelegateIteratorAcquisition>
>;

function reduceSimpleDelegateLoop(
	body: t.Statement[],
	loopIndex: number,
	acquisition: DelegateAcquisition,
	sentName: string | null,
) {
	const stmt = body[loopIndex];
	if (
		!t.isWhileStatement(stmt) ||
		!t.isBooleanLiteral(stmt.test, { value: true }) ||
		!t.isBlockStatement(stmt.body)
	) return false;

	const loopBody = stmt.body.body;
	if (
		!loopBody.slice(0, acquisition.index).every((loopStmt) =>
			t.isVariableDeclaration(loopStmt) ||
			t.isExpressionStatement(loopStmt)
		)
	) return false;

	let cursor = acquisition.index + 1;
	if (
		isEnsureObjectStatement(
			loopBody[cursor],
			acquisition.iteratorName,
		)
	) {
		cursor++;
	}
	cursor = skipIteratorNextPropertyReads(
		loopBody,
		cursor,
		acquisition.iteratorName,
	);

	const nextDecl = singleDeclarator(loopBody[cursor]);
	if (
		!nextDecl ||
		!t.isIdentifier(nextDecl.id) ||
		!isIteratorNextCallWithOptionalSentValue(
			nextDecl.init,
			acquisition.iteratorName,
			sentName,
		)
	) return false;
	const nextName = nextDecl.id.name;
	if (!isEnsureObjectStatement(loopBody[cursor + 1], nextName)) {
		return false;
	}
	const doneBody = doneBranchStatementsOrBreak(
		loopBody[cursor + 2],
		nextName,
	);
	if (doneBody == null) return false;
	if (doneBody.some((doneStmt) => t.isBreakStatement(doneStmt))) {
		return false;
	}

	let yieldIndex = cursor + 3;
	if (isGeneratorSetDelegatedStatement(loopBody[yieldIndex])) yieldIndex++;
	const yieldTarget = yieldedAssignmentTarget(loopBody[yieldIndex], nextName);
	if (
		yieldTarget == null &&
		!yieldResultStatement(loopBody[yieldIndex], nextName)
	) return false;
	if (
		loopBody.slice(yieldIndex + 1).some((loopStmt) =>
			!t.isContinueStatement(loopStmt) &&
			!isUnconditionalBreakIf(loopStmt)
		)
	) return false;

	const trailing = doneBody.map((doneStmt) => t.cloneNode(doneStmt, true));
	const hasCompletionReads = rewriteCompletionValueReads(
		trailing,
		0,
		nextName,
	);
	if (hasCompletionReads == null) return false;
	if (!hasCompletionReads && trailing.length === 1) {
		if (isEmptyReturn(trailing[0])) trailing.splice(0, 1);
	}

	const prelude = loopBody.slice(0, acquisition.index).map((loopStmt) =>
		t.cloneNode(loopStmt, true)
	);
	removeConsumedPreludeDeclarations(
		prelude,
		prelude.length,
		acquisition.consumedNames,
	);
	const replacement: t.Statement[] = [
		...prelude,
		hasCompletionReads
			? t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier(nextName),
					delegateYieldIntrinsic(acquisition.argument),
				),
			])
			: t.expressionStatement(
				delegateYieldIntrinsic(acquisition.argument),
			),
		...trailing,
	];
	if (yieldTarget) {
		removeObsoleteYieldTargetDeclaration(
			replacement,
			replacement.length,
			yieldTarget,
		);
	}

	body.splice(loopIndex, 1, ...replacement);
	return true;
}

function reduceBodyLevelDirectDelegateLoop(
	body: t.Statement[],
	acquisition: DelegateAcquisition,
	loopIndex: number,
) {
	const stmt = body[loopIndex];
	if (
		!t.isWhileStatement(stmt) ||
		!t.isBooleanLiteral(stmt.test, { value: true }) ||
		!t.isBlockStatement(stmt.body)
	) return false;
	const loopBody = stmt.body.body;
	const tryStmt = (loopBody.length === 1 ||
			(loopBody.length === 2 && isUnconditionalBreakIf(loopBody[1]))) &&
			t.isTryStatement(loopBody[0])
		? loopBody[0]
		: null;
	const targetBody = tryStmt ? tryStmt.block.body : loopBody;

	let cursor = 0;
	const sentName = isUndefinedDeclaration(targetBody[cursor]);
	if (sentName) cursor++;
	cursor = skipIteratorNextPropertyReads(
		targetBody,
		cursor,
		acquisition.iteratorName,
	);

	const nextDecl = singleDeclarator(targetBody[cursor]);
	if (
		!nextDecl ||
		!t.isIdentifier(nextDecl.id) ||
		!isIteratorNextCallWithOptionalSentValue(
			nextDecl.init,
			acquisition.iteratorName,
			sentName,
		)
	) return false;
	const nextName = nextDecl.id.name;
	if (!isEnsureObjectStatement(targetBody[cursor + 1], nextName)) {
		return false;
	}

	let doneIndex = cursor + 2;
	while (t.isVariableDeclaration(targetBody[doneIndex])) doneIndex++;
	const maybeResultAssign = targetBody[doneIndex];
	if (
		t.isExpressionStatement(maybeResultAssign) &&
		t.isAssignmentExpression(maybeResultAssign.expression, {
			operator: '=',
		}) &&
		t.isIdentifier(maybeResultAssign.expression.right, { name: nextName })
	) {
		doneIndex++;
	}
	const doneBody = doneBranchStatements(targetBody[doneIndex], nextName);
	if (doneBody == null) return false;
	if (doneBody.some((doneStmt) => t.isBreakStatement(doneStmt))) {
		return false;
	}

	const ifStmt = targetBody[doneIndex];
	if (!t.isIfStatement(ifStmt)) return false;
	const yieldBody = ifStmt.alternate
		? (t.isBlockStatement(ifStmt.alternate)
			? ifStmt.alternate.body
			: [ifStmt.alternate])
		: targetBody.slice(doneIndex + 1);
	if (
		yieldBody.length < 2 ||
		!isGeneratorSetDelegatedStatement(yieldBody[0]) ||
		!yieldResultOrAssignmentStatement(yieldBody[1], nextName)
	) return false;
	if (
		yieldBody.slice(2).some((stmt) =>
			!t.isContinueStatement(stmt) && !isUnconditionalBreakIf(stmt)
		)
	) return false;
	if (
		tryStmt &&
		(!tryStmt.handler ||
			!containsLoweredDelegateCatchMachinery(tryStmt.handler.body.body))
	) return false;

	const trailing = doneBody.map((doneStmt) => t.cloneNode(doneStmt, true));
	const hasCompletionReads = rewriteCompletionValueReads(
		trailing,
		0,
		nextName,
	);
	if (hasCompletionReads == null) return false;
	if (!hasCompletionReads && trailing.length === 1) {
		if (isEmptyReturn(trailing[0])) trailing.splice(0, 1);
	}

	const replacement: t.Statement[] = [
		hasCompletionReads
			? t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier(nextName),
					delegateYieldIntrinsic(acquisition.argument),
				),
			])
			: t.expressionStatement(
				delegateYieldIntrinsic(acquisition.argument),
			),
		...trailing,
	];
	const start = removeConsumedPreludeDeclarations(
		body,
		acquisition.index,
		acquisition.consumedNames,
	);
	body.splice(start, loopIndex - start + 1, ...replacement);
	return true;
}

interface InlineProtectedDelegateYield {
	yieldTarget: string | null;
}

function matchInlineProtectedDelegateYield(
	body: t.Statement[],
	start: number,
	nextName: string,
): InlineProtectedDelegateYield | null {
	let cursor = start;
	const declaredYieldTarget = isUndefinedDeclaration(body[cursor]);
	if (declaredYieldTarget) cursor++;
	if (cursor !== body.length - 1) return null;

	const stmt = body[cursor];
	if (
		!t.isTryStatement(stmt) || !stmt.handler || stmt.finalizer ||
		!containsLoweredDelegateCatchMachinery(stmt.handler.body.body)
	) return null;
	const tryBody = stmt.block.body;
	if (
		tryBody.length < 2 ||
		!isGeneratorSetDelegatedStatement(tryBody[0])
	) return null;
	const yieldTarget = yieldedAssignmentTarget(tryBody[1], nextName);
	if (
		yieldTarget == null &&
		!yieldResultStatement(tryBody[1], nextName)
	) return null;
	if (declaredYieldTarget && yieldTarget !== declaredYieldTarget) return null;
	if (
		tryBody.slice(2).some((tryStmt) =>
			!t.isContinueStatement(tryStmt) &&
			!isUnconditionalBreakIf(tryStmt)
		)
	) return null;
	return { yieldTarget };
}

function delegateCompletionReplacement(
	trailing: t.Statement[],
	nextName: string,
	argument: t.Expression,
): t.Statement | null {
	const aliasStatement = trailing[0];
	const completionAlias = identifierAliasName(aliasStatement, nextName);
	if (completionAlias) {
		trailing.shift();
		if (
			rewriteCompletionValueReads(
					trailing,
					0,
					completionAlias,
					completionAlias,
				) == null ||
			rewriteCompletionValueReads(
					trailing,
					0,
					nextName,
					completionAlias,
				) == null
		) return null;
		const declaration = singleDeclarator(aliasStatement);
		if (
			t.isVariableDeclaration(aliasStatement) &&
			declaration &&
			t.isIdentifier(declaration.id, { name: completionAlias })
		) {
			return t.variableDeclaration(aliasStatement.kind, [
				t.variableDeclarator(
					t.cloneNode(declaration.id),
					delegateYieldIntrinsic(argument),
				),
			]);
		}
		return t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier(completionAlias),
			delegateYieldIntrinsic(argument),
		));
	}

	const hasCompletionReads = rewriteCompletionValueReads(
		trailing,
		0,
		nextName,
	);
	if (hasCompletionReads == null) return null;
	return hasCompletionReads
		? t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier(nextName),
				delegateYieldIntrinsic(argument),
			),
		])
		: t.expressionStatement(delegateYieldIntrinsic(argument));
}

function isBreakableStatement(node: t.Node): boolean {
	return t.isWhileStatement(node) || t.isDoWhileStatement(node) ||
		t.isForStatement(node) || t.isForInStatement(node) ||
		t.isForOfStatement(node) || t.isSwitchStatement(node);
}

function containsUnlabelledBreakAtDepth(
	node: t.Node,
	breakableDepth: number,
): boolean {
	if (t.isFunction(node)) return false;
	if (t.isBreakStatement(node)) {
		return node.label == null && breakableDepth === 0;
	}
	const childDepth = breakableDepth + (isBreakableStatement(node) ? 1 : 0);
	for (const key of t.VISITOR_KEYS[node.type] ?? []) {
		const child = (node as unknown as Record<string, unknown>)[key];
		if (Array.isArray(child)) {
			for (const entry of child) {
				if (
					t.isNode(entry) &&
					containsUnlabelledBreakAtDepth(entry, childDepth)
				) return true;
			}
		} else if (
			t.isNode(child) &&
			containsUnlabelledBreakAtDepth(child, childDepth)
		) {
			return true;
		}
	}
	return false;
}

function infiniteWhileCannotFallThrough(stmt: t.WhileStatement) {
	return t.isBooleanLiteral(stmt.test, { value: true }) &&
		!containsUnlabelledBreakAtDepth(stmt.body, 0);
}

function isDelegateThrowTypeErrorStatement(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expression = stmt.expression;
	if (
		!t.isCallExpression(expression) ||
		!t.isMemberExpression(expression.callee) ||
		!t.isIdentifier(expression.callee.object, { name: 'HermesInternal' }) ||
		memberName(expression.callee) !== 'throwTypeError'
	) return false;
	const message = expression.arguments[0];
	return t.isStringLiteral(message) &&
		message.value === 'yield* delegate must have a .throw() method';
}

function stripUnreachableDelegateProtocolSuffix(body: t.Statement[]) {
	const protocolAfter = new Array<boolean>(body.length);
	let suffixContainsProtocol = false;
	for (let i = body.length - 1; i >= 0; i--) {
		protocolAfter[i] = suffixContainsProtocol;
		const statement = body[i]!;
		suffixContainsProtocol ||=
			isDelegateThrowTypeErrorStatement(statement) ||
			containsLoweredDelegateCatchMachinery([statement]);
	}

	for (let i = 0; i < body.length - 1; i++) {
		const stmt = body[i]!;
		if (
			t.isWhileStatement(stmt) &&
			protocolAfter[i] &&
			infiniteWhileCannotFallThrough(stmt)
		) {
			body.splice(i + 1);
			return true;
		}
	}
	return false;
}

function reduceRecoveredDelegateYieldStatements(body: t.Statement[]) {
	let changed = false;
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (
			!t.isWhileStatement(stmt) ||
			!t.isBooleanLiteral(stmt.test, { value: true }) ||
			!t.isBlockStatement(stmt.body)
		) continue;

		const loopBody = stmt.body.body;
		const tryStmt = (loopBody.length === 1 ||
				(loopBody.length === 2 &&
					isUnconditionalBreakIf(loopBody[1]))) &&
				t.isTryStatement(loopBody[0])
			? loopBody[0]
			: null;
		const targetBody = tryStmt ? tryStmt.block.body : loopBody;
		const acquisition = findDelegateIteratorAcquisition(targetBody);
		if (!acquisition) continue;

		let cursor = acquisition.index + 1;
		if (
			isEnsureObjectStatement(
				targetBody[cursor],
				acquisition.iteratorName,
			)
		) {
			cursor++;
		}
		cursor = skipIteratorNextPropertyReads(
			targetBody,
			cursor,
			acquisition.iteratorName,
		);
		if (undefinedResetName(targetBody[cursor])) cursor++;

		const nextDecl = singleDeclarator(targetBody[cursor]);
		if (
			!nextDecl ||
			!t.isIdentifier(nextDecl.id) ||
			!isIteratorNextCallWithSentValue(
				nextDecl.init,
				acquisition.iteratorName,
			)
		) continue;
		const nextName = nextDecl.id.name;
		if (!isEnsureObjectStatement(targetBody[cursor + 1], nextName)) {
			continue;
		}
		const ifStmt = targetBody[cursor + 2];
		const doneBody = doneBranchStatements(ifStmt, nextName);
		if (!doneBody) continue;
		const alternateTarget = alternateYieldTarget(ifStmt, nextName);
		const protectedDelegate = alternateTarget == null
			? matchInlineProtectedDelegateYield(
				targetBody,
				cursor + 3,
				nextName,
			)
			: null;
		const yieldTarget = alternateTarget ??
			protectedDelegate?.yieldTarget ?? null;
		if (!alternateTarget && !protectedDelegate) continue;

		const trailing = doneBody.map((doneStmt) =>
			t.cloneNode(doneStmt, true)
		);
		const delegateCompletion = protectedDelegate
			? delegateCompletionReplacement(
				trailing,
				nextName,
				acquisition.argument,
			)
			: (() => {
				const hasCompletionReads = rewriteCompletionValueReads(
					trailing,
					0,
					nextName,
				);
				if (hasCompletionReads == null) return null;
				if (!hasCompletionReads && trailing.length === 1) {
					if (isEmptyReturn(trailing[0])) trailing.splice(0, 1);
				}
				return hasCompletionReads
					? t.variableDeclaration('const', [
						t.variableDeclarator(
							t.identifier(nextName),
							delegateYieldIntrinsic(acquisition.argument),
						),
					])
					: t.expressionStatement(
						delegateYieldIntrinsic(acquisition.argument),
					);
			})();
		if (!delegateCompletion) continue;

		const replacement: t.Statement[] = [
			delegateCompletion,
			...trailing,
		];

		const start = removeConsumedPreludeDeclarations(
			targetBody,
			acquisition.index,
			acquisition.consumedNames,
		);
		targetBody.splice(
			start,
			targetBody.length - start,
			...replacement,
		);
		if (yieldTarget) {
			removeObsoleteYieldTargetDeclaration(
				targetBody,
				start,
				yieldTarget,
			);
		}

		if (protectedDelegate) {
			changed = true;
			continue;
		}

		if (tryStmt) {
			body.splice(i, 1, t.cloneNode(tryStmt, true));
		} else {
			body.splice(
				i,
				1,
				...targetBody.map((bodyStmt) => t.cloneNode(bodyStmt, true)),
			);
			i += targetBody.length - 1;
		}
		changed = true;
		continue;
	}

	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (
			!t.isWhileStatement(stmt) ||
			!t.isBooleanLiteral(stmt.test, { value: true }) ||
			!t.isBlockStatement(stmt.body)
		) continue;

		const loopBody = stmt.body.body;
		const acquisition = findDelegateIteratorAcquisition(loopBody);
		if (!acquisition) continue;
		let sentName: string | null = null;
		for (let j = i - 1; j >= 0; j--) {
			sentName = isUndefinedDeclaration(body[j]);
			if (sentName || !t.isVariableDeclaration(body[j])) break;
		}
		if (reduceSimpleDelegateLoop(body, i, acquisition, sentName)) {
			changed = true;
			continue;
		}
		if (
			!loopBody.slice(0, acquisition.index).every((loopStmt) =>
				t.isVariableDeclaration(loopStmt) ||
				t.isExpressionStatement(loopStmt)
			)
		) continue;

		const prelude = iteratorProtocolPrelude(
			loopBody,
			acquisition.index + 1,
			acquisition.iteratorName,
		);
		let cursor = prelude.cursor;

		const nextDecl = singleDeclarator(loopBody[cursor]);
		if (
			!nextDecl ||
			!t.isIdentifier(nextDecl.id) ||
			!isIteratorNextCallWithSentValue(
				nextDecl.init,
				prelude.receiverName,
			)
		) continue;
		const nextName = nextDecl.id.name;
		if (!isEnsureObjectStatement(loopBody[cursor + 1], nextName)) {
			continue;
		}
		cursor += 2;
		const completionAlias = identifierAliasName(
			loopBody[cursor],
			nextName,
		);
		const completionName = completionAlias ?? nextName;
		const consumedProtocolNames = new Set(prelude.consumedNames);
		if (completionAlias) {
			consumedProtocolNames.add(completionAlias);
			cursor++;
		}
		if (!isDoneBreak(loopBody[cursor], nextName)) continue;
		const yieldStatement = loopBody[cursor + 1];
		if (!yieldResultOrAssignmentStatement(yieldStatement, nextName)) {
			continue;
		}
		if (
			loopBody.slice(cursor + 2).some((loopStmt) =>
				!t.isContinueStatement(loopStmt)
			)
		) continue;

		const hasCompletionReads = rewriteCompletionValueReads(
			body,
			i + 1,
			completionName,
		);
		if (hasCompletionReads == null) continue;

		const yieldTarget = yieldedAssignmentTarget(
			yieldStatement,
			nextName,
		);
		const replacement = [
			...loopBody.slice(0, acquisition.index)
				.filter((loopStmt) => {
					const declaration = singleDeclarator(loopStmt);
					return !(
						declaration && t.isIdentifier(declaration.id) &&
						consumedProtocolNames.has(declaration.id.name)
					);
				})
				.map((loopStmt) => t.cloneNode(loopStmt, true)),
			hasCompletionReads
				? t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier(completionName),
						delegateYieldIntrinsic(acquisition.argument),
					),
				])
				: t.expressionStatement(
					delegateYieldIntrinsic(acquisition.argument),
				),
		];
		if (yieldTarget) {
			removeObsoleteYieldTargetDeclaration(
				replacement,
				replacement.length,
				yieldTarget,
			);
		}

		body.splice(i, 1, ...replacement);
		i += replacement.length - 1;
		changed = true;
	}
	return changed;
}

export function reduceDelegateYieldLoopsInBody(body: t.Statement[]): boolean {
	let changed = false;

	changed = removeDiscardedCompletionValueReads(body) || changed;
	changed = hoistStructuredDelegateCompletion(body) || changed;
	changed = reduceRecoveredDelegateYieldStatements(body) || changed;

	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (!t.isTryStatement(stmt) || !stmt.handler || stmt.finalizer) {
			continue;
		}
		const tryBody = stmt.block.body;

		if (
			!tryBody.some((tryStmt) =>
				delegateYieldExpressionStatement(tryStmt)
			)
		) {
			continue;
		}
		if (
			!containsLoweredDelegateCatchMachinery(stmt.handler.body.body)
		) continue;
		body.splice(
			i,
			1,
			...tryBody.map((tryStmt) => t.cloneNode(tryStmt, true)),
		);
		i += tryBody.length - 1;
		changed = true;
	}

	for (const stmt of body) {
		if (t.isBlockStatement(stmt)) {
			changed = reduceDelegateYieldLoopsInBody(stmt.body) || changed;
		} else if (
			t.isLabeledStatement(stmt) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = reduceDelegateYieldLoopsInBody(stmt.body.body) || changed;
		} else if (t.isTryStatement(stmt)) {
			changed = reduceDelegateYieldLoopsInBody(stmt.block.body) ||
				changed;
			if (stmt.handler) {
				changed = reduceDelegateYieldLoopsInBody(
					stmt.handler.body.body,
				) || changed;
			}
			if (stmt.finalizer) {
				changed = reduceDelegateYieldLoopsInBody(stmt.finalizer.body) ||
					changed;
			}
		} else if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = reduceDelegateYieldLoopsInBody(
					stmt.consequent.body,
				) || changed;
			}
			if (t.isBlockStatement(stmt.alternate)) {
				changed = reduceDelegateYieldLoopsInBody(stmt.alternate.body) ||
					changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = reduceDelegateYieldLoopsInBody(
					switchCase.consequent,
				) || changed;
			}
		}
	}

	let indexOffset = 0;
	for (const acquisition of scanDelegateIteratorAcquisitions(body)) {
		const i = acquisition.index + indexOffset;
		if (body[i] !== acquisition.statement) continue;
		const previousLength = body.length;
		acquisition.index = i;

		let cursor = i + 1;
		if (isEnsureObjectStatement(body[cursor], acquisition.iteratorName)) {
			cursor++;
		}
		cursor = skipIteratorNextPropertyReads(
			body,
			cursor,
			acquisition.iteratorName,
		);

		if (reduceLoopCarriedProtectedDelegateLoop(body, acquisition, cursor)) {
			changed = true;
			indexOffset += body.length - previousLength;
			continue;
		}

		if (reduceBodyLevelDirectDelegateLoop(body, acquisition, cursor)) {
			changed = true;
			indexOffset += body.length - previousLength;
			continue;
		}

		const sentName = isUndefinedDeclaration(body[cursor]);
		if (!sentName) break;

		const loopAt2 = body[cursor + 2];
		if (loopAt2) {
			// Pattern: matchProtectedDelegateYieldLoop (4-stmt loop body, try-catch 4th)
			const trailing = matchProtectedDelegateYieldLoop(
				loopAt2,
				acquisition.iteratorName,
				sentName,
			);
			if (trailing) {
				const start = removeConsumedPreludeDeclarations(
					body,
					i,
					acquisition.consumedNames,
				);
				cursor -= i - start;
				body.splice(
					start,
					cursor + 3 - start,
					t.expressionStatement(
						delegateYieldIntrinsic(acquisition.argument),
					),
					...trailing,
				);
				changed = true;
				indexOffset += body.length - previousLength;
				continue;
			}

			// Pattern: matchDelegateYieldLoop (declarator at cursor+1, 5-6-stmt loop body)
			const resultName = declaratorIdentifier(body[cursor + 1]);
			if (
				resultName &&
				matchDelegateYieldLoop(
					loopAt2,
					acquisition.iteratorName,
					sentName,
					resultName,
				)
			) {
				const hasCompletionReads = rewriteCompletionValueReads(
					body,
					cursor + 3,
					resultName,
				);
				if (hasCompletionReads != null) {
					const replacement = hasCompletionReads
						? t.variableDeclaration('const', [
							t.variableDeclarator(
								t.identifier(resultName),
								delegateYieldIntrinsic(acquisition.argument),
							),
						])
						: t.expressionStatement(
							delegateYieldIntrinsic(acquisition.argument),
						);
					const start = removeConsumedPreludeDeclarations(
						body,
						i,
						acquisition.consumedNames,
					);
					cursor -= i - start;
					body.splice(start, cursor + 3 - start, replacement);
					changed = true;
					indexOffset += body.length - previousLength;
					continue;
				}
			}
		}

		// Pattern: matchBreakDelegateYieldLoop (4-stmt loop body at cursor+1)
		const loopAt1 = body[cursor + 1];
		if (loopAt1) {
			const match = matchBreakDelegateYieldLoop(
				loopAt1,
				acquisition.iteratorName,
				sentName,
			);
			if (match) {
				const hasCompletionReads = rewriteCompletionValueReads(
					body,
					cursor + 2,
					match.nextName,
				);
				if (hasCompletionReads != null) {
					const replacement = hasCompletionReads
						? t.variableDeclaration('const', [
							t.variableDeclarator(
								t.identifier(match.nextName),
								delegateYieldIntrinsic(acquisition.argument),
							),
						])
						: t.expressionStatement(
							delegateYieldIntrinsic(acquisition.argument),
						);
					const start = removeConsumedPreludeDeclarations(
						body,
						i,
						acquisition.consumedNames,
					);
					cursor -= i - start;
					body.splice(start, cursor + 2 - start, replacement);
					changed = true;
					indexOffset += body.length - previousLength;
					continue;
				}
			}
		}

		break;
	}

	changed = stripUnreachableDelegateProtocolSuffix(body) || changed;

	return changed;
}

export function reduceDelegateYieldCFG(func: IRFunction) {
	let changed = false;
	for (const block of func.blocks.values()) {
		if (block.branch || block.consequentAddresses.length !== 1) continue;
		const childAddr = block.consequentAddresses[0];
		const child = func.blocks.get(childAddr);
		if (!child) continue;
		const acquisition = findDelegateIteratorAcquisition(
			block.body as t.Statement[],
		);
		if (!acquisition) continue;
		const parentHandlers = func.exceptions.activeHandlersAtBlock(
			block.address,
		);
		const delegateHandlers = [...func.exceptions.activeHandlersAtBlock(
			childAddr,
		)].filter((handler) => {
			if (parentHandlers.has(handler)) return false;
			return handlerContainsLoweredDelegateCatchMachinery(func, handler);
		});
		const prelude = iteratorProtocolPrelude(
			block.body as t.Statement[],
			acquisition.index + 1,
			acquisition.iteratorName,
		);
		const directLoopStart = delegateYieldLoopStart(
			child.body as t.Statement[],
			prelude.receiverName,
		);
		const materializedLoopStart = materializedDelegateYieldLoopStart(
			(child.body as t.Statement[])[0],
		);
		const loopStart = directLoopStart ??
			(delegateHandlers.length > 0 ? materializedLoopStart : null);
		if (!loopStart) continue;
		let completionBindingName = loopStart.completionName;
		if (loopStart.completionName != null) {
			if (child.consequentAddresses.length > 1) continue;
			const completionAddr = child.consequentAddresses[0];
			const completionBlock = completionAddr == null
				? null
				: func.blocks.get(completionAddr);
			if (completionBlock) {
				const context = phiContext(func);
				const completionPhi = context.phiInMergedBlock(
					completionAddr,
					loopStart.completionName,
				);
				const normalCompletion = completionPhi == null
					? null
					: context.sourceForPredecessor(completionPhi, childAddr);
				if (normalCompletion != null) {
					completionBindingName = registerName(normalCompletion);
				}
				const rewritten = rewriteCompletionValueReads(
					completionBlock.body as t.Statement[],
					0,
					loopStart.completionName,
					completionBindingName ?? loopStart.completionName,
				);
				if (rewritten == null) continue;
			}
		}
		const delegateRegion = new Set([block.address, childAddr]);
		const referenceFacts = delegateReferenceFacts(
			func,
			acquisition.consumedNames,
			delegateRegion,
		);
		const sharedClosure = sharedClosureArgument(
			acquisition,
			block.body as t.Statement[],
			referenceFacts.counts,
		);
		const argument = sharedClosure
			? sharedClosure.argument
			: resolveDelegateArgumentFromPredecessor(
				func,
				block.address,
				acquisition.argument,
			);
		const locallyConsumed = locallyConsumedDelegateNames(
			acquisition.consumedNames,
			referenceFacts,
		);
		for (const name of sharedClosure?.preservedNames ?? []) {
			locallyConsumed.delete(name);
		}
		const acquisitionIndex = removeConsumedPreludeDeclarations(
			block.body as t.Statement[],
			acquisition.index,
			locallyConsumed,
		);
		const delegateYield = delegateYieldIntrinsic(argument);
		const replacement = completionBindingName == null
			? t.expressionStatement(delegateYield)
			: t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier(completionBindingName),
					delegateYield,
				),
			]);
		(block.body as t.Statement[]).splice(
			acquisitionIndex,
			block.body.length - acquisitionIndex,
			replacement,
		);
		block.branch = child.branch;
		block.consequentAddresses = [...child.consequentAddresses];
		if (block.consequentAddresses.length === 1) {
			const completionBlock = func.blocks.get(
				block.consequentAddresses[0],
			);
			if (
				completionBlock &&
				isUnusedDelegateCompletionBlock(
					completionBlock.body as t.Statement[],
				)
			) {
				block.consequentAddresses = [];
			}
		}
		if (func.predecessorsOf(childAddr).size === 1) {
			func.markMergedBlocks(block.address, childAddr);
		}
		// Hermes protects SaveGenerator/ResumeGenerator with an implicit handler
		// implementing the `yield*` throw/return protocol. Once that complete
		// protocol has become DelegateYield, retaining the handler leaves an
		// unreachable exceptional entry which prevents the generator body from
		// becoming a single function expression. Remove only handlers introduced
		// at the delegate loop boundary whose body contains that protocol; outer
		// source-level try/catch/finally handlers are active at the acquisition
		// block too and are deliberately preserved.
		func.exceptions.removeHandlers(delegateHandlers);
		for (const handler of delegateHandlers) func.deleteBlock(handler);
		changed = true;
	}

	if (changed) func.isGenerator = true;
	return changed;
}

export function reduceDelegateYieldStructuredBodies(func: IRFunction) {
	let changed = false;
	for (const block of func.blocks.values()) {
		changed = reduceDelegateYieldLoopsInBody(block.body as t.Statement[]) ||
			changed;
	}
	if (changed) func.isGenerator = true;
	return changed;
}
