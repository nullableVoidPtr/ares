import * as t from '@babel/types';
import generate from '@babel/generator';
import traverse from '@babel/traverse';
import { invertTest } from './expression.ts';
import { LiftedAST } from './mod.ts';
import { isParameterExpression } from './alias.ts';

function nodesCodeEqual(a: t.Node, b: t.Node): boolean {
	return generate(a).code === generate(b).code;
}

function findDeclInStmt(
	stmt: t.Statement,
	name: string,
): {
	container: t.Statement[];
	index: number;
	init?: t.Expression;
	replacement?: (destName: string) => t.Statement[];
} | null {
	const scanBody = (body: t.Statement[]) => {
		for (let i = 0; i < body.length; i++) {
			const s = body[i];
			if (t.isVariableDeclaration(s)) {
				for (const d of s.declarations) {
					if (t.isIdentifier(d.id, { name }) && d.init) {
						return { container: body, index: i, init: d.init };
					}
					if (
						d.init &&
						t.isPatternLike(d.id) &&
						bindingPatternContainsName(d.id, name)
					) {
						return {
							container: body,
							index: i,
							replacement: (destName: string) => [
								t.cloneNode(s, true),
								t.expressionStatement(
									t.assignmentExpression(
										'=',
										t.identifier(destName),
										t.identifier(name),
									),
								),
							],
						};
					}
				}
			}
			const nested = findDeclInStmt(s, name);
			if (nested) return nested;
		}
		return null;
	};

	if (t.isIfStatement(stmt)) {
		if (t.isBlockStatement(stmt.consequent)) {
			const r = scanBody(stmt.consequent.body);
			if (r) return r;
		}
		if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
			const r = scanBody(stmt.alternate.body);
			if (r) return r;
		}
	} else if (
		(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
			t.isForOfStatement(stmt)) &&
		t.isBlockStatement(stmt.body)
	) {
		return scanBody(stmt.body.body);
	} else if (t.isTryStatement(stmt)) {
		return scanBody(stmt.block.body) ??
			(stmt.handler ? scanBody(stmt.handler.body.body) : null) ??
			(stmt.finalizer ? scanBody(stmt.finalizer.body) : null);
	} else if (t.isSwitchStatement(stmt)) {
		for (const switchCase of stmt.cases) {
			const r = scanBody(switchCase.consequent);
			if (r) return r;
		}
	}
	return null;
}

function bindingPatternContainsName(
	pattern: t.PatternLike,
	name: string,
): boolean {
	let found = false;
	t.traverseFast(pattern, (node) => {
		if (found) return t.traverseFast.skip;
		if (t.isIdentifier(node, { name })) found = true;
	});
	return found;
}

interface LocatedPhiDeclaration {
	container: t.Statement[];
	index: number;
	statement: LiftedAST<t.VariableDeclaration>;
	declaration: t.VariableDeclarator;
}

function findPhiDeclarationInStatement(
	stmt: t.Statement,
): LocatedPhiDeclaration | null {
	const scan = (body: t.Statement[]): LocatedPhiDeclaration | null => {
		for (let index = 0; index < body.length; index++) {
			const candidate = body[index];
			if (
				t.isVariableDeclaration(candidate) &&
				candidate.declarations.length === 1
			) {
				const declaration = candidate.declarations[0];
				if (
					t.isIdentifier(declaration.id) &&
					t.isCallExpression(declaration.init) &&
					t.isV8IntrinsicIdentifier(declaration.init.callee, {
						name: 'Phi',
					})
				) {
					return {
						container: body,
						index,
						statement: candidate,
						declaration,
					};
				}
			}
			const nested = findPhiDeclarationInStatement(candidate);
			if (nested) return nested;
		}
		return null;
	};

	if (t.isIfStatement(stmt)) {
		if (t.isBlockStatement(stmt.consequent)) {
			const found = scan(stmt.consequent.body);
			if (found) return found;
		}
		if (t.isBlockStatement(stmt.alternate)) {
			return scan(stmt.alternate.body);
		}
	} else if (
		(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
			t.isForOfStatement(stmt) || t.isForStatement(stmt)) &&
		t.isBlockStatement(stmt.body)
	) {
		return scan(stmt.body.body);
	} else if (t.isTryStatement(stmt)) {
		return scan(stmt.block.body) ??
			(stmt.handler ? scan(stmt.handler.body.body) : null) ??
			(stmt.finalizer ? scan(stmt.finalizer.body) : null);
	} else if (t.isSwitchStatement(stmt)) {
		for (const switchCase of stmt.cases) {
			const found = scan(switchCase.consequent);
			if (found) return found;
		}
	}
	return null;
}

/**
 * Repair an SSA Phi whose source declaration was enclosed by a structured
 * sibling while the join was subsequently enclosed by the following
 * try/loop/switch. The source name is not a valid JavaScript binding outside
 * its branch, so scope cleanup would otherwise discard the value before the
 * ordinary nested Phi pass can see it.
 */
function liftPhiAcrossFollowingContainer(body: t.Statement[]): boolean {
	for (let ownerIndex = 1; ownerIndex < body.length; ownerIndex++) {
		if (!t.isTryStatement(body[ownerIndex])) continue;
		const located = findPhiDeclarationInStatement(body[ownerIndex]);
		if (
			!located || located.index !== 0 ||
			!t.isIdentifier(located.declaration.id)
		) continue;
		const call = located.declaration.init;
		if (!t.isCallExpression(call)) continue;
		const args = call.arguments.filter(t.isExpression);
		if (args.length !== 2 || !args.every(t.isIdentifier)) continue;

		const nestedSources = args.flatMap((arg) => {
			for (let index = ownerIndex - 1; index >= 0; index--) {
				const source = findDeclInStmt(body[index], arg.name);
				if (source?.init) {
					return [{ arg, source, init: source.init, owner: index }];
				}
			}
			return [];
		});
		if (nestedSources.length !== 1) continue;
		const nested = nestedSources[0];
		const initial = args.find((arg) => arg.name !== nested.arg.name);
		if (!initial) continue;

		const destination = located.declaration.id.name;
		nested.source.container[nested.source.index] = t.expressionStatement(
			t.assignmentExpression(
				'=',
				t.identifier(destination),
				t.cloneNode(nested.init, true),
			),
		);
		const declaration = t.variableDeclaration('let', [
			t.variableDeclarator(
				t.identifier(destination),
				t.cloneNode(initial, true),
			),
		]) as LiftedAST<t.VariableDeclaration>;
		declaration.extra = {
			...declaration.extra,
			liftedPhiSources: args.map((arg) => arg.name).sort(),
			isPotentialConditionalValue: true,
		};
		body.splice(nested.owner, 0, declaration);
		located.container.splice(located.index, 1);
		return true;
	}
	return false;
}

function replacePhiSourceDecls(
	toReplace: Array<
		{
			container: t.Statement[];
			index: number;
			initExpr?: t.Expression;
			replacement?: (destName: string) => t.Statement[];
		}
	>,
	destName: string,
): void {
	const byContainer = new Map<
		t.Statement[],
		Array<{
			index: number;
			initExpr?: t.Expression;
			replacement?: (destName: string) => t.Statement[];
		}>
	>();
	for (const replacement of toReplace) {
		const replacements = byContainer.get(replacement.container) ?? [];
		replacements.push(replacement);
		byContainer.set(replacement.container, replacements);
	}

	for (const [container, replacements] of byContainer) {
		replacements.sort((a, b) => b.index - a.index);
		for (const { index, initExpr, replacement } of replacements) {
			if (replacement) {
				container.splice(index, 1, ...replacement(destName));
				continue;
			}
			if (!initExpr) continue;
			container[index] = t.expressionStatement(
				t.assignmentExpression(
					'=',
					t.identifier(destName),
					initExpr,
				),
			);
		}
	}
}

function assignmentInitInStmt(
	stmt: t.Statement,
	name: string,
): t.Expression | null {
	if (
		t.isExpressionStatement(stmt) &&
		t.isAssignmentExpression(stmt.expression, { operator: '=' }) &&
		t.isIdentifier(stmt.expression.left, { name }) &&
		t.isExpression(stmt.expression.right)
	) {
		return stmt.expression.right;
	}
	return null;
}

function liftLoopHeaderPhiNodes(
	body: t.Statement[],
	preserveDestinations: boolean,
): boolean {
	let anyChanged = false;

	for (let stmtIndex = 0; stmtIndex < body.length; stmtIndex++) {
		const stmt = body[stmtIndex];
		if (
			!(
				(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
					t.isForOfStatement(stmt)) &&
				t.isBlockStatement(stmt.body)
			)
		) continue;

		const loopBody = stmt.body.body;
		const declarationsToInsert: t.VariableDeclaration[] = [];

		const identifiersAfterLoop = new Map<string, t.Identifier[]>();
		for (
			let nextIndex = stmtIndex + 1;
			nextIndex < body.length;
			nextIndex++
		) {
			t.traverseFast(body[nextIndex], (node) => {
				if (!t.isIdentifier(node)) return;
				const identifiers = identifiersAfterLoop.get(node.name) ?? [];
				identifiers.push(node);
				identifiersAfterLoop.set(node.name, identifiers);
			});
		}

		for (let i = loopBody.length - 1; i >= 0; i--) {
			const phiStmt = loopBody[i];
			if (!t.isVariableDeclaration(phiStmt, { kind: 'const' })) continue;
			if (phiStmt.declarations.length !== 1) continue;
			const phiDecl = phiStmt.declarations[0];
			if (!t.isIdentifier(phiDecl.id)) continue;
			if (!t.isCallExpression(phiDecl.init)) continue;
			if (
				!t.isV8IntrinsicIdentifier(phiDecl.init.callee, { name: 'Phi' })
			) continue;

			const destName = phiDecl.id.name;
			const args = phiDecl.init.arguments as t.Expression[];
			let initialValue: t.Expression | undefined;
			const replacedSrcNames = new Set<string>();
			const toReplace: Array<
				{
					container: t.Statement[];
					index: number;
					initExpr?: t.Expression;
					replacement?: (destName: string) => t.Statement[];
				}
			> = [];

			for (const arg of args) {
				if (t.isIdentifier(arg)) {
					if (arg.name === destName) continue;

					const sourceInLoop = findDeclInStmt(stmt, arg.name);
					if (sourceInLoop) {
						toReplace.push({
							container: sourceInLoop.container,
							index: sourceInLoop.index,
							initExpr: sourceInLoop.init
								? t.cloneNode(sourceInLoop.init, true)
								: undefined,
							replacement: sourceInLoop.replacement,
						});
						if (!sourceInLoop.replacement) {
							replacedSrcNames.add(arg.name);
						}
						continue;
					}

					if (initialValue === undefined) {
						initialValue = t.cloneNode(arg, true);
					}
					continue;
				}

				if (initialValue === undefined) {
					initialValue = t.cloneNode(arg, true) as t.Expression;
				}
			}

			if (initialValue === undefined && toReplace.length === 0) continue;
			let assignmentName = destName;
			let insertDeclaration = true;
			const exitAliases = new Set<string>();
			for (const loopStatement of loopBody) {
				t.traverseFast(loopStatement, (node) => {
					if (
						t.isVariableDeclarator(node) &&
						t.isIdentifier(node.id) &&
						t.isIdentifier(node.init, { name: destName })
					) exitAliases.add(node.id.name);
				});
			}
			const destinationUsedAfterLoop = identifiersAfterLoop.has(destName);
			if (
				!preserveDestinations &&
				!destinationUsedAfterLoop &&
				t.isIdentifier(initialValue) &&
				sameRegisterBase(destName, initialValue.name)
			) {
				assignmentName = initialValue.name;
				insertDeclaration = false;
				makePriorDeclarationMutable(body, stmtIndex, assignmentName);
			}
			replacePhiSourceDecls(toReplace, assignmentName);
			if (assignmentName !== destName) {
				for (const loopStatement of loopBody) {
					if (loopStatement === phiStmt) continue;
					t.traverseFast(loopStatement, (node) => {
						if (t.isIdentifier(node, { name: destName })) {
							node.name = assignmentName;
						}
					});
				}
				for (const alias of exitAliases) {
					if (alias === assignmentName) continue;
					const identifiers = identifiersAfterLoop.get(alias);
					if (!identifiers) continue;
					let assignmentIdentifiers = identifiersAfterLoop.get(
						assignmentName,
					);
					if (!assignmentIdentifiers) {
						assignmentIdentifiers = [];
						identifiersAfterLoop.set(
							assignmentName,
							assignmentIdentifiers,
						);
					}
					for (const identifier of identifiers) {
						identifier.name = assignmentName;
						assignmentIdentifiers.push(identifier);
					}
					identifiersAfterLoop.delete(alias);
				}
			}

			// Any remaining identifier uses of the loop-back source name now refer to destName
			// (e.g. the break condition `if (!(r2_3 < 10))` after `r2_2 = ToNumeric(r2_2)+1`).
			for (const srcName of replacedSrcNames) {
				t.traverseFast(t.blockStatement(loopBody), (node) => {
					if (t.isIdentifier(node, { name: srcName })) {
						(node as t.Identifier).name = assignmentName;
					}
				});
			}

			if (insertDeclaration) {
				declarationsToInsert.unshift(
					t.variableDeclaration('let', [
						t.variableDeclarator(
							t.identifier(destName),
							initialValue,
						),
					]),
				);
			}
			loopBody.splice(i, 1);
			anyChanged = true;
		}

		if (declarationsToInsert.length > 0) {
			body.splice(stmtIndex, 0, ...declarationsToInsert);
			stmtIndex += declarationsToInsert.length;
		}
	}

	return anyChanged;
}

function declaredNamesInStatement(stmt: t.Statement): Set<string> {
	const names = new Set<string>();
	if (!t.isVariableDeclaration(stmt)) return names;
	for (const decl of stmt.declarations) {
		if (t.isIdentifier(decl.id)) names.add(decl.id.name);
	}
	return names;
}

function isPrimitivePhiSource(expr: t.Expression): boolean {
	return t.isStringLiteral(expr) ||
		t.isNumericLiteral(expr) ||
		t.isBooleanLiteral(expr) ||
		t.isNullLiteral(expr) ||
		t.isIdentifier(expr, { name: 'undefined' });
}

function isParameterIdentifier(expr: t.Expression): expr is t.Identifier {
	return t.isIdentifier(expr) && isParameterExpression(expr);
}

function scopedPhiReplacement(
	call: t.CallExpression,
	inScope: Set<string>,
): t.Expression | null {
	if (!t.isV8IntrinsicIdentifier(call.callee, { name: 'Phi' })) return null;
	const args = call.arguments.filter(t.isExpression);
	const computedSources = args.filter((arg) =>
		!t.isIdentifier(arg) && !isPrimitivePhiSource(arg)
	);
	if (computedSources.length === 1) {
		return t.cloneNode(computedSources[0], true);
	}
	if (computedSources.length > 1) return null;

	const scopedSources = args.filter((arg): arg is t.Identifier =>
		t.isIdentifier(arg) && inScope.has(arg.name)
	);
	const distinctScopedSources = distinctExpressions(scopedSources);
	if (distinctScopedSources.length === 1) {
		return t.cloneNode(distinctScopedSources[0], true);
	}
	if (distinctScopedSources.length > 1) return null;

	const primitiveSources = args.filter(isPrimitivePhiSource);
	const distinctPrimitiveSources = distinctExpressions(primitiveSources);
	if (distinctPrimitiveSources.length === 1) {
		return t.cloneNode(distinctPrimitiveSources[0], true);
	}
	return null;
}

function distinctExpressions<T extends t.Expression>(values: T[]): T[] {
	const distinct: T[] = [];
	for (const value of values) {
		if (distinct.some((candidate) => nodesCodeEqual(candidate, value))) {
			continue;
		}
		distinct.push(value);
	}
	return distinct;
}

function expressionReferencesIdentifier(
	expr: t.Expression,
	name: string,
): boolean {
	let found = false;
	t.traverseFast(expr, (node) => {
		if (t.isIdentifier(node, { name })) found = true;
	});
	return found;
}

function nodeContainsPhiCall(node: t.Node): boolean {
	let found = false;
	t.traverseFast(node, (child) => {
		if (found) return t.traverseFast.skip;
		if (
			t.isCallExpression(child) &&
			t.isV8IntrinsicIdentifier(child.callee, { name: 'Phi' })
		) {
			found = true;
		}
	});
	return found;
}

/**
 * Resolve a Phi whose every syntactic operand is the same SSA value even when
 * the value's generated binding has already been removed from the materialized
 * AST. The caller supplies the SSA-provenance lookup; without a recovered
 * expression this deliberately leaves the out-of-scope identifier untouched.
 */
export function simplifyProvenanceResolvedPhiCalls(
	body: t.Statement[],
	recover: (name: string) => t.Expression | null,
): boolean {
	let changed = false;
	const file = t.file(t.program(body));
	try {
		traverse(file, {
			noScope: true,
			Function(path) {
				path.skip();
			},
			CallExpression(path) {
				if (
					!t.isV8IntrinsicIdentifier(path.node.callee, {
						name: 'Phi',
					})
				) return;
				if (
					path.node.arguments.length === 0 ||
					!path.node.arguments.every(t.isExpression)
				) return;
				const distinct = distinctExpressions(path.node.arguments);
				if (distinct.length !== 1) return;
				const [source] = distinct;
				const replacement = isPrimitivePhiSource(source)
					? t.cloneNode(source, true)
					: t.isIdentifier(source)
					? recover(source.name)
					: null;
				if (!replacement) return;
				path.replaceWith(t.cloneNode(replacement, true));
				changed = true;
			},
		});
	} finally {
		traverse.cache.clear();
	}
	return changed;
}

export function simplifySelfUpdatePhiAssignments(body: t.Statement[]): boolean {
	let changed = false;

	for (const stmt of body) {
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = simplifySelfUpdatePhiAssignments(
					stmt.consequent.body,
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = simplifySelfUpdatePhiAssignments(
					stmt.alternate.body,
				) || changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt) || t.isForStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = simplifySelfUpdatePhiAssignments(stmt.body.body) ||
				changed;
		} else if (t.isTryStatement(stmt)) {
			changed = simplifySelfUpdatePhiAssignments(stmt.block.body) ||
				changed;
			if (stmt.handler) {
				changed = simplifySelfUpdatePhiAssignments(
					stmt.handler.body.body,
				) || changed;
			}
			if (stmt.finalizer) {
				changed = simplifySelfUpdatePhiAssignments(
					stmt.finalizer.body,
				) || changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = simplifySelfUpdatePhiAssignments(
					switchCase.consequent,
				) || changed;
			}
		}

		if (!t.isExpressionStatement(stmt)) continue;
		const expr = stmt.expression;
		if (
			!t.isAssignmentExpression(expr, { operator: '=' }) ||
			!t.isIdentifier(expr.left) ||
			!t.isCallExpression(expr.right) ||
			!t.isV8IntrinsicIdentifier(expr.right.callee, { name: 'Phi' })
		) continue;

		const args = expr.right.arguments.filter(t.isExpression);
		const computedSources = args.filter((arg) =>
			!t.isIdentifier(arg) && !isPrimitivePhiSource(arg)
		);
		if (computedSources.length !== 1) continue;
		const [source] = computedSources;
		if (!expressionReferencesIdentifier(source, expr.left.name)) continue;
		expr.right = t.cloneNode(source, true);
		changed = true;
	}

	return changed;
}

export function simplifyScopedPhiCalls(
	body: t.Statement[],
	visibleNames = new Set<string>(),
): boolean {
	let changed = false;
	const inScope = new Set(visibleNames);

	for (const stmt of body) {
		if (nodeContainsPhiCall(stmt)) {
			traverse(t.file(t.program([stmt])), {
				noScope: true,
				Function(path) {
					path.skip();
				},
				CallExpression(path) {
					const parent = path.parentPath;
					if (
						parent.isVariableDeclarator({ init: path.node }) ||
						parent.isAssignmentExpression({ right: path.node }) ||
						parent.isExpressionStatement({ expression: path.node })
					) return;
					const replacement = scopedPhiReplacement(
						path.node,
						inScope,
					);
					if (!replacement) return;
					path.replaceWith(replacement);
					changed = true;
				},
			});
		}

		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = simplifyScopedPhiCalls(
					stmt.consequent.body,
					inScope,
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = simplifyScopedPhiCalls(
					stmt.alternate.body,
					inScope,
				) || changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = simplifyScopedPhiCalls(stmt.body.body, inScope) ||
				changed;
		} else if (t.isTryStatement(stmt)) {
			changed = simplifyScopedPhiCalls(stmt.block.body, inScope) ||
				changed;
			if (stmt.handler) {
				changed = simplifyScopedPhiCalls(
					stmt.handler.body.body,
					inScope,
				) || changed;
			}
			if (stmt.finalizer) {
				changed =
					simplifyScopedPhiCalls(stmt.finalizer.body, inScope) ||
					changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = simplifyScopedPhiCalls(
					switchCase.consequent,
					inScope,
				) || changed;
			}
		}

		for (const name of declaredNamesInStatement(stmt)) inScope.add(name);
	}

	return changed;
}

export function simplifyScopedPhiDeclarations(
	body: t.Statement[],
	visibleNames = new Set<string>(),
): boolean {
	let changed = false;
	const inScope = new Set(visibleNames);

	for (const stmt of body) {
		if (t.isVariableDeclaration(stmt) && stmt.declarations.length === 1) {
			const [decl] = stmt.declarations;
			if (t.isCallExpression(decl.init)) {
				const replacement = scopedPhiReplacement(decl.init, inScope);
				if (replacement) {
					decl.init = replacement;
					changed = true;
				}
			}
		}

		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = simplifyScopedPhiDeclarations(
					stmt.consequent.body,
					inScope,
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = simplifyScopedPhiDeclarations(
					stmt.alternate.body,
					inScope,
				) || changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt) || t.isForStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = simplifyScopedPhiDeclarations(stmt.body.body, inScope) ||
				changed;
		} else if (t.isTryStatement(stmt)) {
			changed = simplifyScopedPhiDeclarations(stmt.block.body, inScope) ||
				changed;
			if (stmt.handler) {
				changed = simplifyScopedPhiDeclarations(
					stmt.handler.body.body,
					inScope,
				) || changed;
			}
			if (stmt.finalizer) {
				changed = simplifyScopedPhiDeclarations(
					stmt.finalizer.body,
					inScope,
				) || changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = simplifyScopedPhiDeclarations(
					switchCase.consequent,
					inScope,
				) || changed;
			}
		}

		for (const name of declaredNamesInStatement(stmt)) inScope.add(name);
	}

	return changed;
}

function singleScopedIdentifierPhiSource(
	call: t.CallExpression,
	inScope: Set<string>,
): t.Identifier | null {
	if (!t.isV8IntrinsicIdentifier(call.callee, { name: 'Phi' })) return null;
	const args = call.arguments.filter(t.isExpression);
	if (
		args.some((arg) => !t.isIdentifier(arg) && !isPrimitivePhiSource(arg))
	) return null;
	const scopedSources = args.filter((arg): arg is t.Identifier =>
		t.isIdentifier(arg) && inScope.has(arg.name)
	);
	const distinctScopedSources = distinctExpressions(scopedSources);
	if (distinctScopedSources.length !== 1) return null;
	return t.identifier(distinctScopedSources[0].name);
}

export function simplifyScopedPhiAssignments(
	body: t.Statement[],
	visibleNames = new Set<string>(),
): boolean {
	let changed = false;
	const inScope = new Set(visibleNames);

	for (const stmt of body) {
		if (t.isExpressionStatement(stmt)) {
			const expr = stmt.expression;
			if (
				t.isAssignmentExpression(expr, { operator: '=' }) &&
				t.isCallExpression(expr.right)
			) {
				const replacement = singleScopedIdentifierPhiSource(
					expr.right,
					inScope,
				);
				if (replacement) {
					expr.right = replacement;
					changed = true;
				}
			}
		}

		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = simplifyScopedPhiAssignments(
					stmt.consequent.body,
					inScope,
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = simplifyScopedPhiAssignments(
					stmt.alternate.body,
					inScope,
				) || changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt) || t.isForStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = simplifyScopedPhiAssignments(stmt.body.body, inScope) ||
				changed;
		} else if (t.isTryStatement(stmt)) {
			changed = simplifyScopedPhiAssignments(stmt.block.body, inScope) ||
				changed;
			if (stmt.handler) {
				changed = simplifyScopedPhiAssignments(
					stmt.handler.body.body,
					inScope,
				) || changed;
			}
			if (stmt.finalizer) {
				changed = simplifyScopedPhiAssignments(
					stmt.finalizer.body,
					inScope,
				) || changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = simplifyScopedPhiAssignments(
					switchCase.consequent,
					inScope,
				) || changed;
			}
		}

		for (const name of declaredNamesInStatement(stmt)) inScope.add(name);
	}

	return changed;
}

function flattenLogicalOr(expr: t.Expression): t.Expression[] {
	if (t.isLogicalExpression(expr, { operator: '||' })) {
		return [
			...flattenLogicalOr(expr.left),
			...flattenLogicalOr(expr.right),
		];
	}
	return [expr];
}

function primitivePhiArgs(
	call: t.CallExpression,
	constants = new Map<string, t.Expression>(),
): t.Expression[] | null {
	if (!t.isV8IntrinsicIdentifier(call.callee, { name: 'Phi' })) return null;
	const args = call.arguments.filter(t.isExpression).map((arg) =>
		t.isIdentifier(arg) && constants.has(arg.name)
			? t.cloneNode(constants.get(arg.name)!, true)
			: arg
	);
	if (args.length === 0 || !args.every(isPrimitivePhiSource)) return null;
	return args;
}

function conditionalFromGuardTerms(
	terms: t.Expression[],
	values: t.Expression[],
): t.Expression | null {
	if (terms.length !== values.length || values.length === 0) return null;
	let expr = t.cloneNode(values[values.length - 1], true);
	for (let i = values.length - 2; i >= 0; i--) {
		expr = t.conditionalExpression(
			t.cloneNode(terms[i], true),
			t.cloneNode(values[i], true),
			expr,
		);
	}
	return expr;
}

function replaceNodeInPlace(node: t.Node, replacement: t.Node): void {
	for (const key of Object.keys(node)) {
		delete (node as unknown as Record<string, unknown>)[key];
	}
	Object.assign(node, replacement);
}

function simplifyGuardedPrimitivePhiCallsInBody(
	body: t.Statement[],
	terms: t.Expression[],
	constants: Map<string, t.Expression>,
): boolean {
	let changed = false;
	t.traverseFast(t.blockStatement(body), (node) => {
		if (t.isFunction(node)) return t.traverseFast.skip;
		if (!t.isCallExpression(node)) return;
		const args = primitivePhiArgs(node, constants);
		if (!args) return;
		const replacement = conditionalFromGuardTerms(terms, args);
		if (!replacement) return;
		replaceNodeInPlace(node, replacement);
		changed = true;
	});
	return changed;
}

export function simplifyGuardedPrimitivePhiCalls(
	body: t.Statement[],
	visibleConstants = new Map<string, t.Expression>(),
): boolean {
	let changed = false;
	const constants = new Map(visibleConstants);

	for (const stmt of body) {
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				const terms = flattenLogicalOr(stmt.test);
				changed = simplifyGuardedPrimitivePhiCallsInBody(
					stmt.consequent.body,
					terms,
					constants,
				) || changed;
				changed = simplifyGuardedPrimitivePhiCalls(
					stmt.consequent.body,
					constants,
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = simplifyGuardedPrimitivePhiCalls(
					stmt.alternate.body,
					constants,
				) || changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt) || t.isForStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed =
				simplifyGuardedPrimitivePhiCalls(stmt.body.body, constants) ||
				changed;
		} else if (t.isTryStatement(stmt)) {
			changed =
				simplifyGuardedPrimitivePhiCalls(stmt.block.body, constants) ||
				changed;
			if (stmt.handler) {
				changed = simplifyGuardedPrimitivePhiCalls(
					stmt.handler.body.body,
					constants,
				) || changed;
			}
			if (stmt.finalizer) {
				changed = simplifyGuardedPrimitivePhiCalls(
					stmt.finalizer.body,
					constants,
				) || changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = simplifyGuardedPrimitivePhiCalls(
					switchCase.consequent,
					constants,
				) || changed;
			}
		}

		if (t.isVariableDeclaration(stmt, { kind: 'const' })) {
			for (const decl of stmt.declarations) {
				if (
					t.isIdentifier(decl.id) &&
					decl.init &&
					t.isExpression(decl.init) &&
					isPrimitivePhiSource(decl.init)
				) {
					constants.set(decl.id.name, decl.init);
				}
			}
		}
	}

	return changed;
}

export function simplifyTerminalReturnPhis(
	body: t.Statement[],
	visibleNames = new Set<string>(),
): boolean {
	let changed = false;
	const inScope = new Set(visibleNames);

	for (const stmt of body) {
		if (t.isReturnStatement(stmt) && t.isCallExpression(stmt.argument)) {
			const call = stmt.argument;
			if (t.isV8IntrinsicIdentifier(call.callee, { name: 'Phi' })) {
				const args = call.arguments.filter(t.isExpression);
				const inlineSources = args.filter((arg) =>
					!t.isIdentifier(arg) && !isPrimitivePhiSource(arg)
				);
				if (inlineSources.length === 1) {
					stmt.argument = t.cloneNode(inlineSources[0], true);
					changed = true;
				} else {
					const scopedSource = args.find((arg) =>
						t.isIdentifier(arg) && inScope.has(arg.name)
					);
					if (scopedSource) {
						stmt.argument = t.cloneNode(scopedSource, true);
						changed = true;
					} else {
						const parameterSources = args.filter(
							isParameterIdentifier,
						);
						if (parameterSources.length === 1) {
							stmt.argument = t.cloneNode(
								parameterSources[0],
								true,
							);
							changed = true;
						}
					}
				}
			}
		}

		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = simplifyTerminalReturnPhis(
					stmt.consequent.body,
					inScope,
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = simplifyTerminalReturnPhis(
					stmt.alternate.body,
					inScope,
				) || changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = simplifyTerminalReturnPhis(stmt.body.body, inScope) ||
				changed;
		} else if (t.isTryStatement(stmt)) {
			changed = simplifyTerminalReturnPhis(stmt.block.body, inScope) ||
				changed;
			if (stmt.handler) {
				changed = simplifyTerminalReturnPhis(
					stmt.handler.body.body,
					inScope,
				) || changed;
			}
			if (stmt.finalizer) {
				changed =
					simplifyTerminalReturnPhis(stmt.finalizer.body, inScope) ||
					changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = simplifyTerminalReturnPhis(
					switchCase.consequent,
					inScope,
				) || changed;
			}
		}

		for (const name of declaredNamesInStatement(stmt)) inScope.add(name);
	}

	return changed;
}

export function removeUnusedPhiExpressions(body: t.Statement[]): boolean {
	let changed = false;

	for (const stmt of body) {
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = removeUnusedPhiExpressions(stmt.consequent.body) ||
					changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = removeUnusedPhiExpressions(stmt.alternate.body) ||
					changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt) || t.isForStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = removeUnusedPhiExpressions(stmt.body.body) || changed;
		} else if (t.isTryStatement(stmt)) {
			changed = removeUnusedPhiExpressions(stmt.block.body) || changed;
			if (stmt.handler) {
				changed = removeUnusedPhiExpressions(stmt.handler.body.body) ||
					changed;
			}
			if (stmt.finalizer) {
				changed = removeUnusedPhiExpressions(stmt.finalizer.body) ||
					changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = removeUnusedPhiExpressions(switchCase.consequent) ||
					changed;
			}
		}
	}

	for (let i = body.length - 1; i >= 0; i--) {
		const s = body[i];
		if (
			t.isExpressionStatement(s) &&
			t.isCallExpression(s.expression) &&
			t.isV8IntrinsicIdentifier(s.expression.callee, { name: 'Phi' })
		) {
			body.splice(i, 1);
			changed = true;
		}
	}

	return changed;
}

function findPriorLetDeclaration(
	body: t.Statement[],
	before: number,
	name: string,
): t.VariableDeclarator | null {
	for (let i = before - 1; i >= 0; i--) {
		const stmt = body[i];
		if (!t.isVariableDeclaration(stmt, { kind: 'let' })) continue;
		for (const decl of stmt.declarations) {
			if (t.isIdentifier(decl.id, { name })) return decl;
		}
	}
	return null;
}

function sameRegisterBase(left: string, right: string): boolean {
	const leftBase = /^r\d+_/.exec(left)?.[0];
	const rightBase = /^r\d+_/.exec(right)?.[0];
	return leftBase != null && leftBase === rightBase;
}

function makePriorDeclarationMutable(
	body: t.Statement[],
	before: number,
	name: string,
): void {
	for (let i = before - 1; i >= 0; i--) {
		const stmt = body[i];
		if (!t.isVariableDeclaration(stmt)) continue;
		for (const decl of stmt.declarations) {
			if (
				t.isIdentifier(decl.id, { name }) ||
				(t.isPatternLike(decl.id) &&
					bindingPatternContainsName(decl.id, name))
			) {
				if (stmt.kind === 'const') stmt.kind = 'let';
				return;
			}
		}
	}
}

export function liftLoopHeaderPhiAssignments(body: t.Statement[]): boolean {
	let changed = false;

	for (let stmtIndex = 0; stmtIndex < body.length; stmtIndex++) {
		const stmt = body[stmtIndex];
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = liftLoopHeaderPhiAssignments(stmt.consequent.body) ||
					changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = liftLoopHeaderPhiAssignments(stmt.alternate.body) ||
					changed;
			}
			continue;
		}
		if (t.isTryStatement(stmt)) {
			changed = liftLoopHeaderPhiAssignments(stmt.block.body) || changed;
			if (stmt.handler) {
				changed =
					liftLoopHeaderPhiAssignments(stmt.handler.body.body) ||
					changed;
			}
			if (stmt.finalizer) {
				changed = liftLoopHeaderPhiAssignments(stmt.finalizer.body) ||
					changed;
			}
			continue;
		}
		if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = liftLoopHeaderPhiAssignments(
					switchCase.consequent,
				) || changed;
			}
			continue;
		}
		if (
			!(
				(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
					t.isForOfStatement(stmt) || t.isForStatement(stmt)) &&
				t.isBlockStatement(stmt.body)
			)
		) continue;

		const loopBody = stmt.body.body;
		changed = liftLoopHeaderPhiAssignments(loopBody) || changed;

		for (let i = 0; i < loopBody.length; i++) {
			const phiStmt = loopBody[i];
			if (!t.isExpressionStatement(phiStmt)) break;
			const expr = phiStmt.expression;
			if (
				!t.isAssignmentExpression(expr, { operator: '=' }) ||
				!t.isIdentifier(expr.left) ||
				!t.isCallExpression(expr.right) ||
				!t.isV8IntrinsicIdentifier(expr.right.callee, { name: 'Phi' })
			) break;

			const name = expr.left.name;
			const args = expr.right.arguments.filter(t.isExpression);
			const initialSources = args.filter((arg) =>
				!(t.isIdentifier(arg, { name }) ||
					t.isIdentifier(arg, { name: 'undefined' }))
			);
			if (initialSources.length > 1) continue;

			if (initialSources.length === 1) {
				const priorDecl = findPriorLetDeclaration(
					body,
					stmtIndex,
					name,
				);
				if (!priorDecl) continue;
				if (!priorDecl.init) {
					priorDecl.init = t.cloneNode(initialSources[0], true);
				}
			}

			loopBody.splice(i, 1);
			i--;
			changed = true;
		}
	}

	return changed;
}

export function simplifyNullGuardedPhiDeclarations(
	body: t.Statement[],
): boolean {
	let changed = false;

	for (const stmt of body) {
		if (t.isIfStatement(stmt)) {
			const nullCheck = asNullCheck(stmt.test);
			if (
				nullCheck?.trueWhenNull &&
				t.isIdentifier(nullCheck.tested) &&
				t.isBlockStatement(stmt.consequent)
			) {
				const testedName = nullCheck.tested.name;
				for (const inner of stmt.consequent.body) {
					if (
						!t.isVariableDeclaration(inner) ||
						inner.declarations.length !== 1
					) continue;
					const [decl] = inner.declarations;
					if (!t.isCallExpression(decl.init)) continue;
					if (
						!t.isV8IntrinsicIdentifier(decl.init.callee, {
							name: 'Phi',
						})
					) continue;
					const args = decl.init.arguments.filter(t.isExpression);
					if (
						!args.some((arg) =>
							t.isIdentifier(arg, {
								name: testedName,
							})
						)
					) continue;
					const computedSources = args.filter((arg) =>
						!t.isIdentifier(arg) && !isPrimitivePhiSource(arg)
					);
					if (computedSources.length !== 1) continue;
					decl.init = t.cloneNode(computedSources[0], true);
					changed = true;
				}
				changed = simplifyNullGuardedPhiDeclarations(
					stmt.consequent.body,
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = simplifyNullGuardedPhiDeclarations(
					stmt.alternate.body,
				) || changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt) || t.isForStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = simplifyNullGuardedPhiDeclarations(stmt.body.body) ||
				changed;
		} else if (t.isTryStatement(stmt)) {
			changed = simplifyNullGuardedPhiDeclarations(stmt.block.body) ||
				changed;
			if (stmt.handler) {
				changed = simplifyNullGuardedPhiDeclarations(
					stmt.handler.body.body,
				) || changed;
			}
			if (stmt.finalizer) {
				changed = simplifyNullGuardedPhiDeclarations(
					stmt.finalizer.body,
				) || changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = simplifyNullGuardedPhiDeclarations(
					switchCase.consequent,
				) || changed;
			}
		}
	}

	return changed;
}

function simplifyImmediatePrecedingPhiDeclarations(
	body: t.Statement[],
): boolean {
	let changed = false;

	for (let i = 1; i < body.length; i++) {
		const prev = body[i - 1];
		const stmt = body[i];
		if (
			!t.isVariableDeclaration(prev, { kind: 'const' }) ||
			prev.declarations.length !== 1 ||
			!t.isVariableDeclaration(stmt, { kind: 'const' }) ||
			stmt.declarations.length !== 1
		) continue;
		const [sourceDecl] = prev.declarations;
		const [phiDecl] = stmt.declarations;
		if (!t.isIdentifier(sourceDecl.id)) continue;
		if (
			!t.isIdentifier(phiDecl.id) ||
			!t.isCallExpression(phiDecl.init) ||
			!t.isV8IntrinsicIdentifier(phiDecl.init.callee, { name: 'Phi' })
		) continue;
		const sourceName = sourceDecl.id.name;
		if (
			!phiDecl.init.arguments.some((arg) =>
				t.isIdentifier(arg, { name: sourceName })
			)
		) continue;
		phiDecl.init = t.identifier(sourceName);
		changed = true;
	}

	return changed;
}

function liftPhiAssignmentsInBody(body: t.Statement[]): boolean {
	let anyChanged = false;

	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (!t.isExpressionStatement(stmt)) continue;
		const expr = stmt.expression;
		if (
			!t.isAssignmentExpression(expr, { operator: '=' }) ||
			!t.isIdentifier(expr.left) ||
			!t.isCallExpression(expr.right) ||
			!t.isV8IntrinsicIdentifier(expr.right.callee, { name: 'Phi' })
		) continue;

		const destName = expr.left.name;
		const args = expr.right.arguments.filter(t.isExpression);
		let insertionIndex = i;
		let initialValue: t.Expression | undefined;
		interface SourceReplace {
			container: t.Statement[];
			index: number;
			initExpr: t.Expression;
			srcName: string;
		}
		const toReplace: SourceReplace[] = [];

		for (const arg of args) {
			if (!t.isIdentifier(arg)) {
				if (initialValue === undefined) {
					initialValue = t.cloneNode(arg, true);
				}
				continue;
			}
			const srcName = arg.name;
			if (srcName === destName) {
				if (initialValue === undefined) {
					initialValue = t.identifier(destName);
				}
				continue;
			}

			let handled = false;
			for (let j = i - 1; j >= 0; j--) {
				const sib = body[j];
				if (t.isVariableDeclaration(sib)) {
					for (const d of sib.declarations) {
						if (t.isIdentifier(d.id, { name: srcName }) && d.init) {
							if (initialValue === undefined) {
								initialValue = t.cloneNode(d.init, true);
							}
							handled = true;
							break;
						}
					}
					if (handled) break;
				}
				const assignmentInit = assignmentInitInStmt(sib, srcName);
				if (assignmentInit) {
					if (initialValue === undefined) {
						initialValue = t.identifier(srcName);
					}
					handled = true;
					break;
				}
				const inner = findDeclInStmt(sib, srcName);
				if (inner) {
					if (!inner.init) continue;
					insertionIndex = Math.min(insertionIndex, j);
					toReplace.push({
						container: inner.container,
						index: inner.index,
						initExpr: t.cloneNode(inner.init, true),
						srcName,
					});
					handled = true;
					break;
				}
			}

			if (!handled && initialValue === undefined) {
				initialValue = t.cloneNode(arg, true);
			}
		}

		if (toReplace.length === 0) continue;

		for (const { container, index, initExpr, srcName } of toReplace) {
			container[index] = t.expressionStatement(
				t.assignmentExpression('=', t.identifier(destName), initExpr),
			);
			for (let k = index + 1; k < container.length; k++) {
				t.traverseFast(container[k], (node) => {
					if (t.isIdentifier(node, { name: srcName })) {
						node.name = destName;
					}
				});
			}
		}

		if (
			initialValue === undefined ||
			t.isIdentifier(initialValue, { name: destName })
		) {
			body.splice(i, 1);
			i--;
		} else if (insertionIndex < i) {
			body.splice(
				insertionIndex,
				0,
				t.expressionStatement(
					t.assignmentExpression(
						'=',
						t.identifier(destName),
						initialValue,
					),
				),
			);
			body.splice(i + 1, 1);
		} else {
			expr.right = initialValue;
		}
		anyChanged = true;
	}

	return anyChanged;
}

function recoveredEnvironmentSSANames(body: t.Statement[]): Set<string> {
	const names = new Set<string>();
	for (const statement of body) {
		t.traverseFast(statement, (node) => {
			if (
				t.isIdentifier(node) &&
				(node as LiftedAST<t.Identifier>).extra
						?.recoveredEnvironmentSSA === true
			) names.add(node.name);
		});
	}
	return names;
}

function restoreRecoveredEnvironmentSSAProvenance(
	body: t.Statement[],
	names: ReadonlySet<string>,
): void {
	if (names.size === 0) return;
	for (const statement of body) {
		t.traverseFast(statement, (node) => {
			if (!t.isIdentifier(node) || !names.has(node.name)) return;
			const lifted = node as LiftedAST<t.Identifier>;
			lifted.extra = {
				...lifted.extra,
				recoveredEnvironmentSSA: true,
			};
		});
	}
}

export function liftPhiNodesInBody(
	body: t.Statement[],
	options: {
		includePatternBindings?: boolean;
		preserveLoopPhiDestinations?: boolean;
	} = {},
): boolean {
	let anyChanged = false;
	const recoveredEnvironmentNames = recoveredEnvironmentSSANames(body);

	anyChanged = liftLoopHeaderPhiNodes(
		body,
		options.preserveLoopPhiDestinations === true,
	) || anyChanged;
	anyChanged = liftLoopHeaderPhiAssignments(body) || anyChanged;
	while (liftPhiAcrossFollowingContainer(body)) anyChanged = true;

	// Bottom-up: recurse into nested blocks first
	for (const stmt of body) {
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				anyChanged =
					liftPhiNodesInBody(stmt.consequent.body, options) ||
					anyChanged;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				anyChanged = liftPhiNodesInBody(stmt.alternate.body, options) ||
					anyChanged;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			anyChanged = liftPhiNodesInBody(stmt.body.body, options) ||
				anyChanged;
		} else if (t.isTryStatement(stmt)) {
			anyChanged = liftPhiNodesInBody(stmt.block.body, options) ||
				anyChanged;
			if (stmt.handler) {
				anyChanged = liftPhiNodesInBody(
					stmt.handler.body.body,
					options,
				) ||
					anyChanged;
			}
			if (stmt.finalizer) {
				anyChanged = liftPhiNodesInBody(stmt.finalizer.body, options) ||
					anyChanged;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				anyChanged = liftPhiNodesInBody(
					switchCase.consequent,
					options,
				) ||
					anyChanged;
			}
		}
	}

	anyChanged = removeUnusedPhiExpressions(body) || anyChanged;
	anyChanged = liftPhiAssignmentsInBody(body) || anyChanged;

	// Lift each Phi declaration
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (!t.isVariableDeclaration(stmt)) continue;
		if (stmt.declarations.length !== 1) continue;
		const phiDecl = stmt.declarations[0];
		if (!t.isIdentifier(phiDecl.id)) continue;
		if (!t.isCallExpression(phiDecl.init)) continue;
		if (!t.isV8IntrinsicIdentifier(phiDecl.init.callee, { name: 'Phi' })) {
			continue;
		}

		const destName = phiDecl.id.name;
		const args = phiDecl.init.arguments as t.Expression[];
		const sourceNames = args.every((arg) => t.isIdentifier(arg))
			? args.map((arg) => (arg as t.Identifier).name).sort()
			: null;
		if (
			args.length > 0 &&
			args.every((arg) => t.isIdentifier(arg, { name: destName }))
		) {
			body.splice(i, 1);
			i--;
			anyChanged = true;
			continue;
		}
		if (sourceNames) {
			const priorAccumulator = body.slice(0, i).findLast((candidate) => {
				if (!t.isVariableDeclaration(candidate)) return false;
				const priorSources =
					(candidate as LiftedAST<t.VariableDeclaration>)
						.extra?.liftedPhiSources;
				return priorSources?.length === sourceNames.length &&
					priorSources.every((name, index) =>
						name === sourceNames[index]
					);
			});
			if (
				priorAccumulator && t.isVariableDeclaration(priorAccumulator) &&
				priorAccumulator.declarations.length === 1
			) {
				const priorId = priorAccumulator.declarations[0].id;
				if (t.isIdentifier(priorId)) {
					phiDecl.init = t.identifier(priorId.name);
					anyChanged = true;
					continue;
				}
			}
		}
		// Only pristine SSA Phi declarations are restructured below. A previously
		// lifted `let` can reach this point when later simplification rewrites its
		// initializer; the provenance-based reuse above is the safe repair for it.
		if (stmt.kind !== 'const') continue;

		// insertionIndex tracks where to put `let destName` — starts at i (before the Phi
		// itself, the loop-carried default) and can be pulled earlier by branch-merge sources.
		let insertionIndex = i;
		let initialValue: t.Expression | undefined;

		interface SourceReplace {
			container: t.Statement[];
			index: number;
			initExpr?: t.Expression;
			replacement?: (destName: string) => t.Statement[];
			srcName: string;
		}
		const toReplace: SourceReplace[] = [];

		for (const arg of args) {
			if (!t.isIdentifier(arg)) {
				// Already-inlined expression (e.g. `global`) — use as initial value.
				if (initialValue === undefined) {
					initialValue = t.cloneNode(arg as t.Expression, true);
				}
				continue;
			}
			const srcName = arg.name;
			let handled = false;

			// Search PRECEDING siblings for srcName.
			for (let j = i - 1; j >= 0; j--) {
				const sib = body[j];
				// Direct const declaration in this block — in-scope source.
				if (t.isVariableDeclaration(sib)) {
					for (const d of sib.declarations) {
						if (t.isIdentifier(d.id, { name: srcName }) && d.init) {
							if (initialValue === undefined) {
								initialValue = sib.kind === 'const'
									? t.cloneNode(d.init, true)
									: t.identifier(srcName);
							}
							handled = true;
							break;
						}
					}
					if (handled) break;
				}
				const assignmentInit = assignmentInitInStmt(sib, srcName);
				if (assignmentInit) {
					if (initialValue === undefined) {
						initialValue = t.identifier(srcName);
					}
					handled = true;
					break;
				}
				// Declaration inside the sibling (if branch, while body, try block).
				const inner = findDeclInStmt(sib, srcName);
				if (inner) {
					if (
						!inner.init &&
						(!options.includePatternBindings || !inner.replacement)
					) continue;
					insertionIndex = Math.min(insertionIndex, j);
					toReplace.push({
						container: inner.container,
						index: inner.index,
						initExpr: inner.init
							? t.cloneNode(inner.init, true)
							: undefined,
						replacement: options.includePatternBindings
							? inner.replacement
							: undefined,
						srcName,
					});
					handled = true;
					break;
				}
			}

			if (!handled) {
				// Search FOLLOWING siblings — loop-carried source (defined after the Phi
				// in the same block, e.g. the update register in a while body).
				for (let j = i + 1; j < body.length; j++) {
					const sib = body[j];
					if (t.isVariableDeclaration(sib)) {
						for (const d of sib.declarations) {
							if (
								t.isIdentifier(d.id, { name: srcName }) &&
								d.init
							) {
								toReplace.push({
									container: body,
									index: j,
									initExpr: t.cloneNode(d.init, true),
									srcName,
								});
								handled = true;
								break;
							}
						}
						if (handled) break;
					}
					const assignmentInit = assignmentInitInStmt(sib, srcName);
					if (assignmentInit) {
						toReplace.push({
							container: body,
							index: j,
							initExpr: t.cloneNode(assignmentInit, true),
							srcName,
						});
						handled = true;
						break;
					}
				}

				if (!handled && initialValue === undefined) {
					// The source has no declaration in this block — it's a register from an
					// enclosing scope, valid as-is. Use it directly as the default rather than
					// dropping it (which would leave `let X;` defaulting to undefined and lose
					// e.g. the `A` in `A && obj`).
					initialValue = t.cloneNode(arg as t.Expression, true);
				}
			}
		}

		if (toReplace.length === 0) continue; // Nothing to restructure.

		// Apply replacements in the SOURCE containers.
		// Process body-array replacements from highest index to lowest to avoid shifting.
		const bodyReplaces = toReplace.filter((r) => r.container === body).sort(
			(a, b) => b.index - a.index,
		);
		const otherReplaces = toReplace.filter((r) => r.container !== body);

		for (
			const { container, index, initExpr, replacement, srcName }
				of otherReplaces
		) {
			if (replacement) {
				container.splice(index, 1, ...replacement(destName));
				continue;
			}
			if (!initExpr) continue;
			container[index] = t.expressionStatement(
				t.assignmentExpression('=', t.identifier(destName), initExpr),
			);
			// Rename all remaining uses of the now-replaced source SSA variable to
			// destName, since its declaration has been turned into a destName assignment.
			for (let k = index + 1; k < container.length; k++) {
				t.traverseFast(container[k], (node) => {
					if (t.isIdentifier(node, { name: srcName })) {
						(node as t.Identifier).name = destName;
					}
				});
			}
		}
		for (const { index, initExpr, replacement } of bodyReplaces) {
			if (replacement) {
				body.splice(index, 1, ...replacement(destName));
				continue;
			}
			if (!initExpr) continue;
			body[index] = t.expressionStatement(
				t.assignmentExpression('=', t.identifier(destName), initExpr),
			);
		}

		// Insert `let destName [= initialValue]` at insertionIndex, carrying forward the
		// IR-level conditional-merge marker from the Phi declaration so the deferred fold
		// can recognise this `let destName = D; if (C) { destName = R }` as foldable.
		const letDecl = t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier(destName), initialValue),
		]);
		const letExtra = (letDecl as LiftedAST<t.VariableDeclaration>).extra ??=
			{};
		if (sourceNames) letExtra.liftedPhiSources = sourceNames;
		if (
			(stmt as LiftedAST<t.VariableDeclaration>).extra
				?.isPotentialConditionalValue
		) {
			letExtra.isPotentialConditionalValue = true;
		}
		body.splice(insertionIndex, 0, letDecl);
		i++; // account for the inserted statement; Phi is now at i

		// Remove the Phi declaration.
		body.splice(i, 1);
		i--; // the for-loop will do i++, so net movement is 0

		anyChanged = true;
	}

	anyChanged = simplifyScopedPhiCalls(body) || anyChanged;
	anyChanged = simplifyScopedPhiDeclarations(body) || anyChanged;
	anyChanged = simplifyScopedPhiAssignments(body) || anyChanged;
	anyChanged = simplifyGuardedPrimitivePhiCalls(body) || anyChanged;
	anyChanged = simplifyTerminalReturnPhis(body) || anyChanged;
	anyChanged = simplifySelfUpdatePhiAssignments(body) || anyChanged;
	anyChanged = simplifyNullGuardedPhiDeclarations(body) || anyChanged;
	anyChanged = simplifyImmediatePrecedingPhiDeclarations(body) || anyChanged;
	restoreRecoveredEnvironmentSSAProvenance(
		body,
		recoveredEnvironmentNames,
	);

	return anyChanged;
}

// === Deferred conditional-value fold ===========================================
// Consumes the `isPotentialConditionalValue` marker stamped at IR level (see
// markPotentialConditionalPhis in cfg/mod.ts) and collapses
//   let X = D; if (C) { X = R } [else { X = R2 }]
// into a single `const X = <??/||/&&/?./ternary>` once the conditionally-computed
// RVal has been reduced to a single expression. While the branch still spans
// multiple statements the marker is left in place and the fold retries later.

function branchSingleAssignment(
	branch: t.Statement | null | undefined,
	name: string,
): t.Expression | null {
	if (!branch) return null;
	const body = t.isBlockStatement(branch) ? branch.body : [branch];
	return assignmentProgramExpression(body, name);
}

function assignmentExpressionStatement(
	stmt: t.Statement,
	name: string,
): t.Expression | null {
	if (!t.isExpressionStatement(stmt)) return null;
	const expr = stmt.expression;
	if (!t.isAssignmentExpression(expr, { operator: '=' })) return null;
	if (!t.isIdentifier(expr.left, { name })) return null;
	return expr.right;
}

function assignmentProgramExpression(
	body: t.Statement[],
	name: string,
): t.Expression | null {
	if (body.length === 1) {
		const stmt = body[0];
		const assignment = assignmentExpressionStatement(stmt, name);
		if (assignment) return assignment;
		if (!t.isIfStatement(stmt)) return null;
		const thenVal = branchSingleAssignment(stmt.consequent, name);
		const elseVal = branchSingleAssignment(stmt.alternate, name);
		if (!thenVal || !elseVal) return null;
		// Route through the folder rather than emitting a ternary outright:
		// this shape carries the same nullish/shortcut forms as every other
		// conditional value, and building the ternary here hid them.
		return buildConditionalValueExpression(stmt.test, thenVal, elseVal);
	}

	if (body.length !== 2) return null;
	const [localDeclaration, localConditional] = body;
	if (
		t.isVariableDeclaration(localDeclaration, { kind: 'const' }) &&
		localDeclaration.declarations.length === 1 &&
		t.isIdentifier(localDeclaration.declarations[0].id) &&
		t.isExpression(localDeclaration.declarations[0].init) &&
		t.isIfStatement(localConditional)
	) {
		const [declarator] = localDeclaration.declarations;
		const nested = assignmentProgramExpression([localConditional], name);
		if (nested) {
			return substituteSingleExpressionIdentifier(
				nested,
				(declarator.id as t.Identifier).name,
				declarator.init as t.Expression,
			);
		}
	}
	const defaultValue = assignmentExpressionStatement(body[0], name);
	const ifStmt = body[1];
	if (!defaultValue || !t.isIfStatement(ifStmt) || ifStmt.alternate) {
		return null;
	}
	const thenVal = branchSingleAssignment(ifStmt.consequent, name);
	if (!thenVal || !isPureConditionalDefault(defaultValue)) return null;
	return buildConditionalValueExpression(
		ifStmt.test,
		thenVal,
		defaultValue,
	);
}

/**
 * Inline a receiver cached immediately before a nullish guard. The folded
 * optional chain contains the receiver exactly once, so replacing that one
 * reference preserves both evaluation count and getter/call receiver identity.
 */
function substituteSingleExpressionIdentifier(
	expression: t.Expression,
	name: string,
	replacement: t.Expression,
): t.Expression | null {
	const statement = t.expressionStatement(t.cloneNode(expression, true));
	const file = t.file(t.program([statement]));
	let references = 0;
	traverse(file, {
		noScope: true,
		Identifier(path) {
			if (!path.isReferencedIdentifier({ name })) return;
			references++;
		},
	});
	if (references !== 1) return null;
	traverse(file, {
		noScope: true,
		Identifier(path) {
			if (!path.isReferencedIdentifier({ name })) return;
			path.replaceWith(t.cloneNode(replacement, true));
			path.skip();
		},
	});
	return references === 1 && t.isExpression(statement.expression)
		? statement.expression
		: null;
}

// `A == null` / `A != null`, including the `!(A == null)` wrapping the decompiler emits.
function asNullCheck(
	test: t.Expression,
): { tested: t.Expression; trueWhenNull: boolean } | null {
	if (
		t.isUnaryExpression(test, { operator: '!' }) &&
		t.isExpression(test.argument)
	) {
		const inner = asNullCheck(test.argument);
		return inner
			? { tested: inner.tested, trueWhenNull: !inner.trueWhenNull }
			: null;
	}
	if (
		t.isBinaryExpression(test) &&
		(test.operator === '==' || test.operator === '!=')
	) {
		const { left, right } = test;
		let tested: t.Expression | null = null;
		if (t.isNullLiteral(right) && t.isExpression(left)) tested = left;
		else if (t.isNullLiteral(left) && t.isExpression(right)) tested = right;
		if (tested) return { tested, trueWhenNull: test.operator === '==' };
	}
	return null;
}

// Given `tested != null` guarding `value` (an access on `tested`), build the optional form.
function buildOptionalAccess(
	tested: t.Expression,
	value: t.Expression,
): t.Expression | null {
	return prependOptionalAccess(value, tested);
}

/** Add an optional boundary at the matching root of an existing access chain. */
function prependOptionalAccess(
	value: t.Expression,
	tested: t.Expression,
): t.Expression | null {
	if (t.isMemberExpression(value) || t.isOptionalMemberExpression(value)) {
		if (!t.isExpression(value.object)) return null;
		if (nodesCodeEqual(value.object, tested)) {
			return t.optionalMemberExpression(
				t.cloneNode(value.object, true),
				t.cloneNode(value.property, true),
				value.computed,
				true,
			);
		}
		const object = prependOptionalAccess(value.object, tested);
		if (!object) return null;
		return t.optionalMemberExpression(
			object,
			t.cloneNode(value.property, true),
			value.computed,
			t.isOptionalMemberExpression(value) ? value.optional : false,
		);
	}
	if (t.isCallExpression(value) || t.isOptionalCallExpression(value)) {
		if (!t.isExpression(value.callee)) return null;
		const args = value.arguments.map((argument) =>
			t.cloneNode(argument, true)
		);
		if (nodesCodeEqual(value.callee, tested)) {
			return t.optionalCallExpression(
				t.cloneNode(value.callee, true),
				args,
				true,
			);
		}
		const callee = prependOptionalAccess(value.callee, tested);
		if (!callee) return null;
		return t.optionalCallExpression(
			callee,
			args,
			t.isOptionalCallExpression(value) ? value.optional : false,
		);
	}
	return null;
}

function foldConditionalValue(
	decl: t.VariableDeclaration,
	ifStmt: t.IfStatement,
	name: string,
): t.Expression | null {
	const test = ifStmt.test;
	const thenVal = branchSingleAssignment(ifStmt.consequent, name);
	if (!thenVal) return null; // RVal not yet a single expression — defer.

	if (ifStmt.alternate) {
		const elseVal = branchSingleAssignment(ifStmt.alternate, name);
		if (!elseVal) return null;
		return buildConditionalValueExpression(test, thenVal, elseVal);
	}

	const dflt = decl.declarations[0].init;
	if (!dflt || !t.isExpression(dflt)) return null;
	return buildGuardedConditionalValue(test, thenVal, dflt);
}

/**
 * Reconstruct the source-level expression represented by a two-way conditional
 * Phi. Both legacy Phi lifting and recursive Region emission use this helper so
 * shortcut/nullish/optional forms do not depend on their declaration layout.
 */
export function buildConditionalValueExpression(
	test: t.Expression,
	consequent: t.Expression,
	alternate: t.Expression,
): t.Expression {
	const direct = buildGuardedConditionalValue(test, consequent, alternate);
	if (direct) return direct;

	// Also recognize the equivalent form with the carried/default value in the
	// consequent arm: `A ? A : R` is `A || R`, for example.
	const inverted = buildGuardedConditionalValue(
		invertTest(t.cloneNode(test, true)),
		alternate,
		consequent,
	);
	if (inverted) return inverted;

	return t.conditionalExpression(test, consequent, alternate);
}

function buildGuardedConditionalValue(
	test: t.Expression,
	thenVal: t.Expression,
	dflt: t.Expression,
): t.Expression | null {
	if (t.isIdentifier(dflt, { name: 'undefined' })) {
		const optNullCheck = asNullCheck(test);
		if (!optNullCheck || optNullCheck.trueWhenNull) return null;
		const optional = buildOptionalAccess(optNullCheck.tested, thenVal);
		if (optional) return optional;
	}

	// A ?? R : guard is `A == null`, default is A.
	const nullCheck = asNullCheck(test);
	if (
		nullCheck && nullCheck.trueWhenNull &&
		nodesCodeEqual(nullCheck.tested, dflt)
	) {
		return t.logicalExpression('??', dflt, thenVal);
	}

	// A ?? R, inverted layout: `let X = R; if (A != null) { X = A }`.
	// The unconditional default read is side-effect-free when it is an identifier,
	// so this preserves the original branch-only evaluation of A.
	if (
		nullCheck && !nullCheck.trueWhenNull &&
		nodesCodeEqual(nullCheck.tested, thenVal) &&
		isPureConditionalDefault(dflt)
	) {
		return t.logicalExpression('??', thenVal, dflt);
	}

	// A && R: the guard is the default itself — `let X = A; if (A) { X = R }`. A may be any
	// expression (e.g. `!flag`), so compare the whole test against the default, not a stripped
	// operand. A is always evaluated (the && left operand), matching the let initializer.
	if (nodesCodeEqual(test, dflt)) {
		return t.logicalExpression('&&', dflt, thenVal);
	}

	// A || R: the guard is the negation of the default — `let X = A;
	// if (!A) { X = R }`. Compare the normalized inverse so branch opcodes such
	// as `null === value` also match a carried `null !== value` predicate.
	if (
		nodesCodeEqual(
			invertTest(t.cloneNode(test, true)),
			dflt,
		)
	) {
		return t.logicalExpression('||', dflt, thenVal);
	}

	// General ternary: `let X = D; if (C) { X = R }` ≡ `C ? R : D`. Only safe when D is
	// side-effect-free — D is the unconditional initializer but the ternary skips it when C
	// is true. A LoadConst-derived literal (e.g. `null`) is pure, so this is sound there.
	if (isPureConditionalDefault(dflt)) {
		return t.conditionalExpression(test, thenVal, dflt);
	}

	return null;
}

// Side-effect-free constants — safe to relocate into a conditionally-evaluated position.
function isPureConstant(node: t.Expression): boolean {
	return t.isNullLiteral(node) ||
		t.isNumericLiteral(node) ||
		t.isStringLiteral(node) ||
		t.isBooleanLiteral(node) ||
		t.isBigIntLiteral(node) ||
		t.isRegExpLiteral(node) ||
		t.isIdentifier(node, { name: 'undefined' });
}

function isPureConditionalDefault(node: t.Expression): boolean {
	return isPureConstant(node) || t.isIdentifier(node) ||
		t.isThisExpression(node);
}

// Without a conditional-Phi marker, only deduplicate guards whose evaluation is
// mechanically repeatable. The hoisted layout evaluates the default and test
// separately, while `A && B` / `A || B` evaluates A once. Marked SSA values carry
// the stronger provenance needed for effectful expressions; this conservative
// fallback covers the common `typeof x === 'object'` and identifier guards.
function isRepeatableConditionalGuard(node: t.Expression): boolean {
	if (
		isPureConstant(node) || t.isIdentifier(node) || t.isThisExpression(node)
	) {
		return true;
	}
	if (t.isUnaryExpression(node)) {
		return (node.operator === '!' || node.operator === 'typeof') &&
			t.isExpression(node.argument) &&
			isRepeatableConditionalGuard(node.argument);
	}
	if (t.isBinaryExpression(node)) {
		const safeComparison = node.operator === '===' ||
			node.operator === '!==' ||
			(
				(node.operator === '==' || node.operator === '!=') &&
				(t.isNullLiteral(node.left) || t.isNullLiteral(node.right))
			);
		return safeComparison && t.isExpression(node.left) &&
			t.isExpression(node.right) &&
			isRepeatableConditionalGuard(node.left) &&
			isRepeatableConditionalGuard(node.right);
	}
	if (t.isLogicalExpression(node)) {
		return isRepeatableConditionalGuard(node.left) &&
			isRepeatableConditionalGuard(node.right);
	}
	return false;
}

function assignsIdentifier(stmts: t.Statement[], name: string): boolean {
	return stmts.some((stmt) => {
		let found = false;
		t.traverseFast(stmt, (node) => {
			if (
				t.isAssignmentExpression(node) &&
				t.isIdentifier(node.left, { name })
			) found = true;
		});
		return found;
	});
}

/**
 * Re-run the conditional-value recogniser over ternaries already built.
 *
 * A conditional value is folded as soon as its `if` is recognised, which can
 * be before copy collapsing has unified the registers it mentions: one case
 * tested `r1_2` for null while the arm carried `r2_3`, the same value under
 * two names, so the nullish form did not match and a plain ternary was
 * emitted. Those names read alike once the copies collapse, and running the
 * same recogniser over the finished ternary recovers the `??`/`||`/`&&` form.
 *
 * The recogniser hands back an equivalent ternary when nothing matches, so
 * only a shape that actually improved is written back and repeated runs
 * settle.
 */
export function refoldConditionalValues(node: t.Node): boolean {
	let changed = false;
	t.traverseFast(node, (child) => {
		if (!t.isConditionalExpression(child)) return;
		const rebuilt = buildConditionalValueExpression(
			child.test,
			child.consequent,
			child.alternate,
		);
		if (t.isConditionalExpression(rebuilt)) return;

		for (const key of Object.keys(child)) {
			delete (child as unknown as Record<string, unknown>)[key];
		}
		Object.assign(child, rebuilt);
		changed = true;
	});

	return changed;
}

export function foldConditionalValuesInBody(body: t.Statement[]): boolean {
	let changed = false;

	// Bottom-up: fold inner conditionals first so nested/composed forms collapse.
	for (const stmt of body) {
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = foldConditionalValuesInBody(stmt.consequent.body) ||
					changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = foldConditionalValuesInBody(stmt.alternate.body) ||
					changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt) || t.isForStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = foldConditionalValuesInBody(stmt.body.body) || changed;
		} else if (t.isTryStatement(stmt)) {
			changed = foldConditionalValuesInBody(stmt.block.body) || changed;
			if (stmt.handler) {
				changed = foldConditionalValuesInBody(stmt.handler.body.body) ||
					changed;
			}
			if (stmt.finalizer) {
				changed = foldConditionalValuesInBody(stmt.finalizer.body) ||
					changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			for (const switchCase of stmt.cases) {
				changed = foldConditionalValuesInBody(switchCase.consequent) ||
					changed;
			}
		}
	}

	for (let i = 0; i < body.length; i++) {
		const decl = body[i];
		if (!t.isVariableDeclaration(decl, { kind: 'let' })) continue;
		if (decl.declarations.length !== 1) continue;
		const declarator = decl.declarations[0];
		const id = declarator.id;
		if (!t.isIdentifier(id)) continue;

		// Recursive emission hoists conditional-Phi targets to `let X;`, then
		// places the carried/default edge assignment immediately before the if:
		//
		//     let X;
		//     X = A;
		//     if (A) X = B;
		//
		// Treat that as the initialized layout consumed by the existing fold.
		// The exact adjacency and single-assignment arm keep this provenance-free
		// fallback mechanical; `buildGuardedConditionalValue` still rejects an
		// unsafe relocation of an effectful default.
		let ifIndex = i + 1;
		let foldDeclaration: t.VariableDeclaration = decl;
		const separateDefault = declarator.init == null
			? assignmentExpressionStatement(body[i + 1], id.name)
			: null;
		if (separateDefault) {
			if (expressionReferencesIdentifier(separateDefault, id.name)) {
				continue;
			}
			ifIndex++;
			foldDeclaration = t.variableDeclaration('let', [
				t.variableDeclarator(
					t.identifier(id.name),
					t.cloneNode(separateDefault, true),
				),
			]);
		}

		const ifStmt = body[ifIndex];
		if (!t.isIfStatement(ifStmt)) continue;
		const hasConditionalPhiMarker =
			(decl as LiftedAST<t.VariableDeclaration>).extra
				?.isPotentialConditionalValue === true;
		const isCompleteUnmarkedAssignment = (separateDefault != null &&
			isRepeatableConditionalGuard(separateDefault)) ||
			(
				declarator.init == null && ifStmt.alternate != null &&
				branchSingleAssignment(ifStmt.consequent, id.name) != null &&
				branchSingleAssignment(ifStmt.alternate, id.name) != null
			);
		if (
			(decl as LiftedAST<t.VariableDeclaration>).extra
				?.preserveAcrossBlocks &&
			!isCompleteUnmarkedAssignment
		) continue;
		if (!hasConditionalPhiMarker && !isCompleteUnmarkedAssignment) {
			continue;
		}

		const folded = foldConditionalValue(
			foldDeclaration,
			ifStmt,
			id.name,
		);
		if (!folded) continue; // deferred — leave the marker for a later pass.

		// SSA temps are single-assignment; only emit `const` when nothing reassigns it.
		const rest = body.slice(ifIndex + 1);
		const kind = assignsIdentifier(rest, id.name) ? 'let' : 'const';

		// Keep cross-block liveness/provenance metadata attached to the original
		// declaration. Per-block cleanup relies on `preserveAcrossBlocks` after
		// this fold and would otherwise discard a value used by a successor.
		(decl as t.VariableDeclaration).kind = kind;
		declarator.init = folded;
		body.splice(i + 1, ifIndex - i); // remove default assignment and folded if
		changed = true;
	}

	return changed;
}
