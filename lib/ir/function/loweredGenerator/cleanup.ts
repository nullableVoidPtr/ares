import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import { rewriteStructuredStatementLists } from '../../ast/statementLists.ts';
import type { LiftedAST } from '../../ast/mod.ts';
import type { IRFunction } from '../mod.ts';
import type { LoweredGeneratorModel } from './types.ts';

function referencedNamesInStatements(statements: t.Statement[]): Set<string> {
	const names = new Set<string>();
	if (statements.length === 0) return names;
	const wrapped = t.file(t.program(statements));
	traverse(wrapped, {
		Identifier(path: NodePath<t.Identifier>) {
			if (path.isReferencedIdentifier()) names.add(path.node.name);
		},
	});
	return names;
}

function hoistTrySharedRegisterDeclarationsInList(
	body: t.Statement[],
): boolean {
	let changed = false;
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (!t.isTryStatement(stmt)) continue;

		const siblingReferences = referencedNamesInStatements([
			...(stmt.handler?.body.body ?? []),
			...(stmt.finalizer?.body ?? []),
		]);
		if (siblingReferences.size === 0) continue;

		const hoisted: t.VariableDeclaration[] = [];
		for (let j = 0; j < stmt.block.body.length; j++) {
			const declaration = stmt.block.body[j];
			if (
				!t.isVariableDeclaration(declaration) ||
				declaration.declarations.length !== 1
			) continue;
			const declarator = declaration.declarations[0];
			if (
				!t.isIdentifier(declarator.id) || !declarator.init ||
				!/^r\d+_\d+$/.test(declarator.id.name) ||
				!siblingReferences.has(declarator.id.name)
			) continue;

			const outerDeclaration = t.variableDeclaration('let', [
				t.variableDeclarator(t.cloneNode(declarator.id)),
			]);
			(outerDeclaration as LiftedAST<t.VariableDeclaration>).extra = {
				preserveAcrossBlocks: true,
			};
			hoisted.push(outerDeclaration);
			stmt.block.body[j] = t.expressionStatement(t.assignmentExpression(
				'=',
				t.cloneNode(declarator.id),
				t.cloneNode(declarator.init, true) as t.Expression,
			));
			changed = true;
		}
		if (hoisted.length > 0) {
			body.splice(i, 0, ...hoisted);
			i += hoisted.length;
		}
	}
	return changed;
}

export function hoistRecoveredTrySharedRegisterDeclarations(
	func: IRFunction,
): boolean {
	let changed = false;
	for (const block of func.blocks.values()) {
		changed = rewriteStructuredStatementLists(
			block.body as t.Statement[],
			hoistTrySharedRegisterDeclarationsInList,
		) || changed;
	}
	return changed;
}

/**
 * Any environment cell left after CFG-based SSA promotion is still a proven
 * non-escaping generator local. Lower it to one function-scoped mutable binding
 * so storage implementation names never survive native generator recovery.
 */
export function lowerRecoveredEnvironmentCellsToLocals(func: IRFunction) {
	if (func.blocks.size !== 1) return false;
	const block = func.blocks.values().next().value;
	if (!block) return false;
	const wrapped = t.file(t.program(block.body as t.Statement[]));
	const candidates = new Set<string>();
	traverse(wrapped, {
		Identifier(path: NodePath<t.Identifier>) {
			if (path.node.extra?.recoveredEnvironmentSlot) {
				candidates.add(path.node.name);
			}
		},
	});
	if (candidates.size === 0) return false;

	const replacements = new Map<string, t.Identifier>();
	for (const name of candidates) {
		const index = func.ssa.allocateSyntheticRegisterIndex();
		const register = func.ssa.allocateRegisterVersion(index);
		const identifier = t.identifier(
			`r${register.index}_${register.version}`,
		) as LiftedAST<t.Identifier>;
		identifier.extra = {
			sourceRegister: register,
			bindingOwnerFunctionId: func.id,
			recoveredEnvironmentLocal: true,
		};
		replacements.set(name, identifier);
	}
	traverse(wrapped, {
		Identifier(path: NodePath<t.Identifier>) {
			const replacement = replacements.get(path.node.name);
			if (!replacement) return;
			path.replaceWith(t.cloneNode(replacement));
		},
	});
	traverse(wrapped, {
		VariableDeclaration: {
			exit(path: NodePath<t.VariableDeclaration>) {
				if (path.node.declarations.length !== 1) return;
				const declarator = path.node.declarations[0];
				if (!t.isIdentifier(declarator.id)) return;
				const name = declarator.id.name;
				if (
					![...replacements.values()].some((replacement) =>
						replacement.name === name
					)
				) return;
				if (t.isExpression(declarator.init)) {
					path.replaceWith(t.expressionStatement(
						t.assignmentExpression(
							'=',
							t.cloneNode(declarator.id),
							declarator.init,
						),
					));
				} else {
					path.remove();
				}
			},
		},
	});
	wrapped.program.body.unshift(t.variableDeclaration(
		'let',
		[...replacements.values()].map((identifier) =>
			t.variableDeclarator(t.cloneNode(identifier))
		),
	));
	block.body = wrapped.program.body;
	return true;
}

export function repairDanglingRecoveredYieldOperands(
	func: IRFunction,
	model: LoweredGeneratorModel,
): void {
	if (model.parentParameterAliases.size === 0) return;
	for (const block of func.blocks.values()) {
		const wrapped = t.file(t.program(block.body as t.Statement[]));
		traverse(wrapped, {
			YieldExpression(path: NodePath<t.YieldExpression>) {
				if (!t.isIdentifier(path.node.argument)) return;
				const parameter = model.parentParameterAliases.get(
					path.node.argument.name,
				);
				if (parameter) {
					path.node.argument = t.cloneNode(parameter, true);
				}
			},
		});
		block.body = wrapped.program.body;
	}
}
