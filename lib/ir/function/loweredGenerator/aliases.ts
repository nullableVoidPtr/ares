import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import { FunctionKind } from '../../../hbc/disassembly/function.ts';
import { FunctionId } from '../../../hbc/disassembly/instruction.ts';
import { HBCFile } from '../../../parser/file.ts';
import { extractFunctionRef } from '../../ast/utils.ts';
import type { ElidedWrapperEnvironmentCapture } from '../../environment.ts';
import type { IRFunction } from '../mod.ts';
import { isIncomingValueExpression } from '../../ast/alias.ts';
import {
	environmentStoreFromStatement,
	loadEnvironmentCall,
} from './envAccess.ts';

export function recordLoweredGeneratorWrapperSlotAliases(
	file: HBCFile,
	loweredGeneratorId: FunctionId,
	body: t.Statement[],
	createGeneratorEnv: t.Node,
) {
	const wrapperSlotAliases = collectWrapperGeneratorSlotAliases(
		body,
		createGeneratorEnv,
	);
	if (wrapperSlotAliases.size === 0) return;
	file.loweredGeneratorWrapperSlotAliases.set(
		loweredGeneratorId,
		wrapperSlotAliases,
	);
}

export function applyLoweredGeneratorWrapperSlotAliases(func: IRFunction) {
	const slotAliases = func.file.loweredGeneratorWrapperSlotAliases.get(
		func.id,
	);
	if (!slotAliases?.size) return;
	let changed = false;

	const localNames = new Set<string>();
	for (const block of func.blocks.values()) {
		for (const stmt of <t.Statement[]> block.body) {
			if (!t.isVariableDeclaration(stmt)) continue;
			for (const decl of stmt.declarations) {
				if (!t.isIdentifier(decl.id)) continue;
				if (
					t.isCallExpression(decl.init) &&
					t.isV8IntrinsicIdentifier(decl.init.callee, {
						name: 'GetParentEnvironment',
					})
				) continue;
				localNames.add(decl.id.name);
			}
		}
	}

	for (const block of func.blocks.values()) {
		const wrapped = t.file(t.program(<t.Statement[]> block.body));
		traverse(wrapped, {
			VariableDeclarator(path: NodePath<t.VariableDeclarator>) {
				if (!t.isIdentifier(path.node.id)) return;
				if (!t.isExpression(path.node.init)) return;
				const load = loadEnvironmentCall(path.node.init);
				if (!load) return;
				const alias = slotAliases.get(load.slot);
				if (!alias) return;
				const binding = path.scope.getBinding(path.node.id.name);
				if (!binding || binding.referencePaths.length === 0) return;
				if (
					!binding.referencePaths.every((ref) =>
						ref.parentPath?.isMemberExpression({
							object: ref.node,
						})
					)
				) return;
				changed = true;
				path.node.init = t.cloneNode(alias, true);
			},
			MemberExpression(path: NodePath<t.MemberExpression>) {
				const load = loadEnvironmentCall(path.node);
				if (
					load &&
					t.isCallExpression(load.env) &&
					t.isV8IntrinsicIdentifier(load.env.callee, {
						name: 'GetParentEnvironment',
					})
				) {
					const alias = slotAliases.get(load.slot);
					if (!alias) return;
					changed = true;
					path.replaceWith(t.cloneNode(alias, true));
					return;
				}
				if (!path.node.computed) return;
				if (!t.isIdentifier(path.node.object)) return;
				if (path.node.object.name === 'arguments') return;
				if (localNames.has(path.node.object.name)) return;
				if (!t.isNumericLiteral(path.node.property)) return;
				const alias = slotAliases.get(path.node.property.value);
				if (!alias) return;
				changed = true;
				path.replaceWith(t.cloneNode(alias, true));
			},
		});
		block.body = wrapped.program.body;
	}
	if (changed) func.cleanupLiftedBlocks();
}

export interface LoweredGeneratorClosureAnalysis {
	functionId: FunctionId;
	environmentCapture: ElidedWrapperEnvironmentCapture;
}

function loweredGeneratorEnvironmentCapture(
	body: t.Statement[],
	env: t.Node,
	seenNames = new Set<string>(),
): ElidedWrapperEnvironmentCapture {
	if (
		t.isCallExpression(env) &&
		(
			t.isV8IntrinsicIdentifier(env.callee, {
				name: 'CreateFunctionEnvironment',
			}) ||
			t.isV8IntrinsicIdentifier(env.callee, {
				name: 'CreateTopLevelEnvironment',
			})
		)
	) return { kind: 'local' };
	if (
		t.isCallExpression(env) &&
		t.isV8IntrinsicIdentifier(env.callee, {
			name: 'GetParentEnvironment',
		}) &&
		t.isNumericLiteral(env.arguments[0])
	) return { kind: 'parent', depth: env.arguments[0].value };
	if (t.isIdentifier(env)) {
		if (seenNames.has(env.name)) return { kind: 'parent', depth: 0 };
		seenNames.add(env.name);
		for (const stmt of body) {
			if (t.isVariableDeclaration(stmt)) {
				for (const decl of stmt.declarations) {
					if (
						t.isIdentifier(decl.id, { name: env.name }) &&
						decl.init
					) {
						return loweredGeneratorEnvironmentCapture(
							body,
							decl.init,
							seenNames,
						);
					}
				}
			}
			if (
				t.isExpressionStatement(stmt) &&
				t.isAssignmentExpression(stmt.expression, { operator: '=' }) &&
				t.isIdentifier(stmt.expression.left, { name: env.name })
			) {
				return loweredGeneratorEnvironmentCapture(
					body,
					stmt.expression.right,
					seenNames,
				);
			}
		}
	}
	// Existing lowered-generator recognition accepts arbitrary environment
	// operands. Preserve its historical interpretation when the operand cannot
	// be proven to be a wrapper-local environment.
	return { kind: 'parent', depth: 0 };
}

export function analyseLoweredGeneratorClosure(
	wrapper: IRFunction,
): LoweredGeneratorClosureAnalysis | undefined {
	if (wrapper.ssa._func.functionKind !== FunctionKind.GeneratorFunction) {
		return;
	}
	if (wrapper.blocks.size !== 1) return;

	const body = <t.Statement[]> wrapper.blocks.get(0)!.body;
	const ret = body.at(-1);
	if (!t.isReturnStatement(ret)) return;
	const arg = ret.argument;
	if (
		!t.isCallExpression(arg) ||
		!t.isV8IntrinsicIdentifier(arg.callee, { name: 'CreateGenerator' })
	) return;
	if (arg.arguments.length !== 2) return;
	const loweredGeneratorId = extractFunctionRef(arg.arguments[1]);
	if (loweredGeneratorId == null) return;
	recordLoweredGeneratorWrapperSlotAliases(
		wrapper.file,
		loweredGeneratorId,
		body,
		arg.arguments[0],
	);
	return {
		functionId: loweredGeneratorId,
		environmentCapture: loweredGeneratorEnvironmentCapture(
			body,
			arg.arguments[0],
		),
	};
}

function collectWrapperGeneratorSlotAliases(
	body: t.Statement[],
	createGeneratorEnv: t.Node,
) {
	const envNames = new Set<string>();
	const valueAliases = new Map<string, t.Expression>();
	if (t.isIdentifier(createGeneratorEnv)) {
		envNames.add(createGeneratorEnv.name);
	}
	const aliases = new Map<number, t.Expression>();

	for (const stmt of body) {
		if (t.isVariableDeclaration(stmt)) {
			for (const decl of stmt.declarations) {
				if (
					t.isVariableDeclarator(decl) &&
					t.isIdentifier(decl.id) &&
					t.isIdentifier(decl.init, { name: 'arguments' })
				) {
					valueAliases.set(decl.id.name, t.identifier('arguments'));
				} else if (
					t.isVariableDeclarator(decl) &&
					t.isIdentifier(decl.id) &&
					t.isThisExpression(decl.init)
				) {
					valueAliases.set(decl.id.name, t.thisExpression());
				}
				if (
					!t.isVariableDeclarator(decl) ||
					!t.isIdentifier(decl.id) ||
					!t.isCallExpression(decl.init) ||
					!t.isV8IntrinsicIdentifier(decl.init.callee, {
						name: 'CreateFunctionEnvironment',
					})
				) continue;
				if (
					t.isIdentifier(createGeneratorEnv, {
						name: decl.id.name,
					})
				) {
					envNames.add(decl.id.name);
				}
			}
			continue;
		}

		const store = environmentStoreFromStatement(stmt);
		if (
			!store ||
			!t.isIdentifier(store.env) ||
			!envNames.has(store.env.name)
		) continue;
		let alias: t.Expression | undefined;
		if (t.isIdentifier(store.value)) {
			alias = valueAliases.get(store.value.name);
		}
		// `this`, `_param_<fn>_<i>_`, `arguments` and `arguments[k]` are four
		// spellings of the same thing -- a value that arrived from outside the
		// body -- so ask what the expression denotes rather than matching each
		// spelling in its own branch.
		if (!alias && isIncomingValueExpression(store.value)) {
			alias = t.cloneNode(store.value, true);
		}
		if (!alias) continue;
		aliases.set(store.slot, alias);
	}
	return aliases;
}
