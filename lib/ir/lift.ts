import * as t from '@babel/types';
import { SSAFunction } from '../ssa.ts';
// @ts-types="npm:@types/babel__generator"
import { default as _generate } from '@babel/generator';
// @ts-types="npm:@types/babel__traverse"
import { default as _traverse, Binding, Scope } from '@babel/traverse';
import { HBCFile } from '../parser/file.ts';
import { extractFunctionRef, LiftedExtra } from './ast.ts';
import { LiftError } from './error.ts';
import { IRFunction } from './function/mod.ts';
import { assert } from 'node:console';

const generate = _generate.default;
const traverse = _traverse.default;

export function liftFile(file: HBCFile) {
	const functions = new Map<number, IRFunction>();
	const soleFunctionReferences = new Map<number, Set<number>>();
	for (let i = 0; i < file.functions.length; i++) {
		const ssa = new SSAFunction(file.functions[i]);
		functions.set(i, new IRFunction(file, ssa));
		soleFunctionReferences.set(i, new Set());
	}

	for (const [id, func] of functions) {
		for (const [ref, count] of func.referencedFunctionIds) {
			if (count !== 1) continue;
			soleFunctionReferences.get(ref)!.add(id);
		}
	}

	const safelyNestedFunctions = new Set<number>();
	for (const [child, parent] of soleFunctionReferences) {
		if (parent.size !== 1) continue;
		safelyNestedFunctions.add(child);
	}

	const fileBody = functions.get(0)!.blocks.get(0)!;

	function popNestedFunction(functionId?: number) {
		if (functionId == null) return;
		if (!safelyNestedFunctions.has(functionId)) return;

		assert(functions.has(functionId));
		const func = functions.get(functionId);
		functions.delete(functionId);

		return func;
	}

	function inlineNestedFunctionRef(funcRef: t.Node) {
		return popNestedFunction(extractFunctionRef(funcRef));
	}

	const declaredGlobals = new Map<string, Binding>();
	const referencedGlobals = new Set<string>();
	const wrapped = t.file(t.program(<t.Statement[]>fileBody.body));
	traverse(wrapped, {
		CallExpression: {
			exit(call) {
				if (!t.isV8IntrinsicIdentifier(call.node.callee)) return;
				if (call.node.callee.name == 'CreateEnvironment') {
					const functionId = (<LiftedExtra | undefined>call.node.extra)?.parentFunctionId;
					if (functionId == null) throw new LiftError('Missing extra data');

					call.scope.setData('environment', `_env_${functionId}_`);
					call.remove();

					const decl = call.parentPath;
					if (!decl.isVariableDeclarator() || call.key != 'init') return;
					const id = decl.node.id;
					if (!t.isIdentifier(id)) return;
					const binding = decl.scope.getBinding(id.name);
					if (!binding?.constant) return;

					for (const ref of binding.referencePaths) {
						ref.replaceWith(t.callExpression(
							t.v8IntrinsicIdentifier('GetEnvironment'),
							[t.numericLiteral(0)],
						));
					}

					decl.remove();
				} else if (call.node.callee.name == 'LoadFromEnvironment') {
					const [env, slotIndex] = call.node.arguments;
					if (!t.isCallExpression(env) || !t.isV8IntrinsicIdentifier(env.callee, { name: 'GetEnvironment' })) throw new LiftError('Unresolved environment register');
					const [envIndex] = env.arguments;
					if (!t.isNumericLiteral(envIndex)) throw new LiftError('Unresolved environment register');

					if (!t.isNumericLiteral(slotIndex)) throw new LiftError('Unresolved environment slot index');

					let currentIndex = -1;
					let scope: Scope | undefined;
					while (currentIndex !== envIndex.value) {
						scope = (scope) ? scope.parent : call.scope;
						if (!scope) throw new LiftError('');

						if (scope.getData('environment') != null) {
							currentIndex++;
						}
					}

					const prefix = scope!.getData('environment');
					if (!prefix) throw new LiftError('');

					call.replaceWith(t.identifier(prefix + slotIndex.value));
				} else if (['StoreToEnvironment', 'StoreNPToEnvironment'].includes(call.node.callee.name)) {
					const [env, slotIndex, value] = call.node.arguments;
					if (!t.isCallExpression(env) || !t.isV8IntrinsicIdentifier(env.callee, { name: 'GetEnvironment' })) throw new LiftError('Unresolved environment register');
					const [envIndex] = env.arguments;
					if (!t.isNumericLiteral(envIndex)) throw new LiftError('Unresolved environment register');

					if (!t.isNumericLiteral(slotIndex)) throw new LiftError('Unresolved environment slot index');

					if (!t.isExpression(value)) throw new LiftError('');

					let currentIndex = -1;
					let scope: Scope | undefined;
					while (currentIndex !== envIndex.value) {
						scope = (scope) ? scope.parent : call.scope;
						if (!scope) throw new LiftError('');

						if (scope.getData('environment') != null) {
							currentIndex++;
						}
					}

					const prefix = scope!.getData('environment');
					if (!prefix) throw new LiftError('');

					call.replaceWith(t.assignmentExpression('=',
						t.identifier(prefix + slotIndex.value),
						value,
					));
				} else if (call.node.callee.name == 'CreateClosure') {
					const closureRef = call.get('arguments.0');
					const irFunc = inlineNestedFunctionRef(closureRef.node);
					if (!irFunc) return;

					call.replaceWith(irFunc.getFunctionExpr());
				} else if (call.node.callee.name == 'CreateGeneratorClosure') {
					const closureRef = call.get('arguments.0');
					const genIRClosure = inlineNestedFunctionRef(closureRef.node);
					if (genIRClosure == null) return;

					const genIRFunc = popNestedFunction(genIRClosure.analyseGeneratorClosure());
					if (!genIRFunc) {
						closureRef.replaceWith(genIRClosure.getFunctionExpr());
						return;
					}

					const genFunc = genIRFunc.getFunctionExpr();
					if (genIRClosure.name) {
						genFunc.id = t.identifier(genIRClosure.name);
					}
					call.replaceWith(genFunc);
				} else if (call.node.callee.name == 'CreateAsyncClosure') {
					const closureRef = call.get('arguments.0');
					const asyncIRClosure = inlineNestedFunctionRef(closureRef.node);
					if (!asyncIRClosure) return;

					const genIRClosure = popNestedFunction(asyncIRClosure.analyseAsyncClosure());
					if (!genIRClosure) {
						closureRef.replaceWith(asyncIRClosure.getFunctionExpr());
						return;
					}

					const innerGenIRFunc = popNestedFunction(genIRClosure.analyseGeneratorClosure());
					if (!innerGenIRFunc) {
						closureRef.replaceWith(genIRClosure.getFunctionExpr());
						return;
					}

					const asyncFunc = innerGenIRFunc.getFunctionExpr();
					asyncFunc.generator = false;
					asyncFunc.async = true;
					if (asyncIRClosure.name) {
						asyncFunc.id = t.identifier(asyncIRClosure.name);
					}
					call.replaceWith(asyncFunc)[0].traverse({
						Function(f) { f.skip() },
						YieldExpression(yieldExpr) {
							yieldExpr.replaceWith(
								t.awaitExpression(yieldExpr.node.argument!)
							);
						}
					});
				}
			}
		},
		VariableDeclaration(decn) {
			if (decn.node.kind != 'var') return;
			for (const decl of decn.get('declarations')) {
				if (!decl.node.extra?.isDeclaredGlobal) continue;
				const id = decl.node.id;
				if (!t.isIdentifier(id)) continue;

				const binding = decl.scope.getBinding(id.name);
				if (!binding) continue;

				declaredGlobals.set(id.name, binding);
			}
		},
		Identifier(id) {
			if (id.node.extra?.isReferencedGlobal) {
				referencedGlobals.add(id.node.name);
			}
		}
	});
	
	traverse(wrapped, {
		AssignmentExpression(assign) {
			const stmt = assign.parentPath;
			if (!stmt.isExpressionStatement()) return;
			if (assign.node.operator != '=') return;

			const left = assign.get('left');
			const right = assign.get('right');

			if (!left.isMemberExpression() || !left.get('object').isIdentifier({ name: 'global' })) return;
			const id = left.get('property');
			if (!id.isIdentifier()) return;
			const binding = declaredGlobals.get(id.node.name);
			if (binding?.scope != stmt.scope) return;
			if (right.isFunctionExpression()) {
				if (right.node.id && id.node.name != right.node.id.name) return;

				stmt.replaceWith(t.functionDeclaration(
					id.node,
					right.node.params,
					right.node.body,
					right.node.generator,
					right.node.async,
				));

				binding.path.remove();
			}
		},
		MemberExpression(memberExpr) {
			if (!memberExpr.get('object').isIdentifier({ name: 'global' }))	return;

			const id = memberExpr.get('property');
			if (!id.isIdentifier()) return;
			if (!declaredGlobals.has(id.node.name) && !referencedGlobals.has(id.node.name)) return;

			memberExpr.replaceWith(id.node);
		},
	});

	const ret = <t.Statement>fileBody.body.at(-1);
	if (t.isReturnStatement(ret) && ret.argument) {
		fileBody.body[fileBody.body.length - 1] = t.expressionStatement(
			ret.argument,
		);
	}

	console.log(
		generate(
			t.program(<t.Statement[]>fileBody.body)
		).code,
	);
}