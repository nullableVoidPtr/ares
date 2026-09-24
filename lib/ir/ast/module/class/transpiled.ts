import * as t from '@babel/types';
import { NodePath } from '@babel/traverse';
import { constIdentifierInit } from '../../utils.ts';

function extractCallWithExplicitThis(receiver: NodePath) {
	const parent = receiver.parentPath;
	if (!parent?.isMemberExpression({ computed: false })) return null;
	if (!parent.get('property').isIdentifier({ name: 'call' })) return null;

	const call = parent.parentPath;
	if (!call.isCallExpression()) return null;
	const args = call.get('arguments');
	if (!args[0].isThisExpression()) return null;

	return {
		target: call,
		arguments: args.slice(1),
	};
}

export function cleanupClassSuper(decl: NodePath<t.VariableDeclarator>) {
	const init = decl.get('init');
	if (!init.node?.extra?.isSuper) return;

	const superId = decl.get('id');
	if (!superId.isIdentifier()) return;

	const superBinding = decl.scope.getBinding(superId.node.name);
	if (
		!superBinding?.constant || superBinding.constantViolations.length !== 0
	) return;

	let missed = false;
	for (const superRef of superBinding.referencePaths) {
		let extracted = extractCallWithExplicitThis(superRef);
		if (extracted) {
			extracted.target.replaceWith(t.callExpression(
				t.super(),
				extracted.arguments.map((e) => e.node),
			));
			continue;
		}

		if (
			!superRef.parentPath?.isMemberExpression() ||
			superRef.key != 'object'
		) {
			missed = true;
			continue;
		}

		let callee = superRef.parentPath;
		if (
			callee.get('property').isIdentifier({ name: 'prototype' }) &&
			!callee.node.computed
		) {
			if (callee.parentPath.isMemberExpression()) {
				callee = callee.parentPath;
			}
		}

		const property = callee.get('property');
		extracted = extractCallWithExplicitThis(callee);
		if (extracted) {
			extracted.target.replaceWith(t.callExpression(
				t.memberExpression(
					t.super(),
					property.node,
					callee.node.computed,
				),
				extracted.arguments.map((e) => e.node),
			));
			continue;
		}

		missed = true;
	}

	if (!missed) {
		superBinding.path.remove();
	}
}

export function cleanupClassDefinitionClosure(
	call: NodePath<t.CallExpression>,
) {
	if (call.node.arguments.length !== 0) return;

	const func = call.get('callee');
	if (!func.isFunctionExpression()) return;

	let classExpr;
	for (const stmt of func.get('body').get('body')) {
		if (!stmt.isVariableDeclaration() || stmt.node.kind != 'const') {
			continue;
		}
		if (stmt.node.declarations.length !== 1) continue;

		const decn = stmt.get('declarations')[0];
		const id = decn.get('id');
		if (!id.isIdentifier()) continue;
		const klass = decn.get('init');
		if (!klass.isClass()) continue;

		if (stmt.getAllPrevSiblings().length !== 0) {
			// TODO
			continue;
		}
		const ret = stmt.getNextSibling();
		if (!ret.isReturnStatement()) continue;
		if (!ret.get('argument').isIdentifier({ name: id.node.name })) continue;

		classExpr = klass;
		break;
	}

	if (!classExpr) return;

	const classDecl = call.parentPath;
	if (classDecl.isVariableDeclarator()) {
		const origId = classDecl.get('id');
		const classDecn = classDecl.parentPath;
		if (
			origId.isIdentifier() && classDecn.isVariableDeclaration() &&
			classDecn.node.declarations.length === 1
		) {
			let className;
			const classId = classExpr.get('id');
			if (classId.isIdentifier()) {
				className = classId.node.name;
			}

			const binding = classDecn.scope.getBinding(origId.node.name);
			if (
				binding?.constant || binding?.constantViolations?.length === 0
			) {
				if (className && !classDecn.scope.hasBinding(className)) {
					classId.remove();
					classDecn.replaceWith(t.classDeclaration(
						t.identifier(className),
						classExpr.node.superClass,
						classExpr.node.body,
						classExpr.node.decorators,
					));
					classDecn.scope.rename(origId.node.name, className);
				}
			}
		}
	}

	call.replaceWith(classExpr.node);
}

function defineClass(call: NodePath<t.CallExpression>): boolean {
	const [klass, superClass] = call.get('arguments');
	let replaceTarget: NodePath | undefined;
	let constructorFunc: NodePath | undefined;
	if (klass.isIdentifier()) {
		replaceTarget = constructorFunc = constIdentifierInit(
			call.scope,
			klass.node.name,
		);
	} else if (klass.isFunctionExpression()) {
		replaceTarget = call;
		constructorFunc = klass;
	}

	if (
		!replaceTarget || !constructorFunc ||
		!constructorFunc.isFunctionExpression()
	) return false;

	call.scope.crawl();

	let actualSuperClass = null;
	if (!superClass.isNullLiteral()) {
		if (superClass.isIdentifier()) {
			const resolved = constIdentifierInit(
				call.scope,
				superClass.node.name,
			);
			if (resolved) {
				const binding = call.scope.getBinding(superClass.node.name);
				if (binding?.constant && binding.references === 2) {
					for (const ref of binding.referencePaths) {
						if (ref == superClass) continue;
						ref.replaceWith(t.cloneNode(resolved.node, true))[0]
							.node.extra = { isSuper: true };
					}
					binding.path.remove();
					actualSuperClass = resolved.node;
				}
			}
		}
	}

	if (replaceTarget != call) call.remove();
	replaceTarget.replaceWith(t.classExpression(
		constructorFunc.node.id,
		actualSuperClass,
		t.classBody([
			t.classMethod(
				'constructor',
				t.identifier('constructor'),
				constructorFunc.node.params,
				constructorFunc.node.body,
			),
		]),
	));

	return true;
}

function defineClassMethod(
	call: NodePath<t.CallExpression>,
	options?: Partial<{ kind: t.ClassMethod['kind']; static: boolean }>,
): boolean {
	const [klass, id, func] = call.get('arguments');

	let classExpr: NodePath<t.Class> | undefined;
	if (klass.isIdentifier()) {
		const init = constIdentifierInit(call.scope, klass.node.name);
		if (!init?.isClass()) return false;
		classExpr = init;
	}

	if (!classExpr) return false;

	if (!id.isStringLiteral()) return false;

	if (!func.isFunctionExpression()) return false;

	classExpr.get('body').get('body').at(-1)!.insertAfter(t.classMethod(
		options?.kind ?? 'method',
		t.isValidIdentifier(id.node.value)
			? t.identifier(id.node.value)
			: id.node,
		func.node.params,
		func.node.body,
		false,
		options?.static ?? false,
	));

	call.remove();

	return true;
}

export function liftHermesES6Class(call: NodePath<t.CallExpression>): boolean {
	const callee = call.get('callee');
	if (!callee.isMemberExpression({ computed: false })) return false;
	if (!callee.get('object').isIdentifier({ name: 'HermesES6Internal' })) {
		return false;
	}

	const property = callee.get('property');
	if (!property.isIdentifier()) return false;

	if (property.node.name == 'defineClass') {
		return defineClass(call);
	} else if (property.node.name == 'defineClassMethod') {
		return defineClassMethod(call);
	} else if (property.node.name == 'defineStaticClassMethod') {
		return defineClassMethod(call, { static: true });
	} else if (property.node.name == 'defineClassPropertyGetter') {
		return defineClassMethod(call, { kind: 'get' });
	} else if (property.node.name == 'defineClassPropertySetter') {
		return defineClassMethod(call, { kind: 'set' });
	} else if (property.node.name == 'defineStaticClassPropertyGetter') {
		return defineClassMethod(call, { kind: 'get', static: true });
	} else if (property.node.name == 'defineStaticClassPropertySetter') {
		return defineClassMethod(call, { kind: 'set', static: true });
	}

	return false;
}
