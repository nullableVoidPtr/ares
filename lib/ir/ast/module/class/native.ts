import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import { getIRInstruction } from '../../mod.ts';

function isNewTarget(node: t.Node | null | undefined) {
	return t.isMetaProperty(node) &&
		t.isIdentifier(node.meta, { name: 'new' }) &&
		t.isIdentifier(node.property, { name: 'target' });
}

function sameIdentifier(
	left: t.Node | null | undefined,
	right: t.Node | null | undefined,
) {
	return t.isIdentifier(left) && t.isIdentifier(right, { name: left.name });
}

function callArgsFromArrayExpression(
	expr: t.Expression,
): (t.Expression | t.SpreadElement)[] {
	if (t.isArrayExpression(expr)) {
		return expr.elements.flatMap((element) =>
			t.isExpression(element) || t.isSpreadElement(element)
				? [element]
				: []
		);
	}
	return [t.spreadElement(expr)];
}

function replaceIdentifierUses(
	body: t.BlockStatement,
	name: string,
	replacement: t.Expression,
) {
	const wrapped = t.file(
		t.program([
			t.expressionStatement(t.functionExpression(null, [], body)),
		]),
	);
	traverse(wrapped, {
		Identifier(path) {
			if (path.node.name !== name) return;
			if (!path.isReferencedIdentifier()) return;
			path.replaceWith(t.cloneNode(replacement, true));
		},
	});
	traverse.cache.clear();
}

function removeUnusedConst(body: t.BlockStatement, name: string) {
	const used = new Set<string>();
	const wrapped = t.file(
		t.program([
			t.expressionStatement(t.functionExpression(null, [], body)),
		]),
	);
	traverse(wrapped, {
		Identifier(path) {
			if (path.node.name !== name) return;
			if (!path.isReferencedIdentifier()) return;
			used.add(name);
		},
	});
	traverse.cache.clear();
	if (used.has(name)) return;
	body.body = body.body.filter((stmt) => {
		if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
			return true;
		}
		const [decl] = stmt.declarations;
		return !t.isIdentifier(decl.id, { name });
	});
}

function stripEmptyThisInitializedGuard(body: t.BlockStatement) {
	body.body = body.body.filter((stmt) => {
		if (!t.isExpressionStatement(stmt)) return true;
		const expr = stmt.expression;
		if (!t.isCallExpression(expr)) return true;
		if (
			!t.isV8IntrinsicIdentifier(expr.callee, {
				name: 'ThrowIfThisInitialized',
			})
		) return true;
		const [arg] = expr.arguments;
		return !t.isIdentifier(arg, { name: '__hermes_empty__' });
	});
}

function isObjectCreateNewTargetPrototype(expr: t.Node | null | undefined) {
	if (!t.isCallExpression(expr)) return false;
	const callee = expr.callee;
	if (!t.isMemberExpression(callee, { computed: false })) return false;
	if (!t.isIdentifier(callee.object, { name: 'Object' })) return false;
	if (!t.isIdentifier(callee.property, { name: 'create' })) return false;
	const [prototype] = expr.arguments;
	if (!t.isMemberExpression(prototype, { computed: false })) return false;
	return isNewTarget(prototype.object) &&
		t.isIdentifier(prototype.property, { name: 'prototype' });
}

function classFieldKeyFromObjectProperty(
	property: t.ObjectProperty,
): { key: t.Expression; computed: boolean } | null {
	const key = property.key;
	if (t.isStringLiteral(key) && t.isValidIdentifier(key.value)) {
		return { key: t.identifier(key.value), computed: false };
	}
	if (!t.isExpression(key)) return null;
	return { key: t.cloneNode(key), computed: property.computed };
}

function fieldsFromObjectAssignSources(
	sources: (t.Expression | t.SpreadElement | t.ArgumentPlaceholder)[],
) {
	const fields: t.ClassProperty[] = [];
	for (const source of sources) {
		if (!t.isObjectExpression(source)) return null;
		for (const property of source.properties) {
			if (!t.isObjectProperty(property)) return null;
			if (!t.isExpression(property.value)) return null;
			const fieldKey = classFieldKeyFromObjectProperty(property);
			if (!fieldKey) return null;
			const { key, computed } = fieldKey;
			fields.push(t.classProperty(
				key,
				t.cloneNode(property.value, true),
				null,
				[],
				computed,
			));
		}
	}
	return fields;
}

export function cleanupBaseConstructorBody(body: t.BlockStatement) {
	const fields: t.ClassProperty[] = [];
	for (let i = 0; i < body.body.length; i++) {
		const stmt = body.body[i];
		if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
			continue;
		}
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id)) continue;
		const init = decl.init;
		if (!t.isCallExpression(init)) continue;

		if (isObjectCreateNewTargetPrototype(init)) {
			replaceIdentifierUses(body, decl.id.name, t.thisExpression());
			body.body.splice(i, 1);
			i--;
			continue;
		}

		const callee = init.callee;
		if (!t.isMemberExpression(callee, { computed: false })) continue;
		if (!t.isIdentifier(callee.object, { name: 'Object' })) continue;
		if (!t.isIdentifier(callee.property, { name: 'assign' })) continue;
		const [target, ...sources] = init.arguments;
		if (!isObjectCreateNewTargetPrototype(target)) continue;
		if (
			!sources.every((source) =>
				t.isExpression(source) || t.isSpreadElement(source)
			)
		) continue;

		const assignFields = fieldsFromObjectAssignSources(sources);
		replaceIdentifierUses(body, decl.id.name, t.thisExpression());
		if (
			assignFields &&
			getIRInstruction(init) == 'NewObjectWithBufferAndParent'
		) {
			fields.push(...assignFields);
			body.body.splice(i, 1);
			i--;
			continue;
		}

		const assign = t.callExpression(
			t.memberExpression(t.identifier('Object'), t.identifier('assign')),
			[
				t.thisExpression(),
				...sources.map((source) => t.cloneNode(source, true)),
			],
		);
		assign.extra = init.extra;
		body.body[i] = t.expressionStatement(assign);
		break;
	}

	for (let i = 0; i < body.body.length; i++) {
		const stmt = body.body[i];
		if (!t.isExpressionStatement(stmt)) continue;
		const expr = stmt.expression;
		if (!t.isCallExpression(expr)) continue;
		if (getIRInstruction(expr) != 'NewObjectWithBufferAndParent') continue;
		const callee = expr.callee;
		if (!t.isMemberExpression(callee, { computed: false })) continue;
		if (!t.isIdentifier(callee.object, { name: 'Object' })) continue;
		if (!t.isIdentifier(callee.property, { name: 'assign' })) continue;
		const [target, ...sources] = expr.arguments;
		if (!t.isThisExpression(target)) continue;
		const assignFields = fieldsFromObjectAssignSources(sources);
		if (!assignFields) continue;
		fields.push(...assignFields);
		body.body.splice(i, 1);
		i--;
	}

	body.body = body.body.filter((stmt) => {
		if (!t.isReturnStatement(stmt)) return true;
		if (t.isThisExpression(stmt.argument)) return false;
		return !isObjectCreateNewTargetPrototype(stmt.argument);
	});

	return fields;
}

export function cleanupDerivedConstructorBody(body: t.BlockStatement) {
	let superThisName: string | null = null;

	for (let i = 0; i < body.body.length; i++) {
		const stmt = body.body[i];
		if (!t.isReturnStatement(stmt)) continue;
		const ret = stmt.argument;
		if (
			!t.isCallExpression(ret) ||
			!t.isV8IntrinsicIdentifier(ret.callee, { name: 'SelectObject' })
		) continue;
		const [thisArg, ctorCall] = ret.arguments;
		if (!t.isIdentifier(thisArg)) continue;
		if (!t.isCallExpression(ctorCall)) continue;
		if (!t.isMemberExpression(ctorCall.callee, { computed: false })) {
			continue;
		}
		if (!t.isIdentifier(ctorCall.callee.property, { name: 'call' })) {
			continue;
		}
		if (!sameIdentifier(ctorCall.arguments[0], thisArg)) continue;
		const ctor = ctorCall.callee.object;
		if (!t.isIdentifier(ctor)) continue;

		const thisDeclIndex = body.body.findIndex((candidate) => {
			if (
				!t.isVariableDeclaration(candidate) ||
				candidate.declarations.length !== 1
			) return false;
			const [decl] = candidate.declarations;
			if (!t.isIdentifier(decl.id, { name: thisArg.name })) return false;
			const init = decl.init;
			if (
				!t.isCallExpression(init) ||
				!t.isV8IntrinsicIdentifier(init.callee, { name: 'CreateThis' })
			) return false;
			const [prototype, newTarget] = init.arguments;
			return sameIdentifier(prototype, ctor) && isNewTarget(newTarget);
		});
		if (thisDeclIndex === -1) continue;

		body.body.splice(thisDeclIndex, 1);
		body.body[i > thisDeclIndex ? i - 1 : i] = t.expressionStatement(
			t.callExpression(
				t.super(),
				ctorCall.arguments.slice(1).flatMap((arg) =>
					t.isExpression(arg) || t.isSpreadElement(arg) ? [arg] : []
				),
			),
		);
		removeUnusedConst(body, ctor.name);
		stripEmptyThisInitializedGuard(body);
		return;
	}

	for (let i = 0; i < body.body.length; i++) {
		const stmt = body.body[i];
		if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
			continue;
		}
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id)) continue;
		const init = decl.init;
		if (!t.isCallExpression(init)) continue;
		if (!t.isMemberExpression(init.callee, { computed: false })) continue;
		if (!t.isIdentifier(init.callee.object, { name: 'HermesInternal' })) {
			continue;
		}
		if (
			!t.isIdentifier(init.callee.property, {
				name: 'applyWithNewTarget',
			})
		) continue;
		const [target, args, thisValue, newTarget] = init.arguments;
		if (
			!t.isIdentifier(target) || !t.isExpression(args) ||
			!isNewTarget(newTarget)
		) continue;
		if (
			!t.isCallExpression(thisValue) ||
			!t.isV8IntrinsicIdentifier(thisValue.callee, {
				name: 'CreateThisForSuper',
			})
		) continue;
		const [prototype, thisNewTarget] = thisValue.arguments;
		if (!sameIdentifier(prototype, target) || !isNewTarget(thisNewTarget)) {
			continue;
		}

		superThisName = decl.id.name;
		body.body[i] = t.expressionStatement(t.callExpression(
			t.super(),
			callArgsFromArrayExpression(args),
		));
		replaceIdentifierUses(body, superThisName, t.thisExpression());
		removeUnusedConst(body, target.name);
		stripEmptyThisInitializedGuard(body);
		break;
	}

	body.body = body.body.filter((stmt) =>
		!(t.isReturnStatement(stmt) && t.isThisExpression(stmt.argument))
	);
}

function prototypeMemberAlias(
	init: t.Node | null | undefined,
	className: string,
) {
	if (!t.isMemberExpression(init, { computed: false })) return false;
	return t.isIdentifier(init.object, { name: className }) &&
		t.isIdentifier(init.property, { name: 'prototype' });
}

function classMethodKeyFromMember(member: t.MemberExpression) {
	if (t.isPrivateName(member.property)) return null;
	if (!member.computed && t.isIdentifier(member.property)) {
		return {
			key: t.cloneNode(member.property),
			computed: false,
		};
	}
	if (
		member.computed && t.isStringLiteral(member.property) &&
		t.isValidIdentifier(member.property.value)
	) {
		return {
			key: t.identifier(member.property.value),
			computed: false,
		};
	}
	if (!t.isExpression(member.property)) return null;
	return {
		key: t.cloneNode(member.property, true),
		computed: member.computed,
	};
}

function methodFromAssignment(
	assign: t.AssignmentExpression,
	className: string,
	prototypeAlias?: string,
) {
	if (assign.operator !== '=') return null;
	if (!t.isMemberExpression(assign.left)) return null;
	if (!t.isFunctionExpression(assign.right)) return null;

	let isStatic = false;
	if (
		prototypeAlias &&
		t.isIdentifier(assign.left.object, { name: prototypeAlias })
	) {
		isStatic = false;
	} else if (t.isIdentifier(assign.left.object, { name: className })) {
		isStatic = true;
	} else if (
		t.isMemberExpression(assign.left.object, { computed: false }) &&
		t.isIdentifier(assign.left.object.property, { name: 'prototype' }) &&
		t.isIdentifier(assign.left.object.object, { name: className })
	) {
		isStatic = false;
	} else {
		return null;
	}

	const key = classMethodKeyFromMember(assign.left);
	if (!key) return null;

	const method = t.classMethod(
		'method',
		key.key,
		assign.right.params,
		assign.right.body,
		key.computed,
		isStatic,
	);
	method.generator = assign.right.generator;
	method.async = assign.right.async;
	return method;
}

function replacePrototypeAliasUses(
	path: NodePath<t.VariableDeclaration>,
	aliasName: string,
	className: string,
) {
	const binding = path.scope.getBinding(aliasName);
	if (!binding?.constant) return false;

	for (const ref of binding.referencePaths) {
		ref.replaceWith(t.memberExpression(
			t.identifier(className),
			t.identifier('prototype'),
		));
	}
	binding.path.remove();
	return true;
}

function isReflectGetSuperExpr(
	node: t.Node,
): { property: t.Expression; computed: boolean } | null {
	if (!t.isCallExpression(node)) return null;
	const { callee, arguments: args } = node;
	if (!t.isMemberExpression(callee, { computed: false })) return null;
	if (
		!t.isIdentifier((callee as t.MemberExpression).object, {
			name: 'Reflect',
		})
	) return null;
	if (
		!t.isIdentifier((callee as t.MemberExpression).property, {
			name: 'get',
		})
	) return null;
	if (args.length !== 3) return null;
	const [obj, prop, receiver] = args;
	if (!t.isThisExpression(receiver) || !t.isExpression(prop)) return null;
	if (!t.isCallExpression(obj)) return null;
	const objCallee = (obj as t.CallExpression).callee;
	if (!t.isMemberExpression(objCallee, { computed: false })) return null;
	if (
		!t.isIdentifier((objCallee as t.MemberExpression).object, {
			name: 'Object',
		})
	) return null;
	if (
		!t.isIdentifier((objCallee as t.MemberExpression).property, {
			name: 'getPrototypeOf',
		})
	) return null;
	if (t.isStringLiteral(prop) && t.isValidIdentifier(prop.value)) {
		return { property: t.identifier(prop.value), computed: false };
	}
	return {
		property: t.cloneNode(prop, true) as t.Expression,
		computed: true,
	};
}

function isDerivedClassMethod(path: NodePath): boolean {
	const method = path.findParent((p) => p.isClassMethod());
	if (!method?.isClassMethod()) return false;
	const klass = method.parentPath?.parentPath;
	return !!(klass?.isClass() && klass.node.superClass);
}

function cleanupReflectGetSuperCall(call: NodePath<t.CallExpression>) {
	if (!call.isCallExpression()) return;
	const callee = call.get('callee');

	// Handle: Reflect.get(Object.getPrototypeOf(X), "prop", this).call(this, ...args)
	if (
		callee.isMemberExpression({ computed: false }) &&
		callee.get('property').isIdentifier({ name: 'call' })
	) {
		const inner = callee.get('object');
		if (!inner.isCallExpression()) return;
		const superMember = isReflectGetSuperExpr(inner.node);
		if (!superMember) return;
		const args = call.get('arguments');
		if (!args[0]?.isThisExpression()) return;
		if (!isDerivedClassMethod(call)) return;
		call.replaceWith(t.callExpression(
			t.memberExpression(
				t.super(),
				superMember.property,
				superMember.computed,
			),
			args.slice(1).map((a) => a.node as t.Expression | t.SpreadElement),
		));
		return;
	}

	// Handle: bare Reflect.get(Object.getPrototypeOf(X), "prop", this) not immediately .call()-ed
	const superMember = isReflectGetSuperExpr(call.node);
	if (!superMember) return;
	const parent = call.parentPath;
	if (
		parent?.isMemberExpression({ computed: false }) &&
		t.isIdentifier((parent.node as t.MemberExpression).property, {
			name: 'call',
		})
	) return;
	if (!isDerivedClassMethod(call)) return;
	call.replaceWith(
		t.memberExpression(
			t.super(),
			superMember.property,
			superMember.computed,
		),
	);
}

export function inlineAdjacentClassMethods(classPath: NodePath<t.Class>) {
	let className: string | undefined;
	let classStmt: NodePath | undefined;

	if (classPath.isClassDeclaration()) {
		const id = classPath.get('id');
		if (!id.isIdentifier()) return;
		className = id.node.name;
		classStmt = classPath;
	} else if (classPath.isClassExpression()) {
		const decl = classPath.parentPath;
		if (!decl?.isVariableDeclarator()) return;
		const id = decl.get('id');
		if (!id.isIdentifier()) return;
		const stmt = decl.parentPath;
		if (!stmt?.isVariableDeclaration()) return;
		className = id.node.name;
		classStmt = stmt;
	}

	if (!className || !classStmt) return;

	let stmt = classStmt.getNextSibling();

	let aliasStmt: NodePath<t.VariableDeclaration> | undefined;
	let aliasId: NodePath<t.Identifier> | undefined;
	if (stmt.isVariableDeclaration()) {
		aliasStmt = stmt;
		if (aliasStmt.node.declarations.length !== 1) return;

		const aliasDecl = aliasStmt.get('declarations.0');
		const id = aliasDecl.get('id');
		if (!id.isIdentifier()) return;
		aliasId = id;

		if (!prototypeMemberAlias(aliasDecl.node.init, className)) return;

		stmt = stmt.getNextSibling();
	}

	let inserted = false;
	while (stmt.isExpressionStatement()) {
		const expr = stmt.get('expression');
		if (!expr.isAssignmentExpression({ operator: '=' })) break;

		const method = methodFromAssignment(
			expr.node,
			className,
			aliasId?.node?.name,
		);
		if (!method) break;

		const body = classPath.get('body.body');
		const last = body.at(-1);
		const insertedMethod = last
			? last.insertAfter(method)[0]
			: classPath.get('body').unshiftContainer('body', method)[0];
		insertedMethod.traverse({
			CallExpression: cleanupReflectGetSuperCall,
		});

		const next = stmt.getNextSibling();
		stmt.remove();
		inserted = true;
		stmt = next;
	}

	if (!inserted) return;

	if (aliasStmt && aliasId) {
		replacePrototypeAliasUses(aliasStmt, aliasId.node.name, className);
	}
}
