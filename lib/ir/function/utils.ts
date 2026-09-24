import * as t from '@babel/types';
import { NodePath } from '@babel/traverse';
import generate from '@babel/generator';

function pathContains(ancestor: NodePath, descendant: NodePath): boolean {
	for (
		let path: NodePath | null = descendant;
		path;
		path = path.parentPath
	) {
		if (path === ancestor) return true;
	}
	return false;
}

export function crossesControlBoundary(
	declaration: NodePath,
	reference: NodePath,
) {
	for (let path = reference.parentPath; path; path = path.parentPath) {
		if (path.isConditionalExpression()) {
			if (pathContains(path.get('test'), reference)) continue;
			return true;
		}
		if (path.isLogicalExpression()) {
			if (pathContains(path.get('left'), reference)) continue;
			return true;
		}
		if (
			!path.isWhileStatement() &&
			!path.isDoWhileStatement() &&
			!path.isForStatement() &&
			!path.isForInStatement() &&
			!path.isForOfStatement() &&
			!path.isIfStatement() &&
			!path.isSwitchStatement() &&
			!path.isTryStatement()
		) {
			continue;
		}

		if (
			path.isIfStatement() &&
			pathContains(path.get('test'), reference)
		) continue;

		if (pathContains(path, declaration)) return false;
		return true;
	}

	return false;
}

export function isDuplicableScalarExpression(node: t.Expression): boolean {
	if (
		t.isIdentifier(node) ||
		t.isThisExpression(node) ||
		t.isSuper(node) ||
		t.isNullLiteral(node) ||
		t.isStringLiteral(node) ||
		t.isNumericLiteral(node) ||
		t.isBooleanLiteral(node) ||
		t.isBigIntLiteral(node)
	) {
		return true;
	}

	if (t.isUnaryExpression(node)) {
		return node.operator !== 'delete' &&
			isDuplicableScalarExpression(<t.Expression> node.argument);
	}

	if (t.isBinaryExpression(node) || t.isLogicalExpression(node)) {
		if (!t.isExpression(node.left)) return false;
		return isDuplicableScalarExpression(node.left) &&
			isDuplicableScalarExpression(<t.Expression> node.right);
	}

	if (t.isConditionalExpression(node)) {
		return isDuplicableScalarExpression(node.test) &&
			isDuplicableScalarExpression(node.consequent) &&
			isDuplicableScalarExpression(node.alternate);
	}

	return false;
}

export function isFreelyDuplicableInit(
	init: NodePath<t.Expression | null>,
) {
	if (!init.node) return false;
	if (init.node.extra?.isNonVolatile) return true;
	if (isDuplicableScalarExpression(init.node)) return true;
	if (!init.isPure()) return false;

	// Babel's purity means "no observable side effects", not "safe to clone".
	// Allocating expressions carry object identity, so duplicating them changes
	// subsequent property writes from one shared object into writes on fresh objects.
	if (
		init.isObjectExpression() ||
		init.isArrayExpression() ||
		init.isNewExpression() ||
		init.isFunctionExpression() ||
		init.isArrowFunctionExpression() ||
		init.isClassExpression() ||
		init.isRegExpLiteral()
	) {
		return false;
	}

	return true;
}

export function isCreateThisCall(
	path: NodePath<t.Expression | null>,
) {
	return path.node && path.isCallExpression() &&
		path.get('callee').isV8IntrinsicIdentifier({ name: 'CreateThis' });
}

export function isSelectObjectThisArgument(reference: NodePath) {
	const argumentList = reference.parentPath;
	if (!argumentList?.isCallExpression()) return false;
	if (
		!argumentList.get('callee').isV8IntrinsicIdentifier({
			name: 'SelectObject',
		})
	) return false;
	const [thisArg] = argumentList.get('arguments');
	return reference.node === thisArg.node;
}

export function createThisMatchesConstructor(
	createThis: NodePath,
	constructorName: string,
) {
	if (!createThis.isCallExpression()) return false;
	if (
		createThis.get('callee').isV8IntrinsicIdentifier({ name: 'CreateThis' })
	) {
		const args = createThis.get('arguments');
		if (args.length !== 2) return false;
		const [prototype, constructorArg] = args;
		if (!prototype.isMemberExpression()) return false;
		if (!prototype.get('object').isIdentifier({ name: constructorName })) {
			return false;
		}
		if (!prototype.get('property').isIdentifier({ name: 'prototype' })) {
			return false;
		}
		if (!constructorArg.isIdentifier({ name: constructorName })) {
			return false;
		}

		return true;
	}

	if (
		createThis.get('callee').isV8IntrinsicIdentifier({
			name: 'CreateThisForNew',
		})
	) {
		const constructorArg = createThis.get('arguments.0');
		if (!constructorArg.isIdentifier({ name: constructorName })) {
			return false;
		}

		return true;
	}

	return false;
}

export function expressionsEqual(left: t.Node, right: t.Node) {
	return generate(left).code === generate(right).code;
}

export function propertyExpressionFromName(name: string) {
	return /^[$A-Z_a-z][$\w]*$/.test(name)
		? { property: t.identifier(name), computed: false }
		: { property: t.stringLiteral(name), computed: true };
}

export function collectDeclaredNames(node: t.Node, names: Set<string>) {
	for (const name of Object.keys(t.getBindingIdentifiers(node))) {
		names.add(name);
	}
}

export function singleDeclarator(
	stmt: t.Statement | undefined,
	kind?: 'var' | 'let' | 'const',
): t.VariableDeclarator | null {
	if (!stmt || !t.isVariableDeclaration(stmt)) return null;
	if (kind && stmt.kind !== kind) return null;
	if (stmt.declarations.length !== 1) return null;
	return stmt.declarations[0];
}

export function identifierUseCount(nodes: t.Node[], name: string): number {
	let count = 0;
	for (const node of nodes) {
		t.traverseFast(node, (child) => {
			if (t.isIdentifier(child, { name })) count++;
		});
	}
	return count;
}

export function tryGetByIdCallCallee(
	func: t.Expression,
	receiver: t.Node,
): t.Expression | null {
	if (!t.isCallExpression(func)) return null;
	if (!t.isV8IntrinsicIdentifier(func.callee, { name: 'TryGetById' })) {
		return null;
	}
	if (func.arguments.length !== 2) return null;
	const [object, property] = func.arguments;
	if (!t.isExpression(object) || !t.isStringLiteral(property)) return null;

	if (t.isExpression(receiver) && expressionsEqual(object, receiver)) {
		const prop = propertyExpressionFromName(property.value);
		return t.memberExpression(
			t.cloneNode(object, true),
			prop.property,
			prop.computed,
		);
	}

	return null;
}

function objectCreatePrototypeConstructor(
	expr: t.CallExpression,
	constructorRef: t.Expression,
) {
	const callee = expr.callee;
	if (!t.isMemberExpression(callee, { computed: false })) return null;
	if (!t.isIdentifier(callee.object, { name: 'Object' })) return null;
	if (!t.isIdentifier(callee.property, { name: 'create' })) return null;
	if (expr.arguments.length !== 1) return null;

	const [prototype] = expr.arguments;
	if (!t.isMemberExpression(prototype, { computed: false })) return null;
	if (!t.isExpression(prototype.object)) return null;
	if (!t.isIdentifier(prototype.property, { name: 'prototype' })) return null;
	if (!expressionsEqual(prototype.object, constructorRef)) return null;

	return constructorRef;
}

/**
 * Whether `prototype` is the prototype belonging to `constructorRef`.
 *
 * `CreateThis` and `CreateThisForSuper` take the prototype object and the
 * constructor as separate operands, so the first argument is `Ctor.prototype`
 * rather than `Ctor`. Comparing it against the constructor directly never
 * matched what Hermes emits; the bare-equality case is kept for shapes that
 * had already been folded to the constructor itself.
 */
function isPrototypeOfConstructor(
	prototype: t.Expression,
	constructorRef: t.Expression,
): boolean {
	if (expressionsEqual(prototype, constructorRef)) return true;
	return t.isMemberExpression(prototype, { computed: false }) &&
		t.isIdentifier(prototype.property, { name: 'prototype' }) &&
		t.isExpression(prototype.object) &&
		expressionsEqual(prototype.object, constructorRef);
}

export function createThisMatchesConstructTarget(
	createThis: t.Node,
	constructorRef: t.Expression,
): t.Expression | null {
	if (!t.isCallExpression(createThis)) return null;
	if (t.isV8IntrinsicIdentifier(createThis.callee, { name: 'CreateThis' })) {
		const [prototype, newTarget] = createThis.arguments;
		if (!t.isExpression(prototype) || !t.isExpression(newTarget)) {
			return null;
		}
		if (!isPrototypeOfConstructor(prototype, constructorRef)) return null;
		return newTarget;
	}
	if (
		t.isV8IntrinsicIdentifier(createThis.callee, {
			name: 'CreateThisForNew',
		})
	) {
		const constructorArg = createThis.arguments[0];
		if (!t.isExpression(constructorArg)) return null;
		if (!expressionsEqual(constructorArg, constructorRef)) return null;

		return constructorArg;
	}
	if (
		t.isV8IntrinsicIdentifier(createThis.callee, {
			name: 'CreateThisForSuper',
		})
	) {
		const [prototype, newTarget] = createThis.arguments;
		if (!t.isExpression(prototype) || !t.isExpression(newTarget)) {
			return null;
		}
		if (!isPrototypeOfConstructor(prototype, constructorRef)) return null;
		return newTarget;
	}

	const objectCreateNewTarget = objectCreatePrototypeConstructor(
		createThis,
		constructorRef,
	);
	if (objectCreateNewTarget) return objectCreateNewTarget;

	return null;
}

export function isHermesEnsureObjectArgument(path: NodePath) {
	if (!path.isIdentifier()) return false;
	const parent = path.parentPath;
	if (!parent?.isCallExpression()) return false;
	if (!parent.node.arguments.includes(path.node)) return false;
	return t.isMemberExpression(parent.node.callee) &&
		t.isIdentifier(parent.node.callee.object, {
			name: 'HermesInternal',
		}) &&
		t.isIdentifier(parent.node.callee.property, {
			name: 'ensureObject',
		});
}

export function enclosingDerivedConstructor(path: NodePath) {
	const method = path.findParent((parent) =>
		parent.isClassMethod({ kind: 'constructor' })
	);
	if (!method?.isClassMethod()) return null;
	const klass = method.parentPath?.parentPath;
	if (!klass?.isClass() || !klass.node.superClass) return null;
	return method as NodePath<t.ClassMethod>;
}

export function objectGetPrototypeOfArgument(expr: t.Expression) {
	if (!t.isCallExpression(expr)) return null;
	const callee = expr.callee;
	if (!t.isMemberExpression(callee, { computed: false })) return null;
	if (!t.isIdentifier(callee.object, { name: 'Object' })) return null;
	if (!t.isIdentifier(callee.property, { name: 'getPrototypeOf' })) {
		return null;
	}
	const [arg] = expr.arguments;
	return t.isExpression(arg) ? arg : null;
}

export function callArgsFromArrayExpression(
	argsExpr: t.Expression,
): (t.Expression | t.SpreadElement)[] {
	if (t.isArrayExpression(argsExpr)) {
		return argsExpr.elements.flatMap((element) =>
			t.isExpression(element) || t.isSpreadElement(element)
				? [element]
				: []
		);
	}
	return [t.spreadElement(argsExpr)];
}

export function implicitConstructExpression(
	path: NodePath<t.CallExpression>,
	constructorRef: t.Expression,
	args: (t.Expression | t.SpreadElement)[],
	newTarget: t.Expression,
) {
	if (
		// enclosingDerivedConstructor(path) &&
		t.isMetaProperty(newTarget) &&
		t.isIdentifier(newTarget.meta, { name: 'new' }) &&
		t.isIdentifier(newTarget.property, { name: 'target' })
	) {
		return t.callExpression(t.super(), args);
	}

	const prototypeOf = objectGetPrototypeOfArgument(constructorRef);
	if (prototypeOf && expressionsEqual(prototypeOf, newTarget)) {
		return t.newExpression(t.cloneNode(newTarget, true), args);
	}

	if (expressionsEqual(constructorRef, newTarget)) {
		return t.newExpression(t.cloneNode(newTarget, true), args);
	}

	return null;
}
