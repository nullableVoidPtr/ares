import { env } from 'node:process';
import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import type { LiftedAST, LiftedExtra } from './mod.ts';
import {
	comparableAst,
	constIdentifierInit,
	extractRegisterAssign,
	isUndefinedNode,
	nodePathIsAttached,
} from './utils.ts';
import { SerializedLiteralValue } from '../../parser/file.ts';

let DEBUG_INLINE_OBJ = false;
try {
	DEBUG_INLINE_OBJ = env['ARES_DEBUG_INLINE_OBJ'] === '1';
} catch { /**/ }
function debugInlineObj(...args: unknown[]) {
	if (DEBUG_INLINE_OBJ) console.error('[inline-obj]', ...args);
}

/** Lift Hermes' variadic string concatenation helper into a template literal. */
export function liftHermesConcatCall(
	call: NodePath<t.CallExpression>,
): boolean {
	const callee = call.get('callee');
	if (!callee.matchesPattern('HermesInternal.concat.call')) return false;

	const quasis: t.TemplateElement[] = [];
	const expressions: t.Expression[] = [];
	let cooked = '';
	for (const argument of call.node.arguments) {
		if (t.isStringLiteral(argument)) {
			cooked += argument.value;
			continue;
		}
		if (!t.isExpression(argument)) return false;
		const raw = cooked
			.replace(/\\/g, '\\\\')
			.replace(/`/g, '\\`')
			.replace(/\$\{/g, '\\${');
		quasis.push(t.templateElement({ raw, cooked }, false));
		expressions.push(argument);
		cooked = '';
	}
	const raw = cooked
		.replace(/\\/g, '\\\\')
		.replace(/`/g, '\\`')
		.replace(/\$\{/g, '\\${');
	quasis.push(t.templateElement({ raw, cooked }, true));
	call.replaceWith(t.templateLiteral(quasis, expressions));
	return true;
}

/** Lift every concat helper exposed by late sequence and alias cleanup. */
export function liftHermesConcatCalls(file: t.File): number {
	let lifted = 0;
	traverse(file, {
		CallExpression: {
			exit(path) {
				if (liftHermesConcatCall(path)) lifted++;
			},
		},
	});
	return lifted;
}

function receiverMatchesApplyTarget(
	call: NodePath<t.CallExpression>,
	target: t.Expression,
	thisValue: t.Node,
): boolean {
	let resolvedTarget: t.Expression | undefined = target;
	if (t.isIdentifier(target)) {
		resolvedTarget = constIdentifierInit(call.scope, target.name)?.node;
	}
	if (!t.isMemberExpression(resolvedTarget)) return false;

	const receiver = resolvedTarget.object;
	if (t.isIdentifier(receiver)) {
		return t.isIdentifier(thisValue, { name: receiver.name });
	}
	return t.isThisExpression(receiver) && t.isThisExpression(thisValue);
}

/** Lift Hermes' dense-array apply helper without changing receiver identity. */
export function liftHermesApplyCall(
	call: NodePath<t.CallExpression>,
): boolean {
	const callee = call.get('callee');
	if (!callee.matchesPattern('HermesInternal.apply')) return false;
	const args = call.node.arguments;
	if (args.length !== 2 && args.length !== 3) return false;
	const [target, innerArgsArray, thisValue] = args;
	if (!t.isExpression(target) || !t.isArrayExpression(innerArgsArray)) {
		return false;
	}

	const innerArgs: (t.Expression | t.SpreadElement)[] = [];
	for (const element of innerArgsArray.elements) {
		if (!t.isExpression(element) && !t.isSpreadElement(element)) {
			return false;
		}
		innerArgs.push(element);
	}

	if (args.length === 2) {
		call.replaceWith(t.newExpression(target, innerArgs));
		return true;
	}
	// IRGen emits this form for source spread calls, not for `Reflect.apply`.
	// Require the callee/receiver relationship before recovering that source
	// call rather than replacing unrelated intrinsic-shaped input.
	if (!isUndefinedNode(thisValue)) {
		if (!receiverMatchesApplyTarget(call, target, thisValue)) return false;
		if (!t.isMemberExpression(target)) {
			call.replaceWith(t.callExpression(
				t.memberExpression(target, t.identifier('call')),
				[thisValue, ...innerArgs],
			));
			return true;
		}
	}

	call.replaceWith(t.callExpression(target, innerArgs));
	return true;
}

function liftHermesApplyArgumentsCall(
	call: NodePath<t.CallExpression>,
): boolean {
	const callee = call.get('callee');
	if (
		!callee.matchesPattern('HermesInternal.applyArguments') &&
		!callee.matchesPattern('HermesInternal.applyWithArguments')
	) return false;
	const args = call.node.arguments;
	if (args.length !== 2 && args.length !== 3) return false;
	const [target, thisValue, newTarget] = args;
	if (!t.isExpression(target) || !t.isExpression(thisValue)) return false;

	if (newTarget && !isUndefinedNode(newTarget)) {
		if (
			!t.isExpression(newTarget) ||
			!t.isIdentifier(target) ||
			!t.isCallExpression(thisValue) ||
			!t.isV8IntrinsicIdentifier(thisValue.callee, {
				name: 'CreateThisForSuper',
			})
		) return false;
		const [prototype, thisNewTarget] = thisValue.arguments;
		if (
			!t.isIdentifier(prototype, { name: target.name }) ||
			!t.isNodesEquivalent(thisNewTarget, newTarget)
		) return false;
		call.replaceWith(t.callExpression(
			t.memberExpression(
				t.identifier('Reflect'),
				t.identifier('construct'),
			),
			[target, t.identifier('arguments'), newTarget],
		));
		return true;
	}

	const forwardedArguments = t.spreadElement(t.identifier('arguments'));
	if (
		isUndefinedNode(thisValue) ||
		(t.isMemberExpression(target) &&
			receiverMatchesApplyTarget(call, target, thisValue))
	) {
		call.replaceWith(t.callExpression(target, [forwardedArguments]));
	} else {
		call.replaceWith(t.callExpression(
			t.memberExpression(target, t.identifier('call')),
			[thisValue, forwardedArguments],
		));
	}
	return true;
}

function liftHermesApplyWithNewTargetCall(
	call: NodePath<t.CallExpression>,
): boolean {
	const callee = call.get('callee');
	if (!callee.matchesPattern('HermesInternal.applyWithNewTarget')) {
		return false;
	}
	const [target, innerArgsArray, thisValue, newTarget] = call.node.arguments;
	if (
		call.node.arguments.length !== 4 ||
		!t.isIdentifier(target) ||
		!t.isExpression(innerArgsArray) ||
		!t.isCallExpression(thisValue) ||
		!t.isExpression(newTarget) ||
		!t.isV8IntrinsicIdentifier(thisValue.callee, {
			name: 'CreateThisForSuper',
		})
	) return false;
	const [prototype, thisNewTarget] = thisValue.arguments;
	if (
		!t.isIdentifier(prototype, { name: target.name }) ||
		!t.isNodesEquivalent(thisNewTarget, newTarget)
	) return false;

	call.replaceWith(t.callExpression(
		t.memberExpression(
			t.identifier('Reflect'),
			t.identifier('construct'),
		),
		[target, innerArgsArray, newTarget],
	));
	return true;
}

/** Lift apply-family helpers exposed only after whole-file composition. */
export function liftHermesApplyCalls(file: t.File): number {
	let lifted = 0;
	traverse(file, {
		CallExpression: {
			exit(path) {
				if (
					liftHermesApplyCall(path) ||
					liftHermesApplyArgumentsCall(path) ||
					liftHermesApplyWithNewTargetCall(path)
				) lifted++;
			},
		},
	});
	return lifted;
}

/**
 * Lift Hermes' template-object helper and its tag call into a tagged template.
 *
 * `ESTreeIRGen::genTaggedTemplateExpr` lowers ``tag`a${x}b` `` to
 * `tag(%getTemplateObject(id, dup, ...raw, ...cooked), x)`, then calls the tag
 * with the template object followed by the substitutions in source order.
 * `dup` reports that every cooked string equals its raw string, in which case
 * the cooked list is omitted entirely; a quasi with no cooked value (an
 * invalid escape) is passed as `undefined`.
 *
 * The raw strings are the source text between the delimiters, so they carry
 * their own escapes and go into the template element verbatim: an unescaped
 * backtick or `${` could not have appeared there without ending the quasi.
 */
export function liftHermesTaggedTemplateCall(
	call: NodePath<t.CallExpression>,
): boolean {
	let tag = call.node.callee;
	let callArguments = call.node.arguments;
	// IRGen passes an `undefined` receiver exactly when the tag is not a member
	// expression, so an unfolded `.call` says nothing about the tag itself.
	if (
		t.isMemberExpression(tag) && !tag.computed &&
		t.isIdentifier(tag.property, { name: 'call' }) &&
		isUndefinedNode(callArguments[0])
	) {
		tag = tag.object;
		callArguments = callArguments.slice(1);
	}
	if (!t.isExpression(tag)) return false;

	const [templateObject, ...substitutions] = callArguments;
	if (!t.isCallExpression(templateObject)) return false;
	if (
		!t.matchesPattern(templateObject.callee, [
			'HermesInternal',
			'getTemplateObject',
		])
	) return false;
	const [id, dup, ...strings] = templateObject.arguments;
	if (!t.isNumericLiteral(id) || !t.isBooleanLiteral(dup)) return false;
	const count = dup.value ? strings.length : strings.length / 2;
	if (!Number.isInteger(count) || count !== substitutions.length + 1) {
		return false;
	}
	if (
		!substitutions.every((substitution): substitution is t.Expression =>
			t.isExpression(substitution)
		)
	) return false;

	const quasis: t.TemplateElement[] = [];
	for (let index = 0; index < count; index++) {
		const raw = strings[index];
		const cooked = dup.value ? raw : strings[count + index];
		if (!t.isStringLiteral(raw)) return false;
		const tail = index === count - 1;
		if (t.isStringLiteral(cooked)) {
			quasis.push(
				t.templateElement(
					{ raw: raw.value, cooked: cooked.value },
					tail,
				),
			);
		} else if (isUndefinedNode(cooked)) {
			quasis.push(t.templateElement({ raw: raw.value }, tail));
		} else return false;
	}

	call.replaceWith(
		t.taggedTemplateExpression(
			tag,
			t.templateLiteral(quasis, substitutions),
		),
	);
	return true;
}

/** Lift every tagged template exposed by late sequence and alias cleanup. */
export function liftHermesTaggedTemplateCalls(file: t.File): number {
	let lifted = 0;
	traverse(file, {
		CallExpression: {
			exit(path) {
				if (liftHermesTaggedTemplateCall(path)) lifted++;
			},
		},
	});
	return lifted;
}

function isToNumericCall(
	node: t.Node | null | undefined,
): node is t.CallExpression {
	return t.isCallExpression(node) &&
		t.isV8IntrinsicIdentifier(node.callee, { name: 'ToNumeric' }) &&
		node.arguments.length === 1;
}

function isNumericOne(node: t.Node | null | undefined) {
	return t.isNumericLiteral(node, { value: 1 });
}

function updateOperatorForNumericDelta(expr: t.Expression) {
	if (!t.isBinaryExpression(expr)) return;
	if (!isNumericOne(expr.right)) return;
	if (expr.operator === '+') return '++';
	if (expr.operator === '-') return '--';
}

function toNumericUpdateTarget(init: t.Expression): t.Expression | undefined {
	if (!isToNumericCall(init)) return;
	const [arg] = init.arguments;
	if (t.isArgumentPlaceholder(arg) || t.isSpreadElement(arg)) return;

	return arg;
}

function isSameLVal(
	left: t.OptionalMemberExpression | t.LVal | undefined,
	right: t.Expression | undefined,
) {
	if (!left || !right) return false;

	if (t.isIdentifier(left)) {
		return t.isIdentifier(right, { name: left.name });
	} else if (t.isIdentifier(right)) {
		return false;
	}

	if (t.isMemberExpression(left)) {
		if (!t.isMemberExpression(right)) return false;
		// `a.b` and `a["b"]` reach the same property but are not the same
		// node; comparing the property alone would treat `a[b]` as `a.b`.
		if (left.computed !== right.computed) return false;

		// The object may be `this`, which is the same object on both sides but
		// is not an LVal. Requiring one here declined every `this.x++`, which
		// is the commonest shape this recogniser meets.
		if (t.isThisExpression(left.object)) {
			if (!t.isThisExpression(right.object)) return false;
		} else if (
			!t.isLVal(left.object) || !t.isLVal(right.object) ||
			!isSameLVal(left.object, right.object)
		) return false;

		if (t.isIdentifier(left.property)) {
			if (!t.isIdentifier(right.property)) return false;
			return left.property.name === right.property.name;
		}
	} else if (t.isMemberExpression(right)) {
		return false;
	}

	return false;
}

export function assignmentUpdateExpression(
	assign: t.AssignmentExpression,
): t.UpdateExpression | undefined {
	if (assign.operator !== '=') return;
	if (
		!t.isExpression(assign.left) ||
		t.isOptionalMemberExpression(assign.left)
	) return;
	if (!t.isStandardized(assign.left)) return;
	if (!t.isBinaryExpression(assign.right)) return;
	const operator = updateOperatorForNumericDelta(assign.right);
	if (!operator) return;

	if (
		!isSameLVal(
			assign.left,
			toNumericUpdateTarget(assign.right.left as t.Expression),
		)
	) return;

	return t.updateExpression(operator, t.cloneNode(assign.left), false);
}

export function postfixUpdateFromToNumericTemp(
	decn: NodePath<t.VariableDeclaration>,
) {
	const assign = extractRegisterAssign(decn);
	if (!assign) return false;

	const { id, init } = assign;
	const target = toNumericUpdateTarget(init.node);
	if (!target) return false;
	if (!t.isLVal(target)) return false;
	if (!t.isStandardized(target)) return false;

	const next = decn.getNextSibling();
	if (!next.isExpressionStatement()) return false;
	const expr = next.get('expression');
	if (!expr.isAssignmentExpression({ operator: '=' })) return false;
	const left = expr.get('left');
	if (!isSameLVal(left.node, target)) return false;
	const right = expr.get('right');
	if (!right.get('left').isIdentifier({ name: id.node.name })) return false;

	const operator = updateOperatorForNumericDelta(right.node);
	if (!operator) return false;

	init.replaceWith(t.updateExpression(operator, t.cloneNode(target), false));
	next.remove();
	return true;
}

const BINARY_TO_COMPOUND: Partial<
	Record<
		t.BinaryExpression['operator'],
		t.AssignmentExpression['operator']
	>
> = {
	'+': '+=',
	'-': '-=',
	'*': '*=',
	'/': '/=',
	'%': '%=',
	'&': '&=',
	'|': '|=',
	'^': '^=',
	'<<': '<<=',
	'>>': '>>=',
	'>>>': '>>>=',
	'**': '**=',
};

function isCompoundLhs(expr: t.Expression | t.LVal | t.Super): boolean {
	if (t.isIdentifier(expr)) return true;
	if (t.isSuper(expr)) return true;
	if (t.isMemberExpression(expr)) {
		return isCompoundLhs(expr.object) &&
			(!expr.computed || isCompoundLhs(expr.property as t.Expression));
	}
	return false;
}

export function toCompoundAssignment(
	assign: t.AssignmentExpression,
): t.AssignmentExpression | undefined {
	if (assign.operator !== '=') return;
	if (!t.isBinaryExpression(assign.right)) return;
	const op = BINARY_TO_COMPOUND[assign.right.operator];
	if (!op) return;
	if (!isCompoundLhs(assign.left)) return;
	// Compound assignment is only valid when the binary expression reads the
	// exact l-value it writes.  `comparableAst` deliberately alpha-normalises all
	// generated SSA identifiers, so using it here made unrelated registers such
	// as `r0_4` and `r2_2` compare equal and changed
	// `r0_4 = r2_2 - 1` into the uninitialised `r0_4 -= 1`.
	if (
		!isSameLVal(
			assign.left,
			assign.right.left as t.Expression,
		)
	) return;
	return t.assignmentExpression(
		op,
		t.cloneNode(assign.left as t.LVal, true),
		t.cloneNode(assign.right.right as t.Expression, true),
	);
}

function extractGetterSetterDefine(
	expr: NodePath<t.Expression>,
	targetName?: string,
) {
	if (!expr.isCallExpression()) return;
	if (!expr.get('callee').matchesPattern('Object.defineProperty')) return;

	const args = expr.get('arguments');
	if (args.length !== 3) return;

	const [target, name, options] = args;
	if (targetName) {
		if (!target.isIdentifier({ name: targetName })) return;
	}

	if (!name.isStringLiteral()) return;
	if (!options.isObjectExpression()) return;

	let getter, setter: t.Expression | undefined;
	let enumerable = false;

	function isCreateClosure(value: NodePath) {
		if (!value.isCallExpression()) return false;
		const callee = value.get('callee');
		if (!callee.isV8IntrinsicIdentifier()) return false;
		if (
			!['CreateClosure', 'CreateGeneratorClosure', 'CreateAsyncClosure']
				.includes(callee.node.name)
		) return false;

		return true;
	}

	for (const prop of options.get('properties')) {
		let id;
		let value;
		if (prop.isObjectProperty()) {
			const key = prop.get('key');
			if (!prop.node.computed && key.isIdentifier()) {
				id = key.node.name;
			} else if (key.isStringLiteral()) {
				id = key.node.value;
			}
			const path = prop.get('value');
			if (!path.isExpression()) continue;
			value = path;
		} else {
			continue;
		}

		if (id == 'get') {
			if (isCreateClosure(value)) {
				getter = value.node;
			}
		} else if (id == 'set') {
			if (isCreateClosure(value)) {
				setter = value.node;
			}
		} else if (id == 'enumerable') {
			const evaluation = value.evaluateTruthy();
			if (typeof evaluation !== 'undefined') {
				enumerable = evaluation;
			}
		}
	}

	return {
		target,
		name: name.node.value,
		getter,
		setter,
		enumerable,
	};
}

// Running write position into the array being built. While no dynamic-length spread has
// happened the position is a numeric literal (`base === null`); after a spread captures the
// new length in a register the position is tracked symbolically as `base + delta`.
type ArrayOffset = { base: string | null; delta: number };

function arrayOffsetMatches(
	offset: ArrayOffset,
	index: t.Node | null | undefined,
): boolean {
	if (!index) return false;
	if (offset.base === null) {
		return t.isNumericLiteral(index, { value: offset.delta });
	}
	let delta = 0;
	let base: t.Node = index;
	while (
		t.isBinaryExpression(base, { operator: '+' }) &&
		t.isNumericLiteral(base.right)
	) {
		delta += base.right.value;
		base = base.left;
	}
	return t.isIdentifier(base, { name: offset.base }) &&
		delta === offset.delta;
}

// HermesInternal.arraySpread(arr, iter, <startIndex>) — returns the spread iterables (one,
// or several when the start-index position is itself a nested arraySpread, as Hermes emits
// for adjacent spreads like `[...a, ...b]`) plus the innermost start-index node for the
// caller to validate against the running ArrayOffset. Iterables are ordered first-executed
// (innermost) to last.
function matchArraySpreadCall(
	callPath: NodePath,
	arrName: string,
): {
	iterables: t.Expression[];
	startIndex: t.Node;
	refs: NodePath<t.Identifier>[];
} | null {
	if (!callPath.isCallExpression()) return null;
	const callee = callPath.get('callee') as NodePath;
	if (!callee.isMemberExpression()) return null;
	if (!callee.get('object').isIdentifier({ name: 'HermesInternal' })) {
		return null;
	}
	if (!callee.get('property').isIdentifier({ name: 'arraySpread' })) {
		return null;
	}
	const args = callPath.get('arguments') as NodePath[];
	if (args.length !== 3) return null;
	if (!args[0].isIdentifier({ name: arrName })) return null;
	if (!t.isExpression(args[1].node)) return null;

	const arrayRef = args[0] as NodePath<t.Identifier>;
	const iterable = args[1].node as t.Expression;
	const startPath = args[2];

	// Nested: arraySpread(arr, iter, arraySpread(arr, innerIter, …)) — inner runs first.
	if (startPath.isCallExpression()) {
		const inner = matchArraySpreadCall(startPath, arrName);
		if (inner) {
			return {
				iterables: [...inner.iterables, iterable],
				startIndex: inner.startIndex,
				refs: [...inner.refs, arrayRef],
			};
		}
	}

	return {
		iterables: [iterable],
		startIndex: startPath.node as t.Node,
		refs: [arrayRef],
	};
}

interface ArraySpreadSegment {
	iterables: t.Expression[];
	startIndex: t.Node;
	// When the post-spread offset is captured (`const off = arraySpread(…)`), the spread is
	// non-terminal: subsequent elements/spreads are tracked relative to `offsetVar`. Bare and
	// embedded spreads don't expose the new offset, so they terminate collection.
	offsetVar: string | null;
	// Embedded form `arr[arraySpread(arr, iter, n)] = v` lands `v` right after the spread.
	trailingValue: t.Expression | null;
	refs: NodePath<t.Identifier>[];
}
function analyseArraySpreadExpression(
	expr: NodePath<t.Expression>,
	arrName: string,
	captureOffset: boolean,
): ArraySpreadSegment | null {
	if (expr.isAssignmentExpression({ operator: '=' })) {
		const left = expr.get('left');

		// offset = HermesInternal.arraySpread(arr, iter, idx)
		if (
			captureOffset &&
			left.isIdentifier() &&
			/^r\d+_\d+$/.test(left.node.name)
		) {
			const matched = matchArraySpreadCall(expr.get('right'), arrName);
			if (matched) {
				return {
					iterables: matched.iterables,
					startIndex: matched.startIndex,
					offsetVar: left.node.name,
					trailingValue: null,
					refs: matched.refs,
				};
			}
		}

		// arr[HermesInternal.arraySpread(arr, iter, idx)] = val
		if (
			left.isMemberExpression({ computed: true }) &&
			left.get('object').isIdentifier({ name: arrName })
		) {
			const matched = matchArraySpreadCall(
				left.get('property') as NodePath,
				arrName,
			);
			const value = expr.get('right');
			if (matched && t.isExpression(value.node)) {
				return {
					iterables: matched.iterables,
					startIndex: matched.startIndex,
					offsetVar: null,
					trailingValue: value.node,
					refs: [
						left.get('object') as NodePath<t.Identifier>,
						...matched.refs,
					],
				};
			}
		}
	}

	// HermesInternal.arraySpread(arr, iter, idx) [return value discarded]
	const matched = matchArraySpreadCall(expr, arrName);
	if (!matched) return null;
	return {
		iterables: matched.iterables,
		startIndex: matched.startIndex,
		offsetVar: null,
		trailingValue: null,
		refs: matched.refs,
	};
}

function analyseArraySpreadStatement(
	stmt: NodePath,
	arrName: string,
): ArraySpreadSegment | null {
	// const off = HermesInternal.arraySpread(arr, iter, idx)
	if (stmt.isVariableDeclaration({ kind: 'const' })) {
		const decls = stmt.get('declarations') as NodePath<
			t.VariableDeclarator
		>[];
		if (decls.length !== 1) return null;
		const idPath = decls[0].get('id');
		if (!idPath.isIdentifier()) return null;
		const matched = matchArraySpreadCall(
			decls[0].get('init') as NodePath,
			arrName,
		);
		if (!matched) return null;
		return {
			iterables: matched.iterables,
			startIndex: matched.startIndex,
			offsetVar: (idPath.node as t.Identifier).name,
			trailingValue: null,
			refs: matched.refs,
		};
	}

	if (!stmt.isExpressionStatement()) return null;
	return analyseArraySpreadExpression(
		stmt.get('expression') as NodePath<t.Expression>,
		arrName,
		false,
	);
}
interface AdjacentArraySpreadAlias {
	declaration: NodePath<t.VariableDeclaration>;
	init: t.Expression;
	name: string;
}

function analyseAdjacentArraySpreadAlias(
	current: NodePath<t.Node | null>,
	targetName: string,
	offset: ArrayOffset,
): AdjacentArraySpreadAlias | null {
	if (!current.isVariableDeclaration({ kind: 'const' })) return null;
	const declarations = current.get('declarations');
	if (declarations.length !== 1) return null;
	const declarator = declarations[0];
	const id = declarator.get('id');
	const init = declarator.get('init');
	if (
		!id.isIdentifier() || !init.node || !t.isExpression(init.node) ||
		generatedIdentifierUseCount(init.node, targetName) > 0
	) return null;

	const binding = current.scope.getBinding(id.node.name);
	if (
		!binding?.constant || binding.path !== declarator ||
		binding.referencePaths.length !== 1
	) return null;
	const reference = binding.referencePaths[0];
	if (!nodePathIsAttached(reference)) return null;

	const next = current.getNextSibling();
	if (!next.node || !next.isStandardized()) return null;
	const spread = analyseArraySpreadStatement(next, targetName);
	if (
		!spread || !arrayOffsetMatches(offset, spread.startIndex) ||
		!spread.iterables.some((iterable) => iterable === reference.node)
	) return null;

	return {
		declaration: current,
		init: init.node,
		name: id.node.name,
	};
}
function isAdjacentArraySpreadSetupDeclaration(
	current: NodePath<t.Node | null>,
	targetName: string,
	offset: ArrayOffset,
): boolean {
	if (!current.isVariableDeclaration({ kind: 'const' })) return false;
	const declarations = current.get('declarations');
	if (declarations.length !== 1) return false;
	const declarator = declarations[0];
	const id = declarator.get('id');
	const init = declarator.get('init');
	if (
		!id.isIdentifier() || !/^r\d+_\d+$/.test(id.node.name) ||
		!init.node || !t.isExpression(init.node) ||
		generatedIdentifierUseCount(init.node, targetName) > 0
	) return false;

	const binding = current.scope.getBinding(id.node.name);
	if (
		!binding?.constant || binding.path !== declarator ||
		binding.referencePaths.length < 2
	) return false;

	const next = current.getNextSibling();
	if (!next.node || !next.isStandardized()) return false;
	const spread = analyseArraySpreadStatement(next, targetName);
	if (!spread || !arrayOffsetMatches(offset, spread.startIndex)) return false;
	const iterableNodes = new Set<t.Node>(spread.iterables);
	return binding.referencePaths.every((reference) =>
		nodePathIsAttached(reference) &&
		nodePathIsWithinAny(reference, iterableNodes)
	);
}

function analyseObjectAssign(stmt: NodePath, targetName: string) {
	if (!stmt.isExpressionStatement()) return null;
	const expr = stmt.get('expression');
	if (!expr.isAssignmentExpression({ operator: '=' })) return null;
	const left = expr.get('left');
	if (!left.isMemberExpression()) return null;

	const object = left.get('object');
	if (!object.isIdentifier({ name: targetName })) return null;

	const property = left.get('property');

	return {
		ref: object,
		property: property.node,
		value: expr.get('right').node,
		computed: left.node.computed,
	};
}

// Decomposes a (possibly chained) assignment `target.p1 = target.p2 = … = V` into one
// entry per property, each valued V (cloned for every link but the last, which reuses the
// node since the whole statement is removed). A plain `target.p = V` yields a single entry.
// Returns null when the statement isn't an assignment whose LHS chain writes members of
// `target` — e.g. a copyDataProperties call, or a link writing a different object's member.
function analyseObjectAssignChain(stmt: NodePath, targetName: string) {
	if (!stmt.isExpressionStatement()) return null;
	let expr: NodePath = stmt.get('expression');
	const links: {
		ref: NodePath;
		property: t.MemberExpression['property'];
		computed: boolean;
	}[] = [];
	while (expr.isAssignmentExpression({ operator: '=' })) {
		const left = expr.get('left');
		if (!left.isMemberExpression()) break;
		const object = left.get('object');
		if (!object.isIdentifier({ name: targetName })) return null;
		links.push({
			ref: object,
			property: (left.node as t.MemberExpression).property,
			computed: (left.node as t.MemberExpression).computed,
		});
		expr = expr.get('right');
	}
	if (links.length === 0) return null;
	const terminal = expr.node;
	if (!t.isExpression(terminal)) return null;
	// The innermost link is the first store executed (chaining nests the first statement
	// deepest), so reverse to recover original source order. The whole statement is removed
	// afterwards, so clone the shared value for every property.
	links.reverse();
	return links.map((link) => ({
		ref: link.ref,
		property: link.property,
		computed: link.computed,
		value: t.cloneNode(terminal as t.Expression, true),
	}));
}

function movableObjectConstructionAliasValue(expr: t.Expression): boolean {
	if (
		t.isIdentifier(expr) || t.isThisExpression(expr) ||
		t.isSuper(expr) || t.isLiteral(expr)
	) return true;
	if (t.isUnaryExpression(expr) && expr.operator !== 'delete') {
		return movableObjectConstructionAliasValue(expr.argument);
	}
	if (t.isMemberExpression(expr)) {
		if (
			!movableObjectConstructionAliasValue(
				expr.object as t.Expression,
			)
		) return false;
		return !expr.computed ||
			movableObjectConstructionAliasValue(expr.property as t.Expression);
	}
	if (t.isBinaryExpression(expr) || t.isLogicalExpression(expr)) {
		return t.isExpression(expr.left) &&
			movableObjectConstructionAliasValue(expr.left) &&
			movableObjectConstructionAliasValue(expr.right);
	}
	if (t.isConditionalExpression(expr)) {
		return movableObjectConstructionAliasValue(expr.test) &&
			movableObjectConstructionAliasValue(expr.consequent) &&
			movableObjectConstructionAliasValue(expr.alternate);
	}
	return false;
}

function nodeReferencesIdentifier(node: t.Node, name: string): boolean {
	let found = false;
	t.traverseFast(node, (child) => {
		if (found) return t.traverseFast.skip;
		if (t.isIdentifier(child, { name })) found = true;
	});
	return found;
}

function isMemberReadReference(ref: NodePath): boolean {
	const parent = ref.parentPath?.node;
	if (
		!parent || !t.isMemberExpression(parent) || parent.object !== ref.node
	) {
		return false;
	}
	const container = ref.parentPath?.parentPath?.node;
	return !(
		container && t.isAssignmentExpression(container) &&
		container.left === parent
	);
}

function isEnvironmentSlotWriteReference(ref: NodePath): boolean {
	const assignment = ref.parentPath?.node;
	if (
		!assignment || !t.isAssignmentExpression(assignment) ||
		assignment.right !== ref.node
	) return false;
	const left = assignment.left;
	return t.isMemberExpression(left, { computed: true }) &&
		t.isCallExpression(left.object) &&
		t.isV8IntrinsicIdentifier(left.object.callee, {
			name: 'expectEnvironment',
		});
}

function inlineBareObjectExpressionIntoNextGeneratedReference(
	stmt: NodePath<t.ExpressionStatement>,
) {
	const expr = stmt.get('expression');
	let replacement: t.ObjectExpression | undefined;
	if (expr.isObjectExpression()) {
		replacement = expr.node;
	} else if (expr.isAssignmentExpression({ operator: '=' })) {
		const left = expr.get('left');
		const right = expr.get('right');
		if (!left.isMemberExpression() || !right.isExpression()) return false;
		const object = left.get('object');
		if (!object.isObjectExpression()) return false;
		replacement = t.cloneNode(object.node, true);
		replacement.properties.push(objectPropertyFromAssignment(
			left.node.property,
			right.node,
			left.node.computed,
		));
	} else {
		return false;
	}
	const next = stmt.getNextSibling();
	if (!next.isExpressionStatement()) return false;
	const nextExpr = next.get('expression');
	if (!nextExpr.isAssignmentExpression({ operator: '=' })) return false;
	const right = nextExpr.get('right');
	const refs: NodePath<t.Identifier>[] = [];
	right.traverse({
		Identifier(path) {
			if (!/^r\d+_\d+$/.test(path.node.name)) return;
			if (
				path.parentPath?.isObjectProperty() &&
				path.parentPath.node.key === path.node &&
				!path.parentPath.node.computed
			) return;
			refs.push(path);
		},
	});
	if (refs.length !== 1) return false;
	refs[0].replaceWith(replacement);
	stmt.remove();
	return true;
}

function isAssignmentRightReference(ref: NodePath): boolean {
	const parent = ref.parentPath?.node;
	return !!(
		parent && t.isAssignmentExpression(parent) && parent.right === ref.node
	);
}

function inlineMovableAliasBeforeObjectWrites(
	current: NodePath<t.Node | null>,
	targetName: string,
): NodePath | null {
	if (!current.isVariableDeclaration({ kind: 'const' })) return null;
	const declarations = current.get('declarations');
	if (declarations.length !== 1) return null;
	const declarator = declarations[0];
	const id = declarator.get('id');
	const init = declarator.get('init');
	if (
		!id.isIdentifier() || !init.node || !t.isExpression(init.node) ||
		!movableObjectConstructionAliasValue(init.node)
	) return null;
	const binding = current.scope.getBinding(id.node.name);
	if (!binding?.constant || binding.path !== declarator) return null;
	const refs = new Set(binding.referencePaths);
	if (refs.size === 0) return null;
	let probe = current.getNextSibling();
	while (probe.node) {
		if (!analyseObjectAssignChain(probe, targetName)) break;
		for (const ref of [...refs]) {
			const statement = ref.findParent((path) => path.isStatement());
			if (statement?.node !== probe.node) continue;
			ref.replaceWith(t.cloneNode(init.node, true));
			refs.delete(ref);
		}
		if (refs.size === 0) return current;
		probe = probe.getNextSibling();
	}
	return null;
}

function propertyKeyMatches(
	property: t.ObjectProperty,
	key: t.Expression | t.PrivateName,
	computed: boolean,
) {
	const propertyName = t.toComputedKey(property);
	if (property.computed !== computed) {
		if (
			t.isStringLiteral(propertyName) &&
			t.isStringLiteral(key) &&
			propertyName.value === key.value
		) return true;
		if (
			t.isStringLiteral(propertyName) &&
			t.isIdentifier(key) &&
			propertyName.value === key.name
		) return true;
		return false;
	}
	if (!computed && t.isIdentifier(property.key) && t.isIdentifier(key)) {
		return property.key.name === key.name;
	}
	if (!computed && t.isStringLiteral(property.key) && t.isIdentifier(key)) {
		return property.key.value === key.name;
	}
	if (!computed && t.isIdentifier(property.key) && t.isStringLiteral(key)) {
		return property.key.name === key.value;
	}
	if (t.isStringLiteral(property.key) && t.isStringLiteral(key)) {
		return property.key.value === key.value;
	}
	if (t.isNumericLiteral(property.key) && t.isNumericLiteral(key)) {
		return property.key.value === key.value;
	}
	return JSON.stringify(comparableAst(property.key)) ===
		JSON.stringify(comparableAst(key));
}

function objectPropertyFromAssignment(
	key: t.Expression | t.PrivateName,
	value: t.Expression,
	computed: boolean,
): t.ObjectProperty {
	if (
		computed && t.isStringLiteral(key) &&
		t.isValidIdentifier(key.value, false)
	) {
		return t.objectProperty(
			t.identifier(key.value),
			t.cloneNode(value, true),
			false,
		);
	}
	return t.objectProperty(
		t.cloneNode(key, true),
		t.cloneNode(value, true),
		computed,
	);
}

function inlineSingleStringKeyObject(decn: NodePath<t.VariableDeclaration>) {
	const assign = extractRegisterAssign(decn);
	if (!assign || !assign.init.isObjectExpression()) return false;
	const id = assign.id;
	const init = assign.init;
	if (init.node.properties.length !== 0) return false;
	const binding = decn.scope.getBinding(id.node.name);
	if (!binding?.constant) return false;

	// A prior construction rewrite in this traversal may have cloned one of
	// this binding's references into a new literal. Babel does not index that
	// clone until the fixpoint's next scope crawl, so acting on the incomplete
	// reference set could remove the declaration and strand the cloned use.
	if (
		binding.referencePaths.some((reference) =>
			!nodePathIsAttached(reference)
		)
	) return false;
	const write = decn.getNextSibling();
	if (!write.isExpressionStatement()) return false;
	const expr = write.get('expression');
	if (!expr.isAssignmentExpression({ operator: '=' })) return false;
	const left = expr.get('left');
	const right = expr.get('right');
	if (!left.isMemberExpression() || !right.isStringLiteral()) return false;
	const object = left.get('object');
	const property = left.get('property');
	if (!object.isIdentifier({ name: id.node.name })) return false;
	if (!property.isIdentifier() || property.node.name !== right.node.value) {
		return false;
	}

	const refs = new Set(binding.referencePaths);
	refs.delete(object);
	const propertyValue = t.stringLiteral(right.node.value);
	const objectLiteral = t.objectExpression([
		t.objectProperty(t.identifier(property.node.name), propertyValue),
	]);
	let assignmentRight: NodePath | undefined;
	for (const ref of [...refs]) {
		const parent = ref.parentPath;
		if (parent?.isMemberExpression() && parent.node.object === ref.node) {
			const container = parent.parentPath?.node;
			if (
				container && t.isAssignmentExpression(container) &&
				container.left === parent.node
			) return false;
			if (
				!propertyKeyMatches(
					t.objectProperty(
						t.identifier(property.node.name),
						propertyValue,
					),
					parent.node.property,
					parent.node.computed,
				)
			) return false;
			const objectProperty = parent.parentPath;
			if (
				objectProperty?.isObjectProperty() &&
				objectProperty.node.key === parent.node &&
				objectProperty.node.computed &&
				t.isValidIdentifier(right.node.value, false)
			) {
				objectProperty.replaceWith(t.objectProperty(
					t.identifier(right.node.value),
					objectProperty.node.value,
					false,
				));
			} else {
				parent.replaceWith(t.stringLiteral(right.node.value));
			}
			refs.delete(ref);
			continue;
		}
		if (isAssignmentRightReference(ref)) {
			if (assignmentRight) return false;
			assignmentRight = ref;
			continue;
		}
		return false;
	}
	if (!assignmentRight || refs.size !== 1) return false;
	assignmentRight.replaceWith(objectLiteral);
	write.remove();
	decn.remove();
	return true;
}

function findObjectProperty(
	object: t.ObjectExpression,
	key: t.Expression | t.PrivateName,
	computed: boolean,
) {
	for (const property of object.properties) {
		if (!t.isObjectProperty(property)) continue;
		if (propertyKeyMatches(property, key, computed)) return property;
	}
}

function isObjectConstructionAccumulator(owner: t.Node, expr: t.Node) {
	const instruction = (expr.extra as LiftedExtra | undefined)?.instruction ??
		(owner.extra as LiftedExtra | undefined)?.instruction;
	return instruction === 'NewObject' ||
		instruction === 'NewObjectWithBuffer' ||
		instruction === 'NewObjectWithBufferAndParent';
}

function hasNullPlaceholderObjectProperty(expr: t.ObjectExpression) {
	return expr.properties.some((property) =>
		t.isObjectProperty(property) && t.isNullLiteral(property.value)
	);
}

function analyseCopyDataPropertiesCall(
	current: NodePath<t.Node | null>,
	objName: string,
): { src: t.Expression; objRef: NodePath<t.Identifier> } | null {
	if (!current.isExpressionStatement()) return null;
	const callPath = (current as NodePath<t.ExpressionStatement>).get(
		'expression',
	);
	if (!callPath.isCallExpression()) return null;
	const callee = (callPath as NodePath<t.CallExpression>).get('callee');
	const isCopyDataProperties = callee.matchesPattern(
		'HermesInternal.copyDataProperties',
	);
	const isObjectAssign = callee.matchesPattern('Object.assign');
	if (!isCopyDataProperties && !isObjectAssign) return null;
	const callArgs = (callPath as NodePath<t.CallExpression>).get('arguments');
	// Object.assign(target, source) is the public equivalent produced by the
	// two-argument copyDataProperties cleanup. Keep multi-source Object.assign
	// untouched: each later source observes prior writes to the same target.
	if (isObjectAssign && callArgs.length !== 2) return null;
	// 2-arg copyDataProperties: (target, source) — older HBC; 3-arg:
	// (target, source, excluded) — newer HBC.
	if (
		isCopyDataProperties && (callArgs.length < 2 || callArgs.length > 3)
	) return null;
	if (!callArgs[0].isIdentifier({ name: objName })) return null;
	if (!t.isExpression(callArgs[1].node)) return null;
	return {
		src: callArgs[1].node as t.Expression,
		objRef: callArgs[0] as NodePath<t.Identifier>,
	};
}

export function rewriteTwoArgumentCopyDataProperties(root: t.Node): number {
	let rewritten = 0;
	t.traverseFast(root, (node) => {
		if (node !== root && t.isFunction(node)) return t.traverseFast.skip;
		if (!t.isCallExpression(node)) return;
		const callee = node.callee;
		if (
			!t.isMemberExpression(callee, { computed: false }) ||
			!t.isIdentifier(callee.object, { name: 'HermesInternal' }) ||
			!t.isIdentifier(callee.property, { name: 'copyDataProperties' }) ||
			node.arguments.length !== 2 ||
			!t.isExpression(node.arguments[0]) ||
			!t.isExpression(node.arguments[1])
		) return;
		Object.assign(
			node,
			t.callExpression(
				t.memberExpression(
					t.identifier('Object'),
					t.identifier('assign'),
				),
				[node.arguments[0], node.arguments[1]],
			),
		);
		rewritten++;
		return t.traverseFast.skip;
	});
	return rewritten;
}

function analyseObjectSpread(
	current: NodePath<t.Node | null>,
	objName: string,
): {
	src: t.Expression;
	objRef: NodePath<t.Identifier>;
	last: NodePath<t.Node | null>;
	consumed: NodePath<t.Node | null>[];
} | null {
	if (!current.isVariableDeclaration({ kind: 'const' })) return null;
	const decls = (current as NodePath<t.VariableDeclaration>).get(
		'declarations',
	);
	if (decls.length !== 1) return null;
	const declId = decls[0].get('id');
	if (!declId.isIdentifier()) return null;
	const exclName = (declId.node as t.Identifier).name;
	const declInit = decls[0].get('init');
	if (
		!declInit.isCallExpression() ||
		!(declInit as NodePath<t.CallExpression>).get('callee').matchesPattern(
			'Object.create',
		)
	) return null;
	const initArgs = (declInit as NodePath<t.CallExpression>).get('arguments');
	if (initArgs.length !== 1 || !initArgs[0].isNullLiteral()) return null;

	// Consume zero or more excl[key] = 0 assignments
	const consumed: NodePath<t.Node | null>[] = [];
	let probe = current.getNextSibling();
	while (probe.node) {
		if (!probe.isExpressionStatement()) break;
		const expr = (probe as NodePath<t.ExpressionStatement>).get(
			'expression',
		);
		if (!expr.isAssignmentExpression({ operator: '=' })) break;
		const lhs = (expr as NodePath<t.AssignmentExpression>).get('left');
		if (
			!lhs.isMemberExpression({ computed: true }) ||
			!lhs.get('object').isIdentifier({ name: exclName })
		) break;
		if (
			!(expr as NodePath<t.AssignmentExpression>).get('right')
				.isNumericLiteral({ value: 0 })
		) break;
		consumed.push(probe);
		probe = probe.getNextSibling();
	}

	// probe must now be at the bare copyDataProperties(obj, src, excl) call
	if (!probe.node || !probe.isExpressionStatement()) return null;
	const callPath = (probe as NodePath<t.ExpressionStatement>).get(
		'expression',
	);
	if (!callPath.isCallExpression()) return null;
	if (
		!(callPath as NodePath<t.CallExpression>).get('callee').matchesPattern(
			'HermesInternal.copyDataProperties',
		)
	) return null;
	const callArgs = (callPath as NodePath<t.CallExpression>).get('arguments');
	if (callArgs.length !== 3) return null;
	if (!callArgs[0].isIdentifier({ name: objName })) return null;
	if (!callArgs[2].isIdentifier({ name: exclName })) return null;
	if (!t.isExpression(callArgs[1].node)) return null;

	return {
		src: callArgs[1].node as t.Expression,
		objRef: callArgs[0] as NodePath<t.Identifier>,
		last: probe,
		consumed,
	};
}

// The construction target: `const rN = …` (single-assignment register) or, when rN is a phi
// register, the bare assignment `rN = …`. Only a register identifier qualifies for the
// assignment form; the caller verifies the binding is a (non-constant) phi `let`.
function extractObjectConstructionTarget(stmt: NodePath): {
	id: NodePath<t.Identifier>;
	init: NodePath<t.Expression>;
	isAssignment: boolean;
} | undefined {
	if (stmt.isVariableDeclaration()) {
		const assign = extractRegisterAssign(
			stmt as NodePath<t.VariableDeclaration>,
		);
		if (!assign) return;
		return {
			id: assign.id,
			init: assign.init as NodePath<t.Expression>,
			isAssignment: false,
		};
	}
	if (stmt.isExpressionStatement()) {
		const expr = stmt.get('expression');
		if (!expr.isAssignmentExpression({ operator: '=' })) return;
		const left = (expr as NodePath<t.AssignmentExpression>).get('left');
		if (
			!left.isIdentifier() ||
			!/^r\d+_\d+$/.test((left.node as t.Identifier).name)
		) return;
		const init = (expr as NodePath<t.AssignmentExpression>).get('right');
		if (!init.node) return;
		return {
			id: left as NodePath<t.Identifier>,
			init: init as NodePath<t.Expression>,
			isAssignment: true,
		};
	}
}

/**
 * Hermes lowers `{ __proto__: null, ... }` by creating an ordinary literal and
 * immediately invoking its private `silentSetPrototypeOf` builtin. Rebuild the
 * source-level literal only while the target is the adjacent fresh binding;
 * calls on an existing or aliased object retain their runtime semantics.
 */
export function inlineNullPrototypeObjectLiteral(stmt: NodePath) {
	if (!stmt.isExpressionStatement()) return;
	const call = stmt.get('expression');
	if (
		!call.isCallExpression() ||
		!call.get('callee').matchesPattern(
			'HermesInternal.silentSetPrototypeOf',
		)
	) return;
	const args = call.get('arguments');
	if (
		args.length !== 2 || !args[0].isIdentifier() ||
		!args[1].isNullLiteral()
	) return;

	const declarationPath = stmt.getPrevSibling();
	if (!declarationPath.isVariableDeclaration({ kind: 'const' })) return;
	const declarations = declarationPath.get('declarations');
	if (declarations.length !== 1) return;
	const declaration = declarations[0];
	const id = declaration.get('id');
	const init = declaration.get('init');
	if (
		!id.isIdentifier({ name: args[0].node.name }) ||
		!init.isObjectExpression()
	) return;
	const binding = stmt.scope.getBinding(id.node.name);
	if (!binding?.constant || binding.path !== declaration) return;

	const alreadyHasPrototypeSetter = init.node.properties.some((property) => {
		if (!t.isObjectProperty(property) || property.computed) return false;
		return t.isIdentifier(property.key, { name: '__proto__' }) ||
			t.isStringLiteral(property.key, { value: '__proto__' });
	});
	if (alreadyHasPrototypeSetter) return;

	init.node.properties.unshift(t.objectProperty(
		t.identifier('__proto__'),
		t.nullLiteral(),
	));
	stmt.remove();
	return true;
}

function pruneDetachedReferencePaths(refs: Set<NodePath>) {
	for (const ref of refs) {
		if (!nodePathIsAttached(ref)) refs.delete(ref);
	}
}
function nodePathIsWithinAny(
	path: NodePath,
	containers: ReadonlySet<t.Node>,
): boolean {
	let current: NodePath | null = path;
	while (current) {
		if (containers.has(current.node)) return true;
		current = current.parentPath;
	}
	return false;
}

function isAssignmentTargetReference(ref: NodePath): boolean {
	let current: NodePath | null = ref;
	while (current?.parentPath) {
		if (
			current.parentPath.isAssignmentExpression() &&
			current.key === 'left'
		) return true;
		if (
			current.parentPath.isUpdateExpression() &&
			current.key === 'argument'
		) return true;
		current = current.parentPath;
	}
	return false;
}

export function inlineObjectConstruction(decn: NodePath) {
	if (
		decn.isVariableDeclaration() &&
		inlineFoldedNamedFunctionDefine(decn as NodePath<t.VariableDeclaration>)
	) return true;
	const target = extractObjectConstructionTarget(decn);
	if (!target) return;

	const { id, init, isAssignment } = target;
	const binding = decn.scope.getBinding(id.node.name);
	if (!binding) return;
	// Construction folding can relocate a reference while this traversal is
	// still visiting later declarations. Defer this binding until the next
	// fixpoint iteration has crawled scopes and indexed the relocated use.
	if (
		binding.referencePaths.some((reference) =>
			!nodePathIsAttached(reference)
		)
	) return;
	const declaration = binding.path.parentPath;
	if (
		declaration.isVariableDeclaration() &&
		(declaration.node as LiftedAST<t.VariableDeclaration>).extra
			?.preserveAcrossBlocks
	) return;
	// `const rN = …` must be a constant register. `rN = …` is only foldable when rN is a phi
	// register — a `let` the SSA→AST phi lift made multiply-assigned; the build-up below then
	// fully defines its value in this branch.
	if (isAssignment ? binding.constant : !binding.constant) return;

	// const x = HermesInternal.copyDataProperties({}, src[, excl]) → const x = { ...src }
	// Only when excl is absent or the literal `undefined` — a named excl identifier means
	// this is a destructuring rest pattern handled by cleanupSequentialObjectDestructuringInBody.
	if (init.isCallExpression()) {
		const callee = (init as NodePath<t.CallExpression>).get('callee');
		if (callee.matchesPattern('HermesInternal.copyDataProperties')) {
			const args = (init as NodePath<t.CallExpression>).get('arguments');
			const exclArg = args.length === 3 ? args[2] : null;
			const excludesNothing = exclArg === null ||
				(t.isExpression(exclArg.node) && isUndefinedNode(exclArg.node));
			if (
				excludesNothing &&
				args.length >= 2 &&
				args.length <= 3 &&
				args[0].isObjectExpression() &&
				(args[0] as NodePath<t.ObjectExpression>).node.properties
						.length === 0 &&
				t.isExpression(args[1].node)
			) {
				const spread = t.objectExpression([
					t.spreadElement(args[1].node as t.Expression),
				]) as LiftedAST<t.ObjectExpression>;
				spread.extra = {
					...(init.node as LiftedAST<t.CallExpression>).extra,
					copyDataPropertiesSpread: true,
				};
				init.replaceWith(spread);
				return true;
			}
		}
	}

	// Unified array construction: `new Array(N)` prefilled by `arr[k] = v`, or an array
	// literal, optionally followed by any number of `HermesInternal.arraySpread` calls
	// (captured/bare/embedded) interleaved with element writes. Element positions are tracked
	// by a running ArrayOffset — numeric while static, symbolic (offsetVar + delta) after a
	// length-changing spread — which lets multiple spreads to the same target compose.
	const isNewArray = init.isNewExpression() &&
		init.get('callee').isIdentifier({ name: 'Array' });
	if (isNewArray || init.isArrayExpression()) {
		let length: number | null = null;
		const segments: (t.Expression | t.SpreadElement | null)[] = [];
		if (isNewArray) {
			const args = (init as NodePath<t.NewExpression>).get('arguments');
			if (args.length !== 1) return;
			if (!args[0].isNumericLiteral()) return;
			length = (args[0].node as t.NumericLiteral).value;
		} else {
			segments.push(...(init.node as t.ArrayExpression).elements);
			// Drop trailing holes: Hermes leaves the slot where a spread is inserted (or which
			// a later write fills) as an elision. If nothing fills it we won't transform, so the
			// original literal is left untouched.
			while (
				segments.length > 0 && segments[segments.length - 1] === null
			) {
				segments.pop();
			}
		}

		const refs = new Set(binding.referencePaths);
		let offset: ArrayOffset = { base: null, delta: segments.length };
		let sawSpread = false;
		let terminated = false;
		const spreadAliases = new Map<string, AdjacentArraySpreadAlias>();
		let deferredSpreadSetup = false;
		let deferredSpreadStatement: t.Node | null = null;

		let current: NodePath<t.Node | null> = decn;
		const toRemove: NodePath[] = [decn];

		while (!terminated) {
			current = current.getNextSibling();
			if (!current.node || !current.isStandardized()) break;

			// Element write: arr[idx] = v
			const assign = analyseObjectAssign(current, id.node.name);
			if (assign && t.isExpression(assign.value)) {
				if (
					offset.base === null && t.isNumericLiteral(assign.property)
				) {
					// Static phase: fill by absolute index (holes / out-of-order allowed).
					const idx = (assign.property as t.NumericLiteral).value;
					while (segments.length <= idx) segments.push(null);
					segments[idx] = assign.value as t.Expression;
					refs.delete(assign.ref);
					toRemove.push(current);
					offset = { base: null, delta: segments.length };
					continue;
				}
				if (
					offset.base !== null &&
					arrayOffsetMatches(offset, assign.property)
				) {
					// Dynamic phase: sequential append after a spread.
					segments.push(assign.value as t.Expression);
					refs.delete(assign.ref);
					toRemove.push(current);
					offset = { base: offset.base, delta: offset.delta + 1 };
					continue;
				}
			}

			// Spread: captured / bare / embedded (possibly a nested chain of adjacent spreads)
			const spread = analyseArraySpreadStatement(current, id.node.name);
			if (spread && arrayOffsetMatches(offset, spread.startIndex)) {
				for (const iterable of spread.iterables) {
					const alias = t.isIdentifier(iterable)
						? spreadAliases.get(iterable.name)
						: undefined;
					segments.push(t.spreadElement(
						alias ? t.cloneNode(alias.init, true) : iterable,
					));
					if (alias) spreadAliases.delete(alias.name);
				}
				if (spread.trailingValue) segments.push(spread.trailingValue);
				for (const r of spread.refs) refs.delete(r);
				toRemove.push(current);
				sawSpread = true;
				if (deferredSpreadSetup) deferredSpreadStatement = current.node;
				if (spread.offsetVar) {
					// The captured variable holds the post-spread length (after every nested
					// spread in the chain), so tracking continues relative to it.
					offset = { base: spread.offsetVar, delta: 0 };
				} else {
					terminated = true; // bare/embedded: post-spread offset is untrackable
				}
				continue;
			}
			const spreadAlias = analyseAdjacentArraySpreadAlias(
				current,
				id.node.name,
				offset,
			);
			if (spreadAlias) {
				spreadAliases.set(spreadAlias.name, spreadAlias);
				toRemove.push(spreadAlias.declaration);
				continue;
			}
			if (
				segments.length === 0 &&
				offset.base === null &&
				offset.delta === 0 &&
				isAdjacentArraySpreadSetupDeclaration(
					current,
					id.node.name,
					offset,
				)
			) {
				deferredSpreadSetup = true;
				continue;
			}
			const alias = inlineMovableAliasBeforeObjectWrites(
				current,
				id.node.name,
			);
			if (alias) {
				toRemove.push(alias);
				continue;
			}

			break;
		}

		if (spreadAliases.size > 0) return;
		if (toRemove.length <= 1) return; // collected nothing beyond the declaration
		if (offset.base !== null) {
			const offsetBinding = decn.scope.getBinding(offset.base);
			const removedNodes = new Set(
				toRemove.flatMap((path) => path.node ? [path.node] : []),
			);
			if (
				offsetBinding?.referencePaths.some((ref) =>
					ref.isIdentifier({ name: offset.base! }) &&
					nodePathIsAttached(ref) &&
					!nodePathIsWithinAny(ref, removedNodes)
				)
			) return;
		}

		// A plain `new Array(N)` with no spread keeps its length; pad trailing holes.
		if (isNewArray && !sawSpread && length !== null) {
			while (segments.length < length) segments.push(null);
		}

		pruneDetachedReferencePaths(refs);
		if (deferredSpreadSetup) {
			if (isAssignment || refs.size !== 1) return;
			const reference = [...refs][0];
			if (isAssignmentTargetReference(reference)) return;
			const terminal = reference.findParent((path) => path.isStatement());
			if (
				!terminal?.isStatement() ||
				terminal.getPrevSibling().node !== deferredSpreadStatement
			) return;
		}
		if (
			!isAssignment && refs.size === 1 &&
			!isAssignmentTargetReference([...refs][0])
		) {
			[...refs][0].replaceWith(t.arrayExpression(segments));
			for (const p of toRemove) p.remove();
			return true;
		}
		// Multiple (or zero) remaining uses — fold onto the declaration, leaving each use
		// referencing the SSA register.
		init.replaceWith(t.arrayExpression(segments));
		for (const p of toRemove) {
			if (p !== decn) p.remove();
		}
		return true;
	} else if (
		init.isObjectExpression() && init.node.properties.length > 0 &&
		(isObjectConstructionAccumulator(decn.node, init.node) ||
			hasNullPlaceholderObjectProperty(init.node) ||
			init.node.properties.some((p) => t.isSpreadElement(p)))
	) {
		let current: NodePath<t.Node | null> = decn;
		const toRemove: NodePath[] = [];
		const refs = new Set(binding.referencePaths);
		const updates: {
			property: t.ObjectProperty;
			value: t.Expression;
		}[] = [];
		const appends: (t.ObjectMember | t.SpreadElement)[] = [];
		let changed = false;

		while (true) {
			current = current.getNextSibling();
			if (!current.node) break;

			const chain = analyseObjectAssignChain(current, id.node.name);
			if (chain) {
				// Plan every chain link first so the statement is applied atomically:
				// either all properties fold in or the chain blocks inlining.
				const planned: Array<
					| { update: t.ObjectProperty; value: t.Expression }
					| { append: t.ObjectProperty }
				> = [];
				let blocked = false;
				for (const entry of chain) {
					const property = findObjectProperty(
						init.node,
						entry.property,
						entry.computed,
					);
					if (
						property && t.isNullLiteral(property.value) &&
						t.isExpression(entry.value)
					) {
						planned.push({ update: property, value: entry.value });
					} else if (!property && t.isExpression(entry.value)) {
						planned.push({
							append: objectPropertyFromAssignment(
								entry.property,
								entry.value,
								entry.computed,
							),
						});
					} else {
						blocked = true;
						break;
					}
				}
				if (blocked) break;

				for (const p of planned) {
					if ('update' in p) {
						updates.push({ property: p.update, value: p.value });
					} else {
						appends.push(p.append);
					}
				}
				for (const entry of chain) refs.delete(entry.ref);
				toRemove.push(current);
				changed = true;
			} else if (current.isExpressionStatement()) {
				const getterSetter = extractGetterSetterDefine(
					current.get('expression'),
					id.node.name,
				);
				if (!getterSetter?.enumerable) {
					const copyData = analyseCopyDataPropertiesCall(
						current,
						id.node.name,
					);
					if (!copyData) break;
					appends.push(t.spreadElement(copyData.src));
					refs.delete(copyData.objRef);
					toRemove.push(current);
					changed = true;
					continue;
				}
				const { name, getter, setter } = getterSetter;
				refs.delete(getterSetter.target);
				const getterArg: t.Expression = getter ??
					t.identifier('undefined');
				const setterArg: t.Expression = setter ??
					t.identifier('undefined');
				if (!getter && !setter) break;

				toRemove.push(current);
				appends.push(t.objectProperty(
					t.isValidIdentifier(name, false)
						? t.identifier(name)
						: t.stringLiteral(name),
					t.callExpression(
						t.v8IntrinsicIdentifier('asGetterSetter'),
						[getterArg, setterArg],
					),
					!t.isValidIdentifier(name, false),
				));
			} else if (current.isVariableDeclaration()) {
				const alias = inlineMovableAliasBeforeObjectWrites(
					current,
					id.node.name,
				);
				if (alias) {
					toRemove.push(alias);
					changed = true;
					continue;
				}
				const method = extractNamedFunctionDefine(
					current,
					id.node.name,
				);
				if (!method?.ref) break;
				const ref = method.ref;

				appends.push(t.objectProperty(
					method.property,
					method.value,
					true,
				));
				refs.delete(ref);
				toRemove.push(current, ...method.toRemove);
			} else {
				break;
			}
		}

		if (!changed) return;
		for (const update of updates) {
			update.property.value = update.value;
		}
		if (appends.length > 0) {
			init.get('properties').at(-1)!.insertAfter(appends);
		}
		pruneDetachedReferencePaths(refs);
		if (
			!isAssignment && refs.size === 1 &&
			!isAssignmentTargetReference([...refs][0])
		) {
			// Single remaining use — move the completed buffer literal into it.
			[...refs][0].replaceWith(init.node);
			for (const p of toRemove) p.remove();
			decn.remove();
			return true;
		}
		// Multiple (or zero) remaining uses — updates/appends are applied to the buffer in
		// place; keep the declaration and leave each use referencing the SSA register.
		for (const p of toRemove) p.remove();
		return true;
	} else if (init.isObjectExpression() && init.node.properties.length === 0) {
		let current: NodePath<t.Node | null> = decn;
		const toRemove = [];
		const skippedPrelude: NodePath[] = [];

		const refs = new Set(binding.referencePaths);

		debugInlineObj('empty-obj start', {
			name: id.node.name,
			totalRefs: refs.size,
		});

		const properties: t.ObjectExpression['properties'][number][] = [];

		while (true) {
			current = current.getNextSibling();
			if (!current.node) break;

			const chain = analyseObjectAssignChain(current, id.node.name);
			if (chain) {
				for (const entry of chain) {
					refs.delete(entry.ref);
					properties.push(
						objectPropertyFromAssignment(
							entry.property,
							entry.value,
							entry.computed,
						),
					);
				}
				toRemove.push(current);
				continue;
			} else if (current.isExpressionStatement()) {
				const getterSetter = extractGetterSetterDefine(
					current.get('expression'),
					id.node.name,
				);
				if (getterSetter?.enumerable) {
					const { name, getter, setter } = getterSetter;
					refs.delete(getterSetter.target);
					const getterArg: t.Expression = getter ??
						t.identifier('undefined');
					const setterArg: t.Expression = setter ??
						t.identifier('undefined');
					if (getter || setter) {
						toRemove.push(current);
						properties.push(t.objectProperty(
							t.isValidIdentifier(name, false)
								? t.identifier(name)
								: t.stringLiteral(name),
							t.callExpression(
								t.v8IntrinsicIdentifier('asGetterSetter'),
								[getterArg, setterArg],
							),
							!t.isValidIdentifier(name, false),
						));
						continue;
					}
				} else {
					const copyData = analyseCopyDataPropertiesCall(
						current,
						id.node.name,
					);
					if (copyData) {
						refs.delete(copyData.objRef);
						properties.push(t.spreadElement(copyData.src));
						toRemove.push(current);
						continue;
					}
				}
			} else if (current.isVariableDeclaration()) {
				const alias = inlineMovableAliasBeforeObjectWrites(
					current,
					id.node.name,
				);
				if (alias) {
					toRemove.push(alias);
					continue;
				}
				const method = extractNamedFunctionDefine(
					current,
					id.node.name,
				);
				if (method?.ref) {
					const ref = method.ref;
					properties.push(t.objectProperty(
						method.property,
						method.value,
						true,
					));
					refs.delete(ref);
					toRemove.push(current, ...method.toRemove);
					continue;
				}

				const spread = analyseObjectSpread(current, id.node.name);
				if (spread) {
					refs.delete(spread.objRef);
					properties.push(t.spreadElement(spread.src));
					toRemove.push(current, ...spread.consumed, spread.last);
					current = spread.last;
					continue;
				}
			}

			// The fresh allocation itself is movable. Skip setup statements that
			// precede the first object write and do not mention the accumulator
			if (
				properties.length === 0 && toRemove.length === 0 &&
				!nodeReferencesIdentifier(current.node, id.node.name)
			) {
				skippedPrelude.push(current);
				continue;
			}
			// Nothing matched — log the blocker before deciding to bail or inline
			if (DEBUG_INLINE_OBJ) {
				let blockerId = '(unknown)';
				try {
					const node = current.node as t.Node;
					if (t.isExpressionStatement(node)) {
						const expr = node.expression;
						if (t.isCallExpression(expr)) {
							const callee = expr.callee;
							if (
								t.isMemberExpression(callee, {
									computed: false,
								}) &&
								t.isIdentifier(callee.object) &&
								t.isIdentifier(callee.property)
							) {
								blockerId =
									`call:${callee.object.name}.${callee.property.name}`;
							} else if (t.isV8IntrinsicIdentifier(callee)) {
								blockerId = `intrinsic:${callee.name}`;
							} else {
								blockerId = `call:${expr.type}`;
							}
						} else if (t.isAssignmentExpression(expr)) {
							blockerId = `assign:${expr.operator}`;
						} else {
							blockerId = `expr:${expr.type}`;
						}
					} else {
						blockerId = `stmt:${node.type}`;
					}
				} catch { /**/ }
				debugInlineObj('blocker for', id.node.name, {
					blocker: blockerId,
					refsRemaining: refs.size,
					propsCollected: properties.length,
				});
			}

			break;
		}

		pruneDetachedReferencePaths(refs);
		if (
			!isAssignment && refs.size === 1 &&
			!isAssignmentTargetReference([...refs][0])
		) {
			const [remainingRef] = [...refs];
			if (
				skippedPrelude.length > 0 &&
				isEnvironmentSlotWriteReference(remainingRef)
			) return;
			// Single remaining use — inline the literal directly into it.
			remainingRef.replaceWith(t.objectExpression(properties));
			for (const p of toRemove) {
				p.remove();
			}
			decn.remove();
			return true;
		}

		// Multiple (or zero) remaining uses — fold the collected properties onto the
		// declaration and leave each use referencing the SSA register. Preserve the
		// bytecode construction provenance so a temporary declaration which blocked
		// this scan can be removed by another cleanup and the next iteration can
		// resume folding this now-non-empty object.
		if (
			toRemove.length > 0 && skippedPrelude.length === 0 &&
			refs.size > 0 &&
			![...refs].some(isMemberReadReference)
		) {
			const partial = t.objectExpression(properties) as LiftedAST<
				t.ObjectExpression
			>;
			partial.extra = {
				...(decn.node as LiftedAST<t.Node>).extra,
				...(init.node as LiftedAST<t.ObjectExpression>).extra,
			};
			init.replaceWith(partial);
			for (const p of toRemove) {
				p.remove();
			}
			return true;
		}
	}
}
interface CapturedSequenceArrayOffset {
	name: string;
	assignment: t.AssignmentExpression;
	declarator: NodePath<t.VariableDeclarator>;
}

function generatedIdentifierUseCount(node: t.Node, name: string): number {
	let count = 0;
	t.traverseFast(node, (child) => {
		if (t.isIdentifier(child, { name })) count++;
	});
	return count;
}

function sequenceIsInsideHandledRegion(
	path: NodePath<t.SequenceExpression>,
): boolean {
	let current: NodePath | null = path.parentPath;
	while (current && !current.isFunction()) {
		if (current.isTryStatement()) return true;
		current = current.parentPath;
	}
	return false;
}

function referenceCrossesFunctionBoundary(
	reference: NodePath,
	scopePath: NodePath,
): boolean {
	let current = reference.parentPath;
	while (current && current !== scopePath) {
		if (current.isFunction()) return true;
		current = current.parentPath;
	}
	return false;
}

function removeGeneratedDeclarator(path: NodePath<t.VariableDeclarator>) {
	const declaration = path.parentPath;
	path.remove();
	if (
		declaration?.isVariableDeclaration() &&
		declaration.node.declarations.length === 0
	) declaration.remove();
}

interface BranchArrayRegionPlan {
	expression: t.ArrayExpression;
	protocol: NodePath<t.Statement>[];
	terminal: NodePath<t.Identifier>;
	consumedReferences: Set<t.Node>;
}

function branchArrayTerminalReference(
	statement: NodePath<t.Statement>,
	references: readonly NodePath<t.Identifier>[],
): NodePath<t.Identifier> | null {
	if (references.length !== 1) return null;
	const reference = references[0];
	if (isAssignmentTargetReference(reference)) return null;

	if (statement.isReturnStatement()) {
		const argument = statement.get('argument');
		return argument.node === reference.node ? reference : null;
	}
	if (!statement.isExpressionStatement()) return null;
	const expression = statement.get('expression');
	if (!expression.isAssignmentExpression({ operator: '=' })) return null;
	const left = expression.get('left');
	const right = expression.get('right');
	if (!left.isIdentifier() || !right.isExpression()) return null;
	if (right.node === reference.node) return reference;
	if (!right.isCallExpression()) return null;

	const callee = right.get('callee');
	if (callee.isMemberExpression()) {
		const object = callee.get('object');
		if (object.node === reference.node) return reference;
	}
	if (!callee.isIdentifier()) return null;
	const args = right.get('arguments');
	const argumentIndex = args.findIndex((argument) =>
		argument.node === reference.node
	);
	if (argumentIndex < 0) return null;
	if (
		args.slice(0, argumentIndex).some((argument) =>
			!argument.isIdentifier() &&
			!argument.isLiteral() &&
			!argument.isThisExpression()
		)
	) return null;
	return reference;
}

function branchReferencesInStatement(
	statement: NodePath<t.Statement>,
	references: readonly NodePath<t.Identifier>[],
): NodePath<t.Identifier>[] {
	const container = new Set<t.Node>([statement.node]);
	return references.filter((reference) =>
		nodePathIsAttached(reference) &&
		nodePathIsWithinAny(reference, container)
	);
}

function planBranchArrayRegion(
	statements: readonly NodePath<t.Statement>[],
	targetName: string,
	references: readonly NodePath<t.Identifier>[],
): BranchArrayRegionPlan | null {
	const segments: (t.Expression | t.SpreadElement | null)[] = [];
	let offset: ArrayOffset = { base: null, delta: 0 };
	let sawSpread = false;
	let spreadTerminated = false;
	const protocol: NodePath<t.Statement>[] = [];
	const consumedReferences = new Set<t.Node>();

	for (const statement of statements) {
		if (!spreadTerminated) {
			const assign = analyseObjectAssign(statement, targetName);
			if (
				assign && t.isExpression(assign.value) &&
				offset.base === null &&
				t.isNumericLiteral(assign.property)
			) {
				const index = assign.property.value;
				while (segments.length <= index) segments.push(null);
				segments[index] = t.cloneNode(assign.value, true);
				offset = { base: null, delta: segments.length };
				consumedReferences.add(assign.ref.node);
				protocol.push(statement);
				continue;
			}

			const spread = analyseArraySpreadStatement(statement, targetName);
			if (
				spread && spread.offsetVar === null &&
				arrayOffsetMatches(offset, spread.startIndex)
			) {
				for (const iterable of spread.iterables) {
					segments.push(t.spreadElement(t.cloneNode(iterable, true)));
				}
				if (spread.trailingValue) {
					segments.push(t.cloneNode(spread.trailingValue, true));
				}
				for (const reference of spread.refs) {
					consumedReferences.add(reference.node);
				}
				protocol.push(statement);
				sawSpread = true;
				spreadTerminated = true;
				continue;
			}
		}

		if (!sawSpread) return null;
		const statementReferences = branchReferencesInStatement(
			statement,
			references,
		);
		const terminal = branchArrayTerminalReference(
			statement,
			statementReferences,
		);
		if (!terminal) return null;
		consumedReferences.add(terminal.node);
		return {
			expression: t.arrayExpression(segments),
			protocol,
			terminal,
			consumedReferences,
		};
	}

	return null;
}

function isUninitialisedBranchResultDeclaration(
	statement: NodePath<t.Statement>,
): boolean {
	if (!statement.isVariableDeclaration({ kind: 'let' })) return false;
	return statement.get('declarations').every((declaration) =>
		declaration.get('init').node == null
	);
}

function inlineBranchArrayConstruction(initializer: NodePath): boolean {
	const target = extractObjectConstructionTarget(initializer);
	if (!target) return false;
	const { id, init, isAssignment } = target;
	if (!/^r\d+_\d+$/.test(id.node.name)) return false;

	const emptyArray = init.isArrayExpression() &&
		init.node.elements.length === 0;
	const capacityArray = init.isNewExpression() &&
		init.get('callee').isIdentifier({ name: 'Array' }) &&
		init.get('arguments').length === 1 &&
		init.get('arguments.0').isNumericLiteral();
	if (!emptyArray && !capacityArray) return false;

	const binding = initializer.scope.getBinding(id.node.name);
	if (!binding || !binding.path.isVariableDeclarator()) return false;
	if (
		binding.referencePaths.some((reference) =>
			referenceCrossesFunctionBoundary(reference, binding.scope.path)
		)
	) return false;
	if (isAssignment) {
		const expression = initializer.get('expression');
		if (
			!expression.isAssignmentExpression() ||
			binding.constantViolations.length !== 1 ||
			binding.constantViolations[0].node !== expression.node
		) return false;
	} else if (!binding.constant) {
		return false;
	}

	const parent = initializer.parentPath;
	if (!parent?.isBlockStatement() && !parent?.isProgram()) return false;
	const siblings = parent.get('body') as NodePath<t.Statement>[];
	const initializerIndex = siblings.findIndex((sibling) =>
		sibling.node === initializer.node
	);
	if (initializerIndex < 0) return false;

	let branchIndex = initializerIndex + 1;
	while (
		branchIndex < siblings.length &&
		isUninitialisedBranchResultDeclaration(siblings[branchIndex])
	) {
		branchIndex++;
	}
	const branch = siblings[branchIndex];
	if (!branch?.isIfStatement()) return false;
	const consequent = branch.get('consequent');
	if (!consequent.isBlockStatement()) return false;

	const references = binding.referencePaths.filter((reference) =>
		reference.isIdentifier({ name: id.node.name }) &&
		nodePathIsAttached(reference)
	) as NodePath<t.Identifier>[];
	const plans: BranchArrayRegionPlan[] = [];
	const consequentPlan = planBranchArrayRegion(
		consequent.get('body') as NodePath<t.Statement>[],
		id.node.name,
		references,
	);
	if (!consequentPlan) return false;
	plans.push(consequentPlan);

	const alternate = branch.get('alternate');
	if (alternate.node) {
		if (!alternate.isBlockStatement()) return false;
		const alternatePlan = planBranchArrayRegion(
			alternate.get('body') as NodePath<t.Statement>[],
			id.node.name,
			references,
		);
		if (!alternatePlan) return false;
		plans.push(alternatePlan);
	} else {
		if (!statementBranchAlwaysTerminates(consequent.node)) return false;
		const fallthroughPlan = planBranchArrayRegion(
			siblings.slice(branchIndex + 1),
			id.node.name,
			references,
		);
		if (!fallthroughPlan) return false;
		plans.push(fallthroughPlan);
	}

	const consumedReferences = new Set(
		plans.flatMap((plan) => [...plan.consumedReferences]),
	);
	if (
		references.some((reference) => !consumedReferences.has(reference.node))
	) return false;

	for (const plan of plans) {
		plan.terminal.replaceWith(plan.expression);
	}
	for (const plan of plans) {
		for (const statement of plan.protocol) statement.remove();
	}
	initializer.remove();
	if (isAssignment) {
		removeGeneratedDeclarator(binding.path);
	}
	return true;
}

/**
 * Fold an array construction whose bytecode mutation protocol is duplicated
 * across mutually exclusive `if` arms. Each arm is planned independently and
 * the edit commits only when every reference to the shared fresh array is
 * consumed.
 */
export function inlineBranchArrayConstructionsToFixpoint(
	root: t.File,
): number {
	let total = 0;
	let changed = 0;
	do {
		changed = 0;
		traverse(root, {
			ExpressionStatement: {
				exit(path) {
					if (!inlineBranchArrayConstruction(path)) return;
					changed++;
					total++;
					path.stop();
				},
			},
			VariableDeclaration: {
				exit(path) {
					if (!inlineBranchArrayConstruction(path)) return;
					changed++;
					total++;
					path.stop();
				},
			},
		});
		traverse.cache.clear();
	} while (changed > 0);
	return total;
}
/**
 * Recover `receiver.method(args)` from Hermes' explicit receiver protocols
 * inside a composed predicate sequence:
 *
 *     method = receiver.property
 *     result = method.call(receiver, ...args)
 *
 * or, for a source call containing spread arguments:
 *
 *     method = receiver.property
 *     args = [...values]
 *     result = HermesInternal.apply(method, args, receiver)
 *
 * The method binding must be private to the call. Ordered generated argument
 * setup is folded at its original position. When an adjacent receiver
 * assignment supplies both the member lookup and explicit receiver, it is
 * folded too, evaluating its RHS once.
 */
export function inlineSequenceMemberCalls(
	path: NodePath<t.SequenceExpression>,
): number {
	let total = 0;

	while (true) {
		const expressions = path.get('expressions') as NodePath<t.Expression>[];
		let changed = false;

		for (let index = 0; index < expressions.length - 1; index++) {
			const methodAssignment = expressions[index];
			if (
				!methodAssignment.isAssignmentExpression({ operator: '=' })
			) continue;
			const methodId = methodAssignment.get('left');
			const member = methodAssignment.get('right');
			if (
				!methodId.isIdentifier() ||
				!/^r\d+_\d+$/.test(methodId.node.name) ||
				!member.isMemberExpression() ||
				!member.get('object').isIdentifier()
			) continue;

			const receiverRef = member.get('object') as NodePath<t.Identifier>;
			const receiverName = receiverRef.node.name;
			let candidate: NodePath<t.CallExpression> | null = null;
			let consumerIndex = -1;
			let protocol: 'call' | 'apply' | null = null;
			for (
				let searchIndex = index + 1;
				searchIndex < expressions.length;
				searchIndex++
			) {
				const expression = expressions[searchIndex]!;
				const possible = expression.isCallExpression()
					? expression
					: expression.isAssignmentExpression({ operator: '=' }) &&
							expression.get('right').isCallExpression()
					? expression.get('right')
					: null;
				if (possible?.isCallExpression()) {
					const callee = possible.get('callee');
					const possibleArgs = possible.get('arguments');
					if (
						callee.isMemberExpression({ computed: false }) &&
						callee.get('property').isIdentifier({ name: 'call' }) &&
						callee.get('object').isIdentifier({
							name: methodId.node.name,
						})
					) {
						candidate = possible;
						protocol = 'call';
						consumerIndex = searchIndex;
						break;
					}
					if (
						callee.matchesPattern('HermesInternal.apply') &&
						possibleArgs.length === 3 &&
						possibleArgs[0].isIdentifier({
							name: methodId.node.name,
						})
					) {
						candidate = possible;
						protocol = 'apply';
						consumerIndex = searchIndex;
						break;
					}
				}
				if (
					!expression.isAssignmentExpression({ operator: '=' }) ||
					!expression.get('left').isIdentifier() ||
					!/^r\d+_\d+$/.test(
						(expression.node.left as t.Identifier).name,
					)
				) break;
			}
			if (!candidate || !protocol || consumerIndex < 0) continue;

			const args = candidate.get('arguments');
			let methodReference: t.Node;
			let explicitReceiver: t.Node;
			let callArguments = candidate.node.arguments.slice(1);
			if (protocol === 'call') {
				const outerCallee = candidate.get('callee');
				if (!outerCallee.isMemberExpression()) continue;
				const methodObject = outerCallee.get('object');
				if (!methodObject.isIdentifier()) continue;
				if (
					args.length === 0 ||
					!args[0].isIdentifier({ name: receiverName })
				) continue;
				methodReference = methodObject.node;
				explicitReceiver = args[0].node;
			} else {
				if (
					args.length !== 3 ||
					!args[0].isIdentifier({ name: methodId.node.name }) ||
					!args[2].isIdentifier({ name: receiverName })
				) continue;
				methodReference = args[0].node;
				explicitReceiver = args[2].node;
				callArguments = candidate.node.arguments.slice(1, 2);
			}

			const methodBinding = path.scope.getBinding(methodId.node.name);
			if (
				!methodBinding?.path.isVariableDeclarator() ||
				methodBinding.path.node.init != null ||
				methodBinding.constantViolations.length !== 1 ||
				methodBinding.constantViolations[0]?.node !==
					methodAssignment.node ||
				methodBinding.referencePaths.length !== 1 ||
				methodBinding.referencePaths[0]?.node !== methodReference
			) continue;

			const setup: {
				assignment: NodePath<t.AssignmentExpression>;
				declarator: NodePath<t.VariableDeclarator>;
				reference: NodePath<t.Identifier>;
			}[] = [];
			let previousArgumentIndex = -1;
			let setupIsSafe = true;
			const setupCallArguments = callArguments;
			for (
				const setupPath of expressions.slice(index + 1, consumerIndex)
			) {
				if (
					!setupPath.isAssignmentExpression({ operator: '=' }) ||
					!setupPath.get('left').isIdentifier() ||
					!t.isExpression(setupPath.node.right)
				) {
					setupIsSafe = false;
					break;
				}
				const setupName = (setupPath.node.left as t.Identifier).name;
				if (!/^r\d+_\d+$/.test(setupName)) {
					setupIsSafe = false;
					break;
				}
				const setupBinding = path.scope.getBinding(setupName);
				if (
					!setupBinding?.path.isVariableDeclarator() ||
					setupBinding.path.node.init != null ||
					setupBinding.constantViolations.length !== 1 ||
					setupBinding.constantViolations[0]?.node !==
						setupPath.node ||
					setupBinding.referencePaths.length !== 1
				) {
					setupIsSafe = false;
					break;
				}
				const occurrenceCount = setupCallArguments.reduce(
					(count, argument) =>
						count +
						(t.isNode(argument)
							? generatedIdentifierUseCount(argument, setupName)
							: 0),
					0,
				);
				const argumentIndex = setupCallArguments.findIndex((argument) =>
					t.isNode(argument) &&
					generatedIdentifierUseCount(argument, setupName) > 0
				);
				if (
					occurrenceCount !== 1 ||
					argumentIndex <= previousArgumentIndex
				) {
					setupIsSafe = false;
					break;
				}
				const reference = setupBinding.referencePaths[0]!;
				let owner: NodePath | null = reference;
				while (owner && owner !== candidate) owner = owner.parentPath;
				if (!owner) {
					setupIsSafe = false;
					break;
				}
				setup.push({
					assignment: setupPath as NodePath<t.AssignmentExpression>,
					declarator: setupBinding.path,
					reference: reference as NodePath<t.Identifier>,
				});
				previousArgumentIndex = argumentIndex;
			}
			if (!setupIsSafe) continue;

			let receiverInit: t.Expression = t.identifier(receiverName);
			let receiverDeclarator: NodePath<t.VariableDeclarator> | null =
				null;
			let receiverAssignment: NodePath<t.AssignmentExpression> | null =
				null;
			const previous = expressions[index - 1];
			if (
				previous?.isAssignmentExpression({ operator: '=' }) &&
				previous.get('left').isIdentifier({ name: receiverName }) &&
				t.isExpression(previous.node.right)
			) {
				const receiverBinding = path.scope.getBinding(receiverName);
				const explicitReceiverRef = explicitReceiver;
				if (
					receiverBinding?.path.isVariableDeclarator() &&
					receiverBinding.path.node.init == null &&
					receiverBinding.constantViolations.length === 1 &&
					receiverBinding.constantViolations[0]?.node ===
						previous.node &&
					receiverBinding.referencePaths.length === 2 &&
					receiverBinding.referencePaths.every((reference) =>
						reference.node === receiverRef.node ||
						reference.node === explicitReceiverRef
					)
				) {
					receiverInit = previous.node.right;
					receiverDeclarator = receiverBinding.path;
					receiverAssignment = previous;
				}
			}

			let recoveredApplyArguments:
				| (t.Expression | t.SpreadElement)[]
				| null = null;
			if (protocol === 'apply') {
				let argumentArray = candidate.node.arguments[1];
				if (t.isIdentifier(argumentArray)) {
					const setupArgument = setup.find((value) =>
						value.reference.node === argumentArray
					);
					if (setupArgument) {
						argumentArray = setupArgument.assignment.node.right;
					}
				}
				if (!t.isArrayExpression(argumentArray)) continue;
				recoveredApplyArguments = [];
				for (const element of argumentArray.elements) {
					if (
						!t.isExpression(element) && !t.isSpreadElement(element)
					) {
						recoveredApplyArguments = null;
						break;
					}
					recoveredApplyArguments.push(t.cloneNode(element, true));
				}
				if (!recoveredApplyArguments) continue;
			}

			for (const value of setup) {
				value.reference.replaceWith(
					t.cloneNode(value.assignment.node.right, true),
				);
			}
			const directMember = t.cloneNode(member.node, true);
			directMember.object = t.cloneNode(receiverInit, true);
			candidate.node.callee = directMember;
			candidate.node.arguments = protocol === 'call'
				? candidate.node.arguments.slice(1)
				: recoveredApplyArguments!;

			const removed = new Set<t.Node>([methodAssignment.node]);
			if (receiverAssignment) removed.add(receiverAssignment.node);
			for (const value of setup) removed.add(value.assignment.node);
			path.node.expressions = path.node.expressions.filter((expression) =>
				!removed.has(expression)
			);
			removeGeneratedDeclarator(methodBinding.path);
			if (receiverDeclarator) {
				removeGeneratedDeclarator(receiverDeclarator);
			}
			for (const value of setup) {
				removeGeneratedDeclarator(value.declarator);
			}
			total++;
			changed = true;
			break;
		}

		if (!changed) return total;
	}
}

function inlineOneSequenceArrayConstruction(
	path: NodePath<t.SequenceExpression>,
): number {
	if (sequenceIsInsideHandledRegion(path)) return 0;
	const expressions = path.get('expressions') as NodePath<t.Expression>[];

	for (let start = 0; start < expressions.length - 1; start++) {
		const assignment = expressions[start];
		if (!assignment.isAssignmentExpression({ operator: '=' })) continue;
		const target = assignment.get('left');
		const init = assignment.get('right');
		if (
			!target.isIdentifier() ||
			!/^r\d+_\d+$/.test(target.node.name) ||
			!init.isArrayExpression() ||
			init.node.elements.some((element) => t.isSpreadElement(element))
		) continue;

		const targetName = target.node.name;
		const targetBinding = path.scope.getBinding(targetName);
		if (
			!targetBinding?.path.isVariableDeclarator() ||
			targetBinding.path.node.init != null ||
			targetBinding.constantViolations.length !== 1 ||
			targetBinding.constantViolations[0]?.node !== assignment.node ||
			targetBinding.referencePaths.some((reference) =>
				referenceCrossesFunctionBoundary(
					reference,
					targetBinding.scope.path,
				)
			)
		) continue;

		const segments: (t.Expression | t.SpreadElement | null)[] = [
			...init.node.elements,
		];
		let offset: ArrayOffset = {
			base: null,
			delta: segments.length,
		};
		const capturedOffsets: CapturedSequenceArrayOffset[] = [];
		const protocolNodes = new Set<t.Node>();
		const consumed = new Set<number>();
		let pending: NodePath<t.Expression>[] = [];
		let spreadCount = 0;
		let terminated = false;

		for (let index = start + 1; index < expressions.length; index++) {
			const expression = expressions[index];
			const spread = analyseArraySpreadExpression(
				expression,
				targetName,
				true,
			);
			if (
				!spread ||
				!arrayOffsetMatches(offset, spread.startIndex)
			) {
				pending.push(expression);
				continue;
			}

			if (
				pending.some((operand) =>
					generatedIdentifierUseCount(operand.node, targetName) > 0 ||
					capturedOffsets.some(({ name }) =>
						generatedIdentifierUseCount(operand.node, name) > 0
					)
				)
			) break;

			const iterables = [...spread.iterables];
			if (pending.length > 0) {
				iterables[0] = t.sequenceExpression([
					...pending.map((operand) => operand.node),
					iterables[0]!,
				]);
				for (const operand of pending) {
					consumed.add(operand.key as number);
				}
				pending = [];
			}
			for (const iterable of iterables) {
				segments.push(t.spreadElement(iterable));
			}
			if (spread.trailingValue) segments.push(spread.trailingValue);
			protocolNodes.add(expression.node);
			consumed.add(index);
			spreadCount += spread.iterables.length;

			if (spread.offsetVar) {
				const binding = path.scope.getBinding(spread.offsetVar);
				if (
					!binding?.path.isVariableDeclarator() ||
					binding.path.node.init != null ||
					binding.constantViolations.length !== 1 ||
					binding.constantViolations[0]?.node !== expression.node
				) break;
				capturedOffsets.push({
					name: spread.offsetVar,
					assignment: expression.node as t.AssignmentExpression,
					declarator: binding.path,
				});
				offset = { base: spread.offsetVar, delta: 0 };
				continue;
			}

			terminated = true;
			break;
		}

		if (!terminated || spreadCount === 0) continue;
		if (
			capturedOffsets.some(({ name, assignment, declarator }) => {
				const binding = path.scope.getBinding(name);
				return !binding ||
					binding.path !== declarator ||
					binding.constantViolations.length !== 1 ||
					binding.constantViolations[0]?.node !== assignment ||
					binding.referencePaths.length !== 1 ||
					binding.referencePaths.some((reference) =>
						!nodePathIsWithinAny(reference, protocolNodes)
					);
			})
		) continue;

		assignment.node.right = t.arrayExpression(segments);
		path.node.expressions = path.node.expressions.filter(
			(_expression, index) => !consumed.has(index),
		);
		for (const { declarator } of capturedOffsets) {
			removeGeneratedDeclarator(declarator);
		}
		return spreadCount;
	}

	return 0;
}

/**
 * Recover array literals built inside a predicate `SequenceExpression`.
 *
 * Recursive CFG emission keeps the sequence under its original short-circuit
 * arm. Intervening operands are nested into the following spread iterable so
 * their evaluation remains between the same two spread operations.
 *
 * The caller owns scope crawling; this is part of the sequence-assignment pass
 * so both transformations share one traversal.
 */
export function inlineSequenceArrayConstruction(
	path: NodePath<t.SequenceExpression>,
): number {
	let total = 0;
	let changed = 0;
	do {
		changed = inlineOneSequenceArrayConstruction(path);
		total += changed;
	} while (changed > 0 && path.node.expressions.length > 1);
	return total;
}

/**
 * Fold object/array construction chains until statement-order dependencies no
 * longer expose another candidate. A consumer declaration is visited before a
 * later source buffer in the same traversal, so one pass can inline the source
 * while necessarily missing the now-unblocked consumer.
 */
export function inlineObjectConstructionsToFixpoint(root: t.File): number {
	let total = 0;
	let changed = 0;
	do {
		traverse(root, {
			Program(path) {
				path.scope.crawl();
				path.stop();
			},
		});
		changed = 0;
		traverse(root, {
			ExpressionStatement: {
				exit(path) {
					if (
						!inlineBareObjectExpressionIntoNextGeneratedReference(
							path,
						) &&
						!inlineObjectConstruction(path)
					) return;
					changed++;
					total++;
				},
			},
			VariableDeclaration: {
				exit(path) {
					if (
						!inlineSingleStringKeyObject(path) &&
						!inlineObjectConstruction(path)
					) return;
					changed++;
					total++;
				},
			},
		});
		traverse.cache.clear();
	} while (changed > 0);
	return total;
}

function lowerResidualArraySpreadStatement(
	statement: NodePath<t.Statement>,
): boolean {
	let call: NodePath<t.CallExpression>;
	let capturedOffset: t.Identifier | null = null;
	if (statement.isExpressionStatement()) {
		const expression = statement.get('expression');
		if (!expression.isCallExpression()) return false;
		call = expression;
	} else if (statement.isVariableDeclaration({ kind: 'const' })) {
		const declarations = statement.get('declarations');
		if (declarations.length !== 1) return false;
		const id = declarations[0].get('id');
		const init = declarations[0].get('init');
		if (!id.isIdentifier() || !init.isCallExpression()) return false;
		capturedOffset = id.node;
		call = init;
	} else {
		return false;
	}

	const args = call.get('arguments');
	if (args.length !== 3 || !args[0].isIdentifier()) return false;
	const targetName = args[0].node.name;
	const spread = matchArraySpreadCall(call, targetName);
	if (
		!spread || !t.isNumericLiteral(spread.startIndex) ||
		!Number.isSafeInteger(spread.startIndex.value) ||
		spread.startIndex.value < 0 ||
		spread.iterables.some((iterable) =>
			nodeReferencesIdentifier(iterable, targetName)
		)
	) return false;
	const startIndex = spread.startIndex.value;

	const binding = statement.scope.getBinding(targetName);
	if (
		!binding?.path.isVariableDeclarator() ||
		binding.referencePaths.some((reference) =>
			referenceCrossesFunctionBoundary(reference, binding.scope.path)
		)
	) return false;
	const targetDeclaration = binding.path.parentPath;
	if (
		!targetDeclaration.isVariableDeclaration({ kind: 'const' }) ||
		targetDeclaration.node.declarations.length !== 1 ||
		targetDeclaration.parentPath?.node !== statement.parentPath?.node
	) return false;
	const targetInit = binding.path.get('init');
	const isCapacityArray = targetInit.isNewExpression() &&
		targetInit.get('callee').isIdentifier({ name: 'Array' }) &&
		targetInit.get('arguments').length === 1 &&
		targetInit.get('arguments.0').isNumericLiteral();
	if (!isCapacityArray && !targetInit.isArrayExpression()) return false;

	const initialized = new Set<number>();
	if (targetInit.isArrayExpression()) {
		for (let index = 0; index < targetInit.node.elements.length; index++) {
			if (targetInit.node.elements[index] === null) continue;
			if (index >= startIndex) return false;
			initialized.add(index);
		}
	}

	let current = targetDeclaration.getNextSibling();
	while (current.node && current.node !== statement.node) {
		if (!current.isStandardized()) return false;
		const container = new Set<t.Node>([current.node]);
		const references = binding.referencePaths.filter((reference) =>
			nodePathIsAttached(reference) &&
			nodePathIsWithinAny(reference, container)
		);
		if (references.length > 0) {
			const write = analyseObjectAssign(current, targetName);
			if (
				!write || !t.isNumericLiteral(write.property) ||
				!Number.isSafeInteger(write.property.value) ||
				write.property.value < 0 ||
				write.property.value >= startIndex ||
				references.length !== 1 ||
				references[0].node !== write.ref.node
			) return false;
			initialized.add(write.property.value);
		}
		current = current.getNextSibling();
	}
	if (current.node !== statement.node) return false;
	for (let index = 0; index < startIndex; index++) {
		if (!initialized.has(index)) return false;
	}

	const elements: (t.Expression | t.SpreadElement)[] = [];
	for (let index = 0; index < startIndex; index++) {
		elements.push(t.memberExpression(
			t.identifier(targetName),
			t.numericLiteral(index),
			true,
		));
	}
	for (const iterable of spread.iterables) {
		elements.push(t.spreadElement(t.cloneNode(iterable, true)));
	}
	const replacement = t.assignmentExpression(
		'=',
		t.identifier(targetName),
		t.arrayExpression(elements),
	);

	(targetDeclaration.node as t.VariableDeclaration).kind = 'let';
	if (capturedOffset === null) {
		(statement.get('expression') as NodePath<t.Expression>).replaceWith(
			replacement,
		);
		return true;
	}

	if (!statement.isVariableDeclaration()) return false;
	const offsetDeclaration = t.cloneNode(statement.node, true);
	offsetDeclaration.declarations[0].init = t.memberExpression(
		t.identifier(targetName),
		t.identifier('length'),
	);
	statement.replaceWithMultiple([
		t.expressionStatement(replacement),
		offsetDeclaration,
	]);
	return true;
}

/**
 * Replace residual array-spread intrinsics with a reassignment expressed in
 * source syntax. Prefix values stay in the fresh accumulator until the spread
 * point, preserving evaluation order across intervening setup statements.
 */
export function lowerResidualArraySpreadCalls(root: t.File): number {
	traverse(root, {
		Program(path) {
			path.scope.crawl();
			path.stop();
		},
	});
	let lowered = 0;
	traverse(root, {
		ExpressionStatement: {
			exit(path) {
				if (!lowerResidualArraySpreadStatement(path)) return;
				lowered++;
			},
		},
		VariableDeclaration: {
			exit(path) {
				if (!lowerResidualArraySpreadStatement(path)) return;
				lowered++;
			},
		},
	});
	return lowered;
}

interface ToPropertyKeyExtraction {
	argument: t.Expression;
	temporary?: NodePath<t.VariableDeclaration>;
}

interface NamedFunctionDefine {
	ref?: NodePath;
	property: t.Expression;
	value: t.CallExpression;
	toRemove: NodePath[];
	literalProperty?: {
		object: t.ObjectExpression;
		index: number;
	};
}

function extractToPropertyKeyArgument(
	node: t.Node,
	scope?: NodePath['scope'],
): ToPropertyKeyExtraction | null {
	if (t.isCallExpression(node)) {
		if (
			!t.isV8IntrinsicIdentifier(node.callee, { name: 'ToPropertyKey' })
		) {
			return null;
		}
		const [argument] = node.arguments;
		if (node.arguments.length !== 1 || !t.isExpression(argument)) {
			return null;
		}
		return { argument };
	}

	if (!scope || !t.isIdentifier(node)) return null;
	const binding = scope.getBinding(node.name);
	if (!binding?.constant) return null;
	const declarator = binding.path;
	if (!declarator.isVariableDeclarator()) return null;
	const declaration = declarator.parentPath;
	if (
		!declaration.isVariableDeclaration({ kind: 'const' }) ||
		declaration.node.declarations.length !== 1
	) return null;
	const id = declarator.get('id');
	if (!id.isIdentifier({ name: node.name })) return null;
	const init = declarator.node.init;
	if (!init) return null;
	const extracted = extractToPropertyKeyArgument(init);
	if (!extracted) return null;
	return {
		argument: extracted.argument,
		temporary: declaration as NodePath<t.VariableDeclaration>,
	};
}

function removableSharedToPropertyKeyTemporary(
	functionProperty: NodePath,
	property: t.Node,
	functionName: ToPropertyKeyExtraction | null,
	propertyName: ToPropertyKeyExtraction | null,
): NodePath<t.VariableDeclaration> | null {
	const temporary = functionName?.temporary;
	if (!temporary || propertyName?.temporary?.node !== temporary.node) {
		return null;
	}
	const declarator = temporary.get('declarations.0');
	const id = declarator.get('id');
	if (!id.isIdentifier()) return null;
	const binding = temporary.scope.getBinding(id.node.name);
	if (!binding || binding.referencePaths.length !== 2) return null;
	if (
		!binding.referencePaths.some((ref) =>
			ref.node === functionProperty.node
		) ||
		!binding.referencePaths.some((ref) => ref.node === property)
	) return null;
	return temporary;
}

function objectLiteralNamedFunctionProperty(
	object: t.ObjectExpression,
	functionBinding: { referencePaths: NodePath[] },
	functionName: ToPropertyKeyExtraction,
	scope: NodePath['scope'],
): {
	object: t.ObjectExpression;
	index: number;
	property: t.ObjectProperty;
	key: ToPropertyKeyExtraction;
} | null {
	for (let index = 0; index < object.properties.length; index++) {
		const candidate = object.properties[index];
		if (!t.isObjectProperty(candidate) || !candidate.computed) continue;
		if (
			!functionBinding.referencePaths.some((ref) =>
				ref.node === candidate.value
			)
		) continue;
		const key = extractToPropertyKeyArgument(candidate.key, scope);
		if (!key) continue;
		if (
			JSON.stringify(comparableAst(functionName.argument)) !==
				JSON.stringify(comparableAst(key.argument))
		) continue;
		return { object, index, property: candidate, key };
	}
	return null;
}

function extractNamedFunctionDefine(
	decn: NodePath<t.VariableDeclaration>,
	targetName?: string,
): NamedFunctionDefine | undefined {
	const assign = extractRegisterAssign(decn);
	if (!assign) return;

	const { id, init } = assign;
	const binding = decn.scope.getBinding(id.node.name);
	if (!binding?.constant) return;
	if (binding.referencePaths.length !== 2) return;

	const setFunctionName = decn.getNextSibling();
	if (!setFunctionName.isExpressionStatement()) return;
	const call = setFunctionName.get('expression');
	if (
		!call.isCallExpression() ||
		!call.get('callee').matchesPattern('HermesInternal.setFunctionName')
	) return;
	const args = call.get('arguments');
	if (args.length !== 3) return;
	const [closure, functionProperty] = args;
	if (!binding.referencePaths.includes(closure)) return;

	const functionName = extractToPropertyKeyArgument(
		functionProperty.node,
		functionProperty.scope,
	);
	if (!functionName) return;

	const define = setFunctionName.getNextSibling();
	if (define.isExpressionStatement()) {
		const objectAssign = define.get('expression');
		if (!objectAssign.isAssignmentExpression({ operator: '=' })) return;

		const target = objectAssign.get('left');
		const value = objectAssign.get('right');
		if (binding.referencePaths.includes(value)) {
			if (!target.isMemberExpression({ computed: true })) return;
			const property = target.get('property');
			const propertyName = extractToPropertyKeyArgument(
				property.node,
				property.scope,
			);
			if (!propertyName) return;

			if (
				JSON.stringify(comparableAst(functionName.argument)) !==
					JSON.stringify(comparableAst(propertyName.argument))
			) return;

			const ref = target.get('object');
			if (targetName) {
				if (!ref.isIdentifier({ name: targetName })) return;
			}
			const toRemove: NodePath[] = [setFunctionName, define];
			const keyTemporary = removableSharedToPropertyKeyTemporary(
				functionProperty,
				property.node,
				functionName,
				propertyName,
			);
			if (keyTemporary) toRemove.push(keyTemporary);
			return {
				ref,
				property: t.cloneNode(propertyName.argument, true),
				value: t.callExpression(
					t.v8IntrinsicIdentifier('asNamedObjectMethod'),
					[init.node],
				),
				toRemove,
			};
		}

		if (!targetName && value.isObjectExpression()) {
			const literalProperty = objectLiteralNamedFunctionProperty(
				value.node,
				binding,
				functionName,
				value.scope,
			);
			if (!literalProperty) return;
			const toRemove: NodePath[] = [setFunctionName];
			const keyTemporary = removableSharedToPropertyKeyTemporary(
				functionProperty,
				literalProperty.property.key,
				functionName,
				literalProperty.key,
			);
			if (keyTemporary) toRemove.push(keyTemporary);
			return {
				literalProperty: {
					object: literalProperty.object,
					index: literalProperty.index,
				},
				property: t.cloneNode(literalProperty.key.argument, true),
				value: t.callExpression(
					t.v8IntrinsicIdentifier('asNamedObjectMethod'),
					[init.node],
				),
				toRemove,
			};
		}
		return;
	}

	if (!targetName && define.isVariableDeclaration()) {
		for (const declaration of define.get('declarations')) {
			const value = declaration.get('init');
			if (!value.isObjectExpression()) continue;
			const literalProperty = objectLiteralNamedFunctionProperty(
				value.node,
				binding,
				functionName,
				value.scope,
			);
			if (!literalProperty) continue;
			const toRemove: NodePath[] = [setFunctionName];
			const keyTemporary = removableSharedToPropertyKeyTemporary(
				functionProperty,
				literalProperty.property.key,
				functionName,
				literalProperty.key,
			);
			if (keyTemporary) toRemove.push(keyTemporary);
			return {
				literalProperty: {
					object: literalProperty.object,
					index: literalProperty.index,
				},
				property: t.cloneNode(literalProperty.key.argument, true),
				value: t.callExpression(
					t.v8IntrinsicIdentifier('asNamedObjectMethod'),
					[init.node],
				),
				toRemove,
			};
		}
	}
}

function inlineFoldedNamedFunctionDefine(
	decn: NodePath<t.VariableDeclaration>,
) {
	const method = extractNamedFunctionDefine(decn);
	if (!method?.literalProperty) return false;
	const init = extractRegisterAssign(decn)?.init;
	if (!init?.isFunctionExpression()) return false;
	method.literalProperty.object.properties[method.literalProperty.index] = t
		.objectMethod(
			'method',
			method.property,
			init.node.params,
			init.node.body,
			true,
			init.node.generator,
			init.node.async,
		);
	for (const path of method.toRemove) path.remove();
	decn.remove();
	return true;
}

export function invertTest(expr: t.Expression): t.Expression {
	if (t.isUnaryExpression(expr, { operator: '!' })) {
		return <t.Expression> t.cloneNode(expr.argument, true);
	}

	if (
		t.isLogicalExpression(expr) &&
		(expr.operator === '&&' || expr.operator === '||')
	) {
		return t.logicalExpression(
			expr.operator === '&&' ? '||' : '&&',
			invertTest(t.cloneNode(expr.left, true) as t.Expression),
			invertTest(t.cloneNode(expr.right, true)),
		);
	}

	if (t.isBinaryExpression(expr, { operator: '===' })) {
		return <t.Expression> t.binaryExpression('!==', expr.left, expr.right);
	}

	if (t.isBinaryExpression(expr, { operator: '!==' })) {
		return <t.Expression> t.binaryExpression('===', expr.left, expr.right);
	}

	if (t.isBinaryExpression(expr, { operator: '==' })) {
		return <t.Expression> t.binaryExpression('!=', expr.left, expr.right);
	}

	if (t.isBinaryExpression(expr, { operator: '!=' })) {
		return <t.Expression> t.binaryExpression('==', expr.left, expr.right);
	}

	return t.unaryExpression('!', <t.Expression> t.cloneNode(expr, true), true);
}

/**
 * Whether re-running `invertTest` on `expr` would simplify it, in a way that is
 * valid wherever the enclosing `!expr` appears -- including a value position.
 *
 * Branch predicates are inverted while still a bare SSA register, so every rule
 * in `invertTest` misses and the `!` is materialized blind. Once register
 * inlining puts the defining expression underneath that `!`, this says whether
 * retrying is worthwhile.
 *
 * Two of `invertTest`'s rules are deliberately absent:
 *
 * - `!!x -> x`. Sound only in a boolean context, and the caller is a plain
 *   `UnaryExpression` visitor that also sees `return !!x` and `f(!!x)`. There
 *   `!!x` is a boolean coercion, so dropping it changes both value and type --
 *   `return !![]` would become `return []`. `invertTest` may keep the rule
 *   because it is only ever applied to branch predicates.
 * - relational operators. Hermes' `JNotLess` is `!lessOp(a, b)`, which is true
 *   for NaN, whereas `a >= b` is false. Flipping them would miscompile NaN.
 *
 * The remaining rules all yield a boolean from a boolean, so they are safe in
 * any position: `!(a === b)` and `a !== b` agree, and so do `!(a && b)` and
 * `!a || !b`.
 */
export function invertTestSimplifies(expr: t.Expression): boolean {
	if (
		t.isLogicalExpression(expr) &&
		(expr.operator === '&&' || expr.operator === '||')
	) return true;
	return t.isBinaryExpression(expr) &&
		(expr.operator === '===' || expr.operator === '!==' ||
			expr.operator === '==' || expr.operator === '!=');
}

/** Replace `else { if (...) ... }` with the equivalent `else if (...) ...`. */
export function flattenElseIfBlock(statement: t.IfStatement): boolean {
	const alternate = statement.alternate;
	if (
		!t.isBlockStatement(alternate) || alternate.body.length !== 1 ||
		!t.isIfStatement(alternate.body[0])
	) return false;
	statement.alternate = alternate.body[0];
	return true;
}

/**
 * Rotate a terminating guard at the start of one arm into a canonical
 * `if / else if / else` chain.
 *
 * `if (!a) { if (!b) return; valueB(); } else { valueA(); }` becomes
 * `if (a) valueA(); else if (b) valueB(); else return`.
 */
export function rotateTerminatingGuardIntoElseIf(
	statement: t.IfStatement,
): t.IfStatement | null {
	if (!statement.alternate || !t.isBlockStatement(statement.consequent)) {
		return null;
	}
	const [guard, ...fallthrough] = statement.consequent.body;
	if (
		!guard || !t.isIfStatement(guard) || guard.alternate != null ||
		fallthrough.length === 0 ||
		!statementBranchAlwaysTerminates(guard.consequent)
	) return null;

	return t.ifStatement(
		invertTest(t.cloneNode(statement.test, true)),
		t.cloneNode(statement.alternate, true),
		t.ifStatement(
			invertTest(t.cloneNode(guard.test, true)),
			t.blockStatement(fallthrough),
			t.cloneNode(guard.consequent, true),
		),
	);
}

function statementBranchAlwaysTerminates(statement: t.Statement): boolean {
	if (t.isReturnStatement(statement) || t.isThrowStatement(statement)) {
		return true;
	}
	if (t.isBlockStatement(statement)) {
		const last = statement.body.at(-1);
		return last != null && statementBranchAlwaysTerminates(last);
	}
	if (t.isIfStatement(statement) && statement.alternate) {
		return statementBranchAlwaysTerminates(statement.consequent) &&
			statementBranchAlwaysTerminates(statement.alternate);
	}
	return false;
}
