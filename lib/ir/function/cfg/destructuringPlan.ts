import * as t from '@babel/types';
import { isUndefinedNode } from '../../ast/utils.ts';

/**
 * Semantic source selection that precedes a destructuring pattern in a
 * defaulted parameter, e.g. `function f({ x } = makeDefault())`.
 */
export interface DestructuringSourceDefault {
	source: t.Identifier;
	defaultValue: t.Expression;
}

function undefinedComparison(
	test: t.Expression,
	sourceName: string,
	undefinedAliases: ReadonlySet<string>,
): 'undefined' | 'defined' | null {
	if (
		t.isUnaryExpression(test, { operator: '!' }) &&
		t.isExpression(test.argument)
	) {
		const inner = undefinedComparison(
			test.argument,
			sourceName,
			undefinedAliases,
		);
		return inner === 'undefined'
			? 'defined'
			: inner === 'defined'
			? 'undefined'
			: null;
	}
	if (!t.isBinaryExpression(test)) return null;
	const isUndefined = (candidate: t.Expression | t.PrivateName) =>
		t.isIdentifier(candidate) &&
		(candidate.name === 'undefined' ||
			undefinedAliases.has(candidate.name));
	const comparesUndefined =
		(t.isIdentifier(test.left, { name: sourceName }) &&
			isUndefined(test.right)) ||
		(isUndefined(test.left) &&
			t.isIdentifier(test.right, { name: sourceName }));
	if (!comparesUndefined) return null;
	if (test.operator === '===' || test.operator === '==') return 'undefined';
	if (test.operator === '!==' || test.operator === '!=') return 'defined';
	return null;
}

function defaultValueWithoutSourceReference(
	value: t.Expression,
	sourceName: string,
	undefinedAliases: ReadonlySet<string>,
): t.Expression | null {
	const comparison = undefinedComparison(value, sourceName, undefinedAliases);
	if (comparison === 'undefined') return t.booleanLiteral(true);
	if (comparison === 'defined') return t.booleanLiteral(false);
	if (identifierOccurrences(value, sourceName) === 0) {
		return t.cloneNode(value, true);
	}
	return null;
}

/**
 * Recognize the expression form produced after a parameter-default diamond is
 * lowered through a Phi. The raw parameter must occupy exactly the non-default
 * arm; callers separately prove that it has no uses outside this initializer.
 */
export function destructuringSourceDefault(
	init: t.Expression,
	sourceName: string,
	undefinedAliases: ReadonlySet<string> = new Set(['undefined']),
): DestructuringSourceDefault | null {
	if (!t.isConditionalExpression(init)) return null;
	const check = undefinedComparison(init.test, sourceName, undefinedAliases);
	if (
		check === 'undefined' &&
		t.isIdentifier(init.alternate, { name: sourceName })
	) {
		const defaultValue = defaultValueWithoutSourceReference(
			init.consequent,
			sourceName,
			undefinedAliases,
		);
		if (!defaultValue) return null;
		return {
			source: t.identifier(sourceName),
			defaultValue,
		};
	}
	if (
		check === 'defined' &&
		t.isIdentifier(init.consequent, { name: sourceName })
	) {
		const defaultValue = defaultValueWithoutSourceReference(
			init.alternate,
			sourceName,
			undefinedAliases,
		);
		if (!defaultValue) return null;
		return {
			source: t.identifier(sourceName),
			defaultValue,
		};
	}
	return null;
}

/** Identifiers proven to carry JavaScript's undefined value in this body. */
export function destructuringUndefinedAliases(node: t.Node): Set<string> {
	const aliases = new Set(['undefined']);
	t.traverseFast(node, (candidate) => {
		if (
			!t.isVariableDeclarator(candidate) ||
			!t.isIdentifier(candidate.id) || !candidate.init
		) return;
		if (isUndefinedNode(candidate.init)) aliases.add(candidate.id.name);
	});
	return aliases;
}

export function identifierOccurrences(node: t.Node, name: string): number {
	let count = 0;
	t.traverseFast(node, (candidate) => {
		if (t.isIdentifier(candidate, { name })) count++;
	});
	return count;
}

const DESTRUCTURING_PROTOCOL_INTRINSICS = new Set([
	'IteratorBegin',
	'IteratorNext',
	'IteratorNextValue',
	'IteratorNextWithDefault',
	'IteratorClose',
]);

/**
 * A clean Region may still contain the compiler protocol for an unrecovered
 * destructuring operation. Such an emission is structurally complete but not
 * semantically reduced, so it must not bypass the compatibility reducer.
 */
export function containsDestructuringProtocol(node: t.Node): boolean {
	let found = false;
	t.traverseFast(node, (candidate) => {
		if (found) return t.traverseFast.skip;
		if (
			t.isCallExpression(candidate) &&
			t.isV8IntrinsicIdentifier(candidate.callee) &&
			DESTRUCTURING_PROTOCOL_INTRINSICS.has(candidate.callee.name)
		) {
			found = true;
			return t.traverseFast.skip;
		}
		if (
			t.isCallExpression(candidate) &&
			t.isMemberExpression(candidate.callee, { computed: false }) &&
			t.isIdentifier(candidate.callee.object, {
				name: 'HermesInternal',
			}) &&
			t.isIdentifier(candidate.callee.property, {
				name: 'copyDataProperties',
			})
		) {
			found = true;
			return t.traverseFast.skip;
		}
	});
	return found;
}
