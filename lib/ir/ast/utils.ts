import * as t from '@babel/types';
import { NodePath } from '@babel/traverse';
import { FunctionId } from '../../hbc/disassembly/instruction.ts';
export function nodePathIsAttached(path: NodePath): boolean {
	const target = path.node;
	let current: NodePath | null = path;
	let statement: NodePath | null = null;
	let root: NodePath = path;
	while (current) {
		if (current.removed || current.node == null) return false;
		if (
			current.container != null && current.key != null &&
			(current.container as unknown as Record<string | number, unknown>)[
					current.key
				] !== current.node
		) return false;
		if (!statement && current.isStatement()) statement = current;
		root = current;
		current = current.parentPath;
	}

	let found = false;
	t.traverseFast((statement ?? root).node, (node) => {
		if (node !== target) return;
		found = true;
		return t.traverseFast.skip;
	});
	return found;
}

export function extractFunctionRef(funcRef: t.Node): FunctionId | undefined {
	if (!t.isCallExpression(funcRef)) return;
	if (
		!t.isV8IntrinsicIdentifier(funcRef.callee, { name: 'getFunctionById' })
	) return;

	const index = funcRef.arguments[0];
	if (!t.isNumericLiteral(index)) return;

	return index.value;
}

/**
 * Environment-handle reads are stable within one function invocation. Unlike
 * `%Create*Environment`, cloning or discarding these lookups does not allocate
 * a runtime environment or expose an observable operation.
 */
export function isReadOnlyEnvironmentLookup(
	node: t.Node | null | undefined,
): node is t.CallExpression {
	return t.isCallExpression(node) &&
		t.isV8IntrinsicIdentifier(node.callee) &&
		[
			'GetParentEnvironment',
			'GetEnvironment',
			'GetClosureEnvironment',
		].includes(node.callee.name);
}

export function extractRegisterAssign(decn: NodePath<t.VariableDeclaration>) {
	if (decn.node.kind !== 'const') return;
	if (decn.node.declarations.length !== 1) return;
	const decl = decn.get('declarations.0');

	const id = decl.get('id');
	if (!id.isIdentifier()) return;
	const init = decl.get('init');
	if (!init.node) return;

	return {
		id,
		init,
	};
}

export function constIdentifierInit(scope: NodePath['scope'], name: string) {
	const binding = scope.getBinding(name);
	if (!binding?.constant) return;

	const path = binding.path;
	if (!path.isVariableDeclarator()) return;

	const parent = path.parentPath;
	if (!parent.isVariableDeclaration({ kind: 'const' })) return;

	const id = path.get('id');
	if (!id.isIdentifier({ name })) return;

	const init = path.get('init');
	if (!init.node) return;

	return init;
}

export function comparableAst(value: unknown, key?: string): unknown {
	if (
		[
			'loc',
			'start',
			'end',
			'extra',
			'leadingComments',
			'innerComments',
			'trailingComments',
		].includes(key ?? '')
	) return undefined;

	// A BigIntLiteral carries a native bigint, which JSON.stringify refuses to
	// serialize. Its decimal digits compare identically and do serialize.
	if (typeof value === 'bigint') return value.toString();

	if (Array.isArray(value)) return value.map((v) => comparableAst(v));
	if (value && typeof value === 'object') {
		if (
			t.isIdentifier(value as t.Node) &&
			/^(?:r\d+_\d+|e_\d+)$/.test((value as t.Identifier).name)
		) {
			return { type: 'Identifier', name: '$generated' };
		}

		// Normalize %getFunctionById(N) — two finalizer copies that capture closures
		// with different function IDs are still structurally equivalent.
		// TODO: narrow further by comparing exact bytecode?
		if (
			t.isCallExpression(value as t.Node) &&
			t.isV8IntrinsicIdentifier((value as t.CallExpression).callee, {
				name: 'getFunctionById',
			})
		) {
			return {
				type: 'CallExpression',
				callee: {
					type: 'V8IntrinsicIdentifier',
					name: 'getFunctionById',
				},
				arguments: [],
			};
		}

		const result: Record<string, unknown> = {};
		for (
			const [childKey, childValue] of Object.entries(value).toSorted((
				[a],
				[b],
			) => a.localeCompare(b))
		) {
			const comparable = comparableAst(childValue, childKey);
			if (comparable !== undefined) result[childKey] = comparable;
		}
		return result;
	}

	return value;
}

export function isUndefinedNode(node: t.Node | null | undefined) {
	return t.isIdentifier(node, { name: 'undefined' });
}
