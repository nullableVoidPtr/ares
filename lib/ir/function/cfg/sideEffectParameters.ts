import * as t from '@babel/types';
import type { StorageLocation } from '../../ast/alias.ts';
import { locationOf } from '../../ast/alias.ts';
import { isUndefinedNode } from '../../ast/utils.ts';
import type { IRFunction } from '../mod.ts';
import type {
	ParameterSlotPlan,
	ParameterSlotProvenance,
} from './parameterPlan.ts';

function singleDeclarator(statement: t.Statement | undefined) {
	if (
		!t.isVariableDeclaration(statement) ||
		statement.declarations.length !== 1
	) return;
	return statement.declarations[0];
}

function overflowLocation(
	node: t.Node,
	functionId: number,
): { jsIndex: number; location: StorageLocation } | undefined {
	const location = locationOf(node);
	if (
		location?.kind !== 'parameter' ||
		location.owner.functionId !== functionId ||
		location.parameter.form !== 'overflow' ||
		location.parameter.index < 1
	) return;
	return { jsIndex: location.parameter.index - 1, location };
}

function undefinedBranchSource(
	expression: t.Expression,
	functionId: number,
	overflowAliases: ReadonlyMap<
		string,
		{ jsIndex: number; location: StorageLocation }
	>,
	undefinedAliases: ReadonlySet<string>,
):
	| { jsIndex: number; location: StorageLocation; outcome: boolean }
	| undefined {
	let test = expression;
	let negated = false;
	while (t.isUnaryExpression(test, { operator: '!' })) {
		negated = !negated;
		test = test.argument;
	}
	if (
		!t.isBinaryExpression(test) ||
		(test.operator !== '===' && test.operator !== '==')
	) return;
	const isUndefined = (node: t.Node) => {
		return t.isIdentifier(node) &&
			(node.name === 'undefined' || undefinedAliases.has(node.name));
	};
	const overflow = (node: t.Node) =>
		overflowLocation(node, functionId) ??
			(t.isIdentifier(node) ? overflowAliases.get(node.name) : undefined);
	const source = isUndefined(test.left)
		? overflow(test.right)
		: isUndefined(test.right)
		? overflow(test.left)
		: undefined;
	if (!source) return;
	return { ...source, outcome: !negated };
}

function safeToDuplicate(expression: t.Expression): boolean {
	if (
		t.isIdentifier(expression) || t.isLiteral(expression) ||
		t.isThisExpression(expression)
	) return true;
	return t.isCallExpression(expression) &&
		t.isV8IntrinsicIdentifier(expression.callee) &&
		[
			'GetParentEnvironment',
			'GetEnvironment',
			'GetClosureEnvironment',
			'expectEnvironment',
		].includes(expression.callee.name) &&
		expression.arguments.every((argument) =>
			t.isExpression(argument) && safeToDuplicate(argument)
		);
}

function identifierUses(node: t.Node, name: string): number {
	let uses = 0;
	t.traverseFast(node, (candidate) => {
		if (t.isIdentifier(candidate, { name })) uses++;
	});
	return uses;
}

function substituteDefinitions(
	expression: t.Expression,
	definitions: ReadonlyMap<string, t.Expression>,
	useCounts: ReadonlyMap<string, number>,
	visiting = new Set<string>(),
): t.Expression | undefined {
	if (t.isIdentifier(expression)) {
		const value = definitions.get(expression.name);
		if (!value) return t.cloneNode(expression, true);
		if (visiting.has(expression.name)) return;
		if (
			(useCounts.get(expression.name) ?? 0) > 1 && !safeToDuplicate(value)
		) {
			return;
		}
		const next = new Set(visiting);
		next.add(expression.name);
		return substituteDefinitions(value, definitions, useCounts, next);
	}
	const clone = t.cloneNode(expression, true);
	let valid = true;
	const visit = (node: t.Node): void => {
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (let index = 0; index < value.length; index++) {
					const child = value[index];
					if (!t.isNode(child)) continue;
					if (t.isIdentifier(child) && definitions.has(child.name)) {
						const replacement = substituteDefinitions(
							child,
							definitions,
							useCounts,
							new Set(visiting),
						);
						if (!replacement) {
							valid = false;
							return;
						}
						(value as t.Node[])[index] = replacement;
					} else visit(child);
				}
			} else if (t.isNode(value)) {
				if (t.isIdentifier(value) && definitions.has(value.name)) {
					const replacement = substituteDefinitions(
						value,
						definitions,
						useCounts,
						new Set(visiting),
					);
					if (!replacement) {
						valid = false;
						return;
					}
					(node as unknown as Record<string, unknown>)[key] =
						replacement;
				} else visit(value);
			}
			if (!valid) return;
		}
	};
	visit(clone);
	return valid && t.isExpression(clone) ? clone : undefined;
}

/** Compose an unused `new Array(N); arr[i] = value` initializer arm. */
function composeArrayInitializer(
	body: readonly t.Statement[],
): t.ArrayExpression | undefined {
	const definitions = new Map<string, t.Expression>();
	let arrayName: string | undefined;
	let length: number | undefined;
	for (const statement of body) {
		const declaration = singleDeclarator(statement);
		if (!declaration || !t.isIdentifier(declaration.id)) continue;
		if (!t.isExpression(declaration.init)) return;
		definitions.set(declaration.id.name, declaration.init);
		if (
			t.isNewExpression(declaration.init) &&
			t.isIdentifier(declaration.init.callee, { name: 'Array' }) &&
			declaration.init.arguments.length === 1 &&
			t.isNumericLiteral(declaration.init.arguments[0]) &&
			Number.isSafeInteger(declaration.init.arguments[0].value) &&
			declaration.init.arguments[0].value >= 0
		) {
			if (arrayName != null) return;
			arrayName = declaration.id.name;
			length = declaration.init.arguments[0].value;
		}
	}
	if (arrayName == null || length == null) return;
	definitions.delete(arrayName);
	const elements: Array<t.Expression | null> = new Array(length).fill(null);
	const writes = new Set<t.Statement>();
	for (const statement of body) {
		if (
			!t.isExpressionStatement(statement) ||
			!t.isAssignmentExpression(statement.expression, {
				operator: '=',
			}) ||
			!t.isMemberExpression(statement.expression.left, {
				computed: true,
			}) ||
			!t.isIdentifier(statement.expression.left.object, {
				name: arrayName,
			}) ||
			!t.isNumericLiteral(statement.expression.left.property) ||
			!Number.isSafeInteger(statement.expression.left.property.value) ||
			statement.expression.left.property.value < 0 ||
			statement.expression.left.property.value >= length ||
			!t.isExpression(statement.expression.right)
		) continue;
		const index = statement.expression.left.property.value;
		if (elements[index] != null) return;
		elements[index] = statement.expression.right;
		writes.add(statement);
	}
	if (elements.some((element) => element == null)) return;
	if (
		body.some((statement) =>
			!writes.has(statement) && singleDeclarator(statement) == null
		)
	) return;
	const all = t.program(
		body.map((statement) => t.cloneNode(statement, true)),
	);
	const useCounts = new Map(
		[...definitions].map(([name]) => [name, identifierUses(all, name) - 1]),
	);
	const composed: t.Expression[] = [];
	for (const element of elements) {
		const replacement = substituteDefinitions(
			element!,
			definitions,
			useCounts,
		);
		if (!replacement) return;
		composed.push(replacement);
	}
	return t.arrayExpression(composed);
}

function locationOccurs(
	node: t.Node,
	location: StorageLocation,
): boolean {
	let occurs = false;
	t.traverseFast(node, (candidate) => {
		if (occurs) return t.traverseFast.skip;
		const found = locationOf(candidate);
		if (found && JSON.stringify(found) === JSON.stringify(location)) {
			occurs = true;
		}
	});
	return occurs;
}

/** Recover the unused array-valued default arm while its CFG is still intact. */
export function reduceSideEffectOnlyOverflowDefault(func: IRFunction): boolean {
	const entryAddress = func.entryAddress;
	const entry = func.blocks.get(entryAddress);
	if (
		!entry || entry.consequentAddresses.length !== 2 || !entry.branch ||
		func.cfgPredecessorsOf(entryAddress).size !== 0 ||
		func.exceptions.activeHandlersAtBlock(entryAddress).size !== 0
	) return false;
	const overflowAliases = new Map<
		string,
		{ jsIndex: number; location: StorageLocation }
	>();
	const undefinedAliases = new Set<string>();
	for (const statement of entry.body as t.Statement[]) {
		const declaration = singleDeclarator(statement);
		if (!declaration || !t.isIdentifier(declaration.id)) continue;
		const overflow = declaration.init &&
			overflowLocation(declaration.init, func.id);
		if (overflow) overflowAliases.set(declaration.id.name, overflow);
		if (isUndefinedNode(declaration.init)) {
			undefinedAliases.add(declaration.id.name);
		}
	}
	const source = undefinedBranchSource(
		entry.branch as t.Expression,
		func.id,
		overflowAliases,
		undefinedAliases,
	);
	if (!source) return false;
	const boundary = Math.max(func.paramCount - 1, 0);
	if (source.jsIndex < boundary) return false;
	const defaultAddress = entry.consequentAddresses[source.outcome ? 1 : 0];
	const continuationAddress =
		entry.consequentAddresses[source.outcome ? 0 : 1];
	const defaultBlock = func.blocks.get(defaultAddress);
	if (
		!defaultBlock || defaultBlock.branch ||
		defaultBlock.consequentAddresses.length !== 1 ||
		defaultBlock.consequentAddresses[0] !== continuationAddress ||
		func.cfgPredecessorsOf(defaultAddress).size !== 1 ||
		func.cfgPredecessorsOf(continuationAddress).size !== 2 ||
		!func.exceptions.activeHandlersEqual(entryAddress, defaultAddress)
	) return false;
	const defaultValue = composeArrayInitializer(
		defaultBlock.body as t.Statement[],
	);
	if (!defaultValue) return false;
	if (
		(entry.body as t.Statement[]).some((statement) => {
			const declaration = singleDeclarator(statement);
			return !declaration || !t.isIdentifier(declaration.id) ||
				!(locationOccurs(
					declaration.init ?? declaration.id,
					source.location,
				) ||
					isUndefinedNode(declaration.init));
		})
	) return false;
	for (const [address, block] of func.blocks) {
		if (address === entryAddress || address === defaultAddress) continue;
		if (
			(block.body as t.Statement[]).some((statement) =>
				locationOccurs(statement, source.location)
			) || block.branch &&
				locationOccurs(block.branch as t.Expression, source.location)
		) return false;
	}
	const continuationSSA = func.ssa.basicBlocks.get(continuationAddress);
	if (
		continuationSSA?.ssaInstructions.some((instruction) =>
			instruction.instruction === 'Phi' &&
			instruction.sources.has(defaultAddress)
		)
	) return false;

	const suffix: ParameterSlotPlan[] = [];
	for (let jsIndex = boundary; jsIndex <= source.jsIndex; jsIndex++) {
		const isDefault = jsIndex === source.jsIndex;
		const provenance: ParameterSlotProvenance = isDefault
			? 'overflow-default'
			: 'inferred-gap';
		suffix.push({
			hermesIndex: jsIndex + 1,
			jsIndex,
			binding: t.identifier(`_param_${func.id}_${jsIndex}_`),
			defaultValue: isDefault
				? defaultValue
				: jsIndex === boundary
				? t.identifier('undefined')
				: undefined,
			provenance,
			rawLocations: isDefault ? [structuredClone(source.location)] : [],
		});
		if (!isDefault) func.parameterPlan.telemetry.inferredGaps++;
	}
	func.parameterPlan.slots = [
		...func.parameterPlan.slots.filter((slot) => slot.jsIndex < boundary),
		...suffix,
	];
	func.parameterPlan.telemetry.sideEffectOnlyDefaultsRecovered++;
	entry.body = [];
	entry.branch = undefined;
	entry.consequentAddresses = [continuationAddress];
	func.markMergedBlocks(entryAddress, defaultAddress);
	func.rebuildPredecessorMap();
	return true;
}
