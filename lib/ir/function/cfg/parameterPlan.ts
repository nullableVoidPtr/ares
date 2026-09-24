import * as t from '@babel/types';
import traverse, { type Binding, type NodePath } from '@babel/traverse';
import type { StorageLocation } from '../../ast/alias.ts';
import { locationOf } from '../../ast/alias.ts';
import { invertTest } from '../../ast/expression.ts';
import { comparableAst, isUndefinedNode } from '../../ast/utils.ts';

export type ParameterSlotProvenance =
	| 'header'
	| 'overflow-default'
	| 'overflow-trailing'
	| 'inferred-gap';

export interface ParameterSlotPlan {
	hermesIndex: number;
	jsIndex: number;
	binding: t.Identifier | t.ArrayPattern | t.ObjectPattern;
	defaultValue?: t.Expression;
	provenance: ParameterSlotProvenance;
	rawLocations: StorageLocation[];
}

export interface RestParameterPlan {
	startIndex: number;
	binding: t.Identifier;
	provenance: 'copy-rest-intrinsic' | 'arguments-copy-loop';
}

export interface ParameterProjectionPlan {
	jsIndex: number;
	path: Array<{ key: t.Expression; computed: boolean }>;
	binding: t.Identifier;
}

export interface ParameterRecoveryDecline {
	reason: string;
	detail?: string;
}

export interface ParameterRecoveryTelemetry {
	overflowLoadsDiscovered: number;
	valueDefaultsRecovered: number;
	sideEffectOnlyDefaultsRecovered: number;
	trailingFormalsPromoted: number;
	inferredGaps: number;
	parameterPatternsAttached: number;
	patternsDeclinedSourceEscapes: number;
	restIntrinsicsRecovered: number;
	restLoopsRecovered: number;
	residualOverflowProvenance: number;
	compatibilityFallbackUses: number;
	declines: ParameterRecoveryDecline[];
}

export interface ParameterPlan {
	slots: ParameterSlotPlan[];
	rest?: RestParameterPlan;
	projections: ParameterProjectionPlan[];
	telemetry: ParameterRecoveryTelemetry;
}

function emptyTelemetry(): ParameterRecoveryTelemetry {
	return {
		overflowLoadsDiscovered: 0,
		valueDefaultsRecovered: 0,
		sideEffectOnlyDefaultsRecovered: 0,
		trailingFormalsPromoted: 0,
		inferredGaps: 0,
		parameterPatternsAttached: 0,
		patternsDeclinedSourceEscapes: 0,
		restIntrinsicsRecovered: 0,
		restLoopsRecovered: 0,
		residualOverflowProvenance: 0,
		compatibilityFallbackUses: 0,
		declines: [],
	};
}

function parameterBinding(
	param: t.Function['params'][number],
): t.Identifier | t.ArrayPattern | t.ObjectPattern | undefined {
	if (
		t.isIdentifier(param) || t.isArrayPattern(param) ||
		t.isObjectPattern(param)
	) {
		return param;
	}
	if (
		t.isAssignmentPattern(param) &&
		(t.isIdentifier(param.left) || t.isArrayPattern(param.left) ||
			t.isObjectPattern(param.left))
	) return param.left;
	return;
}

export function createParameterPlan(
	functionId: number,
	params: t.Function['params'],
): ParameterPlan {
	const slots: ParameterSlotPlan[] = [];
	for (let jsIndex = 0; jsIndex < params.length; jsIndex++) {
		const param = params[jsIndex];
		if (t.isRestElement(param)) break;
		const binding = parameterBinding(param);
		if (!binding) continue;
		slots.push({
			hermesIndex: jsIndex + 1,
			jsIndex,
			binding: t.cloneNode(binding, true),
			defaultValue: t.isAssignmentPattern(param) &&
					t.isExpression(param.right)
				? t.cloneNode(param.right, true)
				: undefined,
			provenance: 'header',
			rawLocations: [{
				kind: 'parameter',
				owner: { functionId },
				parameter: { index: jsIndex + 1, form: 'named' },
			}],
		});
	}
	const rest = params.find((param) =>
		t.isRestElement(param) && t.isIdentifier(param.argument)
	);
	return {
		slots,
		rest: rest && t.isRestElement(rest) && t.isIdentifier(rest.argument)
			? {
				startIndex: slots.length,
				binding: t.cloneNode(rest.argument, true),
				provenance: 'copy-rest-intrinsic',
			}
			: undefined,
		projections: [],
		telemetry: emptyTelemetry(),
	};
}

export function cloneParameterPlan(plan: ParameterPlan): ParameterPlan {
	return {
		slots: plan.slots.map((slot) => ({
			...slot,
			binding: t.cloneNode(slot.binding, true),
			defaultValue: slot.defaultValue == null
				? undefined
				: t.cloneNode(slot.defaultValue, true),
			rawLocations: slot.rawLocations.map((location) =>
				structuredClone(location)
			),
		})),
		rest: plan.rest == null ? undefined : {
			...plan.rest,
			binding: t.cloneNode(plan.rest.binding, true),
		},
		projections: (plan.projections ?? []).map((projection) => ({
			jsIndex: projection.jsIndex,
			path: projection.path.map((segment) => ({
				key: t.cloneNode(segment.key, true),
				computed: segment.computed,
			})),
			binding: t.cloneNode(projection.binding, true),
		})),
		telemetry: {
			...plan.telemetry,
			declines: plan.telemetry.declines.map((decline) => ({
				...decline,
			})),
		},
	};
}

export function materializeParameterPlan(
	plan: ParameterPlan,
): t.Function['params'] {
	const slots = [...plan.slots].sort((left, right) =>
		left.jsIndex - right.jsIndex
	);
	const params: t.Function['params'] = slots.map((slot) => {
		const binding = t.cloneNode(slot.binding, true);
		return slot.defaultValue == null ? binding : t.assignmentPattern(
			binding,
			t.cloneNode(slot.defaultValue, true),
		);
	});
	if (plan.rest) {
		params.splice(
			plan.rest.startIndex,
			params.length - plan.rest.startIndex,
			t.restElement(t.cloneNode(plan.rest.binding, true)),
		);
	}
	return params;
}

/** Absorb patterns/defaults attached by the shared destructuring fallbacks. */
export function synchronizeParameterPlan(
	plan: ParameterPlan,
	params: t.Function['params'],
): void {
	for (let jsIndex = 0; jsIndex < params.length; jsIndex++) {
		const param = params[jsIndex];
		if (t.isRestElement(param)) {
			if (t.isIdentifier(param.argument)) {
				plan.rest = {
					startIndex: jsIndex,
					binding: t.cloneNode(param.argument, true),
					provenance: plan.rest?.provenance ?? 'copy-rest-intrinsic',
				};
			}
			break;
		}
		const binding = parameterBinding(param);
		if (!binding) continue;
		const slot = plan.slots.find((candidate) =>
			candidate.jsIndex === jsIndex
		);
		if (!slot) continue;
		const wasPattern = t.isArrayPattern(slot.binding) ||
			t.isObjectPattern(slot.binding);
		const isPattern = t.isArrayPattern(binding) ||
			t.isObjectPattern(binding);
		if (!wasPattern && isPattern) {
			plan.telemetry.parameterPatternsAttached++;
		}
		slot.binding = t.cloneNode(binding, true);
		slot.defaultValue = t.isAssignmentPattern(param) &&
				t.isExpression(param.right)
			? t.cloneNode(param.right, true)
			: undefined;
	}
}

/** Replace the materialized signature after a generator priming adapter ran. */
export function adoptRecoveredFunctionParameters(
	plan: ParameterPlan,
	functionId: number,
	params: t.Function['params'],
): void {
	const recovered = createParameterPlan(functionId, params);
	for (const slot of recovered.slots) {
		const previous = plan.slots.find((candidate) =>
			candidate.jsIndex === slot.jsIndex
		);
		if (previous) {
			slot.provenance = previous.provenance;
			slot.rawLocations = previous.rawLocations.map((location) =>
				structuredClone(location)
			);
		} else {
			slot.provenance = slot.defaultValue == null
				? 'overflow-trailing'
				: 'overflow-default';
		}
	}
	plan.slots = recovered.slots;
	plan.rest = recovered.rest == null ? undefined : {
		...recovered.rest,
		provenance: plan.rest?.provenance ?? 'copy-rest-intrinsic',
	};
}

function indexedOverflowLocation(
	node: t.Node | null | undefined,
	functionId: number,
): { jsIndex: number; location: StorageLocation } | undefined {
	if (!node) return;
	const location = locationOf(node);
	if (
		location?.kind !== 'parameter' ||
		location.owner.functionId !== functionId ||
		location.parameter.form !== 'overflow' ||
		location.parameter.index < 1
	) return;
	return { jsIndex: location.parameter.index - 1, location };
}

function liftedInstructionIs(
	node: t.Node,
	functionId: number,
	instruction: 'GetArgumentsLength' | 'GetArgumentsPropByVal',
): boolean {
	return node.extra?.instruction === instruction &&
		node.extra?.parentFunctionId === functionId;
}

function indexedArgumentsProperty(
	node: t.Node | null | undefined,
	functionId: number,
): { jsIndex: number; location: StorageLocation } | undefined {
	if (
		!node || !t.isMemberExpression(node, { computed: true }) ||
		!liftedInstructionIs(node, functionId, 'GetArgumentsPropByVal') ||
		!t.isIdentifier(node.object, { name: 'arguments' }) ||
		!t.isNumericLiteral(node.property) ||
		!Number.isSafeInteger(node.property.value) || node.property.value < 0
	) return;
	const jsIndex = node.property.value;
	return {
		jsIndex,
		location: {
			kind: 'parameter',
			owner: { functionId },
			parameter: { index: jsIndex + 1, form: 'overflow' },
		},
	};
}

function isArgumentsLength(
	node: t.Node,
	functionId: number,
): boolean {
	return t.isMemberExpression(node, { computed: false }) &&
		liftedInstructionIs(node, functionId, 'GetArgumentsLength') &&
		t.isIdentifier(node.object, { name: 'arguments' }) &&
		t.isIdentifier(node.property, { name: 'length' });
}

function indexedParameterSource(
	node: t.Node | null | undefined,
	functionId: number,
): number | undefined {
	if (!node) return;
	const location = locationOf(node);
	if (
		location?.kind === 'parameter' &&
		location.owner.functionId === functionId &&
		location.parameter.index >= 1
	) return location.parameter.index - 1;
	if (t.isIdentifier(node)) {
		const match = new RegExp(`^_param_${functionId}_(\\d+)_$`).exec(
			node.name,
		);
		if (match) return Number(match[1]);
	}
	return;
}

function singleDeclarator(statement: t.Statement | undefined) {
	if (
		!t.isVariableDeclaration(statement) ||
		statement.declarations.length !== 1
	) return;
	return statement.declarations[0];
}

function assignmentTo(
	statement: t.Statement | undefined,
	name: string,
): t.AssignmentExpression | undefined {
	if (
		!t.isExpressionStatement(statement) ||
		!t.isAssignmentExpression(statement.expression, { operator: '=' }) ||
		!t.isIdentifier(statement.expression.left, { name }) ||
		!t.isExpression(statement.expression.right)
	) return;
	return statement.expression;
}

function undefinedComparisonSource(
	test: t.Expression,
): { source: t.Expression; negated: boolean } | undefined {
	let current = test;
	let negated = false;
	while (t.isUnaryExpression(current, { operator: '!' })) {
		negated = !negated;
		current = current.argument;
	}
	if (!t.isBinaryExpression(current)) return;
	const inequality = current.operator === '!==' || current.operator === '!=';
	if (
		!inequality && current.operator !== '===' && current.operator !== '=='
	) return;
	negated = negated !== inequality;
	if (isUndefinedNode(current.right) && t.isExpression(current.left)) {
		return { source: current.left, negated };
	}
	if (isUndefinedNode(current.left) && t.isExpression(current.right)) {
		return { source: current.right, negated };
	}
	return;
}

function argumentCountPresence(
	test: t.Expression,
	functionId: number,
): { jsIndex: number; presentWhenTrue: boolean } | undefined {
	let current = test;
	let inverted = false;
	while (t.isUnaryExpression(current, { operator: '!' })) {
		inverted = !inverted;
		current = current.argument;
	}
	if (!t.isBinaryExpression(current)) return;
	let jsIndex: number | undefined;
	let presentWhenTrue: boolean | undefined;
	if (
		current.operator === '<' && t.isNumericLiteral(current.left) &&
		isArgumentsLength(current.right, functionId)
	) {
		jsIndex = current.left.value;
		presentWhenTrue = true;
	} else if (
		current.operator === '>' &&
		isArgumentsLength(current.left, functionId) &&
		t.isNumericLiteral(current.right)
	) {
		jsIndex = current.right.value;
		presentWhenTrue = true;
	} else if (
		current.operator === '>=' &&
		isArgumentsLength(current.left, functionId) &&
		t.isNumericLiteral(current.right)
	) {
		jsIndex = current.right.value - 1;
		presentWhenTrue = true;
	} else if (
		current.operator === '<=' && t.isNumericLiteral(current.left) &&
		isArgumentsLength(current.right, functionId)
	) {
		jsIndex = current.left.value - 1;
		presentWhenTrue = true;
	}
	if (
		jsIndex == null || presentWhenTrue == null ||
		!Number.isSafeInteger(jsIndex) || jsIndex < 0
	) return;
	return {
		jsIndex,
		presentWhenTrue: inverted ? !presentWhenTrue : presentWhenTrue,
	};
}

interface DefaultProtocol {
	jsIndex: number;
	defaultValue: t.Expression;
	aliases: Set<string>;
	consumed: Set<number>;
	selections: t.ConditionalExpression[];
	sideEffectOnly: boolean;
}

function commonStatementSuffixLength(
	left: readonly t.Statement[],
	right: readonly t.Statement[],
): number {
	let length = 0;
	while (
		length < left.length && length < right.length &&
		statementsEquivalent(
			left[left.length - length - 1],
			right[right.length - length - 1],
		)
	) length++;
	return length;
}

function normalizeDuplicatedOverflowDefaultTails(body: t.Statement[]): void {
	for (let index = 0; index < body.length; index++) {
		const branch = body[index];
		if (
			!t.isIfStatement(branch) ||
			!t.isBlockStatement(branch.consequent) ||
			!t.isBlockStatement(branch.alternate)
		) continue;
		const comparison = undefinedComparisonSource(branch.test);
		if (!comparison) continue;
		const provided = comparison.negated
			? branch.consequent.body
			: branch.alternate.body;
		const defaulted = comparison.negated
			? branch.alternate.body
			: branch.consequent.body;
		const suffixLength = commonStatementSuffixLength(provided, defaulted);
		if (
			suffixLength === 0 || suffixLength !== provided.length ||
			defaulted.length <= suffixLength
		) continue;
		const initializer = defaulted.slice(0, -suffixLength);
		const suffix = provided.map((statement) =>
			t.cloneNode(statement, true)
		);
		body.splice(
			index,
			1,
			t.ifStatement(
				comparison.negated
					? invertTest(t.cloneNode(branch.test, true))
					: t.cloneNode(branch.test, true),
				t.blockStatement(
					initializer.map((statement) =>
						t.cloneNode(statement, true)
					),
				),
			),
			...suffix,
		);
	}
}

function substituteDefaultDefinitions(
	expression: t.Expression,
	definitions: ReadonlyMap<string, t.Expression>,
	seen = new Set<string>(),
): t.Expression | undefined {
	const substituteNode = (
		node: t.Node,
		active: ReadonlySet<string>,
	): t.Node | undefined => {
		if (t.isIdentifier(node)) {
			const definition = definitions.get(node.name);
			if (!definition) return t.cloneNode(node, true);
			if (active.has(node.name)) return;
			const nextSeen = new Set(active);
			nextSeen.add(node.name);
			return substituteNode(definition, nextSeen);
		}
		const clone = t.cloneNode(node, false);
		for (const key of t.VISITOR_KEYS[clone.type] ?? []) {
			const child = clone[key as keyof typeof clone];
			if (Array.isArray(child)) {
				const replaced: unknown[] = [];
				for (const element of child) {
					if (!t.isNode(element)) {
						replaced.push(element);
						continue;
					}
					const replacement = substituteNode(element, active);
					if (!replacement) return;
					replaced.push(replacement);
				}
				(clone as unknown as Record<string, unknown>)[key] = replaced;
			} else if (t.isNode(child)) {
				const replacement = substituteNode(child, active);
				if (!replacement) return;
				(clone as unknown as Record<string, unknown>)[key] =
					replacement;
			}
		}
		return clone;
	};
	const substituted = substituteNode(expression, seen);
	return t.isExpression(substituted) ? substituted : undefined;
}

function isSafelyDeferredDefaultPrefix(expression: t.Expression): boolean {
	return t.isIdentifier(expression) || t.isThisExpression(expression) ||
		t.isNullLiteral(expression) || t.isStringLiteral(expression) ||
		t.isNumericLiteral(expression) || t.isBooleanLiteral(expression) ||
		t.isBigIntLiteral(expression) ||
		(t.isUnaryExpression(expression) && expression.operator !== 'delete' &&
			t.isExpression(expression.argument) &&
			isSafelyDeferredDefaultPrefix(expression.argument));
}

function composeLinearDefaultValue(
	statements: readonly t.Statement[],
	targetName: string,
	inherited: ReadonlyMap<string, t.Expression>,
): t.Expression | undefined {
	const definitions = new Map(inherited);
	for (const statement of statements) {
		if (t.isVariableDeclaration(statement)) {
			if (
				!statement.declarations.every((declaration) =>
					t.isIdentifier(declaration.id) && declaration.init == null
				)
			) return;
			continue;
		}
		const assignment = t.isExpressionStatement(statement) &&
			assignmentTo(statement, targetName);
		const expression = t.isExpressionStatement(statement) &&
				t.isAssignmentExpression(statement.expression, {
					operator: '=',
				})
			? statement.expression
			: undefined;
		if (
			!expression || !t.isIdentifier(expression.left) ||
			!t.isExpression(expression.right)
		) return;
		const value = substituteDefaultDefinitions(
			expression.right,
			definitions,
		);
		if (!value) return;
		definitions.set(expression.left.name, value);
		if (assignment && expression.left.name !== targetName) return;
	}
	return definitions.get(targetName);
}

function composeStructuredDefaultArm(
	statements: readonly t.Statement[],
	targetName: string,
): t.Expression | undefined {
	const conditionalIndex = statements.findIndex(t.isIfStatement);
	if (conditionalIndex < 0 || conditionalIndex !== statements.length - 1) {
		return composeLinearDefaultValue(statements, targetName, new Map());
	}
	const prefix = statements.slice(0, conditionalIndex);
	const definitions = new Map<string, t.Expression>();
	for (const statement of prefix) {
		if (t.isVariableDeclaration(statement)) {
			for (const declaration of statement.declarations) {
				if (!t.isIdentifier(declaration.id)) return;
				if (declaration.init) {
					if (!t.isExpression(declaration.init)) return;
					definitions.set(declaration.id.name, declaration.init);
				}
			}
			continue;
		}
		if (
			!t.isExpressionStatement(statement) ||
			!t.isAssignmentExpression(statement.expression, {
				operator: '=',
			}) ||
			!t.isIdentifier(statement.expression.left) ||
			!t.isExpression(statement.expression.right)
		) return;
		const value = substituteDefaultDefinitions(
			statement.expression.right,
			definitions,
		);
		if (!value || !isSafelyDeferredDefaultPrefix(value)) return;
		definitions.set(statement.expression.left.name, value);
	}
	const conditional = statements[conditionalIndex] as t.IfStatement;
	if (
		!t.isBlockStatement(conditional.consequent) ||
		!t.isBlockStatement(conditional.alternate)
	) return;
	const consequent = composeLinearDefaultValue(
		conditional.consequent.body,
		targetName,
		definitions,
	);
	const alternate = composeLinearDefaultValue(
		conditional.alternate.body,
		targetName,
		definitions,
	);
	const test = substituteDefaultDefinitions(conditional.test, definitions);
	if (!consequent || !alternate || !test) return;
	return t.conditionalExpression(test, consequent, alternate);
}

function valueDefaultProtocols(
	body: t.Statement[],
	functionId: number,
	loads: ReadonlyMap<string, { jsIndex: number; statementIndex: number }>,
): DefaultProtocol[] {
	const protocols: DefaultProtocol[] = [];
	for (let index = 0; index < body.length; index++) {
		const conditional = body[index];
		if (
			!t.isIfStatement(conditional) || conditional.alternate != null ||
			!t.isBlockStatement(conditional.consequent) ||
			conditional.consequent.body.length !== 1
		) continue;
		const comparison = undefinedComparisonSource(conditional.test);
		if (!comparison || comparison.negated) continue;
		const source = t.isIdentifier(comparison.source)
			? loads.get(comparison.source.name)
			: indexedOverflowLocation(comparison.source, functionId);
		if (!source) continue;

		const fallbackStatement = conditional.consequent.body[0];
		if (!t.isExpressionStatement(fallbackStatement)) continue;
		const fallback = fallbackStatement.expression;
		if (
			!t.isAssignmentExpression(fallback, { operator: '=' }) ||
			!t.isIdentifier(fallback.left) ||
			!t.isExpression(fallback.right)
		) continue;
		const target = fallback.left.name;
		const consumed = new Set<number>([index]);
		let initial: t.Expression | undefined;
		const previousDeclaration = singleDeclarator(body[index - 1]);
		if (
			previousDeclaration &&
			t.isIdentifier(previousDeclaration.id, { name: target }) &&
			t.isExpression(previousDeclaration.init)
		) {
			initial = previousDeclaration.init;
			consumed.add(index - 1);
		} else {
			const previousAssignment = assignmentTo(body[index - 1], target);
			const declaration = singleDeclarator(body[index - 2]);
			if (
				previousAssignment && declaration &&
				t.isIdentifier(declaration.id, { name: target }) &&
				declaration.init == null
			) {
				initial = previousAssignment.right;
				consumed.add(index - 1);
				consumed.add(index - 2);
			}
		}
		const sourceName = t.isIdentifier(comparison.source)
			? comparison.source.name
			: undefined;
		if (
			!initial ||
			!(sourceName && t.isIdentifier(initial, { name: sourceName }) ||
				indexedOverflowLocation(initial, functionId)?.jsIndex ===
					source.jsIndex)
		) continue;
		protocols.push({
			jsIndex: source.jsIndex,
			defaultValue: t.cloneNode(fallback.right, true),
			aliases: new Set([target, ...(sourceName ? [sourceName] : [])]),
			consumed,
			selections: [],
			sideEffectOnly: false,
		});
	}
	return protocols;
}

function structuredValueDefaultProtocols(
	body: t.Statement[],
	loads: ReadonlyMap<string, { jsIndex: number; statementIndex: number }>,
): DefaultProtocol[] {
	const protocols: DefaultProtocol[] = [];
	for (let index = 0; index < body.length; index++) {
		const conditional = body[index];
		if (
			!t.isIfStatement(conditional) || conditional.alternate != null ||
			!t.isBlockStatement(conditional.consequent) ||
			conditional.consequent.body.length < 2
		) continue;
		const comparison = undefinedComparisonSource(conditional.test);
		if (
			!comparison || comparison.negated ||
			!t.isIdentifier(comparison.source)
		) continue;
		const source = loads.get(comparison.source.name);
		if (!source) continue;

		let targetName: string | undefined;
		const consumed = new Set<number>([index]);
		const previousDeclaration = singleDeclarator(body[index - 1]);
		if (
			previousDeclaration && t.isIdentifier(previousDeclaration.id) &&
			t.isIdentifier(previousDeclaration.init, {
				name: comparison.source.name,
			})
		) {
			targetName = previousDeclaration.id.name;
			consumed.add(index - 1);
		} else {
			const previous = body[index - 1];
			const assignment = t.isExpressionStatement(previous) &&
					t.isAssignmentExpression(previous.expression, {
						operator: '=',
					})
				? previous.expression
				: undefined;
			const declaration = singleDeclarator(body[index - 2]);
			if (
				assignment && t.isIdentifier(assignment.left) &&
				t.isIdentifier(assignment.right, {
					name: comparison.source.name,
				}) && declaration &&
				t.isIdentifier(declaration.id, {
					name: assignment.left.name,
				}) &&
				declaration.init == null
			) {
				targetName = assignment.left.name;
				consumed.add(index - 1);
				consumed.add(index - 2);
			}
		}
		if (!targetName) continue;
		const defaultValue = composeStructuredDefaultArm(
			conditional.consequent.body,
			targetName,
		);
		if (!defaultValue) continue;
		protocols.push({
			jsIndex: source.jsIndex,
			defaultValue,
			aliases: new Set([comparison.source.name, targetName]),
			consumed,
			selections: [],
			sideEffectOnly: false,
		});
	}
	return protocols;
}

function expressionIsProtocolSource(
	expression: t.Expression,
	comparisonSource: t.Expression,
	functionId: number,
	loads: ReadonlyMap<string, { jsIndex: number; statementIndex: number }>,
): { jsIndex: number; alias?: string } | undefined {
	if (t.isIdentifier(comparisonSource)) {
		const load = loads.get(comparisonSource.name);
		if (
			load && t.isIdentifier(expression, { name: comparisonSource.name })
		) {
			return { jsIndex: load.jsIndex, alias: comparisonSource.name };
		}
		return;
	}
	const comparison = indexedOverflowLocation(comparisonSource, functionId);
	const selected = indexedOverflowLocation(expression, functionId);
	if (comparison && selected?.jsIndex === comparison.jsIndex) {
		return { jsIndex: comparison.jsIndex };
	}
	return;
}

function conditionalDefaultProtocols(
	body: t.Statement[],
	functionId: number,
	loads: ReadonlyMap<string, { jsIndex: number; statementIndex: number }>,
): DefaultProtocol[] {
	const protocols: DefaultProtocol[] = [];
	for (const statement of body) {
		t.traverseFast(statement, (node) => {
			if (node !== statement && t.isFunction(node)) {
				return t.traverseFast.skip;
			}
			if (!t.isConditionalExpression(node)) return;
			const comparison = undefinedComparisonSource(node.test);
			if (!comparison) return;
			const selected = comparison.negated
				? node.consequent
				: node.alternate;
			const fallback = comparison.negated
				? node.alternate
				: node.consequent;
			if (!t.isExpression(selected) || !t.isExpression(fallback)) return;
			const source = expressionIsProtocolSource(
				selected,
				comparison.source,
				functionId,
				loads,
			);
			if (!source) return;
			protocols.push({
				jsIndex: source.jsIndex,
				defaultValue: t.cloneNode(fallback, true),
				aliases: new Set(source.alias ? [source.alias] : []),
				consumed: new Set(),
				selections: [node],
				sideEffectOnly: false,
			});
		});
	}
	return protocols;
}

/** Recover the argument-count guard Hermes emits for omitted optional formals. */
function argumentLengthDefaultProtocols(
	body: t.Statement[],
	functionId: number,
): DefaultProtocol[] {
	const protocols: DefaultProtocol[] = [];
	for (const statement of body) {
		t.traverseFast(statement, (node) => {
			if (node !== statement && t.isFunction(node)) {
				return t.traverseFast.skip;
			}
			if (!t.isConditionalExpression(node)) return;
			if (t.isLogicalExpression(node.test)) {
				const operands = [node.test.left, node.test.right];
				const countIndex = operands.findIndex((operand) =>
					t.isExpression(operand) &&
					argumentCountPresence(operand, functionId) != null
				);
				const comparisonIndex = operands.findIndex((operand) =>
					t.isExpression(operand) &&
					undefinedComparisonSource(operand) != null
				);
				if (
					countIndex < 0 || comparisonIndex < 0 ||
					countIndex === comparisonIndex
				) return;
				const count = argumentCountPresence(
					operands[countIndex] as t.Expression,
					functionId,
				)!;
				const comparison = undefinedComparisonSource(
					operands[comparisonIndex] as t.Expression,
				)!;
				const comparedSource = indexedArgumentsProperty(
					comparison.source,
					functionId,
				);
				const selectedWhenTrue = node.test.operator === '&&';
				const guardMatches = selectedWhenTrue
					? count.presentWhenTrue && comparison.negated
					: !count.presentWhenTrue && !comparison.negated;
				const selected = selectedWhenTrue
					? node.consequent
					: node.alternate;
				const fallback = selectedWhenTrue
					? node.alternate
					: node.consequent;
				const selectedSource = indexedArgumentsProperty(
					selected,
					functionId,
				);
				if (
					!guardMatches || !comparedSource || !selectedSource ||
					count.jsIndex !== comparedSource.jsIndex ||
					count.jsIndex !== selectedSource.jsIndex ||
					!t.isExpression(fallback)
				) return;
				protocols.push({
					jsIndex: count.jsIndex,
					defaultValue: t.cloneNode(fallback, true),
					aliases: new Set(),
					consumed: new Set(),
					selections: [node],
					sideEffectOnly: false,
				});
				return;
			}
			const presence = argumentCountPresence(node.test, functionId);
			if (!presence) return;
			const present = presence.presentWhenTrue
				? node.consequent
				: node.alternate;
			const missing = presence.presentWhenTrue
				? node.alternate
				: node.consequent;
			if (
				!t.isConditionalExpression(present) ||
				!t.isExpression(missing)
			) return;

			const comparison = undefinedComparisonSource(present.test);
			if (!comparison) return;
			const selected = comparison.negated
				? present.consequent
				: present.alternate;
			const fallback = comparison.negated
				? present.alternate
				: present.consequent;
			if (!t.isExpression(selected) || !t.isExpression(fallback)) return;
			const comparedSource = indexedArgumentsProperty(
				comparison.source,
				functionId,
			);
			const selectedSource = indexedArgumentsProperty(
				selected,
				functionId,
			);
			if (
				!comparedSource || !selectedSource ||
				comparedSource.jsIndex !== presence.jsIndex ||
				selectedSource.jsIndex !== presence.jsIndex ||
				JSON.stringify(comparableAst(fallback)) !==
					JSON.stringify(comparableAst(missing))
			) return;
			protocols.push({
				jsIndex: presence.jsIndex,
				defaultValue: t.cloneNode(fallback, true),
				aliases: new Set(),
				consumed: new Set(),
				selections: [node],
				sideEffectOnly: false,
			});
		});
	}
	return protocols;
}

function argumentLengthTrailingSelections(
	body: t.Statement[],
	functionId: number,
): Array<{ jsIndex: number; selection: t.ConditionalExpression }> {
	const selections: Array<{
		jsIndex: number;
		selection: t.ConditionalExpression;
	}> = [];
	for (const statement of body) {
		t.traverseFast(statement, (node) => {
			if (node !== statement && t.isFunction(node)) {
				return t.traverseFast.skip;
			}
			if (!t.isConditionalExpression(node)) return;
			const presence = argumentCountPresence(node.test, functionId);
			if (!presence) return;
			const present = presence.presentWhenTrue
				? node.consequent
				: node.alternate;
			const missing = presence.presentWhenTrue
				? node.alternate
				: node.consequent;
			const source = indexedArgumentsProperty(present, functionId);
			if (
				!source || source.jsIndex !== presence.jsIndex ||
				!isUndefinedNode(missing)
			) return;
			selections.push({
				jsIndex: presence.jsIndex,
				selection: node,
			});
		});
	}
	return selections;
}

function statementsEquivalent(left: t.Statement, right: t.Statement): boolean {
	return JSON.stringify(comparableAst(left)) ===
		JSON.stringify(comparableAst(right));
}

function sideEffectDefaultProtocol(
	body: t.Statement[],
	functionId: number,
): DefaultProtocol | undefined {
	for (let index = 0; index < body.length - 1; index++) {
		const conditional = body[index];
		if (
			!t.isIfStatement(conditional) || conditional.alternate != null ||
			!t.isBlockStatement(conditional.consequent) ||
			conditional.consequent.body.length === 0
		) continue;
		const comparison = undefinedComparisonSource(conditional.test);
		if (!comparison) continue;
		const source = indexedOverflowLocation(comparison.source, functionId);
		if (!source) continue;
		const final = body.at(-1)!;
		const arm = conditional.consequent.body;
		const duplicatedTail = comparison.negated ? arm[0] : arm.at(-1);
		if (!duplicatedTail || !statementsEquivalent(duplicatedTail, final)) {
			continue;
		}
		const initializerStatements = comparison.negated
			? body.slice(index + 1, -1)
			: arm.slice(0, -1);
		if (
			initializerStatements.length === 0 ||
			!initializerStatements.every((statement) =>
				t.isExpressionStatement(statement) &&
				t.isExpression(statement.expression)
			)
		) continue;
		const expressions = initializerStatements.map((statement) =>
			t.cloneNode((statement as t.ExpressionStatement).expression, true)
		);
		return {
			jsIndex: source.jsIndex,
			defaultValue: expressions.length === 1
				? expressions[0]
				: t.sequenceExpression(expressions),
			aliases: new Set(),
			consumed: new Set([
				index,
				...(comparison.negated
					? initializerStatements.map((_, offset) =>
						index + offset + 1
					)
					: []),
			]),
			selections: [],
			sideEffectOnly: true,
		};
	}
	return;
}

function replaceRecoveredSources(
	body: t.Statement[],
	functionId: number,
	recovered: ReadonlySet<number>,
	aliases: ReadonlyMap<string, number>,
	selections: ReadonlyMap<t.ConditionalExpression, number>,
): void {
	const file = t.file(t.program(body));
	traverse(file, {
		ConditionalExpression(path) {
			const jsIndex = selections.get(path.node);
			if (jsIndex == null || !recovered.has(jsIndex)) return;
			path.replaceWith(t.identifier(`_param_${functionId}_${jsIndex}_`));
			path.skip();
		},
		MemberExpression(path) {
			const source = indexedOverflowLocation(path.node, functionId) ??
				indexedArgumentsProperty(path.node, functionId);
			if (!source || !recovered.has(source.jsIndex)) return;
			path.replaceWith(t.identifier(
				`_param_${functionId}_${source.jsIndex}_`,
			));
			path.skip();
		},
		Identifier(path) {
			if (!path.isReferencedIdentifier()) return;
			const jsIndex = aliases.get(path.node.name);
			if (jsIndex == null || !recovered.has(jsIndex)) return;
			path.replaceWith(t.identifier(`_param_${functionId}_${jsIndex}_`));
		},
	});
}

function replaceRecoveredDefaultSources(
	expression: t.Expression,
	functionId: number,
	recovered: ReadonlySet<number>,
	aliases: ReadonlyMap<string, number>,
): t.Expression {
	const statement = t.expressionStatement(t.cloneNode(expression, true));
	const file = t.file(t.program([statement]));
	traverse(file, {
		MemberExpression(path) {
			const source = indexedOverflowLocation(path.node, functionId) ??
				indexedArgumentsProperty(path.node, functionId);
			if (!source || !recovered.has(source.jsIndex)) return;
			path.replaceWith(t.identifier(
				`_param_${functionId}_${source.jsIndex}_`,
			));
			path.skip();
		},
		Identifier(path) {
			if (!path.isReferencedIdentifier()) return;
			const jsIndex = aliases.get(path.node.name);
			if (jsIndex == null || !recovered.has(jsIndex)) return;
			path.replaceWith(t.identifier(`_param_${functionId}_${jsIndex}_`));
		},
	});
	return statement.expression;
}

export interface OverflowParameterRecoveryInput {
	functionId: number;
	headerParamCount: number;
	body: t.Statement[];
	plan: ParameterPlan;
}

function replacePatternBindingDefault(
	pattern: t.ArrayPattern | t.ObjectPattern,
	name: string,
	defaultValue: t.Expression,
): boolean {
	let changed = false;
	const visit = (node: t.Node): void => {
		if (t.isObjectProperty(node)) {
			if (t.isIdentifier(node.value, { name })) {
				node.value = t.assignmentPattern(
					t.cloneNode(node.value),
					t.cloneNode(defaultValue, true),
				);
				node.shorthand = false;
				changed = true;
				return;
			}
			if (t.isNode(node.value)) visit(node.value);
			return;
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const child = node[key as keyof typeof node];
			if (Array.isArray(child)) {
				for (let index = 0; index < child.length; index++) {
					const element = child[index];
					if (!t.isNode(element)) continue;
					if (t.isIdentifier(element, { name })) {
						(child as unknown as t.Node[])[index] = t
							.assignmentPattern(
								t.cloneNode(element),
								t.cloneNode(defaultValue, true),
							);
						changed = true;
					} else visit(element);
				}
			} else if (t.isNode(child)) {
				if (t.isIdentifier(child, { name })) {
					(node as unknown as Record<string, unknown>)[key] = t
						.assignmentPattern(
							t.cloneNode(child),
							t.cloneNode(defaultValue, true),
						);
					changed = true;
				} else visit(child);
			}
		}
	};
	visit(pattern);
	return changed;
}

/** Fold repeated post-pattern undefined selections into binding defaults. */
export function attachPatternBindingDefaults(body: t.Statement[]): number {
	const declaration = singleDeclarator(body[0]);
	if (
		!declaration ||
		!(t.isArrayPattern(declaration.id) || t.isObjectPattern(declaration.id))
	) return 0;
	const pattern = declaration.id;
	const candidates = new Map<
		string,
		{ defaults: t.Expression[]; selections: t.ConditionalExpression[] }
	>();
	for (const statement of body.slice(1)) {
		t.traverseFast(statement, (node) => {
			if (node !== statement && t.isFunction(node)) {
				return t.traverseFast.skip;
			}
			if (!t.isConditionalExpression(node)) return;
			const comparison = undefinedComparisonSource(node.test);
			if (!comparison || !t.isIdentifier(comparison.source)) return;
			const selected = comparison.negated
				? node.consequent
				: node.alternate;
			const fallback = comparison.negated
				? node.alternate
				: node.consequent;
			if (
				!t.isIdentifier(selected, { name: comparison.source.name }) ||
				!t.isExpression(fallback)
			) return;
			const entry = candidates.get(comparison.source.name) ?? {
				defaults: [],
				selections: [],
			};
			entry.defaults.push(fallback);
			entry.selections.push(node);
			candidates.set(comparison.source.name, entry);
		});
	}

	let attached = 0;
	for (const [name, candidate] of candidates) {
		const [first] = candidate.defaults;
		if (
			!first ||
			candidate.defaults.some((value) =>
				JSON.stringify(comparableAst(value)) !==
					JSON.stringify(comparableAst(first))
			)
		) continue;
		const wrapped = t.file(t.program(body.slice(1)));
		let references = 0;
		traverse(wrapped, {
			Identifier(path) {
				if (path.isReferencedIdentifier({ name })) references++;
			},
		});
		if (references !== candidate.selections.length * 2) continue;
		if (!replacePatternBindingDefault(pattern, name, first)) continue;
		const selectionSet = new Set(candidate.selections);
		traverse(wrapped, {
			ConditionalExpression(path) {
				if (!selectionSet.has(path.node)) return;
				path.replaceWith(t.identifier(name));
				path.skip();
			},
		});
		attached++;
	}
	return attached;
}

interface ObjectProjection {
	node: t.MemberExpression;
	path: Array<{ key: t.Expression; computed: boolean }>;
	binding: t.Identifier;
}

function staticObjectProjectionRoot(
	node: t.MemberExpression,
): { source: t.Identifier; path: ObjectProjection['path'] } | undefined {
	const reversed: ObjectProjection['path'] = [];
	let current: t.Expression | t.Super = node;
	while (t.isMemberExpression(current)) {
		if (t.isPrivateName(current.property)) return;
		if (
			current.computed &&
			!(t.isStringLiteral(current.property) ||
				t.isNumericLiteral(current.property))
		) return;
		reversed.push({
			key: t.cloneNode(current.property, true) as t.Expression,
			computed: current.computed,
		});
		current = current.object;
	}
	if (!t.isIdentifier(current)) return;
	return { source: current, path: reversed.reverse() };
}

function staticObjectProjection(
	node: t.MemberExpression,
	sourceName: string,
): ObjectProjection['path'] | undefined {
	const projection = staticObjectProjectionRoot(node);
	return projection?.source.name === sourceName ? projection.path : undefined;
}

function projectionKey(
	segment: ObjectProjection['path'][number],
): string {
	return `${segment.computed ? 'c' : 'p'}:${
		JSON.stringify(
			comparableAst(segment.key),
		)
	}`;
}

function objectRestProjectionKey(
	segment: ObjectProjection['path'][number],
): string {
	if (!segment.computed) {
		if (t.isIdentifier(segment.key)) return `p:${segment.key.name}`;
		if (t.isStringLiteral(segment.key)) return `p:${segment.key.value}`;
		if (t.isNumericLiteral(segment.key)) return `p:${segment.key.value}`;
	}
	return projectionKey(segment);
}

interface ProjectionTree {
	segment?: ObjectProjection['path'][number];
	children: Map<string, ProjectionTree>;
	binding?: t.Identifier;
}

function projectionPattern(
	projections: readonly ObjectProjection[],
): t.ObjectPattern | undefined {
	const root: ProjectionTree = { children: new Map() };
	for (const projection of projections) {
		let current = root;
		for (const segment of projection.path) {
			if (current.binding) return;
			const key = projectionKey(segment);
			let child = current.children.get(key);
			if (!child) {
				child = { segment, children: new Map() };
				current.children.set(key, child);
			}
			current = child;
		}
		if (current.children.size > 0) return;
		if (
			current.binding && current.binding.name !== projection.binding.name
		) {
			return;
		}
		current.binding = projection.binding;
	}
	const build = (tree: ProjectionTree): t.ObjectPattern | undefined => {
		const properties: t.ObjectProperty[] = [];
		for (const child of tree.children.values()) {
			if (!child.segment) return;
			const value = child.binding ?? build(child);
			if (!value) return;
			properties.push(t.objectProperty(
				t.cloneNode(child.segment.key, true),
				t.cloneNode(value, true),
				child.segment.computed,
			));
		}
		return t.objectPattern(properties);
	};
	return build(root);
}

function nullPrototypeProperty(
	property: t.ObjectExpression['properties'][number],
): boolean {
	if (!t.isObjectProperty(property) || property.computed) return false;
	if (
		!t.isIdentifier(property.key, { name: '__proto__' }) &&
		!t.isStringLiteral(property.key, { value: '__proto__' })
	) return false;
	return t.isNullLiteral(property.value);
}

function objectRestExclusionLiteralKeys(
	excluded: t.ObjectExpression,
): Set<string> | null {
	const keys = new Set<string>();
	let hasNullPrototype = false;
	for (const property of excluded.properties) {
		if (nullPrototypeProperty(property)) {
			hasNullPrototype = true;
			continue;
		}
		if (
			!t.isObjectProperty(property) ||
			!t.isExpression(property.key) ||
			!t.isNumericLiteral(property.value, { value: 0 })
		) return null;
		const key = objectRestProjectionKey({
			key: property.key,
			computed: property.computed,
		});
		if (keys.has(key)) return null;
		keys.add(key);
	}
	return hasNullPrototype && keys.size > 0 ? keys : null;
}

function objectCreateNullArgument(
	expression: t.Expression,
): t.Expression | null {
	if (
		!t.isCallExpression(expression) ||
		!t.isMemberExpression(expression.callee, { computed: false }) ||
		!t.isIdentifier(expression.callee.object, { name: 'Object' }) ||
		!t.isIdentifier(expression.callee.property, { name: 'create' }) ||
		expression.arguments.length !== 1 ||
		!t.isExpression(expression.arguments[0])
	) return null;
	return expression.arguments[0];
}

function staticExpressionBinding(
	body: readonly t.Statement[],
	name: string,
	before: number,
): { expression: t.Expression; index: number } | null {
	for (let index = before - 1; index >= 0; index--) {
		if (!t.isVariableDeclaration(body[index], { kind: 'const' })) continue;
		const declaration = singleDeclarator(body[index]);
		if (
			declaration &&
			t.isIdentifier(declaration.id, { name }) &&
			t.isExpression(declaration.init)
		) return { expression: declaration.init, index };
	}
	return null;
}

function resolvesToNull(
	body: readonly t.Statement[],
	expression: t.Expression,
	before: number,
): boolean {
	if (t.isNullLiteral(expression)) return true;
	if (!t.isIdentifier(expression)) return false;
	const resolved = staticExpressionBinding(body, expression.name, before);
	return resolved
		? resolvesToNull(body, resolved.expression, resolved.index)
		: false;
}

function assignNullPrototypeObjectKeys(
	body: readonly t.Statement[],
	expression: t.CallExpression,
	before: number,
): Set<string> | null {
	if (
		!t.isMemberExpression(expression.callee, { computed: false }) ||
		!t.isIdentifier(expression.callee.object, { name: 'Object' }) ||
		!t.isIdentifier(expression.callee.property, { name: 'assign' }) ||
		expression.arguments.length !== 2 ||
		!t.isExpression(expression.arguments[0]) ||
		!t.isObjectExpression(expression.arguments[1])
	) return null;
	const parent = objectCreateNullArgument(expression.arguments[0]);
	if (!parent || !resolvesToNull(body, parent, before)) return null;
	const object = t.cloneNode(expression.arguments[1], true);
	object.properties.unshift(t.objectProperty(
		t.identifier('__proto__'),
		t.nullLiteral(),
	));
	return objectRestExclusionLiteralKeys(object);
}

interface ObjectRestExclusionKeyPlan {
	keys: Set<string>;
	cleanupIndices: Set<number>;
	cleanupNames: Set<string>;
}

function emptyObjectRestExclusionKeyPlan(
	keys: Set<string>,
): ObjectRestExclusionKeyPlan {
	return {
		keys,
		cleanupIndices: new Set<number>(),
		cleanupNames: new Set<string>(),
	};
}

function silentNullPrototypeIndices(
	body: readonly t.Statement[],
	name: string,
	start: number,
	before: number,
): number[] {
	const indices: number[] = [];
	for (let index = start; index < before; index++) {
		const statement = body[index];
		if (
			t.isExpressionStatement(statement) &&
			t.isCallExpression(statement.expression) &&
			t.isMemberExpression(statement.expression.callee, {
				computed: false,
			}) &&
			t.isIdentifier(statement.expression.callee.object, {
				name: 'HermesInternal',
			}) &&
			t.isIdentifier(statement.expression.callee.property, {
				name: 'silentSetPrototypeOf',
			}) &&
			statement.expression.arguments.length === 2 &&
			t.isIdentifier(statement.expression.arguments[0], { name }) &&
			t.isNullLiteral(statement.expression.arguments[1])
		) indices.push(index);
	}
	return indices;
}

function objectRestExclusionKeys(
	body: readonly t.Statement[],
	excluded: t.Expression,
	before: number,
): ObjectRestExclusionKeyPlan | null {
	if (t.isObjectExpression(excluded)) {
		const keys = objectRestExclusionLiteralKeys(excluded);
		return keys ? emptyObjectRestExclusionKeyPlan(keys) : null;
	}
	if (t.isCallExpression(excluded)) {
		const keys = assignNullPrototypeObjectKeys(body, excluded, before);
		return keys ? emptyObjectRestExclusionKeyPlan(keys) : null;
	}
	if (!t.isIdentifier(excluded)) return null;
	const resolved = staticExpressionBinding(body, excluded.name, before);
	if (!resolved) return null;
	const cleanupIndices = new Set<number>([resolved.index]);
	const cleanupNames = new Set<string>([excluded.name]);
	let keys: Set<string> | null = null;
	if (t.isObjectExpression(resolved.expression)) {
		const object = t.cloneNode(resolved.expression, true);
		if (!object.properties.some(nullPrototypeProperty)) {
			for (
				const index of silentNullPrototypeIndices(
					body,
					excluded.name,
					resolved.index + 1,
					before,
				)
			) {
				object.properties.unshift(t.objectProperty(
					t.identifier('__proto__'),
					t.nullLiteral(),
				));
				cleanupIndices.add(index);
			}
		}
		keys = objectRestExclusionLiteralKeys(object);
	}
	if (!keys && t.isCallExpression(resolved.expression)) {
		keys = assignNullPrototypeObjectKeys(
			body,
			resolved.expression,
			resolved.index,
		);
	}
	if (!keys && t.isCallExpression(resolved.expression)) {
		const parent = objectCreateNullArgument(resolved.expression);
		if (!parent || !resolvesToNull(body, parent, resolved.index)) {
			return null;
		}
		const assignedKeys = new Set<string>();
		for (let index = resolved.index + 1; index < before; index++) {
			const statement = body[index];
			if (
				t.isExpressionStatement(statement) &&
				t.isCallExpression(statement.expression) &&
				t.isMemberExpression(statement.expression.callee, {
					computed: false,
				}) &&
				t.isIdentifier(statement.expression.callee.object, {
					name: 'HermesInternal',
				}) &&
				t.isIdentifier(statement.expression.callee.property, {
					name: 'silentSetPrototypeOf',
				})
			) {
				cleanupIndices.add(index);
				continue;
			}
			if (
				!t.isExpressionStatement(statement) ||
				!t.isAssignmentExpression(statement.expression, {
					operator: '=',
				}) ||
				!t.isMemberExpression(statement.expression.left) ||
				!t.isIdentifier(statement.expression.left.object, {
					name: excluded.name,
				}) ||
				!t.isExpression(statement.expression.left.property) ||
				!t.isNumericLiteral(statement.expression.right, { value: 0 })
			) continue;
			assignedKeys.add(objectRestProjectionKey({
				key: statement.expression.left.property,
				computed: statement.expression.left.computed,
			}));
			cleanupIndices.add(index);
		}
		keys = assignedKeys.size > 0 ? assignedKeys : null;
	}
	return keys ? { keys, cleanupIndices, cleanupNames } : null;
}

function projectedRestExclusionKeys(
	members: readonly { path: ObjectProjection['path'] }[],
): Set<string> | null {
	const keys = new Set<string>();
	for (const member of members) {
		const [top] = member.path;
		if (!top) return null;
		keys.add(objectRestProjectionKey(top));
	}
	return keys.size > 0 ? keys : null;
}

function sameKeySet(left: ReadonlySet<string>, right: ReadonlySet<string>) {
	if (left.size !== right.size) return false;
	for (const key of left) {
		if (!right.has(key)) return false;
	}
	return true;
}

function referencedIdentifierCountInStatement(
	statement: t.Statement,
	name: string,
): number {
	let count = 0;
	t.traverseFast(statement, (node) => {
		if (node !== statement && t.isFunction(node)) {
			return t.traverseFast.skip;
		}
		if (t.isIdentifier(node, { name })) count++;
	});
	return count;
}

function referencedIdentifierOutsideIndices(
	body: readonly t.Statement[],
	name: string,
	allowedIndices: ReadonlySet<number>,
): boolean {
	for (let index = 0; index < body.length; index++) {
		if (allowedIndices.has(index)) continue;
		if (referencedIdentifierCountInStatement(body[index]!, name) > 0) {
			return true;
		}
	}
	return false;
}

function objectRestCopySource(
	body: readonly t.Statement[],
	before: number,
	expression: t.CallExpression,
	sourceName: string,
	requiredKeys: ReadonlySet<string>,
): {
	source: t.Identifier;
	cleanupIndices: Set<number>;
	cleanupNames: Set<string>;
} | null {
	const callee = expression.callee;
	if (!t.isMemberExpression(callee, { computed: false })) return null;
	if (!t.isIdentifier(callee.object, { name: 'HermesInternal' })) return null;
	if (!t.isIdentifier(callee.property, { name: 'copyDataProperties' })) {
		return null;
	}
	if (expression.arguments.length !== 3) return null;
	const [targetArg, sourceArg, excludedArg] = expression.arguments;
	if (!t.isObjectExpression(targetArg) || targetArg.properties.length !== 0) {
		return null;
	}
	if (!t.isIdentifier(sourceArg, { name: sourceName })) return null;
	if (!t.isExpression(excludedArg)) return null;
	const exclusion = objectRestExclusionKeys(body, excludedArg, before);
	if (!exclusion || !sameKeySet(exclusion.keys, requiredKeys)) return null;
	return {
		source: sourceArg,
		cleanupIndices: exclusion.cleanupIndices,
		cleanupNames: exclusion.cleanupNames,
	};
}

function objectRestBinding(functionId: number, jsIndex: number) {
	return t.identifier(`_rest_${functionId}_${jsIndex}_`);
}

function projectionTarget(statement: t.Statement): {
	binding: t.Identifier;
	value: t.MemberExpression;
} | undefined {
	const declaration = singleDeclarator(statement);
	if (
		declaration && t.isIdentifier(declaration.id) &&
		t.isMemberExpression(declaration.init)
	) return { binding: declaration.id, value: declaration.init };
	if (
		t.isExpressionStatement(statement) &&
		t.isAssignmentExpression(statement.expression, { operator: '=' }) &&
		t.isIdentifier(statement.expression.left) &&
		t.isMemberExpression(statement.expression.right)
	) {
		return {
			binding: statement.expression.left,
			value: statement.expression.right,
		};
	}
	return;
}

function overflowSources(
	expression: t.Expression,
	functionId: number,
	definitions: ReadonlyMap<string, readonly t.Expression[]>,
	visiting = new Set<string>(),
): Set<number> {
	const direct = indexedParameterSource(expression, functionId);
	if (direct != null) return new Set([direct]);
	if (t.isIdentifier(expression)) {
		if (visiting.has(expression.name)) return new Set();
		const values = definitions.get(expression.name);
		if (!values) return new Set();
		const next = new Set(visiting);
		next.add(expression.name);
		const sources = new Set<number>();
		for (const value of values) {
			for (
				const source of overflowSources(
					value,
					functionId,
					definitions,
					new Set(next),
				)
			) sources.add(source);
		}
		return sources;
	}
	const sources = new Set<number>();
	if (
		t.isCallExpression(expression) &&
		t.isV8IntrinsicIdentifier(expression.callee, { name: 'Phi' })
	) {
		for (const argument of expression.arguments) {
			if (!t.isExpression(argument)) continue;
			for (
				const source of overflowSources(
					argument,
					functionId,
					definitions,
					new Set(visiting),
				)
			) sources.add(source);
		}
	} else if (t.isConditionalExpression(expression)) {
		for (const value of [expression.consequent, expression.alternate]) {
			for (
				const source of overflowSources(
					value,
					functionId,
					definitions,
					new Set(visiting),
				)
			) sources.add(source);
		}
	}
	return sources;
}

interface ProjectionSource {
	jsIndex: number;
	path: ObjectProjection['path'];
}

function projectionSources(
	expression: t.Expression,
	functionId: number,
	definitions: ReadonlyMap<string, readonly t.Expression[]>,
	visiting = new Set<string>(),
): ProjectionSource[] {
	const direct = t.isMemberExpression(expression)
		? staticObjectProjectionRoot(expression)
		: undefined;
	if (direct) {
		const directSource = indexedParameterSource(
			direct.source,
			functionId,
		);
		if (directSource != null) {
			return [{ jsIndex: directSource, path: direct.path }];
		}
		const bases = projectionSources(
			direct.source,
			functionId,
			definitions,
			visiting,
		);
		return bases.map((base) => ({
			jsIndex: base.jsIndex,
			path: [
				...base.path.map((segment) => ({
					key: t.cloneNode(segment.key, true),
					computed: segment.computed,
				})),
				...direct.path,
			],
		}));
	}
	const jsIndex = indexedParameterSource(expression, functionId);
	if (jsIndex != null) return [{ jsIndex, path: [] }];
	if (!t.isIdentifier(expression)) return [];
	if (visiting.has(expression.name)) return [];
	const values = definitions.get(expression.name);
	if (!values || values.length !== 1) return [];
	const next = new Set(visiting);
	next.add(expression.name);
	return projectionSources(values[0], functionId, definitions, next);
}

/** Capture property-probe binding provenance before sequence inlining. */
export function captureParameterProjections(
	functionId: number,
	bodies: Iterable<readonly t.Statement[]>,
	plan: ParameterPlan,
): number {
	const statements = [...bodies].flatMap((body) => [...body]);
	const definitions = new Map<string, t.Expression[]>();
	for (const statement of statements) {
		const declaration = singleDeclarator(statement);
		if (
			declaration && t.isIdentifier(declaration.id) &&
			t.isExpression(declaration.init)
		) {
			const values = definitions.get(declaration.id.name) ?? [];
			values.push(declaration.init);
			definitions.set(declaration.id.name, values);
		}
	}
	let captured = 0;
	for (const statement of statements) {
		const target = projectionTarget(statement);
		if (!target) continue;
		const projection = staticObjectProjectionRoot(target.value);
		if (!projection || projection.path.length === 0) continue;
		const sources = projectionSources(
			target.value,
			functionId,
			definitions,
		).filter((source) => source.path.length > 0);
		if (sources.length !== 1) continue;
		const [{ jsIndex, path }] = sources;
		const key = path.map(projectionKey).join('/');
		if (
			(plan.projections ?? []).some((candidate) =>
				candidate.jsIndex === jsIndex &&
				candidate.path.map(projectionKey).join('/') === key &&
				JSON.stringify(comparableAst(candidate.binding)) ===
					JSON.stringify(comparableAst(target.binding))
			)
		) continue;
		plan.projections.push({
			jsIndex,
			path: path.map((segment) => ({
				key: t.cloneNode(segment.key, true),
				computed: segment.computed,
			})),
			binding: t.cloneNode(target.binding, true),
		});
		captured++;
	}
	return captured;
}

/**
 * Recover the compact object-parameter lowering which Hermes emits as plain
 * property projections. There is no iterator/helper intrinsic for this form:
 * after default recovery its only remaining provenance is `_param_N_I_.x`.
 *
 * The pre-reduction capture supplies the binding target which distinguishes
 * this from a late AST-only guess and lets both header and overflow parameters
 * share the attachment path. A direct canonical-source escape declines this
 * compact inference: unlike a full iterator/helper protocol, an isolated
 * property read is bytecode-identical to source-level `obj.x`. A direct
 * `arguments[i]` read is deliberately not an escape because destructured
 * formals do not remove the arguments object.
 */
function boundIdentifierIsReferenced(
	body: t.Statement[],
	name: string,
): boolean {
	let referenced = false;
	const wrapped = t.file(t.program(body));
	let binding: Binding | undefined;
	traverse(wrapped, {
		Program(path) {
			binding = path.scope.getBinding(name);
		},
		Identifier(path) {
			if (!path.isReferencedIdentifier({ name })) return;
			if (binding && path.scope.getBinding(name) === binding) {
				referenced = true;
				path.stop();
			}
		},
	});
	return referenced;
}

function objectPatternDestructuringSource(path: NodePath<t.Identifier>) {
	const parent = path.parentPath;
	return (
		parent.isAssignmentExpression({ operator: '=' }) &&
		parent.node.right === path.node &&
		t.isObjectPattern(parent.node.left)
	) || (
		parent.isVariableDeclarator() &&
		parent.node.init === path.node &&
		t.isObjectPattern(parent.node.id)
	);
}

export function attachProjectedObjectParameterPatterns(
	_functionId: number,
	body: t.Statement[],
	plan: ParameterPlan,
): number {
	let recovered = 0;
	for (const slot of plan.slots) {
		if (!t.isIdentifier(slot.binding)) continue;
		const allCaptured = (plan.projections ?? []).filter((projection) =>
			projection.jsIndex === slot.jsIndex
		);
		if (allCaptured.length === 0) continue;
		const sourceName = slot.binding.name;
		const wrapped = t.file(t.program(body));
		const memberPaths: Array<{
			node: t.MemberExpression;
			path: ObjectProjection['path'];
			bareStatement?: t.ExpressionStatement;
		}> = [];
		const coveredSources = new Set<t.Identifier>();
		traverse(wrapped, {
			Function(path) {
				path.skip();
			},
			MemberExpression(path) {
				if (
					path.parentPath.isAssignmentExpression() &&
						path.parentPath.node.left === path.node ||
					path.parentPath.isUpdateExpression() ||
					path.parentPath.isUnaryExpression({ operator: 'delete' })
				) return;
				if (
					path.parentPath.isMemberExpression() &&
					path.parentPath.node.object === path.node
				) return;
				const projection = staticObjectProjection(
					path.node,
					sourceName,
				);
				if (!projection || projection.length === 0) return;
				memberPaths.push({
					node: path.node,
					path: projection,
					bareStatement: path.parentPath.isExpressionStatement()
						? path.parentPath.node
						: undefined,
				});
				let object: t.Expression | t.Super = path.node;
				while (t.isMemberExpression(object)) object = object.object;
				if (t.isIdentifier(object)) coveredSources.add(object);
			},
		});
		if (memberPaths.length === 0) continue;
		const memberPathKeys = new Set(
			memberPaths.map((member) =>
				member.path.map(projectionKey).join('/')
			),
		);
		const captured = allCaptured.filter((projection) =>
			memberPathKeys.has(projection.path.map(projectionKey).join('/')) ||
			boundIdentifierIsReferenced(body, projection.binding.name)
		);
		if (captured.length === 0) continue;

		const byPath = new Map<string, ObjectProjection>();
		let conflicting = false;
		for (const projection of captured) {
			const key = projection.path.map(projectionKey).join('/');
			const previous = byPath.get(key);
			if (
				previous &&
				JSON.stringify(comparableAst(previous.binding)) !==
					JSON.stringify(comparableAst(projection.binding))
			) {
				conflicting = true;
				break;
			}
			byPath.set(key, {
				node: memberPaths[0].node,
				path: projection.path,
				binding: projection.binding,
			});
		}
		let discardedBindingIndex = 0;
		const discardedBindings = new Set<string>();
		for (const member of memberPaths) {
			const key = member.path.map(projectionKey).join('/');
			if (byPath.has(key)) continue;
			if (member.path.length !== 1 || !member.bareStatement) {
				conflicting = true;
				break;
			}
			const binding = t.identifier(
				`_unused_${_functionId}_${slot.jsIndex}_${discardedBindingIndex++}_`,
			);
			discardedBindings.add(binding.name);
			byPath.set(key, {
				node: member.node,
				path: member.path,
				binding,
			});
		}
		const usedPaths = new Set([
			...memberPaths.map((member) =>
				member.path.map(projectionKey).join('/')
			),
			...captured.map((projection) =>
				projection.path.map(projectionKey).join('/')
			),
		]);
		const patternProjections = [...byPath].flatMap(([key, projection]) =>
			usedPaths.has(key) ? [projection] : []
		);
		const pattern = conflicting
			? undefined
			: projectionPattern(patternProjections);
		if (!pattern) {
			plan.telemetry.declines.push({
				reason: 'conflicting-object-parameter-projections',
				detail: `parameter ${slot.jsIndex}`,
			});
			continue;
		}
		const restExclusionKeys = projectedRestExclusionKeys(
			patternProjections,
		);
		const restCopies = new Set<t.CallExpression>();
		const restSourceIdentifiers = new Set<t.Identifier>();
		const restCopyStatementIndices = new Set<number>();
		const restCleanupIndices = new Set<number>();
		const restCleanupNames = new Set<string>();
		if (restExclusionKeys) {
			for (
				let statementIndex = 0;
				statementIndex < body.length;
				statementIndex++
			) {
				t.traverseFast(body[statementIndex]!, (node) => {
					if (node !== body[statementIndex] && t.isFunction(node)) {
						return t.traverseFast.skip;
					}
					if (!t.isCallExpression(node)) return;
					const source = objectRestCopySource(
						body,
						statementIndex,
						node,
						sourceName,
						restExclusionKeys,
					);
					if (!source) return;
					restCopies.add(node);
					restSourceIdentifiers.add(source.source);
					restCopyStatementIndices.add(statementIndex);
					for (const index of source.cleanupIndices) {
						restCleanupIndices.add(index);
					}
					for (const name of source.cleanupNames) {
						restCleanupNames.add(name);
					}
				});
			}
		}
		let directSourceEscape = false;
		traverse(wrapped, {
			Function(path) {
				path.skip();
			},
			Identifier(path) {
				if (
					path.isReferencedIdentifier({ name: sourceName }) &&
					!coveredSources.has(path.node) &&
					!restSourceIdentifiers.has(path.node) &&
					!objectPatternDestructuringSource(
						path as NodePath<t.Identifier>,
					)
				) directSourceEscape = true;
			},
		});
		if (directSourceEscape || restCopies.size > 1) {
			plan.telemetry.patternsDeclinedSourceEscapes++;
			continue;
		}
		const restBinding = restCopies.size === 1
			? objectRestBinding(_functionId, slot.jsIndex)
			: null;
		// Without a proven rest copy, a single property read is bytecode
		// identical to source-level `obj.k`, and a pattern keyed only by
		// computed numeric literals renders array indexing as destructuring.
		// Neither is evidence of a formal pattern.
		if (!restBinding) {
			if (pattern.properties.length < 2) {
				plan.telemetry.declines.push({
					reason: 'single-object-parameter-projection',
					detail: `parameter ${slot.jsIndex}`,
				});
				continue;
			}
			if (
				pattern.properties.every((property) =>
					t.isObjectProperty(property) && property.computed &&
					t.isNumericLiteral(property.key)
				)
			) {
				plan.telemetry.declines.push({
					reason: 'numeric-object-parameter-projection',
					detail: `parameter ${slot.jsIndex}`,
				});
				continue;
			}
		}
		if (restBinding) {
			pattern.properties.push(t.restElement(t.cloneNode(restBinding)));
		}
		const replacements = new Map(
			memberPaths.map((member) => [
				member.node,
				byPath.get(member.path.map(projectionKey).join('/'))!.binding,
			]),
		);
		traverse(wrapped, {
			CallExpression(path) {
				if (!restBinding || !restCopies.has(path.node)) return;
				path.replaceWith(t.cloneNode(restBinding, true));
				path.skip();
			},
			MemberExpression(path) {
				const binding = replacements.get(path.node);
				if (!binding) return;
				path.replaceWith(t.cloneNode(binding, true));
				path.skip();
			},
		});
		if (restBinding && restCleanupIndices.size > 0) {
			const allowedIndices = new Set([
				...restCleanupIndices,
				...restCopyStatementIndices,
			]);
			let removeCleanup = true;
			for (const name of restCleanupNames) {
				if (
					referencedIdentifierOutsideIndices(
						body,
						name,
						allowedIndices,
					)
				) {
					removeCleanup = false;
					break;
				}
			}
			if (removeCleanup) {
				for (
					const index of [...restCleanupIndices].sort((a, b) => b - a)
				) {
					body.splice(index, 1);
				}
			}
		}
		for (let index = body.length - 1; index >= 0; index--) {
			const declaration = singleDeclarator(body[index]);
			if (
				declaration && t.isIdentifier(declaration.id) &&
				t.isIdentifier(declaration.init, {
					name: declaration.id.name,
				})
			) {
				body.splice(index, 1);
				continue;
			}
			const statement = body[index];
			if (
				t.isExpressionStatement(statement) &&
				t.isIdentifier(statement.expression) &&
				discardedBindings.has(statement.expression.name)
			) {
				body.splice(index, 1);
				continue;
			}
			if (
				t.isExpressionStatement(statement) &&
				t.isAssignmentExpression(statement.expression, {
					operator: '=',
				}) &&
				t.isIdentifier(statement.expression.left) &&
				t.isIdentifier(statement.expression.right, {
					name: statement.expression.left.name,
				})
			) body.splice(index, 1);
		}
		slot.binding = pattern;
		plan.telemetry.parameterPatternsAttached++;
		recovered++;
	}
	return recovered;
}

function simpleDefaultAssignmentInBlock(
	stmt: t.Statement | undefined,
	name: string,
): t.Expression | null {
	if (!stmt || !t.isBlockStatement(stmt) || stmt.body.length !== 1) {
		return null;
	}
	const assign = assignmentTo(stmt.body[0], name);
	return assign ? t.cloneNode(assign.right, true) : null;
}

function countAssignmentsToName(body: readonly t.Statement[], name: string) {
	let count = 0;
	for (const statement of body) {
		t.traverseFast(statement, (node) => {
			if (node !== statement && t.isFunction(node)) {
				return t.traverseFast.skip;
			}
			if (
				t.isAssignmentExpression(node, { operator: '=' }) &&
				t.isIdentifier(node.left, { name })
			) count++;
			if (
				t.isUpdateExpression(node) &&
				t.isIdentifier(node.argument, { name })
			) {
				count++;
			}
		});
	}
	return count;
}

function replaceBoundIdentifierReferences(
	body: t.Statement[],
	name: string,
	replacement: t.Identifier,
): void {
	const wrapped = t.file(t.program(body));
	let binding: Binding | undefined;
	traverse(wrapped, {
		Program(path) {
			binding = path.scope.getBinding(name);
		},
		Identifier(path) {
			if (!path.isReferencedIdentifier({ name })) return;
			if (binding && path.scope.getBinding(name) === binding) {
				path.replaceWith(t.cloneNode(replacement, true));
			}
		},
	});
}

export function attachParameterPatternAssignmentDefaults(
	body: t.Statement[],
	plan: ParameterPlan,
): number {
	let attached = 0;
	for (let index = 0; index < body.length - 2; index++) {
		const declaration = singleDeclarator(body[index]);
		if (
			!declaration ||
			!t.isIdentifier(declaration.id) ||
			declaration.init != null
		) continue;
		const targetName = declaration.id.name;
		const initializer = assignmentTo(body[index + 1], targetName);
		if (!initializer || !t.isIdentifier(initializer.right)) continue;
		const sourceName = initializer.right.name;
		const guard = body[index + 2];
		if (!t.isIfStatement(guard) || guard.alternate) continue;
		const comparison = undefinedComparisonSource(guard.test);
		if (
			!comparison || comparison.negated ||
			!t.isIdentifier(comparison.source, { name: sourceName }) ||
			countAssignmentsToName(body, targetName) !== 2
		) continue;
		const defaultValue = simpleDefaultAssignmentInBlock(
			guard.consequent,
			targetName,
		);
		if (!defaultValue) continue;
		const ownerSlot = plan.slots.find((slot) =>
			t.isObjectPattern(slot.binding) &&
			replacePatternBindingDefault(
				slot.binding,
				sourceName,
				defaultValue,
			)
		);
		if (!ownerSlot) continue;
		replaceBoundIdentifierReferences(
			body,
			targetName,
			t.identifier(sourceName),
		);
		body.splice(index, 3);
		index--;
		attached++;
	}
	return attached;
}

function patternHasOnlyParameterBindings(pattern: t.Node): boolean {
	if (t.isIdentifier(pattern)) return true;
	if (t.isRestElement(pattern)) {
		return patternHasOnlyParameterBindings(pattern.argument);
	}
	if (t.isAssignmentPattern(pattern)) {
		return patternHasOnlyParameterBindings(pattern.left);
	}
	if (t.isArrayPattern(pattern)) {
		return pattern.elements.every((element) =>
			element == null || patternHasOnlyParameterBindings(element)
		);
	}
	if (t.isObjectPattern(pattern)) {
		return pattern.properties.every((property) =>
			t.isRestElement(property)
				? patternHasOnlyParameterBindings(property.argument)
				: patternHasOnlyParameterBindings(property.value)
		);
	}
	return false;
}

function referencedIdentifierCount(
	bodies: Iterable<t.Statement[]>,
	name: string,
): number {
	let count = 0;
	for (const body of bodies) {
		if (count > 1) return count;
		traverse(t.file(t.program(body)), {
			Identifier(path) {
				if (path.isReferencedIdentifier({ name })) count++;
			},
		});
	}
	return count;
}

function isParameterPatternBookkeepingPrelude(
	statement: t.Statement,
	plan: ParameterPlan,
): boolean {
	if (
		t.isVariableDeclaration(statement) &&
		statement.declarations.every((declaration) => declaration.init == null)
	) return true;
	const declaration = singleDeclarator(statement);
	if (
		declaration && t.isIdentifier(declaration.id) &&
		t.isCallExpression(declaration.init) &&
		t.isV8IntrinsicIdentifier(declaration.init.callee) &&
		[
			'CreateEnvironment',
			'CreateFunctionEnvironment',
			'CreateTopLevelEnvironment',
		].includes(declaration.init.callee.name)
	) return true;
	if (
		!t.isExpressionStatement(statement) ||
		!t.isAssignmentExpression(statement.expression, { operator: '=' }) ||
		!t.isMemberExpression(statement.expression.left, { computed: true }) ||
		!t.isCallExpression(statement.expression.left.object) ||
		!t.isV8IntrinsicIdentifier(statement.expression.left.object.callee, {
			name: 'expectEnvironment',
		})
	) return false;
	const value = statement.expression.right;
	if (t.isIdentifier(value)) {
		const valueName = value.name;
		if (valueName === 'undefined') return true;
		return plan.slots.some((slot) =>
			t.isIdentifier(slot.binding, { name: valueName })
		);
	}
	return t.isThisExpression(value);
}

/**
 * Attach an array/object protocol already proven by the CFG destructuring
 * recognizer to its canonical parameter slot. The source must be consumed
 * exclusively by the pattern, so moving the protocol to invocation time does
 * not remove an independently observable raw-parameter value.
 */
export function attachDirectParameterPatterns(
	body: t.Statement[],
	plan: ParameterPlan,
	referenceBodies: Iterable<t.Statement[]> = [body],
): number {
	let attached = 0;
	for (let statementIndex = 0; statementIndex < body.length;) {
		const statement = body[statementIndex];
		const declaration = singleDeclarator(statement);
		if (
			statement.extra?.fromDestructuring !== true || !declaration ||
			!(t.isArrayPattern(declaration.id) ||
				t.isObjectPattern(declaration.id)) ||
			!patternHasOnlyParameterBindings(declaration.id) ||
			!t.isIdentifier(declaration.init)
		) {
			if (isParameterPatternBookkeepingPrelude(statement, plan)) {
				statementIndex++;
				continue;
			}
			break;
		}
		const sourceName = declaration.init.name;

		const slot = plan.slots.find((candidate) =>
			t.isIdentifier(candidate.binding, {
				name: sourceName,
			})
		);
		if (!slot) break;
		if (referencedIdentifierCount(referenceBodies, sourceName) !== 1) {
			plan.telemetry.patternsDeclinedSourceEscapes++;
			break;
		}

		slot.binding = t.cloneNode(declaration.id, true);
		body.splice(statementIndex, 1);
		plan.telemetry.parameterPatternsAttached++;
		attached++;
	}
	return attached;
}

/**
 * Recover the non-simple formal suffix from a fully structured entry body.
 *
 * This is deliberately transactional: all recognition and rewriting happens
 * on clones, and the caller's CFG body changes only after a default protocol
 * proves that Hermes omitted a real formal suffix from `paramCount`.
 */
export function recoverOverflowParameters(
	input: OverflowParameterRecoveryInput,
): boolean {
	const { functionId, headerParamCount, plan } = input;
	const body = input.body.map((statement) => t.cloneNode(statement, true));
	normalizeDuplicatedOverflowDefaultTails(body);
	const boundary = Math.max(headerParamCount - 1, 0);
	const loads = new Map<
		string,
		{ jsIndex: number; statementIndex: number }
	>();
	const locations = new Map<number, StorageLocation[]>();
	for (
		let statementIndex = 0;
		statementIndex < body.length;
		statementIndex++
	) {
		const declaration = singleDeclarator(body[statementIndex]);
		if (
			declaration && t.isIdentifier(declaration.id) &&
			indexedOverflowLocation(declaration.init, functionId)
		) {
			const source = indexedOverflowLocation(
				declaration.init,
				functionId,
			)!;
			loads.set(declaration.id.name, { ...source, statementIndex });
		}
		t.traverseFast(body[statementIndex], (node) => {
			const source = indexedOverflowLocation(node, functionId) ??
				indexedArgumentsProperty(node, functionId);
			if (!source) return;
			const seen = locations.get(source.jsIndex) ?? [];
			if (
				!seen.some((location) =>
					JSON.stringify(location) === JSON.stringify(source.location)
				)
			) seen.push(source.location);
			locations.set(source.jsIndex, seen);
		});
	}
	plan.telemetry.overflowLoadsDiscovered += [...locations.values()].reduce(
		(count, values) => count + values.length,
		0,
	);
	const protocols = [
		...valueDefaultProtocols(body, functionId, loads),
		...structuredValueDefaultProtocols(body, loads),
		...conditionalDefaultProtocols(body, functionId, loads),
		...argumentLengthDefaultProtocols(body, functionId),
	];
	const sideEffect = sideEffectDefaultProtocol(body, functionId);
	if (sideEffect) protocols.push(sideEffect);
	const defaults = new Map<number, DefaultProtocol>();
	for (const protocol of protocols) {
		const existing = defaults.get(protocol.jsIndex);
		if (
			existing &&
			JSON.stringify(comparableAst(existing.defaultValue)) !==
				JSON.stringify(comparableAst(protocol.defaultValue))
		) {
			plan.telemetry.declines.push({
				reason: 'conflicting-default-protocols',
				detail: `parameter ${protocol.jsIndex}`,
			});
			return false;
		}
		if (existing) {
			for (const alias of protocol.aliases) existing.aliases.add(alias);
			for (const index of protocol.consumed) existing.consumed.add(index);
			existing.selections.push(...protocol.selections);
		} else defaults.set(protocol.jsIndex, protocol);
	}
	const proven = [...defaults.keys()].filter((index) => index >= boundary)
		.toSorted((left, right) => left - right);
	if (proven.length === 0) {
		if (locations.size > 0) {
			plan.telemetry.declines.push({ reason: 'no-default-protocol' });
			plan.telemetry.residualOverflowProvenance += locations.size;
		}
		return false;
	}
	if (proven[0] !== boundary && !defaults.has(proven[0])) return false;

	const maxIndex = Math.max(
		...proven,
		...[...locations.keys()].filter((index) => index >= boundary),
	);
	const recovered = new Set<number>();
	const aliases = new Map<string, number>();
	const selections = new Map<t.ConditionalExpression, number>();
	const consumed = new Set<number>();
	for (const protocol of protocols) {
		if (protocol.jsIndex < boundary) continue;
		for (const alias of protocol.aliases) {
			aliases.set(alias, protocol.jsIndex);
		}
		for (const index of protocol.consumed) consumed.add(index);
		for (const selection of protocol.selections) {
			selections.set(selection, protocol.jsIndex);
		}
	}
	for (const trailing of argumentLengthTrailingSelections(body, functionId)) {
		if (trailing.jsIndex >= boundary) {
			selections.set(trailing.selection, trailing.jsIndex);
		}
	}
	for (const [alias, { jsIndex, statementIndex }] of loads) {
		aliases.set(alias, jsIndex);
		consumed.add(statementIndex);
	}

	const headerSlots = plan.slots.filter((slot) => slot.jsIndex < boundary);
	const suffix: ParameterSlotPlan[] = [];
	for (let jsIndex = boundary; jsIndex <= maxIndex; jsIndex++) {
		const protocol = defaults.get(jsIndex);
		const rawLocations = locations.get(jsIndex) ?? [];
		let provenance: ParameterSlotProvenance;
		let defaultValue: t.Expression | undefined;
		if (protocol) {
			provenance = 'overflow-default';
			defaultValue = protocol.defaultValue;
			if (protocol.sideEffectOnly) {
				plan.telemetry.sideEffectOnlyDefaultsRecovered++;
			} else plan.telemetry.valueDefaultsRecovered++;
		} else if (rawLocations.length > 0) {
			provenance = 'overflow-trailing';
			plan.telemetry.trailingFormalsPromoted++;
		} else {
			provenance = 'inferred-gap';
			plan.telemetry.inferredGaps++;
		}
		// The first omitted slot must carry a default so generated JavaScript
		// retains Hermes' `function.length`, even when the slot itself was sparse.
		if (jsIndex === boundary && defaultValue == null) {
			defaultValue = t.identifier('undefined');
		}
		suffix.push({
			hermesIndex: jsIndex + 1,
			jsIndex,
			binding: t.identifier(`_param_${functionId}_${jsIndex}_`),
			defaultValue: defaultValue == null
				? undefined
				: replaceRecoveredDefaultSources(
					defaultValue,
					functionId,
					recovered,
					aliases,
				),
			provenance,
			rawLocations: rawLocations.map((location) =>
				structuredClone(location)
			),
		});
		recovered.add(jsIndex);
	}

	const rewritten = body.filter((_, index) => !consumed.has(index));
	replaceRecoveredSources(
		rewritten,
		functionId,
		recovered,
		aliases,
		selections,
	);
	input.body.splice(0, input.body.length, ...rewritten);
	plan.slots = [...headerSlots, ...suffix];
	return true;
}

export function setRestParameter(
	plan: ParameterPlan,
	functionId: number,
	startIndex: number,
	provenance: RestParameterPlan['provenance'],
): void {
	plan.slots = plan.slots.filter((slot) => slot.jsIndex < startIndex);
	plan.rest = {
		startIndex,
		binding: t.identifier(`_rest_${functionId}_`),
		provenance,
	};
	if (provenance === 'copy-rest-intrinsic') {
		plan.telemetry.restIntrinsicsRecovered++;
	} else plan.telemetry.restLoopsRecovered++;
}
