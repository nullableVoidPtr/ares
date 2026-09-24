import * as t from '@babel/types';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import {
	HermesEmpty,
	isStringRef,
} from '../../../hbc/disassembly/instruction.ts';
import { LiftedAST } from '../../ast/mod.ts';
import type { IRFunction } from '../mod.ts';
import { AddressSet } from '../../../utils/set.ts';
import { statementListEndsAbruptly } from '../../ast/completion.ts';
import { reduceSharedLeadingPhi } from './terminals.ts';

function parseUIntSwitchMarker(
	block: { body: LiftedAST<t.Statement>[]; consequentAddresses: BlockAddr[] },
): {
	discriminant: t.Expression;
	labels: t.Expression[];
	targets: BlockAddr[];
} | null {
	const marker = block.body.at(-1) as t.Statement | undefined;
	if (!t.isExpressionStatement(marker)) return null;
	if (!t.isCallExpression(marker.expression)) return null;
	if (
		!t.isV8IntrinsicIdentifier(marker.expression.callee, {
			name: 'UIntSwitchImm',
		})
	) return null;
	const args = marker.expression.arguments;
	if (args.length !== 3) return null;
	if (!t.isExpression(args[0])) return null;
	if (!t.isNumericLiteral(args[1]) || !t.isNumericLiteral(args[2])) {
		return null;
	}
	const minValue = args[1].value;
	const maxValue = args[2].value;
	const caseCount = maxValue - minValue + 1;
	if (!Number.isSafeInteger(caseCount) || caseCount <= 0) return null;
	return {
		discriminant: args[0],
		labels: Array.from(
			{ length: caseCount },
			(_, index) => t.numericLiteral(minValue + index),
		),
		targets: block.consequentAddresses,
	};
}

function parseStringSwitchMarker(
	block: { body: LiftedAST<t.Statement>[]; consequentAddresses: BlockAddr[] },
): {
	discriminant: t.Expression;
	labels: t.Expression[];
	targets: BlockAddr[];
} | null {
	const marker = block.body.at(-1) as t.Statement | undefined;
	if (!t.isExpressionStatement(marker)) return null;
	if (!t.isCallExpression(marker.expression)) return null;
	if (
		!t.isV8IntrinsicIdentifier(marker.expression.callee, {
			name: 'StringSwitchImm',
		})
	) return null;
	const args = marker.expression.arguments;
	if (args.length !== 2) return null;
	if (!t.isExpression(args[0]) || !t.isArrayExpression(args[1])) return null;
	const labels: t.Expression[] = [];
	for (const element of args[1].elements) {
		if (!t.isStringLiteral(element)) return null;
		labels.push(element);
	}
	if (labels.length === 0) return null;
	return {
		discriminant: args[0],
		labels,
		targets: block.consequentAddresses,
	};
}

function parseSwitchMarker(
	block: { body: LiftedAST<t.Statement>[]; consequentAddresses: BlockAddr[] },
) {
	return parseUIntSwitchMarker(block) ?? parseStringSwitchMarker(block);
}

function isSwitchMarkerStatement(stmt: t.Statement | undefined) {
	if (!t.isExpressionStatement(stmt)) return false;
	if (!t.isCallExpression(stmt.expression)) return false;
	return t.isV8IntrinsicIdentifier(stmt.expression.callee, {
		name: 'UIntSwitchImm',
	}) ||
		t.isV8IntrinsicIdentifier(stmt.expression.callee, {
			name: 'StringSwitchImm',
		});
}

function cloneTerminalCaseBody(blockBody: t.Statement[]): t.Statement[] {
	const body = blockBody.map((stmt) => t.cloneNode(stmt, true));
	if (!statementListEndsAbruptly(body)) {
		body.push(t.breakStatement());
	}
	return body;
}

type CompareSwitchTest = {
	discriminant: t.Expression;
	value: t.Expression;
	literalDeclIndex: number;
	negated: boolean;
};

type CompareSwitchCase = {
	test: BlockAddr;
	value: t.Expression;
	target: BlockAddr;
	prefix: t.Statement[];
};

type FallthroughPhiRewrite = {
	initializers: t.VariableDeclaration[];
	joinDestinations: Map<BlockAddr, Set<string>>;
	sourceAssignments: Map<
		BlockAddr,
		Map<string, { dest: string; expression: t.Expression }>
	>;
};

function expressionsEqual(left: t.Expression, right: t.Expression) {
	return JSON.stringify(left) === JSON.stringify(right);
}

function stableSwitchExpression(
	expr: t.Expression | null | undefined,
): boolean {
	if (!expr) return false;
	if (
		t.isNumericLiteral(expr) ||
		t.isStringLiteral(expr) ||
		t.isBooleanLiteral(expr) ||
		t.isNullLiteral(expr) ||
		t.isIdentifier(expr) ||
		t.isThisExpression(expr)
	) return true;
	if (t.isUnaryExpression(expr)) {
		return expr.operator !== 'delete' &&
			t.isExpression(expr.argument) &&
			stableSwitchExpression(expr.argument);
	}
	if (t.isMemberExpression(expr)) {
		return t.isExpression(expr.object) &&
			stableSwitchExpression(expr.object) &&
			(!expr.computed ||
				(t.isExpression(expr.property) &&
					stableSwitchExpression(expr.property)));
	}
	if (t.isCallExpression(expr)) {
		return t.isV8IntrinsicIdentifier(expr.callee, {
			name: 'expectEnvironment',
		}) && expr.arguments.every((arg) => t.isExpression(arg));
	}
	return false;
}

function parseCompareSwitchTest(
	block: { body: LiftedAST<t.Statement>[]; branch?: LiftedAST<t.Expression> },
	literalConstants?: Map<string, t.Expression>,
): CompareSwitchTest | null {
	let branch = block.branch as t.Expression | undefined;
	let negated = false;
	if (
		t.isUnaryExpression(branch, { operator: '!' }) &&
		t.isBinaryExpression(branch.argument, { operator: '===' })
	) {
		branch = branch.argument;
		negated = true;
	}
	if (t.isBinaryExpression(branch, { operator: '!==' })) {
		branch = t.binaryExpression('===', branch.left, branch.right);
		negated = true;
	}
	if (
		!branch ||
		!t.isBinaryExpression(branch, { operator: '===' })
	) {
		return null;
	}
	let literalName: string | undefined;
	let literalInit: t.Expression | undefined;
	if (t.isIdentifier(branch.left)) {
		literalName = branch.left.name;
	} else if (
		t.isExpression(branch.left) &&
		stableSwitchExpression(branch.left)
	) {
		literalInit = branch.left;
	} else {
		return null;
	}

	const literalDeclIndex = literalName == null ? -1 : block.body.findIndex(
		(stmt) => {
			const node = stmt as t.Statement;
			if (!t.isVariableDeclaration(node, { kind: 'const' })) return false;
			if (node.declarations.length !== 1) return false;
			const [decl] = node.declarations;
			return t.isIdentifier(decl.id, { name: literalName }) &&
				t.isExpression(decl.init) &&
				stableSwitchExpression(decl.init);
		},
	);
	if (literalInit == null && literalDeclIndex === -1) {
		if (literalName == null) return null;
		literalInit = literalConstants?.get(literalName);
		if (!literalInit) return null;
	} else if (literalInit == null) {
		const decl = (block.body[literalDeclIndex] as t.VariableDeclaration)
			.declarations[0];
		if (!t.isExpression(decl.init)) return null;
		literalInit = decl.init;
	}

	if (!t.isExpression(branch.right)) return null;
	const discriminant = resolveStableAlias(branch.right, literalConstants);

	return {
		discriminant,
		value: literalInit,
		literalDeclIndex: literalDeclIndex === -1
			? block.body.length
			: literalDeclIndex,
		negated,
	};
}

function resolveStableAlias(
	expr: t.Expression,
	literalConstants?: Map<string, t.Expression>,
	seen = new Set<string>(),
): t.Expression {
	if (!t.isIdentifier(expr) || !literalConstants || seen.has(expr.name)) {
		return expr;
	}
	const resolved = literalConstants.get(expr.name);
	if (!resolved) return expr;
	seen.add(expr.name);
	return resolveStableAlias(resolved, literalConstants, seen);
}

function blockHasOnlyCompareLiteral(
	block: { body: LiftedAST<t.Statement>[] },
	test: CompareSwitchTest,
) {
	return block.body.length === 1 && test.literalDeclIndex === 0;
}

function pureLiteralPrefix(
	block: { body: LiftedAST<t.Statement>[] },
	test: CompareSwitchTest,
): t.Statement[] | null {
	const prefix = block.body.slice(0, test.literalDeclIndex) as t.Statement[];
	for (const stmt of prefix) {
		if (!t.isVariableDeclaration(stmt, { kind: 'const' })) return null;
		if (stmt.declarations.length !== 1) return null;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id)) return null;
		if (!t.isExpression(decl.init) || !stableSwitchExpression(decl.init)) {
			return null;
		}
	}
	return prefix.map((stmt) => t.cloneNode(stmt, true));
}

function cloneCompareCaseBody(
	func: IRFunction,
	target: BlockAddr,
	switchTargets: AddressSet<BlockAddr>,
	prefix: t.Statement[] = [],
	phiRewrite?: FallthroughPhiRewrite,
	continuationTarget?: BlockAddr,
	options: {
		stopBeforeTargets?: AddressSet<BlockAddr>;
		onlyPhiRewrite?: boolean;
	} = {},
) {
	const block = func.blocks.get(target);
	if (!block) return null;
	const body = [
		...prefix.map((stmt) => t.cloneNode(stmt, true)),
		...(<t.Statement[]> block.body).map((stmt) => t.cloneNode(stmt, true)),
	];
	rewriteCompareSwitchPhiBody(body, target, phiRewrite);
	if (options.onlyPhiRewrite) return body;
	if (block.consequentAddresses.length === 0) {
		if (!statementListEndsAbruptly(body)) body.push(t.breakStatement());
		return body;
	}
	if (
		block.consequentAddresses.length === 1 &&
		options.stopBeforeTargets?.has(block.consequentAddresses[0])
	) {
		return body;
	}
	if (
		block.consequentAddresses.length === 1 &&
		switchTargets.has(block.consequentAddresses[0])
	) {
		return body;
	}
	if (
		continuationTarget != null &&
		block.consequentAddresses.length === 1 &&
		block.consequentAddresses[0] === continuationTarget
	) {
		if (!statementListEndsAbruptly(body)) body.push(t.breakStatement());
		return body;
	}
	return null;
}

function statementLiteralDeclarations(
	body: t.Statement[],
	literalConstants: Map<string, t.Expression>,
) {
	const declarations = new Map<string, t.Expression>();
	for (const stmt of body) {
		if (!t.isVariableDeclaration(stmt)) continue;
		if (stmt.declarations.length !== 1) continue;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id)) continue;
		if (t.isIdentifier(decl.init)) {
			const resolved = literalConstants.get(decl.init.name);
			if (resolved) declarations.set(decl.id.name, resolved);
		}
		if (
			!t.isExpression(decl.init) ||
			!stableSwitchExpression(decl.init)
		) continue;
		declarations.set(decl.id.name, decl.init);
	}
	return declarations;
}

function leadingPhiDeclarations(body: t.Statement[]) {
	const phis: Array<{ dest: string; args: t.Expression[] }> = [];
	for (const stmt of body) {
		if (!t.isVariableDeclaration(stmt, { kind: 'const' })) break;
		if (stmt.declarations.length !== 1) break;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id)) break;
		if (!t.isCallExpression(decl.init)) break;
		if (!t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })) {
			break;
		}
		const args = decl.init.arguments;
		if (!args.every((arg) => t.isExpression(arg))) break;
		phis.push({ dest: decl.id.name, args: args as t.Expression[] });
	}
	return phis;
}

function phiDestinationsInBody(body: t.Statement[]) {
	const destinations = new Set<string>();
	for (const stmt of body) {
		if (!t.isVariableDeclaration(stmt, { kind: 'const' })) continue;
		if (stmt.declarations.length !== 1) continue;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id)) continue;
		if (!t.isCallExpression(decl.init)) continue;
		if (!t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })) {
			continue;
		}
		destinations.add(decl.id.name);
	}
	return destinations;
}

function collectCompareSwitchPhiRewrite(
	func: IRFunction,
	cases: CompareSwitchCase[],
	literalConstants: Map<string, t.Expression>,
): FallthroughPhiRewrite {
	const initializerValues = new Map<
		string,
		{ priority: number; expression: t.Expression }
	>();
	const joinDestinations = new Map<BlockAddr, Set<string>>();
	const sourceAssignments = new Map<
		BlockAddr,
		Map<string, { dest: string; expression: t.Expression }>
	>();

	const addJoinDestination = (join: BlockAddr, dest: string) => {
		const destinations = joinDestinations.get(join) ?? new Set<string>();
		destinations.add(dest);
		joinDestinations.set(join, destinations);
	};
	const addSourceAssignment = (
		source: BlockAddr,
		sourceName: string,
		dest: string,
		expression: t.Expression,
	) => {
		const assignments = sourceAssignments.get(source) ??
			new Map<string, { dest: string; expression: t.Expression }>();
		assignments.set(sourceName, {
			dest,
			expression: t.cloneNode(expression, true),
		});
		sourceAssignments.set(source, assignments);
	};
	const addInitializer = (
		dest: string,
		expression: t.Expression,
		priority: number,
	) => {
		const current = initializerValues.get(dest);
		if (current && current.priority > priority) return;
		initializerValues.set(dest, {
			priority,
			expression: t.cloneNode(expression, true),
		});
	};

	for (const entry of cases) {
		const block = func.blocks.get(entry.target);
		if (!block) continue;

		const joins: Array<
			{ join: BlockAddr; sourceDecls: Map<string, t.Expression> }
		> = [];
		if (block.consequentAddresses.length === 1) {
			joins.push({
				join: block.consequentAddresses[0],
				sourceDecls: statementLiteralDeclarations(
					block.body as t.Statement[],
					literalConstants,
				),
			});
		}
		joins.push({
			join: entry.target,
			sourceDecls: statementLiteralDeclarations(
				func.blocks.get(entry.test)?.body as t.Statement[] ??
					entry.prefix,
				literalConstants,
			),
		});

		for (const { join, sourceDecls } of joins) {
			const joinBlock = func.blocks.get(join);
			if (!joinBlock) continue;
			for (
				const { dest, args } of leadingPhiDeclarations(
					joinBlock.body as t.Statement[],
				)
			) {
				for (const arg of args) {
					if (!t.isIdentifier(arg)) continue;
					const sourceInit = sourceDecls.get(arg.name);
					if (!sourceInit) continue;
					addJoinDestination(join, dest);
					addInitializer(
						dest,
						sourceInit,
						entry.target === join ? 1 : 0,
					);
					if (entry.target !== join) {
						addSourceAssignment(
							entry.target,
							arg.name,
							dest,
							sourceInit,
						);
					}
				}
			}
		}
	}

	const initializers = [...initializerValues].map(([dest, { expression }]) =>
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier(dest), expression),
		])
	);

	return { initializers, joinDestinations, sourceAssignments };
}

function rewriteCompareSwitchPhiBody(
	body: t.Statement[],
	target: BlockAddr,
	phiRewrite?: FallthroughPhiRewrite,
) {
	if (!phiRewrite) return;
	const assignments = phiRewrite.sourceAssignments.get(target);
	const joinDestinations = phiRewrite.joinDestinations.get(target);

	for (let i = body.length - 1; i >= 0; i--) {
		const stmt = body[i];
		if (!t.isVariableDeclaration(stmt)) continue;
		if (stmt.declarations.length !== 1) continue;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id)) continue;

		if (joinDestinations?.has(decl.id.name)) {
			if (
				t.isCallExpression(decl.init) &&
				t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })
			) {
				body.splice(i, 1);
			}
			continue;
		}

		const assignment = assignments?.get(decl.id.name);
		if (!assignment) continue;
		body[i] = t.expressionStatement(
			t.assignmentExpression(
				'=',
				t.identifier(assignment.dest),
				t.cloneNode(assignment.expression, true),
			),
		);
	}
}

function isCompareChainContinuation(
	func: IRFunction,
	addr: BlockAddr,
	literalConstants: Map<string, t.Expression>,
) {
	for (const pred of func.predecessorsOf(addr)) {
		const predBlock = func.blocks.get(pred);
		if (!predBlock || predBlock.consequentAddresses[0] !== addr) {
			continue;
		}
		if (parseCompareSwitchTest(predBlock, literalConstants)) return true;
	}
	return false;
}

function collectUniqueLiteralConstants(func: IRFunction) {
	const constants = new Map<string, t.Expression>();
	const invalid = new Set<string>();
	for (const block of func.blocks.values()) {
		for (const stmt of block.body as t.Statement[]) {
			if (!t.isVariableDeclaration(stmt, { kind: 'const' })) continue;
			if (stmt.declarations.length !== 1) continue;
			const [decl] = stmt.declarations;
			if (!t.isIdentifier(decl.id)) continue;
			if (
				!t.isExpression(decl.init) ||
				!stableSwitchExpression(decl.init)
			) continue;
			if (constants.has(decl.id.name)) {
				invalid.add(decl.id.name);
				continue;
			}
			constants.set(decl.id.name, decl.init);
		}
	}
	for (const name of invalid) constants.delete(name);
	return constants;
}

function expressionForPhiArg(body: t.Statement[], name: string) {
	for (const stmt of body) {
		if (!t.isVariableDeclaration(stmt)) continue;
		if (stmt.declarations.length !== 1) continue;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id, { name })) continue;
		return t.isExpression(decl.init) ? decl.init : undefined;
	}
}

function clonedJoinBodyWithPhiSource(
	joinBody: t.Statement[],
	source: t.Expression,
	options: { stripTrailingSwitchMarker?: boolean } = {},
) {
	const [first] = joinBody;
	if (!t.isVariableDeclaration(first, { kind: 'const' })) return null;
	if (first.declarations.length !== 1) return null;
	const [decl] = first.declarations;
	if (!t.isIdentifier(decl.id)) return null;
	if (
		!t.isCallExpression(decl.init) ||
		!t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })
	) return null;
	const phiName = decl.id.name;
	const sourceBody = options.stripTrailingSwitchMarker &&
			isSwitchMarkerStatement(joinBody.at(-1))
		? joinBody.slice(1, -1)
		: joinBody.slice(1);
	const body = sourceBody.map((stmt) => t.cloneNode(stmt, true));
	const wrapped = t.file(t.program(body));
	t.traverseFast(wrapped, (node) => {
		if (!t.isIdentifier(node, { name: phiName })) return;
		for (const key of Object.keys(node)) {
			delete (node as unknown as Record<string, unknown>)[key];
		}
		Object.assign(node, t.cloneNode(source, true));
		return t.traverseFast.skip;
	});
	return wrapped.program.body;
}

function phiAssignmentStatement(dest: string, source: t.Expression) {
	return t.expressionStatement(
		t.assignmentExpression(
			'=',
			t.identifier(dest),
			t.cloneNode(source, true),
		),
	);
}

function sourceIdentifierForPhi(
	phi: { dest: string; args: t.Expression[] },
	sourceBody: t.Statement[],
): t.Identifier | null {
	for (const arg of phi.args) {
		if (!t.isIdentifier(arg)) continue;
		if (expressionForPhiArg(sourceBody, arg.name)) {
			return t.identifier(arg.name);
		}
	}
	return null;
}

function ssaRegisterName(name: string) {
	const match = /^r(\d+)_(\d+)$/.exec(name);
	if (!match) return null;
	return {
		index: Number(match[1]),
		version: Number(match[2]),
	};
}

function loadConstValueToNode(func: IRFunction, value: unknown): t.Expression {
	if (isStringRef(value)) return func.fromStringRef(value);
	if (value === HermesEmpty) return t.identifier('__hermes_empty__');
	return t.valueToNode(value);
}

function expressionForPhiArgFromSSA(
	func: IRFunction,
	sourceAddr: BlockAddr,
	name: string,
): t.Expression | null {
	const reg = ssaRegisterName(name);
	if (!reg) return null;
	const sourceAddrs = [
		sourceAddr,
		...(func.mergedBlocks.get(sourceAddr) ?? new AddressSet<BlockAddr>()),
	];
	for (const addr of sourceAddrs) {
		const ssaBlock = func.ssa.basicBlocks.get(addr);
		if (!ssaBlock) continue;
		for (const instr of ssaBlock.ssaInstructions) {
			if (instr.instruction !== 'LoadConst') continue;
			if (instr.defs.destination.index !== reg.index) continue;
			if (instr.defs.destination.version !== reg.version) continue;
			return loadConstValueToNode(func, instr.value);
		}
	}
	return null;
}

function sourceExpressionForPhi(
	func: IRFunction,
	phi: { dest: string; args: t.Expression[] },
	sourceAddr: BlockAddr,
	sourceBody: t.Statement[],
): t.Expression | null {
	for (const arg of phi.args) {
		if (!t.isIdentifier(arg)) continue;
		const expression = expressionForPhiArg(sourceBody, arg.name) ??
			expressionForPhiArgFromSSA(func, sourceAddr, arg.name);
		if (expression) return expression;
	}
	return null;
}

function switchJoinForTarget(
	func: IRFunction,
	target: BlockAddr,
): { join: BlockAddr; prefix: t.Statement[] } | null {
	const targetBlock = func.blocks.get(target);
	if (!targetBlock || targetBlock.branch) return null;
	if (leadingPhiDeclarations(targetBlock.body as t.Statement[]).length > 0) {
		return { join: target, prefix: [] };
	}
	if (targetBlock.consequentAddresses.length !== 1) return null;
	const join = targetBlock.consequentAddresses[0];
	const joinBlock = func.blocks.get(join);
	if (
		!joinBlock || joinBlock.branch ||
		leadingPhiDeclarations(joinBlock.body as t.Statement[]).length === 0
	) {
		return null;
	}
	return {
		join,
		prefix: (targetBlock.body as t.Statement[]).map((stmt) =>
			t.cloneNode(stmt, true)
		),
	};
}

function reduceSwitchSharedPhi(
	func: IRFunction,
	addr: BlockAddr,
	block: {
		body: LiftedAST<t.Statement>[];
		branch?: LiftedAST<t.Expression>;
		consequentAddresses: BlockAddr[];
	},
	marker: NonNullable<ReturnType<typeof parseSwitchMarker>>,
): boolean {
	const caseCount = marker.labels.length;
	if (marker.targets.length !== caseCount + 1) return false;

	const [defaultTarget, ...caseTargets] = marker.targets;
	const defaultJoin = switchJoinForTarget(func, defaultTarget);
	if (!defaultJoin) return false;
	const join = defaultJoin.join;
	const joinBlock = func.blocks.get(join);
	if (!joinBlock || joinBlock.branch) return false;
	const joinBody = joinBlock.body as t.Statement[];
	const phi = leadingPhiDeclarations(joinBody)[0];
	if (!phi) return false;

	const defaultSource = sourceExpressionForPhi(
		func,
		phi,
		addr,
		block.body.slice(0, -1) as t.Statement[],
	);
	if (!defaultSource) return false;

	const targetInfo = new Map<
		BlockAddr,
		{ prefix: t.Statement[]; source: t.Expression }
	>();
	for (const target of new AddressSet(caseTargets)) {
		if (target === defaultTarget) continue;
		const info = switchJoinForTarget(func, target);
		if (!info || info.join !== join) return false;
		if (target === join) {
			targetInfo.set(target, {
				prefix: info.prefix,
				source: defaultSource,
			});
			continue;
		}
		const targetBlock = func.blocks.get(target);
		if (!targetBlock) return false;
		for (const pred of func.predecessorsOf(target)) {
			if (pred !== addr) return false;
		}
		const source = sourceExpressionForPhi(
			func,
			phi,
			target,
			targetBlock.body as t.Statement[],
		);
		if (!source) return false;
		targetInfo.set(target, { prefix: info.prefix, source });
	}

	const consumedJoinPreds = new AddressSet<BlockAddr>([
		addr,
		defaultTarget,
		...targetInfo.keys(),
	]);
	const consumesJoin = [...func.predecessorsOf(join)].every((pred) =>
		consumedJoinPreds.has(pred)
	);
	if (consumesJoin) {
		const cases: t.SwitchCase[] = [];
		let pendingLabels: t.Expression[] = [];
		let pendingTarget: BlockAddr | null = null;
		const flushPending = () => {
			if (pendingTarget == null || pendingLabels.length === 0) return;
			const info = targetInfo.get(pendingTarget);
			if (!info) {
				pendingLabels = [];
				pendingTarget = null;
				return;
			}
			const consequent = [
				...info.prefix.map((stmt) => t.cloneNode(stmt, true)),
				phiAssignmentStatement(phi.dest, info.source),
				t.breakStatement(),
			];
			for (let i = 0; i < pendingLabels.length; i++) {
				cases.push(
					t.switchCase(
						t.cloneNode(pendingLabels[i], true),
						i === pendingLabels.length - 1
							? consequent.map((stmt) => t.cloneNode(stmt, true))
							: [],
					),
				);
			}
			pendingLabels = [];
			pendingTarget = null;
		};

		for (let i = 0; i < caseTargets.length; i++) {
			const target = caseTargets[i];
			if (target === defaultTarget) {
				flushPending();
				continue;
			}
			if (pendingTarget !== target) {
				flushPending();
				pendingTarget = target;
			}
			pendingLabels.push(marker.labels[i]);
		}
		flushPending();
		cases.push(t.switchCase(null, [
			phiAssignmentStatement(phi.dest, defaultSource),
		]));

		const switchStmt = t.switchStatement(
			t.cloneNode(marker.discriminant, true),
			cases,
		);
		switchStmt.extra = block.body.at(-1)?.extra;
		block.body = [
			...block.body.slice(0, -1),
			t.variableDeclaration('let', [
				t.variableDeclarator(t.identifier(phi.dest)),
			]),
			switchStmt,
			...joinBody.slice(1).map((stmt) => t.cloneNode(stmt, true)),
		];
		block.consequentAddresses = [...joinBlock.consequentAddresses];

		const consumedTargets = new AddressSet([...targetInfo.keys()]);
		for (const target of consumedTargets) {
			func.markMergedBlocks(addr, target);
		}
		func.markMergedBlocks(addr, join);
		return true;
	}
	const cloneOptions = { stripTrailingSwitchMarker: !consumesJoin };
	const defaultTail = clonedJoinBodyWithPhiSource(
		joinBody,
		defaultSource,
		cloneOptions,
	);
	if (!defaultTail) return false;
	if (!statementListEndsAbruptly(defaultTail)) {
		defaultTail.push(t.breakStatement());
	}

	const cases: t.SwitchCase[] = [];
	let pendingLabels: t.Expression[] = [];
	let pendingTarget: BlockAddr | null = null;
	const flushPending = () => {
		if (pendingTarget == null || pendingLabels.length === 0) return;
		const info = targetInfo.get(pendingTarget);
		if (!info) {
			pendingLabels = [];
			pendingTarget = null;
			return;
		}
		for (let i = 0; i < pendingLabels.length; i++) {
			const consequent = i === pendingLabels.length - 1
				? [
					...info.prefix.map((stmt) => t.cloneNode(stmt, true)),
					...(clonedJoinBodyWithPhiSource(
						joinBody,
						info.source,
						cloneOptions,
					) ??
						[]),
				]
				: [];
			if (
				i === pendingLabels.length - 1 &&
				!statementListEndsAbruptly(consequent)
			) {
				consequent.push(t.breakStatement());
			}
			cases.push(
				t.switchCase(t.cloneNode(pendingLabels[i], true), consequent),
			);
		}
		pendingLabels = [];
		pendingTarget = null;
	};

	for (let i = 0; i < caseTargets.length; i++) {
		const target = caseTargets[i];
		if (target === defaultTarget) {
			flushPending();
			continue;
		}
		if (pendingTarget !== target) {
			flushPending();
			pendingTarget = target;
		}
		pendingLabels.push(marker.labels[i]);
	}
	flushPending();

	cases.push(t.switchCase(null, defaultTail));
	const switchStmt = t.switchStatement(
		t.cloneNode(marker.discriminant, true),
		cases,
	);
	switchStmt.extra = block.body.at(-1)?.extra;

	block.body = [...block.body.slice(0, -1), switchStmt];
	block.consequentAddresses = [];

	const consumedTargets = new AddressSet([...targetInfo.keys()]);
	for (const target of consumedTargets) {
		func.markMergedBlocks(addr, target);
	}
	if (consumesJoin) {
		func.markMergedBlocks(addr, join);
	}
	return true;
}

function reduceTwoTargetJoinedSwitch(
	func: IRFunction,
	addr: BlockAddr,
	block: {
		body: LiftedAST<t.Statement>[];
		branch?: LiftedAST<t.Expression>;
		consequentAddresses: BlockAddr[];
	},
	marker: NonNullable<ReturnType<typeof parseSwitchMarker>>,
): boolean {
	const caseCount = marker.labels.length;
	if (marker.targets.length !== caseCount + 1) return false;

	const [defaultTarget, ...caseTargets] = marker.targets;
	const nonDefaultTargets = new AddressSet(
		caseTargets.filter((target) => target !== defaultTarget),
	);
	if (nonDefaultTargets.size !== 1) return false;
	const [caseTarget] = nonDefaultTargets;

	const defaultBlock = func.blocks.get(defaultTarget);
	const caseBlock = func.blocks.get(caseTarget);
	if (!defaultBlock || !caseBlock) return false;
	if (defaultBlock.branch || caseBlock.branch) return false;
	if (
		defaultBlock.consequentAddresses.length !== 1 ||
		caseBlock.consequentAddresses.length !== 1 ||
		defaultBlock.consequentAddresses[0] !==
			caseBlock.consequentAddresses[0]
	) return false;

	for (const target of [defaultTarget, caseTarget]) {
		for (const pred of func.predecessorsOf(target)) {
			if (pred !== addr) return false;
		}
	}

	const labels = caseTargets.flatMap((target, index) =>
		target === caseTarget ? [marker.labels[index]] : []
	);
	if (labels.length === 0) return false;

	const test = t.callExpression(
		t.memberExpression(
			t.arrayExpression(labels.map((label) => t.cloneNode(label, true))),
			t.identifier('includes'),
		),
		[t.cloneNode(marker.discriminant, true)],
	);
	const ifStmt = t.ifStatement(
		test,
		t.blockStatement(
			(caseBlock.body as t.Statement[]).map((stmt) =>
				t.cloneNode(stmt, true)
			),
		),
		t.blockStatement(
			(defaultBlock.body as t.Statement[]).map((stmt) =>
				t.cloneNode(stmt, true)
			),
		),
	);
	ifStmt.extra = block.body.at(-1)?.extra;

	block.body = [
		...block.body.slice(0, -1),
		ifStmt,
	];
	block.consequentAddresses = [defaultBlock.consequentAddresses[0]];
	func.markMergedBlocks(addr, caseTarget);
	func.markMergedBlocks(addr, defaultTarget);
	return true;
}

function reduceSwitchCommonTerminalJoin(
	func: IRFunction,
	addr: BlockAddr,
	block: {
		body: LiftedAST<t.Statement>[];
		branch?: LiftedAST<t.Expression>;
		consequentAddresses: BlockAddr[];
	},
	marker: NonNullable<ReturnType<typeof parseSwitchMarker>>,
): boolean {
	const caseCount = marker.labels.length;
	if (marker.targets.length !== caseCount + 1) return false;

	const [defaultTarget, ...caseTargets] = marker.targets;
	const uniqueTargets = new AddressSet(marker.targets);
	let terminalTarget: BlockAddr | undefined;
	const directBodies = new Map<BlockAddr, t.Statement[]>();

	for (const target of uniqueTargets) {
		const targetBlock = func.blocks.get(target);
		if (!targetBlock || targetBlock.branch) return false;
		if (leadingPhiDeclarations(targetBlock.body as t.Statement[]).length) {
			return false;
		}

		if (targetBlock.consequentAddresses.length === 0) {
			if (terminalTarget == null) {
				terminalTarget = target;
			} else if (terminalTarget !== target) {
				return false;
			}
			directBodies.set(target, []);
			continue;
		}

		if (targetBlock.consequentAddresses.length !== 1) return false;
		const [successor] = targetBlock.consequentAddresses;
		if (terminalTarget == null) {
			terminalTarget = successor;
		} else if (terminalTarget !== successor) {
			return false;
		}
		directBodies.set(target, targetBlock.body as t.Statement[]);
	}

	if (terminalTarget == null) return false;
	const terminalBlock = func.blocks.get(terminalTarget);
	if (
		!terminalBlock || terminalBlock.branch ||
		terminalBlock.consequentAddresses.length !== 0 ||
		leadingPhiDeclarations(terminalBlock.body as t.Statement[]).length
	) {
		return false;
	}

	for (const target of uniqueTargets) {
		for (const pred of func.predecessorsOf(target)) {
			if (target === terminalTarget) {
				if (pred !== addr && !uniqueTargets.has(pred)) return false;
				continue;
			}
			if (pred !== addr) return false;
		}
	}

	for (const pred of func.predecessorsOf(terminalTarget)) {
		if (pred !== addr && !uniqueTargets.has(pred)) return false;
	}

	const terminalBody = terminalBlock.body as t.Statement[];
	const bodyForTarget = (target: BlockAddr): t.Statement[] => {
		const prefix = directBodies.get(target) ?? [];
		return cloneTerminalCaseBody([
			...prefix.map((stmt) => t.cloneNode(stmt, true)),
			...terminalBody.map((stmt) => t.cloneNode(stmt, true)),
		]);
	};

	const cases: t.SwitchCase[] = [];
	let pendingLabels: t.Expression[] = [];
	let pendingTarget: BlockAddr | null = null;
	const flushPending = () => {
		if (pendingTarget == null || pendingLabels.length === 0) return;
		for (let i = 0; i < pendingLabels.length; i++) {
			cases.push(t.switchCase(
				t.cloneNode(pendingLabels[i], true),
				i === pendingLabels.length - 1
					? bodyForTarget(pendingTarget)
					: [],
			));
		}
		pendingLabels = [];
		pendingTarget = null;
	};

	for (let i = 0; i < caseTargets.length; i++) {
		const target = caseTargets[i];
		if (target === defaultTarget) {
			flushPending();
			continue;
		}
		if (pendingTarget !== target) {
			flushPending();
			pendingTarget = target;
		}
		pendingLabels.push(marker.labels[i]);
	}
	flushPending();

	cases.push(t.switchCase(null, bodyForTarget(defaultTarget)));
	const switchStmt = t.switchStatement(
		t.cloneNode(marker.discriminant, true),
		cases,
	);
	switchStmt.extra = block.body.at(-1)?.extra;

	block.body = [...block.body.slice(0, -1), switchStmt];
	block.consequentAddresses = [];
	for (const target of uniqueTargets) {
		func.markMergedBlocks(addr, target);
	}
	func.markMergedBlocks(addr, terminalTarget);
	return true;
}

function reduceSwitchCommonJoin(
	func: IRFunction,
	addr: BlockAddr,
	block: {
		body: LiftedAST<t.Statement>[];
		branch?: LiftedAST<t.Expression>;
		consequentAddresses: BlockAddr[];
	},
	marker: NonNullable<ReturnType<typeof parseSwitchMarker>>,
): boolean {
	if (marker.targets.length !== marker.labels.length + 1) return false;
	const [defaultTarget, ...caseTargets] = marker.targets;
	const uniqueTargets = new AddressSet(marker.targets);
	let join: BlockAddr | null = null;

	for (const target of uniqueTargets) {
		const targetBlock = func.blocks.get(target);
		if (!targetBlock || targetBlock.branch) return false;
		if (leadingPhiDeclarations(targetBlock.body as t.Statement[]).length) {
			return false;
		}
		if (join != null || targetBlock.consequentAddresses.length !== 1) {
			continue;
		}
		const [successor] = targetBlock.consequentAddresses;
		if (uniqueTargets.has(successor)) join = successor;
	}
	if (join == null || !func.blocks.has(join)) return false;

	for (const target of uniqueTargets) {
		const targetBlock = func.blocks.get(target)!;
		if (target === join) continue;
		if (
			targetBlock.consequentAddresses.length !== 1 ||
			targetBlock.consequentAddresses[0] !== join
		) return false;
		for (const predecessor of func.predecessorsOf(target)) {
			if (predecessor !== addr) return false;
		}
	}
	const bodyForTarget = (target: BlockAddr): t.Statement[] => {
		if (target === join) return [];
		const body = (func.blocks.get(target)!.body as t.Statement[]).map(
			(statement) => t.cloneNode(statement, true),
		);
		if (!statementListEndsAbruptly(body)) body.push(t.breakStatement());
		return body;
	};
	const cases: t.SwitchCase[] = [];
	let pendingLabels: t.Expression[] = [];
	let pendingTarget: BlockAddr | null = null;
	const flushPending = () => {
		if (pendingTarget == null || pendingLabels.length === 0) return;
		for (let index = 0; index < pendingLabels.length; index++) {
			cases.push(t.switchCase(
				t.cloneNode(pendingLabels[index], true),
				index === pendingLabels.length - 1
					? bodyForTarget(pendingTarget)
					: [],
			));
		}
		pendingLabels = [];
		pendingTarget = null;
	};
	for (let index = 0; index < caseTargets.length; index++) {
		const target = caseTargets[index];
		if (target === defaultTarget) {
			flushPending();
			continue;
		}
		if (pendingTarget !== target) {
			flushPending();
			pendingTarget = target;
		}
		pendingLabels.push(marker.labels[index]);
	}
	flushPending();
	cases.push(t.switchCase(null, bodyForTarget(defaultTarget)));

	const switchStatement = t.switchStatement(
		t.cloneNode(marker.discriminant, true),
		cases,
	);
	switchStatement.extra = block.body.at(-1)?.extra;
	block.body = [...block.body.slice(0, -1), switchStatement];
	block.consequentAddresses = [join];
	for (const target of uniqueTargets) {
		if (target !== join) func.markMergedBlocks(addr, target);
	}
	return true;
}

function compareChainCaseSource(
	func: IRFunction,
	testAddr: BlockAddr,
	caseTarget: BlockAddr,
): { join: BlockAddr; source: t.Expression; mergeTarget?: BlockAddr } | null {
	const testBlock = func.blocks.get(testAddr);
	const targetBlock = func.blocks.get(caseTarget);
	if (!testBlock || !targetBlock || targetBlock.branch) return null;
	if (targetBlock.consequentAddresses.length === 0) {
		const phi =
			leadingPhiDeclarations(targetBlock.body as t.Statement[])[0];
		if (!phi) return null;
		for (const arg of phi.args) {
			if (!t.isIdentifier(arg)) continue;
			const source = expressionForPhiArg(
				testBlock.body as t.Statement[],
				arg.name,
			);
			if (source) return { join: caseTarget, source };
		}
		return null;
	}
	if (targetBlock.consequentAddresses.length !== 1) return null;
	const [join] = targetBlock.consequentAddresses;
	const joinBlock = func.blocks.get(join);
	if (!joinBlock || joinBlock.branch) return null;
	const phi = leadingPhiDeclarations(joinBlock.body as t.Statement[])[0];
	if (!phi) return null;
	for (const arg of phi.args) {
		if (!t.isIdentifier(arg)) continue;
		const source = expressionForPhiArg(
			targetBlock.body as t.Statement[],
			arg.name,
		);
		if (source) return { join, source, mergeTarget: caseTarget };
	}
	return null;
}

function reduceCompareChainSharedPhiSwitch(func: IRFunction): boolean {
	const switchAddrs = [...func.blocks.keys()].sort((a, b) => b - a);
	const literalConstants = collectUniqueLiteralConstants(func);

	for (const addr of switchAddrs) {
		const block = func.blocks.get(addr);
		if (!block || block.consequentAddresses.length !== 2) continue;
		if (isCompareChainContinuation(func, addr, literalConstants)) {
			continue;
		}
		const firstTest = parseCompareSwitchTest(block, literalConstants);
		if (!firstTest) continue;

		const prefix = block.body.slice(0, firstTest.literalDeclIndex);
		const cases: Array<{
			test: BlockAddr;
			value: t.Expression;
			source: t.Expression;
			mergeTarget?: BlockAddr;
		}> = [];
		const testBlocks: BlockAddr[] = [];
		let cursor: BlockAddr | undefined = addr;
		let joinTarget: BlockAddr | undefined;
		let defaultTarget: BlockAddr | undefined;
		let defaultSource: t.Expression | undefined;
		let canReduce = true;
		const seen = new AddressSet<BlockAddr>();

		while (cursor !== undefined) {
			if (seen.has(cursor)) {
				canReduce = false;
				break;
			}
			seen.add(cursor);
			const testBlock = func.blocks.get(cursor);
			if (!testBlock || testBlock.consequentAddresses.length !== 2) {
				canReduce = false;
				break;
			}
			const test = parseCompareSwitchTest(testBlock, literalConstants);
			if (
				!test ||
				!expressionsEqual(test.discriminant, firstTest.discriminant)
			) {
				canReduce = false;
				break;
			}
			const [falseTarget, trueTarget] = testBlock.consequentAddresses;
			const caseTarget = test.negated ? falseTarget : trueTarget;
			const missTarget = test.negated ? trueTarget : falseTarget;
			const caseInfo = compareChainCaseSource(func, cursor, caseTarget);
			if (!caseInfo) {
				canReduce = false;
				break;
			}
			if (joinTarget == null) joinTarget = caseInfo.join;
			if (joinTarget !== caseInfo.join) {
				canReduce = false;
				break;
			}
			cases.push({
				test: cursor,
				value: test.value,
				source: t.cloneNode(caseInfo.source, true),
				mergeTarget: caseInfo.mergeTarget,
			});
			testBlocks.push(cursor);

			const next = func.blocks.get(missTarget);
			if (
				next &&
				!seen.has(missTarget) &&
				parseCompareSwitchTest(next, literalConstants)
			) {
				cursor = missTarget;
				continue;
			}
			defaultTarget = missTarget;
			const defaultInfo = compareChainCaseSource(
				func,
				cursor,
				missTarget,
			);
			if (defaultInfo?.join === joinTarget) {
				defaultSource = defaultInfo.source;
			}
			break;
		}
		if (
			!canReduce ||
			!joinTarget ||
			defaultTarget == null ||
			cases.length < 2
		) continue;
		const joinBlock = func.blocks.get(joinTarget);
		if (!joinBlock || joinBlock.branch) continue;
		const joinBody = joinBlock.body as t.Statement[];
		const joinPhis = leadingPhiDeclarations(joinBody);
		if (joinPhis.length > 1) {
			if (
				reduceSharedLeadingPhi(func, {
					address: joinTarget,
					maxPhis: 4,
				})
			) return true;
			// The singular switch rewrite below cannot preserve several independent
			// edge values. Leave the graph untouched if provenance lowering cannot
			// consume the whole leading Phi group.
			continue;
		}
		if (isSwitchMarkerStatement(joinBody.at(-1))) {
			const joinPhi = leadingPhiDeclarations(joinBody)[0];
			if (!joinPhi || !defaultSource) continue;

			const switchCases: t.SwitchCase[] = [];
			let pendingSource: string | null = null;
			let pendingValues: t.Expression[] = [];
			let pendingConsequent: t.Statement[] | null = null;
			const flushMaterialized = () => {
				if (!pendingValues.length || !pendingConsequent) return;
				for (let i = 0; i < pendingValues.length; i++) {
					switchCases.push(t.switchCase(
						t.cloneNode(pendingValues[i], true),
						i === pendingValues.length - 1
							? pendingConsequent.map((stmt) =>
								t.cloneNode(stmt, true)
							)
							: [],
					));
				}
				pendingSource = null;
				pendingValues = [];
				pendingConsequent = null;
			};
			for (const entry of cases) {
				const sourceBody = entry.mergeTarget == null
					? []
					: (func.blocks.get(entry.mergeTarget)?.body as
						| t.Statement[]
						| undefined) ?? [];
				const consequent = [
					...sourceBody.map((stmt) => t.cloneNode(stmt, true)),
					phiAssignmentStatement(joinPhi.dest, entry.source),
					t.breakStatement(),
				];
				const sourceKey = JSON.stringify(entry.source);
				if (pendingSource !== sourceKey) {
					flushMaterialized();
					pendingSource = sourceKey;
					pendingConsequent = consequent;
				}
				pendingValues.push(entry.value);
			}
			flushMaterialized();
			let defaultSourceBody = defaultTarget == null
				? []
				: (func.blocks.get(defaultTarget)?.body as
					| t.Statement[]
					| undefined) ?? [];
			const guardedDefault = defaultSourceBody[0];
			const guardedConsequent = t.isIfStatement(guardedDefault)
				? t.isBlockStatement(guardedDefault.consequent)
					? guardedDefault.consequent.body[0]
					: guardedDefault.consequent
				: null;
			if (
				t.isIfStatement(guardedDefault) &&
				t.isBinaryExpression(guardedDefault.test, {
					operator: '===',
				}) &&
				(!t.isBlockStatement(guardedDefault.consequent) ||
					guardedDefault.consequent.body.length === 1) &&
				t.isExpressionStatement(guardedConsequent)
			) {
				const guardedLabel = t.isStringLiteral(guardedDefault.test.left)
					? guardedDefault.test.left
					: t.isStringLiteral(guardedDefault.test.right)
					? guardedDefault.test.right
					: null;
				if (!guardedLabel) {
					switchCases.push(t.switchCase(null, [
						...defaultSourceBody.map((stmt) =>
							t.cloneNode(stmt, true)
						),
						phiAssignmentStatement(joinPhi.dest, defaultSource),
					]));
					defaultSourceBody = [];
				} else {
					switchCases.push(t.switchCase(
						t.cloneNode(guardedLabel, true),
						[
							phiAssignmentStatement(
								joinPhi.dest,
								guardedConsequent.expression,
							),
							t.breakStatement(),
						],
					));
					defaultSourceBody = defaultSourceBody.slice(1);
				}
			}
			if (defaultSourceBody.length > 0) {
				switchCases.push(t.switchCase(null, [
					...defaultSourceBody.map((stmt) => t.cloneNode(stmt, true)),
					phiAssignmentStatement(joinPhi.dest, defaultSource),
				]));
			} else {
				switchCases.push(t.switchCase(null, [
					phiAssignmentStatement(joinPhi.dest, defaultSource),
				]));
			}

			const switchStmt = t.switchStatement(
				t.cloneNode(firstTest.discriminant, true),
				switchCases,
			);
			switchStmt.extra = block.branch?.extra;
			block.body = [
				...prefix,
				t.variableDeclaration('let', [
					t.variableDeclarator(t.identifier(joinPhi.dest)),
				]),
				switchStmt,
				...joinBody.slice(1).map((stmt) => t.cloneNode(stmt, true)),
			];
			block.branch = undefined;
			block.consequentAddresses = [...joinBlock.consequentAddresses];

			for (const testBlock of testBlocks) {
				if (testBlock !== addr) func.markMergedBlocks(addr, testBlock);
			}
			const mergeTargets = new AddressSet(
				cases.flatMap((entry) =>
					entry.mergeTarget == null ? [] : [entry.mergeTarget]
				),
			);
			for (const target of mergeTargets) {
				let onlyChainPredecessors = true;
				for (const pred of func.predecessorsOf(target)) {
					if (!seen.has(pred)) {
						onlyChainPredecessors = false;
						break;
					}
				}
				if (onlyChainPredecessors) func.markMergedBlocks(addr, target);
			}
			func.markMergedBlocks(addr, joinTarget);
			return true;
		}

		const switchCases: t.SwitchCase[] = [];
		let pendingSource: string | null = null;
		let pendingValues: t.Expression[] = [];
		let pendingConsequent: t.Statement[] | null = null;
		const flush = () => {
			if (!pendingValues.length || !pendingConsequent) return;
			for (let i = 0; i < pendingValues.length; i++) {
				switchCases.push(t.switchCase(
					t.cloneNode(pendingValues[i], true),
					i === pendingValues.length - 1
						? pendingConsequent.map((stmt) =>
							t.cloneNode(stmt, true)
						)
						: [],
				));
			}
			pendingSource = null;
			pendingValues = [];
			pendingConsequent = null;
		};
		for (const entry of cases) {
			const consequent = clonedJoinBodyWithPhiSource(
				joinBlock.body as t.Statement[],
				entry.source,
				{ stripTrailingSwitchMarker: true },
			);
			if (!consequent) {
				canReduce = false;
				break;
			}
			const sourceKey = JSON.stringify(entry.source);
			if (pendingSource !== sourceKey) {
				flush();
				pendingSource = sourceKey;
				pendingConsequent = consequent;
			}
			pendingValues.push(entry.value);
		}
		if (!canReduce) continue;
		flush();

		const defaultBody = defaultSource
			? clonedJoinBodyWithPhiSource(
				joinBlock.body as t.Statement[],
				defaultSource,
				{ stripTrailingSwitchMarker: true },
			)
			: [];
		if (defaultBody == null) continue;
		switchCases.push(t.switchCase(null, defaultBody));

		const switchStmt = t.switchStatement(
			t.cloneNode(firstTest.discriminant, true),
			switchCases,
		);
		switchStmt.extra = block.branch?.extra;
		block.body = [...prefix, switchStmt];
		block.branch = undefined;
		block.consequentAddresses = defaultSource ? [] : [defaultTarget];

		for (const testBlock of testBlocks) {
			if (testBlock !== addr) func.markMergedBlocks(addr, testBlock);
		}
		const mergeTargets = new AddressSet(
			cases.flatMap((entry) =>
				entry.mergeTarget == null ? [] : [entry.mergeTarget]
			),
		);
		for (const target of mergeTargets) {
			let onlyChainPredecessors = true;
			for (const pred of func.predecessorsOf(target)) {
				if (!seen.has(pred)) {
					onlyChainPredecessors = false;
					break;
				}
			}
			if (onlyChainPredecessors) func.markMergedBlocks(addr, target);
		}
		return true;
	}

	return false;
}

function reduceCompareChainSwitch(func: IRFunction): boolean {
	const switchAddrs = [...func.blocks.keys()].sort((a, b) => b - a);
	const literalConstants = collectUniqueLiteralConstants(func);

	for (const addr of switchAddrs) {
		const block = func.blocks.get(addr);
		if (!block || block.consequentAddresses.length !== 2) continue;
		if (isCompareChainContinuation(func, addr, literalConstants)) {
			continue;
		}
		const firstTest = parseCompareSwitchTest(block, literalConstants);
		if (!firstTest) continue;

		const prefix = block.body.slice(0, firstTest.literalDeclIndex);
		const cases: CompareSwitchCase[] = [];
		const testBlocks: BlockAddr[] = [];
		const seenTests = new AddressSet<BlockAddr>();
		const activePrefix: t.Statement[] = [];
		let cursor: BlockAddr | undefined = addr;
		let defaultTarget: BlockAddr | undefined;
		let defaultPrefix: t.Statement[] = [];
		let canReduce = true;

		while (cursor !== undefined) {
			if (seenTests.has(cursor)) {
				canReduce = false;
				break;
			}
			seenTests.add(cursor);
			const testBlock = func.blocks.get(cursor);
			if (!testBlock || testBlock.consequentAddresses.length !== 2) {
				canReduce = false;
				break;
			}
			const test = parseCompareSwitchTest(testBlock, literalConstants);
			if (!test) {
				canReduce = false;
				break;
			}
			let casePrefix: t.Statement[] = [];
			if (cursor !== addr) {
				if (blockHasOnlyCompareLiteral(testBlock, test)) {
					casePrefix = activePrefix.map((stmt) =>
						t.cloneNode(stmt, true)
					);
				} else {
					const localPrefix = pureLiteralPrefix(testBlock, test);
					if (localPrefix == null) {
						canReduce = false;
						break;
					}
					casePrefix = [
						...activePrefix.map((stmt) => t.cloneNode(stmt, true)),
						...localPrefix.map((stmt) => t.cloneNode(stmt, true)),
					];
					activePrefix.push(...localPrefix);
				}
			}
			if (!expressionsEqual(test.discriminant, firstTest.discriminant)) {
				canReduce = false;
				break;
			}

			testBlocks.push(cursor);
			const [falseTarget, trueTarget] = testBlock.consequentAddresses;
			const caseTarget = test.negated ? falseTarget : trueTarget;
			const missTarget = test.negated ? trueTarget : falseTarget;
			cases.push({
				test: cursor,
				value: test.value,
				target: caseTarget,
				prefix: casePrefix,
			});

			const next = func.blocks.get(missTarget);
			if (
				!seenTests.has(missTarget) &&
				next &&
				parseCompareSwitchTest(next, literalConstants)
			) {
				cursor = missTarget;
			} else {
				defaultTarget = missTarget;
				defaultPrefix = activePrefix.map((stmt) =>
					t.cloneNode(stmt, true)
				);
				break;
			}
		}

		if (!canReduce || defaultTarget === undefined || cases.length < 2) {
			continue;
		}

		const defaultIsContinuation = defaultTarget === addr;
		const targets = new AddressSet([
			...(defaultIsContinuation ? [] : [defaultTarget]),
			...cases.map(({ target }) => target),
		]);
		const fallthroughTargets = new AddressSet<BlockAddr>();
		for (const target of targets) {
			const targetBlock = func.blocks.get(target);
			if (
				!targetBlock ||
				targetBlock.branch
			) {
				canReduce = false;
				break;
			}
			if (targetBlock.consequentAddresses.length === 1) {
				const [successor] = targetBlock.consequentAddresses;
				if (
					!targets.has(successor) &&
					(!defaultIsContinuation || successor !== addr)
				) {
					canReduce = false;
					break;
				}
				fallthroughTargets.add(target);
			} else if (targetBlock.consequentAddresses.length !== 0) {
				canReduce = false;
				break;
			}
		}
		if (!canReduce) continue;
		for (const target of targets) {
			for (const pred of func.predecessorsOf(target)) {
				if (
					!seenTests.has(pred) && !fallthroughTargets.has(pred) &&
					(!defaultIsContinuation || pred !== addr)
				) {
					canReduce = false;
					break;
				}
			}
			if (!canReduce) break;
		}
		if (!canReduce) continue;

		const phiRewrite = collectCompareSwitchPhiRewrite(
			func,
			cases,
			literalConstants,
		);
		const chainedJoinTarget = [...phiRewrite.joinDestinations.keys()]
			.find((join) => {
				const joinBlock = func.blocks.get(join);
				return joinBlock != null &&
					isSwitchMarkerStatement(
						(joinBlock.body as t.Statement[]).at(-1),
					);
			});
		if (chainedJoinTarget != null) {
			const joinBlock = func.blocks.get(chainedJoinTarget);
			if (!joinBlock || joinBlock.branch) continue;
			const joinBody = joinBlock.body as t.Statement[];
			const joinPhi = leadingPhiDeclarations(joinBody)[0];
			if (!joinPhi) continue;

			const switchCases: t.SwitchCase[] = [];
			let pendingTarget: BlockAddr | null = null;
			let pendingValues: t.Expression[] = [];
			let pendingPrefix: t.Statement[] = [];
			const flushPending = () => {
				if (pendingTarget == null || pendingValues.length === 0) {
					return;
				}
				const body = cloneCompareCaseBody(
					func,
					pendingTarget,
					targets,
					pendingPrefix,
					phiRewrite,
					defaultIsContinuation ? addr : undefined,
					{ stopBeforeTargets: new AddressSet([chainedJoinTarget]) },
				);
				if (body == null) {
					canReduce = false;
					return;
				}
				if (!statementListEndsAbruptly(body)) {
					body.push(t.breakStatement());
				}
				for (let i = 0; i < pendingValues.length; i++) {
					switchCases.push(t.switchCase(
						t.cloneNode(pendingValues[i], true),
						i === pendingValues.length - 1
							? body.map((stmt) => t.cloneNode(stmt, true))
							: [],
					));
				}
				pendingTarget = null;
				pendingValues = [];
				pendingPrefix = [];
			};

			for (const entry of cases) {
				if (entry.target === defaultTarget) {
					flushPending();
					continue;
				}
				const entryPrefixJson = JSON.stringify(entry.prefix);
				const pendingPrefixJson = JSON.stringify(pendingPrefix);
				if (
					pendingTarget !== entry.target ||
					pendingPrefixJson !== entryPrefixJson
				) {
					flushPending();
					pendingTarget = entry.target;
					pendingPrefix = entry.prefix;
				}
				pendingValues.push(entry.value);
			}
			flushPending();
			if (!canReduce) continue;

			const defaultBody = defaultIsContinuation
				? defaultPrefix.map((stmt) => t.cloneNode(stmt, true))
				: cloneCompareCaseBody(
					func,
					defaultTarget,
					targets,
					defaultPrefix,
					phiRewrite,
					undefined,
					{ stopBeforeTargets: new AddressSet([chainedJoinTarget]) },
				);
			if (defaultBody == null) continue;
			if (!statementListEndsAbruptly(defaultBody)) {
				defaultBody.push(t.breakStatement());
			}
			switchCases.push(t.switchCase(null, defaultBody));

			const switchStmt = t.switchStatement(
				t.cloneNode(firstTest.discriminant, true),
				switchCases,
			);
			switchStmt.extra = block.branch?.extra;
			const prefixPhiDestinations = phiDestinationsInBody(
				prefix as t.Statement[],
			);
			const initializers = phiRewrite.initializers.filter((stmt) => {
				const [decl] = stmt.declarations;
				return !t.isIdentifier(decl.id) ||
					!prefixPhiDestinations.has(decl.id.name);
			});
			block.body = [
				...prefix,
				...initializers,
				switchStmt,
				...joinBody.slice(1).map((stmt) => t.cloneNode(stmt, true)),
			];
			block.branch = undefined;
			block.consequentAddresses = [...joinBlock.consequentAddresses];

			for (const testBlock of testBlocks) {
				if (testBlock !== addr) func.markMergedBlocks(addr, testBlock);
			}
			for (const target of targets) {
				if (target !== chainedJoinTarget) {
					func.markMergedBlocks(addr, target);
				}
			}
			func.markMergedBlocks(addr, chainedJoinTarget);
			return true;
		}
		const switchCases: t.SwitchCase[] = [];
		let pendingTarget: BlockAddr | null = null;
		let pendingValues: t.Expression[] = [];
		let pendingPrefix: t.Statement[] = [];
		const flushPending = () => {
			if (pendingTarget == null || pendingValues.length === 0) return;
			for (let i = 0; i < pendingValues.length; i++) {
				const consequent = i === pendingValues.length - 1
					? cloneCompareCaseBody(
						func,
						pendingTarget,
						targets,
						pendingPrefix,
						phiRewrite,
						defaultIsContinuation ? addr : undefined,
					)
					: [];
				if (consequent == null) {
					canReduce = false;
					return;
				}
				switchCases.push(t.switchCase(
					t.cloneNode(pendingValues[i], true),
					consequent,
				));
			}
			pendingTarget = null;
			pendingValues = [];
			pendingPrefix = [];
		};

		for (const entry of cases) {
			if (entry.target === defaultTarget) {
				flushPending();
				continue;
			}
			const entryPrefixJson = JSON.stringify(entry.prefix);
			const pendingPrefixJson = JSON.stringify(pendingPrefix);
			if (
				pendingTarget !== entry.target ||
				pendingPrefixJson !== entryPrefixJson
			) {
				flushPending();
				pendingTarget = entry.target;
				pendingPrefix = entry.prefix;
			}
			pendingValues.push(entry.value);
		}
		flushPending();
		if (!canReduce) continue;
		const defaultBody = defaultIsContinuation
			? defaultPrefix.map((stmt) => t.cloneNode(stmt, true))
			: cloneCompareCaseBody(
				func,
				defaultTarget,
				targets,
				defaultPrefix,
				phiRewrite,
			);
		if (defaultBody == null) continue;
		switchCases.push(t.switchCase(
			null,
			defaultBody,
		));

		const switchStmt = t.switchStatement(
			t.cloneNode(firstTest.discriminant, true),
			switchCases,
		);
		switchStmt.extra = block.branch?.extra;
		const prefixPhiDestinations = phiDestinationsInBody(
			prefix as t.Statement[],
		);
		const initializers = phiRewrite.initializers.filter((stmt) => {
			const [decl] = stmt.declarations;
			return !t.isIdentifier(decl.id) ||
				!prefixPhiDestinations.has(decl.id.name);
		});
		block.body = [...prefix, ...initializers, switchStmt];
		block.branch = undefined;
		block.consequentAddresses = defaultIsContinuation ? [addr] : [];

		for (const testBlock of testBlocks) {
			if (testBlock !== addr) func.markMergedBlocks(addr, testBlock);
		}
		for (const target of targets) {
			func.markMergedBlocks(addr, target);
		}
		return true;
	}

	return false;
}

export function reduceSwitch(func: IRFunction): boolean {
	if (reduceCompareChainSharedPhiSwitch(func)) return true;
	if (reduceCompareChainSwitch(func)) return true;

	const switchAddrs = [...func.blocks.keys()].sort((a, b) => b - a);

	for (const addr of switchAddrs) {
		const block = func.blocks.get(addr);
		if (!block || block.branch) continue;
		const marker = parseSwitchMarker(block);
		if (!marker) continue;
		if (reduceSwitchSharedPhi(func, addr, block, marker)) return true;
		if (reduceTwoTargetJoinedSwitch(func, addr, block, marker)) return true;
		if (reduceSwitchCommonJoin(func, addr, block, marker)) return true;
		if (reduceSwitchCommonTerminalJoin(func, addr, block, marker)) {
			return true;
		}

		const caseCount = marker.labels.length;
		if (marker.targets.length !== caseCount + 1) continue;

		const [defaultTarget, ...caseTargets] = marker.targets;
		const uniqueTargets = new AddressSet(marker.targets);
		const terminalTailByTarget = new Map<BlockAddr, BlockAddr | null>();
		const consumedBlocks = new AddressSet<BlockAddr>(uniqueTargets);
		let canReduce = true;
		for (const target of uniqueTargets) {
			const targetBlock = func.blocks.get(target);
			if (
				targetBlock &&
				phiDestinationsInBody(targetBlock.body as t.Statement[]).size >
					0
			) {
				canReduce = false;
				break;
			}
			if (!targetBlock || targetBlock.branch) {
				canReduce = false;
				break;
			}
			if (targetBlock.consequentAddresses.length === 0) {
				terminalTailByTarget.set(target, null);
				continue;
			}
			if (targetBlock.consequentAddresses.length !== 1) {
				canReduce = false;
				break;
			}
			const [tailAddress] = targetBlock.consequentAddresses;
			const tail = func.blocks.get(tailAddress);
			if (
				!tail || tail.branch || tail.consequentAddresses.length !== 0 ||
				phiDestinationsInBody(tail.body as t.Statement[]).size > 0
			) {
				canReduce = false;
				break;
			}
			terminalTailByTarget.set(target, tailAddress);
			consumedBlocks.add(tailAddress);
		}
		if (!canReduce) continue;
		for (const target of consumedBlocks) {
			for (const pred of func.predecessorsOf(target)) {
				if (pred !== addr && !consumedBlocks.has(pred)) {
					canReduce = false;
					break;
				}
			}
			if (!canReduce) break;
		}
		if (!canReduce) continue;

		const cases: t.SwitchCase[] = [];
		let pendingLabels: t.Expression[] = [];
		let pendingTarget: BlockAddr | null = null;
		const bodyForTarget = (target: BlockAddr) => {
			const targetBody = <t.Statement[]> func.blocks.get(target)?.body ??
				[];
			const tailAddress = terminalTailByTarget.get(target);
			const tailBody = tailAddress == null
				? []
				: <t.Statement[]> func.blocks.get(tailAddress)?.body ?? [];
			return cloneTerminalCaseBody([...targetBody, ...tailBody]);
		};
		const flushPending = () => {
			if (pendingTarget == null || pendingLabels.length === 0) return;
			for (let i = 0; i < pendingLabels.length; i++) {
				const value = pendingLabels[i];
				const consequent = i === pendingLabels.length - 1
					? bodyForTarget(pendingTarget)
					: [];
				cases.push(
					t.switchCase(
						t.cloneNode(value, true),
						consequent,
					),
				);
			}
			pendingLabels = [];
			pendingTarget = null;
		};

		for (let i = 0; i < caseTargets.length; i++) {
			const value = marker.labels[i];
			const target = caseTargets[i];
			if (target === defaultTarget) {
				flushPending();
				continue;
			}
			if (pendingTarget !== target) {
				flushPending();
				pendingTarget = target;
			}
			pendingLabels.push(value);
		}
		flushPending();

		cases.push(
			t.switchCase(
				null,
				bodyForTarget(defaultTarget),
			),
		);
		const switchStmt = t.switchStatement(
			<t.Expression> t.cloneNode(marker.discriminant, true),
			cases,
		);
		switchStmt.extra = block.body.at(-1)?.extra;

		block.body = [
			...block.body.slice(0, -1),
			switchStmt,
		];
		block.consequentAddresses = [];
		for (const target of consumedBlocks) {
			func.markMergedBlocks(addr, target);
		}
		return true;
	}

	return false;
}
