import type * as t from '@babel/types';
import * as bt from '@babel/types';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { CFGBlock, ImmutableCFG } from '../immutableCFG.ts';
import type { SwitchCaseEdge } from '../terminator.ts';

export interface SwitchCaseDescriptor {
	test: t.Expression | null;
	target: BlockAddr;
	source?: BlockAddr;
	prefix?: t.Statement[];
}

export interface SwitchDescriptor {
	dispatchBlock: BlockAddr;
	/** Stable declarations evaluated before a recovered comparison chain. */
	prelude?: t.Statement[];
	discriminant: t.Expression;
	cases: SwitchCaseDescriptor[];
	defaultTarget: BlockAddr;
	defaultSource?: BlockAddr;
	join?: BlockAddr;
	coveredBlocks?: AddressSet<BlockAddr>;
	kind?: 'terminator' | 'compareChain';
}

export interface SwitchDescriptorInfo {
	switches: SwitchDescriptor[];
	switchByDispatch: AddressMap<SwitchDescriptor>;
}

export function recoverSwitchDescriptors(
	cfg: ImmutableCFG,
): SwitchDescriptorInfo {
	const switches: SwitchDescriptor[] = [];
	const switchByDispatch = new AddressMap<SwitchDescriptor>();
	const compareChainDispatches = recoverCompareChainSwitchDescriptors(cfg);
	for (const descriptor of compareChainDispatches) {
		switches.push(descriptor);
		switchByDispatch.set(descriptor.dispatchBlock, descriptor);
	}
	for (const [addr, block] of cfg.blocks) {
		if (switchByDispatch.has(addr)) continue;
		const descriptor = descriptorFromBlock(addr, block);
		if (!descriptor) continue;
		switches.push(descriptor);
		switchByDispatch.set(addr, descriptor);
	}
	return { switches, switchByDispatch };
}

function descriptorFromBlock(
	addr: BlockAddr,
	block: CFGBlock,
): SwitchDescriptor | null {
	if (block.terminator.kind !== 'switch') return null;
	return {
		dispatchBlock: addr,
		discriminant: block.terminator.discriminant,
		cases: block.terminator.cases.map((edge) => ({
			...caseDescriptor(edge),
			source: addr,
		})),
		defaultTarget: block.terminator.defaultTarget,
		defaultSource: addr,
		kind: 'terminator',
	};
}

function caseDescriptor(edge: SwitchCaseEdge): SwitchCaseDescriptor {
	return {
		test: edge.test,
		target: edge.target,
	};
}

interface CompareSwitchTest {
	rawDiscriminant: t.Expression;
	discriminant: t.Expression;
	value: t.Expression;
	negated: boolean;
	literalDeclIndex: number;
}

function recoverCompareChainSwitchDescriptors(
	cfg: ImmutableCFG,
): SwitchDescriptor[] {
	const descriptors: SwitchDescriptor[] = [];
	const literalConstants = collectUniqueLiteralConstants(cfg);
	const addrs = [...cfg.blocks.keys()].sort((a, b) => b - a);

	for (const addr of addrs) {
		if (isCompareChainContinuation(cfg, addr, literalConstants)) continue;
		const block = cfg.blocks.get(addr);
		const firstTest = block
			? parseCompareSwitchTest(
				block,
				literalConstants,
			)
			: null;
		if (!firstTest) continue;
		if (!hasOnlyStableComparePrefix(block!, firstTest)) continue;

		const cases: SwitchCaseDescriptor[] = [];
		const prelude: t.Statement[] = [];
		const coveredBlocks = new AddressSet<BlockAddr>();
		let cursor: BlockAddr | undefined = addr;
		let defaultTarget: BlockAddr | undefined;
		let defaultSource: BlockAddr | undefined;
		let canRecover = true;

		while (cursor !== undefined) {
			if (coveredBlocks.has(cursor)) {
				canRecover = false;
				break;
			}
			const testBlock = cfg.blocks.get(cursor);
			const test = testBlock
				? parseCompareSwitchTest(testBlock, literalConstants)
				: null;
			if (!test || !hasOnlyStableComparePrefix(testBlock!, test)) {
				canRecover = false;
				break;
			}
			if (!expressionsEqual(test.discriminant, firstTest.discriminant)) {
				canRecover = false;
				break;
			}
			const targets = compareTestTargets(testBlock!, test);
			if (!targets) {
				canRecover = false;
				break;
			}

			coveredBlocks.add(cursor);
			const testPrelude = compareSwitchPrelude(
				testBlock!,
				test,
				cursor === addr,
			);
			if (!testPrelude) {
				canRecover = false;
				break;
			}
			prelude.push(...testPrelude);
			cases.push({
				test: bt.cloneNode(test.value, true),
				target: targets.caseTarget,
				source: cursor,
			});

			const next = cfg.blocks.get(targets.missTarget);
			if (
				next &&
				!coveredBlocks.has(targets.missTarget) &&
				parseCompareSwitchTest(next, literalConstants)
			) {
				cursor = targets.missTarget;
				continue;
			}
			defaultTarget = targets.missTarget;
			defaultSource = cursor;
			break;
		}

		if (!canRecover || defaultTarget == null || cases.length < 2) continue;
		// Parse the complete comparison graph before deciding whether it is a
		// switch. Rejecting one dynamic comparison while discovering chain heads
		// can expose a nested literal suffix as a new switch and steal ownership
		// from an enclosing if/loop Region. A complete dynamic ladder is still
		// rejected because switch case evaluation would make it eager.
		if (
			!cases.every((switchCase) =>
				switchCase.test != null &&
				stableSwitchCaseValue(switchCase.test)
			)
		) continue;
		descriptors.push({
			dispatchBlock: addr,
			prelude,
			discriminant: bt.cloneNode(firstTest.rawDiscriminant, true),
			cases,
			defaultTarget,
			defaultSource,
			coveredBlocks,
			kind: 'compareChain',
		});
	}

	return descriptors;
}

function compareSwitchPrelude(
	block: CFGBlock,
	test: CompareSwitchTest,
	first: boolean,
): t.Statement[] | undefined {
	const prefix = compareCasePrefix(block, test);
	if (!prefix) return undefined;
	if (!first) {
		for (const statement of prefix) {
			if (!bt.isVariableDeclaration(statement)) return undefined;
			const [declaration] = statement.declarations;
			if (
				!declaration || !bt.isExpression(declaration.init) ||
				!stableSwitchCaseValue(declaration.init)
			) return undefined;
		}
	}
	// A chain block also computes the value its own edge contributes to a join.
	// The dispatch replaces the block, so that declaration has to survive as part
	// of the prelude; a chain that computes it with something observable keeps
	// its equality ladder instead.
	const suffix = compareCaseSuffix(block, test);
	if (!suffix) return undefined;
	const literalDeclaration = block.body[test.literalDeclIndex];
	return [
		...prefix,
		...(literalDeclaration &&
				bt.isVariableDeclaration(literalDeclaration)
			? [bt.cloneNode(literalDeclaration, true)]
			: []),
		...suffix,
	];
}

/** Stable declarations a chain block evaluates after its case literal. */
function compareCaseSuffix(
	block: CFGBlock,
	test: CompareSwitchTest,
): t.Statement[] | undefined {
	const suffix = block.body.slice(test.literalDeclIndex + 1);
	for (const statement of suffix) {
		if (!bt.isVariableDeclaration(statement, { kind: 'const' })) {
			return undefined;
		}
		if (statement.declarations.length !== 1) return undefined;
		const [declaration] = statement.declarations;
		if (
			!bt.isIdentifier(declaration.id) ||
			!bt.isExpression(declaration.init) ||
			!stableSwitchExpression(declaration.init)
		) return undefined;
	}
	return suffix.map((statement) => bt.cloneNode(statement, true));
}

function parseCompareSwitchTest(
	block: CFGBlock,
	literalConstants: Map<string, t.Expression>,
): CompareSwitchTest | null {
	if (block.terminator.kind !== 'if') return null;
	let branch = block.terminator.test;
	let negated = false;
	if (
		bt.isUnaryExpression(branch, { operator: '!' }) &&
		bt.isBinaryExpression(branch.argument, { operator: '===' })
	) {
		branch = branch.argument;
		negated = true;
	}
	if (bt.isBinaryExpression(branch, { operator: '!==' })) {
		branch = bt.binaryExpression('===', branch.left, branch.right);
		negated = true;
	}
	if (!bt.isBinaryExpression(branch, { operator: '===' })) return null;

	let literalName: string | undefined;
	let literalInit: t.Expression | undefined;
	if (bt.isIdentifier(branch.left)) {
		literalName = branch.left.name;
	} else if (
		bt.isExpression(branch.left) && stableSwitchExpression(branch.left)
	) {
		literalInit = branch.left;
	} else {
		return null;
	}

	const literalDeclIndex = literalName == null ? -1 : block.body.findIndex(
		(stmt) => {
			if (!bt.isVariableDeclaration(stmt, { kind: 'const' })) {
				return false;
			}
			if (stmt.declarations.length !== 1) return false;
			const [decl] = stmt.declarations;
			return bt.isIdentifier(decl.id, { name: literalName }) &&
				bt.isExpression(decl.init) &&
				stableSwitchExpression(decl.init);
		},
	);

	if (literalInit == null && literalDeclIndex === -1) {
		if (literalName == null) return null;
		literalInit = literalConstants.get(literalName);
		if (!literalInit) return null;
	} else if (literalInit == null) {
		const decl = (block.body[literalDeclIndex] as t.VariableDeclaration)
			.declarations[0];
		if (!bt.isExpression(decl.init)) return null;
		literalInit = decl.init;
	}
	if (!bt.isExpression(branch.right)) return null;
	return {
		rawDiscriminant: bt.cloneNode(branch.right, true),
		discriminant: resolveStableAlias(branch.right, literalConstants),
		value: literalInit,
		negated,
		literalDeclIndex: literalDeclIndex === -1
			? block.body.length
			: literalDeclIndex,
	};
}

function stableSwitchCaseValue(expr: t.Expression): boolean {
	if (
		bt.isNumericLiteral(expr) ||
		bt.isStringLiteral(expr) ||
		bt.isBooleanLiteral(expr) ||
		bt.isNullLiteral(expr)
	) return true;
	if (bt.isIdentifier(expr)) return expr.name === 'undefined';
	return bt.isUnaryExpression(expr) &&
		expr.operator !== 'delete' &&
		bt.isExpression(expr.argument) &&
		stableSwitchCaseValue(expr.argument);
}

function compareTestTargets(
	block: CFGBlock,
	test: CompareSwitchTest,
): { caseTarget: BlockAddr; missTarget: BlockAddr } | null {
	if (block.terminator.kind !== 'if') return null;
	const falseTarget = block.terminator.fallthrough;
	const trueTarget = block.terminator.taken;
	return {
		caseTarget: test.negated ? falseTarget : trueTarget,
		missTarget: test.negated ? trueTarget : falseTarget,
	};
}

function isCompareChainContinuation(
	cfg: ImmutableCFG,
	addr: BlockAddr,
	literalConstants: Map<string, t.Expression>,
): boolean {
	const predecessors = cfg.normalPredecessors.get(addr) ??
		new AddressSet<BlockAddr>();
	for (const pred of predecessors) {
		const predBlock = cfg.blocks.get(pred);
		if (!predBlock) continue;
		const predTest = parseCompareSwitchTest(predBlock, literalConstants);
		if (!predTest) continue;
		const targets = compareTestTargets(predBlock, predTest);
		if (targets?.missTarget === addr) return true;
	}
	return false;
}

function hasOnlyStableComparePrefix(
	block: CFGBlock,
	test: CompareSwitchTest,
): boolean {
	return compareCasePrefix(block, test) != null;
}

function compareCasePrefix(
	block: CFGBlock,
	test: CompareSwitchTest,
): t.Statement[] | undefined {
	const prefix = block.body.slice(0, test.literalDeclIndex);
	if (prefix.length === 0) return [];
	for (const stmt of prefix) {
		if (!bt.isVariableDeclaration(stmt, { kind: 'const' })) {
			return undefined;
		}
		if (stmt.declarations.length !== 1) return undefined;
		const [decl] = stmt.declarations;
		if (!bt.isIdentifier(decl.id)) return undefined;
		if (
			!bt.isExpression(decl.init) ||
			!stableSwitchExpression(decl.init)
		) {
			return undefined;
		}
	}
	return prefix.map((stmt) => bt.cloneNode(stmt, true));
}

function collectUniqueLiteralConstants(
	cfg: ImmutableCFG,
): Map<string, t.Expression> {
	const constants = new Map<string, t.Expression>();
	const invalid = new Set<string>();
	for (const block of cfg.blocks.values()) {
		for (const stmt of block.body) {
			if (!bt.isVariableDeclaration(stmt, { kind: 'const' })) continue;
			if (stmt.declarations.length !== 1) continue;
			const [decl] = stmt.declarations;
			if (!bt.isIdentifier(decl.id)) continue;
			if (
				!bt.isExpression(decl.init) ||
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

function stableSwitchExpression(
	expr: t.Expression | null | undefined,
): boolean {
	if (!expr) return false;
	if (
		bt.isNumericLiteral(expr) ||
		bt.isStringLiteral(expr) ||
		bt.isBooleanLiteral(expr) ||
		bt.isNullLiteral(expr) ||
		bt.isIdentifier(expr) ||
		bt.isThisExpression(expr)
	) return true;
	if (bt.isUnaryExpression(expr)) {
		return expr.operator !== 'delete' &&
			bt.isExpression(expr.argument) &&
			stableSwitchExpression(expr.argument);
	}
	if (bt.isMemberExpression(expr)) {
		return bt.isExpression(expr.object) &&
			stableSwitchExpression(expr.object) &&
			(!expr.computed ||
				(bt.isExpression(expr.property) &&
					stableSwitchExpression(expr.property)));
	}
	if (bt.isCallExpression(expr)) {
		return bt.isV8IntrinsicIdentifier(expr.callee, {
			name: 'expectEnvironment',
		}) && expr.arguments.every((arg) => bt.isExpression(arg));
	}
	return false;
}

function resolveStableAlias(
	expr: t.Expression,
	literalConstants: Map<string, t.Expression>,
	seen = new Set<string>(),
): t.Expression {
	if (!bt.isIdentifier(expr) || seen.has(expr.name)) return expr;
	const resolved = literalConstants.get(expr.name);
	if (!resolved) return expr;
	seen.add(expr.name);
	return resolveStableAlias(resolved, literalConstants, seen);
}

function expressionsEqual(left: t.Expression, right: t.Expression): boolean {
	return JSON.stringify(left) === JSON.stringify(right);
}
