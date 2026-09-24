import * as t from '@babel/types';
import { env } from 'node:process';
import type { IRFunction } from '../mod.ts';
import type { IRBlock, LiftedAST } from '../../ast/mod.ts';
import { comparableAst } from '../../ast/utils.ts';
import { ssaLivenessAnalysis } from '../../../utils/liveness.ts';

let DEBUG_CONSUMED = false;
try {
	DEBUG_CONSUMED = env['ARES_DEBUG_CONSUMED'] === '1';
} catch { /**/ }
function debugConsumed(...args: unknown[]) {
	if (DEBUG_CONSUMED) console.error('[consumed]', ...args);
}

export function expressionStatementAssignment(
	stmt: t.Statement | undefined,
): t.AssignmentExpression | null {
	if (!stmt || !t.isExpressionStatement(stmt)) return null;
	if (!t.isAssignmentExpression(stmt.expression, { operator: '=' })) {
		return null;
	}
	return stmt.expression;
}

function collectNodeAddresses(
	node: t.Node,
	addresses: Set<number>,
	ignoredSignatures = new Set<string>(),
) {
	if (
		t.isNumericLiteral(node) ||
		t.isStringLiteral(node) ||
		t.isBooleanLiteral(node) ||
		t.isNullLiteral(node) ||
		t.isIdentifier(node, { name: 'undefined' }) ||
		t.isIdentifier(node, { name: 'global' })
	) return;

	if (
		t.isExpression(node) &&
		ignoredSignatures.has(JSON.stringify(comparableAst(node)))
	) return;

	const address = (node as LiftedAST<t.Node>).extra?.address;
	if (address != null) addresses.add(address);

	for (const key of t.VISITOR_KEYS[node.type] ?? []) {
		const child = node[key as keyof typeof node];
		if (Array.isArray(child)) {
			for (const element of child) {
				if (t.isNode(element)) {
					collectNodeAddresses(element, addresses, ignoredSignatures);
				}
			}
		} else if (t.isNode(child)) {
			collectNodeAddresses(child, addresses, ignoredSignatures);
		}
	}
}

function statementAddresses(
	stmt: t.Statement | undefined,
	ignoredAddresses: Set<number>,
	ignoredSignatures: Set<string>,
): number[] {
	if (!stmt) return [];
	const addresses = new Set<number>();
	collectNodeAddresses(stmt, addresses, ignoredSignatures);
	return [...addresses].filter((address) => !ignoredAddresses.has(address));
}

function collectGeneratedBindingNames(node: t.Node, names: Set<string>) {
	if (t.isIdentifier(node) && /^(?:r\d+_\d+|e_\d+)$/.test(node.name)) {
		names.add(node.name);
	}
}

function rawRegisterIndexFromGeneratedName(name: string): number | null {
	const match = /^r(\d+)_\d+$/.exec(name);
	return match ? Number(match[1]) : null;
}

function collectGeneratedDefinitions(stmt: t.Statement, names: Set<string>) {
	if (t.isVariableDeclaration(stmt)) {
		for (const decl of stmt.declarations) {
			if (t.isIdentifier(decl.id)) {
				collectGeneratedBindingNames(decl.id, names);
			} else if (t.isArrayPattern(decl.id)) {
				for (const element of decl.id.elements) {
					if (t.isIdentifier(element)) {
						collectGeneratedBindingNames(element, names);
					}
				}
			}
		}
		return;
	}

	const assign = expressionStatementAssignment(stmt);
	if (assign && t.isIdentifier(assign.left)) {
		collectGeneratedBindingNames(assign.left, names);
		return;
	}

	if (t.isIfStatement(stmt)) {
		if (t.isBlockStatement(stmt.consequent)) {
			for (const child of stmt.consequent.body) {
				collectGeneratedDefinitions(child, names);
			}
		}
		if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
			for (const child of stmt.alternate.body) {
				collectGeneratedDefinitions(child, names);
			}
		}
	} else if (t.isBlockStatement(stmt)) {
		for (const child of stmt.body) {
			collectGeneratedDefinitions(child, names);
		}
	} else if (t.isTryStatement(stmt)) {
		for (const child of stmt.block.body) {
			collectGeneratedDefinitions(child, names);
		}
	} else if (t.isWhileStatement(stmt) && t.isBlockStatement(stmt.body)) {
		for (const child of stmt.body.body) {
			collectGeneratedDefinitions(child, names);
		}
	}
}

function containsIdentifier(node: t.Node, names: Set<string>): boolean {
	if (t.isIdentifier(node) && names.has(node.name)) return true;
	for (const key of t.VISITOR_KEYS[node.type] ?? []) {
		const child = node[key as keyof typeof node];
		if (Array.isArray(child)) {
			if (
				child.some((element) =>
					t.isNode(element) && containsIdentifier(element, names)
				)
			) return true;
		} else if (t.isNode(child) && containsIdentifier(child, names)) {
			return true;
		}
	}
	return false;
}

export function consumedDefinitionsAreDead(
	func: IRFunction,
	block: IRBlock,
	stmts: t.Statement[],
	preservedInputs: t.Node[],
	inlineConsumedResults: t.Node[],
	escapedNames: Set<string> = new Set(),
	skipIdentifierCheck = false,
	body: t.Statement[] = <t.Statement[]> block.body,
): boolean {
	const consumedStmtSet = new Set(stmts);
	const consumedNames = new Set<string>();
	for (const stmt of stmts) collectGeneratedDefinitions(stmt, consumedNames);
	if (!skipIdentifierCheck) {
		const checkNames = escapedNames.size > 0
			? new Set([...consumedNames].filter((n) => !escapedNames.has(n)))
			: consumedNames;
		if (checkNames.size > 0) {
			for (const stmt of body) {
				if (consumedStmtSet.has(stmt as t.Statement)) continue;
				if (containsIdentifier(stmt as t.Statement, checkNames)) {
					debugConsumed('identifier', {
						checkNames: [...checkNames],
						stmtType: stmt.type,
					});
					return false;
				}
			}
		}
	}
	const consumedNamedRawRegs = new Set(
		[...consumedNames].flatMap((name) => {
			const index = rawRegisterIndexFromGeneratedName(name);
			return index == null ? [] : [index];
		}),
	);

	const ignoredAddresses = new Set<number>();
	const ignoredSignatures = new Set<string>();
	for (const input of preservedInputs) {
		collectNodeAddresses(input, ignoredAddresses);
		if (t.isExpression(input)) {
			ignoredSignatures.add(JSON.stringify(comparableAst(input)));
		}
	}
	const addresses = stmts.flatMap((stmt) =>
		statementAddresses(stmt, ignoredAddresses, ignoredSignatures)
	);
	const liveness = ssaLivenessAnalysis(func.ssa);

	const byAddress = new Map<
		number,
		{ blockAddr: number; instrIndex: number }
	>();
	for (const [blockAddr, rawBlock] of func.ssa._func.basicBlocks) {
		for (const [instrIndex, instr] of rawBlock.instructions.entries()) {
			byAddress.set(instr.functionLocalOffset, { blockAddr, instrIndex });
		}
	}
	const allowedLiveOutDefs = new Set<string>();
	for (const result of inlineConsumedResults) {
		const address = (result as LiftedAST<t.Node>).extra?.address;
		if (address == null) continue;
		const location = byAddress.get(address);
		if (location) {
			allowedLiveOutDefs.add(
				`${location.blockAddr}:${location.instrIndex}`,
			);
		}
	}

	const consumed = new Map<number, Set<number>>();
	const consumedDefRegs = new Set<number>();
	const lastConsumedAccess = new Map<string, number>();
	for (const address of addresses) {
		const location = byAddress.get(address);
		if (!location) return false;
		const instrLiveness = liveness.instrLiveness.get(location.blockAddr);
		if (!instrLiveness) return false;
		const blockConsumed = consumed.get(location.blockAddr) ??
			new Set<number>();
		blockConsumed.add(location.instrIndex);
		consumed.set(location.blockAddr, blockConsumed);
		const live = instrLiveness[location.instrIndex];
		for (const def of live?.defs ?? []) {
			consumedDefRegs.add(def);
			lastConsumedAccess.set(
				`${location.blockAddr}:${def}`,
				Math.max(
					lastConsumedAccess.get(`${location.blockAddr}:${def}`) ??
						-1,
					location.instrIndex,
				),
			);
		}
		for (const reg of [...live?.uses ?? [], ...live?.defs ?? []]) {
			const key = `${location.blockAddr}:${reg}`;
			if (!consumedDefRegs.has(reg) && !lastConsumedAccess.has(key)) {
				continue;
			}
			lastConsumedAccess.set(
				key,
				Math.max(
					lastConsumedAccess.get(key) ?? -1,
					location.instrIndex,
				),
			);
		}
	}
	if (consumedDefRegs.size === 0) return true;

	for (const [key, instrIndex] of lastConsumedAccess) {
		const [blockAddrText, regText] = key.split(':');
		const blockAddr = Number(blockAddrText);
		const reg = Number(regText);
		if (!consumedDefRegs.has(reg)) continue;
		const live = liveness.instrLiveness.get(blockAddr)?.[instrIndex];
		if (
			live?.liveOut.has(reg) &&
			!consumedNamedRawRegs.has(reg) &&
			!allowedLiveOutDefs.has(`${blockAddr}:${instrIndex}`)
		) {
			debugConsumed('liveout', {
				blockAddr,
				instrIndex,
				reg,
				consumedNamedRawRegs: [...consumedNamedRawRegs],
				allowedLiveOutDefs: [...allowedLiveOutDefs],
			});
			return false;
		}
	}

	return true;
}
