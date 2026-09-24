import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import type { BlockAddr } from '../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../utils/map.ts';
import {
	type SSABasicBlock,
	type SSARegister,
	ssaRegisterEquals,
} from '../../../ssa.ts';
import { liftSSABlocktoIR } from '../../ast/lift.ts';
import type { LiftedAST } from '../../ast/mod.ts';
import type { IRFunction } from '../mod.ts';
import {
	environmentStoreFromStatement,
	isEnvMember,
	loadEnvironmentCall,
} from './envAccess.ts';
import { debugModel } from './debug.ts';
import { roleStateControlSlots } from './recognition.ts';
import {
	caseBodies,
	iteratorResultTerminalFromBody,
	literalValueNode,
	throwTerminalFromBody,
	yieldExpressionStatementValue,
} from './caseUtils.ts';
import type {
	CaseBlockInfo,
	CaseInfo,
	CaseTerminal,
	GeneratorCaseBlockModel,
	GeneratorCaseModel,
	SSAGeneratorModel,
	StateRoles,
	TerminalValue,
} from './types.ts';

function statementIsEnvLoad(stmt: t.Statement, slotIndex: number) {
	if (!t.isVariableDeclaration(stmt)) return false;
	const decl = stmt.declarations[0];
	if (!t.isVariableDeclarator(decl)) return false;
	if (!isEnvMember(decl.init as t.Expression | null | undefined)) {
		return false;
	}
	return loadEnvironmentCall(decl.init as t.Expression)?.slot === slotIndex;
}

export function stripSyntheticStatements(
	body: t.Statement[],
	roles: StateRoles,
) {
	const stateControlSlots = roleStateControlSlots(roles);
	return body.filter((stmt) =>
		!stateControlSlots.has(
			environmentStoreFromStatement(stmt)?.slot ?? -1,
		) &&
		!statementIsEnvLoad(stmt, roles.exceptionHandlerSlot) &&
		!statementIsEnvLoad(stmt, roles.executionStatusSlot ?? -1)
	);
}

function terminalValueExpression(
	func: IRFunction,
	value: TerminalValue,
): t.Expression | null {
	if (value == null) return null;
	if (value.kind === 'register') {
		return registerIdentifier(func, value.register);
	}
	return literalValueNode(func, value.value);
}

function terminalStatementFromModel(
	func: IRFunction,
	terminal: CaseTerminal,
): t.Statement {
	const value = terminalValueExpression(func, terminal.value) ??
		t.identifier('undefined');
	switch (terminal.kind) {
		case 'yield':
			return t.expressionStatement(t.yieldExpression(value));
		case 'iteratorResult':
			return t.expressionStatement(t.yieldExpression(value));
		case 'return':
			return t.returnStatement(value);
		case 'throw':
			return t.throwStatement(value);
	}
}

function registerKey(register: SSARegister) {
	return `${register.index}:${register.version}`;
}

function resumeValueRegisters(func: IRFunction) {
	const registers = new Map<string, SSARegister>();
	for (const block of func.ssa.basicBlocks.values()) {
		for (const instr of block.ssaInstructions) {
			if (
				instr.instruction === 'LoadParam' &&
				instr.parameterIndex === 2
			) {
				registers.set(
					registerKey(instr.defs.destination),
					instr.defs.destination,
				);
			}
		}
	}
	return registers;
}

function sourceRegister(node: t.Identifier) {
	return (node as LiftedAST<t.Identifier>).extra?.sourceRegister;
}

function registerIdentifier(
	func: IRFunction,
	register: SSARegister,
	resumeValue = false,
) {
	const identifier = t.identifier(
		`r${register.index}_${register.version}`,
	) as LiftedAST<t.Identifier>;
	identifier.extra = {
		sourceRegister: register,
		bindingOwnerFunctionId: func.id,
		loweredGeneratorResumeValue: resumeValue,
	};
	return identifier;
}

function firstReferencedRegister(
	stmts: t.Statement[],
	registers: ReadonlyMap<string, SSARegister>,
) {
	let found: SSARegister | undefined;
	const wrapped = t.file(t.program(
		stmts.map((statement) => t.cloneNode(statement, true)),
	));
	traverse(wrapped, {
		Identifier(path: NodePath<t.Identifier>) {
			if (!path.isReferencedIdentifier()) return;
			const register = sourceRegister(path.node);
			if (!register) return;
			found = registers.get(registerKey(register));
			if (found) path.stop();
		},
	});
	return found;
}

function firstReferencedRegisterInCase(
	info: CaseInfo,
	registers: ReadonlyMap<string, SSARegister>,
) {
	if (!info.blocks) return firstReferencedRegister(info.body, registers);
	const statements: t.Statement[] = [];
	for (const block of info.blocks.values()) {
		statements.push(...block.body);
		if (block.branch) {
			statements.push(t.expressionStatement(block.branch));
		}
	}
	return firstReferencedRegister(statements, registers);
}

function replaceResumeReferences(
	func: IRFunction,
	stmts: t.Statement[],
	resumeRegister: SSARegister,
	replacement: SSARegister | string,
) {
	const resumeParam = func.getParam(2);
	const replacementIdentifier = () => {
		const identifier = typeof replacement === 'string'
			? t.identifier(replacement) as LiftedAST<t.Identifier>
			: registerIdentifier(func, replacement, true);
		identifier.extra = {
			...identifier.extra,
			loweredGeneratorResumeValue: true,
		};
		return identifier;
	};
	const wrapped = t.file(t.program(
		stmts.map((statement) => t.cloneNode(statement, true)),
	));
	traverse(wrapped, {
		Identifier(path: NodePath<t.Identifier>) {
			const register = sourceRegister(path.node);
			if (
				register &&
				ssaRegisterEquals(register, resumeRegister)
			) {
				path.replaceWith(replacementIdentifier());
				return;
			}
			if (
				path.isReferencedIdentifier() &&
				t.isIdentifier(resumeParam) &&
				path.node.name === resumeParam.name
			) {
				path.replaceWith(replacementIdentifier());
			}
		},
	});
	stmts.splice(
		0,
		stmts.length,
		...wrapped.program.body as t.Statement[],
	);
}

function replaceResumeReferencesInCase(
	func: IRFunction,
	info: CaseInfo,
	resumeRegister: SSARegister,
	replacement: SSARegister | string,
) {
	if (!info.blocks) {
		replaceResumeReferences(
			func,
			info.body,
			resumeRegister,
			replacement,
		);
		return;
	}
	const statements: t.Statement[] = [];
	const spans: Array<{
		block: CaseBlockInfo;
		start: number;
		bodyLength: number;
		branchIndex: number | null;
	}> = [];
	for (const block of info.blocks.values()) {
		const start = statements.length;
		statements.push(...block.body);
		const branchIndex = block.branch ? statements.length : null;
		if (block.branch) {
			statements.push(t.expressionStatement(block.branch));
		}
		spans.push({
			block,
			start,
			bodyLength: block.body.length,
			branchIndex,
		});
	}
	replaceResumeReferences(
		func,
		statements,
		resumeRegister,
		replacement,
	);
	for (const { block, start, bodyLength, branchIndex } of spans) {
		block.body.splice(
			0,
			block.body.length,
			...statements.slice(start, start + bodyLength),
		);
		if (branchIndex == null) continue;
		const statement = statements[branchIndex];
		if (t.isExpressionStatement(statement)) {
			block.branch = statement.expression;
		}
	}
}

/**
 * Where a case suspends.
 *
 * A case can hold more than one terminal -- an early `throw` guard followed by
 * a `yield`, say -- and only one of them becomes `info.terminal`. Resume values
 * belong to the yields, so they are collected per block with that block's own
 * successor state.
 */
interface YieldSuspension {
	body: t.Statement[];
	nextState: number | null;
	block?: CaseBlockInfo;
}

function yieldSuspensions(info: CaseInfo): YieldSuspension[] {
	if (!info.blocks) {
		if (!yieldExpressionStatementValue(info.terminal)) return [];
		return [{ body: info.body, nextState: info.nextState }];
	}
	const suspensions: YieldSuspension[] = [];
	for (const block of info.blocks.values()) {
		if (!yieldExpressionStatementValue(block.terminal)) continue;
		suspensions.push({
			body: block.body,
			nextState: block.nextState === undefined
				? info.nextState
				: block.nextState,
			block,
		});
	}
	return suspensions;
}

export function bindYieldResumeValues(
	func: IRFunction,
	cases: Map<number, CaseInfo>,
	order: number[],
) {
	const resumeRegisters = resumeValueRegisters(func);
	if (resumeRegisters.size === 0) return [];
	const statesToVisit = new Set(order);
	for (const info of cases.values()) statesToVisit.add(info.state);
	const byNextState = new Map<
		number,
		{
			nextInfo: CaseInfo;
			resumeRegister: SSARegister;
			incoming: Array<{
				info: CaseInfo;
				suspension: YieldSuspension;
				yieldExpression: t.YieldExpression;
				predecessor: BlockAddr;
			}>;
		}
	>();

	for (const state of statesToVisit) {
		const info = cases.get(state);
		if (!info) continue;
		for (const suspension of yieldSuspensions(info)) {
			if (suspension.nextState == null) continue;
			const nextInfo = cases.get(suspension.nextState);
			if (!nextInfo) continue;
			const yieldExpression = yieldExpressionStatementValue(
				suspension.body.at(-1),
			);
			if (!yieldExpression) continue;
			let target = byNextState.get(suspension.nextState);
			if (!target) {
				const resumeRegister = firstReferencedRegisterInCase(
					nextInfo,
					resumeRegisters,
				);
				if (!resumeRegister) continue;
				target = { nextInfo, resumeRegister, incoming: [] };
				byNextState.set(suspension.nextState, target);
			}
			target.incoming.push({
				info,
				suspension,
				yieldExpression,
				predecessor: suspension.block?.address ?? info.address,
			});
		}
	}

	for (const target of byNextState.values()) {
		const uniqueIncoming = [
			...new Map(
				target.incoming.map((incoming) => [
					incoming.predecessor,
					incoming,
				]),
			).values(),
		];
		const resumeVersions = uniqueIncoming.map(() =>
			func.ssa.allocateRegisterVersion(target.resumeRegister.index)
		);
		const resumeVersionByPredecessor = new Map(
			uniqueIncoming.map((incoming, index) => [
				incoming.predecessor,
				resumeVersions[index],
			]),
		);
		const continuation = uniqueIncoming.length === 1
			? resumeVersions[0]
			: func.ssa.allocateRegisterVersion(target.resumeRegister.index);
		replaceResumeReferencesInCase(
			func,
			target.nextInfo,
			target.resumeRegister,
			continuation,
		);

		if (uniqueIncoming.length > 1) {
			const sources = new AddressMap<SSARegister>(
				uniqueIncoming.map((incoming, index) => [
					incoming.predecessor,
					resumeVersions[index],
				]),
			);
			const phi = {
				instruction: 'Phi' as const,
				destination: continuation,
				sources,
			};
			func.ssa.basicBlocks.get(target.nextInfo.address)
				?.ssaInstructions.unshift(phi);
			const entryBody = target.nextInfo.blocks
				?.get(target.nextInfo.address)?.body ?? target.nextInfo.body;
			entryBody.unshift(t.variableDeclaration('const', [
				t.variableDeclarator(
					registerIdentifier(func, continuation, true),
					t.callExpression(
						t.v8IntrinsicIdentifier('Phi'),
						[...sources.values()].map((source) =>
							registerIdentifier(func, source, true)
						),
					),
				),
			]));
		}

		for (
			const { info, suspension, yieldExpression, predecessor } of target
				.incoming
		) {
			const resumeVersion = resumeVersionByPredecessor.get(predecessor)!;
			const replacement = t.variableDeclaration('const', [
				t.variableDeclarator(
					registerIdentifier(func, resumeVersion, true),
					t.cloneNode(yieldExpression, true),
				),
			]);
			suspension.body[suspension.body.length - 1] = replacement;
			if (!suspension.block) {
				info.terminal = replacement;
				continue;
			}
			const previousTerminal = suspension.block.terminal;
			suspension.block.terminal = replacement;
			if (info.terminal === previousTerminal) info.terminal = replacement;
		}
	}
	return [];
}

function liftSSACaseBody(
	func: IRFunction,
	info: GeneratorCaseModel,
) {
	const block = {
		address: info.entry,
		instructions: [],
		ssaInstructions: info.instructions,
		consequentAddresses: [],
		predicate: null,
	} as SSABasicBlock;
	let body = <t.Statement[]> liftSSABlocktoIR(func, block).body;

	const recoveredTerminal = iteratorResultTerminalFromBody(body) ??
		throwTerminalFromBody(body);
	if (recoveredTerminal) {
		body = recoveredTerminal.body;
	}
	while (body.length && t.isReturnStatement(body.at(-1))) body.pop();
	const terminal = terminalStatementFromModel(func, info.terminal);
	body.push(terminal);
	return { body, terminal };
}

function liftSSACaseBlock(
	func: IRFunction,
	info: GeneratorCaseModel,
	blockInfo: GeneratorCaseBlockModel,
) {
	const block = {
		address: blockInfo.address,
		instructions: [],
		ssaInstructions: blockInfo.instructions,
		consequentAddresses: blockInfo.consequentAddresses,
		predicate: null,
	} as SSABasicBlock;
	const lifted = liftSSABlocktoIR(func, block);
	let body = <t.Statement[]> lifted.body;
	const branch = lifted.branch as t.Expression | undefined;
	let terminal: t.Statement | null = null;

	if (blockInfo.terminal) {
		const recoveredTerminal = iteratorResultTerminalFromBody(body) ??
			throwTerminalFromBody(body);
		if (recoveredTerminal) {
			body = recoveredTerminal.body;
		}
		while (body.length && t.isReturnStatement(body.at(-1))) body.pop();
		terminal = terminalStatementFromModel(func, blockInfo.terminal);
		body.push(terminal);
	}

	if (blockInfo.address === info.entry && blockInfo.terminal == null) {
		while (body.length && t.isReturnStatement(body.at(-1))) body.pop();
	}

	return {
		address: blockInfo.address,
		body,
		branch,
		consequentAddresses: blockInfo.consequentAddresses,
		terminal,
		nextState: blockInfo.nextState,
	};
}

function collectCaseFromSSAModel(
	func: IRFunction,
	info: GeneratorCaseModel,
): CaseInfo | undefined {
	const isLinear = info.blocks.size === info.path.length &&
		info.path.every((address, index) => {
			const block = info.blocks.get(address);
			if (!block) return false;
			if (index === info.path.length - 1) return block.terminal != null;
			return block.consequentAddresses.length === 1 &&
				block.consequentAddresses[0] === info.path[index + 1];
		});
	const { body, terminal } = isLinear ? liftSSACaseBody(func, info) : {
		body: [] as t.Statement[],
		terminal: terminalStatementFromModel(func, info.terminal),
	};
	const blocks = isLinear ? undefined : new AddressMap<CaseBlockInfo>();
	if (blocks) {
		for (const [address, blockInfo] of info.blocks) {
			blocks.set(address, liftSSACaseBlock(func, info, blockInfo));
		}
	}
	return {
		state: info.state,
		address: info.entry,
		path: info.path,
		body,
		blocks,
		nextState: info.nextState,
		activeHandlerIndex: info.activeHandlerIndex,
		terminal,
	};
}

export function collectSSACases(
	func: IRFunction,
	ssaModel: SSAGeneratorModel,
) {
	const cases = new Map<number, CaseInfo>();
	try {
		for (const [state, info] of ssaModel.cases) {
			const caseInfo = collectCaseFromSSAModel(func, info);
			if (!caseInfo) return;
			cases.set(state, caseInfo);
		}
	} catch (err) {
		debugModel('SSA case emitter failed', {
			functionId: func.id,
			error: err instanceof Error ? err.message : String(err),
		});
		return;
	}
	return cases;
}
