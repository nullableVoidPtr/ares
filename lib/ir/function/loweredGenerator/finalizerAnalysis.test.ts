import { strict as assert } from 'node:assert';
import * as t from '@babel/types';
import type { BlockAddr } from '../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../utils/map.ts';
import type { IRFunction } from '../mod.ts';
import { caseContinuation } from './caseUtils.ts';
import { analyseFinalizerCopies } from './finalizerAnalysis.ts';
import type { CaseBlockInfo, CaseInfo, StateRoles } from './types.ts';

function environmentLoad(slot: number) {
	return t.variableDeclaration('const', [
		t.variableDeclarator(
			t.identifier(`r${slot}_1`),
			t.memberExpression(
				t.callExpression(t.v8IntrinsicIdentifier('expectEnvironment'), [
					t.identifier('env'),
				]),
				t.numericLiteral(slot),
				true,
			),
		),
	]);
}

function terminalBlock(
	address: number,
	nextState: number | null,
	body: t.Statement[] = [],
): CaseBlockInfo {
	return {
		address: address as BlockAddr,
		body,
		consequentAddresses: [],
		terminal: t.expressionStatement(
			t.yieldExpression(t.identifier('value')),
		),
		nextState,
	};
}

function caseInfo(
	state: number,
	terminal: t.Statement,
	blocks?: AddressMap<CaseBlockInfo>,
): CaseInfo {
	return {
		state,
		address: state,
		path: blocks ? [...blocks.keys()] : [],
		body: [],
		blocks,
		nextState: null,
		activeHandlerIndex: null,
		terminal,
	};
}

Deno.test('case continuation ignores abrupt exits beside one suspension', () => {
	const blocks = new AddressMap<CaseBlockInfo>([
		[1 as BlockAddr, {
			address: 1 as BlockAddr,
			body: [],
			consequentAddresses: [],
			terminal: t.throwStatement(t.identifier('error')),
			nextState: null,
		}],
		[2 as BlockAddr, terminalBlock(2, 4)],
	]);
	const info = caseInfo(0, blocks.get(1)!.terminal!, blocks);

	assert.deepEqual(caseContinuation(info), {
		kind: 'unique',
		states: [4],
		state: 4,
	});
});

Deno.test('finalizer analysis declines a case with multiple continuations', () => {
	const caughtSlot = 7;
	const finalizerBlocks = new AddressMap<CaseBlockInfo>([
		[10 as BlockAddr, terminalBlock(10, 2, [environmentLoad(caughtSlot)])],
		[11 as BlockAddr, terminalBlock(11, 3, [environmentLoad(caughtSlot)])],
	]);
	const caught = caseInfo(
		0,
		t.throwStatement(t.identifier('caught')),
	);
	caught.body = [environmentLoad(caughtSlot)];
	caught.activeHandlerIndex = 2;
	const finalizer = caseInfo(
		1,
		t.throwStatement(t.identifier('caught')),
		finalizerBlocks,
	);
	const cases = new Map([
		[0, caught],
		[1, finalizer],
	]);
	const roles: StateRoles = {
		actionRegister: 0,
		switchSlot: 1,
		stateEnvRegisterIndex: 0,
		exceptionHandlerSlot: 2,
		caughtExceptionSlot: caughtSlot,
		mainSwitchAddress: 0,
		handlerIndexToState: new Map([[1, 0], [2, 1]]),
		constants: new Map(),
	};

	const result = analyseFinalizerCopies(
		{} as IRFunction,
		cases,
		roles,
		new Map([[0, 0], [1, 1]]),
	);

	assert.equal(result.finalizerStates.has(1), false);
	assert.deepEqual(result.declines, [{
		state: 1,
		continuations: [2, 3],
		reason: 'multiple-continuations',
	}]);
});
