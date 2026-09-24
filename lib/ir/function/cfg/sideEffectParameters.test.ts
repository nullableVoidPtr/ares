import { strict as assert } from 'node:assert';
import generate from '@babel/generator';
import * as t from '@babel/types';
import { tagStorageLocation } from '../../ast/alias.ts';
import type { IRFunction } from '../mod.ts';
import {
	createParameterPlan,
	materializeParameterPlan,
} from './parameterPlan.ts';
import { reduceSideEffectOnlyOverflowDefault } from './sideEffectParameters.ts';

const intrinsic = (name: string, args: t.Expression[]) =>
	t.callExpression(t.v8IntrinsicIdentifier(name), args);

Deno.test('recovers an unused array-valued default before CFG reduction', () => {
	const functionId = 35;
	const raw = t.identifier('r0_1');
	const undef = t.identifier('r3_1');
	const overflow = tagStorageLocation(
		t.memberExpression(
			t.identifier('arguments'),
			t.numericLiteral(1),
			true,
		),
		{
			kind: 'parameter',
			owner: { functionId },
			parameter: { index: 2, form: 'overflow' },
		},
	);
	const blocks = new Map<number, {
		body: t.Statement[];
		branch?: t.Expression;
		consequentAddresses: number[];
	}>([
		[0, {
			body: [
				t.variableDeclaration('const', [
					t.variableDeclarator(raw, overflow),
				]),
				t.variableDeclaration('const', [
					t.variableDeclarator(undef, t.identifier('undefined')),
				]),
			],
			branch: t.unaryExpression(
				'!',
				t.binaryExpression('===', t.cloneNode(raw), t.cloneNode(undef)),
			),
			consequentAddresses: [9, 32],
		}],
		[9, {
			body: [
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_2'),
					intrinsic('GetParentEnvironment', [t.numericLiteral(0)]),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r2_1'),
					t.memberExpression(
						intrinsic('expectEnvironment', [t.identifier('r0_2')]),
						t.numericLiteral(7),
						true,
					),
				)]),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r1_1'),
					t.newExpression(t.identifier('Array'), [
						t.numericLiteral(2),
					]),
				)]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.memberExpression(
						t.identifier('r1_1'),
						t.numericLiteral(0),
						true,
					),
					t.identifier('r2_1'),
				)),
				t.variableDeclaration('const', [t.variableDeclarator(
					t.identifier('r0_3'),
					t.memberExpression(
						intrinsic('expectEnvironment', [t.identifier('r0_2')]),
						t.numericLiteral(8),
						true,
					),
				)]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.memberExpression(
						t.identifier('r1_1'),
						t.numericLiteral(1),
						true,
					),
					t.identifier('r0_3'),
				)),
			],
			consequentAddresses: [32],
		}],
		[32, {
			body: [t.returnStatement(t.numericLiteral(1))],
			consequentAddresses: [],
		}],
	]);
	const predecessors = (target: number) =>
		new Set(
			[...blocks].flatMap(([address, block]) =>
				block.consequentAddresses.includes(target) ? [address] : []
			),
		);
	const func = {
		id: functionId,
		paramCount: 1,
		entryAddress: 0,
		blocks,
		parameterPlan: createParameterPlan(functionId, []),
		cfgPredecessorsOf: predecessors,
		exceptions: {
			activeHandlersAtBlock: () => new Set(),
			activeHandlersEqual: () => true,
		},
		ssa: { basicBlocks: new Map() },
		markMergedBlocks(_parent: number, child: number) {
			blocks.delete(child);
		},
		rebuildPredecessorMap() {},
	} as unknown as IRFunction;

	assert.equal(reduceSideEffectOnlyOverflowDefault(func), true);
	const signature = generate(t.functionExpression(
		null,
		materializeParameterPlan(func.parameterPlan) as t.FunctionParameter[],
		t.blockStatement([]),
	)).code;
	assert.match(
		signature,
		/_param_35_0_ = undefined, _param_35_1_ = \[/,
	);
	assert.equal(blocks.has(9), false);
	assert.deepEqual(blocks.get(0)?.consequentAddresses, [32]);
	assert.equal(
		func.parameterPlan.telemetry.sideEffectOnlyDefaultsRecovered,
		1,
	);
});
