import * as assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import * as t from '@babel/types';
import { tagStorageLocation } from './alias.ts';
import { placeEnvironmentSlotsInTree } from './environmentPlacement.ts';

const site = {
	functionId: 3,
	kind: 'CreateFunctionEnvironment' as const,
	address: 12,
};
const slot = {
	kind: 'environment-slot' as const,
	environment: site,
	slot: 0,
};
const slotId = () => tagStorageLocation(t.identifier('_env_3_0'), slot);

describe('placeEnvironmentSlotsInTree', () => {
	it('keeps a captured slot in its creating function', () => {
		const child = t.functionExpression(
			null,
			[],
			t.blockStatement([t.returnStatement(slotId())]),
		);
		child.extra = { parentFunctionId: 4 };
		const owner = t.functionExpression(
			null,
			[],
			t.blockStatement([
				t.variableDeclaration('var', [
					t.variableDeclarator(t.identifier('_env_3_0')),
				]),
				t.ifStatement(
					t.identifier('condition'),
					t.blockStatement([t.expressionStatement(
						t.assignmentExpression(
							'=',
							slotId(),
							t.numericLiteral(1),
						),
					)]),
				),
				t.variableDeclaration('const', [
					t.variableDeclarator(t.identifier('closure'), child),
				]),
			]),
		);
		owner.extra = { parentFunctionId: 3 };
		const program = t.program([t.expressionStatement(owner)]);

		const result = placeEnvironmentSlotsInTree(program);
		assert.equal(result.analysed, 1);
		assert.equal(result.localized, 1);
		assert.equal(result.captured, 1);
		assert.equal(result.declarationsTagged, 1);
		assert.equal(result.unresolved, 0);
	});

	it('inserts a missing declaration at the creation owner', () => {
		const owner = t.functionExpression(
			null,
			[],
			t.blockStatement([t.expressionStatement(
				t.assignmentExpression('=', slotId(), t.numericLiteral(1)),
			)]),
		);
		owner.extra = { parentFunctionId: 3 };
		const program = t.program([t.expressionStatement(owner)]);

		const result = placeEnvironmentSlotsInTree(program);
		assert.equal(result.placed, 1);
		assert.equal(result.unresolved, 0);
		assert.ok(t.isVariableDeclaration(owner.body.body[0]));
		assert.equal(
			t.isVariableDeclaration(owner.body.body[0]) &&
				t.isIdentifier(owner.body.body[0].declarations[0].id) &&
				owner.body.body[0].declarations[0].id.name,
			'_env_3_0',
		);
	});

	it('does not invent a declaration for a read-only unresolved slot', () => {
		const owner = t.functionExpression(
			null,
			[],
			t.blockStatement([t.returnStatement(slotId())]),
		);
		owner.extra = { parentFunctionId: 3 };
		const program = t.program([t.expressionStatement(owner)]);

		const result = placeEnvironmentSlotsInTree(program);
		assert.equal(result.unresolved, 1);
		assert.equal(owner.body.body.length, 1);
	});

	it('moves a declaration out of a conditional to its creation owner', () => {
		const conditional = t.ifStatement(
			t.identifier('condition'),
			t.blockStatement([
				t.variableDeclaration('var', [
					t.variableDeclarator(t.identifier('_env_3_0')),
				]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					slotId(),
					t.numericLiteral(1),
				)),
			]),
		);
		const owner = t.functionExpression(
			null,
			[],
			t.blockStatement([conditional]),
		);
		owner.extra = { parentFunctionId: 3 };
		const program = t.program([t.expressionStatement(owner)]);

		const result = placeEnvironmentSlotsInTree(program);
		assert.equal(result.placed, 1);
		assert.equal(result.declarationsTagged, 1);
		assert.ok(t.isVariableDeclaration(owner.body.body[0]));
		assert.ok(t.isIfStatement(owner.body.body[1]));
		assert.equal(
			t.isBlockStatement(conditional.consequent) &&
				conditional.consequent.body.some(t.isVariableDeclaration),
			false,
		);
	});
});
