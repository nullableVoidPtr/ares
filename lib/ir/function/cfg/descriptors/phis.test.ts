import { strict as assert } from 'node:assert';
import * as t from '@babel/types';
import type { IRBlock } from '../../../ast/mod.ts';
import type { IRFunction } from '../../mod.ts';
import type { SSAInstruction, SSARegister } from '../../../../ssa.ts';
import { AddressGraph } from '../../../../utils/graph.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import { ImmutableCFG } from '../immutableCFG.ts';
import { recoverPhiDescriptors } from './phis.ts';

function register(index: number, version: number): SSARegister {
	return { type: 'register', index, version };
}

function phi(
	destination: SSARegister,
	sources: Array<[number, SSARegister]>,
): SSAInstruction {
	return {
		instruction: 'Phi',
		destination,
		sources: new AddressMap(sources),
	} as unknown as SSAInstruction;
}

function mov(
	destination: SSARegister,
	source: SSARegister,
): SSAInstruction {
	return {
		instruction: 'Mov',
		defs: { destination },
		uses: { source },
	} as unknown as SSAInstruction;
}

function loadUndefined(destination: SSARegister): SSAInstruction {
	return {
		instruction: 'LoadConst',
		destination,
		value: undefined,
		defs: { destination },
		uses: {},
	} as unknown as SSAInstruction;
}

function phiFixture(
	target: SSARegister,
	source: SSARegister,
	instructions: SSAInstruction[],
) {
	const targetName = `r${target.index}_${target.version}`;
	const sourceName = `r${source.index}_${source.version}`;
	const blocks = new AddressMap<IRBlock>([
		[0, {
			address: 0,
			body: [],
			consequentAddresses: [1],
			kind: 'normal',
		}],
		[1, {
			address: 1,
			body: [t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier(targetName),
					t.callExpression(t.v8IntrinsicIdentifier('Phi'), [
						t.identifier(sourceName),
					]),
				),
			])],
			consequentAddresses: [],
			kind: 'normal',
		}],
	]);
	const mergedBlocks = new AddressGraph<number, number>([
		[0, new AddressSet([0])],
		[1, new AddressSet([1])],
	]);
	const func = {
		id: 1,
		blocks,
		entryAddress: 0,
		mergedBlocks,
		ssa: {
			basicBlocks: new AddressMap([
				[0, { ssaInstructions: [] }],
				[1, { ssaInstructions: instructions }],
			]),
		},
		exceptions: { records: new AddressMap() },
	} as unknown as IRFunction;
	return recoverPhiDescriptors(ImmutableCFG.fromIRFunction(func)).phis[0];
}

Deno.test('Phi source recovery leaves loop-carried SCCs unresolved', () => {
	const target = register(0, 1);
	const loopValue = register(1, 1);
	const alias = register(2, 1);
	const descriptor = phiFixture(target, alias, [
		phi(target, [[0, alias]]),
		phi(loopValue, [[0, alias], [1, alias]]),
		mov(alias, loopValue),
	]);
	const value = descriptor.incoming.get(0)?.value;
	assert.ok(t.isIdentifier(value));
	assert.equal(value.name, 'r2_1');
});

Deno.test('undefined SSA versions become undefined Phi sources', () => {
	const target = register(0, 1);
	const source = register(1, 0);
	const descriptor = phiFixture(target, source, [
		phi(target, [[0, source]]),
	]);

	assert.ok(t.isIdentifier(descriptor.incoming.get(0)?.value, {
		name: 'undefined',
	}));
});

Deno.test('Phi source recovery condenses shared acyclic Phi DAGs', () => {
	const target = register(0, 1);
	const constant = register(9, 1);
	const instructions: SSAInstruction[] = [loadUndefined(constant)];
	let source = constant;
	// The old recursive resolver visited both copies of every child and therefore
	// expanded this small graph into 2^28 calls.
	for (let version = 1; version <= 28; version++) {
		const destination = register(1, version);
		instructions.push(phi(destination, [[0, source], [1, source]]));
		source = destination;
	}
	instructions.push(phi(target, [[0, source]]));
	const descriptor = phiFixture(target, source, instructions);
	assert.ok(t.isIdentifier(descriptor.target, { name: 'r0_1' }));
	assert.ok(t.isIdentifier(descriptor.incoming.get(0)?.value, {
		name: 'undefined',
	}));
});
