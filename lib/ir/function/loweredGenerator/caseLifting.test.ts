import { strict as assert } from 'node:assert';
import * as t from '@babel/types';
import type { BlockAddr } from '../../../hbc/disassembly/function.ts';
import type { SSARegister } from '../../../ssa.ts';
import { AddressMap } from '../../../utils/map.ts';
import type { LiftedAST } from '../../ast/mod.ts';
import type { IRFunction } from '../mod.ts';
import { bindYieldResumeValues } from './caseLifting.ts';
import type { CaseBlockInfo, CaseInfo } from './types.ts';

function registerIdentifier(register: SSARegister) {
	const identifier = t.identifier(
		`r${register.index}_${register.version}`,
	) as LiftedAST<t.Identifier>;
	identifier.extra = {
		sourceRegister: register,
		bindingOwnerFunctionId: 7537,
	};
	return identifier;
}

Deno.test('yield resume binding includes branch-only continuation uses', () => {
	const resumeRegister: SSARegister = {
		type: 'register',
		index: 0,
		version: 2,
	};
	let nextVersion = resumeRegister.version;
	const func = {
		id: 7537,
		getParam(index: number) {
			assert.equal(index, 2);
			return t.identifier('_resume');
		},
		ssa: {
			basicBlocks: new Map([
				[0, {
					ssaInstructions: [{
						instruction: 'LoadParam',
						parameterIndex: 2,
						defs: { destination: resumeRegister },
					}],
				}],
			]),
			allocateRegisterVersion(index: number): SSARegister {
				assert.equal(index, resumeRegister.index);
				return { type: 'register', index, version: ++nextVersion };
			},
		},
	} as unknown as IRFunction;

	const yieldStatement = t.expressionStatement(
		t.yieldExpression(t.identifier('source')),
	);
	const suspendingCase: CaseInfo = {
		state: 0,
		address: 10,
		path: [10],
		body: [yieldStatement],
		nextState: 1,
		activeHandlerIndex: null,
		terminal: yieldStatement,
	};
	const continuationBlock: CaseBlockInfo = {
		address: 20 as BlockAddr,
		body: [],
		branch: t.unaryExpression(
			'!',
			registerIdentifier(resumeRegister),
		),
		consequentAddresses: [21 as BlockAddr, 22 as BlockAddr],
		terminal: null,
	};
	const continuationCase: CaseInfo = {
		state: 1,
		address: continuationBlock.address,
		path: [continuationBlock.address],
		body: [],
		blocks: new AddressMap([[
			continuationBlock.address,
			continuationBlock,
		]]),
		nextState: null,
		activeHandlerIndex: null,
		terminal: t.returnStatement(t.numericLiteral(0)),
	};

	bindYieldResumeValues(
		func,
		new Map([[0, suspendingCase], [1, continuationCase]]),
		[0, 1],
	);

	const resumedYield = suspendingCase.body[0];
	assert(t.isVariableDeclaration(resumedYield));
	const declaration = resumedYield.declarations[0];
	assert(t.isIdentifier(declaration.id));
	assert.equal(declaration.id.name, 'r0_3');
	assert(t.isYieldExpression(declaration.init));

	const branch = continuationBlock.branch;
	assert(t.isUnaryExpression(branch));
	assert(t.isIdentifier(branch.argument));
	assert.equal(branch.argument.name, declaration.id.name);
});
