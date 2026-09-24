import * as assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import * as t from '@babel/types';
import traverse from '@babel/traverse';
import {
	coalesceParameterAliases,
	coalesceStableStorageAliases,
	destructureGeneratedObjectPropertyAliases,
	isGeneratedLocalName,
	isIncomingValueExpression,
	isParameterExpression,
	locationKey,
	locationOf,
	locationsMayAlias,
	sameLocation,
	type StorageLocation,
	tagStorageLocation,
	writesLocationWithin,
} from './alias.ts';
import { inlineObjectConstruction } from './expression.ts';

function namedParameter(functionId: number, index: number) {
	return tagStorageLocation(
		t.identifier(`_param_${functionId}_${index - 1}_`),
		{
			kind: 'parameter',
			owner: { functionId },
			parameter: { index, form: 'named' },
		},
	);
}

function overflowParameter(functionId: number, index: number) {
	return tagStorageLocation(
		t.memberExpression(
			tagStorageLocation(t.identifier('arguments'), {
				kind: 'arguments-object',
				owner: { functionId },
			}),
			t.numericLiteral(index - 1),
			true,
		),
		{
			kind: 'parameter',
			owner: { functionId },
			parameter: { index, form: 'overflow' },
		},
	);
}

describe('storage locations', () => {
	it('reads parameter 0 as this rather than a name', () => {
		const thisParam = tagStorageLocation(t.thisExpression(), {
			kind: 'parameter',
			owner: { functionId: 3 },
			parameter: { index: 0, form: 'this' },
		});
		const location = locationOf(thisParam);
		assert.equal(location?.kind, 'parameter');
		assert.equal(
			location?.kind === 'parameter' && location.parameter.form,
			'this',
		);
		assert.ok(isParameterExpression(thisParam));
	});

	it('reads an overflow parameter through arguments', () => {
		const location = locationOf(overflowParameter(3, 2));
		assert.equal(location?.kind, 'parameter');
		assert.equal(
			location?.kind === 'parameter' && location.parameter.form,
			'overflow',
		);
	});

	it('unshifts the _param_ name so tagged and untagged agree', () => {
		// `getParam` spells parameter 2 as `_param_3_1_`; both spellings must
		// answer with the same unshifted index, or a tagged tree and an
		// untagged one would disagree about which parameter this is.
		const tagged = locationOf(namedParameter(3, 2));
		const untagged = locationOf(t.identifier('_param_3_1_'));
		assert.ok(sameLocation(tagged, untagged));
		assert.equal(
			untagged?.kind === 'parameter' && untagged.parameter.index,
			2,
		);
	});

	it('leaves an untagged this or arguments unknown', () => {
		assert.equal(locationOf(t.thisExpression()), null);
		assert.equal(locationOf(t.identifier('arguments')), null);
		// ...but they are still recognisable as incoming values by form.
		assert.ok(isIncomingValueExpression(t.thisExpression()));
		assert.ok(isIncomingValueExpression(t.identifier('arguments')));
	});

	it('keeps one name in two functions apart', () => {
		assert.equal(
			sameLocation(
				locationOf(t.identifier('_param_3_0_')),
				locationOf(t.identifier('_param_4_0_')),
			),
			false,
		);
	});

	it('aliases arguments with its own overflow parameters only', () => {
		const args: StorageLocation = {
			kind: 'arguments-object',
			owner: { functionId: 3 },
		};
		assert.ok(locationsMayAlias(args, locationOf(overflowParameter(3, 2))));
		assert.equal(
			locationsMayAlias(args, locationOf(overflowParameter(4, 2))),
			false,
		);
		// A named parameter is not reached through `arguments`.
		assert.equal(
			locationsMayAlias(args, locationOf(namedParameter(3, 1))),
			false,
		);
	});

	it('gives distinct keys to distinct locations', () => {
		const keys = new Set([
			locationKey(locationOf(namedParameter(3, 1))!),
			locationKey(locationOf(namedParameter(3, 2))!),
			locationKey(locationOf(overflowParameter(3, 2))!),
			locationKey({ kind: 'arguments-object', owner: { functionId: 3 } }),
		]);
		assert.equal(keys.size, 4);
	});

	it('keys environment slots by creation site rather than spelling', () => {
		const first: StorageLocation = {
			kind: 'environment-slot',
			environment: {
				functionId: 3,
				kind: 'CreateFunctionEnvironment',
				address: 10,
			},
			slot: 0,
		};
		const second: StorageLocation = {
			kind: 'environment-slot',
			environment: {
				functionId: 3,
				kind: 'CreateFunctionEnvironment',
				address: 20,
			},
			slot: 0,
		};
		assert.equal(sameLocation(first, second), false);
		assert.notEqual(locationKey(first), locationKey(second));
		const handle: StorageLocation = {
			kind: 'environment-handle',
			environment: first.environment,
		};
		assert.notEqual(locationKey(handle), locationKey(first));
	});

	it('derives register identity from compact lift provenance', () => {
		const identifier = t.identifier('r5_2');
		identifier.extra = {
			sourceRegister: { type: 'register', index: 5, version: 2 },
			bindingOwnerFunctionId: 7,
		};
		const location = locationOf(identifier);
		assert.equal(location?.kind, 'register');
		assert.equal(
			location?.kind === 'register' && location.owner.functionId,
			7,
		);
	});

	it('survives cloneNode', () => {
		const clone = t.cloneNode(namedParameter(3, 1), true);
		assert.ok(sameLocation(
			locationOf(clone),
			locationOf(namedParameter(3, 1)),
		));
	});

	it('round-trips through a JSON encode', () => {
		// The cold store encodes records with msgpackr, which carries plain
		// data and drops prototypes; a location must be plain data to survive.
		const location = locationOf(namedParameter(3, 1))!;
		const decoded = JSON.parse(JSON.stringify(location)) as StorageLocation;
		assert.ok(sameLocation(location, decoded));
	});
});

describe('writesLocationWithin', () => {
	const location = locationOf(namedParameter(3, 1))!;

	it('sees an assignment and an update', () => {
		assert.ok(writesLocationWithin(
			t.expressionStatement(t.assignmentExpression(
				'=',
				namedParameter(3, 1),
				t.numericLiteral(1),
			)),
			location,
		));
		assert.ok(writesLocationWithin(
			t.expressionStatement(
				t.updateExpression('++', namedParameter(3, 1)),
			),
			location,
		));
	});

	it('ignores a read and another parameter', () => {
		assert.equal(
			writesLocationWithin(
				t.expressionStatement(namedParameter(3, 1)),
				location,
			),
			false,
		);
		assert.equal(
			writesLocationWithin(
				t.expressionStatement(t.assignmentExpression(
					'=',
					namedParameter(3, 2),
					t.numericLiteral(1),
				)),
				location,
			),
			false,
		);
	});

	it('sees a write to arguments against an overflow parameter', () => {
		const overflow = locationOf(overflowParameter(3, 2))!;
		assert.ok(writesLocationWithin(
			t.expressionStatement(t.assignmentExpression(
				'=',
				overflowParameter(3, 2),
				t.numericLiteral(1),
			)),
			overflow,
		));
	});
});

describe('isGeneratedLocalName', () => {
	it('covers every generated spelling', () => {
		assert.ok(isGeneratedLocalName('r5_1'));
		assert.ok(isGeneratedLocalName('_env_0_3'));
		assert.ok(isGeneratedLocalName('_env_0_x1_3'));
		// The materialized lowered-generator slot form.
		assert.ok(isGeneratedLocalName('r26_r7_11_0'));
		assert.equal(isGeneratedLocalName('value'), false);
		assert.equal(isGeneratedLocalName('_param_3_0_'), false);
	});
});

describe('coalesceParameterAliases', () => {
	const aliasDeclaration = (
		local: string,
		functionId: number,
		index: number,
	) => t.variableDeclaration('let', [
		t.variableDeclarator(
			t.identifier(local),
			namedParameter(functionId, index),
		),
	]);

	it('folds a sole-reference parameter into its local', () => {
		const body: t.Statement[] = [
			aliasDeclaration('r26_r7_11_0', 3, 1),
			t.expressionStatement(t.identifier('r26_r7_11_0')),
			t.expressionStatement(
				t.updateExpression('++', t.identifier('r26_r7_11_0')),
			),
		];
		const coalesced = coalesceParameterAliases(body, [...body]);

		assert.deepEqual(coalesced, ['r26_r7_11_0']);
		assert.equal(body.length, 2);
		assert.equal(
			((body[0] as t.ExpressionStatement).expression as t.Identifier)
				.name,
			'_param_3_0_',
		);
		// The rewritten uses carry the location, not just the spelling.
		assert.ok(isParameterExpression(
			(body[0] as t.ExpressionStatement).expression,
		));
	});

	it('declines when the parameter is read elsewhere', () => {
		// A second read would observe writes made through the local.
		const body: t.Statement[] = [
			aliasDeclaration('r26_r7_11_0', 3, 1),
			t.expressionStatement(
				t.updateExpression('++', t.identifier('r26_r7_11_0')),
			),
			t.expressionStatement(namedParameter(3, 1)),
		];
		assert.deepEqual(coalesceParameterAliases(body, [...body]), []);
		assert.equal(body.length, 3);
	});

	it('declines a second local for one parameter', () => {
		const body: t.Statement[] = [
			aliasDeclaration('r26_r7_11_0', 3, 1),
			aliasDeclaration('r26_r7_11_1', 3, 1),
		];
		// Two references to the parameter, so neither is folded.
		assert.deepEqual(coalesceParameterAliases(body, [...body]), []);
	});

	it('declines when a nested function shadows either name', () => {
		const body: t.Statement[] = [
			aliasDeclaration('r26_r7_11_0', 3, 1),
			t.expressionStatement(t.functionExpression(
				null,
				[t.identifier('r26_r7_11_0')],
				t.blockStatement([
					t.expressionStatement(t.identifier('r26_r7_11_0')),
				]),
			)),
		];
		assert.deepEqual(coalesceParameterAliases(body, [...body]), []);
	});

	it('declines this and arguments', () => {
		// A nested non-arrow function rebinds both, so folding one across a
		// function boundary would change what it denotes.
		const thisAlias = t.variableDeclaration('let', [
			t.variableDeclarator(
				t.identifier('r26_r7_11_0'),
				tagStorageLocation(t.thisExpression(), {
					kind: 'parameter',
					owner: { functionId: 3 },
					parameter: { index: 0, form: 'this' },
				}),
			),
		]);
		const body: t.Statement[] = [thisAlias];
		assert.deepEqual(coalesceParameterAliases(body, [...body]), []);
		assert.equal(body.length, 1);
	});

	it('leaves a same-named property key alone', () => {
		// `obj.r26_r7_11_0` shares a spelling with the local and nothing else.
		// Obfuscated bundles do use short generated-looking property names.
		const property = t.memberExpression(
			t.identifier('obj'),
			t.identifier('r26_r7_11_0'),
		);
		const body: t.Statement[] = [
			aliasDeclaration('r26_r7_11_0', 3, 1),
			t.expressionStatement(property),
		];
		assert.deepEqual(
			coalesceParameterAliases(body, [...body]),
			['r26_r7_11_0'],
		);
		assert.equal((property.property as t.Identifier).name, 'r26_r7_11_0');
	});

	it('does not count a property key as a parameter reference', () => {
		// A property literally spelled `_param_3_0_` must not make the pass
		// think the parameter is read a second time.
		const body: t.Statement[] = [
			aliasDeclaration('r26_r7_11_0', 3, 1),
			t.expressionStatement(t.memberExpression(
				t.identifier('obj'),
				t.identifier('_param_3_0_'),
			)),
		];
		assert.deepEqual(
			coalesceParameterAliases(body, [...body]),
			['r26_r7_11_0'],
		);
	});

	it('leaves a non-generated local alone', () => {
		const body: t.Statement[] = [
			t.variableDeclaration('let', [
				t.variableDeclarator(
					t.identifier('total'),
					namedParameter(3, 1),
				),
			]),
		];
		assert.deepEqual(coalesceParameterAliases(body, [...body]), []);
	});

	it('is idempotent', () => {
		const body: t.Statement[] = [
			aliasDeclaration('r26_r7_11_0', 3, 1),
			t.expressionStatement(t.identifier('r26_r7_11_0')),
		];
		coalesceParameterAliases(body, [...body]);
		assert.deepEqual(coalesceParameterAliases(body, [...body]), []);
		assert.equal(body.length, 1);
	});
});
describe('destructureGeneratedObjectPropertyAliases', () => {
	it('folds generated member aliases and bare reads', () => {
		const file = t.file(t.program([
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r3_8'),
					t.callExpression(t.identifier('load'), []),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('_env_3_0'),
					t.memberExpression(
						t.identifier('r3_8'),
						t.identifier('StyleSheet'),
					),
				),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('_env_3_1'),
					t.memberExpression(
						t.identifier('r3_8'),
						t.identifier('View'),
					),
				),
			]),
			t.expressionStatement(t.memberExpression(
				t.identifier('r3_8'),
				t.identifier('Platform'),
			)),
		]));

		assert.equal(destructureGeneratedObjectPropertyAliases(file), 1);
		assert.equal(file.program.body.length, 1);
		const declaration = file.program.body[0];
		assert.ok(t.isVariableDeclaration(declaration));
		const pattern = declaration.declarations[0].id;
		assert.ok(t.isObjectPattern(pattern));
		assert.equal(pattern.properties.length, 3);
		const unusedProperty = pattern.properties[2];
		assert.ok(t.isObjectProperty(unusedProperty));
		assert.ok(t.isIdentifier(unusedProperty.value));
		assert.equal(unusedProperty.value.name, 'r3_8');
	});

	it('does not fold multiple bare reads into one binding', () => {
		const file = t.file(t.program([
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier('r0_1'),
					t.memberExpression(
						t.identifier('_param_1_0_'),
						t.identifier('nativeEvent'),
					),
				),
			]),
			t.expressionStatement(t.memberExpression(
				t.identifier('r0_1'),
				t.identifier('clientX'),
			)),
			t.expressionStatement(t.memberExpression(
				t.identifier('r0_1'),
				t.identifier('clientY'),
			)),
		]));

		assert.equal(destructureGeneratedObjectPropertyAliases(file), 0);
		traverse(file, {});
	});
});

describe('coalesceStableStorageAliases', () => {
	const environment = {
		functionId: 3,
		kind: 'CreateFunctionEnvironment' as const,
		address: 10,
	};
	const location = {
		kind: 'environment-slot' as const,
		environment,
		slot: 0,
	};
	const source = () => tagStorageLocation(t.identifier('_env_3_0'), location);
	const secondSource = () =>
		tagStorageLocation(t.identifier('_env_3_1'), {
			...location,
			slot: 1,
		});
	const parameter = () => namedParameter(3, 1);
	const projectedParameterBinding = () =>
		tagStorageLocation(t.identifier('r1_1'), {
			kind: 'register',
			owner: { functionId: 3 },
			register: { type: 'register', index: 1, version: 1 },
		});

	it('removes a nested generated alias of a stable slot', () => {
		const child = t.functionExpression(
			null,
			[],
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(t.identifier('r7_1'), source()),
				]),
				t.returnStatement(t.identifier('r7_1')),
			]),
		);
		const file = t.file(t.program([
			t.variableDeclaration('const', [
				t.variableDeclarator(source(), t.numericLiteral(1)),
			]),
			t.expressionStatement(child),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.analysed, 1);
		assert.equal(result.coalesced, 1);
		assert.equal(child.body.body.length, 1);
		const returned = child.body.body[0];
		assert.ok(t.isReturnStatement(returned));
		assert.ok(t.isIdentifier(returned.argument, { name: '_env_3_0' }));
	});

	it('removes generated aliases of free external environment slots', () => {
		const child = t.functionExpression(
			null,
			[],
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r7_1'),
						t.identifier('_env_3_0'),
					),
				]),
				t.returnStatement(t.identifier('r7_1')),
			]),
		);
		const file = t.file(t.program([t.expressionStatement(child)]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.analysed, 1);
		assert.equal(result.coalesced, 1);
		assert.equal(result.registerAliasesCoalesced, 1);
		assert.equal(child.body.body.length, 1);
		const returned = child.body.body[0];
		assert.ok(t.isReturnStatement(returned));
		assert.ok(t.isIdentifier(returned.argument, { name: '_env_3_0' }));
	});

	it('coalesces generated aliases of object rest parameters', () => {
		const rest = t.identifier('_rest_3_0_');
		const file = t.file(t.program([
			t.functionDeclaration(
				t.identifier('outer'),
				[t.objectPattern([t.restElement(rest)])],
				t.blockStatement([
					t.variableDeclaration('const', [
						t.variableDeclarator(
							t.identifier('r0_2'),
							t.identifier('_rest_3_0_'),
						),
					]),
					t.returnStatement(t.memberExpression(
						t.identifier('r0_2'),
						t.identifier('backgroundComponent'),
					)),
				]),
			),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 1);
		const outer = file.program.body[0];
		assert.ok(t.isFunctionDeclaration(outer));
		const returned = outer.body.body[0];
		assert.ok(t.isReturnStatement(returned));
		assert.ok(t.isMemberExpression(returned.argument));
		assert.ok(t.isIdentifier(returned.argument.object, {
			name: '_rest_3_0_',
		}));
	});

	it('coalesces a factory slot into the closures it installs', () => {
		// The Discord module-factory shape (f#107683): slots initialised from
		// factory parameters, then read through register aliases inside the
		// closures the factory installs. The initialising write is the only
		// write, and it precedes every closure, so the aliases are removable.
		const child = t.functionExpression(
			null,
			[],
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(t.identifier('r4_1'), source()),
				]),
				t.expressionStatement(
					t.callExpression(t.identifier('r4_1'), []),
				),
			]),
		);
		const file = t.file(t.program([
			t.functionDeclaration(
				t.identifier('factory'),
				[parameter()],
				t.blockStatement([
					t.variableDeclaration('var', [
						t.variableDeclarator(source()),
					]),
					t.expressionStatement(
						t.assignmentExpression('=', source(), parameter()),
					),
					t.expressionStatement(child),
				]),
			),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 1);
		assert.equal(result.registerAliasesCoalesced, 1);
		assert.equal(result.blockedByWrite, 0);
		assert.equal(child.body.body.length, 1);
	});

	it('keeps an alias read by a closure created before the write', () => {
		// The one write no longer dominates the read, so the closure could run
		// while the slot still holds `undefined`.
		const child = t.functionExpression(
			null,
			[],
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(t.identifier('r4_1'), source()),
				]),
				t.returnStatement(t.identifier('r4_1')),
			]),
		);
		const file = t.file(t.program([
			t.functionDeclaration(
				t.identifier('factory'),
				[parameter()],
				t.blockStatement([
					t.variableDeclaration('var', [
						t.variableDeclarator(source()),
					]),
					t.expressionStatement(child),
					t.expressionStatement(
						t.assignmentExpression('=', source(), parameter()),
					),
				]),
			),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 0);
		assert.equal(result.blockedByWrite, 1);
	});

	it('keeps a snapshot alias when the source slot is written', () => {
		const file = t.file(t.program([
			t.variableDeclaration('let', [
				t.variableDeclarator(source(), t.numericLiteral(1)),
			]),
			t.variableDeclaration('const', [
				t.variableDeclarator(t.identifier('r7_1'), source()),
			]),
			t.expressionStatement(t.assignmentExpression(
				'=',
				source(),
				t.numericLiteral(2),
			)),
			t.expressionStatement(t.identifier('r7_1')),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 0);
		assert.equal(result.blockedByWrite, 1);
	});

	it('coalesces an immutable environment slot into its parameter', () => {
		const file = t.file(t.program([
			t.functionDeclaration(
				t.identifier('outer'),
				[parameter()],
				t.blockStatement([
					t.variableDeclaration('const', [
						t.variableDeclarator(source(), parameter()),
					]),
					t.returnStatement(source()),
				]),
			),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 1);
		assert.equal(result.environmentSlotAliasesCoalesced, 1);
		const outer = file.program.body[0];
		assert.ok(t.isFunctionDeclaration(outer));
		assert.equal(outer.body.body.length, 1);
		const returned = outer.body.body[0];
		assert.ok(t.isReturnStatement(returned));
		assert.ok(t.isIdentifier(returned.argument, {
			name: '_param_3_0_',
		}));
	});

	it('coalesces a captured destructured parameter binding', () => {
		const child = t.arrowFunctionExpression(
			[],
			t.callExpression(source(), []),
		);
		const file = t.file(t.program([
			t.functionDeclaration(
				t.identifier('outer'),
				[t.objectPattern([t.objectProperty(
					t.identifier('onAccept'),
					projectedParameterBinding(),
				)])],
				t.blockStatement([
					t.variableDeclaration('const', [
						t.variableDeclarator(
							source(),
							projectedParameterBinding(),
						),
					]),
					t.returnStatement(child),
				]),
			),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 1);
		assert.equal(result.environmentSlotAliasesCoalesced, 1);
		const outer = file.program.body[0];
		assert.ok(t.isFunctionDeclaration(outer));
		assert.equal(outer.body.body.length, 1);
		const pattern = outer.params[0];
		assert.ok(t.isObjectPattern(pattern));
		const property = pattern.properties[0];
		assert.ok(t.isObjectProperty(property));
		assert.ok(t.isIdentifier(property.value, { name: '_env_3_0' }));
		assert.ok(t.isCallExpression(child.body));
		assert.ok(t.isIdentifier(child.body.callee, { name: '_env_3_0' }));
	});

	it('promotes an ordinary register definition into its environment sink', () => {
		const child = t.arrowFunctionExpression(
			[],
			t.callExpression(source(), []),
		);
		const file = t.file(t.program([
			t.functionDeclaration(
				t.identifier('outer'),
				[],
				t.blockStatement([
					t.variableDeclaration('const', [
						t.variableDeclarator(
							projectedParameterBinding(),
							t.callExpression(t.identifier('value'), []),
						),
					]),
					t.variableDeclaration('const', [
						t.variableDeclarator(
							source(),
							projectedParameterBinding(),
						),
					]),
					t.expressionStatement(projectedParameterBinding()),
					t.returnStatement(child),
				]),
			),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 1);
		assert.equal(result.environmentSlotAliasesCoalesced, 1);
		const outer = file.program.body[0];
		assert.ok(t.isFunctionDeclaration(outer));
		assert.equal(outer.body.body.length, 3);
		const declaration = outer.body.body[0];
		assert.ok(t.isVariableDeclaration(declaration));
		assert.ok(t.isIdentifier(declaration.declarations[0].id, {
			name: '_env_3_0',
		}));
		const expression = outer.body.body[1];
		assert.ok(t.isExpressionStatement(expression));
		assert.ok(t.isIdentifier(expression.expression, { name: '_env_3_0' }));
		assert.ok(t.isCallExpression(child.body));
		assert.ok(t.isIdentifier(child.body.callee, { name: '_env_3_0' }));
	});

	it('keeps a register copied into multiple captured slots', () => {
		const child = t.arrowFunctionExpression(
			[],
			t.callExpression(secondSource(), []),
		);
		const file = t.file(t.program([
			t.functionDeclaration(
				t.identifier('outer'),
				[],
				t.blockStatement([
					t.variableDeclaration('const', [
						t.variableDeclarator(
							projectedParameterBinding(),
							t.callExpression(t.identifier('value'), []),
						),
					]),
					t.variableDeclaration('const', [
						t.variableDeclarator(
							source(),
							projectedParameterBinding(),
						),
					]),
					t.variableDeclaration('const', [
						t.variableDeclarator(
							secondSource(),
							projectedParameterBinding(),
						),
					]),
					t.returnStatement(child),
				]),
			),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 0);
		const outer = file.program.body[0];
		assert.ok(t.isFunctionDeclaration(outer));
		assert.equal(outer.body.body.length, 4);
		assert.ok(t.isCallExpression(child.body));
		assert.ok(t.isIdentifier(child.body.callee, { name: '_env_3_1' }));
	});

	it('promotes a chained register store into its environment binding', () => {
		const child = t.arrowFunctionExpression(
			[],
			t.callExpression(source(), []),
		);
		const file = t.file(t.program([
			t.functionDeclaration(
				t.identifier('outer'),
				[],
				t.blockStatement([
					t.variableDeclaration('var', [
						t.variableDeclarator(source()),
					]),
					t.variableDeclaration('const', [
						t.variableDeclarator(
							projectedParameterBinding(),
							t.assignmentExpression(
								'=',
								source(),
								t.callExpression(t.identifier('value'), []),
							),
						),
					]),
					t.returnStatement(t.arrayExpression([
						t.identifier('r1_1'),
						child,
					])),
				]),
			),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 1);
		assert.equal(result.environmentSlotAliasesCoalesced, 1);
		const outer = file.program.body[0];
		assert.ok(t.isFunctionDeclaration(outer));
		assert.equal(outer.body.body.length, 2);
		const declaration = outer.body.body[0];
		assert.ok(t.isVariableDeclaration(declaration, { kind: 'var' }));
		const [declarator] = declaration.declarations;
		assert.ok(t.isIdentifier(declarator.id, { name: '_env_3_0' }));
		assert.ok(t.isCallExpression(declarator.init));
		const returned = outer.body.body[1];
		assert.ok(t.isReturnStatement(returned));
		assert.ok(t.isArrayExpression(returned.argument));
		assert.ok(t.isIdentifier(returned.argument.elements[0], {
			name: '_env_3_0',
		}));
		assert.ok(t.isCallExpression(child.body));
		assert.ok(t.isIdentifier(child.body.callee, { name: '_env_3_0' }));
	});

	it('coalesces a register through an immutable slot to its parameter', () => {
		const file = t.file(t.program([
			t.functionDeclaration(
				t.identifier('outer'),
				[parameter()],
				t.blockStatement([
					t.variableDeclaration('const', [
						t.variableDeclarator(source(), parameter()),
					]),
					t.variableDeclaration('const', [
						t.variableDeclarator(t.identifier('r7_1'), source()),
					]),
					t.returnStatement(t.identifier('r7_1')),
				]),
			),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 2);
		assert.equal(result.registerAliasesCoalesced, 1);
		assert.equal(result.environmentSlotAliasesCoalesced, 1);
		const outer = file.program.body[0];
		assert.ok(t.isFunctionDeclaration(outer));
		assert.equal(outer.body.body.length, 1);
		const returned = outer.body.body[0];
		assert.ok(t.isReturnStatement(returned));
		assert.ok(t.isIdentifier(returned.argument, {
			name: '_param_3_0_',
		}));
	});

	it('keeps an alias whose final source is shadowed at a reference', () => {
		const shadow = namedParameter(4, 1);
		// Deliberately use the same textual parameter name in the nested function.
		shadow.name = '_param_3_0_';
		const child = t.functionExpression(
			null,
			[shadow],
			t.blockStatement([t.returnStatement(t.identifier('r7_1'))]),
		);
		const file = t.file(t.program([
			t.functionDeclaration(
				t.identifier('outer'),
				[parameter()],
				t.blockStatement([
					t.variableDeclaration('const', [
						t.variableDeclarator(t.identifier('r7_1'), parameter()),
					]),
					t.returnStatement(child),
				]),
			),
		]));

		const result = coalesceStableStorageAliases(file);
		assert.equal(result.coalesced, 0);
		assert.equal(result.blockedByVisibility, 1);
		const returned = child.body.body[0];
		assert.ok(t.isReturnStatement(returned));
		assert.ok(t.isIdentifier(returned.argument, { name: 'r7_1' }));
	});

	it('exposes a captured object buffer for a single-return fold', () => {
		const child = t.functionExpression(
			null,
			[],
			t.blockStatement([
				t.variableDeclaration('const', [
					t.variableDeclarator(t.identifier('r7_1'), source()),
				]),
				t.variableDeclaration('const', [
					t.variableDeclarator(
						t.identifier('r0_1'),
						t.objectExpression([]),
					),
				]),
				t.expressionStatement(t.assignmentExpression(
					'=',
					t.memberExpression(
						t.identifier('r0_1'),
						t.identifier('children'),
					),
					t.arrayExpression([t.identifier('r7_1')]),
				)),
				t.returnStatement(t.identifier('r0_1')),
			]),
		);
		const file = t.file(t.program([
			t.variableDeclaration('const', [
				t.variableDeclarator(source(), t.identifier('jsx')),
			]),
			t.expressionStatement(child),
		]));

		assert.equal(coalesceStableStorageAliases(file).coalesced, 1);
		let folds = 0;
		traverse(file, {
			VariableDeclaration: {
				exit(path) {
					if (inlineObjectConstruction(path)) folds++;
				},
			},
		});
		traverse.cache.clear();

		assert.equal(folds, 1);
		assert.equal(child.body.body.length, 1);
		const returned = child.body.body[0];
		assert.ok(t.isReturnStatement(returned));
		assert.ok(t.isObjectExpression(returned.argument));
		const property = returned.argument.properties[0];
		assert.ok(t.isObjectProperty(property));
		assert.ok(t.isArrayExpression(property.value));
		assert.ok(t.isIdentifier(property.value.elements[0], {
			name: '_env_3_0',
		}));
	});
});
