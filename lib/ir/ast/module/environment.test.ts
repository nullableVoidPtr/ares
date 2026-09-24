import * as assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { parse } from '@babel/parser';
import traverse, { type NodePath } from '@babel/traverse';
import * as t from '@babel/types';
import { cleanupEnvironmentBody } from './environment.ts';
import { locationOf, sameLocation, tagStorageLocation } from '../alias.ts';

function cleanup(
	source: string,
	prepare?: (program: t.Program) => void,
): t.Program {
	const file = parse(source, { sourceType: 'script' });
	prepare?.(file.program);
	traverse(file, {
		Program(path) {
			cleanupEnvironmentBody(path as NodePath<t.Program>);
			path.stop();
		},
	});
	traverse.cache.clear();
	return file.program;
}

describe('cleanupEnvironmentBody aliases', () => {
	it('coalesces a parameter whose prologue copy is its only direct use', () => {
		const program = cleanup(`
			var _env_3_0 = _param_3_0_;
			use(_env_3_0);
			_env_3_0 = next();
		`);
		assert.equal(program.body.length, 2);
		const use = program.body[0] as t.ExpressionStatement;
		const argument = (use.expression as t.CallExpression)
			.arguments[0] as t.Identifier;
		assert.equal(argument.name, '_param_3_0_');
	});

	it('declines when the parameter remains directly observable', () => {
		const program = cleanup(`
			var _env_3_0 = _param_3_0_;
			_env_3_0 = next();
			use(_param_3_0_);
		`);
		const declaration = program.body[0] as t.VariableDeclaration;
		assert.equal(
			(declaration.declarations[0].id as t.Identifier).name,
			'_env_3_0',
		);
	});

	it('carries a creation-site tag into a promoted declaration', () => {
		const file = parse(
			`
			var _env_3_0;
			_env_3_0 = value;
			use(_env_3_0);
		`,
			{ sourceType: 'script' },
		);
		const assignment = (file.program.body[1] as t.ExpressionStatement)
			.expression as t.AssignmentExpression;
		const tagged = tagStorageLocation(assignment.left as t.Identifier, {
			kind: 'environment-slot',
			environment: {
				functionId: 3,
				kind: 'CreateFunctionEnvironment',
				address: 10,
			},
			slot: 0,
		});
		traverse(file, {
			Program(path) {
				cleanupEnvironmentBody(path);
				path.stop();
			},
		});
		traverse.cache.clear();
		const declaration = file.program.body[0] as t.VariableDeclaration;
		const id = declaration.declarations[0].id as t.Identifier;
		assert.ok(sameLocation(locationOf(id), locationOf(tagged)));
	});

	it('keeps the root declaration for a conditional initialization', () => {
		const program = cleanup(`
			var _env_3_0;
			if (condition) {
				_env_3_0 = value;
			}
			const closure = function () { return _env_3_0; };
		`);
		const declaration = program.body[0];
		assert.ok(t.isVariableDeclaration(declaration));
		assert.ok(t.isIdentifier(declaration.declarations[0].id, {
			name: '_env_3_0',
		}));
		const conditional = program.body[1];
		assert.ok(t.isIfStatement(conditional));
		assert.ok(t.isBlockStatement(conditional.consequent));
		assert.ok(t.isExpressionStatement(conditional.consequent.body[0]));
	});

	it('coalesces a named function expression into the environment binding', () => {
		const program = cleanup(
			`
			var _env_3_0;
			_env_3_0 = function installed() {
				return _env_3_0 === installed;
			};
			use(_env_3_0);
		`,
			(program) => {
				const assignment = (program.body[1] as t.ExpressionStatement)
					.expression as t.AssignmentExpression;
				tagStorageLocation(assignment.left as t.Identifier, {
					kind: 'environment-slot',
					environment: {
						functionId: 3,
						kind: 'CreateFunctionEnvironment',
						address: 10,
					},
					slot: 0,
				});
			},
		);
		assert.equal(program.body.length, 2);
		const declaration = program.body[0];
		assert.ok(t.isFunctionDeclaration(declaration));
		assert.ok(t.isIdentifier(declaration.id, { name: 'installed' }));
		const returned = declaration.body.body[0];
		assert.ok(t.isReturnStatement(returned));
		assert.ok(t.isBinaryExpression(returned.argument));
		assert.ok(t.isIdentifier(returned.argument.left, {
			name: 'installed',
		}));
		assert.ok(t.isIdentifier(returned.argument.right, {
			name: 'installed',
		}));
		const use = program.body[1];
		assert.ok(t.isExpressionStatement(use));
		assert.ok(t.isCallExpression(use.expression));
		assert.ok(t.isIdentifier(use.expression.arguments[0], {
			name: 'installed',
		}));
	});

	it('preserves slot provenance on an adopted function name', () => {
		const file = parse(
			`var _env_3_0; _env_3_0 = function installed() {};`,
			{ sourceType: 'script' },
		);
		const assignment = (file.program.body[1] as t.ExpressionStatement)
			.expression as t.AssignmentExpression;
		const tagged = tagStorageLocation(assignment.left as t.Identifier, {
			kind: 'environment-slot',
			environment: {
				functionId: 3,
				kind: 'CreateFunctionEnvironment',
				address: 10,
			},
			slot: 0,
		});
		traverse(file, {
			Program(path) {
				cleanupEnvironmentBody(path);
				path.stop();
			},
		});
		traverse.cache.clear();
		const declaration = file.program.body[0];
		assert.ok(t.isFunctionDeclaration(declaration));
		assert.ok(sameLocation(locationOf(declaration.id), locationOf(tagged)));
	});

	it('keeps a named expression when adopting its name would collide', () => {
		const program = cleanup(
			`
			var installed = other;
			var _env_3_0;
			_env_3_0 = function installed() { return installed; };
			use(_env_3_0);
		`,
			(program) => {
				const assignment = (program.body[2] as t.ExpressionStatement)
					.expression as t.AssignmentExpression;
				tagStorageLocation(assignment.left as t.Identifier, {
					kind: 'environment-slot',
					environment: {
						functionId: 3,
						kind: 'CreateFunctionEnvironment',
						address: 10,
					},
					slot: 0,
				});
			},
		);
		assert.equal(program.body.length, 3);
		const declaration = program.body[1];
		assert.ok(t.isVariableDeclaration(declaration, { kind: 'var' }));
		assert.equal(declaration.declarations.length, 1);
		const declarator = declaration.declarations[0];
		assert.ok(t.isIdentifier(declarator.id, { name: '_env_3_0' }));
		assert.ok(t.isFunctionExpression(declarator.init));
		assert.ok(t.isIdentifier(declarator.init.id, { name: 'installed' }));
	});

	it('does not adopt a name from an untagged environment spelling', () => {
		const program = cleanup(`
			var _env_3_0;
			_env_3_0 = function installed() { return installed; };
			use(_env_3_0);
		`);
		assert.equal(program.body.length, 2);
		const declaration = program.body[0];
		assert.ok(t.isVariableDeclaration(declaration, { kind: 'var' }));
		const declarator = declaration.declarations[0];
		assert.ok(t.isIdentifier(declarator.id, { name: '_env_3_0' }));
		assert.ok(t.isFunctionExpression(declarator.init));
		assert.ok(t.isIdentifier(declarator.init.id, { name: 'installed' }));
	});
});
