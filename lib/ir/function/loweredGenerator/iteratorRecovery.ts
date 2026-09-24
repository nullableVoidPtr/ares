import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import type { IRFunction } from '../mod.ts';
import { invertTest } from '../../ast/expression.ts';
import {
	environmentStoreFromStatement,
	isEnvMember,
	loadEnvironmentCall,
} from './envAccess.ts';
import type { CaseInfo } from './types.ts';

function intrinsicArrayDeclaration(stmt: t.Statement, name: string) {
	if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
		return;
	}
	const decl = stmt.declarations[0];
	if (!t.isArrayPattern(decl.id) || !t.isCallExpression(decl.init)) return;
	if (!t.isV8IntrinsicIdentifier(decl.init.callee, { name })) return;
	const ids = decl.id.elements.filter((element): element is t.Identifier =>
		t.isIdentifier(element)
	);
	if (ids.length !== decl.id.elements.length) return;
	return { ids, args: decl.init.arguments };
}

function singleIdentifierDeclaration(stmt: t.Statement) {
	if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
		return;
	}
	const decl = stmt.declarations[0];
	if (!t.isIdentifier(decl.id) || !t.isExpression(decl.init)) return;
	return { id: decl.id, init: decl.init };
}

function sameEnvironmentExpression(left: t.Expression, right: t.Expression) {
	return t.isIdentifier(left) && t.isIdentifier(right) &&
		left.name === right.name;
}

function replaceRecoveredEnvironmentLoads(
	body: t.Statement[],
	start: number,
	env: t.Expression,
	slot: number,
	value: t.Expression,
	spill?: { env: t.Expression; slot: number },
) {
	const envAliases = new Set<string>();
	const isRequestedEnvironment = (expr: t.Expression) => {
		if (sameEnvironmentExpression(expr, env)) return true;
		if (t.isIdentifier(expr) && envAliases.has(expr.name)) return true;
		if (!spill) return false;
		const spillLoad = loadEnvironmentCall(expr);
		return !!spillLoad && spillLoad.slot === spill.slot &&
			sameEnvironmentExpression(spillLoad.env, spill.env);
	};
	for (let i = start; i < body.length; i++) {
		const aliasDecl = singleIdentifierDeclaration(body[i]);
		if (aliasDecl && spill) {
			const load = loadEnvironmentCall(aliasDecl.init);
			if (
				load && load.slot === spill.slot &&
				sameEnvironmentExpression(load.env, spill.env)
			) envAliases.add(aliasDecl.id.name);
		}
		const wrapped = t.file(t.program([body[i]]));
		traverse(wrapped, {
			Expression(path: NodePath<t.Expression>) {
				if (!isEnvMember(path.node)) return;
				const load = loadEnvironmentCall(path.node);
				if (
					load && load.slot === slot &&
					isRequestedEnvironment(load.env)
				) {
					path.replaceWith(t.cloneNode(value, true));
					path.skip();
				}
			},
			MemberExpression: {
				exit(path: NodePath<t.MemberExpression>) {
					const load = loadEnvironmentCall(path.node);
					if (!load || load.slot !== slot) return;
					if (sameEnvironmentExpression(load.env, env)) {
						path.replaceWith(t.cloneNode(value, true));
						return;
					}
					if (!spill) return;
					const spillLoad = loadEnvironmentCall(load.env);
					if (
						spillLoad && spillLoad.slot === spill.slot &&
						sameEnvironmentExpression(spillLoad.env, spill.env)
					) path.replaceWith(t.cloneNode(value, true));
				},
			},
		});
		body[i] = wrapped.program.body[0];
	}
}

function expressionStatementCall(stmt: t.Statement) {
	return t.isExpressionStatement(stmt) && t.isCallExpression(stmt.expression)
		? stmt.expression
		: undefined;
}

export function normalizeRecoveredIteratorEnvironmentDestructuring(
	func: IRFunction,
): boolean {
	let changed = false;
	for (const block of func.blocks.values()) {
		const body = block.body as t.Statement[];
		for (let i = 0; i < body.length - 8; i++) {
			const begin = intrinsicArrayDeclaration(body[i], 'IteratorBegin');
			if (!begin || begin.ids.length !== 2) continue;
			const [iteratorId, iteratorStateId] = begin.ids;
			const iteratorStateAlias = singleIdentifierDeclaration(body[i + 1]);
			const tempStore = environmentStoreFromStatement(body[i + 2]);
			const iteratorAlias = singleIdentifierDeclaration(body[i + 3]);
			const next = intrinsicArrayDeclaration(body[i + 4], 'IteratorNext');
			const done = singleIdentifierDeclaration(body[i + 5]);
			const valueStore = environmentStoreFromStatement(body[i + 6]);
			const target = singleIdentifierDeclaration(body[i + 7]);
			const targetStore = environmentStoreFromStatement(body[i + 8]);
			if (
				!iteratorStateAlias ||
				!t.isIdentifier(iteratorStateAlias.init, {
					name: iteratorStateId.name,
				}) || !tempStore || !iteratorAlias ||
				!t.isIdentifier(iteratorAlias.init, {
					name: iteratorId.name,
				}) ||
				!next || next.ids.length !== 2 || next.args.length !== 2 ||
				!t.isIdentifier(next.args[0], {
					name: iteratorAlias.id.name,
				}) ||
				!t.isIdentifier(next.args[1], {
					name: iteratorStateAlias.id.name,
				}) || !done ||
				!t.isBinaryExpression(done.init, { operator: '===' }) ||
				!t.isIdentifier(done.init.left, { name: next.ids[1].name }) ||
				!t.isExpression(done.init.right) || !valueStore ||
				!t.isIdentifier(valueStore.value, { name: next.ids[0].name }) ||
				!target || !isEnvMember(target.init) || !targetStore ||
				!t.isIdentifier(targetStore.value, { name: target.id.name })
			) continue;
			if (
				!t.isIdentifier(tempStore.env) ||
				!t.isIdentifier(valueStore.env, { name: tempStore.env.name }) ||
				tempStore.slot !== valueStore.slot
			) continue;

			const spillStoreStatement = body.slice(0, i).findLast((stmt) => {
				const store = environmentStoreFromStatement(stmt);
				return !!store && t.isIdentifier(store.value) &&
					t.isIdentifier(targetStore.env, { name: store.value.name });
			});
			const spillStore = spillStoreStatement
				? environmentStoreFromStatement(spillStoreStatement)
				: undefined;
			const close = body[i + 9];
			const closeCall = expressionStatementCall(close);
			const hasClose = !!closeCall &&
				t.isV8IntrinsicIdentifier(closeCall.callee, {
					name: 'IteratorClose',
				});

			body.splice(
				i + 1,
				hasClose ? 9 : 8,
				t.variableDeclaration('const', [t.variableDeclarator(
					t.arrayPattern([
						t.cloneNode(next.ids[0]),
						t.cloneNode(next.ids[1]),
					]),
					t.callExpression(t.v8IntrinsicIdentifier('IteratorNext'), [
						t.cloneNode(iteratorId),
						t.cloneNode(iteratorStateId),
					]),
				)]),
				t.variableDeclaration('let', [t.variableDeclarator(
					t.cloneNode(target.id),
					t.cloneNode(done.init.right),
				)]),
				t.ifStatement(
					invertTest(t.cloneNode(done.init, true)),
					t.blockStatement([
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.cloneNode(target.id),
							t.cloneNode(next.ids[0]),
						)),
					]),
				),
				...(hasClose
					? [t.ifStatement(
						invertTest(t.cloneNode(done.init, true)),
						t.blockStatement([t.cloneNode(close, true)]),
					)]
					: []),
			);
			replaceRecoveredEnvironmentLoads(
				body,
				i + 1,
				targetStore.env,
				targetStore.slot,
				target.id,
				spillStore
					? { env: spillStore.env, slot: spillStore.slot }
					: undefined,
			);
			changed = true;
		}
	}
	return changed;
}

function caseBodies(info: CaseInfo): t.Statement[][] {
	return info.blocks
		? [...info.blocks.values()].map((block) => block.body)
		: [info.body];
}

export function hasRecoveredIteratorEnvironmentDestructuring(
	cases: Map<number, CaseInfo>,
): boolean {
	for (const info of cases.values()) {
		for (const body of caseBodies(info)) {
			for (let i = 0; i < body.length - 8; i++) {
				const begin = intrinsicArrayDeclaration(
					body[i],
					'IteratorBegin',
				);
				const next = intrinsicArrayDeclaration(
					body[i + 4],
					'IteratorNext',
				);
				const target = singleIdentifierDeclaration(body[i + 7]);
				if (
					begin && next &&
					environmentStoreFromStatement(body[i + 2]) &&
					environmentStoreFromStatement(body[i + 6]) && target &&
					isEnvMember(target.init) &&
					environmentStoreFromStatement(body[i + 8])
				) return true;
			}
		}
	}
	return false;
}
