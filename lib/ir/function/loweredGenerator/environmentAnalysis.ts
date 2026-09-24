import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import { AddressGraph } from '../../../utils/graph.ts';
import type { IRFunction } from '../mod.ts';
import { liftSSABlocktoIR } from '../../ast/lift.ts';
import { tagStorageLocation } from '../../ast/alias.ts';
import type { LiftedAST } from '../../ast/mod.ts';
import {
	comparableAst,
	extractFunctionRef,
	isUndefinedNode,
} from '../../ast/utils.ts';
import {
	environmentStoreFromStatement,
	loadEnvironmentCall,
} from './envAccess.ts';
import { debug } from './debug.ts';
import {
	rawFunctionId,
	rawRegisterIndex,
	roleStateControlSlots,
} from './recognition.ts';
import { caseBodies } from './caseUtils.ts';
import { stripSyntheticStatements } from './caseLifting.ts';
import type {
	CaseInfo,
	LoweredEnvironmentAliases,
	RawEnvironmentRef,
	RawInstructionLike,
	StateRoles,
} from './types.ts';

function loweredPureAliasExpression(expr: t.Expression): boolean {
	if (
		t.isIdentifier(expr) ||
		t.isThisExpression(expr) ||
		t.isNullLiteral(expr) ||
		t.isStringLiteral(expr) ||
		t.isNumericLiteral(expr) ||
		t.isBooleanLiteral(expr) ||
		t.isBigIntLiteral(expr)
	) return true;
	if (expr.extra?.isBuiltin) return true;
	if (t.isUnaryExpression(expr)) {
		return expr.operator !== 'delete' &&
			t.isExpression(expr.argument) &&
			loweredPureAliasExpression(expr.argument);
	}
	if (t.isBinaryExpression(expr) || t.isLogicalExpression(expr)) {
		return t.isExpression(expr.left) &&
			loweredPureAliasExpression(expr.left) &&
			t.isExpression(expr.right) &&
			loweredPureAliasExpression(expr.right);
	}
	if (t.isConditionalExpression(expr)) {
		return loweredPureAliasExpression(expr.test) &&
			loweredPureAliasExpression(expr.consequent) &&
			loweredPureAliasExpression(expr.alternate);
	}
	return false;
}

function loweredPureAliasStatement(stmt: t.Statement): boolean {
	return t.isExpressionStatement(stmt) &&
		loweredPureAliasExpression(stmt.expression);
}

function loweredAliasExpressionsEqual(left: t.Expression, right: t.Expression) {
	return JSON.stringify(comparableAst(left)) ===
		JSON.stringify(comparableAst(right));
}

function callEnvironmentName(
	aliases: LoweredEnvironmentAliases,
	env: t.Expression,
) {
	if (t.isIdentifier(env) && aliases.envSlots.has(env.name)) return env.name;
	const load = loadEnvironmentCall(env);
	if (!load) return;
	if (
		t.isIdentifier(load.env) &&
		aliases.parentEnvNames.has(load.env.name)
	) {
		return aliases.spillEnvSlots.get(load.slot);
	}
}

function loadEnvironmentAlias(
	aliases: LoweredEnvironmentAliases,
	expr: t.Expression,
) {
	const load = loadEnvironmentCall(expr);
	if (!load) return;
	const envName = callEnvironmentName(aliases, load.env);
	if (envName && aliases.escapingEnvNames.has(envName)) return;
	if (envName) {
		const value = aliases.envSlots.get(envName)?.get(load.slot);
		if (value) return value;
	}
	if (
		t.isIdentifier(load.env) &&
		aliases.escapingEnvNames.has(load.env.name)
	) return;
	if (t.isIdentifier(load.env) && aliases.parentEnvNames.has(load.env.name)) {
		const value = aliases.parentEnvSlots.get(load.slot);
		if (value) return value;
	}
}

function substituteLoweredAliases(
	aliases: LoweredEnvironmentAliases,
	expr: t.Expression,
) {
	const root = t.cloneNode(expr, true);
	const wrapped = t.file(t.program([t.expressionStatement(root)]));
	traverse(wrapped, {
		Identifier(path: NodePath<t.Identifier>) {
			if (!path.isReferencedIdentifier()) return;
			const value = aliases.values.get(path.node.name);
			if (!value) return;
			path.replaceWith(t.cloneNode(value, true));
		},
		MemberExpression: {
			exit(path: NodePath<t.MemberExpression>) {
				if (
					path.parentPath?.isAssignmentExpression({
						operator: '=',
					}) &&
					path.key === 'left'
				) return;
				const alias = loadEnvironmentAlias(
					aliases,
					path.node,
				);
				if (!alias) return;
				path.replaceWith(t.cloneNode(alias, true));
			},
		},
	});
	const stmt = wrapped.program.body[0];
	if (!t.isExpressionStatement(stmt)) return root;
	return stmt.expression;
}

function substituteLoweredAliasesInStatement(
	aliases: LoweredEnvironmentAliases,
	stmt: t.Statement,
) {
	const cloned = t.cloneNode(stmt, true);
	const wrapped = t.file(t.program([cloned]));
	traverse(wrapped, {
		Identifier(path: NodePath<t.Identifier>) {
			if (!path.isReferencedIdentifier()) return;
			const value = aliases.values.get(path.node.name);
			if (!value) return;
			path.replaceWith(t.cloneNode(value, true));
		},
		MemberExpression: {
			exit(path: NodePath<t.MemberExpression>) {
				if (
					path.parentPath?.isAssignmentExpression({
						operator: '=',
					}) &&
					path.key === 'left'
				) return;
				const alias = loadEnvironmentAlias(
					aliases,
					path.node,
				);
				if (!alias) return;
				path.replaceWith(t.cloneNode(alias, true));
			},
		},
	});
	return wrapped.program.body;
}

export function discoverParentEnvironmentNames(cases: Map<number, CaseInfo>) {
	const names = new Set<string>();
	for (const info of cases.values()) {
		for (const body of caseBodies(info)) {
			for (const stmt of body) {
				if (!t.isVariableDeclaration(stmt)) continue;
				const decl = stmt.declarations[0];
				if (
					t.isVariableDeclarator(decl) &&
					t.isIdentifier(decl.id) &&
					t.isCallExpression(decl.init) &&
					t.isV8IntrinsicIdentifier(decl.init.callee, {
						name: 'GetParentEnvironment',
					})
				) names.add(decl.id.name);
			}
		}
	}
	return names;
}

interface EnvironmentPromotionRequirements {
	local: Map<string, Set<number>>;
	parent: Map<string, Set<number>>;
}

/**
 * Slots whose recovered source needs an explicit join variable.
 *
 * The same raw block can appear in more than one dispatch case, so stores are
 * deduplicated by bytecode address. Initial `undefined` writes are excluded:
 * they implement the state machine's cell initialization, not a source-level
 * assignment, and a later real store dominates the local reads we promote.
 */
function collectEnvironmentPromotionRequirements(
	cases: Map<number, CaseInfo>,
	preludeBody: t.Statement[],
): EnvironmentPromotionRequirements {
	const parentEnvNames = discoverParentEnvironmentNames(cases);
	const envAliases = new Map<string, string>();
	const parentSpillSlots = new Map<number, string>();
	const valueAliases = new Map<string, t.Expression>();
	const storeSites = new Map<string, Map<number, Set<string>>>();
	const parentStoreSites = new Map<string, Map<number, Set<string>>>();
	const loadsWithoutLocalStore = new Map<string, Set<number>>();
	const parentLoadsWithoutLocalStore = new Map<string, Set<number>>();
	const addSlot = (
		target: Map<string, Set<number>>,
		envName: string,
		slot: number,
	) => {
		const slots = target.get(envName) ?? new Set<number>();
		slots.add(slot);
		target.set(envName, slots);
	};

	const observeDeclaration = (stmt: t.Statement) => {
		if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
			return;
		}
		const decl = stmt.declarations[0];
		if (
			!t.isVariableDeclarator(decl) ||
			!t.isIdentifier(decl.id) ||
			!t.isExpression(decl.init)
		) return;
		if (
			t.isCallExpression(decl.init) &&
			t.isV8IntrinsicIdentifier(decl.init.callee, {
				name: 'GetParentEnvironment',
			})
		) {
			parentEnvNames.add(decl.id.name);
			return;
		}
		if (
			t.isCallExpression(decl.init) &&
			t.isV8IntrinsicIdentifier(decl.init.callee, {
				name: 'CreateTopLevelEnvironment',
			})
		) {
			envAliases.set(decl.id.name, decl.id.name);
			return;
		}
		if (loweredPureAliasExpression(decl.init)) {
			valueAliases.set(decl.id.name, decl.init);
		}
	};
	const resolveValue = (value: t.Expression) => {
		let resolved = value;
		const seen = new Set<string>();
		while (t.isIdentifier(resolved) && !seen.has(resolved.name)) {
			seen.add(resolved.name);
			const alias = valueAliases.get(resolved.name);
			if (!alias) break;
			resolved = alias;
		}
		return resolved;
	};
	const resolveEnvName = (expr: t.Expression): string | undefined => {
		if (t.isIdentifier(expr)) return envAliases.get(expr.name);
		const load = loadEnvironmentCall(expr);
		if (
			load &&
			t.isIdentifier(load.env) &&
			parentEnvNames.has(load.env.name)
		) return parentSpillSlots.get(load.slot);
	};
	const addStore = (
		target: Map<string, Map<number, Set<string>>>,
		envName: string,
		slot: number,
		stmt: t.Statement,
		value: t.Expression,
	) => {
		const slots = target.get(envName) ?? new Map<number, Set<string>>();
		const sites = slots.get(slot) ?? new Set<string>();
		const address = (stmt as LiftedAST<t.Statement>).extra?.address;
		const site = address == null
			? JSON.stringify(comparableAst(value))
			: `0x${address.toString(16)}`;
		sites.add(site);
		slots.set(slot, sites);
		target.set(envName, slots);
		return { site, sites };
	};

	for (const stmt of preludeBody) observeDeclaration(stmt);
	for (const info of cases.values()) {
		for (const body of caseBodies(info)) {
			const loadedSlots = new Set<string>();
			const previousStores = new Map<
				string,
				{ site: string; sites: Set<string> }
			>();
			const observeLoads = (node: t.Node) => {
				t.traverseFast(node, (candidate) => {
					if (!t.isMemberExpression(candidate)) return;
					const load = loadEnvironmentCall(candidate);
					if (!load) return;
					if (
						t.isIdentifier(load.env) &&
						parentEnvNames.has(load.env.name)
					) {
						const key = `parent:${load.env.name}:${load.slot}`;
						loadedSlots.add(key);
						if (!previousStores.has(key)) {
							addSlot(
								parentLoadsWithoutLocalStore,
								load.env.name,
								load.slot,
							);
						}
						return;
					}
					const envName = resolveEnvName(load.env);
					if (envName) {
						const key = `local:${envName}:${load.slot}`;
						loadedSlots.add(key);
						if (!previousStores.has(key)) {
							addSlot(loadsWithoutLocalStore, envName, load.slot);
						}
					}
				});
			};
			const replaceDeadStore = (
				key: string,
				store: { site: string; sites: Set<string> },
			) => {
				const previous = previousStores.get(key);
				if (previous && !loadedSlots.has(key)) {
					previous.sites.delete(previous.site);
				}
				previousStores.set(key, store);
				loadedSlots.delete(key);
			};

			for (const stmt of body) {
				observeDeclaration(stmt);
				if (
					t.isVariableDeclaration(stmt) &&
					stmt.declarations.length === 1
				) {
					const decl = stmt.declarations[0];
					if (
						t.isVariableDeclarator(decl) &&
						t.isIdentifier(decl.id) &&
						t.isExpression(decl.init)
					) {
						const envName = resolveEnvName(decl.init);
						if (envName) envAliases.set(decl.id.name, envName);
					}
				}

				const store = environmentStoreFromStatement(stmt);
				if (!store) {
					observeLoads(stmt);
					continue;
				}
				observeLoads(store.value);
				observeLoads(store.env);
				const value = resolveValue(store.value);
				if (isUndefinedNode(value)) continue;
				if (
					t.isIdentifier(store.env) &&
					parentEnvNames.has(store.env.name)
				) {
					if (
						t.isIdentifier(store.value) &&
						envAliases.has(store.value.name)
					) {
						parentSpillSlots.set(
							store.slot,
							envAliases.get(store.value.name)!,
						);
						continue;
					}
					if (loweredPureAliasExpression(value)) {
						const key = `parent:${store.env.name}:${store.slot}`;
						replaceDeadStore(
							key,
							addStore(
								parentStoreSites,
								store.env.name,
								store.slot,
								stmt,
								value,
							),
						);
					}
					continue;
				}
				const envName = resolveEnvName(store.env);
				if (envName) {
					const key = `local:${envName}:${store.slot}`;
					replaceDeadStore(
						key,
						addStore(storeSites, envName, store.slot, stmt, value),
					);
				}
			}
		}
	}

	const conflicts = (
		sitesByEnvironment: Map<string, Map<number, Set<string>>>,
		nonLocalLoads: Map<string, Set<number>>,
	) => {
		const result = new Map<string, Set<number>>();
		for (const [envName, slots] of sitesByEnvironment) {
			for (const slot of slots.keys()) {
				if (!nonLocalLoads.get(envName)?.has(slot)) continue;
				addSlot(result, envName, slot);
			}
		}
		return result;
	};
	return {
		local: conflicts(storeSites, loadsWithoutLocalStore),
		parent: conflicts(
			parentStoreSites,
			parentLoadsWithoutLocalStore,
		),
	};
}

export function reduceLoweredGeneratorEnvironmentAliases(
	func: IRFunction,
	cases: Map<number, CaseInfo>,
	order: number[],
	preludeBody: t.Statement[],
	roles: StateRoles,
) {
	const escapingEnvNames = escapingClosureEnvironmentNames(func, [
		...preludeBody,
		...[...cases.values()].flatMap((info) => caseBodies(info).flat()),
	]);
	const aliases: LoweredEnvironmentAliases = {
		parentEnvNames: discoverParentEnvironmentNames(cases),
		escapingEnvNames,
		spillEnvSlots: new Map(),
		parentEnvSlots: new Map(
			[
				...(func.file.loweredGeneratorWrapperSlotAliases.get(func.id) ??
					[]),
			].map(([slot, value]) => [slot, t.cloneNode(value, true)]),
		),
		envSlots: new Map(),
		materializedEnvSlots: new Map(),
		environmentSites: new Map(),
		values: new Map(),
	};
	const promotionRequirements = collectEnvironmentPromotionRequirements(
		cases,
		preludeBody,
	);
	const materializedDeclarations: t.VariableDeclaration[] = [];
	const materializedSlotIdentifier = (
		envName: string,
		slot: number,
		initialValue?: t.Expression,
	) => {
		let slots = aliases.materializedEnvSlots.get(envName);
		if (!slots) {
			slots = new Map();
			aliases.materializedEnvSlots.set(envName, slots);
		}
		const existing = slots.get(slot);
		if (existing) return existing;
		const safeEnvName = envName.replaceAll(/[^A-Za-z0-9_$]/g, '_');
		const id = t.identifier(
			`_envCell_${func.id}_${safeEnvName}_${slot}`,
		);
		id.extra = {
			recoveredEnvironmentSlot: {
				environmentName: envName,
				slot,
			},
		};
		const site = aliases.environmentSites.get(envName);
		if (site) {
			tagStorageLocation(id, {
				kind: 'environment-slot',
				environment: site,
				slot,
			});
		}
		slots.set(slot, id);
		materializedDeclarations.push(t.variableDeclaration('let', [
			t.variableDeclarator(
				t.cloneNode(id),
				initialValue == null ? null : t.cloneNode(initialValue, true),
			),
		]));
		return id;
	};
	const materializedSlotAssignment = (
		id: t.Identifier,
		value: t.Expression,
	) => {
		const statement = t.expressionStatement(t.assignmentExpression(
			'=',
			t.cloneNode(id),
			t.cloneNode(value, true),
		)) as LiftedAST<t.ExpressionStatement>;
		statement.extra = {
			recoveredEnvironmentSlot: (id as LiftedAST<t.Identifier>).extra!
				.recoveredEnvironmentSlot!,
		};
		return statement;
	};
	for (const stmt of preludeBody) {
		if (
			!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1
		) continue;
		const decl = stmt.declarations[0];
		if (
			!t.isVariableDeclarator(decl) ||
			!t.isIdentifier(decl.id) ||
			!t.isExpression(decl.init) ||
			!loweredPureAliasExpression(decl.init)
		) {
			if (
				t.isVariableDeclarator(decl) &&
				t.isIdentifier(decl.id) &&
				t.isCallExpression(decl.init) &&
				t.isV8IntrinsicIdentifier(decl.init.callee, {
					name: 'GetParentEnvironment',
				})
			) {
				aliases.parentEnvNames.add(decl.id.name);
			}
			continue;
		}
		aliases.values.set(decl.id.name, t.cloneNode(decl.init, true));
	}
	for (let i = 0; i < preludeBody.length; i++) {
		const substituted = substituteLoweredAliasesInStatement(
			aliases,
			preludeBody[i],
		).filter((stmt) => !loweredPureAliasStatement(stmt));
		preludeBody.splice(i, 1, ...substituted);
		i += substituted.length - 1;
	}
	debug('lowered generator env aliases start', {
		parentEnvNames: [...aliases.parentEnvNames],
		parentEnvSlots: [...aliases.parentEnvSlots].map(([slot, value]) => ({
			slot,
			value: value.type,
		})),
		stateEnvRegisterIndex: roles.stateEnvRegisterIndex,
		stateControlSlots: [...roleStateControlSlots(roles)],
		params: func.params.map((param) =>
			t.isIdentifier(param) ? param.name : param.type
		),
	});

	const reduceBody = (body: t.Statement[]) => {
		const reduced: t.Statement[] = [];
		for (const stmt of body) {
			if (
				t.isVariableDeclaration(stmt) && stmt.declarations.length === 1
			) {
				const decl = stmt.declarations[0];
				if (
					t.isVariableDeclarator(decl) &&
					t.isIdentifier(decl.id) &&
					t.isCallExpression(decl.init) &&
					t.isV8IntrinsicIdentifier(decl.init.callee, {
						name: 'CreateTopLevelEnvironment',
					})
				) {
					const address = (decl.init as LiftedAST<t.CallExpression>)
						.extra
						?.address;
					if (address != null) {
						aliases.environmentSites.set(decl.id.name, {
							functionId: func.id,
							address,
							kind: 'CreateTopLevelEnvironment',
						});
					}
					if (escapingEnvNames.has(decl.id.name)) {
						reduced.push(stmt);
						continue;
					}
					aliases.envSlots.set(decl.id.name, new Map());
					continue;
				}

				if (
					t.isVariableDeclarator(decl) &&
					t.isIdentifier(decl.id) &&
					t.isExpression(decl.init)
				) {
					const substituted = substituteLoweredAliases(
						aliases,
						decl.init,
					);
					const envName = callEnvironmentName(aliases, substituted);
					if (envName) {
						aliases.envSlots.set(
							decl.id.name,
							aliases.envSlots.get(envName) ?? new Map(),
						);
						const conflictingSlots = promotionRequirements.local
							.get(
								envName,
							);
						if (conflictingSlots) {
							promotionRequirements.local.set(
								decl.id.name,
								conflictingSlots,
							);
						}
						const site = aliases.environmentSites.get(envName);
						if (site) {
							aliases.environmentSites.set(decl.id.name, site);
						}
						const materializedSlots = aliases.materializedEnvSlots
							.get(envName);
						if (materializedSlots) {
							aliases.materializedEnvSlots.set(
								decl.id.name,
								materializedSlots,
							);
						}
						continue;
					}
					const loadAlias = loadEnvironmentAlias(
						aliases,
						substituted,
					);
					if (loadAlias) {
						aliases.values.set(
							decl.id.name,
							t.cloneNode(loadAlias, true),
						);
						continue;
					}
					if (loweredPureAliasExpression(substituted)) {
						aliases.values.set(decl.id.name, substituted);
						continue;
					}
					decl.init = substituted;
				}
			}

			const store = environmentStoreFromStatement(stmt);
			if (store) {
				const stateEnvironment =
					(store.env as LiftedAST<t.Node>).extra?.sourceRegister
							?.index === roles.stateEnvRegisterIndex ||
					(t.isIdentifier(store.env) &&
						store.env.name.startsWith(
							`r${roles.stateEnvRegisterIndex}_`,
						));
				if (
					stateEnvironment &&
					roleStateControlSlots(roles).has(store.slot) &&
					store.slot !== roles.caughtExceptionSlot
				) {
					continue;
				}
				const value = substituteLoweredAliases(aliases, store.value);
				if (
					t.isIdentifier(store.env) &&
					aliases.escapingEnvNames.has(store.env.name)
				) {
					reduced.push(
						...substituteLoweredAliasesInStatement(aliases, stmt)
							.filter((candidate) =>
								!loweredPureAliasStatement(candidate)
							),
					);
					continue;
				}
				if (
					t.isIdentifier(store.env) &&
					aliases.parentEnvNames.has(store.env.name) &&
					t.isIdentifier(value) &&
					aliases.envSlots.has(value.name)
				) {
					aliases.spillEnvSlots.set(store.slot, value.name);
					debug('lowered generator spill env slot', {
						slot: store.slot,
						envName: value.name,
					});
					continue;
				}

				if (
					t.isIdentifier(store.env) &&
					aliases.parentEnvNames.has(store.env.name) &&
					loweredPureAliasExpression(value)
				) {
					const materializedEnvName = `parent_${store.env.name}`;
					const materialized = aliases.materializedEnvSlots
						.get(materializedEnvName)
						?.get(store.slot);
					if (materialized) {
						reduced.push(
							materializedSlotAssignment(materialized, value),
						);
						aliases.parentEnvSlots.set(
							store.slot,
							t.cloneNode(materialized),
						);
						continue;
					}
					if (
						promotionRequirements.parent.get(store.env.name)?.has(
							store.slot,
						)
					) {
						const id = materializedSlotIdentifier(
							materializedEnvName,
							store.slot,
							aliases.parentEnvSlots.get(store.slot),
						);
						aliases.parentEnvSlots.set(store.slot, t.cloneNode(id));
						reduced.push(materializedSlotAssignment(id, value));
						continue;
					}
					aliases.parentEnvSlots.set(store.slot, value);
					continue;
				}

				const envName = callEnvironmentName(aliases, store.env);
				if (envName) {
					if (escapingEnvNames.has(envName)) {
						reduced.push(
							...substituteLoweredAliasesInStatement(
								aliases,
								stmt,
							).filter((stmt) =>
								!loweredPureAliasStatement(stmt)
							),
						);
						continue;
					}
					const slots = aliases.envSlots.get(envName);
					const materialized = aliases.materializedEnvSlots
						.get(envName)
						?.get(store.slot);
					if (materialized) {
						reduced.push(
							materializedSlotAssignment(materialized, value),
						);
						slots?.set(store.slot, t.cloneNode(materialized));
						continue;
					}
					if (
						promotionRequirements.local.get(envName)?.has(
							store.slot,
						)
					) {
						if (isUndefinedNode(value)) {
							slots?.set(store.slot, value);
							continue;
						}
						const id = materializedSlotIdentifier(
							envName,
							store.slot,
							undefined,
						);
						slots?.set(store.slot, t.cloneNode(id));
						reduced.push(materializedSlotAssignment(id, value));
						continue;
					}
					const previous = slots?.get(store.slot);
					if (
						previous &&
						!isUndefinedNode(previous) &&
						!loweredAliasExpressionsEqual(previous, value) &&
						loweredPureAliasExpression(previous)
					) {
						const id = materializedSlotIdentifier(
							envName,
							store.slot,
							previous,
						);
						slots?.set(store.slot, t.cloneNode(id));
						reduced.push(materializedSlotAssignment(id, value));
						continue;
					}
					slots?.set(store.slot, value);
					continue;
				}
			}

			reduced.push(
				...substituteLoweredAliasesInStatement(aliases, stmt)
					.filter((stmt) => !loweredPureAliasStatement(stmt)),
			);
		}
		return reduced;
	};

	for (const state of order) {
		const info = cases.get(state);
		if (!info) continue;
		if (info.blocks) {
			for (const address of info.path) {
				const block = info.blocks.get(address);
				if (!block) continue;
				block.body = reduceBody(block.body);
				if (block.branch) {
					block.branch = substituteLoweredAliases(
						aliases,
						block.branch,
					);
				}
			}
			continue;
		}
		const reduced = reduceBody(info.body);
		info.body = reduced;
		if (reduced.length > 0) {
			info.terminal = reduced.at(-1) ?? info.terminal;
		} else {
			const terminal = substituteLoweredAliasesInStatement(
				aliases,
				info.terminal,
			);
			info.terminal = terminal.at(-1) ?? info.terminal;
		}
	}
	preludeBody.unshift(...materializedDeclarations);
	return new Set(
		materializedDeclarations.flatMap((declaration) =>
			declaration.declarations.flatMap((declarator) =>
				t.isIdentifier(declarator.id) ? [declarator.id.name] : []
			)
		),
	);
}

function capturedSlotsForClosureEnvironment(
	func: IRFunction,
	functionId: number,
	seen = new Set<number>(),
): Set<number> | null {
	if (seen.has(functionId)) return new Set();
	seen.add(functionId);
	const rawFunc = func.file.functions[functionId];
	if (!rawFunc) return null;

	const slots = new Set<number>();
	const envRefs = new Map<number, RawEnvironmentRef>();
	const refForRegister = (value: unknown) => {
		const index = rawRegisterIndex(value);
		return index == null ? undefined : envRefs.get(index);
	};
	const addNestedCapturedSlots = (nestedId: number) => {
		const nested = capturedSlotsForClosureEnvironment(
			func,
			nestedId,
			seen,
		);
		if (nested == null) return false;
		for (const slot of nested) slots.add(slot);
		return true;
	};

	for (const block of rawFunc.basicBlocks.values()) {
		for (const instr of block.instructions as RawInstructionLike[]) {
			switch (instr.instruction) {
				case 'GetParentEnvironment': {
					const dest = rawRegisterIndex(instr.destination);
					if (dest == null) break;
					envRefs.set(dest, {
						kind: 'closure',
						depth: instr.levelIndex ?? 0,
					});
					break;
				}
				case 'GetEnvironment': {
					const dest = rawRegisterIndex(instr.destination);
					const parent = refForRegister(instr.parentEnv);
					if (dest == null || !parent) break;
					envRefs.set(
						dest,
						parent.kind === 'closure'
							? {
								kind: 'closure',
								depth: parent.depth +
									(instr.levelIndex ?? 0),
							}
							: { kind: 'local' },
					);
					break;
				}
				case 'CreateFunctionEnvironment':
				case 'CreateTopLevelEnvironment':
				case 'CreateEnvironment':
				case 'CreateInnerEnvironment': {
					const dest = rawRegisterIndex(instr.destination);
					if (dest != null) envRefs.set(dest, { kind: 'local' });
					break;
				}
				case 'LoadFromEnvironment':
				case 'StoreToEnvironment':
				case 'StoreNPToEnvironment': {
					const env = refForRegister(instr.environment);
					if (env?.kind === 'closure' && env.depth === 0) {
						slots.add(instr.slotIndex as number);
					}
					break;
				}
				case 'CreateClosure':
				case 'CreateGeneratorClosure':
				case 'CreateAsyncClosure':
				case 'CreateGenerator': {
					const env = refForRegister(instr.environment);
					if (env?.kind !== 'closure' || env.depth !== 0) break;
					const nestedId = rawFunctionId(instr.function);
					if (nestedId == null) return null;
					if (!addNestedCapturedSlots(nestedId)) return null;
					break;
				}
			}
		}
	}

	seen.delete(functionId);
	return slots;
}

function escapingClosureEnvironmentNames(
	func: IRFunction,
	body: t.Statement[],
) {
	const names = new Set<string>();
	for (const stmt of body) {
		t.traverseFast(stmt, (node) => {
			if (!t.isCallExpression(node)) return;
			if (!t.isV8IntrinsicIdentifier(node.callee)) return;
			const name = node.callee.name;
			const envArg = name === 'CreateGenerator' ? node.arguments[0] : (
				name === 'CreateClosure' ||
					name === 'CreateGeneratorClosure' ||
					name === 'CreateAsyncClosure'
					? node.arguments[1]
					: null
			);
			if (!t.isIdentifier(envArg)) return;
			const funcRef = name === 'CreateGenerator'
				? node.arguments[1]
				: node.arguments[0];
			const functionId = extractFunctionRef(funcRef);
			if (functionId == null) {
				names.add(envArg.name);
				return;
			}
			const captured = capturedSlotsForClosureEnvironment(
				func,
				functionId,
			);
			if (captured == null || captured.size > 0) names.add(envArg.name);
		});
	}
	return names;
}

function isUIntSwitchMarkerStatement(stmt: t.Statement) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	return t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, { name: 'UIntSwitchImm' });
}

function isStablePreludeScalar(node: t.Expression): boolean {
	return t.isIdentifier(node) ||
		t.isThisExpression(node) ||
		t.isNullLiteral(node) ||
		t.isStringLiteral(node) ||
		t.isNumericLiteral(node) ||
		t.isBooleanLiteral(node) ||
		t.isBigIntLiteral(node) ||
		(t.isMemberExpression(node) &&
			t.isExpression(node.object) &&
			!t.isIdentifier(node.object, { name: 'arguments' }) &&
			isStablePreludeScalar(node.object) &&
			(!node.computed ||
				t.isStringLiteral(node.property) ||
				t.isNumericLiteral(node.property) ||
				t.isIdentifier(node.property))) ||
		(t.isUnaryExpression(node) &&
			node.operator !== 'delete' &&
			t.isExpression(node.argument) &&
			isStablePreludeScalar(node.argument));
}

function isGetParentEnvironmentCall(expr: t.Expression) {
	return t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee, {
			name: 'GetParentEnvironment',
		});
}

function isStablePreludeDeclaration(stmt: t.Statement) {
	if (!t.isVariableDeclaration(stmt)) return false;
	if (stmt.declarations.length !== 1) return false;
	const decl = stmt.declarations[0];
	if (!t.isVariableDeclarator(decl) || !decl.init) return false;
	if (t.isIdentifier(decl.init)) {
		return decl.init.name === 'global' || decl.init.name === 'undefined';
	}
	if (t.isCallExpression(decl.init)) {
		return isGetParentEnvironmentCall(decl.init);
	}
	return isStablePreludeScalar(decl.init);
}

export function collectPreludeBody(func: IRFunction, roles: StateRoles) {
	const predecessors = new AddressGraph();
	for (const [addr, block] of func.ssa._func.basicBlocks) {
		for (const succ of block.consequentAddresses) {
			predecessors.addEdge(succ, addr);
		}
	}

	const addresses: number[] = [];
	const seen = new Set<number>();
	let current = roles.mainSwitchAddress;
	while (true) {
		const preds = [...(predecessors.get(current) ?? [])].filter((pred) =>
			pred < current
		);
		if (preds.length !== 1) break;
		const pred = preds[0];
		if (seen.has(pred)) break;
		seen.add(pred);
		addresses.push(pred);
		current = pred;
		if (pred === 0) break;
	}
	addresses.reverse();

	const body: t.Statement[] = [];
	for (const address of addresses) {
		const block = func.ssa.basicBlocks.get(address);
		if (!block) continue;
		body.push(
			...stripSyntheticStatements(
				<t.Statement[]> liftSSABlocktoIR(func, block).body,
				roles,
			).filter((stmt) =>
				!isUIntSwitchMarkerStatement(stmt) &&
				isStablePreludeDeclaration(stmt)
			),
		);
	}
	for (const address of roles.dispatchPreludeAddresses ?? []) {
		const block = func.ssa.basicBlocks.get(address);
		if (!block) continue;
		body.push(
			...stripSyntheticStatements(
				<t.Statement[]> liftSSABlocktoIR(func, block).body,
				roles,
			).filter((stmt) =>
				!isUIntSwitchMarkerStatement(stmt) &&
				isStablePreludeDeclaration(stmt)
			),
		);
	}
	return body;
}
