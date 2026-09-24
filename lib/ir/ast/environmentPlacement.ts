import * as t from '@babel/types';
import type { EnvironmentSiteId } from '../../coldstore/plan.ts';
import { locationKey, locationOf, tagStorageLocation } from './alias.ts';
import type { LiftedExtra } from './mod.ts';
import { isEnvironmentSlotName } from '../environment.ts';

interface SlotGroup {
	location: {
		kind: 'environment-slot';
		environment: EnvironmentSiteId;
		slot: number;
	};
	names: Set<string>;
	assignmentCount: number;
	referenceOwners: Set<number>;
}

interface SlotDeclaration {
	declarator: t.VariableDeclarator;
	declaration: t.VariableDeclaration;
	body: t.Statement[];
}

export interface EnvironmentSlotPlacementResult {
	analysed: number;
	localized: number;
	placed: number;
	unresolved: number;
	captured: number;
	declarationsTagged: number;
	textualDeclarationsUnresolved: number;
}

function directivePrologueLength(body: readonly t.Statement[]): number {
	let index = 0;
	while (index < body.length) {
		const statement = body[index];
		if (
			!t.isExpressionStatement(statement) ||
			!t.isStringLiteral(statement.expression)
		) break;
		index++;
	}
	return index;
}

/**
 * Give each structured environment slot one declaration in its creating
 * function.
 *
 * Environment slots are runtime cells, so their identity is
 * `(creation-site, slot)`, never their emitted `_env_*` spelling. The creating
 * function body is deliberately used as the first authoritative placement:
 * it contains every closure that can capture the cell and preserves the
 * slot's initial `undefined` value. Later dataflow may narrow an uncaptured,
 * single-write slot, but it may never copy a captured declaration into a child.
 */
export function placeEnvironmentSlotsInTree(
	root: t.Program,
): EnvironmentSlotPlacementResult {
	const result: EnvironmentSlotPlacementResult = {
		analysed: 0,
		localized: 0,
		placed: 0,
		unresolved: 0,
		captured: 0,
		declarationsTagged: 0,
		textualDeclarationsUnresolved: 0,
	};
	const ownerBodies = new Map<number, t.Statement[]>([[0, root.body]]);
	const groups = new Map<string, SlotGroup>();

	const walk = (
		node: t.Node,
		owner: number,
		parent: t.Node | null,
	): void => {
		let currentOwner = owner;
		if (t.isFunction(node) && t.isBlockStatement(node.body)) {
			const functionId = (node.extra as LiftedExtra | undefined)
				?.parentFunctionId;
			if (functionId != null) {
				currentOwner = functionId;
				ownerBodies.set(functionId, node.body.body);
			}
		}
		if (t.isIdentifier(node)) {
			const location = locationOf(node);
			if (location?.kind === 'environment-slot') {
				const key = locationKey(location);
				const group = groups.get(key) ?? {
					location,
					names: new Set<string>(),
					assignmentCount: 0,
					referenceOwners: new Set<number>(),
				};
				group.names.add(node.name);
				if (
					parent &&
					((t.isAssignmentExpression(parent) &&
						parent.left === node) ||
						t.isUpdateExpression(parent) &&
							parent.argument === node)
				) group.assignmentCount++;
				if (parent && t.isReferenced(node, parent)) {
					group.referenceOwners.add(currentOwner);
				}
				groups.set(key, group);
			}
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const child of value) {
					if (t.isNode(child)) walk(child, currentOwner, node);
				}
			} else if (t.isNode(value)) walk(value, currentOwner, node);
		}
	};
	walk(root, 0, null);

	// IRFunction creates primary environment declarations before composition
	// knows their creation site. Bridge declarations anywhere in the tree onto
	// provenance only when one structured slot with the same generated spelling
	// exists. Do not require the declaration's current lexical owner to match the
	// site's owner: finding and repairing that exact misplacement is this pass's
	// job. The creation-site namespace makes legitimate names unique; an
	// ambiguous spelling remains textual and is reported.
	const bridgeTextualDeclarations = (node: t.Node): void => {
		if (t.isVariableDeclaration(node)) {
			for (const declarator of node.declarations) {
				if (
					!t.isIdentifier(declarator.id) ||
					!isEnvironmentSlotName(declarator.id.name) ||
					locationOf(declarator.id) != null
				) continue;
				const name = declarator.id.name;
				const matches = [...groups.values()].filter((group) =>
					group.names.has(name)
				);
				if (matches.length !== 1) {
					result.textualDeclarationsUnresolved++;
					continue;
				}
				tagStorageLocation(declarator.id, matches[0].location);
				result.declarationsTagged++;
			}
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const child of value) {
					if (t.isNode(child)) bridgeTextualDeclarations(child);
				}
			} else if (t.isNode(value)) bridgeTextualDeclarations(value);
		}
	};
	bridgeTextualDeclarations(root);

	const declarations = new Map<string, SlotDeclaration[]>();
	const collectDeclarations = (node: t.Node, body: t.Statement[]): void => {
		if (t.isVariableDeclaration(node)) {
			for (const declarator of node.declarations) {
				if (!t.isIdentifier(declarator.id)) continue;
				const location = locationOf(declarator.id);
				if (location?.kind !== 'environment-slot') continue;
				const key = locationKey(location);
				const found = declarations.get(key) ?? [];
				found.push({ declarator, declaration: node, body });
				declarations.set(key, found);
			}
		}
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				const statementBody = value.every((item) =>
						!t.isNode(item) ||
						t.isStatement(item)
					)
					? value as t.Statement[]
					: body;
				for (const child of value) {
					if (t.isNode(child)) {
						collectDeclarations(child, statementBody);
					}
				}
			} else if (t.isNode(value)) {
				collectDeclarations(
					value,
					t.isBlockStatement(value) ? value.body : body,
				);
			}
		}
	};
	collectDeclarations(root, root.body);

	for (const [key, group] of groups) {
		result.analysed++;
		if (
			group.referenceOwners.size > 1 ||
			!group.referenceOwners.has(group.location.environment.functionId) &&
				group.referenceOwners.size > 0
		) result.captured++;
		const targetBody = ownerBodies.get(
			group.location.environment.functionId,
		);
		const existing = declarations.get(key) ?? [];
		if (
			!targetBody ||
			(existing.length === 0 && group.assignmentCount === 0)
		) {
			result.unresolved++;
			continue;
		}
		if (existing.some((entry) => entry.declarator.init != null)) {
			// This pass runs before environment cleanup, so an initialized
			// declaration here is an unexpected ordering-sensitive shape.
			result.unresolved++;
			continue;
		}
		const direct = existing.find((entry) => entry.body === targetBody);
		if (existing.length === 1 && direct) {
			result.localized++;
			continue;
		}
		let kept = direct;
		if (!kept) {
			const id = tagStorageLocation(
				t.identifier([...group.names].toSorted()[0]),
				group.location,
			);
			const declaration = t.variableDeclaration('var', [
				t.variableDeclarator(id),
			]);
			targetBody.splice(
				directivePrologueLength(targetBody),
				0,
				declaration,
			);
			kept = {
				declarator: declaration.declarations[0],
				declaration,
				body: targetBody,
			};
		}
		for (const entry of existing) {
			if (entry === kept) continue;
			const index = entry.declaration.declarations.indexOf(
				entry.declarator,
			);
			if (index >= 0) entry.declaration.declarations.splice(index, 1);
		}
		result.placed++;
	}

	const sweep = (node: t.Node): void => {
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (let index = value.length - 1; index >= 0; index--) {
					const child = value[index];
					if (!t.isNode(child)) continue;
					if (
						t.isVariableDeclaration(child) &&
						child.declarations.length === 0
					) value.splice(index, 1);
					else sweep(child);
				}
			} else if (t.isNode(value)) sweep(value);
		}
	};
	sweep(root);
	return result;
}
