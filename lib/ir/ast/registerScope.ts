import * as t from '@babel/types';
import { isEnvironmentSlotName } from '../environment.ts';

export interface DuplicateRegisterScopeEvent {
	kind: 'body' | 'switch-case';
	context: string;
	name?: string;
	start?: number;
	end?: number;
	names: string[];
	caseIndex?: number;
}

export interface PreserveDuplicateRegisterScopeOptions {
	context?: string;
	onPreserve?: (event: DuplicateRegisterScopeEvent) => void;
	/** Names whose lifetime intentionally crosses sibling lexical scopes. */
	sharedNames?: ReadonlySet<string>;
}

export function isRegisterTempName(name: string): boolean {
	// `r<reg>_<version>` SSA temps and `_env_<funcId>_<slot>` environment registers.
	// Both can be reused across sibling scopes (e.g. two sequential loop counters), so
	// duplicate declarations of either in one block must be scoped/deduplicated.
	return /^r\d+_\d+$/.test(name) || isEnvironmentSlotName(name);
}

export function registerDeclarationName(stmt: t.Statement): string | null {
	if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
		return null;
	}
	const decl = stmt.declarations[0];
	if (
		!t.isVariableDeclarator(decl) ||
		!t.isIdentifier(decl.id) ||
		!isRegisterTempName(decl.id.name)
	) return null;
	return decl.id.name;
}

export function statementReferencesAny(
	stmt: t.Statement,
	names: Set<string>,
): boolean {
	let references = false;
	t.traverseFast(stmt, (node) => {
		if (references) return t.traverseFast.skip;
		if (t.isIdentifier(node) && names.has(node.name)) references = true;
	});
	return references;
}

function contextForChild(parent: string, child: string): string {
	return parent ? `${parent}.${child}` : child;
}

function preserveDuplicateSwitchCaseScopes(
	stmt: t.SwitchStatement,
	options: PreserveDuplicateRegisterScopeOptions,
): boolean {
	const counts = new Map<string, number>();
	for (const switchCase of stmt.cases) {
		for (const consequent of switchCase.consequent) {
			const name = registerDeclarationName(consequent);
			if (name && !options.sharedNames?.has(name)) {
				counts.set(name, (counts.get(name) ?? 0) + 1);
			}
		}
	}

	const duplicateNames = new Set(
		[...counts].filter(([, count]) => count > 1).map(([name]) => name),
	);
	if (duplicateNames.size === 0) return false;

	let changed = false;
	for (let i = 0; i < stmt.cases.length; i++) {
		const switchCase = stmt.cases[i];
		if (
			switchCase.consequent.length === 1 &&
			t.isBlockStatement(switchCase.consequent[0])
		) continue;
		const caseDuplicateNames = new Set<string>();
		for (const consequent of switchCase.consequent) {
			const name = registerDeclarationName(consequent);
			if (name && duplicateNames.has(name)) caseDuplicateNames.add(name);
		}
		if (caseDuplicateNames.size === 0) continue;

		switchCase.consequent = [
			t.blockStatement(switchCase.consequent),
		];
		options.onPreserve?.({
			kind: 'switch-case',
			context: options.context ?? 'body',
			names: [...caseDuplicateNames].toSorted(),
			caseIndex: i,
		});
		changed = true;
	}

	return changed;
}

export function preserveDuplicateRegisterScopesInBody(
	body: t.Statement[],
	options: PreserveDuplicateRegisterScopeOptions = {},
): boolean {
	let changed = false;
	const context = options.context ?? 'body';
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (t.isBlockStatement(stmt)) {
			changed = preserveDuplicateRegisterScopesInBody(stmt.body, {
				...options,
				context: contextForChild(context, `block@${i}`),
			}) || changed;
		} else if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = preserveDuplicateRegisterScopesInBody(
					stmt.consequent.body,
					{
						...options,
						context: contextForChild(context, `if@${i}.consequent`),
					},
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = preserveDuplicateRegisterScopesInBody(
					stmt.alternate.body,
					{
						...options,
						context: contextForChild(context, `if@${i}.alternate`),
					},
				) || changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isDoWhileStatement(stmt) ||
				t.isForStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = preserveDuplicateRegisterScopesInBody(stmt.body.body, {
				...options,
				context: contextForChild(context, `${stmt.type}@${i}.body`),
			}) || changed;
		} else if (t.isTryStatement(stmt)) {
			changed = preserveDuplicateRegisterScopesInBody(stmt.block.body, {
				...options,
				context: contextForChild(context, `try@${i}.block`),
			}) || changed;
			if (stmt.handler) {
				changed = preserveDuplicateRegisterScopesInBody(
					stmt.handler.body.body,
					{
						...options,
						context: contextForChild(context, `try@${i}.catch`),
					},
				) || changed;
			}
			if (stmt.finalizer) {
				changed = preserveDuplicateRegisterScopesInBody(
					stmt.finalizer.body,
					{
						...options,
						context: contextForChild(context, `try@${i}.finally`),
					},
				) || changed;
			}
		} else if (t.isSwitchStatement(stmt)) {
			changed = preserveDuplicateSwitchCaseScopes(stmt, {
				...options,
				context: contextForChild(context, `switch@${i}`),
			}) || changed;
			for (
				let caseIndex = 0;
				caseIndex < stmt.cases.length;
				caseIndex++
			) {
				changed = preserveDuplicateRegisterScopesInBody(
					stmt.cases[caseIndex].consequent,
					{
						...options,
						context: contextForChild(
							context,
							`switch@${i}.case@${caseIndex}`,
						),
					},
				) || changed;
			}
		}
	}

	const declared = new Set<string>();
	for (let i = 0; i < body.length; i++) {
		const name = registerDeclarationName(body[i]);
		if (!name || options.sharedNames?.has(name)) continue;
		if (!declared.has(name)) {
			declared.add(name);
			continue;
		}

		const segmentNames = new Set<string>([name]);
		let end = i + 1;
		while (end < body.length) {
			const next = body[end];
			const nextName = registerDeclarationName(next);
			if (nextName) {
				const refsExisting = statementReferencesAny(next, segmentNames);
				if (!refsExisting && !declared.has(nextName)) break;
				segmentNames.add(nextName);
				end++;
				continue;
			}
			if (!statementReferencesAny(next, segmentNames)) break;
			end++;
		}

		body.splice(i, end - i, t.blockStatement(body.slice(i, end)));
		options.onPreserve?.({
			kind: 'body',
			context,
			name,
			start: i,
			end,
			names: [...segmentNames].toSorted(),
		});
		changed = true;
		i++;
	}
	return changed;
}
