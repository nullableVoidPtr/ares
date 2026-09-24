import * as t from '@babel/types';
import { resolveIdentifierAlias } from '../iterator.ts';
import type { SSARegister } from '../../../../ssa.ts';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { CFGAnalyses, NaturalLoop } from '../algorithms/mod.ts';
import {
	type CFGDescriptors,
	iteratorCleanupRethrowRegister,
} from '../descriptors/mod.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import type { LoopSyntax } from '../regions/region.ts';

interface IntrinsicArrayDeclaration {
	index: number;
	destinations: t.Identifier[];
	call: t.CallExpression;
}

export function recoverIteratorLoopSyntax(
	loop: NaturalLoop,
	cfg: ImmutableCFG,
): LoopSyntax | undefined {
	return recoverForOfLoop(loop, cfg) ?? recoverForInLoop(loop, cfg) ??
		undefined;
}

/**
 * The `for...in` syntax of a property iteration with no backedge: the source
 * body always returns, throws, or breaks, so Hermes emits the full
 * `%GetPNameList`/`%GetNextPName` protocol for a graph that never loops and the
 * natural-loop forest has nothing to offer. The protocol itself is unchanged,
 * so the recovery is the ordinary one over a synthetic single-iteration loop.
 */
export function recoverSingleShotForInSyntax(
	header: BlockAddr,
	body: AddressSet<BlockAddr>,
	cfg: ImmutableCFG,
): LoopSyntax | undefined {
	const syntax = recoverForInLoop({
		id: -1,
		header,
		latches: [],
		body,
		backedges: [],
		exits: [],
		children: [],
	}, cfg);
	return syntax?.kind === 'forIn' ? syntax : undefined;
}

/**
 * The finally landing pad generated for `for...of` is represented by the loop
 * syntax itself. Its protected body may therefore recurse normally, but only
 * after matching the exact IteratorClose/rethrow protocol and the iterator
 * machine used by this loop. User-authored nested protected ranges remain
 * owned by their exception descriptors.
 */
export function iteratorCleanupHandlersForLoop(
	loop: NaturalLoop,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
): AddressSet<BlockAddr> {
	const syntax = recoverIteratorLoopSyntax(loop, cfg);
	if (
		syntax?.kind !== 'forOf' ||
		!descriptors.exceptions.iteratorCleanupActionElision
	) return new AddressSet<BlockAddr>();
	const handlers = new AddressSet<BlockAddr>();
	const machineNames = new Set([
		...(syntax.machineValues ?? []),
		...(syntax.internalValues ?? []),
	].map((identifier) => identifier.name));
	// The cleanup range can extend through a loop-exit trailer (for example the
	// successful callback path before the common continuation), so requiring its
	// whole protected set to be natural-loop blocks loses the generated landing
	// pad. Its protected entry must still open inside this exact iterator loop.
	for (const descriptor of descriptors.exceptions.handlers) {
		if (
			descriptor.protectedBlocks.size === 0 ||
			descriptor.protectedEntries.intersection(loop.body).size === 0
		) continue;
		const iterator = iteratorCleanupRethrowRegister(
			cfg.blocks.get(descriptor.handler)?.body ?? [],
		);
		if (iterator != null && machineNames.has(iterator)) {
			handlers.add(descriptor.handler);
		}
	}
	return handlers;
}

/**
 * Every cleanup landing pad a recovered `for...of` in this function subsumes.
 *
 * The Loop Region owns them: no other Region may, and the loop emits nothing
 * for them, because the syntax already carries the IteratorClose they perform.
 */
export function elidedIteratorCleanupHandlers(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
): AddressSet<BlockAddr> {
	const handlers = new AddressSet<BlockAddr>();
	for (const loop of analyses.naturalLoops.loops) {
		for (
			const handler of iteratorCleanupHandlersForLoop(
				loop,
				cfg,
				descriptors,
			)
		) handlers.add(handler);
	}
	return handlers;
}

function recoverForOfLoop(
	loop: NaturalLoop,
	cfg: ImmutableCFG,
): LoopSyntax | null {
	const header = cfg.blocks.get(loop.header);
	if (!header) return null;
	const next = findIntrinsicArrayDeclaration(header.body, 'IteratorNext');
	if (
		!next ||
		next.destinations.length !== 2 ||
		next.call.arguments.length !== 2
	) return null;
	const [value] = next.destinations;
	const [iteratorArg, sourceOrNextArg] = next.call.arguments;
	if (!t.isExpression(iteratorArg) || !t.isExpression(sourceOrNextArg)) {
		return null;
	}

	const aliases = headerAliasesBefore(header.body, next.index);
	const resolvedIteratorArg = resolveInitialPhiArg(
		resolveIdentifierAliasExpression(iteratorArg, aliases),
		header.body,
	);
	const resolvedSourceOrNextArg = resolveIdentifierAliasExpression(
		sourceOrNextArg,
		aliases,
	);
	const preheader = findLoopPreheaderIntrinsic(
		loop,
		cfg,
		'IteratorBegin',
		(begin) => {
			if (
				begin.destinations.length !== 2 ||
				begin.call.arguments.length !== 1
			) return false;
			const [iterator, sourceOrNext] = begin.destinations;
			return sameGeneratedRegister(resolvedIteratorArg, iterator.name) &&
				sameGeneratedRegister(
					resolvedSourceOrNextArg,
					sourceOrNext.name,
				);
		},
	);
	if (!preheader) return null;
	const [source] = preheader.decl.call.arguments;
	if (!t.isExpression(source)) return null;
	return {
		kind: 'forOf',
		header: loop.header,
		preheader: { block: preheader.block, statement: preheader.index },
		source: t.cloneNode(source, true),
		value: t.cloneNode(value),
		internalValues: [t.cloneNode(next.destinations[1]!)],
		machineValues: machineValueClosure(cfg, preheader.decl.destinations),
	};
}

function recoverForInLoop(
	loop: NaturalLoop,
	cfg: ImmutableCFG,
): LoopSyntax | null {
	const header = cfg.blocks.get(loop.header);
	if (!header) return null;
	const next = findIntrinsicArrayDeclaration(header.body, 'GetNextPName');
	if (
		!next ||
		next.destinations.length !== 2 ||
		next.call.arguments.length !== 3
	) return null;
	const [value] = next.destinations;
	const [listArg, _objectArg, indexArg] = next.call.arguments;
	if (!t.isExpression(listArg) || !t.isExpression(indexArg)) return null;
	const preheader = findLoopPreheaderIntrinsic(
		loop,
		cfg,
		'GetPNameList',
		(begin) => {
			if (
				begin.destinations.length !== 3 ||
				begin.call.arguments.length !== 1
			) return false;
			const [list, index] = begin.destinations;
			return sameGeneratedRegister(listArg, list.name) &&
				sameGeneratedRegister(indexArg, index.name);
		},
	);
	if (!preheader) return null;
	const [source] = preheader.decl.call.arguments;
	if (!t.isExpression(source)) return null;
	return {
		kind: 'forIn',
		header: loop.header,
		preheader: { block: preheader.block, statement: preheader.index },
		source: t.cloneNode(source, true),
		value: t.cloneNode(value),
		internalValues: [t.cloneNode(next.destinations[1]!)],
		machineValues: machineValueClosure(cfg, preheader.decl.destinations),
	};
}

/**
 * Every register that still holds an iterator-machine value the syntax
 * subsumes. The machine copies its iterator before closing it, and those copies
 * live on the exit paths as well as in the loop, so the preheader seeds are
 * closed over copies anywhere in the function and over Phis whose incoming
 * values are all machine values themselves.
 */
function machineValueClosure(
	cfg: ImmutableCFG,
	seeds: readonly t.Identifier[],
): t.Identifier[] {
	const names = new Set(seeds.map((seed) => seed.name));
	for (let changed = true; changed;) {
		changed = false;
		for (const block of cfg.blocks.values()) {
			for (const statement of block.body) {
				for (const copy of registerCopies(statement)) {
					if (
						!names.has(copy.from) || names.has(copy.to)
					) continue;
					names.add(copy.to);
					changed = true;
				}
			}
			for (const instruction of block.ssaInstructions) {
				if (instruction.instruction !== 'Phi') {
					// Register moves are coalesced away by lifting, so the copy
					// only exists in SSA.
					if (!instruction.instruction.startsWith('Mov')) continue;
					const move = instruction as unknown as {
						defs?: Record<string, SSARegister>;
						uses?: Record<string, SSARegister | SSARegister[]>;
					};
					const uses = Object.values(move.uses ?? {}).flat();
					if (!uses.some((use) => names.has(registerName(use)))) {
						continue;
					}
					for (const def of Object.values(move.defs ?? {})) {
						if (names.has(registerName(def))) continue;
						names.add(registerName(def));
						changed = true;
					}
					continue;
				}
				const destination = registerName(instruction.destination);
				const sources = [...instruction.sources.values()].map(
					registerName,
				);
				if (
					names.has(destination) || sources.length === 0 ||
					!sources.every((source) => names.has(source))
				) continue;
				names.add(destination);
				changed = true;
			}
		}
	}
	return [...names].map((name) => t.identifier(name));
}

/** `const a = b` and `a = b` between two registers. */
function registerCopies(
	statement: t.Statement,
): Array<{ to: string; from: string }> {
	if (t.isVariableDeclaration(statement)) {
		return statement.declarations.flatMap((declaration) =>
			t.isIdentifier(declaration.id) && t.isIdentifier(declaration.init)
				? [{ to: declaration.id.name, from: declaration.init.name }]
				: []
		);
	}
	if (
		t.isExpressionStatement(statement) &&
		t.isAssignmentExpression(statement.expression, { operator: '=' }) &&
		t.isIdentifier(statement.expression.left) &&
		t.isIdentifier(statement.expression.right)
	) {
		return [{
			to: statement.expression.left.name,
			from: statement.expression.right.name,
		}];
	}
	return [];
}

function registerName(register: SSARegister): string {
	return `r${register.index}_${register.version}`;
}

function findIntrinsicArrayDeclaration(
	statements: readonly t.Statement[],
	name: string,
): IntrinsicArrayDeclaration | null {
	for (let index = 0; index < statements.length; index++) {
		const stmt = statements[index];
		if (!t.isVariableDeclaration(stmt)) continue;
		if (stmt.declarations.length !== 1) continue;
		const [decl] = stmt.declarations;
		if (!t.isArrayPattern(decl.id)) continue;
		if (!t.isCallExpression(decl.init)) continue;
		if (!t.isV8IntrinsicIdentifier(decl.init.callee, { name })) continue;
		const destinations = decl.id.elements;
		if (!destinations.every(t.isIdentifier)) continue;
		return { index, destinations, call: decl.init };
	}
	return null;
}

function findLoopPreheaderIntrinsic(
	loop: NaturalLoop,
	cfg: ImmutableCFG,
	name: string,
	matches: (decl: IntrinsicArrayDeclaration) => boolean,
): { block: BlockAddr; index: number; decl: IntrinsicArrayDeclaration } | null {
	for (const predecessor of cfg.normalPredecessors.get(loop.header) ?? []) {
		if (loop.body.has(predecessor)) continue;
		const block = cfg.blocks.get(predecessor);
		if (!block) continue;
		const decl = findIntrinsicArrayDeclaration(block.body, name);
		if (!decl || !matches(decl)) continue;
		return { block: predecessor, index: decl.index, decl };
	}
	return null;
}

function sameGeneratedRegister(node: t.Node, name: string): boolean {
	if (!t.isIdentifier(node)) return false;
	if (node.name === name) return true;
	const left = /^r(\d+)_\d+$/.exec(node.name);
	const right = /^r(\d+)_\d+$/.exec(name);
	return !!left && !!right && left[1] === right[1];
}

function headerAliasesBefore(
	statements: readonly t.Statement[],
	end: number,
): Map<string, string> {
	const aliases = new Map<string, string>();
	for (let index = 0; index < end; index++) {
		const init = singleIdentifierInit(statements[index]);
		if (!init) continue;
		aliases.set(init.name, resolveIdentifierAlias(init.init, aliases));
	}
	return aliases;
}

function singleIdentifierInit(
	stmt: t.Statement | undefined,
): { name: string; init: string } | null {
	if (!stmt || !t.isVariableDeclaration(stmt)) return null;
	if (stmt.declarations.length !== 1) return null;
	const [decl] = stmt.declarations;
	if (!t.isIdentifier(decl.id) || !t.isIdentifier(decl.init)) return null;
	return { name: decl.id.name, init: decl.init.name };
}

function resolveIdentifierAliasExpression(
	expr: t.Expression,
	aliases: ReadonlyMap<string, string>,
): t.Expression {
	if (!t.isIdentifier(expr)) return expr;
	const resolved = resolveIdentifierAlias(expr.name, aliases);
	return resolved === expr.name ? expr : t.identifier(resolved);
}

function resolveInitialPhiArg(
	expr: t.Expression,
	statements: readonly t.Statement[],
): t.Expression {
	if (!t.isIdentifier(expr)) return expr;
	for (const stmt of statements) {
		if (!t.isVariableDeclaration(stmt)) continue;
		if (stmt.declarations.length !== 1) continue;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id, { name: expr.name })) continue;
		if (!t.isCallExpression(decl.init)) continue;
		if (!t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })) {
			continue;
		}
		for (const arg of decl.init.arguments) {
			if (!t.isExpression(arg)) continue;
			if (t.isIdentifier(arg, { name: expr.name })) continue;
			return arg;
		}
	}
	return expr;
}
