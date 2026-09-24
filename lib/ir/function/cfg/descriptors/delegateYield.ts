import * as t from '@babel/types';
import traverse from '@babel/traverse';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import {
	type DelegateIteratorAcquisition,
	findDelegateIteratorAcquisition,
} from '../delegateYield.ts';
import type { CFGAnalyses, NaturalLoop } from '../algorithms/mod.ts';
import type { CFGBlock, ImmutableCFG } from '../immutableCFG.ts';

const DEBUG_DELEGATE_DESCRIPTOR = (() => {
	try {
		return Deno.env.get('ARES_DEBUG_DELEGATE_DESCRIPTOR') === '1';
	} catch {
		return false;
	}
})();

export interface DelegateYieldDescriptor {
	prelude: BlockAddr;
	header: BlockAddr;
	normalExit: BlockAddr;
	argument: t.Expression;
	preludeStatements?: t.Statement[];
	sourceBlocks: AddressSet<BlockAddr>;
	completion: 'discarded' | 'assigned';
	// For `completion: 'assigned'`, the temp the delegate's completion value binds to
	// (`x` in `x = yield* g()`); emitted as `<target> = yield* arg`.
	completionTarget?: t.Identifier;
	// Genuine statements from the normal-exit block that follow the completion
	// extraction (continuation code after `yield* x;`), or undefined if none.
	trailing?: t.Statement[];
	// Set when the normal-exit block is shared with enclosing control flow (it
	// ends in a branch the delegate cannot own). The block stays with the
	// structurer; only its leading completion-extraction statements belong to
	// the delegate and are suppressed at emission.
	completionSkip?: { block: BlockAddr; start: number; end: number };
	// With `completionSkip`, the completion target's own declaration is one of
	// the suppressed statements, so the `yield*` must re-declare it.
	declaresCompletionTarget?: boolean;
	// Set when the prelude block belongs to enclosing control flow — it is the
	// header of the loop the `yield*` sits in, so the loop Region owns it. The
	// delegate is then opened at its machine header instead, and the statements
	// this range names (the iterator acquisition) are suppressed in the prelude.
	preludeSkip?: { block: BlockAddr; statements: number[] };
}

export interface DelegateYieldDescriptorInfo {
	delegates: DelegateYieldDescriptor[];
	delegateByPrelude: AddressMap<DelegateYieldDescriptor>;
	/** Delegates whose prelude block is owned by an enclosing loop Region. */
	delegateByHeader: AddressMap<DelegateYieldDescriptor>;
}

export function recoverDelegateYieldDescriptors(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
): DelegateYieldDescriptorInfo {
	const delegates: DelegateYieldDescriptor[] = [];
	const delegateByPrelude = new AddressMap<DelegateYieldDescriptor>();
	const delegateByHeader = new AddressMap<DelegateYieldDescriptor>();

	for (const loop of analyses.naturalLoops.loops) {
		const descriptor = recoverLoopDelegateYield(cfg, analyses, loop);
		if (!descriptor) continue;
		delegates.push(descriptor);
		if (descriptor.preludeSkip) {
			delegateByHeader.set(descriptor.header, descriptor);
		} else {
			delegateByPrelude.set(descriptor.prelude, descriptor);
		}
	}

	return { delegates, delegateByPrelude, delegateByHeader };
}

function recoverLoopDelegateYield(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	loop: NaturalLoop,
): DelegateYieldDescriptor | null {
	const fail = (reason: string) => {
		debugDelegateDescriptor(
			`loop 0x${loop.header.toString(16)} rejected: ${reason}`,
		);
		return null;
	};
	if (loop.exits.length !== 1) return fail(`exit-count=${loop.exits.length}`);
	const [exit] = loop.exits;
	if (exit.from !== loop.header) {
		return fail(`exit-from=0x${exit.from.toString(16)}`);
	}

	const preludeMatch = uniquePreludeWithAcquisition(cfg, loop);
	if (!preludeMatch) return fail('no-unique-acquisition-prelude');
	const { prelude, acquisition } = preludeMatch;
	const preludeBlock = cfg.blocks.get(prelude);
	if (!preludeBlock) return fail('missing-prelude');
	const argument = normalizeDelegateArgument(
		acquisition.argument,
		preludeBlock,
	);
	if (
		!isSafeDelegateArgument(argument) &&
		!isClosureCallDelegateArgument(argument, cfg) &&
		!isInlineClosureCallDelegateArgument(argument) &&
		!isStableLocalObjectArgument(argument, cfg)
	) {
		return fail(`unsafe-argument:${expressionShape(argument)}`);
	}

	const headerBlock = cfg.blocks.get(loop.header);
	const nextName = headerBlock
		? delegateNextResultName(headerBlock, acquisition.iteratorName)
		: null;
	if (!headerBlock || !nextName || !blockTestsDone(headerBlock, nextName)) {
		return fail('header-shape');
	}
	if (!loopHasDelegateYieldBody(cfg, loop, acquisition.iteratorName)) {
		return fail('body-shape');
	}

	const exitBlock = cfg.blocks.get(exit.to);
	const carriedCompletionName = delegateCarriedCompletionName(
		headerBlock,
		nextName,
	);
	// The machine's own blocks first: the completion analysis needs them to tell
	// a second delegate-side entry of the exit block (the throw path's own
	// completion) from an entry belonging to enclosing control flow.
	const sourceBlocks = collectDelegateLoopBlocks(cfg, prelude, loop, exit.to);
	// Absorb only iterator-close machinery owned by the delegate protocol. A
	// delegate loop may sit inside user try/catch/finally; those enclosing handlers
	// have protected predecessors outside the loop and must remain around the
	// emitted `yield*`.
	for (const block of loop.body) {
		for (const handler of cfg.exceptionalSuccessors.get(block) ?? []) {
			if (!handlerIsProtectedOnlyByLoop(cfg, handler, loop.body)) {
				continue;
			}
			absorbDelegateHandlerBlocks(
				cfg,
				sourceBlocks,
				handler,
				loop.body,
				exit.to,
			);
		}
	}
	const completion = exitBlock
		? analyzeCompletionExit(exitBlock, carriedCompletionName) ??
			analyzeSharedCompletionExit(
				cfg,
				exitBlock,
				sourceBlocks,
				carriedCompletionName,
			)
		: null;
	if (!completion) {
		if (exitBlock) {
			debugDelegateDescriptor(
				`completion block 0x${exit.to.toString(16)} body=${
					exitBlock.body.map(statementShape).join(',')
				} terminator=${exitBlock.terminator.kind}`,
			);
		}
		return fail('completion-exit');
	}
	if (completion.skip == null) sourceBlocks.add(exit.to);
	// A prelude that is also a loop header belongs to that loop's Region: it
	// carries the loop's own header statements and its branch. The delegate then
	// starts at its machine header and suppresses only the acquisition.
	const consumedPrelude = delegateConsumedPreludeIndices(
		preludeBlock,
		acquisition,
	);
	const sharedPrelude = analyses.naturalLoops.loopByHeader.has(prelude);
	if (sharedPrelude) sourceBlocks.delete(prelude);

	return {
		prelude,
		header: loop.header,
		normalExit: exit.to,
		argument: t.cloneNode(argument, true),
		preludeStatements: sharedPrelude
			? undefined
			: delegatePreludeStatements(
				preludeBlock,
				acquisition,
				consumedPrelude,
			),
		sourceBlocks,
		completion: completion.kind,
		completionTarget: completion.target,
		trailing: completion.trailing.length > 0
			? completion.trailing
			: undefined,
		completionSkip: completion.skip == null ? undefined : {
			block: exit.to,
			start: 0,
			end: completion.skip,
		},
		declaresCompletionTarget: completion.skip != null &&
				completion.target != null
			? true
			: undefined,
		preludeSkip: sharedPrelude
			? { block: prelude, statements: consumedPrelude }
			: undefined,
	};
}

function handlerIsProtectedOnlyByLoop(
	cfg: ImmutableCFG,
	handler: BlockAddr,
	loopBody: ReadonlySet<BlockAddr>,
) {
	const predecessors = cfg.exceptionalPredecessors.get(handler);
	return predecessors != null && predecessors.size > 0 &&
		[...predecessors].every((predecessor) => loopBody.has(predecessor));
}

function absorbDelegateHandlerBlocks(
	cfg: ImmutableCFG,
	sourceBlocks: AddressSet<BlockAddr>,
	handler: BlockAddr,
	loopBody: ReadonlySet<BlockAddr>,
	normalExit: BlockAddr,
) {
	const stack = [handler];
	while (stack.length > 0) {
		const block = stack.pop()!;
		if (sourceBlocks.has(block)) continue;
		sourceBlocks.add(block);
		for (const successor of cfg.normalSuccessors.get(block) ?? []) {
			if (successor === normalExit || loopBody.has(successor)) continue;
			stack.push(successor);
		}
	}
}

/**
 * Prelude statement indices the `yield*` represents: the acquisition sequence
 * itself and the temps feeding it.
 *
 * The lowered sequence evaluates `iterable[Symbol.iterator]` before invoking
 * the method through `.call(iterable)`. Once the whole sequence becomes
 * `yield* iterable`, retaining that lookup evaluates the iterator protocol
 * twice and can reference an SSA temporary whose declaration was consumed
 * while resolving `iterable`. It is part of the acquisition, not a
 * source-level prelude statement.
 */
function delegateConsumedPreludeIndices(
	block: CFGBlock,
	acquisition: DelegateIteratorAcquisition,
): number[] {
	if (DEBUG_DELEGATE_DESCRIPTOR) {
		debugDelegateDescriptor(
			`prelude 0x${
				block.address.toString(16)
			} acquisition=${acquisition.index}` +
				` consumed=${[...acquisition.consumedNames].join(',')}` +
				` body=${block.body.map(statementShape).join(',')}`,
		);
	}
	const consumed: number[] = [];
	for (let index = 0; index < block.body.length; index++) {
		if (index >= acquisition.index) {
			consumed.push(index);
			continue;
		}
		const stmt = block.body[index];
		const decl = singleDeclarator(stmt);
		if (
			decl && t.isIdentifier(decl.id) &&
			acquisition.consumedNames.has(decl.id.name)
		) {
			consumed.push(index);
			continue;
		}
		if (
			t.isExpressionStatement(stmt) &&
			t.isMemberExpression(stmt.expression) &&
			memberRootIsConsumed(stmt.expression, acquisition.consumedNames)
		) consumed.push(index);
	}
	return consumed;
}

function delegatePreludeStatements(
	block: CFGBlock,
	acquisition: DelegateIteratorAcquisition,
	consumed: readonly number[],
): t.Statement[] | undefined {
	const consumedIndices = new Set(consumed);
	const statements = block.body
		.slice(0, acquisition.index)
		.filter((_, index) => !consumedIndices.has(index))
		.map((stmt) => t.cloneNode(stmt, true));
	return statements.length > 0 ? statements : undefined;
}

function memberRootIsConsumed(
	member: t.MemberExpression,
	consumedNames: Set<string>,
): boolean {
	let object: t.Expression | t.Super = member.object;
	while (t.isMemberExpression(object)) object = object.object;
	return t.isIdentifier(object) && consumedNames.has(object.name);
}

function normalizeDelegateArgument(
	expr: t.Expression,
	prelude: CFGBlock,
): t.Expression {
	const aliases = new Map<string, t.Expression>();
	for (const stmt of prelude.body) {
		const decl = singleDeclarator(stmt);
		if (
			decl &&
			t.isIdentifier(decl.id) &&
			t.isExpression(decl.init)
		) {
			aliases.set(decl.id.name, decl.init);
		}
	}
	const normalize = (
		node: t.Expression,
		seen = new Set<string>(),
	): t.Expression => {
		if (t.isIdentifier(node)) {
			if (node.name === 'global') return t.cloneNode(node, true);
			if (seen.has(node.name)) return t.cloneNode(node, true);
			const init = aliases.get(node.name);
			if (t.isIdentifier(init, { name: 'global' })) {
				return t.identifier('global');
			}
			if (init && isLiteralLikeDelegateArgument(init)) {
				return t.cloneNode(init, true);
			}
			return t.cloneNode(node, true);
		}
		if (t.isMemberExpression(node) && t.isExpression(node.object)) {
			return t.memberExpression(
				normalize(node.object, seen),
				t.cloneNode(node.property, true),
				node.computed,
			);
		}
		// Resolve temp roots inside a call's callee/arguments too, so an iterable like
		// `r2_1.func1()` (where `r2_1` aliases `global`) normalizes to `global.func1()`.
		if (t.isCallExpression(node) && t.isExpression(node.callee)) {
			return t.callExpression(
				normalize(node.callee, seen),
				node.arguments.map((
					arg: t.CallExpression['arguments'][number],
				) => t.isExpression(arg)
					? normalize(arg, seen)
					: t.cloneNode(arg, true)
				),
			);
		}
		return t.cloneNode(node, true);
	};
	return normalize(expr);
}

function isSafeDelegateArgument(expr: t.Expression): boolean {
	if (t.isArrayExpression(expr)) return true;
	if (t.isMemberExpression(expr)) return !memberExpressionUsesTempRoot(expr);
	if (t.isCallExpression(expr)) return !callExpressionUsesTempRoot(expr);
	return false;
}

// Accept `iterable()` where the callee is a temp holding a closure creation defined
// somewhere in the function (e.g. `const r2_1 = %CreateGeneratorClosure(...)` before a
// `try { yield* r2_1(); }`). The temp survives the delegate blocks, and closure inlining
// later rewrites it to the inline `function*(){…}()` form.
function isClosureCallDelegateArgument(
	expr: t.Expression,
	cfg: ImmutableCFG,
): boolean {
	if (!t.isCallExpression(expr)) return false;
	if (!t.isIdentifier(expr.callee)) return false;
	const name = expr.callee.name;
	if (!/^r\d+_\d+$/.test(name)) return false;
	for (const block of cfg.blocks.values()) {
		for (const stmt of block.body) {
			const decl = singleDeclarator(stmt);
			if (
				decl && t.isIdentifier(decl.id, { name }) &&
				t.isCallExpression(decl.init) &&
				t.isV8IntrinsicIdentifier(decl.init.callee) &&
				(decl.init.callee.name === 'CreateClosure' ||
					decl.init.callee.name === 'CreateGeneratorClosure' ||
					decl.init.callee.name === 'CreateAsyncClosure')
			) return true;
		}
	}
	return false;
}

function isStableLocalObjectArgument(
	expr: t.Expression,
	cfg: ImmutableCFG,
): boolean {
	if (!t.isIdentifier(expr) || !/^r\d+_\d+$/.test(expr.name)) return false;
	let definitionCount = 0;
	for (const block of cfg.blocks.values()) {
		for (const stmt of block.body) {
			const decl = singleDeclarator(stmt);
			if (decl && t.isIdentifier(decl.id, { name: expr.name })) {
				if (!t.isObjectExpression(decl.init)) return false;

				definitionCount++;
			}
			let reassigned = false;
			t.traverseFast(stmt, (node) => {
				if (
					t.isAssignmentExpression(node) &&
					t.isIdentifier(node.left, { name: expr.name })
				) reassigned = true;
			});
			if (reassigned) return false;
		}
	}
	return definitionCount === 1;
}
function isInlineClosureCallDelegateArgument(expr: t.Expression): boolean {
	if (!t.isCallExpression(expr)) return false;
	const callee = expr.callee;
	return t.isCallExpression(callee) &&
		t.isV8IntrinsicIdentifier(callee.callee) &&
		[
			'CreateClosure',
			'CreateGeneratorClosure',
			'CreateAsyncClosure',
		].includes(callee.callee.name);
}

function isLiteralLikeDelegateArgument(expr: t.Expression): boolean {
	return t.isArrayExpression(expr) ||
		t.isStringLiteral(expr) ||
		t.isNumericLiteral(expr) ||
		t.isBooleanLiteral(expr) ||
		t.isNullLiteral(expr);
}

function memberExpressionUsesTempRoot(expr: t.MemberExpression): boolean {
	let object: t.Expression | t.Super = expr.object;
	while (t.isMemberExpression(object)) object = object.object;
	return t.isIdentifier(object) && /^r\d+_\d+$/.test(object.name);
}

function callExpressionUsesTempRoot(expr: t.CallExpression): boolean {
	const callee = expr.callee;
	if (t.isIdentifier(callee)) return /^r\d+_\d+$/.test(callee.name);
	if (t.isMemberExpression(callee)) {
		return memberExpressionUsesTempRoot(callee);
	}
	return true;
}

function debugDelegateDescriptor(message: string) {
	if (DEBUG_DELEGATE_DESCRIPTOR) {
		console.error(`[delegate-yield-descriptor] ${message}`);
	}
}

function statementShape(stmt: t.Statement): string {
	if (t.isVariableDeclaration(stmt)) {
		const decl = singleDeclarator(stmt);
		return `var:${t.isIdentifier(decl?.id) ? decl.id.name : '?'}:${
			expressionShape(decl?.init)
		}`;
	}
	return stmt.type;
}

function expressionShape(expr: t.Expression | null | undefined): string {
	if (!expr) return '<none>';
	if (t.isCallExpression(expr)) {
		if (t.isV8IntrinsicIdentifier(expr.callee)) {
			return `CallExpression:%${expr.callee.name}`;
		}
		if (
			t.isMemberExpression(expr.callee) &&
			t.isIdentifier(expr.callee.object) &&
			t.isIdentifier(expr.callee.property)
		) {
			return `CallExpression:${expr.callee.object.name}.${expr.callee.property.name}`;
		}
	}
	return expr.type;
}

function uniquePreludeWithAcquisition(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
): { prelude: BlockAddr; acquisition: DelegateIteratorAcquisition } | null {
	const matches = [...(cfg.normalPredecessors.get(loop.header) ?? [])]
		.filter((pred) => !loop.body.has(pred))
		.flatMap((pred) => {
			const block = cfg.blocks.get(pred);
			if (!block) return [];
			const acquisition = findDelegateIteratorAcquisition([
				...block.body,
			]);
			return acquisition ? [{ prelude: pred, acquisition }] : [];
		});
	return matches.length === 1 ? matches[0] : null;
}

/**
 * The delegate machine's own blocks, excluding the normal-exit block: whether
 * the delegate owns that block depends on how its completion is consumed, and
 * the caller adds it once that is known.
 */
function collectDelegateLoopBlocks(
	cfg: ImmutableCFG,
	prelude: BlockAddr,
	loop: NaturalLoop,
	normalExit: BlockAddr,
): AddressSet<BlockAddr> {
	const blocks = new AddressSet<BlockAddr>([prelude]);
	const stack = [loop.header];
	while (stack.length > 0) {
		const addr = stack.pop()!;
		if (blocks.has(addr) || addr === normalExit) continue;
		// Stay within the natural loop (plus its prelude/exit). Following exceptional
		// successors here would escape into an enclosing user try/catch/finally that
		// merely wraps the `yield*`, wrongly consuming it.
		if (addr !== loop.header && !loop.body.has(addr)) continue;
		blocks.add(addr);
		for (const succ of cfg.normalSuccessors.get(addr) ?? []) {
			if (succ === normalExit) continue;
			stack.push(succ);
		}
		for (const handler of cfg.exceptionalSuccessors.get(addr) ?? []) {
			if (loop.body.has(handler)) stack.push(handler);
		}
	}
	return blocks;
}

function matchesDelegateHeader(
	block: CFGBlock,
	acquisition: DelegateIteratorAcquisition,
): boolean {
	if (block.terminator.kind !== 'if') return false;
	const nextName = delegateNextResultName(block, acquisition.iteratorName);
	if (!nextName) return false;
	return blockTestsDone(block, nextName);
}

function delegateNextResultName(
	block: CFGBlock,
	iteratorName: string,
): string | null {
	for (const stmt of block.body) {
		const decl = singleDeclarator(stmt);
		if (
			decl &&
			t.isIdentifier(decl.id) &&
			t.isCallExpression(decl.init) &&
			isIteratorNextCallWithReceiver(decl.init, iteratorName)
		) {
			return decl.id.name;
		}
	}
	return null;
}

function delegateCarriedCompletionName(
	block: CFGBlock,
	nextName: string,
): string | null {
	for (const stmt of block.body) {
		if (!t.isExpressionStatement(stmt)) continue;
		const expr = stmt.expression;
		if (
			t.isAssignmentExpression(expr, { operator: '=' }) &&
			t.isIdentifier(expr.left) &&
			t.isIdentifier(expr.right, { name: nextName })
		) return expr.left.name;
	}
	return null;
}

function isIteratorNextCallWithReceiver(
	expr: t.CallExpression,
	iteratorName: string,
): boolean {
	const callee = expr.callee;
	if (
		t.isMemberExpression(callee) &&
		memberName(callee) === 'call' &&
		expr.arguments.length >= 1 &&
		t.isIdentifier(expr.arguments[0], { name: iteratorName })
	) return true;
	return t.isMemberExpression(callee) &&
		t.isIdentifier(callee.object, { name: iteratorName }) &&
		memberName(callee) === 'next';
}

function blockTestsDone(block: CFGBlock, nextName: string): boolean {
	if (block.terminator.kind !== 'if') return false;
	const test = block.terminator.test;
	if (
		t.isMemberExpression(test) &&
		t.isIdentifier(test.object, { name: nextName }) &&
		memberName(test) === 'done'
	) return true;
	if (!t.isIdentifier(test)) return false;
	for (const stmt of block.body) {
		const decl = singleDeclarator(stmt);
		if (
			decl &&
			t.isIdentifier(decl.id, { name: test.name }) &&
			t.isMemberExpression(decl.init) &&
			t.isIdentifier(decl.init.object, { name: nextName }) &&
			memberName(decl.init) === 'done'
		) return true;
	}
	return false;
}

function loopHasDelegateYieldBody(
	cfg: ImmutableCFG,
	loop: NaturalLoop,
	iteratorName: string,
): boolean {
	for (const blockAddr of loop.body) {
		if (blockAddr === loop.header) continue;
		const block = cfg.blocks.get(blockAddr);
		if (!block) continue;
		if (
			block.body.some((stmt) => isGeneratorSetDelegated(stmt)) &&
			block.body.some((stmt) => isYieldedIteratorResult(stmt))
		) return true;
	}
	for (const blockAddr of loop.body) {
		const block = cfg.blocks.get(blockAddr);
		if (!block) continue;
		if (
			block.body.some((stmt) =>
				t.isExpressionStatement(stmt) &&
				t.isCallExpression(stmt.expression) &&
				isIteratorNextCallWithReceiver(stmt.expression, iteratorName)
			)
		) return true;
	}
	return false;
}

function isGeneratorSetDelegated(stmt: t.Statement): boolean {
	const expr = statementExpression(stmt);
	if (!t.isCallExpression(expr)) return false;
	const callee = expr.callee;
	return t.isMemberExpression(callee) &&
		t.isIdentifier(callee.object, { name: 'HermesInternal' }) &&
		memberName(callee) === 'generatorSetDelegated';
}

function isYieldedIteratorResult(stmt: t.Statement): boolean {
	const expr = statementExpression(stmt);
	if (t.isYieldExpression(expr, { delegate: false })) return true;
	return t.isAssignmentExpression(expr, { operator: '=' }) &&
		t.isYieldExpression(expr.right, { delegate: false });
}

function statementExpression(stmt: t.Statement): t.Expression | null {
	if (t.isExpressionStatement(stmt)) return stmt.expression;
	const decl = singleDeclarator(stmt);
	return t.isExpression(decl?.init) ? decl.init : null;
}

// A delegate loop's normal-exit block extracts the (discarded) completion value and may
// then run genuine continuation code (statements after `yield* x;`). Split it: the leading
// completion-extraction statements (which reference only the loop's completion temps) are
// dropped; the remainder is returned as `trailing`. Returns null when the block isn't a
// return-terminated discarded-completion exit, or when the continuation reads a discarded
// completion temp (that is a USED completion — handled elsewhere).
interface CompletionAnalysis {
	kind: 'discarded' | 'assigned';
	// For 'assigned': the temp the delegate's completion value is bound to (`x` in
	// `x = yield* g()`). The continuation reads it.
	target?: t.Identifier;
	trailing: t.Statement[];
	// Number of leading statements of the exit block the delegate consumed, set
	// only when the block stays with the structurer (see `completionSkip`).
	skip?: number;
}

interface CompletionPrefix {
	/** First statement index past the completion extraction. */
	index: number;
	completionTemps: Set<string>;
	valueTemp: string | null;
}

/**
 * Leading statements that only read the loop's completion temps.
 *
 * `carried` names the register the header already bound the delegate's result
 * to. Passing it accepts an exit block whose extraction reads that register
 * (`const v = <carried>.value`) rather than re-deriving the result locally,
 * which is the shape left once Phi lowering hoists the result register.
 */
function splitCompletionPrefix(
	block: CFGBlock,
	carried?: string | null,
): CompletionPrefix {
	const completionTemps = new Set<string>(carried == null ? [] : [carried]);
	let valueTemp: string | null = null;
	let index = 0;
	for (; index < block.body.length; index++) {
		const stmt = block.body[index];
		if (index === block.body.length - 1 && t.isReturnStatement(stmt)) break;
		const decl = singleDeclarator(stmt);
		if (!decl || !t.isIdentifier(decl.id)) break;
		const init = decl.init;
		if (init == null || isUndefinedNode(init)) {
			completionTemps.add(decl.id.name);
			continue;
		}
		if (isGeneratorCompletionInit(init)) {
			completionTemps.add(decl.id.name);
			continue;
		}
		if (
			t.isMemberExpression(init) &&
			memberName(init) === 'value' &&
			((t.isIdentifier(init.object) &&
				completionTemps.has(init.object.name)) ||
				(t.isExpression(init.object) &&
					isGeneratorCompletionInit(init.object)))
		) {
			completionTemps.add(decl.id.name);
			valueTemp = decl.id.name;
			continue;
		}
		break;
	}
	return { index, completionTemps, valueTemp };
}

/**
 * A delegate whose completion block ends in a branch: the `yield*` sits inside
 * enclosing control flow, so its normal-exit block is that flow's own join or
 * latch (`while (…) { x = yield* g(); if (x) … }`). The delegate cannot own a
 * block it does not terminate, so the block stays with the structurer and only
 * its leading completion extraction is attributed to the delegate.
 *
 * Sound only when the delegate is the block's single normal entry — otherwise a
 * second predecessor would reach statements the `yield*` is supposed to bind —
 * and when the surviving statements read no completion temp other than the
 * completion value itself, which the `yield*` re-declares.
 */
function analyzeSharedCompletionExit(
	cfg: ImmutableCFG,
	block: CFGBlock,
	machineBlocks: AddressSet<BlockAddr>,
	carriedCompletionName: string | null,
): CompletionAnalysis | null {
	const decline = (reason: string) => {
		debugDelegateDescriptor(
			`shared completion 0x${block.address.toString(16)}: ${reason}`,
		);
		return null;
	};
	if (block.terminator.kind !== 'if') {
		return decline(`terminator=${block.terminator.kind}`);
	}
	for (const predecessor of cfg.normalPredecessors.get(block.address) ?? []) {
		if (!machineBlocks.has(predecessor)) {
			return decline(`predecessor=0x${predecessor.toString(16)}`);
		}
	}
	const { index, completionTemps, valueTemp } = splitCompletionPrefix(
		block,
		carriedCompletionName,
	);
	if (index === 0 || completionTemps.size === 0) {
		return decline(
			`prefix=${index} temps=${completionTemps.size} body=${
				block.body.map(statementShape).join(',')
			}`,
		);
	}
	const survivors: t.Node[] = [
		...block.body.slice(index),
		block.terminator.test,
	];
	const readable = valueTemp == null ? new Set<string>() : new Set([
		valueTemp,
	]);
	let readsValue = false;
	for (const node of survivors) {
		for (const name of readCompletionTempNames(node, completionTemps)) {
			if (!readable.has(name)) return decline(`survivor-reads=${name}`);
			readsValue = true;
		}
	}
	return readsValue && valueTemp != null
		? {
			kind: 'assigned',
			target: t.identifier(valueTemp),
			trailing: [],
			skip: index,
		}
		: { kind: 'discarded', trailing: [], skip: index };
}

/**
 * Completion temps a node reads. A `<temp>.value` read counts as a read of the
 * temp itself: rewriting it into the completion value is only available for a
 * block the delegate owns.
 */
function readCompletionTempNames(
	node: t.Node,
	completionTemps: ReadonlySet<string>,
): Set<string> {
	const names = new Set<string>();
	t.traverseFast(node, (child) => {
		if (t.isIdentifier(child) && completionTemps.has(child.name)) {
			names.add(child.name);
		}
	});
	return names;
}

// A delegate loop's normal-exit block extracts the completion value (`%Phi(...).value`)
// and either discards it (return-terminated) or lets it flow to a continuation
// (goto-terminated — a used `x = yield* g()` completion). Classify it and return any
// genuine trailing statements. Returns null when the block isn't a recognizable exit.
function analyzeCompletionExit(
	block: CFGBlock,
	carriedCompletionName: string | null,
): CompletionAnalysis | null {
	if (
		block.terminator.kind !== 'return' && block.terminator.kind !== 'goto'
	) {
		return null;
	}
	const { index, completionTemps, valueTemp } = splitCompletionPrefix(block);
	const rest = block.body.slice(index);

	if (block.terminator.kind === 'goto') {
		if (valueTemp != null) {
			const rewritten = rewriteCompletionReads(
				rest,
				completionTemps,
				valueTemp,
			);
			if (!rewritten) return null;
			return {
				kind: 'assigned',
				target: t.identifier(valueTemp),
				trailing: rewritten.statements,
			};
		}
		if (carriedCompletionName != null) {
			const rewritten = rewriteCarriedCompletionReads(
				rest,
				carriedCompletionName,
			);
			if (rewritten?.used) {
				return {
					kind: 'assigned',
					target: t.identifier(carriedCompletionName),
					trailing: rewritten.statements,
				};
			}
		}
		return null;
	}

	// Return-terminated exit: discarded completion, with optional genuine continuation.
	const declared = new Set<string>();
	for (const stmt of rest) {
		const decl = singleDeclarator(stmt);
		if (decl && t.isIdentifier(decl.id)) declared.add(decl.id.name);
	}
	const trailing = rest.filter((stmt, index, all) => {
		if (index !== all.length - 1 || !t.isReturnStatement(stmt)) return true;
		const arg = stmt.argument;
		if (arg == null || isUndefinedNode(arg)) return false;
		if (t.isIdentifier(arg) && !declared.has(arg.name)) return false;
		return true;
	});
	if (valueTemp != null) {
		const rewritten = rewriteCompletionReads(
			trailing,
			completionTemps,
			valueTemp,
		);
		if (rewritten?.used) {
			return {
				kind: 'assigned',
				target: t.identifier(valueTemp),
				trailing: rewritten.statements,
			};
		}
	}
	if (carriedCompletionName != null) {
		const rewritten = rewriteCarriedCompletionReads(
			trailing,
			carriedCompletionName,
		);
		if (rewritten?.used) {
			return {
				kind: 'assigned',
				target: t.identifier(carriedCompletionName),
				trailing: rewritten.statements,
			};
		}
	}
	if (
		completionTemps.size > 0 &&
		trailing.some((stmt) => statementReadsAny(stmt, completionTemps))
	) {
		return null;
	}
	return {
		kind: 'discarded',
		trailing: trailing.map((stmt) => t.cloneNode(stmt, true)),
	};
}

function rewriteCompletionReads(
	statements: readonly t.Statement[],
	completionTemps: ReadonlySet<string>,
	valueTemp: string,
): { statements: t.Statement[]; used: boolean } | null {
	const wrapped = t.file(t.program(
		statements.map((stmt) => t.cloneNode(stmt, true)),
	));
	let used = false;
	let invalidName: string | null = null;
	traverse(wrapped, {
		Identifier(path) {
			if (!completionTemps.has(path.node.name)) return;
			const parent = path.parentPath;
			if (
				parent.isMemberExpression() &&
				parent.node.object === path.node &&
				memberName(parent.node) === 'value'
			) return;
			if (path.isReferencedIdentifier()) {
				if (path.node.name === valueTemp) {
					used = true;
					return;
				}
				invalidName = path.node.name;
				path.stop();
			}
		},
		MemberExpression(path) {
			if (
				t.isIdentifier(path.node.object) &&
				completionTemps.has(path.node.object.name) &&
				memberName(path.node) === 'value'
			) {
				path.replaceWith(t.identifier(valueTemp));
				used = true;
			}
		},
	});
	if (invalidName != null) {
		debugDelegateDescriptor(
			`completion rewrite rejected ${invalidName ?? '<unknown>'}`,
		);
		return null;
	}
	return { statements: wrapped.program.body, used };
}

function rewriteCarriedCompletionReads(
	statements: readonly t.Statement[],
	name: string,
): { statements: t.Statement[]; used: boolean } | null {
	const wrapped = t.file(t.program(
		statements.map((stmt) => t.cloneNode(stmt, true)),
	));
	let invalid = false;
	traverse(wrapped, {
		Identifier(path) {
			if (path.node.name !== name) return;
			const parent = path.parentPath;
			if (
				parent.isMemberExpression() &&
				parent.node.object === path.node &&
				memberName(parent.node) === 'value'
			) return;
			if (path.isReferencedIdentifier()) {
				invalid = true;
				path.stop();
			}
		},
	});
	if (invalid) return null;

	let used = false;
	traverse(wrapped, {
		MemberExpression(path) {
			if (
				t.isIdentifier(path.node.object, { name }) &&
				memberName(path.node) === 'value'
			) {
				path.replaceWith(t.identifier(name));
				used = true;
			}
		},
	});
	return { statements: wrapped.program.body, used };
}

function statementReadsAny(
	stmt: t.Statement,
	names: ReadonlySet<string>,
): boolean {
	let found = false;
	t.traverseFast(stmt, (node) => {
		if (found) return;
		if (t.isIdentifier(node) && names.has(node.name)) found = true;
	});
	return found;
}

function isGeneratorCompletionInit(expr: t.Expression): boolean {
	return t.isCallExpression(expr) &&
		t.isV8IntrinsicIdentifier(expr.callee) &&
		(expr.callee.name === 'CompleteGenerator' ||
			expr.callee.name === 'CloseGenerator' ||
			expr.callee.name === 'Phi');
}

function singleDeclarator(stmt: t.Statement) {
	if (!t.isVariableDeclaration(stmt)) return null;
	if (stmt.declarations.length !== 1) return null;
	const [decl] = stmt.declarations;
	return t.isVariableDeclarator(decl) ? decl : null;
}

export function memberName(member: t.MemberExpression) {
	if (!member.computed && t.isIdentifier(member.property)) {
		return member.property.name;
	}
	if (member.computed && t.isStringLiteral(member.property)) {
		return member.property.value;
	}
	return null;
}

function isUndefinedNode(node: t.Node | null | undefined): boolean {
	return t.isIdentifier(node, { name: 'undefined' }) ||
		t.isUnaryExpression(node, { operator: 'void' });
}
