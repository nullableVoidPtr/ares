import * as t from '@babel/types';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import type { SSARegister } from '../../../ssa.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import { statementListEndsAbruptly } from '../../ast/completion.ts';
import type { IRBlock, LiftedAST } from '../../ast/mod.ts';
import { invertTest } from '../../ast/expression.ts';
import type { IRFunction } from '../mod.ts';
import { statementAlwaysTerminates } from '../finalizer.ts';
import { phiContext, PhiLoweringPlan, registerName } from './phi.ts';
import {
	blockContainsIntrinsic,
	cloneBodyForPredecessor,
	cloneStatementList,
	isIteratorCloseRethrowBody,
	leadingPhiDeclarations,
	reduceSequence,
} from './linear.ts';
import {
	conditionForSuccessor,
	otherSuccessor,
	predecessorSetEquals,
} from './predicates.ts';

export function computeImmediateDominators(
	func: IRFunction,
): AddressMap<BlockAddr | null> {
	const ENTRY = 0 as BlockAddr;
	const allBlocks = new AddressSet<BlockAddr>(func.blocks.keys());

	// Compute reachable set via BFS from entry to avoid cyclic idom for unreachable blocks.
	const reachable = new AddressSet<BlockAddr>([ENTRY]);
	const queue: BlockAddr[] = [ENTRY];
	while (queue.length > 0) {
		const cur = queue.pop()!;
		for (const succ of func.blocks.get(cur)?.consequentAddresses ?? []) {
			if (func.blocks.has(succ) && !reachable.has(succ)) {
				reachable.add(succ);
				queue.push(succ);
			}
		}
	}

	const doms = new AddressMap<AddressSet<BlockAddr>>();
	for (const addr of func.blocks.keys()) {
		// Unreachable blocks only dominate themselves; they must not participate
		// in the intersection-based fixed-point (which would produce cyclic idom).
		doms.set(
			addr,
			addr === ENTRY
				? new AddressSet([ENTRY])
				: reachable.has(addr)
				? new AddressSet(allBlocks)
				: new AddressSet([addr]),
		);
	}

	let changed = true;
	while (changed) {
		changed = false;
		for (const addr of func.blocks.keys()) {
			if (addr === ENTRY) continue;
			const preds = func.predecessorsOf(addr);
			if (preds.size === 0) continue;

			let intersection: AddressSet<BlockAddr> | null = null;
			for (const pred of preds) {
				if (!reachable.has(pred)) continue; // unreachable preds don't constrain dominators
				const predDom = doms.get(pred);
				if (!predDom) continue;
				intersection = intersection === null
					? new AddressSet(predDom)
					: <AddressSet<BlockAddr>> intersection.intersection(
						predDom,
					);
			}
			if (intersection === null) continue;
			intersection.add(addr);

			if (!intersection.equals(doms.get(addr)!)) {
				doms.set(addr, intersection);
				changed = true;
			}
		}
	}

	// idom(b) = deepest strict dominator: the d in strictDoms(b) where all other
	// d' in strictDoms(b) also dominate d (i.e., d' ∈ dom(d)).
	const idom = new AddressMap<BlockAddr | null>();
	idom.set(ENTRY, null);

	for (const addr of func.blocks.keys()) {
		if (addr === ENTRY) continue;
		const strictDoms = <AddressSet<BlockAddr>> doms.get(addr)!.difference(
			new AddressSet([addr]),
		);

		let idomAddr: BlockAddr | null = null;
		outer: for (const d of strictDoms) {
			const dDoms = doms.get(d) ?? new AddressSet<BlockAddr>();
			for (const dPrime of strictDoms) {
				if (dPrime === d) continue;
				if (!dDoms.has(dPrime)) continue outer;
			}
			idomAddr = d;
			break;
		}
		idom.set(addr, idomAddr);
	}

	return idom;
}

function dominatesFromImmediateDominators(
	idom: AddressMap<BlockAddr | null>,
	dominator: BlockAddr,
	addr: BlockAddr,
): boolean {
	let current: BlockAddr | null | undefined = addr;
	while (current != null) {
		if (current === dominator) return true;
		current = idom.get(current);
	}
	return false;
}

export function computeLoopBody(
	func: IRFunction,
	header: BlockAddr,
	latch: BlockAddr,
): AddressSet<BlockAddr> {
	const body = new AddressSet<BlockAddr>([header]);
	const stack: BlockAddr[] = [latch];
	while (stack.length > 0) {
		const current = stack.pop()!;
		if (body.has(current)) continue;
		body.add(current);
		if (current === header) continue;
		for (const pred of func.predecessorsOf(current)) {
			if (!body.has(pred)) stack.push(pred);
		}
	}
	return body;
}

function loopContainsSourceBlock(
	func: IRFunction,
	body: ReadonlySet<BlockAddr>,
	source: BlockAddr,
): boolean {
	if (body.has(source)) return true;
	return [...body].some((address) =>
		func.mergedBlocks.get(address)?.has(source)
	);
}

function isLoopLocalIteratorCleanupHandler(
	func: IRFunction,
	body: ReadonlySet<BlockAddr>,
	handler: BlockAddr,
): boolean {
	const record = func.exceptions.records.get(handler);
	if (
		!record ||
		![...record.protectedBlocks].every((address) =>
			loopContainsSourceBlock(func, body, address)
		)
	) return false;

	const statements = func.blocks.get(handler)?.body as
		| t.Statement[]
		| undefined;
	const catchStatement = statements?.[0];
	if (
		!statements || !t.isVariableDeclaration(catchStatement) ||
		catchStatement.declarations.length !== 1
	) return false;
	const [declaration] = catchStatement.declarations;
	if (
		!t.isIdentifier(declaration.id) ||
		!t.isCallExpression(declaration.init) ||
		!t.isV8IntrinsicIdentifier(declaration.init.callee, { name: 'Catch' })
	) return false;
	return isIteratorCloseRethrowBody(
		statements.slice(1),
		declaration.id.name,
	);
}

export function isHeaderTestedProtectedBodyLoop(
	func: IRFunction,
	header: BlockAddr,
	latch: BlockAddr,
): boolean {
	const headerBlock = func.blocks.get(header);
	const latchBlock = func.blocks.get(latch);
	if (!latchBlock) return false;

	const body = computeLoopBody(func, header, latch);
	const latchBackedgeOnly = !latchBlock.branch &&
		latchBlock.consequentAddresses.length === 1 &&
		latchBlock.consequentAddresses[0] === header;
	// A handler present only at the header can be the loop-local protected
	// scope. Conversely, Hermes iterator loops can protect only the body and
	// latch with an exact IteratorClose/rethrow landing pad. Neither shape means
	// the backedge crosses an unrelated try region.
	const latchBranchBackedge = latchBlock.branch &&
		latchBlock.consequentAddresses.length === 2 &&
		latchBlock.consequentAddresses.some((successor) =>
			successor === header
		) &&
		latchBlock.consequentAddresses.some((successor) =>
			!body.has(successor)
		);
	if (!latchBackedgeOnly && !latchBranchBackedge) return false;

	if (headerBlock?.branch) {
		const [left, right] = headerBlock.consequentAddresses;
		if (latchBackedgeOnly && body.has(left) === body.has(right)) {
			return false;
		}
		if (latchBranchBackedge && !body.has(left) && !body.has(right)) {
			return false;
		}
	} else if (headerBlock && headerBlock.consequentAddresses.length === 1) {
		if (!body.has(headerBlock.consequentAddresses[0])) return false;
	} else {
		return false;
	}

	const headerHandlers = func.exceptions.activeHandlersAtBlock(header);
	const latchHandlers = func.exceptions.activeHandlersAtBlock(latch);
	const headerOnlyHandlers = headerHandlers.difference(latchHandlers);
	const latchOnlyHandlers = latchHandlers.difference(headerHandlers);
	let loopLocalHandlers = headerOnlyHandlers;
	if (loopLocalHandlers.size === 0) {
		if (
			latchOnlyHandlers.size === 0 ||
			![...latchOnlyHandlers].every((handler) =>
				isLoopLocalIteratorCleanupHandler(func, body, handler)
			)
		) return false;
		loopLocalHandlers = latchOnlyHandlers;
	} else if (latchOnlyHandlers.size > 0) {
		return false;
	}

	// Compare body handler state with the loop-local protected scope masked out.
	// This admits catch/finally trailer blocks owned by the same dispatch loop
	// and IteratorClose/rethrow handlers protecting only the iterator body,
	// while still rejecting loops that cross an independent handler boundary.
	for (const addr of body) {
		if (addr === header) continue;
		const options = { exclude: loopLocalHandlers };
		if (
			!func.exceptions.activeHandlersEqual(addr, latch, options) &&
			!func.exceptions.activeHandlersEqual(addr, header, options)
		) {
			return false;
		}
	}

	return true;
}

export function appendExclusiveLoopExit(
	func: IRFunction,
	headerBlock: {
		body: LiftedAST<t.Statement>[];
		consequentAddresses: BlockAddr[];
	},
	header: BlockAddr,
	loopExit: BlockAddr,
) {
	const loopExitBlock = func.blocks.get(loopExit);
	const loopExitPreds = func.predecessorsOf(loopExit);
	if (
		loopExitBlock && loopExitBlock.consequentAddresses.length <= 1 &&
		[...loopExitPreds].every((pred) => pred === header)
	) {
		headerBlock.body.push(...<t.Statement[]> loopExitBlock.body);
		headerBlock.consequentAddresses = [
			...loopExitBlock.consequentAddresses,
		];
		func.markMergedBlocks(header, loopExit);
	} else {
		headerBlock.consequentAddresses = [loopExit];
	}
}

// Clone a terminal block's content into a single non-terminal predecessor when
// the terminal has multiple predecessors (preventing reduceSequence from merging).
// Enables downstream reducers to make progress on fan-in patterns.
function terminalCloneBudgetOk(
	predecessorCount: number,
	bodyLength: number,
): boolean {
	if (predecessorCount <= 4) return bodyLength <= 64;
	return predecessorCount <= 8 && bodyLength <= 1;
}

function computeCyclicBlocks(func: IRFunction): AddressSet<BlockAddr> {
	let nextIndex = 0;
	const indexes = new AddressMap<number>();
	const lowlinks = new AddressMap<number>();
	const stack: BlockAddr[] = [];
	const onStack = new AddressSet<BlockAddr>();
	const cyclic = new AddressSet<BlockAddr>();

	const visit = (address: BlockAddr) => {
		indexes.set(address, nextIndex);
		lowlinks.set(address, nextIndex);
		nextIndex++;
		stack.push(address);
		onStack.add(address);

		for (
			const successor of func.blocks.get(address)?.consequentAddresses ??
				[]
		) {
			if (!func.blocks.has(successor)) continue;
			if (!indexes.has(successor)) {
				visit(successor);
				lowlinks.set(
					address,
					Math.min(lowlinks.get(address)!, lowlinks.get(successor)!),
				);
			} else if (onStack.has(successor)) {
				lowlinks.set(
					address,
					Math.min(lowlinks.get(address)!, indexes.get(successor)!),
				);
			}
		}

		if (lowlinks.get(address) !== indexes.get(address)) return;
		const component: BlockAddr[] = [];
		while (true) {
			const member = stack.pop()!;
			onStack.delete(member);
			component.push(member);
			if (member === address) break;
		}
		if (
			component.length > 1 ||
			func.blocks.get(address)?.consequentAddresses.includes(address)
		) {
			for (const member of component) cyclic.add(member);
		}
	};

	for (const address of func.blocks.keys()) {
		if (!indexes.has(address)) visit(address);
	}
	return cyclic;
}

function terminalHasLoopAndNonLoopPredecessors(
	predecessors: ReadonlySet<BlockAddr>,
	cyclicBlocks: ReadonlySet<BlockAddr>,
): boolean {
	let hasLoopPredecessor = false;
	let hasNonLoopPredecessor = false;
	for (const predecessor of predecessors) {
		if (cyclicBlocks.has(predecessor)) hasLoopPredecessor = true;
		else hasNonLoopPredecessor = true;
		if (hasLoopPredecessor && hasNonLoopPredecessor) return true;
	}
	return false;
}

function isNaturalLoopBreakTerminal(
	block: IRBlock,
	body: readonly t.Statement[],
): boolean {
	return block.kind === 'synthetic' &&
		block.terminalKind === 'break' &&
		block.syntheticReason === 'natural-loop-break' &&
		body.length === 1 && t.isBreakStatement(body[0]);
}

function blockContainsFunctionReturn(block: IRBlock): boolean {
	let found = false;
	for (const statement of block.body) {
		t.traverseFast(statement as t.Statement, (node) => {
			if (found) return t.traverseFast.skip;
			if (node !== statement && t.isFunction(node)) {
				return t.traverseFast.skip;
			}
			if (t.isReturnStatement(node)) {
				found = true;
				return t.traverseFast.skip;
			}
		});
		if (found) break;
	}
	return found;
}

/**
 * A terminal may no longer contain a literal `%Phi` after edge lowering, but
 * its original SSA block still identifies it as a join. Cloning such a block
 * into its predecessors destroys that join topology and can make a later clone
 * ambiguous once several predecessor source blocks have been merged together.
 * Keep the continuation shared instead; the conditional/sequence reducers can
 * then structure the selector while emitting the continuation once.
 */
function hasPhiJoinProvenance(
	func: IRFunction,
	address: BlockAddr,
): boolean {
	// Only a Phi at the terminal entry selects a value on the incoming edge
	// being cloned. Phis already structured inside the terminal have their own
	// lexical assignments and do not make the outer clone ambiguous.
	return (func.ssa.basicBlocks.get(address)?.ssaInstructions ?? []).some(
		(instruction) => instruction.instruction === 'Phi',
	);
}

/**
 * Finishes a guard whose shared phi continuation was sequence-merged into one
 * arm. The other arm still names the former continuation address, so cloning
 * the live terminal would duplicate calls/closures. Instead, recover the two
 * edge values, assign the phi conditionally, and append the continuation once.
 */
export function reduceMergedGuardPhiTerminal(func: IRFunction): boolean {
	const phiContext_ = phiContext(func);
	for (const [address, block] of func.blocks) {
		if (!block.branch || block.consequentAddresses.length !== 2) continue;
		const existing = block.consequentAddresses.filter((successor) =>
			func.blocks.has(successor)
		);
		const missing = block.consequentAddresses.filter((successor) =>
			!func.blocks.has(successor)
		);
		if (existing.length !== 1 || missing.length !== 1) continue;

		const [liveAddress] = existing;
		const [mergedJoinAddress] = missing;
		const live = func.blocks.get(liveAddress)!;
		if (live.branch || live.consequentAddresses.length !== 0) continue;
		if (
			!phiContext_.mergedSourceAddresses(liveAddress).has(
				mergedJoinAddress,
			)
		) continue;
		if (
			!func.exceptions.activeHandlersEqual(address, liveAddress) ||
			!func.exceptions.activeHandlersEqual(
				liveAddress,
				mergedJoinAddress,
			)
		) continue;

		const phis = leadingPhiDeclarations(live.body);
		if (phis.length > 4) continue;
		const resolved = phiContext_.resolveUses(
			liveAddress,
			phis.map(({ name }) => name),
			live.body.slice(phis.length) as t.Statement[],
		);
		if (!resolved) continue;
		const terminalBody = resolved.body;
		if (!statementListEndsAbruptly(terminalBody)) continue;

		const parentSources = phiContext_.mergedSourceAddresses(address);
		const assignments: Array<{
			name: string;
			parent: SSARegister;
			live: SSARegister;
		}> = [];
		let complete = true;
		for (const target of resolved.targets) {
			const instr = target.instruction;
			const parentSource = phiContext_.sourceForPredecessor(
				instr,
				address,
			);
			const liveSource = phiContext_.sourceForPredecessor(
				instr,
				liveAddress,
			);
			if (!parentSource || !liveSource) {
				complete = false;
				break;
			}
			const canonicalParent = phiContext_.canonicalSource(parentSource);
			const canonicalLive = phiContext_.canonicalSource(liveSource);
			const parentDefinition = phiContext_.definitionBlock(
				canonicalParent,
			);
			const liveDefinition = phiContext_.definitionBlock(canonicalLive);
			if (
				(parentDefinition != null &&
					!parentSources.has(parentDefinition)) ||
				(liveDefinition != null && !parentSources.has(liveDefinition))
			) {
				complete = false;
				break;
			}
			assignments.push({
				name: target.name,
				parent: canonicalParent,
				live: canonicalLive,
			});
		}
		if (!complete) continue;

		const liveTest = conditionForSuccessor(block, liveAddress);
		if (!liveTest) continue;
		if (!complete || assignments.length === 0) continue;
		if (phis.length === 0 && resolved.inlineCount === 0) continue;
		const body = [
			...block.body,
			t.variableDeclaration(
				'let',
				assignments.map(({ name }) =>
					t.variableDeclarator(t.identifier(name))
				),
			),
			t.ifStatement(
				liveTest,
				t.blockStatement(
					assignments.map(({ name, live: source }) =>
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.identifier(name),
							t.identifier(registerName(source)),
						))
					),
				),
				t.blockStatement(
					assignments.map(({ name, parent: source }) =>
						t.expressionStatement(t.assignmentExpression(
							'=',
							t.identifier(name),
							t.identifier(registerName(source)),
						))
					),
				),
			),
			...terminalBody,
		];
		const plan = new PhiLoweringPlan(func);
		if (!plan.replaceBody(address, body)) continue;
		if (!plan.replaceControlFlow(address, undefined, [])) continue;
		if (!plan.commit()) continue;
		func.markMergedBlocks(address, liveAddress);
		return true;
	}
	return false;
}

export function reduceSharedTerminalPhi(func: IRFunction): boolean {
	const phiContext_ = phiContext(func);
	const idom = computeImmediateDominators(func);
	for (const [addr, block] of func.blocks) {
		if (block.branch || block.consequentAddresses.length !== 0) continue;
		if (
			func.exceptions.records.get(addr)?.canonicalFinallyAddress != null
		) {
			continue;
		}

		const phis = leadingPhiDeclarations(block.body);
		const returnPhi = phis.length === 0 && block.body.length === 1
			? (() => {
				const stmt = block.body[0] as t.Statement;
				if (!t.isReturnStatement(stmt)) return null;
				const arg = stmt.argument;
				if (
					!t.isCallExpression(arg) ||
					!t.isV8IntrinsicIdentifier(arg.callee, { name: 'Phi' })
				) return null;
				return { stmt, call: arg };
			})()
			: null;
		if (
			(phis.length === 0 && returnPhi == null) ||
			(phis.length > 0 && phis.length >= block.body.length)
		) continue;

		const predecessors = func.predecessorsOf(addr);
		if (returnPhi == null) {
			if (phis.length > 4) continue;
			if (predecessors.size <= 4) {
				if (
					block.body.length > 64 ||
					blockContainsIntrinsic(block, 'CreateClosure')
				) continue;
			} else if (block.body.length > 128) {
				continue;
			}
		}
		const minPredecessors = 1;
		if (
			predecessors.size <= minPredecessors ||
			predecessors.size > 16
		) continue;
		if (
			![...predecessors].every((pred) =>
				func.exceptions.activeHandlersEqual(pred, addr)
			)
		) continue;

		const declarationAddr = idom.get(addr);
		const declarationBlock = declarationAddr == null
			? null
			: func.blocks.get(declarationAddr);
		if (!declarationBlock || declarationBlock === block) continue;

		const ssaBlock = func.ssa.basicBlocks.get(addr);
		if (!ssaBlock) continue;
		const ssaPhis = ssaBlock.ssaInstructions.filter((instr) =>
			instr.instruction === 'Phi'
		);
		const targetCount = returnPhi == null ? phis.length : 1;
		if (ssaPhis.length < targetCount) continue;

		const targets = returnPhi == null
			? phis.map((phi, index) => ({ name: phi.name, index }))
			: [{
				name: registerName(ssaPhis[0].destination),
				index: 0,
			}];

		const sourcePlans: Array<{
			predecessor: BlockAddr;
			target: string;
			source: SSARegister;
		}> = [];
		let complete = true;
		for (const target of targets) {
			const ssaPhi = ssaPhis[target.index];
			if (ssaPhi.instruction !== 'Phi') {
				complete = false;
				break;
			}
			if (registerName(ssaPhi.destination) !== target.name) {
				complete = false;
				break;
			}

			for (const pred of predecessors) {
				const source = phiContext_.sourceForPredecessor(ssaPhi, pred);
				if (!source) {
					complete = false;
					break;
				}
				sourcePlans.push({
					predecessor: pred,
					target: target.name,
					source,
				});
			}
			if (!complete) break;
		}
		if (!complete) continue;

		const plan = new PhiLoweringPlan(func);
		if (!plan.declare(declarationAddr!, targets.map(({ name }) => name))) {
			continue;
		}
		let planComplete = true;
		for (const { predecessor, target, source } of sourcePlans) {
			if (
				!plan.assign(
					predecessor,
					target,
					t.identifier(registerName(source)),
				)
			) {
				planComplete = false;
				break;
			}
		}
		if (!planComplete) continue;
		if (returnPhi) {
			plan.replaceReturnArgument(
				returnPhi.stmt,
				t.identifier(targets[0].name),
			);
		} else {
			if (!plan.removeBody(addr, 0, phis.length)) continue;
		}
		if (!plan.commit()) continue;
		return true;
	}

	return false;
}

export function reduceSharedLeadingPhi(
	func: IRFunction,
	options: {
		address?: BlockAddr;
		aliasOnlyClosureContinuation?: boolean;
		nonTerminalOnly?: boolean;
		skipClosureSources?: boolean;
		maxPhis?: number;
		maxPredecessors?: number;
		onApplied?: (info: {
			address: BlockAddr;
			phiCount: number;
			predecessorCount: number;
		}) => void;
	} = {},
): boolean {
	const phiContext_ = phiContext(func);
	const idom = computeImmediateDominators(func);
	for (const [addr, block] of func.blocks) {
		if (options.address != null && addr !== options.address) continue;
		if (
			options.nonTerminalOnly && !block.branch &&
			block.consequentAddresses.length === 0
		) continue;
		const phis = leadingPhiDeclarations(block.body);
		if (
			phis.length === 0 ||
			(phis.length >= block.body.length && !block.branch)
		) continue;
		if (phis.length > (options.maxPhis ?? 4)) continue;
		if (options.aliasOnlyClosureContinuation) {
			if (
				block.body.length !== phis.length + 1 ||
				block.consequentAddresses.length !== 1
			) continue;
			const continuation = func.blocks.get(block.consequentAddresses[0]);
			if (
				!continuation ||
				!blockContainsIntrinsic(continuation, 'CreateClosure')
			) continue;
		}

		const predecessors = func.predecessorsOf(addr);
		if (
			predecessors.size <= 1 ||
			predecessors.size > (options.maxPredecessors ?? 8)
		) continue;
		if (
			options.skipClosureSources &&
			[...predecessors].some((pred) => {
				const predecessor = func.blocks.get(pred);
				return predecessor != null &&
					blockContainsIntrinsic(predecessor, 'CreateClosure');
			})
		) continue;
		if (
			![...predecessors].every((pred) =>
				func.exceptions.activeHandlersEqual(pred, addr)
			)
		) continue;

		// Leave loop-header phis to natural-loop reconstruction. Rewriting a
		// back-edge phi here makes the loop shape less explicit for that pass.
		if (
			[...predecessors].some((pred) =>
				dominatesFromImmediateDominators(idom, addr, pred)
			)
		) continue;

		const declarationAddr = idom.get(addr);
		const declarationBlock = declarationAddr == null
			? null
			: func.blocks.get(declarationAddr);
		if (!declarationBlock || declarationBlock === block) continue;

		const ssaBlock = func.ssa.basicBlocks.get(addr);
		if (!ssaBlock) continue;
		const ssaPhis = ssaBlock.ssaInstructions.filter((instr) =>
			instr.instruction === 'Phi'
		);
		if (ssaPhis.length < phis.length) continue;

		const sourcePlans: Array<{
			pred: BlockAddr;
			target: string;
			source: SSARegister;
		}> = [];
		let complete = true;
		for (const [index, phi] of phis.entries()) {
			const ssaPhi = ssaPhis[index];
			if (
				ssaPhi.instruction !== 'Phi' ||
				registerName(ssaPhi.destination) !== phi.name
			) {
				complete = false;
				break;
			}

			for (const pred of predecessors) {
				const source = phiContext_.sourceForPredecessor(ssaPhi, pred);
				if (!source) {
					complete = false;
					break;
				}
				sourcePlans.push({ pred, target: phi.name, source });
			}
			if (!complete) break;
		}
		if (!complete) continue;

		const plan = new PhiLoweringPlan(func);
		if (
			!plan.declare(
				declarationAddr!,
				phis.map(({ name }) => name),
				true,
			)
		) continue;
		for (const { pred, target, source } of sourcePlans) {
			const predecessor = func.blocks.get(pred);
			if (!predecessor) {
				complete = false;
				break;
			}
			const sourceName = registerName(source);
			const sourceExpression = plan.consumeUnusedInitializer(
				pred,
				sourceName,
			) ?? t.identifier(sourceName);
			if (!plan.assign(pred, target, sourceExpression)) {
				complete = false;
				break;
			}
		}
		if (!complete) continue;

		if (!complete || !plan.removeBody(addr, 0, phis.length)) continue;
		if (!plan.commit()) continue;
		options.onApplied?.({
			address: addr,
			phiCount: phis.length,
			predecessorCount: predecessors.size,
		});
		return true;
	}

	return false;
}

export function reduceInlineTerminal(
	func: IRFunction,
	options: { excludeAddresses?: ReadonlySet<BlockAddr> } = {},
): boolean {
	let changed = false;
	const predecessorMap = new AddressMap<AddressSet<BlockAddr>>();
	for (const address of func.blocks.keys()) {
		predecessorMap.set(address, new AddressSet<BlockAddr>());
	}
	for (const [address, block] of func.blocks) {
		for (const successor of block.consequentAddresses) {
			const predecessors = predecessorMap.get(successor) ??
				new AddressSet<BlockAddr>();
			predecessors.add(address);
			predecessorMap.set(successor, predecessors);
		}
	}
	const cyclicBlocks = computeCyclicBlocks(func);
	const predecessorsOf = (address: BlockAddr): ReadonlySet<BlockAddr> =>
		func.exceptions.isCatchTarget(address)
			? func.predecessorsOf(address)
			: predecessorMap.get(address) ?? new AddressSet<BlockAddr>();
	const setSuccessors = (
		address: BlockAddr,
		block: IRBlock,
		successors: BlockAddr[],
	) => {
		for (const successor of block.consequentAddresses) {
			predecessorMap.get(successor)?.delete(address);
		}
		block.consequentAddresses = successors;
		for (const successor of successors) {
			const predecessors = predecessorMap.get(successor) ??
				new AddressSet<BlockAddr>();
			predecessors.add(address);
			predecessorMap.set(successor, predecessors);
		}
	};
	const preserveSharedLoopTerminal = (
		predecessors: ReadonlySet<BlockAddr>,
	) => terminalHasLoopAndNonLoopPredecessors(predecessors, cyclicBlocks);
	for (const [addr, block] of func.blocks) {
		if (block.branch && block.consequentAddresses.length === 2) {
			if (
				['JmpBuiltinIs', 'JmpBuiltinIsNot'].includes(
					block.branch?.extra?.instruction!,
				)
			) continue;
			for (const succAddr of block.consequentAddresses) {
				if (options.excludeAddresses?.has(succAddr)) continue;
				const succ = func.blocks.get(succAddr);
				if (!succ) continue;
				if (succ.consequentAddresses.length !== 0) continue;
				if (func.id === 0 && blockContainsFunctionReturn(succ)) {
					continue;
				}
				const predecessors = predecessorsOf(succAddr);
				if (predecessors.size === 1 && predecessors.has(addr)) {
					if (!func.exceptions.activeHandlersEqual(addr, succAddr)) {
						continue;
					}
					if (
						func.exceptions.records.get(succAddr)
							?.canonicalFinallyAddress != null
					) continue;
					const terminalBody = cloneBodyForPredecessor(
						func,
						succAddr,
						addr,
					);
					if (
						!statementAlwaysTerminates(
							t.blockStatement(terminalBody),
						)
					) continue;
					const test = conditionForSuccessor(block, succAddr);
					const other = otherSuccessor(block, succAddr);
					if (!test || other == null) continue;
					block.body.push(
						t.ifStatement(test, t.blockStatement(terminalBody)),
					);
					block.branch = undefined;
					setSuccessors(addr, block, [other]);
					func.markMergedBlocks(addr, succAddr);
					changed = true;
					break;
				}
				if (predecessors.size <= 1) continue;
				if (preserveSharedLoopTerminal(predecessors)) {
					continue;
				}
				if (hasPhiJoinProvenance(func, succAddr)) continue;
				if (
					!terminalCloneBudgetOk(
						predecessors.size,
						succ.body.length,
					)
				) continue;
				if (
					succ.body.length > 1 &&
					blockContainsIntrinsic(succ, 'CreateClosure')
				) continue;
				if (!func.exceptions.activeHandlersEqual(addr, succAddr)) {
					continue;
				}
				if (
					func.exceptions.records.get(succAddr)
						?.canonicalFinallyAddress != null
				) {
					continue;
				}

				const clonedBody = cloneBodyForPredecessor(
					func,
					succAddr,
					addr,
				);
				if (
					!statementAlwaysTerminates(t.blockStatement(clonedBody)) &&
					!isNaturalLoopBreakTerminal(succ, clonedBody)
				) continue;
				const test = conditionForSuccessor(block, succAddr);
				const other = otherSuccessor(block, succAddr);
				if (!test || other == null) continue;

				block.body.push(
					t.ifStatement(test, t.blockStatement(clonedBody), null),
				);
				block.branch = undefined;
				setSuccessors(addr, block, [other]);
				changed = true;
				break;
			}
			continue;
		}

		if (block.branch) continue;
		if (block.consequentAddresses.length !== 1) continue;
		const [succAddr] = block.consequentAddresses;
		if (options.excludeAddresses?.has(succAddr)) continue;
		const succ = func.blocks.get(succAddr);
		if (!succ) continue;
		const last = block.body.at(-1) as t.Statement | undefined;
		if (
			t.isIfStatement(last) &&
			!last.alternate &&
			t.isBlockStatement(last.consequent) &&
			statementAlwaysTerminates(last.consequent) &&
			predecessorsOf(succAddr).size === 1 &&
			func.exceptions.activeHandlersEqual(addr, succAddr) &&
			!func.exceptions.isCatchTarget(succAddr) &&
			func.exceptions.records.get(succAddr)?.canonicalFinallyAddress ==
				null
		) {
			last.alternate = t.blockStatement(
				<t.Statement[]> succ.body,
			);
			setSuccessors(addr, block, [...succ.consequentAddresses]);
			func.markMergedBlocks(addr, succAddr);
			changed = true;
			continue;
		}
		if (succ.consequentAddresses.length !== 0) continue;
		if (func.id === 0 && blockContainsFunctionReturn(succ)) continue;
		const predecessors = predecessorsOf(succAddr);
		if (predecessors.size <= 1) continue; // reduceSequence handles this
		if (preserveSharedLoopTerminal(predecessors)) continue;
		if (hasPhiJoinProvenance(func, succAddr)) continue;
		if (!terminalCloneBudgetOk(predecessors.size, succ.body.length)) {
			continue;
		}
		if (
			succ.body.length > 1 &&
			blockContainsIntrinsic(succ, 'CreateClosure')
		) continue;
		if (
			func.exceptions.records.get(succAddr)?.canonicalFinallyAddress !=
				null
		) {
			continue;
		}

		block.body.push(
			...cloneBodyForPredecessor(func, succAddr, addr),
		);
		setSuccessors(addr, block, []);
		changed = true;
	}
	return changed;
}

export function reduceDanglingGuardTail(func: IRFunction): boolean {
	for (const [_addr, block] of func.blocks) {
		if (!block.branch || block.consequentAddresses.length !== 2) continue;
		const [left, right] = block.consequentAddresses;
		if (left !== right) continue;
		// The bytecode still evaluates the predicate even though both outcomes now
		// share a target. Keep that evaluation explicit; cleanup can discard it when
		// it is mechanically pure.
		block.body.push(t.expressionStatement(
			t.cloneNode(block.branch as t.Expression, true),
		));
		block.branch = undefined;
		block.consequentAddresses = [left];
		return true;
	}

	for (const [_addr, block] of func.blocks) {
		if (block.branch) continue;
		if (block.consequentAddresses.length === 0) continue;
		if (
			block.consequentAddresses.every((succ) => !func.blocks.has(succ))
		) {
			block.consequentAddresses = [];
			return true;
		}
	}

	for (const [addr, block] of func.blocks) {
		if (!block.branch || block.consequentAddresses.length !== 2) continue;

		const [left, right] = block.consequentAddresses;
		const leftBlock = func.blocks.get(left);
		const rightBlock = func.blocks.get(right);
		if ((leftBlock == null) !== (rightBlock == null)) {
			const missingAddr = leftBlock == null ? left : right;
			const existingAddr = leftBlock == null ? right : left;
			if (!func.exceptions.activeHandlersEqual(addr, existingAddr)) {
				continue;
			}
			const test = conditionForSuccessor(block, missingAddr);
			if (!test) continue;
			block.body.push(
				t.ifStatement(test, t.blockStatement([t.returnStatement()])),
			);
			block.branch = undefined;
			block.consequentAddresses = [existingAddr];
			return true;
		}
	}

	return false;
}

export function reduceSharedAlternateGuard(func: IRFunction): boolean {
	for (const [addr, block] of func.blocks) {
		if (!block.branch || block.consequentAddresses.length !== 2) continue;

		for (const innerAddr of block.consequentAddresses) {
			const sharedAddr = otherSuccessor(block, innerAddr);
			if (sharedAddr == null) continue;

			const inner = func.blocks.get(innerAddr);
			const shared = func.blocks.get(sharedAddr);
			if (!inner || !shared || !inner.branch || shared.branch) continue;
			if (inner.consequentAddresses.length !== 2) continue;
			if (!inner.consequentAddresses.includes(sharedAddr)) continue;
			if (func.predecessorsOf(innerAddr).size !== 1) continue;
			if (
				!predecessorSetEquals(func, sharedAddr, [addr, innerAddr])
			) continue;
			if (shared.consequentAddresses.length !== 1) continue;
			const joinAddr = otherSuccessor(inner, sharedAddr);
			if (
				joinAddr == null || shared.consequentAddresses[0] !== joinAddr
			) {
				continue;
			}
			if (
				![innerAddr, sharedAddr, joinAddr].every((other) =>
					func.exceptions.activeHandlersEqual(addr, other)
				)
			) continue;

			const outerToInner = conditionForSuccessor(block, innerAddr);
			const innerToShared = conditionForSuccessor(inner, sharedAddr);
			if (!outerToInner || !innerToShared) continue;

			if (shared.body.length > 8) {
				// Factor a large shared arm instead of cloning it into both sides.
				// The temporary records whether control should enter the shared arm;
				// evaluating the outer and inner predicates exactly once preserves
				// their original ordering and any observable coercions.
				const gateName = `_cfgShared_${func.id}_${addressPart(addr)}_${
					addressPart(innerAddr)
				}`;
				block.body.push(
					t.variableDeclaration('let', [
						t.variableDeclarator(
							t.identifier(gateName),
							t.booleanLiteral(true),
						),
					]),
					t.ifStatement(
						outerToInner,
						t.blockStatement([
							...cloneStatementList(inner.body),
							t.expressionStatement(t.assignmentExpression(
								'=',
								t.identifier(gateName),
								innerToShared,
							)),
						]),
					),
				);
				block.branch = t.identifier(gateName);
				block.consequentAddresses = [joinAddr, sharedAddr];
				func.markMergedBlocks(addr, innerAddr);
				return true;
			}

			block.body.push(
				t.ifStatement(
					outerToInner,
					t.blockStatement([
						...cloneStatementList(inner.body),
						t.ifStatement(
							innerToShared,
							t.blockStatement(cloneStatementList(shared.body)),
						),
					]),
					t.blockStatement(cloneStatementList(shared.body)),
				),
			);
			block.branch = undefined;
			block.consequentAddresses = [joinAddr];
			func.markMergedBlocks(addr, innerAddr);
			func.markMergedBlocks(addr, sharedAddr);
			return true;
		}
	}

	return false;
}

function addressPart(address: BlockAddr): string {
	return address < 0 ? `m${-address}` : `${address}`;
}

export function reduceSharedGuardedPrelude(func: IRFunction): boolean {
	for (const [addr, block] of func.blocks) {
		if (!block.branch || block.consequentAddresses.length !== 2) continue;

		for (const innerAddr of block.consequentAddresses) {
			const cancelAddr = otherSuccessor(block, innerAddr);
			if (cancelAddr == null) continue;

			const inner = func.blocks.get(innerAddr);
			const cancel = func.blocks.get(cancelAddr);
			if (!inner?.branch || !cancel?.branch) continue;
			if (inner.consequentAddresses.length !== 2) continue;
			if (cancel.consequentAddresses.length !== 2) continue;
			if (func.predecessorsOf(innerAddr).size !== 1) continue;
			if (!func.exceptions.activeHandlersEqual(addr, innerAddr)) {
				continue;
			}
			if (!func.exceptions.activeHandlersEqual(addr, cancelAddr)) {
				continue;
			}

			for (const bodyAddr of inner.consequentAddresses) {
				const secondAddr = otherSuccessor(inner, bodyAddr);
				if (secondAddr == null) continue;
				const second = func.blocks.get(secondAddr);
				const body = func.blocks.get(bodyAddr);
				if (!second?.branch || !body || body.branch) continue;
				if (second.consequentAddresses.length !== 2) continue;
				if (!second.consequentAddresses.includes(cancelAddr)) continue;
				if (!second.consequentAddresses.includes(bodyAddr)) continue;
				if (!cancel.consequentAddresses.includes(bodyAddr)) continue;
				if (body.consequentAddresses.length !== 1) continue;

				const [tailAddr] = body.consequentAddresses;
				if (otherSuccessor(cancel, bodyAddr) !== tailAddr) continue;
				if (func.predecessorsOf(secondAddr).size !== 1) continue;
				const cancelPreds = func.predecessorsOf(cancelAddr);
				if (
					cancelPreds.size !== 2 ||
					!cancelPreds.has(addr) ||
					!cancelPreds.has(secondAddr)
				) continue;
				const bodyPreds = func.predecessorsOf(bodyAddr);
				if (
					bodyPreds.size !== 3 ||
					!bodyPreds.has(innerAddr) ||
					!bodyPreds.has(secondAddr) ||
					!bodyPreds.has(cancelAddr)
				) continue;
				if (!func.exceptions.activeHandlersEqual(addr, secondAddr)) {
					continue;
				}
				if (!func.exceptions.activeHandlersEqual(addr, bodyAddr)) {
					continue;
				}

				const outerTest = conditionForSuccessor(block, innerAddr);
				const innerTest = conditionForSuccessor(inner, bodyAddr);
				const secondTest = conditionForSuccessor(second, bodyAddr);
				const cancelTest = conditionForSuccessor(cancel, bodyAddr);
				if (!outerTest || !innerTest || !secondTest || !cancelTest) {
					continue;
				}

				const prelude = () => cloneStatementList(body.body);
				const cancelPrelude = () => [
					...cloneStatementList(cancel.body),
					t.ifStatement(
						t.cloneNode(cancelTest, true),
						t.blockStatement(prelude()),
					),
				];
				const secondPrelude = [
					...cloneStatementList(second.body),
					t.ifStatement(
						t.cloneNode(secondTest, true),
						t.blockStatement(prelude()),
						t.blockStatement(cancelPrelude()),
					),
				];

				block.body.push(
					t.ifStatement(
						outerTest,
						t.blockStatement([
							...cloneStatementList(inner.body),
							t.ifStatement(
								innerTest,
								t.blockStatement(prelude()),
								t.blockStatement(secondPrelude),
							),
						]),
						t.blockStatement(cancelPrelude()),
					),
				);
				block.branch = undefined;
				block.consequentAddresses = [tailAddr];
				for (
					const merged of [
						innerAddr,
						secondAddr,
						cancelAddr,
						bodyAddr,
					]
				) {
					func.markMergedBlocks(addr, merged);
				}
				return true;
			}
		}
	}

	return false;
}

function expressionForNonNullishTest(expr: t.Expression): t.Expression | null {
	if (t.isUnaryExpression(expr, { operator: '!' })) {
		const arg = expr.argument;
		if (
			t.isBinaryExpression(arg) &&
			(arg.operator === '==' || arg.operator === '===') &&
			t.isNullLiteral(arg.right)
		) {
			return t.cloneNode(arg.left, true);
		}
		if (
			t.isBinaryExpression(arg) &&
			(arg.operator === '==' || arg.operator === '===') &&
			t.isNullLiteral(arg.left)
		) {
			return t.cloneNode(arg.right, true);
		}
	}
	if (
		t.isBinaryExpression(expr) &&
		(expr.operator === '!=' || expr.operator === '!==') &&
		t.isNullLiteral(expr.right)
	) {
		return t.cloneNode(expr.left, true);
	}
	if (
		t.isBinaryExpression(expr) &&
		(expr.operator === '!=' || expr.operator === '!==') &&
		t.isNullLiteral(expr.left)
	) {
		return t.cloneNode(expr.right, true);
	}
	return null;
}

function terminalNotPhiReturn(block: IRBlock): boolean {
	const body = block.body as t.Statement[];
	if (body.length === 0) return false;
	const last = body.at(-1);
	if (!t.isReturnStatement(last) || !last.argument) return false;
	let arg = last.argument;
	if (t.isIdentifier(arg)) {
		for (let i = body.length - 2; i >= 0; i--) {
			const stmt = body[i];
			if (
				!t.isVariableDeclaration(stmt, { kind: 'const' }) ||
				stmt.declarations.length !== 1
			) continue;
			const [decl] = stmt.declarations;
			if (!t.isIdentifier(decl.id, { name: arg.name }) || !decl.init) {
				continue;
			}
			if (!t.isExpression(decl.init)) return false;
			arg = decl.init;
			break;
		}
	}
	if (
		t.isUnaryExpression(arg, { operator: '!' }) &&
		t.isCallExpression(arg.argument) &&
		t.isV8IntrinsicIdentifier(arg.argument.callee, { name: 'Phi' })
	) return true;
	if (!t.isUnaryExpression(arg, { operator: '!' })) return false;
	if (!t.isIdentifier(arg.argument)) return false;
	for (let i = body.length - 2; i >= 0; i--) {
		const stmt = body[i];
		if (
			!t.isVariableDeclaration(stmt, { kind: 'const' }) ||
			stmt.declarations.length !== 1
		) continue;
		const [decl] = stmt.declarations;
		if (!t.isIdentifier(decl.id, { name: arg.argument.name })) continue;
		return t.isCallExpression(decl.init) &&
			t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' });
	}
	return false;
}

function terminalDefaultPathEffects(
	func: IRFunction,
	addr: BlockAddr,
	joinAddr: BlockAddr,
	seen = new Set<BlockAddr>(),
): t.Statement[] | null {
	if (addr === joinAddr) return [];
	if (seen.has(addr)) return null;
	seen.add(addr);

	const block = func.blocks.get(addr);
	if (!block) return null;
	const body = cloneStatementList(block.body);
	if (!block.branch) {
		if (block.consequentAddresses.length !== 1) return null;
		const tail = terminalDefaultPathEffects(
			func,
			block.consequentAddresses[0],
			joinAddr,
			new Set(seen),
		);
		if (tail == null) return null;
		return [...body, ...tail];
	}
	if (block.consequentAddresses.length !== 2) return null;

	const [left, right] = block.consequentAddresses;
	const leftEffects = terminalDefaultPathEffects(
		func,
		left,
		joinAddr,
		new Set(seen),
	);
	const rightEffects = terminalDefaultPathEffects(
		func,
		right,
		joinAddr,
		new Set(seen),
	);
	if (leftEffects == null || rightEffects == null) return null;
	if (leftEffects.length === 0 && rightEffects.length === 0) return body;

	const leftTest = conditionForSuccessor(block, left);
	const rightTest = conditionForSuccessor(block, right);
	if (!leftTest || !rightTest) return null;
	if (leftEffects.length === 0) {
		return [
			...body,
			t.ifStatement(rightTest, t.blockStatement(rightEffects)),
		];
	}
	if (rightEffects.length === 0) {
		return [
			...body,
			t.ifStatement(leftTest, t.blockStatement(leftEffects)),
		];
	}
	return [
		...body,
		t.ifStatement(
			rightTest,
			t.blockStatement(rightEffects),
			t.blockStatement(leftEffects),
		),
	];
}

function collectReachableUntil(
	func: IRFunction,
	start: BlockAddr,
	stop: BlockAddr,
	seen = new AddressSet<BlockAddr>(),
): AddressSet<BlockAddr> | null {
	if (start === stop) return seen;
	if (seen.has(start)) return seen;
	const block = func.blocks.get(start);
	if (!block) return null;
	seen.add(start);
	for (const succ of block.consequentAddresses) {
		const collected = collectReachableUntil(func, succ, stop, seen);
		if (!collected) return null;
	}
	return seen;
}

function isRegisterIdentifierName(name: string): boolean {
	return /^r\d+_\d+$/.test(name);
}

function declaredNamesInStatements(stmts: t.Statement[]): Set<string> {
	const names = new Set<string>();
	for (const stmt of stmts) {
		if (!t.isVariableDeclaration(stmt)) continue;
		for (const decl of stmt.declarations) {
			if (t.isIdentifier(decl.id)) names.add(decl.id.name);
		}
	}
	return names;
}

function registerIdentifiersInNode(node: t.Node): Set<string> {
	const names = new Set<string>();
	t.traverseFast(node, (child) => {
		if (t.isIdentifier(child) && isRegisterIdentifierName(child.name)) {
			names.add(child.name);
		}
	});
	return names;
}

function originalAliasDeclaration(
	func: IRFunction,
	name: string,
): t.VariableDeclaration | null {
	for (const block of func.ssa.basicBlocks.values()) {
		for (const instr of block.ssaInstructions) {
			if (instr.instruction === 'Phi') continue;
			const dest = Object.values(instr.defs ?? {})[0] as
				| SSARegister
				| undefined;
			if (!dest || registerName(dest) !== name) continue;

			const anyInstr = instr as any;
			const extra = {
				parentFunctionId: func.id,
				address: anyInstr.functionLocalOffset,
				instruction: instr.instruction,
			};
			let init: t.Expression | null = null;
			switch (instr.instruction) {
				case 'LoadParam':
					init = anyInstr.parameterIndex >= func.paramCount
						? t.memberExpression(
							t.identifier('arguments'),
							t.valueToNode(anyInstr.parameterIndex - 1),
							true,
						)
						: t.cloneNode(
							func.getParam(anyInstr.parameterIndex),
							true,
						);
					break;
				case 'GetParentEnvironment':
					init = t.callExpression(
						t.v8IntrinsicIdentifier('GetParentEnvironment'),
						[t.valueToNode(anyInstr.levelIndex)],
					);
					break;
				case 'LoadFromEnvironment': {
					const env = anyInstr.uses?.environment as
						| SSARegister
						| undefined;
					if (!env) return null;
					const envCall = t.callExpression(
						t.v8IntrinsicIdentifier('expectEnvironment'),
						[t.identifier(registerName(env))],
					);
					envCall.extra = extra;
					init = t.memberExpression(
						envCall,
						t.valueToNode(anyInstr.slotIndex),
						true,
					);
					break;
				}
				case 'Mov': {
					const source = anyInstr.uses?.source as
						| SSARegister
						| undefined;
					if (!source) return null;
					init = t.identifier(registerName(source));
					break;
				}
				default:
					return null;
			}
			const decl = t.variableDeclaration('const', [
				t.variableDeclarator(t.identifier(name), init),
			]);
			decl.extra = extra;
			return decl;
		}
	}
	return null;
}

function materializeMissingRegisterAliases(
	func: IRFunction,
	body: t.Statement[],
): t.Statement[] {
	const declared = declaredNamesInStatements(body);
	const needed = new Set<string>();
	for (const stmt of body) {
		for (const name of registerIdentifiersInNode(stmt)) {
			if (!declared.has(name)) needed.add(name);
		}
	}

	const aliases: t.VariableDeclaration[] = [];
	for (let changed = true; changed;) {
		changed = false;
		for (const name of [...needed]) {
			if (declared.has(name)) {
				needed.delete(name);
				continue;
			}
			const alias = originalAliasDeclaration(func, name);
			if (!alias) continue;
			aliases.push(alias);
			declared.add(name);
			needed.delete(name);
			for (const dep of registerIdentifiersInNode(alias)) {
				if (!declared.has(dep)) needed.add(dep);
			}
			changed = true;
		}
	}

	return aliases.length === 0 ? body : [...aliases, ...body];
}

export function reduceNullishDefaultReturnPhi(func: IRFunction): boolean {
	for (const [addr, block] of func.blocks) {
		if (!block.branch || block.consequentAddresses.length !== 2) continue;

		for (const joinAddr of block.consequentAddresses) {
			const defaultAddr = otherSuccessor(block, joinAddr);
			if (defaultAddr == null) continue;
			const join = func.blocks.get(joinAddr);
			if (
				!join ||
				join.branch ||
				join.consequentAddresses.length !== 0 ||
				!terminalNotPhiReturn(join)
			) continue;

			const directTest = conditionForSuccessor(block, joinAddr);
			if (!directTest) continue;
			const value = expressionForNonNullishTest(directTest);
			if (!value) continue;

			const defaultEffects = terminalDefaultPathEffects(
				func,
				defaultAddr,
				joinAddr,
			);
			if (defaultEffects == null) continue;
			const merged = collectReachableUntil(func, defaultAddr, joinAddr);
			if (!merged) continue;

			block.body.push(
				t.ifStatement(
					invertTest(directTest),
					t.blockStatement(materializeMissingRegisterAliases(
						func,
						[
							...defaultEffects,
							t.returnStatement(t.booleanLiteral(false)),
						],
					)),
				),
				t.returnStatement(t.unaryExpression('!', value, true)),
			);
			block.branch = undefined;
			block.consequentAddresses = [];
			for (const mergedAddr of merged) {
				func.markMergedBlocks(addr, mergedAddr);
			}
			func.markMergedBlocks(addr, joinAddr);
			return true;
		}
	}
	return false;
}
