import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { CFGEdge, ImmutableCFG } from '../immutableCFG.ts';
import type { DeferredExit } from '../regions/region.ts';
import type { DominatorInfo } from './dominators.ts';
import type { PostDominatorInfo } from './postdominators.ts';

export interface SESERegion {
	entry: BlockAddr;
	exit: BlockAddr;
	body: AddressSet<BlockAddr>;
}

export interface WeakSESERegion {
	entry: BlockAddr;
	normalExit?: BlockAddr;
	body: AddressSet<BlockAddr>;
	deferredExits: DeferredExit[];
}

export interface SESEValidationFailure {
	reason:
		| 'entryDoesNotDominate'
		| 'exitDoesNotPostdominate'
		| 'incomingEdge'
		| 'outgoingEdge';
	edge?: CFGEdge;
	block?: BlockAddr;
}

export interface SESEContext {
	cfg: ImmutableCFG;
	dominators: DominatorInfo;
	postdominators: PostDominatorInfo;
}

export interface WeakSESEOptions {
	/**
	 * Keep a cyclic arm bounded by dominance instead of absorbing every node
	 * reachable before the declared normal exit. The caller must have separately
	 * established ownership of every reachable loop.
	 */
	boundedCyclicArm?: boolean;
}

export function findSESE(
	entry: BlockAddr,
	exit: BlockAddr,
	ctx: SESEContext,
): SESERegion | null {
	if (!ctx.cfg.blocks.has(entry) || !ctx.cfg.blocks.has(exit)) {
		return null;
	}
	const body = collectRegionBody(entry, exit, ctx.cfg);
	const region = { entry, exit, body };
	return validateSESE(region, ctx).length === 0 ? region : null;
}

export function validateSESE(
	region: SESERegion,
	ctx: SESEContext,
): SESEValidationFailure[] {
	const failures: SESEValidationFailure[] = [];
	for (const block of region.body) {
		if (
			block !== region.entry &&
			!ctx.dominators.dominates(region.entry, block)
		) {
			failures.push({
				reason: 'entryDoesNotDominate',
				block,
			});
		}
		if (
			block !== region.exit &&
			(ctx.cfg.normalSuccessors.get(block)?.size ?? 0) > 0 &&
			!ctx.postdominators.postdominates(region.exit, block)
		) {
			failures.push({
				reason: 'exitDoesNotPostdominate',
				block,
			});
		}
	}

	for (const edge of ctx.cfg.normalEdges()) {
		const fromInside = region.body.has(edge.from);
		const toInside = region.body.has(edge.to);
		if (!fromInside && toInside && edge.to !== region.entry) {
			failures.push({ reason: 'incomingEdge', edge });
		}
		if (fromInside && !toInside && edge.to !== region.exit) {
			failures.push({ reason: 'outgoingEdge', edge });
		}
	}
	return failures;
}

export function findWeakSESE(
	entry: BlockAddr,
	normalExit: BlockAddr | undefined,
	ctx: SESEContext,
	options: WeakSESEOptions = {},
): WeakSESERegion | null {
	if (!ctx.cfg.blocks.has(entry)) return null;
	const body = normalExit == null
		? collectReachableUntilBoundary(entry, new AddressSet(), ctx.cfg)
		: options.boundedCyclicArm
		? collectDominatedRegionBody(entry, normalExit, ctx)
		: ctx.cfg.blocks.size > 96 || hasNormalCycle(ctx.cfg)
		? collectRegionBody(entry, normalExit, ctx.cfg)
		: collectDominatedRegionBody(entry, normalExit, ctx);
	// An exception handler is reached only by an exceptional edge, so the normal
	// walks above never see it. A region containing a protected block has to
	// contain its handler too, or the recursive builder cannot form the
	// try/catch and falls back to a Basic Region that drops the handler
	// entirely.
	const handlers = new AddressSet<BlockAddr>();
	for (let changed = true; changed;) {
		changed = false;
		for (const from of [...body, ...handlers]) {
			for (
				const to of ctx.cfg.exceptionalSuccessors.get(from) ?? []
			) {
				if (
					body.has(to) || handlers.has(to) || to === normalExit ||
					!exceptionHandlerOwnedBy(body, handlers, to, ctx.cfg)
				) continue;
				handlers.add(to);
				changed = true;
			}
		}
		for (const from of [...handlers]) {
			for (const to of ctx.cfg.normalSuccessors.get(from) ?? []) {
				if (body.has(to) || handlers.has(to) || to === normalExit) {
					continue;
				}
				handlers.add(to);
				changed = true;
			}
		}
	}
	const deferredExits: DeferredExit[] = [];
	for (const from of body) {
		for (const to of ctx.cfg.normalSuccessors.get(from) ?? []) {
			if (body.has(to)) continue;
			if (normalExit != null && to === normalExit) continue;
			deferredExits.push({
				kind: 'toJoin',
				edge: { from, to, kind: 'normal' },
				target: to,
				actions: [],
			});
		}
	}
	for (const block of body) {
		if (block === entry) continue;
		if (!ctx.dominators.dominates(entry, block)) return null;
	}
	// Handler blocks are entered only by an exceptional edge, so normal-graph
	// dominance says nothing about them; they belong to the region because the
	// protected block they guard does.
	for (const block of handlers) body.add(block);
	return { entry, normalExit, body, deferredExits };
}

function exceptionHandlerOwnedBy(
	body: AddressSet<BlockAddr>,
	handlers: AddressSet<BlockAddr>,
	handler: BlockAddr,
	cfg: ImmutableCFG,
): boolean {
	const protectedPredecessors = cfg.exceptionalPredecessors.get(handler);
	return protectedPredecessors != null && protectedPredecessors.size > 0 &&
		[...protectedPredecessors].every((predecessor) =>
			body.has(predecessor) || handlers.has(predecessor)
		);
}

function hasNormalCycle(cfg: ImmutableCFG): boolean {
	const visiting = new AddressSet<BlockAddr>();
	const visited = new AddressSet<BlockAddr>();
	const visit = (address: BlockAddr): boolean => {
		if (visiting.has(address)) return true;
		if (visited.has(address)) return false;
		visiting.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (visit(successor)) return true;
		}
		visiting.delete(address);
		visited.add(address);
		return false;
	};
	for (const address of cfg.blocks.keys()) {
		if (visit(address)) return true;
	}
	return false;
}

function collectDominatedRegionBody(
	entry: BlockAddr,
	exit: BlockAddr,
	ctx: SESEContext,
): AddressSet<BlockAddr> {
	const body = new AddressSet<BlockAddr>();
	const pending = [entry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (
			address === exit || body.has(address) ||
			!ctx.cfg.blocks.has(address)
		) continue;
		// A shared continuation can be reached from this arm and from outside it.
		// Keep it as a deferred boundary instead of absorbing it into an arm that
		// does not dominate it.
		if (
			address !== entry &&
			!ctx.dominators.dominates(entry, address)
		) continue;
		body.add(address);
		for (const successor of ctx.cfg.normalSuccessors.get(address) ?? []) {
			if (!body.has(successor)) pending.push(successor);
		}
	}
	return body;
}

function collectRegionBody(
	entry: BlockAddr,
	exit: BlockAddr,
	cfg: ImmutableCFG,
): AddressSet<BlockAddr> {
	return collectReachableUntilBoundary(entry, new AddressSet([exit]), cfg);
}

function collectReachableUntilBoundary(
	entry: BlockAddr,
	boundaries: AddressSet<BlockAddr>,
	cfg: ImmutableCFG,
): AddressSet<BlockAddr> {
	const body = new AddressSet<BlockAddr>();
	const stack = [entry];
	while (stack.length > 0) {
		const addr = stack.pop()!;
		if (body.has(addr) || boundaries.has(addr) || !cfg.blocks.has(addr)) {
			continue;
		}
		body.add(addr);
		for (const succ of cfg.normalSuccessors.get(addr) ?? []) {
			if (!body.has(succ)) stack.push(succ);
		}
	}
	return body;
}
