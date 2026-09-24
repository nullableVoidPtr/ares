import * as t from '@babel/types';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { CFGAnalyses } from '../algorithms/mod.ts';
import type { CFGDescriptors } from '../descriptors/mod.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import {
	blockNeedsBranchRegion,
	containsBasicBranch,
	type Region,
	regionCoveredBlocks,
	type SwitchRegionCase,
} from '../regions/region.ts';
import type { RegionAt } from './sequence.ts';
import { structureStraightLineSequenceFrom } from './sequence.ts';
import {
	type CFGCompatibilityTelemetry,
	recordCFGCompatibilityAttempt,
} from '../compatibility.ts';

const MAX_TERMINAL_CASE_FOREST_BLOCKS = 56;

export function tryStructureSwitchRegion(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	regionAt?: RegionAt,
	options: {
		enclosingRegionOwnsCases?: boolean;
		dispatchBlock?: BlockAddr;
		joinOverride?: BlockAddr;
	} = {},
): Extract<Region, { kind: 'switch' }> | null {
	const dispatchBlock = options.dispatchBlock ?? cfg.entry;
	const descriptor = descriptors.switches.switchByDispatch.get(dispatchBlock);
	if (!descriptor) return null;
	const join = options.joinOverride ?? descriptor.join ??
		commonSwitchJoin(descriptor, analyses);
	const joined = structureSwitchRegion(
		cfg,
		analyses,
		descriptors,
		descriptor,
		join,
		regionAt,
		options.enclosingRegionOwnsCases ?? false,
	);
	if (
		join == null ||
		options.enclosingRegionOwnsCases ||
		switchJoinIsCompletelyStructured(cfg, analyses, descriptors, joined)
	) return joined;

	// A common postdominator is only a candidate case boundary. Large switch
	// arms can contain CFG that the recursive reducer cannot represent yet; if
	// the join-aware walk claims that CFG, it prevents the older conservative
	// boundary from leaving it to an enclosing reducer. Preserve that boundary
	// until every case can be represented without a raw branch.
	return structureSwitchRegion(
		cfg,
		analyses,
		descriptors,
		descriptor,
		undefined,
		regionAt,
		options.enclosingRegionOwnsCases ?? false,
	);
}

function structureSwitchRegion(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	descriptor: CFGDescriptors['switches']['switches'][number],
	join: BlockAddr | undefined,
	regionAt?: RegionAt,
	preferOwnedCaseRegion = false,
): Extract<Region, { kind: 'switch' }> {
	const sourceBlocks = new AddressSet<BlockAddr>([
		descriptor.dispatchBlock,
		...(descriptor.coveredBlocks ?? []),
	]);
	const caseGroups = switchCaseGroups(descriptor);
	const caseBodies = caseGroups.map((group, index) => {
		const switchCase = group.at(-1)!;
		const nextCase = caseGroups[index + 1]?.[0];
		return descriptor.kind !== 'terminator' &&
				nextCase?.target === switchCase.target
			? emptyCaseRegion()
			: regionForTarget(
				cfg,
				switchCase.target,
				join,
				analyses,
				descriptors,
				descriptor.dispatchBlock,
				regionAt,
				preferOwnedCaseRegion,
			);
	});
	let defaultBody = regionForTarget(
		cfg,
		descriptor.defaultTarget,
		join,
		analyses,
		descriptors,
		descriptor.dispatchBlock,
		regionAt,
		preferOwnedCaseRegion,
	);
	const arms = [...caseBodies, defaultBody];
	for (const arm of arms) {
		for (const block of arm.sourceBlocks) sourceBlocks.add(block);
	}
	if (join == null && regionAt) {
		appendCaseContinuations(cfg, descriptor, arms, sourceBlocks, regionAt);
		for (const [index, arm] of arms.entries()) {
			if (index < caseBodies.length) caseBodies[index] = arm;
			else defaultBody = arm;
			for (const block of arm.sourceBlocks) sourceBlocks.add(block);
		}
	}
	const cases: SwitchRegionCase[] = caseGroups.map((group, index) => {
		const switchCase = group.at(-1)!;
		const nextCase = caseGroups[index + 1]?.[0];
		const body = caseBodies[index]!;
		return {
			test: switchCase.test ? t.cloneNode(switchCase.test, true) : null,
			aliases: group.slice(0, -1).flatMap((alias) =>
				alias.test ? [t.cloneNode(alias.test, true)] : []
			),
			target: switchCase.target,
			source: switchCase.source,
			prefix: switchCase.prefix?.map((stmt) => t.cloneNode(stmt, true)),
			body,
			completion: switchCaseCompletion(
				cfg,
				switchCase.target,
				nextCase?.target,
				body,
				join,
				preferOwnedCaseRegion,
			),
		};
	});

	return {
		kind: 'switch',
		header: descriptor.dispatchBlock,
		prelude: descriptor.prelude?.map((statement) =>
			t.cloneNode(statement, true)
		),
		discriminant: t.cloneNode(descriptor.discriminant, true),
		join,
		cases,
		defaultTarget: descriptor.defaultTarget,
		defaultSource: descriptor.defaultSource,
		defaultBody,
		sourceBlocks,
	};
}

/**
 * Sequence each case with the Region at its own continuation.
 *
 * A switch with no common postdominator has one continuation per arm instead of
 * a shared one. The switch owns only its dispatch chain and its case bodies, so
 * such a continuation is reached from that arm alone and belongs inside it;
 * leaving it out ships a Region that stops at the case boundary and drops
 * everything below every arm.
 *
 * A continuation more than one arm reaches is the switch's shared join and is
 * left to the enclosing sequence, which is the existing single-join path. The
 * dispatch block and the case targets are already owned here, and a composed
 * tail that overlaps another arm would emit the same blocks twice, so both are
 * declined.
 */
function appendCaseContinuations(
	cfg: ImmutableCFG,
	descriptor: CFGDescriptors['switches']['switches'][number],
	arms: Region[],
	switchBlocks: AddressSet<BlockAddr>,
	regionAt: RegionAt,
): void {
	const owned = new AddressSet<BlockAddr>([
		descriptor.dispatchBlock,
		descriptor.defaultTarget,
		...descriptor.cases.map((switchCase) => switchCase.target),
	]);
	const continuations = new Map<number, BlockAddr>();
	const shared = new AddressSet<BlockAddr>();
	for (const [index, arm] of arms.entries()) {
		if (arm.sourceBlocks.size === 0) continue;
		const outside = [...regionNormalExits(cfg, arm.sourceBlocks)].filter(
			(exit) => !switchBlocks.has(exit) && !owned.has(exit),
		);
		if (outside.length !== 1) continue;
		const continuation = outside[0]!;
		if ([...continuations.values()].includes(continuation)) {
			shared.add(continuation);
			continue;
		}
		continuations.set(index, continuation);
	}
	const claimed = new AddressSet<BlockAddr>(switchBlocks);
	for (const [index, continuation] of continuations) {
		if (shared.has(continuation)) continue;
		// A block a sibling arm can also reach is shared continuation: it belongs
		// to whatever encloses the switch. Bound the tail away from those blocks
		// so it treats them as its boundary instead of owning them in one case.
		const foreign = blocksReachedByOtherArms(
			cfg,
			arms,
			index,
			switchBlocks,
			continuations,
		);
		const allowed = new AddressSet<BlockAddr>(
			[...reachableFrom(cfg, continuation)].filter((block) =>
				!foreign.has(block) && !claimed.has(block)
			),
		);
		if (!allowed.has(continuation)) continue;
		const tail = regionAt(continuation, allowed);
		if (!tail || tail.sourceBlocks.size === 0) continue;
		// A tail that leaves a branch unowned is not an improvement on leaving the
		// continuation to the enclosing composition: the case would then carry a
		// Basic Region over a conditional and defeat the whole switch candidate.
		if (containsBasicBranch(tail, cfg)) continue;
		const covered = regionCoveredBlocks(tail);
		if (
			[...covered].some((block) =>
				claimed.has(block) || foreign.has(block)
			)
		) continue;
		for (const block of covered) claimed.add(block);
		const body = arms[index]!;
		arms[index] = {
			kind: 'sequence',
			regions: [body, tail],
			sourceBlocks: new AddressSet([
				...body.sourceBlocks,
				...tail.sourceBlocks,
			]),
		};
	}
}

function reachableFrom(
	cfg: ImmutableCFG,
	entry: BlockAddr,
): AddressSet<BlockAddr> {
	const reached = new AddressSet<BlockAddr>();
	const pending = [entry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (reached.has(address) || !cfg.blocks.has(address)) continue;
		reached.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
	}
	return reached;
}

/**
 * Blocks the switch's other arms can reach, stopping at blocks the switch
 * already owns and at the other arms' own continuations. What remains is
 * genuinely shared: no single case may own it.
 */
function blocksReachedByOtherArms(
	cfg: ImmutableCFG,
	arms: readonly Region[],
	index: number,
	switchBlocks: AddressSet<BlockAddr>,
	continuations: ReadonlyMap<number, BlockAddr>,
): AddressSet<BlockAddr> {
	const stops = new AddressSet<BlockAddr>(switchBlocks);
	for (const [other, continuation] of continuations) {
		if (other !== index) stops.add(continuation);
	}
	const pending: BlockAddr[] = [];
	for (const [other, arm] of arms.entries()) {
		if (other === index) continue;
		for (const block of arm.sourceBlocks) {
			for (const successor of cfg.normalSuccessors.get(block) ?? []) {
				pending.push(successor);
			}
		}
	}
	const reached = new AddressSet<BlockAddr>();
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (reached.has(address) || stops.has(address)) continue;
		reached.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
	}
	return reached;
}

function switchJoinIsCompletelyStructured(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	region: Extract<Region, { kind: 'switch' }>,
): boolean {
	if (region.join == null) return true;
	const bodies = new Map<BlockAddr, Region>();
	for (const switchCase of region.cases) {
		// Repeated compare-chain targets deliberately leave the earlier label
		// empty. The final label owns their shared body.
		bodies.set(switchCase.target, switchCase.body);
	}
	bodies.set(region.defaultTarget, region.defaultBody);
	for (const [target, body] of bodies) {
		if (target === region.join) continue;
		const allowed = collectCaseLikeBody(
			cfg,
			target,
			analyses,
			descriptors,
			region.join,
		);
		const covered = regionCoveredBlocks(body);
		if (
			!body.sourceBlocks.isSubsetOf(allowed) ||
			!allowed.isSubsetOf(covered) ||
			containsBasicBranch(body, cfg)
		) return false;
	}
	return true;
}

function switchCaseGroups(
	descriptor: CFGDescriptors['switches']['switches'][number],
): Array<CFGDescriptors['switches']['switches'][number]['cases']> {
	if (descriptor.kind !== 'terminator') {
		return descriptor.cases.map((switchCase) => [switchCase]);
	}
	const groups = new Map<BlockAddr, typeof descriptor.cases>();
	for (const switchCase of descriptor.cases) {
		const group = groups.get(switchCase.target);
		if (group) group.push(switchCase);
		else groups.set(switchCase.target, [switchCase]);
	}
	return [...groups.values()];
}

function emptyCaseRegion(): Region {
	return {
		kind: 'sequence',
		regions: [],
		sourceBlocks: new AddressSet<BlockAddr>(),
	};
}

function regionForTarget(
	cfg: ImmutableCFG,
	target: BlockAddr,
	join: BlockAddr | undefined,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	dispatchBlock: BlockAddr,
	regionAt?: RegionAt,
	preferOwnedRegion = false,
): Region {
	if (target === join) return emptyCaseRegion();
	// A loop/exception owner can model exits which are deliberately not closed in
	// the whole-function CFG (for example, an early return from a switch case in a
	// nested for-in). Prefer that bounded representation before applying the
	// generic closed-terminal-forest requirement.
	if (preferOwnedRegion && regionAt) {
		const owned = regionAt(target);
		if (owned && (join == null || !owned.sourceBlocks.has(join))) {
			return owned;
		}
	}
	if (join == null && cfg.blocks.size <= MAX_TERMINAL_CASE_FOREST_BLOCKS) {
		const terminalForest = regionAt?.(target);
		if (
			terminalForest &&
			isClosedTerminalForest(terminalForest, cfg)
		) return terminalForest;
	}
	const allowed = collectCaseLikeBody(
		cfg,
		target,
		analyses,
		descriptors,
		join,
	);
	// The collector declines a target other paths also reach: it belongs to
	// whatever encloses the switch, not to this case. The case is then an empty
	// arm that resumes there, and structuring a body for a block the case does
	// not own only produces a fallback.
	if (!allowed.has(target)) return emptyCaseRegion();
	const body = structureStraightLineSequenceFrom(
		cfg,
		target,
		allowed,
		(childEntry, childAllowed) =>
			childEntry === dispatchBlock
				? null
				: regionAt?.(childEntry, childAllowed ?? allowed) ?? null,
	);
	if (body) {
		return join == null ? body : stripJoinTerminalReferences(body, join);
	}
	recordCFGCompatibilityAttempt(
		descriptors.compatibility,
		'local-fallback-region',
		target,
		'switch case is not a straight-line sequence yet',
	);
	const fallback: Region = {
		kind: 'fallback',
		entry: target,
		sourceBlocks: allowed,
		reason: 'switch case is not a straight-line sequence yet',
	};
	return join == null
		? fallback
		: stripJoinTerminalReferences(fallback, join);
}

/**
 * A terminal join can look like a shareable terminal leaf when it sits just
 * outside a case's allowed body. It is still the switch continuation, not case
 * ownership: retain the CFG edge for completion/Phi handling but remove the
 * speculative terminal reference so the continuation is emitted once.
 */
function stripJoinTerminalReferences(
	region: Region,
	join: BlockAddr,
): Region {
	if (region.kind === 'terminalReference' && region.entry === join) {
		return emptyCaseRegion();
	}
	switch (region.kind) {
		case 'sequence':
			return {
				...region,
				regions: region.regions.map((child) =>
					stripJoinTerminalReferences(child, join)
				),
			};
		case 'if':
			return {
				...region,
				consequent: stripJoinTerminalReferences(
					region.consequent,
					join,
				),
				alternate: stripJoinTerminalReferences(region.alternate, join),
			};
		case 'switch':
			return {
				...region,
				cases: region.cases.map((switchCase) => ({
					...switchCase,
					body: stripJoinTerminalReferences(switchCase.body, join),
				})),
				defaultBody: stripJoinTerminalReferences(
					region.defaultBody,
					join,
				),
			};
		case 'tryCatch':
			return {
				...region,
				body: stripJoinTerminalReferences(region.body, join),
				handler: stripJoinTerminalReferences(region.handler, join),
			};
		case 'tryFinally':
			return {
				...region,
				body: stripJoinTerminalReferences(region.body, join),
				finalizer: stripJoinTerminalReferences(region.finalizer, join),
			};
		case 'loop':
			return {
				...region,
				body: stripJoinTerminalReferences(region.body, join),
			};
		default:
			return region;
	}
}

/**
 * A switch with terminal cases has no common postdominator, but a case can
 * still own an arbitrarily structured closed subgraph (including loops). The
 * recursive Region is safe when every represented normal edge stays inside
 * its coverage and at least one covered leaf is genuinely terminal.
 */
export function isClosedTerminalForest(
	region: Region,
	cfg: ImmutableCFG,
): boolean {
	if (region.kind === 'fallback') return false;
	const covered = regionCoveredBlocks(region);
	let hasTerminal = false;
	for (const address of covered) {
		const block = cfg.blocks.get(address);
		if (!block) return false;
		if (
			block.terminator.kind === 'return' ||
			block.terminator.kind === 'throw' ||
			block.terminator.kind === 'unreachable'
		) hasTerminal = true;
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (!covered.has(successor)) return false;
		}
	}
	return hasTerminal;
}

function collectCaseLikeBody(
	cfg: ImmutableCFG,
	target: BlockAddr,
	analyses: CFGAnalyses,
	descriptors: CFGDescriptors,
	join?: BlockAddr,
): AddressSet<BlockAddr> {
	const body = new AddressSet<BlockAddr>();
	const stack = [target];
	while (stack.length > 0) {
		const addr = stack.pop()!;
		if (addr === join) continue;
		if (body.has(addr) || !cfg.blocks.has(addr)) continue;
		if (join == null) {
			const predecessors = cfg.normalPredecessors.get(addr) ??
				new AddressSet<BlockAddr>();
			// A block other paths also reach is the switch's shared
			// continuation, not this case's body — including the case target
			// itself. Claiming it here takes it from the Region that has to
			// place it for every path, and carries that claim into everything
			// beyond it.
			if (predecessors.size > 1) continue;
		} else if (!analyses.dominators.dominates(target, addr)) {
			continue;
		}
		body.add(addr);
		const successors = cfg.normalSuccessors.get(addr) ??
			new AddressSet<BlockAddr>();
		if (join == null) {
			// A case that branches still owns whatever only it can reach: the
			// predecessor test above stops the walk at any join, so expanding
			// through the branch keeps a terminal arm and its fall-through
			// inside the case instead of dropping both.
			//
			// The target itself is exempt from that test so a case always owns
			// its entry block. Expanding past one that other paths also reach
			// would carry the exemption into the shared continuation and claim
			// the rest of the function with it.
			if (successors.size === 0) continue;
			const targetPredecessors = cfg.normalPredecessors.get(addr) ??
				new AddressSet<BlockAddr>();
			if (addr === target && targetPredecessors.size > 1) continue;
		}
		for (const successor of successors) {
			stack.push(successor);
		}
	}
	return withContainedHandlerBlocks(body, cfg, descriptors, join);
}

/**
 * A case that contains a whole `try` owns its handler as well.
 *
 * Nothing branches to a handler, so the normal-successor walk above never
 * reaches one, and a case body that excludes it can never open the exception
 * Region for the range: the handler lies outside the bounded set the recursion
 * is allowed to claim. Only handlers whose protected range is wholly inside the
 * case qualify — a range shared with code beyond it belongs to whatever
 * encloses the switch.
 */
function withContainedHandlerBlocks(
	body: AddressSet<BlockAddr>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	join?: BlockAddr,
): AddressSet<BlockAddr> {
	const widened = new AddressSet<BlockAddr>(body);
	const stopBlocks = join == null
		? undefined
		: new AddressSet<BlockAddr>([join]);
	// A handler may itself be protected by another range inside the case, so
	// admitting one can qualify the next.
	for (let changed = true; changed;) {
		changed = false;
		for (const descriptor of descriptors.exceptions.handlers) {
			if (
				descriptor.protectedBlocks.size === 0 ||
				widened.has(descriptor.handler) ||
				!descriptor.protectedBlocks.isSubsetOf(widened)
			) continue;
			const owned = handlerOwnedBlocks(
				descriptor.handler,
				cfg,
				widened,
				stopBlocks,
			);
			if (!owned) continue;
			for (const block of owned) widened.add(block);
			changed = true;
		}
	}
	return widened;
}

/**
 * Blocks a contained handler brings into a bounded structured scope: itself
 * plus everything only it reaches, stopping at blocks the enclosing construct
 * owns separately. `null` when the walk meets a block another path reaches, so
 * admitting the handler would steal a shared continuation.
 */
export function handlerOwnedBlocks(
	handler: BlockAddr,
	cfg: ImmutableCFG,
	body: AddressSet<BlockAddr>,
	stopBlocks?: ReadonlySet<BlockAddr>,
): AddressSet<BlockAddr> | null {
	const owned = new AddressSet<BlockAddr>();
	const pending = [handler];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (
			stopBlocks?.has(address) || body.has(address) || owned.has(address)
		) {
			continue;
		}
		if (!cfg.blocks.has(address)) return null;
		for (const predecessor of cfg.normalPredecessors.get(address) ?? []) {
			if (!body.has(predecessor) && !owned.has(predecessor)) return null;
		}
		owned.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
	}
	return owned.size === 0 ? null : owned;
}

function commonSwitchJoin(
	descriptor: CFGDescriptors['switches']['switches'][number],
	analyses: CFGAnalyses,
): BlockAddr | undefined {
	const targets = new AddressSet<BlockAddr>([
		...descriptor.cases.map((switchCase) => switchCase.target),
		descriptor.defaultTarget,
	]);
	const common = nearestCommonPostdominator([...targets], analyses);
	if (common != null) return common;

	// A switch can have a common continuation for every ordinary case while one
	// or more cases return or throw. Including those abrupt targets in the NCPD
	// query erases that useful join and forces each ordinary case to duplicate the
	// shared suffix. Keep direct abrupt arms inside the switch and let the other
	// cases break to their common continuation.
	const ordinaryTargets = [...targets].filter((target) => {
		const terminator = analyses.cfg.blocks.get(target)?.terminator;
		const abrupt = terminator?.kind === 'throw' ||
			(terminator?.kind === 'return' && !analyses.cfg.isScript) ||
			terminator?.kind === 'unreachable';
		if (!abrupt) return true;
		return [...targets].some((other) =>
			other !== target &&
			analyses.postdominators.postdominates(target, other)
		);
	});
	if (ordinaryTargets.length < 2 || ordinaryTargets.length === targets.size) {
		return undefined;
	}
	return nearestCommonPostdominator(ordinaryTargets, analyses) ?? undefined;
}

function nearestCommonPostdominator(
	targets: BlockAddr[],
	analyses: CFGAnalyses,
): BlockAddr | null {
	const [first, ...rest] = targets;
	if (first == null) return null;
	let join: BlockAddr | null = first;
	for (const target of rest) {
		join = analyses.postdominators.nearestCommonPostdominator(join, target);
		if (join == null) return null;
	}
	return join;
}

function switchCaseCompletion(
	cfg: ImmutableCFG,
	target: BlockAddr,
	nextTarget: BlockAddr | undefined,
	body: Region,
	join: BlockAddr | undefined,
	allowRepresentedAbruptExits = false,
): SwitchRegionCase['completion'] {
	if (nextTarget === target) return 'fallthrough';
	if (join == null) return undefined;
	if (target === join) return 'break';
	const exits = regionNormalExits(cfg, body.sourceBlocks);
	if (exits.size === 0) return undefined;
	if (nextTarget != null && exits.size === 1 && exits.has(nextTarget)) {
		return 'fallthrough';
	}
	// A bounded owner such as a natural loop represents early return/break edges
	// inside the case body. Those abrupt paths do not prevent the remaining
	// normal path from completing at the switch join.
	if (allowRepresentedAbruptExits) {
		if (nextTarget != null && exits.has(nextTarget)) return 'fallthrough';
		if (exits.has(join)) return 'break';
	}
	return exits.size === 1 && exits.has(join) ? 'break' : undefined;
}

function regionNormalExits(
	cfg: ImmutableCFG,
	blocks: AddressSet<BlockAddr>,
): AddressSet<BlockAddr> {
	const exits = new AddressSet<BlockAddr>();
	for (const block of blocks) {
		for (const successor of cfg.normalSuccessors.get(block) ?? []) {
			if (!blocks.has(successor)) exits.add(successor);
		}
	}
	return exits;
}
