import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import type { Region } from '../regions/region.ts';

export type RegionAt = (
	entry: BlockAddr,
	allowed?: AddressSet<BlockAddr>,
	ownerClosed?: boolean,
) => Region | null;

export function structureStraightLineSequence(
	cfg: ImmutableCFG,
	regionAt?: RegionAt,
): Region {
	return structureStraightLineSequenceFrom(
		cfg,
		cfg.entry,
		undefined,
		regionAt,
	) ?? {
		kind: 'sequence',
		regions: [],
		sourceBlocks: new AddressSet(),
	};
}

export function structureStraightLineSequenceFrom(
	cfg: ImmutableCFG,
	entry: BlockAddr,
	allowed?: AddressSet<BlockAddr>,
	regionAt?: RegionAt,
	sharedEntryRegionAt?: RegionAt,
): Region | null {
	const regions: Region[] = [];
	const consumed = new AddressSet<BlockAddr>();
	let cursor: BlockAddr | undefined = entry;
	let predecessor: BlockAddr | undefined;

	while (cursor != null && !consumed.has(cursor)) {
		if (allowed && !allowed.has(cursor)) {
			const terminal = terminalReference(cfg, cursor, predecessor);
			if (terminal) regions.push(terminal);
			break;
		}
		const block = cfg.blocks.get(cursor);
		if (!block) break;
		consumed.add(cursor);
		const structured: Region | null | undefined = regionAt?.(
			cursor,
			allowed,
		);
		if (structured) {
			regions.push(structured);
			for (const consumedBlock of structured.sourceBlocks) {
				consumed.add(consumedBlock);
			}
			const exit: BlockAddr | null = explicitNormalExit(
				structured,
				allowed,
			) ??
				uniqueForwardExit(cfg, structured.sourceBlocks, allowed);
			if (exit == null || consumed.has(exit)) break;
			cursor = exit;
			continue;
		} else {
			regions.push({
				kind: 'basic',
				body: [],
				sourceBlocks: new AddressSet([cursor]),
			});
		}

		const successors: AddressSet<BlockAddr> =
			cfg.normalSuccessors.get(cursor) ?? new AddressSet<BlockAddr>();
		if (successors.size !== 1) break;
		const [next]: BlockAddr[] = [...successors];
		if ((cfg.normalPredecessors.get(next)?.size ?? 0) !== 1) {
			// A retrying catch is the second predecessor of its protected header.
			// That header is nevertheless the next lexical Region after the prelude.
			// Probe only this graph-proven shape: a general join remains owned by its
			// enclosing branch and must not be pulled into a straight-line sequence.
			if (
				sharedEntryRegionAt &&
				isExceptionRetryEntry(cfg, cursor, next)
			) {
				const retried = sharedEntryRegionAt(next, allowed);
				if (
					retried?.kind === 'tryCatch' &&
					retried.retryLoop?.header === next
				) {
					regions.push(retried);
					for (const consumedBlock of retried.sourceBlocks) {
						consumed.add(consumedBlock);
					}
					const exit = explicitNormalExit(retried, allowed);
					if (exit == null || consumed.has(exit)) break;
					predecessor = undefined;
					cursor = exit;
					continue;
				}
			}
			const terminal = terminalReference(cfg, next, cursor);
			if (terminal) regions.push(terminal);
			break;
		}
		predecessor = cursor;
		cursor = next;
	}

	if (regions.length === 0) return null;
	if (regions.length === 1) return regions[0];
	return {
		kind: 'sequence',
		regions,
		sourceBlocks: consumed,
	};
}

function terminalReference(
	cfg: ImmutableCFG,
	entry: BlockAddr,
	predecessor?: BlockAddr,
): Region | null {
	const handlers = cfg.exceptionalSuccessors.get(entry);
	if (predecessor == null) {
		if ((handlers?.size ?? 0) > 0) return null;
	} else {
		const predecessorHandlers = cfg.exceptionalSuccessors.get(predecessor);
		if (
			(handlers?.size ?? 0) !== (predecessorHandlers?.size ?? 0) ||
			[...handlers ?? []].some((handler) =>
				!predecessorHandlers?.has(handler)
			)
		) return null;
	}
	const block = cfg.blocks.get(entry);
	if (
		!block ||
		(cfg.isScript && block.terminator.kind === 'return') ||
		(block.terminator.kind !== 'return' &&
			block.terminator.kind !== 'throw' &&
			block.terminator.kind !== 'unreachable')
	) return null;
	return {
		kind: 'terminalReference',
		entry,
		edge: predecessor == null
			? undefined
			: { from: predecessor, to: entry, kind: 'normal' },
		sourceBlocks: new AddressSet(),
	};
}

function explicitNormalExit(
	region: Region,
	allowed?: AddressSet<BlockAddr>,
): BlockAddr | null {
	const exit = region.kind === 'tryCatch'
		? region.retryLoop?.normalExit
		: region.kind === 'tryFinally'
		? region.normalExit ??
			region.normalExitCandidates?.find((candidate) =>
				!allowed || allowed.has(candidate)
			)
		: undefined;
	if (exit == null) return null;
	if (allowed && !allowed.has(exit)) return null;
	return exit;
}

function isExceptionRetryEntry(
	cfg: ImmutableCFG,
	prelude: BlockAddr,
	entry: BlockAddr,
): boolean {
	const predecessors = cfg.normalPredecessors.get(entry) ??
		new AddressSet<BlockAddr>();
	if (!predecessors.has(prelude)) return false;
	return [...predecessors].some((predecessor) =>
		predecessor !== prelude &&
		(cfg.exceptionalPredecessors.get(predecessor)?.size ?? 0) > 0 &&
		cfg.normalSuccessors.get(predecessor)?.has(entry) === true
	);
}

function uniqueForwardExit(
	cfg: ImmutableCFG,
	sourceBlocks: AddressSet<BlockAddr>,
	allowed?: AddressSet<BlockAddr>,
): BlockAddr | null {
	const exits = new AddressSet<BlockAddr>();
	for (const block of sourceBlocks) {
		for (const succ of cfg.normalSuccessors.get(block) ?? []) {
			if (sourceBlocks.has(succ)) continue;
			if (allowed && !allowed.has(succ)) continue;
			exits.add(succ);
		}
	}
	return exits.size === 1 ? [...exits][0] : null;
}
