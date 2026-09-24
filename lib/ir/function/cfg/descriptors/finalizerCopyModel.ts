import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../../utils/set.ts';
import { AddressMap } from '../../../../utils/map.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import { statementFingerprint } from './subgraphMatch.ts';
import type {
	EnclosingFinallyCopyDescriptor,
	ExceptionDescriptor,
	ExceptionRegionForest,
	StatementRangeDescriptor,
} from './exceptions.ts';

// Roles a copied finalizer block can play. Mirrors the copy kinds carried by
// ExceptionDescriptor (`finallyCopies[].kind`, `finallyCopySuffixes[].kind`)
// plus the enclosing-finalizer copies discovered against an outer owner.
export type FinalizerCopyRole =
	| 'normalExit'
	| 'abruptExit'
	| 'catchTrailer'
	| 'suffix'
	| 'enclosing';

export interface FinalizerCopyClassification {
	ownerHandler: BlockAddr;
	role: FinalizerCopyRole;
	skipRanges: StatementRangeDescriptor[];
}

export interface FinalizerCopyModel {
	// Every block that is a copy of some finalizer body (keyed by the copy root),
	// classified by the finalizer it copies and the role it plays.
	copyBlocks: AddressMap<FinalizerCopyClassification>;
	// The genuine finalizer body for each finally handler, bounded to the prefix
	// of `finallyBodyBlocks` that keeps (a superset of) the protection of the
	// handler's landing pad — enclosing-finalizer / nested-catch copies drop that
	// protection and are excluded (fixes G2). Keyed by handler address.
	canonicalBodyByHandler: AddressMap<AddressSet<BlockAddr>>;
	// Embedded enclosing-finalizer copies discovered inside an owner's body that
	// the HandlerGraph never tracked (fixes G1). Populated in Phase 4; empty here.
	embeddedEnclosingCopies: AddressMap<EnclosingFinallyCopyDescriptor[]>;
	// Descriptor handlers that are per-exit-path COPIES of a canonical sibling
	// finalizer (same body fingerprint, but their protected entry lies outside any
	// finalizer's canonical body). The structurer must not open a region for them —
	// the emitter suppresses their statements; opening a region leaves an empty
	// `try {}` (Defect B). Includes the copy's forest descendants (its owned catch).
	copyDescriptorHandlers: AddressSet<BlockAddr>;
}

interface FinalizerCopyModelInput {
	handlers: ExceptionDescriptor[];
	forest: ExceptionRegionForest;
}

// Bound a finalizer's raw `finallyBodyBlocks` to the genuine prefix. Every
// genuine body block keeps a superset of the handlers protecting the landing
// pad; the first block that drops that protection is an enclosing-finalizer or
// nested-catch copy, so we stop there.
function boundedFinalizerBody(
	cfg: ImmutableCFG,
	descriptor: ExceptionDescriptor,
	info: FinalizerCopyModelInput,
): AddressSet<BlockAddr> {
	const body = descriptor.finallyBodyBlocks;
	if (body == null || body.length === 0) {
		return new AddressSet<BlockAddr>();
	}
	const landingProtection =
		cfg.exceptionalSuccessors.get(descriptor.handler) ??
			new AddressSet<BlockAddr>();
	const bounded = new AddressSet<BlockAddr>();
	for (const block of body) {
		if (
			bounded.size > 0 &&
			info.handlers.some((candidate) =>
				candidate !== descriptor &&
				candidate.protectedEntries.has(block) &&
				!isHandlerDescendantOf(
					candidate.handler,
					descriptor.handler,
					info.forest,
				)
			)
		) break;
		const blockProtection = cfg.exceptionalSuccessors.get(block) ??
			new AddressSet<BlockAddr>();
		if (!landingProtection.isSubsetOf(blockProtection)) break;
		bounded.add(block);
	}
	// Never bound away everything: a landing pad with no residual protection
	// (e.g. the outermost finally) keeps its recorded body verbatim.
	if (bounded.size === 0) {
		for (const block of body) bounded.add(block);
	}
	return bounded;
}

function isHandlerDescendantOf(
	handler: BlockAddr,
	ancestor: BlockAddr,
	forest: ExceptionRegionForest,
): boolean {
	let current = forest.parentByHandler.get(handler);
	const seen = new AddressSet<BlockAddr>();
	while (current != null && !seen.has(current)) {
		if (current === ancestor) return true;
		seen.add(current);
		current = forest.parentByHandler.get(current);
	}
	return false;
}

export function buildFinalizerCopyModel(
	cfg: ImmutableCFG,
	info: FinalizerCopyModelInput,
): FinalizerCopyModel {
	const copyBlocks = new AddressMap<FinalizerCopyClassification>();
	const canonicalBodyByHandler = new AddressMap<AddressSet<BlockAddr>>();

	const classify = (
		copyRoot: BlockAddr,
		ownerHandler: BlockAddr,
		role: FinalizerCopyRole,
		skipRanges: StatementRangeDescriptor[] | undefined,
	) => {
		// Genuine structure (a handler or a canonical body block) is never a copy.
		if (structuralBlocks.has(copyRoot)) return;
		// Keep the first classification if the same block is listed twice.
		if (copyBlocks.has(copyRoot)) return;
		copyBlocks.set(copyRoot, {
			ownerHandler,
			role,
			skipRanges: skipRanges ?? [],
		});
	};

	for (const descriptor of info.handlers) {
		if (descriptor.kind !== 'finally') continue;
		canonicalBodyByHandler.set(
			descriptor.handler,
			boundedFinalizerBody(cfg, descriptor, info),
		);
	}

	// Blocks that are genuine structure — any handler's landing pad, or a block in
	// some finalizer's (bounded) canonical body — must never be demoted to a copy,
	// even if they also appear as a copyRoot of another descriptor's suffix list.
	const structuralBlocks = new AddressSet<BlockAddr>();
	for (const descriptor of info.handlers) {
		structuralBlocks.add(descriptor.handler);
	}
	for (const body of canonicalBodyByHandler.values()) {
		for (const block of body) structuralBlocks.add(block);
	}

	for (const descriptor of info.handlers) {
		if (descriptor.kind !== 'finally') continue;
		const canonical = canonicalBodyByHandler.get(descriptor.handler) ??
			new AddressSet<BlockAddr>();
		for (const copy of descriptor.finallyCopies) {
			if (canonical.has(copy.copyRoot)) continue;
			for (const block of copy.copyBlocks ?? [copy.copyRoot]) {
				classify(block, descriptor.handler, copy.kind, copy.skipRanges);
			}
		}
		for (const suffix of descriptor.finallyCopySuffixes) {
			if (canonical.has(suffix.copyRoot)) continue;
			classify(
				suffix.copyRoot,
				descriptor.handler,
				'suffix',
				suffix.skipRanges,
			);
		}
		for (const copy of descriptor.enclosingFinallyCopyRoots) {
			if (canonical.has(copy.tailRoot)) continue;
			classify(copy.tailRoot, copy.owner, 'enclosing', undefined);
		}
	}

	return {
		copyBlocks,
		canonicalBodyByHandler,
		embeddedEnclosingCopies: new AddressMap<
			EnclosingFinallyCopyDescriptor[]
		>(),
		copyDescriptorHandlers: copyDescriptorHandlersOf(
			cfg,
			info,
			canonicalBodyByHandler,
		),
	};
}

// Per-exit-path finalizer copies: Hermes emits one copy of a `try/finally`'s
// finally region per exit path. All copies share the canonical's body
// fingerprint; the canonical is the single one whose protected entry lies inside
// some finalizer's canonical body, the rest are copies. We fingerprint the
// bounded finally body (SSA-temp-normalized via `statementFingerprint`), group
// by it, and mark the non-canonical members — plus their forest descendants (the
// copy's owned catch) — so the structurer can pass them through.
function copyDescriptorHandlersOf(
	cfg: ImmutableCFG,
	info: FinalizerCopyModelInput,
	canonicalBodyByHandler: AddressMap<AddressSet<BlockAddr>>,
): AddressSet<BlockAddr> {
	const canonicalBlocks = new AddressSet<BlockAddr>();
	for (const body of canonicalBodyByHandler.values()) {
		for (const block of body) canonicalBlocks.add(block);
	}
	const inCanonicalPosition = (descriptor: ExceptionDescriptor): boolean => {
		for (const entry of descriptor.protectedEntries) {
			if (canonicalBlocks.has(entry)) return true;
		}
		return false;
	};
	const bodyFingerprint = (blocks: BlockAddr[] | null): string | null => {
		if (blocks == null || blocks.length === 0) return null;
		return blocks
			.map((block) =>
				(cfg.blocks.get(block)?.body ?? [])
					.map(statementFingerprint)
					.join('|')
			)
			.join('#');
	};

	const groups = new Map<string, ExceptionDescriptor[]>();
	for (const descriptor of info.handlers) {
		if (descriptor.kind !== 'finally') continue;
		const bounded = canonicalBodyByHandler.get(descriptor.handler);
		const key = bodyFingerprint(bounded == null ? null : [...bounded]);
		if (key == null) continue;
		let group = groups.get(key);
		if (!group) groups.set(key, group = []);
		group.push(descriptor);
	}

	const copyHandlers = new AddressSet<BlockAddr>();
	for (const group of groups.values()) {
		if (group.length < 2) continue;
		// A copy only exists relative to a canonical: require at least one member in
		// canonical position, otherwise treat none as copies (avoids suppressing a
		// legitimate lone finalizer that coincidentally matches another).
		if (!group.some(inCanonicalPosition)) continue;
		for (const descriptor of group) {
			if (inCanonicalPosition(descriptor)) continue;
			copyHandlers.add(descriptor.handler);
		}
	}

	// Extend to forest descendants: a copy finalizer's owned catch (and anything
	// nested under it) is equally a copy and must be passed through too.
	for (const descriptor of info.handlers) {
		let ancestor = info.forest.parentByHandler.get(descriptor.handler);
		const seen = new AddressSet<BlockAddr>();
		while (ancestor != null && !seen.has(ancestor)) {
			seen.add(ancestor);
			if (copyHandlers.has(ancestor)) {
				copyHandlers.add(descriptor.handler);
				break;
			}
			ancestor = info.forest.parentByHandler.get(ancestor);
		}
	}
	return copyHandlers;
}
