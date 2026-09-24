import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../../utils/set.ts';
import * as t from '@babel/types';
import type { IRFunction } from '../../mod.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import {
	buildFinalizerCopyModel,
	type FinalizerCopyModel,
} from './finalizerCopyModel.ts';
import { statementFingerprint } from './subgraphMatch.ts';
import { statementMatchesFinalizerPrefix } from '../../finalizer.ts';
import type { HandlerGraphFinalizerEdgeAction } from '../../except/mod.ts';

export interface ExceptionDescriptor {
	handler: BlockAddr;
	kind: 'catch' | 'finally';
	protectedBlocks: AddressSet<BlockAddr>;
	protectedEntries: AddressSet<BlockAddr>;
	catchBody: AddressSet<BlockAddr> | null;
	canonicalFinallyAddress: BlockAddr | null;
	canonicalFinallyOwnership: FinallyOwnershipProof | null;
	finallyCopyRoots: AddressSet<BlockAddr>;
	finallyBodyBlocks: BlockAddr[] | null;
	// The genuine finalizer body, bounded to the prefix of `finallyBodyBlocks`
	// that keeps the landing pad's exceptional protection (fixes G2). Derived from
	// the finalizer-copy model; `finallyBodyBlocks` is left untouched. Null for
	// non-finally descriptors and when no body is recorded.
	boundedFinallyBodyBlocks: BlockAddr[] | null;
	finallyCopies: FinallyCopyDescriptor[];
	finallyCopySuffixes: FinallyCopySuffixDescriptor[];
	enclosingFinallyCopyRoots: EnclosingFinallyCopyDescriptor[];
}

export interface FinallyOwnershipProof {
	finallyAddress: BlockAddr;
	protectsCatch: boolean;
	missingProtectedBlocks: AddressSet<BlockAddr>;
	valid: boolean;
}

export interface ExceptionRegionForest {
	roots: ExceptionRegionForestNode[];
	nodeByHandler: Map<BlockAddr, ExceptionRegionForestNode>;
	parentByHandler: Map<BlockAddr, BlockAddr>;
}

export interface ExceptionRegionForestNode {
	descriptor: ExceptionDescriptor;
	children: ExceptionRegionForestNode[];
}

export interface FinallyCopyDescriptor {
	canonical: BlockAddr;
	copyRoot: BlockAddr;
	next: BlockAddr | null;
	kind: 'normalExit' | 'abruptExit' | 'catchTrailer';
	copyBlocks?: BlockAddr[];
	skipRanges?: StatementRangeDescriptor[];
}

export interface EnclosingFinallyCopyDescriptor {
	owner: BlockAddr;
	copyRoot: BlockAddr;
	tailRoot: BlockAddr;
}

export interface FinallyCopySuffixDescriptor {
	canonical: BlockAddr;
	copyRoot: BlockAddr;
	ownerBlock: BlockAddr;
	next: BlockAddr | null;
	kind: 'tryTrailer' | 'catchTrailer' | 'abruptExitTrailer' | 'canonical';
	statements: t.Statement[];
	skipRanges?: StatementRangeDescriptor[];
}

export interface StatementRangeDescriptor {
	block: BlockAddr;
	start: number;
	end: number;
}

export interface ExceptionDescriptorInfo {
	handlers: ExceptionDescriptor[];
	handlerByAddress: Map<BlockAddr, ExceptionDescriptor>;
	forest: ExceptionRegionForest;
	/**
	 * Compiler-split catch landing pads represented by one enclosing catch.
	 *
	 * Keys are duplicate child handlers; values are their canonical parent.
	 */
	equivalentCatchHandlerAliases: Map<BlockAddr, BlockAddr>;
	finalizerCopyModel: FinalizerCopyModel;
	finalizerEdgeActions: HandlerGraphFinalizerEdgeAction[];
	/** Ordinary for-of syntax may subsume its IteratorClose rethrow landing pad. */
	iteratorCleanupActionElision: boolean;
	/**
	 * Cleanup landing pads a recovered `for...of` Region represents.
	 *
	 * Filled once the loops are known, which is after descriptor recovery, and
	 * read wherever a Region would otherwise be opened for one: the loop syntax
	 * already carries the IteratorClose the handler performs.
	 */
	elidedIteratorCleanupHandlers: AddressSet<BlockAddr>;
}

/**
 * Blocks whose statements a represented finalizer emits instead.
 *
 * Hermes copies the finalizer onto every exit path out of a protected range.
 * The `finally` clause emits those statements once, so the copies are covered
 * by the Region tree while owning no emission of their own -- any ownership
 * measure taken over blocks has to account for them.
 */
export function finalizerCopyBlocks(
	handlers: readonly ExceptionDescriptor[],
): AddressSet<BlockAddr> {
	const blocks = new AddressSet<BlockAddr>();
	for (const descriptor of handlers) {
		for (const root of descriptor.finallyCopyRoots) blocks.add(root);
		for (const copy of descriptor.finallyCopies) {
			blocks.add(copy.copyRoot);
			for (const block of copy.copyBlocks ?? []) blocks.add(block);
		}
		for (const suffix of descriptor.finallyCopySuffixes) {
			blocks.add(suffix.copyRoot);
		}
	}
	return blocks;
}

/**
 * Return the iterator register consumed by Hermes' exceptional for-of cleanup
 * landing pad, or null when the handler is not that exact protocol.
 *
 * Kept with the exception descriptors so structuring and emission use the same
 * proof before allowing `for...of` syntax to subsume a protected range.
 */
export function iteratorCleanupRethrowRegister(
	body: readonly t.Statement[],
): string | null {
	if (body.length !== 3) return null;
	const [catchStatement, closeStatement, throwStatement] = body;
	if (
		!t.isVariableDeclaration(catchStatement) ||
		catchStatement.declarations.length !== 1
	) return null;
	const [catchDeclaration] = catchStatement.declarations;
	if (
		!t.isIdentifier(catchDeclaration.id) ||
		!t.isCallExpression(catchDeclaration.init) ||
		!t.isV8IntrinsicIdentifier(catchDeclaration.init.callee, {
			name: 'Catch',
		})
	) return null;
	if (
		!t.isExpressionStatement(closeStatement) ||
		!t.isCallExpression(closeStatement.expression) ||
		!t.isV8IntrinsicIdentifier(closeStatement.expression.callee, {
			name: 'IteratorClose',
		}) ||
		closeStatement.expression.arguments.length !== 2
	) return null;
	const [iterator, ignoreException] = closeStatement.expression.arguments;
	if (
		!t.isIdentifier(iterator) ||
		!t.isBooleanLiteral(ignoreException, { value: true }) ||
		!t.isThrowStatement(throwStatement) ||
		!t.isIdentifier(throwStatement.argument, {
			name: catchDeclaration.id.name,
		})
	) return null;
	return iterator.name;
}

export function recoverExceptionDescriptors(
	cfg: ImmutableCFG,
	func?: IRFunction,
): ExceptionDescriptorInfo {
	const handlers: ExceptionDescriptor[] = [];
	const handlerByAddress = new Map<BlockAddr, ExceptionDescriptor>();
	let forest: ExceptionRegionForest = emptyExceptionRegionForest();
	if (func) {
		for (
			const descriptor of func.exceptions.structuredRegionDescriptors()
		) {
			if (descriptor.protectedBlocks.size === 0) continue;
			if (!descriptorPrimaryBlocksExist(cfg, descriptor)) continue;
			if (
				descriptor.canonicalFinallyOwnership != null &&
				!descriptor.canonicalFinallyOwnership.valid
			) {
				cfg.diagnostics.add({
					kind: 'exceptionRegionConflict',
					entry: descriptor.handler,
					allowed: descriptor.protectedBlocks,
					message: finallyOwnershipDiagnosticMessage(
						descriptor.handler,
						descriptor.canonicalFinallyOwnership,
					),
				});
			}
			const recovered: ExceptionDescriptor = {
				handler: descriptor.handler,
				kind: descriptor.kind,
				// Normalization merges and removes blocks after the IR-level
				// descriptor was built. A protected block the CFG no longer has
				// can never be contained by any allowed set, so keeping it makes
				// every containment test fail for the rest of the build and the
				// handler is never structured.
				protectedBlocks: new AddressSet(
					[...descriptor.protectedBlocks].filter((block) =>
						cfg.blocks.has(block)
					),
				),
				protectedEntries: new AddressSet(
					[...descriptor.protectedEntries].filter((block) =>
						cfg.blocks.has(block)
					),
				),
				catchBody: descriptor.catchBody == null ? null : new AddressSet(
					[...descriptor.catchBody].filter((block) =>
						cfg.blocks.has(block)
					),
				),
				canonicalFinallyAddress: descriptor.canonicalFinallyAddress,
				canonicalFinallyOwnership:
					descriptor.canonicalFinallyOwnership == null ? null : {
						finallyAddress: descriptor
							.canonicalFinallyOwnership
							.finallyAddress,
						protectsCatch: descriptor
							.canonicalFinallyOwnership
							.protectsCatch,
						missingProtectedBlocks: new AddressSet(
							descriptor.canonicalFinallyOwnership
								.missingProtectedBlocks,
						),
						valid: descriptor.canonicalFinallyOwnership.valid,
					},
				finallyCopyRoots: new AddressSet(descriptor.finallyCopyRoots),
				finallyBodyBlocks: descriptor.finallyBodyBlocks,
				boundedFinallyBodyBlocks: null,
				finallyCopies: descriptor.finallyCopies.map((copy) => ({
					...copy,
					skipRanges: copy.skipRanges?.map((range) => ({
						...range,
					})),
				})),
				finallyCopySuffixes: uniqueFinalizerCopySuffixes(
					descriptor.finallyCopySuffixes,
				).map((suffix) => ({
					...suffix,
					statements: suffix.statements.map((stmt) =>
						t.cloneNode(stmt, true)
					),
					skipRanges: suffix.skipRanges?.map((range) => ({
						...range,
					})),
				})),
				enclosingFinallyCopyRoots: descriptor.enclosingFinallyCopyRoots
					.map((copy) => ({
						...copy,
					})),
			};
			handlers.push(recovered);
			handlerByAddress.set(recovered.handler, recovered);
		}
		forest = cloneHandlerForest(
			func.exceptions.structuredRegionForest(),
			handlerByAddress,
		);
		attachFinallyBodyChildren(forest);
		addMissingExceptionalHandlerDescriptors(
			cfg,
			handlers,
			handlerByAddress,
			forest,
		);
		const equivalentCatchHandlerAliases = new Map(
			[...func.exceptions.equivalentCatchHandlerAliases()].filter(
				([child, parent]) =>
					handlerByAddress.has(child) && handlerByAddress.has(parent),
			),
		);
		const info = finalizeDescriptorInfo(
			cfg,
			handlers,
			handlerByAddress,
			forest,
			!func.isAsync &&
				(!func.isGenerator || func.isNativeGenerator) &&
				!func.isLoweredGenerator,
			equivalentCatchHandlerAliases,
		);
		info.finalizerEdgeActions = func.exceptions.finalizerEdgeActions();
		return info;
	}
	for (const [handler, predecessors] of cfg.exceptionalPredecessors) {
		if (predecessors.size === 0) continue;
		const entry = minAddress(predecessors);
		const descriptor: ExceptionDescriptor = {
			handler,
			kind: 'catch',
			protectedBlocks: new AddressSet(predecessors),
			protectedEntries: new AddressSet(entry == null ? [] : [entry]),
			catchBody: null,
			canonicalFinallyAddress: null,
			canonicalFinallyOwnership: null,
			finallyCopyRoots: new AddressSet(),
			finallyBodyBlocks: null,
			boundedFinallyBodyBlocks: null,
			finallyCopies: [],
			finallyCopySuffixes: [],
			enclosingFinallyCopyRoots: [],
		};
		handlers.push(descriptor);
		handlerByAddress.set(handler, descriptor);
	}
	handlers.sort((left, right) => left.handler - right.handler);
	return finalizeDescriptorInfo(
		cfg,
		handlers,
		handlerByAddress,
		buildFallbackForest(handlers),
		false,
	);
}

// Build the shared finalizer-copy model and stamp each finally descriptor's
// bounded body onto it, then assemble the ExceptionDescriptorInfo. Called at
// every return of recoverExceptionDescriptors so the model is always present.
function finalizeDescriptorInfo(
	cfg: ImmutableCFG,
	handlers: ExceptionDescriptor[],
	handlerByAddress: Map<BlockAddr, ExceptionDescriptor>,
	forest: ExceptionRegionForest,
	iteratorCleanupActionElision: boolean,
	equivalentCatchHandlerAliases: Map<BlockAddr, BlockAddr> = new Map(),
): ExceptionDescriptorInfo {
	recoverBranchingFinalizerCopies(cfg, handlers);
	recoverInlineFinalizerCopies(cfg, handlers);
	const finalizerCopyModel = buildFinalizerCopyModel(cfg, {
		handlers,
		forest,
	});
	for (const descriptor of handlers) {
		if (descriptor.kind !== 'finally') continue;
		const bounded = finalizerCopyModel.canonicalBodyByHandler.get(
			descriptor.handler,
		);
		descriptor.boundedFinallyBodyBlocks = bounded == null
			? descriptor.finallyBodyBlocks
			: [...bounded];
	}
	return {
		handlers,
		handlerByAddress,
		forest,
		equivalentCatchHandlerAliases,
		finalizerCopyModel,
		finalizerEdgeActions: [],
		iteratorCleanupActionElision,
		elidedIteratorCleanupHandlers: new AddressSet<BlockAddr>(),
	};
}

function generatedAliasFeedsNextStatement(
	statement: t.Statement,
	next: t.Statement | undefined,
): boolean {
	if (
		!next ||
		!t.isVariableDeclaration(statement) ||
		statement.declarations.length !== 1
	) return false;
	const [declaration] = statement.declarations;
	if (
		!t.isIdentifier(declaration.id) ||
		!/^r\d+_\d+$/.test(declaration.id.name) ||
		!t.isIdentifier(declaration.init) ||
		!/^r\d+_\d+$/.test(declaration.init.name)
	) return false;
	const name = declaration.id.name;
	let referenced = false;
	t.traverseFast(next, (node) => {
		if (t.isIdentifier(node, { name })) {
			referenced = true;
		}
	});
	return referenced;
}

function matchingFinalizerPrefixEnd(
	candidate: readonly t.Statement[],
	canonical: readonly t.Statement[],
): number | null {
	let candidateIndex = 0;
	for (const finalizerStatement of canonical) {
		let copyStatement = candidate[candidateIndex];
		while (
			copyStatement &&
			!statementMatchesFinalizerPrefix(
				copyStatement,
				finalizerStatement,
			) &&
			generatedAliasFeedsNextStatement(
				copyStatement,
				candidate[candidateIndex + 1],
			)
		) {
			candidateIndex++;
			copyStatement = candidate[candidateIndex];
		}
		if (
			!copyStatement ||
			!statementMatchesFinalizerPrefix(
				copyStatement,
				finalizerStatement,
			)
		) return null;
		candidateIndex++;
	}
	return candidateIndex;
}

// A finalizer copy can share its block with the continuation after the
// `finally` (the copied prefix is followed by ordinary source statements).
// HandlerGraph records whole-block copy roots and therefore cannot represent
// this split. Recover the matching prefix so the emitter retains the remainder.
function recoverInlineFinalizerCopies(
	cfg: ImmutableCFG,
	handlers: ExceptionDescriptor[],
) {
	for (const descriptor of handlers) {
		if (descriptor.kind !== 'finally') continue;
		const canonicalBlock = cfg.blocks.get(descriptor.handler);
		if (!canonicalBlock) continue;
		const canonical = canonicalBlock.body.filter((statement) =>
			!isCatchPrelude(statement) &&
			!isUndefinedTempDeclaration(statement) &&
			!isGlobalAliasDeclaration(statement) &&
			!t.isReturnStatement(statement) &&
			!t.isThrowStatement(statement)
		);
		if (canonical.length === 0) continue;

		for (const protectedBlock of descriptor.protectedBlocks) {
			for (
				const successor of cfg.normalSuccessors.get(protectedBlock) ??
					[]
			) {
				if (descriptor.protectedBlocks.has(successor)) continue;
				if (successor === descriptor.handler) continue;
				if (descriptor.finallyCopyRoots.has(successor)) continue;
				const candidate = cfg.blocks.get(successor);
				if (!candidate || candidate.body.length <= canonical.length) {
					continue;
				}
				const prefixEnd = matchingFinalizerPrefixEnd(
					candidate.body,
					canonical,
				);
				if (prefixEnd == null || prefixEnd >= candidate.body.length) {
					continue;
				}

				descriptor.finallyCopyRoots.add(successor);
				descriptor.finallyCopies.push({
					canonical: descriptor.handler,
					copyRoot: successor,
					next: successor,
					kind: 'normalExit',
					skipRanges: [{
						block: successor,
						start: 0,
						end: prefixEnd,
					}],
				});
			}
		}
		for (const copy of descriptor.finallyCopies) {
			if (copy.skipRanges?.length) continue;
			const candidate = cfg.blocks.get(copy.copyRoot);
			if (!candidate || candidate.body.length <= canonical.length) {
				continue;
			}
			const prefixEnd = matchingFinalizerPrefixEnd(
				candidate.body,
				canonical,
			);
			if (prefixEnd == null || prefixEnd >= candidate.body.length) {
				continue;
			}
			copy.skipRanges = [{
				block: copy.copyRoot,
				start: 0,
				end: prefixEnd,
			}];
		}
	}
}

function isGlobalAliasDeclaration(statement: t.Statement): boolean {
	return t.isVariableDeclaration(statement) &&
		statement.declarations.length === 1 &&
		t.isIdentifier(statement.declarations[0].id) &&
		t.isIdentifier(statement.declarations[0].init, { name: 'global' });
}

function uniqueFinalizerCopySuffixes(
	suffixes: readonly FinallyCopySuffixDescriptor[],
): FinallyCopySuffixDescriptor[] {
	const seen = new Set<string>();
	return suffixes.filter((suffix) => {
		const key = JSON.stringify({
			kind: suffix.kind,
			canonical: suffix.canonical,
			copyRoot: suffix.copyRoot,
			ownerBlock: suffix.ownerBlock,
			next: suffix.next,
			statements: suffix.statements.map(statementFingerprint),
			skipRanges: suffix.skipRanges ?? [],
		});
		if (seen.has(key)) return false;
		seen.add(key);
		return true;
	});
}

// Hermes duplicates a complete looping finalizer on normal return paths. The
// legacy HandlerGraph trace is deliberately linear and therefore cannot see
// these copies. Recover the narrow, mechanically provable shape here: a branch
// landing pad, one self-loop successor with the same normalized body, and a
// terminal continuation.
function recoverBranchingFinalizerCopies(
	cfg: ImmutableCFG,
	handlers: ExceptionDescriptor[],
) {
	for (const descriptor of handlers) {
		if (descriptor.kind !== 'finally') continue;
		const canonical = branchingFinalizerShape(
			cfg,
			descriptor.handler,
			true,
		);
		if (!canonical) continue;
		for (const block of descriptor.protectedBlocks) {
			for (const successor of cfg.normalSuccessors.get(block) ?? []) {
				if (descriptor.protectedBlocks.has(successor)) continue;
				if (successor === descriptor.handler) continue;
				const copy = branchingFinalizerShape(cfg, successor, false);
				if (!copy) continue;
				if (canonical.rootFingerprint !== copy.rootFingerprint) {
					continue;
				}
				if (canonical.loopFingerprint !== copy.loopFingerprint) {
					continue;
				}
				const recovered: FinallyCopyDescriptor = {
					canonical: descriptor.handler,
					copyRoot: successor,
					copyBlocks: [successor, copy.loop],
					next: copy.terminal,
					kind: 'normalExit',
				};
				const existing = descriptor.finallyCopies.find((candidate) =>
					candidate.copyRoot === successor
				);
				if (existing) Object.assign(existing, recovered);
				else descriptor.finallyCopies.push(recovered);
				descriptor.finallyCopyRoots.add(successor);
				// A linear HandlerGraph may have described the same branching copy as
				// an abrupt suffix. The structural match above proves it is the normal
				// copied finalizer, so its old deferred-return action must not survive.
				descriptor.finallyCopySuffixes = descriptor.finallyCopySuffixes
					.filter((suffix) => suffix.copyRoot !== successor);
			}
		}
	}
}

function branchingFinalizerShape(
	cfg: ImmutableCFG,
	entry: BlockAddr,
	canonical: boolean,
): {
	loop: BlockAddr;
	terminal: BlockAddr;
	rootFingerprint: string;
	loopFingerprint: string;
} | null {
	const root = cfg.blocks.get(entry);
	if (!root || root.terminator.kind !== 'if') return null;
	const successors = [...(cfg.normalSuccessors.get(entry) ?? [])];
	if (successors.length !== 2) return null;
	const loop = successors.find((candidate) =>
		cfg.normalSuccessors.get(candidate)?.has(candidate)
	);
	if (loop == null) return null;
	const terminal = successors.find((candidate) => candidate !== loop);
	if (terminal == null) return null;
	const terminalKind = cfg.blocks.get(terminal)?.terminator.kind;
	if (
		canonical
			? terminalKind !== 'throw' && terminalKind !== 'return'
			: terminalKind !== 'return' && terminalKind !== 'throw'
	) return null;
	const loopBlock = cfg.blocks.get(loop);
	if (!loopBlock || loopBlock.terminator.kind !== 'if') return null;
	return {
		loop,
		terminal,
		rootFingerprint: blockFinalizerFingerprint(root.body),
		loopFingerprint: blockFinalizerFingerprint(loopBlock.body),
	};
}

function blockFinalizerFingerprint(body: readonly t.Statement[]): string {
	return body.filter((statement) =>
		!isCatchPrelude(statement) && !isUndefinedTempDeclaration(statement)
	).map(statementFingerprint).join('|');
}

function isCatchPrelude(statement: t.Statement): boolean {
	return t.isVariableDeclaration(statement) && statement.declarations.some(
		(decl) =>
			t.isCallExpression(decl.init) &&
			t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Catch' }),
	);
}

function isUndefinedTempDeclaration(statement: t.Statement): boolean {
	return t.isVariableDeclaration(statement) &&
		statement.declarations.length === 1 &&
		t.isIdentifier(statement.declarations[0].id) &&
		t.isIdentifier(statement.declarations[0].init, { name: 'undefined' });
}

function descriptorPrimaryBlocksExist(
	cfg: ImmutableCFG,
	descriptor: ReturnType<
		IRFunction['exceptions']['structuredRegionDescriptors']
	>[number],
): boolean {
	if (!cfg.blocks.has(descriptor.handler)) return false;
	for (const block of descriptor.protectedBlocks) {
		if (cfg.blocks.has(block)) return true;
	}
	return false;
}

function addMissingExceptionalHandlerDescriptors(
	cfg: ImmutableCFG,
	handlers: ExceptionDescriptor[],
	handlerByAddress: Map<BlockAddr, ExceptionDescriptor>,
	forest: ExceptionRegionForest,
) {
	for (const [handler, predecessors] of cfg.exceptionalPredecessors) {
		if (predecessors.size === 0 || handlerByAddress.has(handler)) {
			continue;
		}
		const entry = minAddress(predecessors);
		const kind = isRethrowOnlyHandler(cfg, handler) ? 'finally' : 'catch';
		const descriptor: ExceptionDescriptor = {
			handler,
			kind,
			protectedBlocks: new AddressSet(predecessors),
			protectedEntries: new AddressSet(entry == null ? [] : [entry]),
			catchBody: null,
			canonicalFinallyAddress: null,
			canonicalFinallyOwnership: null,
			finallyCopyRoots: new AddressSet(),
			finallyBodyBlocks: kind === 'finally' ? [handler] : null,
			boundedFinallyBodyBlocks: null,
			finallyCopies: [],
			finallyCopySuffixes: [],
			enclosingFinallyCopyRoots: [],
		};
		handlers.push(descriptor);
		handlerByAddress.set(handler, descriptor);
		const node: ExceptionRegionForestNode = {
			descriptor,
			children: [],
		};
		forest.roots.push(node);
		forest.nodeByHandler.set(handler, node);
	}
	handlers.sort((left, right) => left.handler - right.handler);
	sortExceptionForestNodes(forest.roots);
}

function isRethrowOnlyHandler(cfg: ImmutableCFG, handler: BlockAddr): boolean {
	const block = cfg.blocks.get(handler);
	if (!block || block.terminator.kind !== 'throw') return false;
	return block.body.some((stmt) =>
		t.isVariableDeclaration(stmt) &&
		stmt.declarations.some((decl) =>
			t.isCallExpression(decl.init) &&
			t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Catch' })
		)
	);
}

function finallyOwnershipDiagnosticMessage(
	catchAddress: BlockAddr,
	proof: FinallyOwnershipProof,
): string {
	if (!proof.protectsCatch) {
		return `finally 0x${
			proof.finallyAddress.toString(16)
		} does not protect catch handler 0x${catchAddress.toString(16)}`;
	}
	const missing = [...proof.missingProtectedBlocks]
		.map((block) => `0x${block.toString(16)}`)
		.join(', ');
	return `finally 0x${
		proof.finallyAddress.toString(16)
	} does not protect catch 0x${
		catchAddress.toString(16)
	} protected blocks: ${missing}`;
}

function cloneHandlerForest(
	source: ReturnType<IRFunction['exceptions']['structuredRegionForest']>,
	handlerByAddress: Map<BlockAddr, ExceptionDescriptor>,
): ExceptionRegionForest {
	const nodeByHandler = new Map<BlockAddr, ExceptionRegionForestNode>();
	const cloneNode = (
		node: typeof source.roots[number],
	): ExceptionRegionForestNode | null => {
		const descriptor = handlerByAddress.get(node.descriptor.handler);
		if (!descriptor) return null;
		const cloned: ExceptionRegionForestNode = {
			descriptor,
			children: [],
		};
		nodeByHandler.set(descriptor.handler, cloned);
		cloned.children = node.children.map(cloneNode).filter((
			child,
		): child is ExceptionRegionForestNode => child != null);
		return cloned;
	};
	const roots = source.roots.map(cloneNode).filter((
		node,
	): node is ExceptionRegionForestNode => node != null);
	const parentByHandler = new Map<BlockAddr, BlockAddr>();
	for (const [child, parent] of source.parentByHandler) {
		if (handlerByAddress.has(child) && handlerByAddress.has(parent)) {
			parentByHandler.set(child, parent);
		}
	}
	return { roots, nodeByHandler, parentByHandler };
}

function attachFinallyBodyChildren(forest: ExceptionRegionForest) {
	let changed = true;
	while (changed) {
		changed = false;
		for (const child of [...forest.nodeByHandler.values()]) {
			if (forest.parentByHandler.has(child.descriptor.handler)) {
				continue;
			}
			const parent = closestFinallyBodyParent(child, forest);
			if (!parent) continue;
			parent.children.push(child);
			forest.parentByHandler.set(
				child.descriptor.handler,
				parent.descriptor.handler,
			);
			forest.roots = forest.roots.filter((root) => root !== child);
			changed = true;
		}
	}
	sortExceptionForestNodes(forest.roots);
}

function closestFinallyBodyParent(
	child: ExceptionRegionForestNode,
	forest: ExceptionRegionForest,
): ExceptionRegionForestNode | null {
	const candidates = [...forest.nodeByHandler.values()].filter((
		candidate,
	) => {
		if (candidate === child) return false;
		if (forestNodeContains(child, candidate)) return false;
		const body = candidate.descriptor.finallyBodyBlocks;
		if (candidate.descriptor.kind !== 'finally' || body == null) {
			return false;
		}
		const bodyBlocks = new AddressSet(body);
		return bodyBlocks.has(child.descriptor.handler) ||
			child.descriptor.protectedEntries.intersection(bodyBlocks).size > 0;
	});
	return candidates.toSorted((left, right) =>
		(left.descriptor.finallyBodyBlocks?.length ?? 0) -
			(right.descriptor.finallyBodyBlocks?.length ?? 0) ||
		left.descriptor.protectedBlocks.size -
			right.descriptor.protectedBlocks.size ||
		left.descriptor.handler - right.descriptor.handler
	)[0] ?? null;
}

function forestNodeContains(
	parent: ExceptionRegionForestNode,
	child: ExceptionRegionForestNode,
): boolean {
	const seen = new Set<ExceptionRegionForestNode>();
	const queue = [...parent.children];
	while (queue.length > 0) {
		const current = queue.shift()!;
		if (seen.has(current)) continue;
		seen.add(current);
		if (current === child) return true;
		queue.push(...current.children);
	}
	return false;
}

function sortExceptionForestNodes(nodes: ExceptionRegionForestNode[]) {
	nodes.sort((left, right) =>
		left.descriptor.protectedBlocks.size -
			right.descriptor.protectedBlocks.size ||
		left.descriptor.handler - right.descriptor.handler
	);
	for (const node of nodes) sortExceptionForestNodes(node.children);
}

function buildFallbackForest(
	handlers: ExceptionDescriptor[],
): ExceptionRegionForest {
	const nodeByHandler = new Map<BlockAddr, ExceptionRegionForestNode>();
	const nodes = handlers.map((descriptor) => {
		const node: ExceptionRegionForestNode = { descriptor, children: [] };
		nodeByHandler.set(descriptor.handler, node);
		return node;
	});
	return { roots: nodes, nodeByHandler, parentByHandler: new Map() };
}

function emptyExceptionRegionForest(): ExceptionRegionForest {
	return {
		roots: [],
		nodeByHandler: new Map(),
		parentByHandler: new Map(),
	};
}

function minAddress(blocks: Iterable<BlockAddr>): BlockAddr | null {
	let min: BlockAddr | null = null;
	for (const block of blocks) {
		if (min == null || block < min) min = block;
	}
	return min;
}
