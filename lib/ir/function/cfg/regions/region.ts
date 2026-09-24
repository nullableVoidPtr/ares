import * as t from '@babel/types';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { CFGEdge, ImmutableCFG } from '../immutableCFG.ts';

export interface RegionBase {
	sourceBlocks: AddressSet<BlockAddr>;
	deferredExits?: DeferredExit[];
}

export type Region =
	| (RegionBase & { kind: 'basic'; body: t.Statement[] })
	| (RegionBase & {
		kind: 'sequence';
		regions: Region[];
		/** Label used by deferred exits that skip the remainder of this sequence. */
		exitLabel?: string;
	})
	| (RegionBase & {
		kind: 'if';
		/** CFG block that owns this conditional terminator. */
		header: BlockAddr;
		/**
		 * CFG branch blocks represented by this predicate. This is larger than the
		 * header when a short-circuit chain is recovered without mutating the CFG.
		 */
		predicateBlocks?: AddressSet<BlockAddr>;
		/**
		 * Generated registers assigned while evaluating a recovered compound
		 * predicate. Their declarations belonged to absorbed CFG blocks, so the
		 * emitter must declare them before the conditional while leaving their
		 * assignments inside the short-circuit expression.
		 */
		predicateBindings?: string[];
		/** Original CFG edges selected by the recovered predicate's two arms. */
		branchEdges?: {
			consequent: CFGEdge;
			alternate: CFGEdge;
		};
		test: t.Expression;
		consequent: Region;
		alternate: Region;
		/**
		 * Shared continuation both arms resume at, when they have one. Absent for
		 * a divergent branch whose arms never meet again — each one returns,
		 * throws, or leaves the enclosing scope by its own edge — which has no
		 * trailer to own and no value join to merge.
		 */
		join?: BlockAddr;
		conditionalValue?: ConditionalValueCandidate;
	})
	| (RegionBase & {
		kind: 'switch';
		/** CFG block that owns this switch dispatch terminator. */
		header: BlockAddr;
		prelude?: t.Statement[];
		discriminant: t.Expression;
		/** Common continuation kept outside all case ownership. */
		join?: BlockAddr;
		cases: SwitchRegionCase[];
		defaultTarget: BlockAddr;
		defaultSource?: BlockAddr;
		defaultBody: Region;
	})
	| (RegionBase & {
		kind: 'tryCatch';
		body: Region;
		handler: Region;
		handlerAddress: BlockAddr;
		protectedBlocks: AddressSet<BlockAddr>;
		/**
		 * Compiler-split child catch pads whose value-only completion is emitted
		 * by this catch. They remain owned for exact CFG coverage but emit nothing.
		 */
		subsumedHandlerBlocks?: AddressSet<BlockAddr>;
		/**
		 * Hermes models a retrying `while (true) { try { ...; break; } catch {
		 * ... } }` with an exceptional edge into the handler and a normal edge
		 * from that handler back to the protected entry. It is not a normal-flow
		 * natural loop, so retain the exceptional-region proof explicitly.
		 */
		retryLoop?: {
			header: BlockAddr;
			/** Scalar/Phi loop header immediately before the protected entry. */
			prelude?: BlockAddr;
			normalExit: BlockAddr;
			backedge: CFGEdge;
			/** A catch trailer which retries on one branch and exits on the other. */
			conditionalExit?: {
				decision: BlockAddr;
				exit: CFGEdge;
			};
			/** Path-local return/throw targets distinct from the normal exit. */
			abruptExits?: BlockAddr[];
		};
	})
	| (RegionBase & {
		kind: 'tryFinally';
		body: Region;
		finalizer: Region;
		handlerAddress: BlockAddr;
		protectedBlocks: AddressSet<BlockAddr>;
		normalExit?: BlockAddr;
		normalExitCandidates?: BlockAddr[];
		finallyCopyKinds?: string[];
	})
	| (RegionBase & {
		kind: 'loop';
		id: number;
		label?: string;
		syntax?: LoopSyntax;
		header: BlockAddr;
		latches: BlockAddr[];
		/** Natural-loop blocks, excluding ordered exit trailers. */
		loopBlocks: AddressSet<BlockAddr>;
		/** Common continuation reached after every ordinary break exit. */
		continuation?: BlockAddr;
		exits: LoopRegionExit[];
		/**
		 * Exit trailers already represented inside `body`.
		 *
		 * Their final deferred transfer still needs the trailer's last block and
		 * outgoing Phi edge, but the loop must not emit the whole trailer again.
		 */
		bodyOwnedExits?: LoopRegionExit[];
		children: number[];
		/**
		 * A header branch that either enters the ordinary body or skips directly to
		 * a distinct latch. The latch is emitted after this conditional so both
		 * incoming edges can retain their own Phi actions.
		 */
		headerLatchBranch?: {
			bodyEntry: BlockAddr;
			latch: BlockAddr;
		};
		/**
		 * The body Region starts at the header and emits its statements.
		 *
		 * Set when a protected range opens exactly at the header: the `try` has
		 * to own those statements, so the loop must not emit them again.
		 */
		bodyOwnsHeader?: boolean;
		/**
		 * Body blocks a finalizer the body represents emits instead.
		 *
		 * Hermes copies the finalizer onto each exit out of a protected range.
		 * When the body owns that range, the copies inside the loop are owned
		 * while emitting nothing of their own.
		 */
		suppressedBodyBlocks?: AddressSet<BlockAddr>;
		/**
		 * Cleanup landing pads this loop's syntax represents, such as the
		 * `for...of` IteratorClose rethrow pad. The Region owns them — nothing
		 * else may — but emits nothing for them.
		 */
		subsumedHandlers?: AddressSet<BlockAddr>;
		body: Region;
	})
	| (RegionBase & {
		kind: 'delegateYield';
		argument: t.Expression;
		preludeStatements?: t.Statement[];
		completion: 'discarded' | 'assigned';
		// For `completion: 'assigned'`, the temp the completion value binds to; emitted as
		// `<completionTarget> = yield* argument`.
		completionTarget?: t.Identifier;
		// Genuine continuation statements from the loop's normal-exit block that follow
		// the completion extraction — e.g. code after `yield* x;`. Emitted right after the
		// `yield*`.
		trailing?: t.Statement[];
		// Set when the normal-exit block belongs to enclosing control flow instead
		// of this Region: emission suppresses the completion-extraction statements
		// this range covers, and the `yield*` re-declares `completionTarget`.
		completionSkip?: { block: BlockAddr; start: number; end: number };
		declaresCompletionTarget?: boolean;
		// Set when an enclosing loop Region owns the prelude block: emission
		// suppresses the acquisition statements these indices name.
		preludeSkip?: { block: BlockAddr; statements: number[] };
	})
	| (RegionBase & {
		kind: 'break';
		target: BlockAddr;
		exit?: LoopRegionExit;
	})
	| (RegionBase & {
		kind: 'continue';
		target: BlockAddr;
		exit?: LoopRegionExit;
	})
	| (RegionBase & {
		kind: 'labelBreak';
		label: string;
		target: BlockAddr;
		exit?: LoopRegionExit;
	})
	| (RegionBase & {
		kind: 'labelContinue';
		label: string;
		target: BlockAddr;
		exit?: LoopRegionExit;
	})
	| (RegionBase & { kind: 'deferredExit'; exit: DeferredExit })
	| (RegionBase & { kind: 'return'; argument?: t.Expression | null })
	| (RegionBase & { kind: 'throw'; argument: t.Expression })
	| (RegionBase & {
		kind: 'terminalReference';
		entry: BlockAddr;
		edge?: CFGEdge;
		/** Ordered loop completion represented by this non-owning terminal leaf. */
		exit?: LoopRegionExit;
	})
	| (RegionBase & {
		kind: 'fallback';
		reason: string;
		entry: BlockAddr;
	});

export interface SwitchRegionCase {
	test: t.Expression | null;
	/** Additional side-effect-free labels sharing this bytecode target. */
	aliases?: t.Expression[];
	target: BlockAddr;
	source?: BlockAddr;
	prefix?: t.Statement[];
	body: Region;
	/** Completion after this case body; omitted for terminal cases. */
	completion?: 'break' | 'fallthrough';
}

/**
 * CFG provenance for a value merged by an If Region. This deliberately does
 * not select JavaScript syntax: the emitter chooses a shortcut, optional
 * access, nullish coalescing, or ternary only after inspecting Phi values.
 */
export interface ConditionalValueCandidate {
	kind: 'conditionalPhi';
	branch: BlockAddr;
	consequentEntry: BlockAddr;
	alternateEntry: BlockAddr;
	join: BlockAddr;
	forms: readonly ['shortcut', 'ternary'];
}

export interface LoopRegionExit {
	from: BlockAddr;
	to: BlockAddr;
	kind:
		| 'break'
		| 'continue'
		| 'labelledBreak'
		| 'labelledContinue'
		| 'return'
		| 'throw';
	label?: string;
	targetLoop?: number;
	/** Blocks that execute on this edge before control leaves the loop. */
	trailer?: Region;
	/** Join reached after the optional trailer. */
	continuation?: BlockAddr;
	/**
	 * Internal flag set when this break is not normal iterator exhaustion.
	 * Recovered iterator syntax uses it when the break bypasses a header-only
	 * exit trailer, or when it reaches the same continuation with different
	 * edge-local Phi values.
	 */
	normalCompletionFlag?: string;
	/**
	 * An enclosing sequence left after this exit's ordered trailer. This is
	 * distinct from the loop break itself: the loop first exits normally, then
	 * the trailer transfers past the loop's ordinary continuation.
	 */
	sequenceExit?: { target: BlockAddr; label?: string };
}

export interface LoopRegionCoverageIssue {
	header: BlockAddr;
	missingBodyBlocks: BlockAddr[];
	unexpectedBodyBlocks: BlockAddr[];
	missingTrailerBlocks: BlockAddr[];
	unexpectedTrailerBlocks: BlockAddr[];
	overlappingTrailerBlocks: BlockAddr[];
}

export interface LoopSyntax {
	kind: 'forOf' | 'forIn';
	header: BlockAddr;
	preheader?: { block: BlockAddr; statement: number };
	source: t.Expression;
	value: t.Identifier;
	/** Iterator-machine outputs subsumed by the high-level loop syntax. */
	internalValues?: t.Identifier[];
	/**
	 * Preheader machine registers the syntax replaced: the iterator object for
	 * `for...of`, the property list, index, and size for `for...in`. Nothing
	 * declares them any more, so statements that still reference them belong to
	 * the machine the syntax stands for.
	 */
	machineValues?: t.Identifier[];
}

/**
 * Blocks represented by a Region, including non-owning terminal references.
 * `sourceBlocks` remains the ownership set used for overlap and exit analysis;
 * this coverage view is used only when proving that recursive decomposition
 * represented every block in a candidate arm.
 */
export function regionCoveredBlocks(region: Region): AddressSet<BlockAddr> {
	const covered = new AddressSet<BlockAddr>(region.sourceBlocks);
	const visit = (candidate: Region) => {
		if (candidate.kind === 'terminalReference') {
			covered.add(candidate.entry);
			return;
		}
		switch (candidate.kind) {
			case 'sequence':
				candidate.regions.forEach(visit);
				break;
			case 'if':
				visit(candidate.consequent);
				visit(candidate.alternate);
				break;
			case 'switch':
				candidate.cases.forEach((switchCase) => visit(switchCase.body));
				visit(candidate.defaultBody);
				break;
			case 'tryCatch':
				visit(candidate.body);
				visit(candidate.handler);
				break;
			case 'tryFinally':
				covered.add(candidate.handlerAddress);
				visit(candidate.body);
				visit(candidate.finalizer);
				break;
			case 'loop':
				visit(candidate.body);
				candidate.exits.forEach((exit) => {
					if (exit.kind === 'return' || exit.kind === 'throw') {
						covered.add(exit.to);
					}
					if (exit.trailer) visit(exit.trailer);
				});
				break;
		}
	};
	visit(region);
	return covered;
}

/**
 * Blocks for which a Region contains an actual structural representation.
 *
 * This deliberately does not trust aggregate `sourceBlocks`: loop and
 * exception Regions use those sets as ownership boundaries, and a fallback
 * may name an entire failed subgraph. Composite coverage is instead rebuilt
 * from its children plus the explicit branch/dispatch header it owns.
 */
export function regionStructuredBlocks(region: Region): AddressSet<BlockAddr> {
	switch (region.kind) {
		case 'fallback':
			return new AddressSet();
		case 'terminalReference':
			// A terminal reference proves control-flow coverage without taking block
			// ownership; it must not satisfy an enclosing loop's body inventory.
			return new AddressSet();
		case 'sequence':
			return unionStructuredBlocks(region.regions);
		case 'if': {
			const children = unionStructuredBlocks([
				region.consequent,
				region.alternate,
			]);
			const childClaims = region.consequent.sourceBlocks.union(
				region.alternate.sourceBlocks,
			);
			return children.union(region.sourceBlocks.difference(childClaims));
		}
		case 'switch': {
			const children = [
				...region.cases.map((switchCase) => switchCase.body),
				region.defaultBody,
			];
			const childClaims = new AddressSet<BlockAddr>(
				children.flatMap((child) => [...child.sourceBlocks]),
			);
			return unionStructuredBlocks(children).union(
				region.sourceBlocks.difference(childClaims),
			);
		}
		case 'tryCatch':
			return unionStructuredBlocks([region.body, region.handler]).union(
				region.subsumedHandlerBlocks ?? new AddressSet<BlockAddr>(),
			);
		case 'tryFinally':
			return unionStructuredBlocks([region.body, region.finalizer]);
		case 'loop': {
			const trailers = region.exits.flatMap((exit) =>
				exit.trailer ? [exit.trailer] : []
			);
			return new AddressSet([
				region.header,
				...(region.headerLatchBranch
					? [region.headerLatchBranch.latch]
					: []),
			])
				.union(regionStructuredBlocks(region.body))
				.union(unionStructuredBlocks(trailers));
		}
		default:
			return new AddressSet(region.sourceBlocks);
	}
}

/**
 * Conditional and dispatch terminators represented only by a Basic Region.
 *
 * A Basic Region legitimately carries the statements of a branch header that an
 * If, Switch, or Loop Region owns, so ownership is decided by the explicit
 * headers in the tree rather than by the Basic Region alone.
 */
/** The canonical empty Region: a sequence that owns nothing. */
export function emptyRegion(): Region {
	return { kind: 'sequence', regions: [], sourceBlocks: new AddressSet() };
}

export function cloneRegion(region: Region): Region {
	return cloneRegionLike(region) as Region;
}

function cloneRegionLike(region: any): any {
	const cloned = {
		...region,
		sourceBlocks: new AddressSet(region.sourceBlocks),
	};
	if (region.deferredExits != null) {
		cloned.deferredExits = region.deferredExits.map(cloneDeferredExit);
	}

	switch (region.kind) {
		case 'basic':
			cloned.body = cloneStatements(region.body);
			break;
		case 'sequence':
			cloned.regions = region.regions.map(cloneRegionLike);
			break;
		case 'if':
			cloned.predicateBlocks = cloneOptionalAddressSet(
				region.predicateBlocks,
			);
			cloned.predicateBindings = cloneOptionalArray(
				region.predicateBindings,
			);
			cloned.branchEdges = region.branchEdges == null ? undefined : {
				consequent: cloneEdge(region.branchEdges.consequent),
				alternate: cloneEdge(region.branchEdges.alternate),
			};
			cloned.test = cloneExpression(region.test);
			cloned.consequent = cloneRegionLike(region.consequent);
			cloned.alternate = cloneRegionLike(region.alternate);
			cloned.conditionalValue = region.conditionalValue == null
				? undefined
				: { ...region.conditionalValue };
			break;
		case 'switch':
			cloned.prelude = cloneOptionalStatements(region.prelude);
			cloned.discriminant = cloneExpression(region.discriminant);
			cloned.cases = region.cases.map(cloneSwitchRegionCase);
			cloned.defaultBody = cloneRegionLike(region.defaultBody);
			break;
		case 'tryCatch':
			cloned.body = cloneRegionLike(region.body);
			cloned.handler = cloneRegionLike(region.handler);
			cloned.protectedBlocks = new AddressSet(region.protectedBlocks);
			cloned.subsumedHandlerBlocks = cloneOptionalAddressSet(
				region.subsumedHandlerBlocks,
			);
			cloned.retryLoop = cloneRetryLoop(region.retryLoop);
			break;
		case 'tryFinally':
			cloned.body = cloneRegionLike(region.body);
			cloned.finalizer = cloneRegionLike(region.finalizer);
			cloned.protectedBlocks = new AddressSet(region.protectedBlocks);
			cloned.normalExitCandidates = cloneOptionalArray(
				region.normalExitCandidates,
			);
			cloned.finallyCopyKinds = cloneOptionalArray(
				region.finallyCopyKinds,
			);
			break;
		case 'loop':
			cloned.syntax = cloneLoopSyntax(region.syntax);
			cloned.latches = [...region.latches];
			cloned.loopBlocks = new AddressSet(region.loopBlocks);
			cloned.exits = region.exits.map(cloneLoopRegionExit);
			cloned.bodyOwnedExits = region.bodyOwnedExits == null
				? undefined
				: region.bodyOwnedExits.map(cloneLoopRegionExit);
			cloned.children = [...region.children];
			cloned.headerLatchBranch = region.headerLatchBranch == null
				? undefined
				: { ...region.headerLatchBranch };
			cloned.suppressedBodyBlocks = region.suppressedBodyBlocks == null
				? undefined
				: new AddressSet(region.suppressedBodyBlocks);
			cloned.subsumedHandlers = region.subsumedHandlers == null
				? undefined
				: new AddressSet(region.subsumedHandlers);
			cloned.body = cloneRegionLike(region.body);
			break;
		case 'delegateYield':
			cloned.argument = cloneExpression(region.argument);
			cloned.preludeStatements = cloneOptionalStatements(
				region.preludeStatements,
			);
			cloned.completionTarget = region.completionTarget == null
				? undefined
				: cloneIdentifier(region.completionTarget);
			cloned.trailing = cloneOptionalStatements(region.trailing);
			cloned.completionSkip = region.completionSkip == null
				? undefined
				: { ...region.completionSkip };
			cloned.preludeSkip = region.preludeSkip == null ? undefined : {
				block: region.preludeSkip.block,
				statements: [...region.preludeSkip.statements],
			};
			break;
		case 'break':
		case 'continue':
		case 'labelBreak':
		case 'labelContinue':
		case 'terminalReference':
			cloned.edge = cloneOptionalEdge(region.edge);
			cloned.exit = cloneOptionalLoopRegionExit(region.exit);
			break;
		case 'deferredExit':
			cloned.exit = cloneDeferredExit(region.exit);
			break;
		case 'return':
			cloned.argument = cloneOptionalExpression(region.argument);
			break;
		case 'throw':
			cloned.argument = cloneExpression(region.argument);
			break;
		case 'fallback':
			break;
		default:
			throw new Error(`Unknown Region kind: ${region.kind}`);
	}

	return cloned;
}

function cloneOptionalAddressSet(
	addresses: AddressSet<BlockAddr> | undefined,
): AddressSet<BlockAddr> | undefined {
	return addresses == null ? undefined : new AddressSet(addresses);
}

function cloneStatements(statements: readonly t.Statement[]): t.Statement[] {
	return statements.map((statement) =>
		t.cloneNode(statement, true) as t.Statement
	);
}

function cloneOptionalStatements(
	statements: readonly t.Statement[] | undefined,
): t.Statement[] | undefined {
	return statements == null ? undefined : cloneStatements(statements);
}

function cloneExpression(expression: t.Expression): t.Expression {
	return t.cloneNode(expression, true) as t.Expression;
}

function cloneOptionalExpression(
	expression: t.Expression | null | undefined,
): t.Expression | null | undefined {
	return expression == null ? expression : cloneExpression(expression);
}

function cloneIdentifier(identifier: t.Identifier): t.Identifier {
	return t.cloneNode(identifier, true) as t.Identifier;
}

function cloneOptionalArray<T>(
	values: readonly T[] | undefined,
): T[] | undefined {
	return values == null ? undefined : [...values];
}

function cloneLoopSyntax(
	syntax: LoopSyntax | undefined,
): LoopSyntax | undefined {
	if (syntax == null) return undefined;
	return {
		...syntax,
		source: cloneExpression(syntax.source),
		value: cloneIdentifier(syntax.value),
		internalValues: syntax.internalValues == null
			? undefined
			: syntax.internalValues.map(cloneIdentifier),
		machineValues: syntax.machineValues == null
			? undefined
			: syntax.machineValues.map(cloneIdentifier),
	};
}

function cloneSwitchRegionCase(
	switchCase: SwitchRegionCase,
): SwitchRegionCase {
	return {
		test: switchCase.test == null ? null : cloneExpression(switchCase.test),
		aliases: switchCase.aliases == null
			? undefined
			: switchCase.aliases.map(cloneExpression),
		target: switchCase.target,
		source: switchCase.source,
		prefix: cloneOptionalStatements(switchCase.prefix),
		body: cloneRegionLike(switchCase.body) as Region,
		completion: switchCase.completion,
	};
}

function cloneRetryLoop(retryLoop: any): any {
	if (retryLoop == null) return undefined;
	return {
		...retryLoop,
		backedge: cloneEdge(retryLoop.backedge),
		conditionalExit: retryLoop.conditionalExit == null ? undefined : {
			decision: retryLoop.conditionalExit.decision,
			exit: cloneEdge(retryLoop.conditionalExit.exit),
		},
		abruptExits: cloneOptionalArray(retryLoop.abruptExits),
	};
}

function cloneLoopRegionExit(exit: LoopRegionExit): LoopRegionExit {
	return {
		...exit,
		trailer: exit.trailer == null ? undefined : cloneRegion(exit.trailer),
		sequenceExit: exit.sequenceExit == null
			? undefined
			: { ...exit.sequenceExit },
	};
}

function cloneOptionalLoopRegionExit(
	exit: LoopRegionExit | undefined,
): LoopRegionExit | undefined {
	return exit == null ? undefined : cloneLoopRegionExit(exit);
}

function cloneEdge(edge: CFGEdge): CFGEdge {
	return { ...edge };
}

function cloneOptionalEdge(edge: CFGEdge | undefined): CFGEdge | undefined {
	return edge == null ? undefined : cloneEdge(edge);
}

function cloneDeferredExit(exit: DeferredExit): DeferredExit {
	return {
		...exit,
		edge: cloneOptionalEdge(exit.edge),
		actions: exit.actions.map(cloneEdgeAction),
	} as DeferredExit;
}

function cloneEdgeAction(action: EdgeAction): EdgeAction {
	switch (action.kind) {
		case 'phi':
		case 'placedPhi':
			return {
				kind: action.kind,
				assignments: action.assignments.map((assignment) => ({
					edge: cloneEdge(assignment.edge),
					target: cloneIdentifier(assignment.target),
					value: cloneExpression(assignment.value),
				})),
			};
		case 'finally':
			return {
				kind: 'finally',
				action: {
					...action.action,
					statements: cloneOptionalStatements(
						action.action.statements,
					),
				},
			};
		case 'statement':
			return {
				kind: 'statement',
				statement: t.cloneNode(action.statement, true) as t.Statement,
			};
		case 'return':
			return {
				kind: 'return',
				argument: cloneOptionalExpression(action.argument),
			};
		case 'throw':
			return {
				kind: 'throw',
				argument: cloneExpression(action.argument),
			};
	}
}

/** Whether the Region represents no control and owns no block. */
export function isEmptyRegion(region: Region): boolean {
	return region.kind === 'sequence' && region.regions.length === 0;
}

/** A sequence Region owning exactly what its children own. */
export function sequenceRegion(
	regions: Region[],
	exitLabel?: string,
): Region {
	return {
		kind: 'sequence',
		regions,
		exitLabel,
		sourceBlocks: new AddressSet(
			regions.flatMap((region) => [...region.sourceBlocks]),
		),
	};
}

/**
 * Whether a reducer has already composed control statements into the blocks.
 *
 * Recovery rules read boundaries out of the raw branch graph. Once an ordinary
 * reducer has folded control into a block body, the remaining edges no longer
 * describe the interior of those statements and the rules must decline.
 */
export function hasPrestructuredControl(cfg: ImmutableCFG): boolean {
	return [...cfg.blocks.values()].some((block) =>
		block.body.some((statement) =>
			t.isIfStatement(statement) ||
			t.isSwitchStatement(statement) ||
			t.isTryStatement(statement) ||
			t.isWhileStatement(statement) ||
			t.isDoWhileStatement(statement) ||
			t.isForStatement(statement) ||
			t.isForInStatement(statement) ||
			t.isForOfStatement(statement)
		)
	);
}

/** Whether any Basic Region in the tree still owns an unstructured branch. */
export function containsBasicBranch(
	region: Region,
	cfg: ImmutableCFG,
): boolean {
	if (
		region.kind === 'basic' &&
		[...region.sourceBlocks].some((address) =>
			blockNeedsBranchRegion(address, cfg)
		)
	) return true;
	switch (region.kind) {
		case 'sequence':
			return region.regions.some((child) =>
				containsBasicBranch(child, cfg)
			);
		case 'if':
			return containsBasicBranch(region.consequent, cfg) ||
				containsBasicBranch(region.alternate, cfg);
		case 'switch':
			return region.cases.some((switchCase) =>
				containsBasicBranch(switchCase.body, cfg)
			) || containsBasicBranch(region.defaultBody, cfg);
		case 'tryCatch':
			return containsBasicBranch(region.body, cfg) ||
				containsBasicBranch(region.handler, cfg);
		case 'tryFinally':
			return containsBasicBranch(region.body, cfg) ||
				containsBasicBranch(region.finalizer, cfg);
		case 'loop':
			return containsBasicBranch(region.body, cfg);
		default:
			return false;
	}
}

/**
 * A speculative attempt's view of the structured-descriptor ledger.
 *
 * The ledger records which exception handlers the region tree already
 * represents, so a continuation block still carrying a descriptor's
 * `protectedEntries` cannot re-open it. Recursive structuring is speculative by
 * construction — a builder composes a candidate, the caller inspects it and may
 * throw it away — and a discarded candidate never reaches the tree. Its ledger
 * entries have to come back out with it, or the descriptor is refused for the
 * rest of the build and its handler is dropped from the output entirely.
 */
export function ledgerSnapshot(
	ledger: AddressSet<BlockAddr>,
): AddressSet<BlockAddr> {
	return new AddressSet(ledger);
}

/** Undo the ledger claims a discarded speculative attempt made. */
export function restoreLedger(
	ledger: AddressSet<BlockAddr>,
	snapshot: AddressSet<BlockAddr>,
): void {
	for (const handler of [...ledger]) {
		if (!snapshot.has(handler)) ledger.delete(handler);
	}
}

/**
 * Whether a Basic Region owning this block leaves a branch unstructured.
 *
 * A conditional whose arms are the same block decides nothing: the comparison
 * it tests is consumed as a value, so there is no If Region to build and a
 * Basic Region owning it is already exact. Counting it leaves every enclosing
 * scope permanently unstructurable — one such block in function 2247 defeated
 * the residual scope at four separate entries.
 *
 * Every "is this branch owned" test shares this rule. It was written out four
 * times before, and the exemption reached only two of them.
 */
export function blockNeedsBranchRegion(
	address: BlockAddr,
	cfg: ImmutableCFG,
): boolean {
	const terminator = cfg.blocks.get(address)?.terminator;
	if (terminator?.kind === 'switch') return true;
	if (terminator?.kind !== 'if') return false;
	return terminator.taken !== terminator.fallthrough;
}

export function regionUnstructuredBranches(
	region: Region,
	cfg: ImmutableCFG,
): AddressSet<BlockAddr> {
	const basicBranches = new AddressSet<BlockAddr>();
	const structuredBranches = new AddressSet<BlockAddr>();
	const visit = (candidate: Region) => {
		if (candidate.kind === 'basic') {
			for (const address of candidate.sourceBlocks) {
				if (blockNeedsBranchRegion(address, cfg)) {
					basicBranches.add(address);
				}
			}
			return;
		}
		switch (candidate.kind) {
			case 'if':
				for (
					const address of candidate.predicateBlocks ??
						[candidate.header]
				) structuredBranches.add(address);
				break;
			case 'switch':
				structuredBranches.add(candidate.header);
				break;
			case 'loop':
				structuredBranches.add(candidate.header);
				for (const latch of candidate.latches) {
					structuredBranches.add(latch);
				}
				break;
		}
		for (const child of childRegions(candidate)) visit(child);
	};
	visit(region);
	return basicBranches.difference(structuredBranches);
}

/**
 * Blocks that more than one Region claims the same way.
 *
 * Statements are emitted for the first claimant only, so a second Basic Region
 * over the same block silently loses them while still testing the values they
 * define; two If or Switch Regions over one header duplicate its branch the
 * same way. A Basic Region beside the branch Region for its own block is the
 * ordinary statement-carrier idiom and is not a duplicate.
 */
/**
 * Blocks the loop's bare `break` exits resume at.
 *
 * `break` leaves a loop at exactly one place — whatever the emission orders
 * after it — so more than one destination cannot be lowered faithfully: the
 * second block is emitted after the loop and therefore runs on the first one's
 * path too. A labelled sequence exit escapes this because it becomes
 * `break <label>` at the exit's own site, except on a recovered `for` header,
 * where the loop simply ends and the statement can only be placed after it.
 */
export function loopBreakDestinations(
	region: Extract<Region, { kind: 'loop' }>,
): AddressSet<BlockAddr> {
	const destinations = new AddressSet<BlockAddr>();
	for (const exit of region.exits) {
		if (exit.kind !== 'break') continue;
		const endsTheLoop = region.syntax != null &&
			exit.from === region.header;
		if (exit.sequenceExit?.label && !endsTheLoop) continue;
		// An ordered trailer runs on this edge and then resumes at the join, so
		// the join is what has to agree with the other breaks.
		const destination = exit.trailer ? exit.continuation : exit.to;
		if (destination != null) destinations.add(destination);
	}
	return destinations;
}

interface RegionOwnershipClaims {
	statement: Map<BlockAddr, number>;
	control: Map<BlockAddr, number>;
}

function regionOwnershipClaims(region: Region): RegionOwnershipClaims {
	const nonEmittingLoopHandlers = nestedSubsumedLoopHandlers(region);
	const statement = new Map<BlockAddr, number>();
	const control = new Map<BlockAddr, number>();
	const claim = (claims: Map<BlockAddr, number>, address: BlockAddr) =>
		claims.set(address, (claims.get(address) ?? 0) + 1);
	const visit = (candidate: Region) => {
		switch (candidate.kind) {
			case 'basic':
				for (const address of candidate.sourceBlocks) {
					if (!nonEmittingLoopHandlers.has(address)) {
						claim(statement, address);
					}
				}
				break;
			case 'if':
				for (
					const address of candidate.predicateBlocks ??
						[candidate.header]
				) claim(control, address);
				break;
			case 'switch':
				claim(control, candidate.header);
				break;
			case 'loop':
				claim(statement, candidate.header);
				break;
		}
		for (const child of childRegions(candidate)) visit(child);
	};
	visit(region);
	return { statement, control };
}

export function regionDuplicateOwnership(
	region: Region,
	cfg: ImmutableCFG,
): BlockAddr[] {
	const claims = regionOwnershipClaims(region);
	const duplicated = new AddressSet<BlockAddr>();
	for (const category of [claims.statement, claims.control]) {
		for (const [address, count] of category) {
			if (count > 1 && cfg.blocks.has(address)) duplicated.add(address);
		}
	}
	return sortedAddresses(duplicated);
}

/**
 * Original SSA/basic blocks materialized by more than one Region claim.
 *
 * A compatibility reduction can split one SSA block into several live CFG
 * blocks. Expanding each live claim through `sourceAddresses` catches that case
 * without changing the live-block overlap gate above. Statement and control
 * claims are paired per live block because a Basic statement carrier beside
 * its own If or Switch Region is one materialization, not two.
 */
export function regionDuplicatedSSABlockCounts(
	region: Region,
	cfg: ImmutableCFG,
	ignoredSources: ReadonlySet<BlockAddr> = new AddressSet(),
): Map<BlockAddr, number> {
	const claims = regionOwnershipClaims(region);
	const liveAddresses = new AddressSet<BlockAddr>([
		...claims.statement.keys(),
		...claims.control.keys(),
	]);
	const sourceClaims = new Map<BlockAddr, number>();
	for (const address of sortedAddresses(liveAddresses)) {
		const block = cfg.blocks.get(address);
		if (!block) continue;
		const count = Math.max(
			claims.statement.get(address) ?? 0,
			claims.control.get(address) ?? 0,
		);
		for (const source of block.sourceAddresses) {
			if (ignoredSources.has(source)) continue;
			sourceClaims.set(source, (sourceClaims.get(source) ?? 0) + count);
		}
	}

	const duplicated = new Map<BlockAddr, number>();
	for (const source of sortedAddresses(sourceClaims.keys())) {
		const count = sourceClaims.get(source)!;
		if (count > 1) duplicated.set(source, count);
	}
	return duplicated;
}

/** Find incomplete or overlapping ownership in every nested Loop Region. */
export function loopRegionCoverageIssues(
	region: Region,
): LoopRegionCoverageIssue[] {
	const issues: LoopRegionCoverageIssue[] = [];
	const visit = (candidate: Region) => {
		if (candidate.kind === 'loop') {
			const subsumedHandlers = candidate.subsumedHandlers ??
				new AddressSet<BlockAddr>();
			const representedBody = regionStructuredBlocks(candidate.body)
				// A nested iterator loop represents its close/rethrow landing pad
				// through the recovered syntax rather than an emitted child Region.
				// That handler is still covered for every enclosing loop that owns it.
				.union(nestedSubsumedLoopHandlers(candidate.body))
				.union(
					new AddressSet([
						candidate.header,
						...(candidate.headerLatchBranch
							? [candidate.headerLatchBranch.latch]
							: []),
					]),
				);
			const claimedTrailers = candidate.sourceBlocks
				.difference(candidate.loopBlocks)
				.difference(subsumedHandlers);
			const representedTrailers = new AddressSet<BlockAddr>();
			const overlappingTrailers = new AddressSet<BlockAddr>();
			for (const exit of candidate.exits) {
				if (!exit.trailer) continue;
				const trailerBlocks = regionStructuredBlocks(exit.trailer);
				for (const block of trailerBlocks) {
					if (subsumedHandlers.has(block)) continue;
					if (
						candidate.loopBlocks.has(block) ||
						representedTrailers.has(block)
					) overlappingTrailers.add(block);
					representedTrailers.add(block);
				}
			}
			// Finalizer copies and iterator cleanup landing pads are owned without
			// being emitted: the represented `finally` or high-level loop syntax
			// executes their semantics once.
			const requiredBody = candidate.loopBlocks
				.difference(
					candidate.suppressedBodyBlocks ??
						new AddressSet<BlockAddr>(),
				)
				.difference(subsumedHandlers);
			const issue: LoopRegionCoverageIssue = {
				header: candidate.header,
				missingBodyBlocks: sortedAddresses(
					requiredBody.difference(representedBody),
				),
				unexpectedBodyBlocks: sortedAddresses(
					representedBody.difference(candidate.loopBlocks),
				),
				missingTrailerBlocks: sortedAddresses(
					claimedTrailers.difference(representedTrailers),
				),
				unexpectedTrailerBlocks: sortedAddresses(
					representedTrailers.difference(claimedTrailers),
				),
				overlappingTrailerBlocks: sortedAddresses(overlappingTrailers),
			};
			if (
				issue.missingBodyBlocks.length > 0 ||
				issue.missingTrailerBlocks.length > 0 ||
				issue.unexpectedTrailerBlocks.length > 0 ||
				issue.overlappingTrailerBlocks.length > 0
			) issues.push(issue);
		}
		for (const child of childRegions(candidate)) visit(child);
	};
	visit(region);
	return issues;
}

export function nestedSubsumedLoopHandlers(
	region: Region,
): AddressSet<BlockAddr> {
	const handlers = new AddressSet<BlockAddr>();
	visitRegions(region, (candidate) => {
		if (candidate.kind !== 'loop' || !candidate.subsumedHandlers) return;
		for (const handler of candidate.subsumedHandlers) handlers.add(handler);
	});
	return handlers;
}

function unionStructuredBlocks(
	regions: readonly Region[],
): AddressSet<BlockAddr> {
	return new AddressSet(
		regions.flatMap((region) => [...regionStructuredBlocks(region)]),
	);
}

/** Visit a Region and every Region nested inside it. */
export function visitRegions(
	region: Region,
	visit: (region: Region) => void,
) {
	visit(region);
	for (const child of childRegions(region)) visitRegions(child, visit);
}

function childRegions(region: Region): Region[] {
	switch (region.kind) {
		case 'sequence':
			return region.regions;
		case 'if':
			return [region.consequent, region.alternate];
		case 'switch':
			return [
				...region.cases.map((switchCase) => switchCase.body),
				region.defaultBody,
			];
		case 'tryCatch':
			return [region.body, region.handler];
		case 'tryFinally':
			return [region.body, region.finalizer];
		case 'loop':
			return [
				region.body,
				...region.exits.flatMap((exit) =>
					exit.trailer ? [exit.trailer] : []
				),
			];
		default:
			return [];
	}
}

function sortedAddresses(addresses: Iterable<BlockAddr>): BlockAddr[] {
	return [...addresses].toSorted((left, right) => left - right);
}

export type DeferredExit =
	| {
		kind: 'toJoin';
		edge: CFGEdge;
		target: BlockAddr;
		actions: EdgeAction[];
	}
	| {
		kind: 'loopBack';
		edge: CFGEdge;
		target: BlockAddr;
		actions: EdgeAction[];
	}
	| {
		kind: 'loopExit';
		edge: CFGEdge;
		target: BlockAddr;
		/**
		 * The labelled span this protected loop exit transfers out of; a bare
		 * `break` reaches only the innermost enclosing loop/switch.
		 */
		label?: string;
		actions: EdgeAction[];
	}
	| {
		kind: 'exception';
		edge: CFGEdge;
		handler: BlockAddr;
		actions: EdgeAction[];
	}
	| { kind: 'functionReturn'; edge?: CFGEdge; actions: EdgeAction[] }
	| { kind: 'functionThrow'; edge?: CFGEdge; actions: EdgeAction[] };

export type EdgeAction =
	| { kind: 'phi'; assignments: EdgePhiAssignment[] }
	| { kind: 'placedPhi'; assignments: EdgePhiAssignment[] }
	| { kind: 'finally'; action: FinallyCopyAction }
	| { kind: 'statement'; statement: t.Statement }
	| { kind: 'return'; argument?: t.Expression | null }
	| { kind: 'throw'; argument: t.Expression };

export interface EdgePhiAssignment {
	edge: CFGEdge;
	target: t.Identifier;
	value: t.Expression;
}

export interface FinallyCopyAction {
	canonical: BlockAddr;
	copyRoot: BlockAddr;
	ownerBlock?: BlockAddr;
	terminalOwnerBlock?: BlockAddr;
	next: BlockAddr | null;
	kind: 'tryTrailer' | 'catchTrailer' | 'abruptExitTrailer' | 'canonical';
	statements?: t.Statement[];
}
