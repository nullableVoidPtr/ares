import * as t from '@babel/types';
import traverse from '@babel/traverse';
import { type SSARegister, ssaRegisterEquals } from '../../../../ssa.ts';
import { AddressSet } from '../../../../utils/set.ts';
import { invertTest } from '../../../ast/expression.ts';
import { isDuplicableScalarExpression } from '../../utils.ts';
import {
	type CFGAnalyses,
	findWeakSESE,
	type WeakSESERegion,
} from '../algorithms/mod.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import {
	type CFGCompatibilityTelemetry,
	recordCFGCompatibilityAttempt,
} from '../compatibility.ts';
import { exclusiveArmPartition } from './armPartition.ts';
import {
	blockNeedsBranchRegion,
	type DeferredExit,
	emptyRegion,
	hasPrestructuredControl,
	isEmptyRegion,
	ledgerSnapshot,
	type Region,
	regionCoveredBlocks,
	regionUnstructuredBranches,
	restoreLedger,
} from '../regions/region.ts';
import {
	type RegionAt,
	structureStraightLineSequenceFrom,
} from './sequence.ts';

/** A two-way branch recovered from a short-circuit condition chain. */
export interface ShortCircuitBranch {
	test: t.Expression;
	/** Target reached when any short-circuit term decides the predicate. */
	sharedTarget: number;
	taken: number;
	fallthrough: number;
	takenSource: number;
	fallthroughSource: number;
	/** Intermediate blocks now represented by the compound test. */
	absorbed: number[];
	/** Generated declarations retained as conditional assignments in `test`. */
	bindings: string[];
}

interface InlinedBlockTest {
	test: t.Expression;
	bindings: string[];
}

/** Whether substituting this initializer can change neither effects nor identity. */
function predicateValueIsFreelyMovable(node: t.Expression): boolean {
	return (node.extra as { isNonVolatile?: boolean } | undefined)
				?.isNonVolatile === true ||
		isDuplicableScalarExpression(node);
}

function immediatePredicateValueUse(
	node: t.Expression,
	name: string,
): boolean {
	if (t.isIdentifier(node, { name })) return true;
	return t.isUnaryExpression(node) &&
		t.isExpression(node.argument) &&
		immediatePredicateValueUse(node.argument, name);
}

function generatedValueUseCount(
	expressions: readonly t.Expression[],
	name: string,
): number {
	let count = 0;
	for (const expression of expressions) {
		t.traverseFast(expression, (node) => {
			if (t.isIdentifier(node, { name })) count++;
		});
	}
	return count;
}

function substituteGeneratedValue(
	node: t.Expression,
	name: string,
	replacement: t.Expression,
): { expression: t.Expression; replaced: number } {
	let replaced = 0;
	const wrapped = t.file(t.program([
		t.expressionStatement(t.cloneNode(node, true)),
	]));
	traverse(wrapped, {
		noScope: true,
		Identifier(path) {
			if (!path.isReferencedIdentifier({ name })) return;
			path.replaceWith(t.cloneNode(replacement, true));
			replaced++;
		},
	});
	const [statement] = wrapped.program.body;
	if (!t.isExpressionStatement(statement)) {
		return { expression: t.cloneNode(node, true), replaced: 0 };
	}
	return { expression: statement.expression, replaced };
}

/**
 * Inline a block's condition into a single expression.
 *
 * The intermediate block of a short-circuit chain runs only when the first
 * condition does not decide the branch, so its computation may only be folded
 * into the compound test, never hoisted before it -- inside `||` or `&&` the
 * evaluation stays conditional, which is exactly the original semantics.
 *
 * Returns null unless every statement is a single generated-register
 * declaration. Private temporaries are substituted into the test. A temporary
 * read by a later chain block is instead retained as an ordered assignment in a
 * sequence expression and reported as a binding for the emitter to declare.
 */

function inlinedBlockTest(
	cfg: ImmutableCFG,
	address: number,
): InlinedBlockTest | null {
	const block = cfg.blocks.get(address);
	if (!block || block.terminator.kind !== 'if') return null;
	const definitions: {
		id: t.Identifier;
		init: t.Expression;
	}[] = [];
	const values = new Set<string>();
	for (const statement of block.body) {
		if (
			!t.isVariableDeclaration(statement) ||
			statement.declarations.length !== 1
		) return null;
		const [declarator] = statement.declarations;
		if (
			!declarator || !t.isIdentifier(declarator.id) ||
			!/^r\d+_\d+$/.test(declarator.id.name) ||
			declarator.init == null || !t.isExpression(declarator.init) ||
			values.has(declarator.id.name)
		) return null;
		definitions.push({
			id: declarator.id,
			init: declarator.init,
		});
		values.add(declarator.id.name);
	}

	const escaped = new Set<string>();
	if (values.size > 0) {
		for (const [other, candidate] of cfg.blocks) {
			if (other === address) continue;
			const noteEscapes = (node: t.Node) => {
				t.traverseFast(node, (child) => {
					if (t.isIdentifier(child) && values.has(child.name)) {
						escaped.add(child.name);
					}
				});
			};
			for (const statement of candidate.body) noteEscapes(statement);
			const terminator = candidate.terminator;
			const test = terminator.kind === 'if'
				? terminator.test
				: terminator.kind === 'switch'
				? terminator.discriminant
				: undefined;
			if (test) noteEscapes(test);
			if (escaped.size === values.size) break;
		}
	}

	let expressions: t.Expression[] = [
		t.cloneNode(block.terminator.test, true),
	];
	const bindings: string[] = [];
	for (const definition of definitions.toReversed()) {
		const name = definition.id.name;
		const useCount = generatedValueUseCount(expressions, name);
		if (!escaped.has(name)) {
			if (predicateValueIsFreelyMovable(definition.init)) {
				if (useCount === 0) continue;
				expressions = expressions.map((expression) =>
					substituteGeneratedValue(
						expression,
						name,
						definition.init,
					).expression
				);
				continue;
			}
			if (
				expressions.length === 1 &&
				immediatePredicateValueUse(expressions[0]!, name)
			) {
				const substituted = substituteGeneratedValue(
					expressions[0]!,
					name,
					definition.init,
				);
				if (substituted.replaced === useCount) {
					expressions[0] = substituted.expression;
					continue;
				}
			}
			if (useCount === 0) {
				expressions.unshift(t.cloneNode(definition.init, true));
				continue;
			}
		}

		expressions.unshift(t.assignmentExpression(
			'=',
			t.cloneNode(definition.id),
			t.cloneNode(definition.init, true),
		));
		bindings.unshift(name);
	}

	return {
		test: expressions.length === 1
			? expressions[0]!
			: t.sequenceExpression(expressions),
		bindings,
	};
}

/**
 * Whether merging two edges into the same target would lose a Phi.
 *
 * The folded branch reaches the shared target by one arm where the CFG had two
 * edges, so a Phi there may no longer be able to tell them apart.
 */
function mergingEdgesLosesPhi(
	cfg: ImmutableCFG,
	target: number,
	sources: readonly number[],
): boolean {
	const block = cfg.blocks.get(target);
	if (!block) return false;
	for (const instruction of block.ssaInstructions) {
		if (instruction.instruction !== 'Phi') continue;
		let first: SSARegister | undefined;
		for (const source of sources) {
			const values = [...instruction.sources]
				.filter(([address]) => cfg.ownersOfSource(address).has(source))
				.map(([, value]) => value);
			const value = values[0];
			// A contracted loop-forest node can stand in for a different concrete
			// predecessor. Without a source value for every edge, equality has not
			// been proved and folding would erase the path distinction.
			if (value == null) return true;
			if (
				values.some((candidate) => !ssaRegisterEquals(value, candidate))
			) {
				return true;
			}
			if (first == null) {
				first = value;
				continue;
			}
			if (!ssaRegisterEquals(first, value)) return true;
		}
	}
	return false;
}

function joinLogicalTerms(
	operator: '&&' | '||',
	terms: readonly t.Expression[],
): t.Expression {
	let expression = terms[0]!;
	for (const term of terms.slice(1)) {
		expression = t.logicalExpression(operator, expression, term);
	}
	return expression;
}

/**
 * Follow one candidate shared arm of a short-circuit guard chain.
 *
 * Every chain block has one edge to `sharedTarget`; its other edge evaluates
 * the next condition, until the final block selects the other structured arm.
 * The edge polarity may change at any point. That is how Hermes represents
 * mixed source predicates such as `a && b && c`: tests for `a` and `b` jump to
 * the failure arm, while the final test for `c` jumps to the success arm.
 */
function shortCircuitChainForSharedTarget(
	cfg: ImmutableCFG,
	sharedTarget: number,
	allowed?: AddressSet<number>,
	entryAddress = cfg.entry,
): ShortCircuitBranch | null {
	const entry = cfg.blocks.get(entryAddress);
	if (!entry || entry.terminator.kind !== 'if') return null;
	const sharedIsTaken = entry.terminator.taken === sharedTarget;
	if (
		sharedIsTaken ===
			(entry.terminator.fallthrough === sharedTarget)
	) return null;

	const terms: t.Expression[] = [];
	const sharedSources: number[] = [];
	const absorbed: number[] = [];
	const bindings = new Set<string>();
	const seen = new AddressSet<number>();
	let address = entryAddress;
	let finalTarget: number | null = null;

	while (seen.size < 64) {
		if (seen.has(address)) return null;
		seen.add(address);
		const block = cfg.blocks.get(address);
		if (!block || block.terminator.kind !== 'if') return null;
		const reachesSharedOnTaken = block.terminator.taken === sharedTarget;
		const reachesSharedOnFallthrough =
			block.terminator.fallthrough === sharedTarget;
		if (reachesSharedOnTaken === reachesSharedOnFallthrough) return null;

		const rawTest = address === entryAddress
			? { test: t.cloneNode(block.terminator.test, true), bindings: [] }
			: inlinedBlockTest(cfg, address);
		if (!rawTest) return null;
		for (const binding of rawTest.bindings) bindings.add(binding);
		sharedSources.push(address);
		if (address !== entryAddress) absorbed.push(address);

		// An OR predicate describes taking the common consequent. An AND
		// predicate describes avoiding the common alternate. Normalising each
		// term separately permits the branch polarity to change within the chain.
		terms.push(
			sharedIsTaken
				? reachesSharedOnTaken ? rawTest.test : invertTest(rawTest.test)
				: reachesSharedOnTaken
				? invertTest(rawTest.test)
				: rawTest.test,
		);

		const next = reachesSharedOnTaken
			? block.terminator.fallthrough
			: block.terminator.taken;
		const nextBlock = cfg.blocks.get(next);
		const nextCanContinue = (!allowed || allowed.has(next)) &&
			(cfg.normalPredecessors.get(next)?.size ?? 0) === 1 &&
			nextBlock?.terminator.kind === 'if' &&
			((nextBlock.terminator.taken === sharedTarget) !==
				(nextBlock.terminator.fallthrough === sharedTarget)) &&
			inlinedBlockTest(cfg, next) != null;
		if (!nextCanContinue) {
			finalTarget = next;
			break;
		}
		address = next;
	}

	// A one-block candidate is just the original branch, not a recovered chain.
	if (absorbed.length === 0 || finalTarget == null) return null;
	if (mergingEdgesLosesPhi(cfg, sharedTarget, sharedSources)) return null;

	if (sharedIsTaken) {
		return {
			test: joinLogicalTerms('||', terms),
			sharedTarget,
			taken: sharedTarget,
			fallthrough: finalTarget,
			takenSource: entryAddress,
			fallthroughSource: address,
			absorbed,
			bindings: [...bindings],
		};
	}
	return {
		test: joinLogicalTerms('&&', terms),
		sharedTarget,
		taken: finalTarget,
		fallthrough: sharedTarget,
		takenSource: address,
		fallthroughSource: entryAddress,
		absorbed,
		bindings: [...bindings],
	};
}

/**
 * Recover a maximal `c1 || c2` / `c1 && c2` guard chain from the branches the
 * bytecode lifts it to.
 *
 * Hermes lifts a short-circuit condition into two branches whose arms overlap:
 * for `||` both jump to the same consequent, for `&&` both fall through to the
 * same alternate. Neither arm is then a single-entry region -- the shared target
 * has two predecessors -- so no weak SESE exists and the whole function drops to
 * a skeleton. Recovering the compound condition restores an ordinary two-way
 * branch, and unlike collapsing the blocks it leaves the CFG alone, so the Phi
 * edges the collapse would have destroyed are still there.
 */
export function shortCircuitBranch(
	cfg: ImmutableCFG,
	allowed?: AddressSet<number>,
	entryAddress = cfg.entry,
): ShortCircuitBranch | null {
	const entry = cfg.blocks.get(entryAddress);
	if (!entry || entry.terminator.kind !== 'if') return null;

	for (
		const sharedTarget of [
			entry.terminator.taken,
			entry.terminator.fallthrough,
		]
	) {
		const branch = shortCircuitChainForSharedTarget(
			cfg,
			sharedTarget,
			allowed,
			entryAddress,
		);
		if (branch) return branch;
	}
	return null;
}

export function tryStructureIfRegion(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	regionAt?: RegionAt,
	allowed?: AddressSet<number>,
	allowAsymmetric = true,
	/** Structured-descriptor ledger, rolled back for discarded arm candidates. */
	ledger?: AddressSet<number>,
	compatibility?: CFGCompatibilityTelemetry,
): Region | null {
	// A proven shared-target chain is the exact source-level predicate. Prefer it
	// to an independently valid but partial outer If Region: the latter can omit
	// the shared arm and is then replaced by the labelled acyclic fallback before
	// this helper gets another opportunity to recover the chain.
	const folded = tryStructureIfRegionWith(
		cfg,
		analyses,
		true,
		regionAt,
		allowed,
		allowAsymmetric,
		ledger,
		compatibility,
	);
	if (folded) return folded;
	const direct = tryStructureIfRegionWith(
		cfg,
		analyses,
		false,
		regionAt,
		allowed,
		allowAsymmetric,
		ledger,
		compatibility,
	);
	if (direct) return direct;
	return allowAsymmetric ? directTerminalGuardRegion(cfg, allowed) : null;
}

/**
 * Join recovered from arm reachability when no postdominator proves one.
 *
 * A branch whose arms both leave the scope -- returning, throwing, or jumping
 * past it -- has no common postdominator, and a one-armed branch has none
 * either, because the arm that falls straight through is itself the
 * continuation. `exclusiveArmPartition` locates the resume point by ownership
 * rather than by proof: the node more than one arm reaches is shared
 * continuation, and when that set has a single entry it is where the branch
 * rejoins. Unlike a transfer-based arm skip this drops nothing -- both the
 * body and the continuation are still emitted, in order -- so it cannot strand
 * a definition the skipped path carried.
 */
function directTerminalGuardRegion(
	cfg: ImmutableCFG,
	allowed?: AddressSet<number>,
): Region | null {
	const header = cfg.blocks.get(cfg.entry);
	if (!header || header.terminator.kind !== 'if') return null;
	const taken = header.terminator.taken;
	const fallthrough = header.terminator.fallthrough;
	const terminalTarget = (target: number): boolean => {
		const block = cfg.blocks.get(target);
		return !!block &&
			!(cfg.isScript && block.terminator.kind === 'return') &&
			(block.terminator.kind === 'return' ||
				block.terminator.kind === 'throw' ||
				block.terminator.kind === 'unreachable');
	};
	const takenTerminal = terminalTarget(taken);
	const fallthroughTerminal = terminalTarget(fallthrough);
	if (takenTerminal === fallthroughTerminal) return null;
	const terminal = takenTerminal ? taken : fallthrough;
	const continuation = takenTerminal ? fallthrough : taken;
	if (allowed && !allowed.has(continuation)) return null;
	const headerHandlers = cfg.exceptionalSuccessors.get(cfg.entry);
	const terminalHandlers = cfg.exceptionalSuccessors.get(terminal);
	if (
		(headerHandlers?.size ?? 0) !== (terminalHandlers?.size ?? 0) ||
		[...headerHandlers ?? []].some((handler) =>
			!terminalHandlers?.has(handler)
		)
	) return null;
	const terminalRegion: Region = {
		kind: 'terminalReference',
		entry: terminal,
		edge: { from: cfg.entry, to: terminal, kind: 'normal' },
		sourceBlocks: new AddressSet(),
	};
	const empty = emptyRegion();
	return {
		kind: 'if',
		header: cfg.entry,
		branchEdges: {
			consequent: { from: cfg.entry, to: taken, kind: 'normal' },
			alternate: { from: cfg.entry, to: fallthrough, kind: 'normal' },
		},
		test: t.cloneNode(header.terminator.test, true),
		consequent: takenTerminal ? terminalRegion : empty,
		alternate: fallthroughTerminal ? terminalRegion : empty,
		join: continuation,
		sourceBlocks: new AddressSet([cfg.entry]),
	};
}

function partitionJoin(
	cfg: ImmutableCFG,
	takenTarget: number,
	fallthroughTarget: number,
): number | null {
	const nodes = new AddressSet<number>();
	const queue = [cfg.entry];
	while (queue.length > 0) {
		const at = queue.pop()!;
		if (nodes.has(at)) continue;
		nodes.add(at);
		for (const to of cfg.normalSuccessors.get(at) ?? []) queue.push(to);
	}
	return exclusiveArmPartition(
		cfg.entry,
		[takenTarget, fallthroughTarget],
		nodes,
		cfg.normalSuccessors,
	)?.trailerRoot ?? null;
}

function tryStructureIfRegionWith(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	foldShortCircuit: boolean,
	regionAt?: RegionAt,
	allowed?: AddressSet<number>,
	allowAsymmetric = true,
	ledger?: AddressSet<number>,
	compatibility?: CFGCompatibilityTelemetry,
): Region | null {
	const entry = cfg.blocks.get(cfg.entry);
	if (!entry || entry.terminator.kind !== 'if') return null;

	// A short-circuit chain is two branches whose arms overlap; recovering the
	// compound condition turns it back into the ordinary two-way branch the
	// source had, and the arms below are then single-entry regions.
	const folded = foldShortCircuit ? shortCircuitBranch(cfg, allowed) : null;
	const takenTarget = folded?.taken ?? entry.terminator.taken;
	const fallthroughTarget = folded?.fallthrough ??
		entry.terminator.fallthrough;

	// Prefer an immediate successor continuation over a later common
	// postdominator. The later node can make one arm subsume the other when the
	// non-direct arm contains a terminal side exit; the successor boundary is the
	// actual source-level join in that shape.
	const conventionalJoin = analyses.postdominators.nearestCommonPostdominator(
		fallthroughTarget,
		takenTarget,
	) ?? partitionJoin(cfg, takenTarget, fallthroughTarget);
	const sharedTargetTerminator = folded
		? cfg.blocks.get(folded.sharedTarget)?.terminator.kind
		: undefined;
	const foldedTerminalJoin = allowAsymmetric && folded &&
			(conventionalJoin == null ||
				sharedTargetTerminator === 'return' ||
				sharedTargetTerminator === 'throw' ||
				sharedTargetTerminator === 'unreachable')
		? foldedShortCircuitTerminalJoin(folded, cfg, allowed)
		: null;
	// The ordinary asymmetric rule reads the raw terminator. A folded predicate
	// instead carries its proven shared target explicitly; when its other target
	// terminates, that shared target is the source-level continuation.
	const asymmetricJoin = foldedTerminalJoin ??
		(allowAsymmetric && !folded
			? asymmetricSuccessorJoin(cfg, analyses, allowed)
			: null);
	const retryConventionalJoin = () =>
		asymmetricJoin == null ? null : tryStructureIfRegionWith(
			cfg,
			analyses,
			foldShortCircuit,
			regionAt,
			allowed,
			false,
			ledger,
			compatibility,
		);
	const join = asymmetricJoin ?? conventionalJoin;
	if (join == null) return null;

	// Region arms use ordinary JavaScript consequent/alternate semantics, so the
	// taken jump edge is the consequent and fallthrough is the alternate.
	const armOwners = new AddressSet([
		cfg.entry,
		...(folded?.absorbed ?? []),
	]);
	let boundedArmCollection = asymmetricJoin != null ||
		((cfg.blocks.size > 96 || analyses.naturalLoops.loops.length > 0) &&
			boundedArmBodiesFit(
				armOwners,
				takenTarget,
				fallthroughTarget,
				join,
				cfg,
				allowed,
			));
	let consequentSESE = findWeakSESE(takenTarget, join, {
		cfg,
		dominators: analyses.dominators,
		postdominators: analyses.postdominators,
	}, { boundedCyclicArm: boundedArmCollection });
	let alternateSESE = findWeakSESE(fallthroughTarget, join, {
		cfg,
		dominators: analyses.dominators,
		postdominators: analyses.postdominators,
	}, { boundedCyclicArm: boundedArmCollection });
	if (
		(!consequentSESE || !alternateSESE) && !boundedArmCollection &&
		boundedArmBodiesFit(
			armOwners,
			takenTarget,
			fallthroughTarget,
			join,
			cfg,
			allowed,
		)
	) {
		boundedArmCollection = true;
		consequentSESE = findWeakSESE(takenTarget, join, {
			cfg,
			dominators: analyses.dominators,
			postdominators: analyses.postdominators,
		}, { boundedCyclicArm: true });
		alternateSESE = findWeakSESE(fallthroughTarget, join, {
			cfg,
			dominators: analyses.dominators,
			postdominators: analyses.postdominators,
		}, { boundedCyclicArm: true });
	}
	if (!consequentSESE || !alternateSESE) return retryConventionalJoin();
	if (allowed) {
		consequentSESE = trimEnclosingExceptionalArm(
			consequentSESE,
			takenTarget,
			join,
			cfg,
			allowed,
		);
		alternateSESE = trimEnclosingExceptionalArm(
			alternateSESE,
			fallthroughTarget,
			join,
			cfg,
			allowed,
		);
	}
	if (foldedTerminalJoin != null) {
		// `findWeakSESE` normally adds an exception handler to any arm containing
		// a protected block. Here the enclosing Try Region already owns that
		// handler; the folded terminal arm is only the normally reachable path to
		// the explicit return/throw. Retaining the handler would make this nested
		// If claim its enclosing Catch and fail the bounded ownership check.
		if (takenTarget !== join) {
			consequentSESE = {
				...consequentSESE,
				body: normalArmBody(takenTarget, join, cfg),
			};
		}
		if (fallthroughTarget !== join) {
			alternateSESE = {
				...alternateSESE,
				body: normalArmBody(fallthroughTarget, join, cfg),
			};
		}
	}
	if (
		allowed &&
		analyses.naturalLoops.loops.length === 0 &&
		(!armFitsAllowed(consequentSESE.body, allowed, cfg) ||
			!armFitsAllowed(alternateSESE.body, allowed, cfg))
	) return retryConventionalJoin();

	const consequent = regionForWeakSESE(
		cfg,
		consequentSESE,
		regionAt,
		asymmetricJoin != null,
		ledger,
		compatibility,
		boundedArmCollection,
	);
	const alternate = regionForWeakSESE(
		cfg,
		alternateSESE,
		regionAt,
		asymmetricJoin != null,
		ledger,
		compatibility,
		boundedArmCollection,
	);
	if (!consequent || !alternate) return retryConventionalJoin();
	return {
		kind: 'if',
		header: cfg.entry,
		predicateBlocks: folded
			? new AddressSet([cfg.entry, ...folded.absorbed])
			: undefined,
		predicateBindings: folded?.bindings.length
			? folded.bindings
			: undefined,
		branchEdges: folded
			? {
				consequent: {
					from: folded.takenSource,
					to: folded.taken,
					kind: 'normal',
				},
				alternate: {
					from: folded.fallthroughSource,
					to: folded.fallthrough,
					kind: 'normal',
				},
			}
			: undefined,
		test: folded?.test ?? t.cloneNode(entry.terminator.test, true),
		consequent,
		alternate,
		join,
		conditionalValue: {
			kind: 'conditionalPhi',
			branch: cfg.entry,
			consequentEntry: takenTarget,
			alternateEntry: fallthroughTarget,
			join,
			forms: ['shortcut', 'ternary'],
		},
		sourceBlocks: new AddressSet([
			cfg.entry,
			...folded?.absorbed ?? [],
			...consequent.sourceBlocks,
			...alternate.sourceBlocks,
		]),
	};
}

/**
 * A branch nested in a protected body inherits exceptional edges to the
 * enclosing handler. Weak-SESE discovery includes that handler in each arm,
 * even though the surrounding Try Region already owns it, and the arm then
 * fails the protected-body ownership check. Remove only exceptional-only
 * blocks outside `allowed`; nested handlers remain because their blocks are
 * themselves part of the caller's bounded ownership set.
 */
function trimEnclosingExceptionalArm(
	region: WeakSESERegion,
	entry: number,
	boundary: number,
	cfg: ImmutableCFG,
	allowed: AddressSet<number>,
): WeakSESERegion {
	if (region.body.isSubsetOf(allowed)) return region;
	const normal = normalArmBody(entry, boundary, cfg);
	if (
		!normal.isSubsetOf(region.body) || !armFitsAllowed(normal, allowed, cfg)
	) {
		return region;
	}
	const owned = new AddressSet(
		[...region.body].filter((address) =>
			allowed.has(address) || normal.has(address)
		),
	);
	return { ...region, body: owned };
}

function normalArmBody(
	entry: number,
	boundary: number,
	cfg: ImmutableCFG,
): AddressSet<number> {
	const body = new AddressSet<number>();
	const pending = [entry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (
			address === boundary || body.has(address) ||
			!cfg.blocks.has(address)
		) {
			continue;
		}
		body.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
	}
	return body;
}

function armFitsAllowed(
	body: AddressSet<number>,
	allowed: AddressSet<number>,
	cfg: ImmutableCFG,
): boolean {
	return [...body].every((address) =>
		allowed.has(address) || isPureBoundaryPrelude(address, cfg)
	);
}

/**
 * Recover terminal short-circuit guards with no ordinary postdominator.
 *
 * Two shapes use the same folded predicate:
 *
 * - `if (a && b) throw; continuation` shares the continuation target.
 * - `if (a || b) return; continuation` shares the terminal target.
 *
 * In both cases the non-terminal successor is the lexical join. Accept it only
 * after proving the opposite arm terminates before it.
 */
function foldedShortCircuitTerminalJoin(
	folded: ShortCircuitBranch,
	cfg: ImmutableCFG,
	allowed?: AddressSet<number>,
): number | null {
	const otherTarget = folded.taken === folded.sharedTarget
		? folded.fallthrough
		: folded.taken;
	if (
		normalPathsTerminateBefore(
			otherTarget,
			folded.sharedTarget,
			cfg,
			allowed,
		)
	) return folded.sharedTarget;
	if (
		normalPathsTerminateBefore(
			folded.sharedTarget,
			otherTarget,
			cfg,
			allowed,
		)
	) return otherTarget;
	return null;
}

function normalPathsTerminateBefore(
	entry: number,
	boundary: number,
	cfg: ImmutableCFG,
	allowed?: AddressSet<number>,
): boolean {
	const visiting = new AddressSet<number>();
	const memo = new Map<number, boolean>();
	const visit = (address: number): boolean => {
		if (address === boundary || !cfg.blocks.has(address)) return false;
		if (
			allowed && !allowed.has(address) &&
			!isPureBoundaryPrelude(address, cfg)
		) return false;
		const cached = memo.get(address);
		if (cached != null) return cached;
		if (visiting.has(address)) return false;
		visiting.add(address);
		const terminator = cfg.blocks.get(address)!.terminator;
		let terminal: boolean;
		switch (terminator.kind) {
			case 'return':
			case 'throw':
			case 'unreachable':
				terminal = true;
				break;
			case 'goto':
				terminal = visit(terminator.target);
				break;
			case 'if':
				terminal = visit(terminator.fallthrough) &&
					visit(terminator.taken);
				break;
			case 'switch':
				terminal = visit(terminator.defaultTarget) &&
					terminator.cases.every((edge) => visit(edge.target));
				break;
		}
		visiting.delete(address);
		memo.set(address, terminal);
		return terminal;
	};
	return visit(entry);
}

/** A handler-free scalar copy can be moved across a protected entry safely. */
function isPureBoundaryPrelude(
	address: number,
	cfg: ImmutableCFG,
): boolean {
	if ((cfg.exceptionalSuccessors.get(address)?.size ?? 0) > 0) return false;
	const block = cfg.blocks.get(address);
	if (!block || block.terminator.kind !== 'goto') return false;
	return block.body.every((statement) => {
		if (
			!t.isVariableDeclaration(statement) ||
			statement.declarations.length !== 1
		) return false;
		const init = statement.declarations[0]?.init;
		return t.isIdentifier(init) || t.isLiteral(init) ||
			t.isThisExpression(init);
	});
}

/**
 * Whether `target` is reachable from `from` without passing through `barrier`.
 *
 * The barrier is the candidate join, so this answers "is this block inside the
 * arm" rather than "is it anywhere downstream".
 */
function reachesBeforeJoin(
	from: number,
	target: number,
	barrier: number,
	cfg: ImmutableCFG,
): boolean {
	if (from === barrier) return false;
	const seen = new AddressSet<number>([from]);
	const queue: number[] = [from];
	while (queue.length > 0) {
		const address = queue.pop()!;
		if (address === target) return true;
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (successor === barrier || seen.has(successor)) continue;
			seen.add(successor);
			queue.push(successor);
		}
	}
	return false;
}

/**
 * A terminal arm means the two successors have no common postdominator even
 * when one successor is the genuine continuation reached by the other arm.
 * Accept that successor as the join only when reachability is asymmetric and
 * the branch entry dominates the non-empty arm. The join itself remains
 * outside both arm bodies, so external predecessors are retained and Phi edge
 * actions stay attached to their original incoming edges.
 */
function asymmetricSuccessorJoin(
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	allowed?: AddressSet<number>,
): number | null {
	// This rule recovers a boundary from the raw branch graph. Once an ordinary
	// reducer has already composed control statements into a block, its remaining
	// edges no longer describe the interior of those statements and must use the
	// conventional postdominator rule.
	if (hasPrestructuredControl(cfg)) {
		return null;
	}
	const block = cfg.blocks.get(cfg.entry);
	if (!block || block.terminator.kind !== 'if') return null;
	const fallthrough = block.terminator.fallthrough;
	const taken = block.terminator.taken;
	const fallthroughIsBounded = allowed?.has(fallthrough) ?? false;
	const takenIsBounded = allowed?.has(taken) ?? false;
	let armEntry: number;
	let join: number;
	if (allowed && fallthroughIsBounded !== takenIsBounded) {
		// A recursive weak-SESE caller has already declared the outside successor
		// to be its boundary. Preserve that boundary even when the inside arm ends
		// through a terminal side exit and therefore cannot reach the join.
		armEntry = fallthroughIsBounded ? fallthrough : taken;
		join = fallthroughIsBounded ? taken : fallthrough;
	} else {
		let fallthroughReachesTaken = reachesBeforeJoin(
			fallthrough,
			taken,
			cfg.entry,
			cfg,
		);
		let takenReachesFallthrough = reachesBeforeJoin(
			taken,
			fallthrough,
			cfg.entry,
			cfg,
		);
		if (fallthroughReachesTaken === takenReachesFallthrough) {
			// An arm whose body throws has no normal successor, so the normal walk
			// sees no join. Its handler can still re-enter ordinary control before
			// the branch; include exceptional edges without crossing that branch.
			fallthroughReachesTaken = reachesIncludingHandlers(
				fallthrough,
				taken,
				cfg.entry,
				cfg,
			);
			takenReachesFallthrough = reachesIncludingHandlers(
				taken,
				fallthrough,
				cfg.entry,
				cfg,
			);
			if (fallthroughReachesTaken === takenReachesFallthrough) {
				return null;
			}
		}
		armEntry = fallthroughReachesTaken ? fallthrough : taken;
		join = fallthroughReachesTaken ? taken : fallthrough;
	}
	const ownedArm = collectOwnerClosedArm(
		new AddressSet([cfg.entry]),
		armEntry,
		join,
		cfg,
		allowed,
	);
	// The proof is local to this arm. Function size is irrelevant: a large Metro
	// function may contain a broad but still single-owner arm.
	if (!ownedArm) return null;
	// Natural-loop ownership is established by loopRegion. A nested arm may still
	// contain loops, but only admit the asymmetric boundary when every loop reached
	// from that arm is wholly owned by the caller's bounded region. This keeps an
	// immediate successor join from cutting through a loop or pulling a sibling
	// loop into the arm.
	for (const loop of analyses.naturalLoops.loops) {
		// Ask whether the loop is in *this arm*, which means reaching it without
		// crossing the join. Plain reachability counted every loop downstream of
		// the join as being in the arm, and because an arm cannot be verified
		// without a bounded region, one loop anywhere in the function made every
		// guard in it decline the asymmetric join.
		if (!reachesBeforeJoin(armEntry, loop.header, join, cfg)) continue;
		if (loop.body.has(join)) return null;
		// A bounded caller must keep every nested loop inside its declared arm.
		// At the top level the join already proved the loop is reached only from
		// this arm and that the join is not part of the loop body, so let
		// loopRegion own it instead of forcing the enclosing branch into a Basic
		// Region.
		if (allowed && !loop.body.isSubsetOf(allowed)) return null;
		if (hasUnsupportedBoundedLoopArm(loop, cfg)) return null;
	}
	if (!analyses.dominators.dominates(cfg.entry, armEntry)) return null;
	if (
		hasSharedNonTerminalBeforeJoin(
			armEntry,
			join,
			cfg,
			analyses,
			allowed,
		)
	) {
		return null;
	}
	return join;
}

function boundedArmBodiesFit(
	owners: AddressSet<number>,
	consequentEntry: number,
	alternateEntry: number,
	join: number,
	cfg: ImmutableCFG,
	allowed?: AddressSet<number>,
): boolean {
	const consequent = collectOwnerClosedArm(
		owners,
		consequentEntry,
		join,
		cfg,
		allowed,
	);
	const alternate = collectOwnerClosedArm(
		owners,
		alternateEntry,
		join,
		cfg,
		allowed,
	);
	if (!consequent || !alternate) return false;
	for (const address of alternate) {
		if (consequent.has(address)) return false;
	}
	return true;
}

/**
 * Collect an asymmetric arm without crossing its predicate or declared join,
 * then prove that every collected block is entered only by a predicate block
 * or another block in the arm. This admits protected and cyclic arms while
 * refusing a reachable sibling loop, shared loop exit, or another owner's
 * handler.
 */
function collectOwnerClosedArm(
	owners: AddressSet<number>,
	armEntry: number,
	join: number,
	cfg: ImmutableCFG,
	allowed?: AddressSet<number>,
): AddressSet<number> | null {
	const body = new AddressSet<number>();
	const pending = [armEntry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (
			owners.has(address) || address === join || body.has(address) ||
			!cfg.blocks.has(address)
		) continue;
		if (
			allowed && !allowed.has(address) &&
			!isPureBoundaryPrelude(address, cfg)
		) continue;
		body.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
		for (const successor of cfg.exceptionalSuccessors.get(address) ?? []) {
			pending.push(successor);
		}
	}
	for (const address of body) {
		for (
			const predecessor of [
				...(cfg.normalPredecessors.get(address) ?? []),
				...(cfg.exceptionalPredecessors.get(address) ?? []),
			]
		) {
			if (owners.has(predecessor) || body.has(predecessor)) continue;
			return null;
		}
	}
	return body;
}

/** Iterator recovery still has its own header/exit emission path. */
export function hasUnsupportedBoundedLoopArm(
	loop: CFGAnalyses['naturalLoops']['loops'][number],
	cfg: ImmutableCFG,
): boolean {
	return loopHeaderContainsIteratorNext(loop, cfg) &&
		hasIteratorHeaderExitPhi(loop, cfg);
}

function hasIteratorHeaderExitPhi(
	loop: CFGAnalyses['naturalLoops']['loops'][number],
	cfg: ImmutableCFG,
): boolean {
	if (!loopHeaderContainsIteratorNext(loop, cfg)) return false;
	for (const successor of cfg.normalSuccessors.get(loop.header) ?? []) {
		if (loop.body.has(successor)) continue;
		if (
			cfg.blocks.get(successor)?.ssaInstructions.some((instruction) =>
				instruction.instruction === 'Phi' &&
				instruction.sources.has(loop.header)
			)
		) return true;
	}
	return false;
}

function loopHeaderContainsIteratorNext(
	loop: CFGAnalyses['naturalLoops']['loops'][number],
	cfg: ImmutableCFG,
): boolean {
	for (const statement of cfg.blocks.get(loop.header)?.body ?? []) {
		let found = false;
		t.traverseFast(statement, (node) => {
			if (
				t.isCallExpression(node) &&
				t.isV8IntrinsicIdentifier(node.callee, { name: 'IteratorNext' })
			) found = true;
		});
		if (found) return true;
	}
	return false;
}

function hasSharedNonTerminalBeforeJoin(
	armEntry: number,
	join: number,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	allowed?: AddressSet<number>,
): boolean {
	const seen = new AddressSet<number>();
	const pending = [armEntry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (address === join || seen.has(address)) continue;
		// A side exit from a nested weak-SESE arm may point directly at the
		// enclosing continuation. It is not a shared subtree of this arm; retain it
		// as a deferred boundary edge and let the enclosing sequence close it.
		if (allowed && !allowed.has(address)) continue;
		if (
			address !== armEntry &&
			!analyses.dominators.dominates(armEntry, address)
		) {
			const terminator = cfg.blocks.get(address)?.terminator;
			if (
				terminator?.kind !== 'return' &&
				terminator?.kind !== 'throw' &&
				terminator?.kind !== 'unreachable'
			) return true;
			continue;
		}
		seen.add(address);
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (!seen.has(successor)) pending.push(successor);
		}
	}
	return false;
}

/**
 * Reachability that also follows exceptional edges.
 *
 * A protected block that throws has no normal successor, so the normal walk
 * reports the arm as terminal. Its handler still rejoins ordinary control flow,
 * and that rejoin is the branch's real continuation.
 */
function reachesIncludingHandlers(
	entry: number,
	target: number,
	barrier: number,
	cfg: ImmutableCFG,
): boolean {
	if (entry === barrier) return false;
	const seen = new AddressSet<number>([entry]);
	const pending = [entry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (address === target) return true;
		for (
			const successor of [
				...(cfg.normalSuccessors.get(address) ?? []),
				...(cfg.exceptionalSuccessors.get(address) ?? []),
			]
		) {
			if (successor === barrier || seen.has(successor)) continue;
			seen.add(successor);
			pending.push(successor);
		}
	}
	return false;
}

function regionForWeakSESE(
	cfg: ImmutableCFG,
	region: WeakSESERegion,
	regionAt?: RegionAt,
	materializeDeferredExits = false,
	ledger?: AddressSet<number>,
	compatibility?: CFGCompatibilityTelemetry,
	ownerClosed = false,
): Region | null {
	if (region.body.size === 0) {
		return {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		};
	}
	// Building the candidate claims any exception descriptor it forms. The
	// checks below may reject it, and a rejected candidate never reaches the
	// tree, so its claims are released before the fallback walk runs — otherwise
	// that walk is refused the same descriptor and drops the handler.
	const ledgerBefore = ledger ? ledgerSnapshot(ledger) : null;
	const recursivelyStructuredCandidate = regionAt?.(
		region.entry,
		region.body,
		true,
	);
	// The explicit weak-SESE exit belongs to the enclosing If Region. Recursive
	// bounded construction may encounter that outside-allowed terminal and create
	// a non-owning terminal reference for terminal-ladder use; retaining it here
	// would emit the shared return/throw inside one arm and consume the real join.
	const candidateContainsLoop = recursivelyStructuredCandidate != null &&
		containsLoopRegion(recursivelyStructuredCandidate);
	const exitHasPhi = region.normalExit != null &&
		hasPhiAt(region.normalExit, cfg);
	// Loop arms already defer a plain shared exit. For ordinary conditional arms,
	// do so only when the exit Phi is exactly what the enclosing If Region will
	// synthesize; applying this to every weak-SESE arm makes large terminal DAGs
	// recursively reconsider the same shared exits. Loop exits with Phis retain
	// their existing explicit terminal-reference path and edge-action handling.
	const shouldDeferNormalExit = (candidateContainsLoop && !exitHasPhi) ||
		(!candidateContainsLoop && exitHasPhi);
	const recursivelyStructured = recursivelyStructuredCandidate == null ||
			region.normalExit == null || !shouldDeferNormalExit
		? recursivelyStructuredCandidate
		: deferDeclaredNormalExit(
			recursivelyStructuredCandidate,
			region.normalExit,
		);
	const recursivelyCovered = recursivelyStructured == null
		? null
		: regionCoveredBlocks(recursivelyStructured);
	if (
		recursivelyStructured &&
		recursivelyStructured.sourceBlocks.isSubsetOf(region.body) &&
		region.body.isSubsetOf(recursivelyCovered!)
	) {
		// Complete coverage is not sufficient if a nested conditional was retained
		// as a basic block. Returning it commits the parent to a decomposition that
		// can no longer try the terminal-ladder path.
		if (
			materializeDeferredExits &&
			regionUnstructuredBranches(recursivelyStructured, cfg).size > 0
		) {
			if (ledger && ledgerBefore) restoreLedger(ledger, ledgerBefore);
			return null;
		}
		if (!materializeDeferredExits) return recursivelyStructured;
		const withDeferredExits = attachDeferredExits(
			recursivelyStructured,
			region,
			cfg,
		);
		if (withDeferredExits) return withDeferredExits;
		if (ledger && ledgerBefore) restoreLedger(ledger, ledgerBefore);
		return null;
	}
	if (ledger && ledgerBefore) restoreLedger(ledger, ledgerBefore);
	// Walk the arm with the recursive builder rather than blind: a block inside
	// it can open an exception region of its own, and without a child builder
	// the walk emits a Basic Region per block and the handler is never formed.
	const sequence = structureStraightLineSequenceFrom(
		cfg,
		region.entry,
		region.body,
		(childEntry, childAllowed) =>
			childEntry === region.entry
				// Reuse the candidate rather than declining: the arm's own entry
				// is where a try/catch opens, and re-entering `regionAt` here
				// would recurse forever. The walk then continues past whatever
				// that Region owns instead of restarting as a Basic block.
				? recursivelyStructured ?? null
				: regionAt?.(childEntry, childAllowed ?? region.body) ?? null,
	);
	if (
		sequence?.sourceBlocks.isSubsetOf(region.body) &&
		region.body.isSubsetOf(regionCoveredBlocks(sequence)) &&
		(!ownerClosed ||
			regionUnstructuredBranches(sequence, cfg).size === 0)
	) return sequence;
	// A bounded arm is an exact ownership contract. Falling back while a child
	// escaped it or left a branch raw would hide that defect from the enclosing
	// loop, which can instead recompose the whole body through its control forest.
	if (ownerClosed) return null;
	recordCFGCompatibilityAttempt(
		compatibility,
		'local-fallback-region',
		region.entry,
		'weak-SESE arm is not a straight-line sequence yet',
	);
	return {
		kind: 'fallback',
		entry: region.entry,
		sourceBlocks: region.body,
		reason: 'weak-SESE arm is not a straight-line sequence yet',
	};
}

function hasPhiAt(entry: number, cfg: ImmutableCFG): boolean {
	return cfg.blocks.get(entry)?.ssaInstructions.some((instruction) =>
		instruction.instruction === 'Phi'
	) ?? false;
}

function containsLoopRegion(region: Region): boolean {
	if (region.kind === 'loop') return true;
	switch (region.kind) {
		case 'sequence':
			return region.regions.some(containsLoopRegion);
		case 'if':
			return containsLoopRegion(region.consequent) ||
				containsLoopRegion(region.alternate);
		case 'switch':
			return region.cases.some((switchCase) =>
				containsLoopRegion(switchCase.body)
			) || containsLoopRegion(region.defaultBody);
		case 'tryCatch':
			return containsLoopRegion(region.body) ||
				containsLoopRegion(region.handler);
		case 'tryFinally':
			return containsLoopRegion(region.body) ||
				containsLoopRegion(region.finalizer);
		default:
			return false;
	}
}

function deferDeclaredNormalExit(
	region: Region,
	normalExit: number,
): Region {
	if (
		region.kind === 'terminalReference' &&
		region.exit == null &&
		region.entry === normalExit
	) {
		return {
			kind: 'sequence',
			regions: [],
			sourceBlocks: new AddressSet(),
		};
	}
	switch (region.kind) {
		case 'sequence':
			return {
				...region,
				regions: region.regions.map((child) =>
					deferDeclaredNormalExit(child, normalExit)
				),
			};
		case 'if':
			return {
				...region,
				consequent: deferDeclaredNormalExit(
					region.consequent,
					normalExit,
				),
				alternate: deferDeclaredNormalExit(
					region.alternate,
					normalExit,
				),
			};
		case 'switch':
			return {
				...region,
				cases: region.cases.map((switchCase) => ({
					...switchCase,
					body: deferDeclaredNormalExit(
						switchCase.body,
						normalExit,
					),
				})),
				defaultBody: deferDeclaredNormalExit(
					region.defaultBody,
					normalExit,
				),
			};
		case 'tryCatch':
			return {
				...region,
				body: deferDeclaredNormalExit(region.body, normalExit),
				handler: deferDeclaredNormalExit(region.handler, normalExit),
			};
		case 'tryFinally':
			return {
				...region,
				body: deferDeclaredNormalExit(region.body, normalExit),
				finalizer: deferDeclaredNormalExit(
					region.finalizer,
					normalExit,
				),
			};
		case 'loop':
			return {
				...region,
				body: deferDeclaredNormalExit(region.body, normalExit),
			};
		default:
			return region;
	}
}

/**
 * Materialize weak-SESE side exits inside the structured arm. The common
 * branch shape has one successor at the local join and one successor at an
 * enclosing join; an empty arm must therefore mean "leave this sequence", not
 * ordinary fallthrough.
 */
function attachDeferredExits(
	structured: Region,
	weak: WeakSESERegion,
	cfg: ImmutableCFG,
): Region | null {
	let result = structured;
	for (const exit of weak.deferredExits) {
		if (exit.kind !== 'toJoin') continue;
		if (regionCoveredBlocks(result).has(exit.target)) continue;
		if (representsExitEdge(result, exit.edge.from, exit.edge.to)) continue;
		const placed = placeDeferredExit(result, exit, cfg);
		if (!placed) return null;
		result = placed;
	}
	return result;
}

/** Return true when a nested Region already owns the exact CFG exit edge. */
function representsExitEdge(
	region: Region,
	from: number,
	to: number,
): boolean {
	if (
		region.kind === 'deferredExit' &&
		region.exit.kind === 'toJoin'
	) {
		return region.exit.edge.from === from && region.exit.edge.to === to;
	}
	if (
		region.kind === 'loop' &&
		region.exits.some((exit) => exit.from === from && exit.to === to)
	) return true;
	switch (region.kind) {
		case 'sequence':
			return region.regions.some((child) =>
				representsExitEdge(child, from, to)
			);
		case 'if':
			return representsExitEdge(region.consequent, from, to) ||
				representsExitEdge(region.alternate, from, to);
		case 'switch':
			return region.cases.some((switchCase) =>
				representsExitEdge(switchCase.body, from, to)
			) || representsExitEdge(region.defaultBody, from, to);
		case 'tryCatch':
			return representsExitEdge(region.body, from, to) ||
				representsExitEdge(region.handler, from, to);
		case 'tryFinally':
			return representsExitEdge(region.body, from, to) ||
				representsExitEdge(region.finalizer, from, to);
		case 'loop':
			return representsExitEdge(region.body, from, to) ||
				region.exits.some((exit) =>
					exit.trailer != null &&
					representsExitEdge(exit.trailer, from, to)
				);
		default:
			return false;
	}
}

function placeDeferredExit(
	region: Region,
	exit: Extract<DeferredExit, { kind: 'toJoin' }>,
	cfg: ImmutableCFG,
): Region | null {
	const deferred: Region = {
		kind: 'deferredExit',
		exit,
		sourceBlocks: new AddressSet(),
	};
	if (region.kind === 'if' && firstSourceBlock(region) === exit.edge.from) {
		const terminator = cfg.blocks.get(exit.edge.from)?.terminator;
		if (terminator?.kind !== 'if') return null;
		if (
			terminator.taken === exit.edge.to &&
			isEmptyRegion(region.consequent)
		) {
			return { ...region, consequent: deferred };
		}
		if (
			terminator.fallthrough === exit.edge.to &&
			isEmptyRegion(region.alternate)
		) {
			return { ...region, alternate: deferred };
		}
		return null;
	}
	if (region.kind === 'sequence') {
		const index = region.regions.findIndex((child) =>
			child.sourceBlocks.has(exit.edge.from)
		);
		if (index < 0) return null;
		const child = placeDeferredExit(region.regions[index]!, exit, cfg);
		if (!child) return null;
		const regions = [...region.regions];
		regions[index] = child;
		return { ...region, regions };
	}
	if (region.kind === 'basic' && region.sourceBlocks.has(exit.edge.from)) {
		const terminator = cfg.blocks.get(exit.edge.from)?.terminator;
		if (terminator?.kind !== 'goto' || terminator.target !== exit.edge.to) {
			return null;
		}
		return {
			kind: 'sequence',
			regions: [region, deferred],
			sourceBlocks: new AddressSet(region.sourceBlocks),
		};
	}
	return null;
}

function firstSourceBlock(region: Region): number | undefined {
	return [...region.sourceBlocks].toSorted((left, right) => left - right)[0];
}
