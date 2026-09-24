import generate from '@babel/generator';
import traverse from '@babel/traverse';
import * as t from '@babel/types';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import {
	flattenElseIfBlock,
	invertTest,
	rotateTerminatingGuardIntoElseIf,
} from '../../../ast/expression.ts';
import type { LiftedAST } from '../../../ast/mod.ts';
import { buildConditionalValueExpression } from '../../../ast/phi.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { PhiInst, SSARegister } from '../../../../ssa.ts';
import { reduceDelegateYieldLoopsInBody } from '../delegateYield.ts';
import {
	createLatchConditionResolver,
	removeLatchConditionDeclaration,
} from '../linear.ts';
import { registerName } from '../phi.ts';
import {
	type CFGDescriptors,
	iteratorCleanupRethrowRegister,
} from '../descriptors/mod.ts';
import type { CFGBlock, CFGEdge, ImmutableCFG } from '../immutableCFG.ts';
import type {
	DeferredExit,
	EdgeAction,
	LoopRegionExit,
	Region,
} from '../regions/region.ts';
import {
	isEmptyRegion,
	loopBreakDestinations,
	regionCoveredBlocks,
} from '../regions/region.ts';
import type { Terminator } from '../terminator.ts';

export interface EmitRegionResult {
	code: string;
	program: t.Program;
	statements: t.Statement[];
	diagnostics: string[];
}

export interface EmitRegionASTResult {
	program: t.Program;
	statements: t.Statement[];
	diagnostics: string[];
}

export function emitRegionToAST(
	region: Region,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
): EmitRegionASTResult {
	const diagnostics: string[] = [];
	const phiState = buildPhiEmitState(region, cfg, descriptors);
	const statements = emitRegion(
		region,
		cfg,
		descriptors,
		phiState,
		diagnostics,
	);
	reportUnplacedPhis(phiState, diagnostics);
	// A recovered loop closes its own iterator, and the machine's explicit close
	// can sit after the loop as well as inside it.
	const withoutMachineCloses = phiState.loopSyntaxes.reduce(
		(body, syntax) => stripSubsumedIteratorCloses(body, syntax),
		statements,
	);
	const statementsWithDeclarations = [
		...phiTargetDeclarations(phiState),
		...withoutMachineCloses,
	];
	reduceDelegateYieldLoopsInBody(statementsWithDeclarations);
	const withoutForwardLabels = simplifyForwardExitLabels(
		statementsWithDeclarations,
	);
	// Run again after the general simplifications. The forward-label lowering
	// only recognises a guard forest once inner scopes are already simplified,
	// so a single pass before them leaves labels standing whose reducible shape
	// only emerges later.
	const program = t.program(
		foldGuardedLoopExitTests(
			simplifyForwardExitLabels(
				simplifyEmittedStatements(withoutForwardLabels),
			),
		),
	);
	return { program, statements: program.body, diagnostics };
}

export function emitRegionToCode(
	region: Region,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
): EmitRegionResult {
	const ast = emitRegionToAST(region, cfg, descriptors);
	return {
		...ast,
		code: generate(ast.program).code,
	};
}

function scopedSwitchCaseBody(statements: t.Statement[]): t.Statement[] {
	return [t.blockStatement(statements)];
}

function emitRegion(
	region: Region,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	switch (region.kind) {
		case 'basic':
			return emitBasicRegion(region, cfg, phiState, diagnostics);
		case 'sequence': {
			const sequenceStatements = emitSequenceRegion(
				region.regions,
				cfg,
				descriptors,
				phiState,
				diagnostics,
			);
			if (region.exitLabel) {
				// A labelled sequence may have ordinary fallthrough edges alongside
				// labelled breaks. Keep the fallthrough Phi actions in the same lexical
				// scope as their source values; the edge-action ledger ensures an
				// enclosing arm cannot emit them again.
				sequenceStatements.push(
					...takePhiActionsForRegionExits(region, cfg, phiState),
				);
				const scoped = emitBlockScopedRegion(
					region,
					cfg,
					descriptors,
					phiState,
					diagnostics,
					{ statements: sequenceStatements },
				);
				return [
					...generatedLetDeclaration(scoped.hoisted),
					t.labeledStatement(
						t.identifier(region.exitLabel),
						t.blockStatement(scoped.statements),
					),
				];
			}
			return sequenceStatements;
		}
		case 'if': {
			const iteratorGuard = redundantIteratorGuardBody(
				region,
				cfg,
				phiState,
			);
			if (iteratorGuard) {
				return [
					...emitBlockStatements(
						region.header,
						cfg,
						phiState,
						diagnostics,
						true,
					),
					...takePhiActionsForEdge(
						iteratorGuard.bypassEdge,
						phiState,
					),
					...emitRegion(
						iteratorGuard.body,
						cfg,
						descriptors,
						phiState,
						diagnostics,
					),
					...takePhiActionsForRegionExits(
						iteratorGuard.body,
						cfg,
						phiState,
					),
				];
			}
			const ifHeader = region.header;
			const ifTerminator = cfg.blocks.get(ifHeader)?.terminator;
			const conditionalPhiTargets = conditionalPhiTargetsForIf(
				region,
				cfg,
				descriptors,
				phiState,
			);
			discardEquivalentFoldedPredicatePhiActions(
				region,
				cfg,
				phiState,
			);
			const consequentStatements = emitIfArm(
				region.consequent,
				region.branchEdges?.consequent ??
					(ifTerminator?.kind === 'if'
						? {
							from: ifHeader,
							to: ifTerminator.taken,
							kind: 'normal',
						}
						: null),
				cfg,
				descriptors,
				phiState,
				diagnostics,
			);
			const alternateStatements = emitIfArm(
				region.alternate,
				region.branchEdges?.alternate ??
					(ifTerminator?.kind === 'if'
						? {
							from: ifHeader,
							to: ifTerminator.fallthrough,
							kind: 'normal',
						}
						: null),
				cfg,
				descriptors,
				phiState,
				diagnostics,
			);
			const conditionalPhiDeclarations = trySynthesizeConditionalPhis(
				region.test,
				conditionalPhiTargets,
				consequentStatements,
				alternateStatements,
				phiState,
			);
			const deferredConditionalPhiDeclarations =
				conditionalPhiDeclarations == null
					? localizeDeferredConditionalPhis(
						region.test,
						conditionalPhiTargets,
						consequentStatements,
						alternateStatements,
						phiState,
					)
					: [];
			const ifStatement = t.ifStatement(
				t.cloneNode(region.test, true),
				t.blockStatement(consequentStatements),
				alternateStatements.length === 0
					? null
					: t.blockStatement(alternateStatements),
			);
			return [
				...emitBlockStatements(
					ifHeader,
					cfg,
					phiState,
					diagnostics,
					true,
				),
				...generatedLetDeclaration(
					new Set(region.predicateBindings ?? []),
				),
				...(conditionalPhiDeclarations ?? [
					...deferredConditionalPhiDeclarations,
					ifStatement,
				]),
			];
		}
		case 'switch': {
			const switchHeader = region.header;
			const switchDescriptor = descriptors.switches.switchByDispatch.get(
				switchHeader,
			);
			return [
				...(region.prelude ?? []).map((statement) =>
					t.cloneNode(statement, true)
				),
				...(switchDescriptor?.kind === 'terminator'
					? emitBlockStatements(
						switchHeader,
						cfg,
						phiState,
						diagnostics,
						true,
					).filter((statement) =>
						!statementContainsOnlyIntrinsicCall(
							statement,
							'UIntSwitchImm',
						) &&
						!statementContainsOnlyIntrinsicCall(
							statement,
							'StringSwitchImm',
						)
					)
					: []),
				t.switchStatement(
					t.cloneNode(region.discriminant, true),
					[
						...region.cases.flatMap((switchCase) => [
							...(switchCase.aliases ?? []).map((alias) =>
								t.switchCase(t.cloneNode(alias, true), [])
							),
							t.switchCase(
								switchCase.test
									? t.cloneNode(switchCase.test, true)
									: null,
								scopedSwitchCaseBody([
									...(switchCase.prefix ?? []).map((stmt) =>
										t.cloneNode(stmt, true)
									),
									...takePhiActionsForSwitchEntry(
										switchCase.source,
										switchCase.target,
										region.discriminant,
										switchCase.aliases?.length
											? null
											: switchCase.test,
										phiState,
									),
									...emitRegion(
										switchCase.body,
										cfg,
										descriptors,
										phiState,
										diagnostics,
									),
									...takePhiActionsForRegionExits(
										switchCase.body,
										cfg,
										phiState,
									),
									...(switchCase.completion === 'break'
										? [t.breakStatement()]
										: []),
								]),
							),
						]),
						t.switchCase(
							null,
							scopedSwitchCaseBody([
								...takePhiActionsForSwitchEntry(
									region.defaultSource,
									region.defaultTarget,
									region.discriminant,
									null,
									phiState,
								),
								...emitRegion(
									region.defaultBody,
									cfg,
									descriptors,
									phiState,
									diagnostics,
								),
								...takePhiActionsForRegionExits(
									region.defaultBody,
									cfg,
									phiState,
								),
							]),
						),
					],
				),
			];
		}
		case 'tryCatch': {
			const catchParameter = t.identifier('_e');
			const retryPreludeStatements = region.retryLoop?.prelude == null
				? []
				: emitBlockStatements(
					region.retryLoop.prelude,
					cfg,
					phiState,
					diagnostics,
					true,
				);
			// `try` and `catch` are block scopes. A value the protected body
			// computes and the code after the statement reads has to be declared
			// outside both, or it is emitted as a block-local `const` and read
			// where nothing declares it.
			const tryStatements = emitRegion(
				region.body,
				cfg,
				descriptors,
				phiState,
				diagnostics,
			);
			tryStatements.push(...takePhiActionsForRegionExits(
				region.body,
				cfg,
				phiState,
			));
			if (region.retryLoop) tryStatements.push(t.breakStatement());
			const tryBody = emitBlockScopedRegion(
				region.body,
				cfg,
				descriptors,
				phiState,
				diagnostics,
				{ statements: tryStatements },
			);
			const catchStatements = bindCatchIntrinsic(
				emitRegion(
					region.handler,
					cfg,
					descriptors,
					phiState,
					diagnostics,
				),
				catchParameter,
			);
			if (region.retryLoop?.conditionalExit) {
				catchStatements.push(...emitConditionalRetryExit(
					region.retryLoop,
					cfg,
					phiState,
				));
			} else {
				catchStatements.push(...takePhiActionsForRegionExits(
					region.handler,
					cfg,
					phiState,
				));
			}
			const catchBody = emitBlockScopedRegion(
				region.handler,
				cfg,
				descriptors,
				phiState,
				diagnostics,
				{ statements: catchStatements },
			);
			const statement = t.tryStatement(
				t.blockStatement(tryBody.statements),
				t.catchClause(
					catchParameter,
					t.blockStatement(catchBody.statements),
				),
			);
			return [
				...generatedLetDeclaration(
					new Set([...tryBody.hoisted, ...catchBody.hoisted]),
				),
				region.retryLoop
					? t.whileStatement(
						t.booleanLiteral(true),
						t.blockStatement([
							...retryPreludeStatements,
							statement,
						]),
					)
					: statement,
			];
		}
		case 'tryFinally': {
			const copyExitBody = rewriteFinalizerCopyExits(region);
			const nestedTryCatch = soleTryCatchRegion(copyExitBody);
			const copyPhiAssignments = finalizerCopyPhiAssignmentsForTryFinally(
				region,
				cfg,
				descriptors,
				phiState,
				nestedTryCatch,
			);
			const bodyStatements = nestedTryCatch ? null : emitRegion(
				copyExitBody,
				cfg,
				descriptors,
				phiState,
				diagnostics,
			);
			bodyStatements?.push(...takePhiActionsForRegionExits(
				copyExitBody,
				cfg,
				phiState,
			));
			if (!nestedTryCatch && bodyStatements) {
				bodyStatements.push(...copyPhiAssignments.body);
			}
			const nestedTryBodyStatements = nestedTryCatch
				? emitRegion(
					nestedTryCatch.body,
					cfg,
					descriptors,
					phiState,
					diagnostics,
				)
				: null;
			const nestedTryHandlerStatements = nestedTryCatch
				? bindCatchIntrinsic(
					emitRegion(
						nestedTryCatch.handler,
						cfg,
						descriptors,
						phiState,
						diagnostics,
					),
					t.identifier('_e'),
				)
				: null;
			if (nestedTryCatch && nestedTryBodyStatements) {
				nestedTryBodyStatements.push(...takePhiActionsForRegionExits(
					nestedTryCatch.body,
					cfg,
					phiState,
				));
				nestedTryBodyStatements.push(...copyPhiAssignments.body);
			}
			if (nestedTryCatch && nestedTryHandlerStatements) {
				nestedTryHandlerStatements.push(...takePhiActionsForRegionExits(
					nestedTryCatch.handler,
					cfg,
					phiState,
				));
				nestedTryHandlerStatements.push(...copyPhiAssignments.handler);
			}
			const finalizerStatements = [
				...takePhiActionsForFinallyEntry(region, phiState),
				...emitFinallyRegion(
					region.finalizer,
					cfg,
					descriptors,
					phiState,
					diagnostics,
				),
			];
			discardExceptionalFinalizerContinuationPhis(
				region,
				cfg,
				descriptors,
				phiState,
			);
			if (finalizerStatements.length === 0) {
				finalizerStatements.push(
					...emitFallbackFinalizerCandidate(
						region,
						cfg,
						descriptors,
						phiState,
					),
				);
			}
			// A recovered `for`-`of` closes its own iterator, so the loop
			// lowering deletes this finalizer, and the emptied statement stops
			// being a block scope at all. Nothing may be hoisted out of a block
			// that is about to stop existing: the declaration would be left
			// split from the statements it was hoisted over, in the same scope.
			const finalizerSurvivesLowering = phiState.loopSyntaxes.reduce(
				(body, syntax) => stripSubsumedIteratorCloses(body, syntax),
				finalizerStatements,
			).length > 0;
			// Each arm of the statement is its own block scope, so each one is
			// scoped separately, but only once it is known to become a block:
			// the no-finalizer path below splices the protected body straight
			// into the enclosing scope, where it needs no hoisting at all.
			const nestedTry = nestedTryCatch == null ? null : {
				body: emitBlockScopedRegion(
					nestedTryCatch.body,
					cfg,
					descriptors,
					phiState,
					diagnostics,
					{ statements: nestedTryBodyStatements ?? [] },
				),
				handler: emitBlockScopedRegion(
					nestedTryCatch.handler,
					cfg,
					descriptors,
					phiState,
					diagnostics,
					{ statements: nestedTryHandlerStatements ?? [] },
				),
			};
			const nestedTryStatement = nestedTry == null
				? null
				: t.tryStatement(
					t.blockStatement(nestedTry.body.statements),
					t.catchClause(
						t.identifier('_e'),
						t.blockStatement(nestedTry.handler.statements),
					),
				);
			const nestedHoisted = nestedTry == null ? [] : [
				...nestedTry.body.hoisted,
				...nestedTry.handler.hoisted,
			];
			if (finalizerStatements.length === 0) {
				if (bodyStatements != null) return bodyStatements;
				return [
					...generatedLetDeclaration(new Set(nestedHoisted)),
					nestedTryStatement!,
				];
			}
			const protectedBody =
				bodyStatements == null || !finalizerSurvivesLowering
					? null
					: emitBlockScopedRegion(
						region.body,
						cfg,
						descriptors,
						phiState,
						diagnostics,
						{ statements: bodyStatements },
					);
			const finalizer = !finalizerSurvivesLowering
				? null
				: emitBlockScopedRegion(
					region.finalizer,
					cfg,
					descriptors,
					phiState,
					diagnostics,
					{ statements: finalizerStatements },
				);
			const finalizerBlock = t.blockStatement(
				finalizer?.statements ?? finalizerStatements,
			);
			const tryStatement = nestedTryStatement
				? t.tryStatement(
					nestedTryStatement.block,
					nestedTryStatement.handler,
					finalizerBlock,
				)
				: t.tryStatement(
					t.blockStatement(
						protectedBody?.statements ?? bodyStatements ?? [],
					),
					null,
					finalizerBlock,
				);
			const hoisted = new Set([
				...nestedHoisted,
				...protectedBody?.hoisted ?? [],
				...finalizer?.hoisted ?? [],
			]);
			const label = firstLabelBreak(region.body);
			return [
				...generatedLetDeclaration(hoisted),
				label
					? t.labeledStatement(
						t.identifier(label),
						t.blockStatement([tryStatement]),
					)
					: tryStatement,
			];
		}
		case 'loop': {
			const effectiveRegion = inheritStructuredLoopExitActions(
				region,
				phiState,
			);
			return withEnclosingLoopExitActions(
				phiState,
				effectiveRegion.exits,
				() => {
					reportDivergentLoopBreaks(
						effectiveRegion,
						cfg,
						descriptors,
						phiState,
						diagnostics,
					);
					if (effectiveRegion.syntax) {
						return emitIteratorLoop(
							effectiveRegion,
							cfg,
							descriptors,
							phiState,
							diagnostics,
						);
					}
					const numericForLoop = emitNumericForLoop(
						effectiveRegion,
						cfg,
						descriptors,
						phiState,
						diagnostics,
					);
					if (numericForLoop) return numericForLoop;
					const entryActions = takePhiActionsForLoopEntry(
						effectiveRegion,
						cfg,
						phiState,
					);
					const bodyRegion = rewriteDeferredExitsForLoop(
						effectiveRegion.body,
						effectiveRegion,
						cfg,
						descriptors,
						phiState.regionBlocks,
					);
					const bodyStatements = emitRegion(
						bodyRegion,
						cfg,
						descriptors,
						phiState,
						diagnostics,
					);
					// A header branch can skip the ordinary body directly to a distinct
					// latch. Both arms still execute that latch's statements before its
					// backedge; emitting only the incoming Phi actions leaves the latch's
					// definitions unbound on either path.
					const headerLatchStatements =
						effectiveRegion.headerLatchBranch
							? emitBlockStatements(
								effectiveRegion.headerLatchBranch.latch,
								cfg,
								phiState,
								diagnostics,
								true,
							)
							: [];
					const backedgeActions = takePhiActionsForLoopBackedges(
						effectiveRegion,
						phiState,
					);
					const normalizedBodyStatements = bodyStatements;
					const latchControl = emitLoopLatchControlFlow(
						effectiveRegion,
						cfg,
						descriptors,
						phiState,
						diagnostics,
					);
					// A protected range that opens at the header makes the body's `try`
					// the owner of those statements; emitting them here as well would
					// run them twice, once outside the protection they belong to.
					const headerStatements = effectiveRegion.bodyOwnsHeader
						? []
						: emitBlockStatements(
							effectiveRegion.header,
							cfg,
							phiState,
							diagnostics,
							true,
						);
					const headerLatchControl = effectiveRegion.headerLatchBranch
						? emitLoopHeaderLatchBranch(
							effectiveRegion,
							bodyStatements,
							cfg,
							phiState,
						)
						: null;
					// A self-loop header computes its branch after executing the block body.
					// Emitting the same terminator as both an entry guard and latch guard drops
					// the first/last iteration and duplicates the test.
					const controlFlow = effectiveRegion.headerLatchBranch ||
							effectiveRegion.bodyOwnsHeader ||
							effectiveRegion.latches.includes(
								effectiveRegion.header,
							)
						? []
						: emitLoopHeaderControlFlow(
							effectiveRegion,
							cfg,
							descriptors,
							phiState,
							diagnostics,
						);
					const loopBody = emitBlockScopedRegion(
						effectiveRegion,
						cfg,
						descriptors,
						phiState,
						diagnostics,
						{
							statements: [
								...headerStatements,
								...controlFlow,
								...(headerLatchControl ??
									normalizedBodyStatements),
								...headerLatchStatements,
								...latchControl,
								...backedgeActions,
							],
						},
					);
					const loop = t.whileStatement(
						t.booleanLiteral(true),
						t.blockStatement(loopBody.statements),
					);
					return [
						...entryActions,
						...generatedLetDeclaration(loopBody.hoisted),
						labelLoopWhenReferenced(loop, effectiveRegion.label),
					];
				},
			);
		}
		case 'delegateYield': {
			// `yield*` subsumes the machine's own blocks and the `.throw()`
			// forwarding handler with them, so the landing-pad Phi state staged
			// for those blocks has no reader left. Leaving it in the ledger
			// reports an unplaced exceptional Phi state and costs the whole
			// function its Region.
			for (const block of region.sourceBlocks) {
				phiState.sameValueAssignmentsByBlock.delete(block);
				phiState.exceptionalStateAssignmentsByBlock.delete(block);
			}
			const yieldExpr = t.yieldExpression(
				t.cloneNode(region.argument, true),
				true,
			);
			const target = region.completion === 'assigned' &&
					region.completionTarget
				? t.cloneNode(region.completionTarget, true)
				: null;
			const head = target == null ? t.expressionStatement(yieldExpr) : (
				// The exit block keeps its own statements when the delegate does
				// not own it, so the declaration this `yield*` replaces was
				// suppressed there and has to reappear here.
				region.declaresCompletionTarget
					? t.variableDeclaration('const', [
						t.variableDeclarator(target, yieldExpr),
					])
					: t.expressionStatement(
						t.assignmentExpression('=', target, yieldExpr),
					)
			);
			return [
				...(region.preludeStatements ?? []).map((stmt) =>
					t.cloneNode(stmt, true)
				),
				head,
				...(region.trailing ?? []).map((stmt) =>
					t.cloneNode(stmt, true)
				),
			];
		}
		case 'break':
			return emitEmbeddedLoopExit(
				region.exit,
				t.breakStatement(),
				cfg,
				descriptors,
				phiState,
				diagnostics,
			);
		case 'continue':
			return emitEmbeddedLoopExit(
				region.exit,
				t.continueStatement(),
				cfg,
				descriptors,
				phiState,
				diagnostics,
			);
		case 'labelBreak':
			return emitEmbeddedLoopExit(
				region.exit,
				t.breakStatement(t.identifier(region.label)),
				cfg,
				descriptors,
				phiState,
				diagnostics,
			);
		case 'labelContinue':
			return emitEmbeddedLoopExit(
				region.exit,
				t.continueStatement(t.identifier(region.label)),
				cfg,
				descriptors,
				phiState,
				diagnostics,
			);
		case 'deferredExit':
			return emitDeferredExit(region.exit, phiState);
		case 'return':
			return [
				t.returnStatement(
					region.argument ? t.cloneNode(region.argument, true) : null,
				),
			];
		case 'throw':
			return [t.throwStatement(t.cloneNode(region.argument, true))];
		case 'terminalReference':
			return [
				...(region.exit
					? emitLoopExitActions(
						region.exit,
						cfg,
						descriptors,
						phiState,
						diagnostics,
					)
					: region.edge == null
					? []
					: takePhiActionsForEdge(region.edge, phiState)),
				...emitBlockStatements(
					region.entry,
					cfg,
					phiState,
					diagnostics,
					false,
					true,
				),
			];
		case 'fallback':
			diagnostics.push(
				`fallback region at 0x${
					region.entry.toString(16)
				}: ${region.reason}`,
			);
			return [
				t.expressionStatement(
					t.stringLiteral(
						`unsupported fallback 0x${
							region.entry.toString(16)
						}: ${region.reason}`,
					),
				),
			];
	}
}

function emitSequenceRegion(
	regions: readonly Region[],
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	const statements: t.Statement[] = [];
	for (let i = 0; i < regions.length; i++) {
		const region = regions[i]!;
		if (i > 0) {
			statements.push(...takePhiActionsBetweenRegions(
				regions[i - 1]!,
				region,
				cfg,
				phiState,
			));
		}
		const iteratorBypass = region.kind === 'if'
			? redundantIteratorGuardBeforeSiblingLoop(
				region,
				regions[i + 1],
				cfg,
			)
			: null;
		if (iteratorBypass) {
			statements.push(...emitBlockStatements(
				iteratorBypass.from,
				cfg,
				phiState,
				diagnostics,
				true,
			));
			statements.push(...takePhiActionsForEdge(
				iteratorBypass,
				phiState,
			));
			continue;
		}
		statements.push(...emitRegion(
			region,
			cfg,
			descriptors,
			phiState,
			diagnostics,
		));
	}
	if (regions.length > 0) {
		statements.push(...takePhiActionsForTrailingSequenceRegion(
			regions.at(-1)!,
			cfg,
			phiState,
		));
	}
	return statements;
}

function redundantIteratorGuardBeforeSiblingLoop(
	guard: Extract<Region, { kind: 'if' }>,
	next: Region | undefined,
	cfg: ImmutableCFG,
): CFGEdge | null {
	if (
		next?.kind !== 'loop' || next.syntax?.kind !== 'forIn' ||
		next.syntax.preheader?.block !== guard.header
	) return null;
	const terminator = cfg.blocks.get(guard.header)?.terminator;
	if (terminator?.kind !== 'if') return null;
	const consequentTerminal = iteratorGuardBypassTarget(guard.consequent, cfg);
	const alternateTerminal = iteratorGuardBypassTarget(guard.alternate, cfg);
	const consequentEmpty = isEmptyRegion(guard.consequent);
	const alternateEmpty = isEmptyRegion(guard.alternate);
	// An enclosing conditional may already own the shared terminal, leaving both
	// guard arms empty even though the CFG edge still bypasses this loop. Recover
	// that edge directly from the preheader terminator and the loop exit.
	if (consequentEmpty && alternateEmpty) {
		const terminal = terminator.taken === next.header
			? terminator.fallthrough
			: terminator.fallthrough === next.header
			? terminator.taken
			: null;
		if (
			terminal != null &&
			next.exits.some((exit) => exit.to === terminal)
		) {
			return {
				from: guard.header,
				to: terminal,
				kind: 'normal',
			};
		}
	}
	if (
		!((consequentTerminal != null && alternateEmpty) ||
			(alternateTerminal != null && consequentEmpty))
	) return null;
	const terminal = consequentTerminal ?? alternateTerminal!;
	const loopTarget = consequentTerminal != null
		? terminator.fallthrough
		: terminator.taken;
	const terminalTarget = consequentTerminal != null
		? terminator.taken
		: terminator.fallthrough;
	if (
		loopTarget !== next.header || terminalTarget !== terminal ||
		!next.exits.some((exit) => exit.to === terminal)
	) return null;
	return {
		from: guard.header,
		to: terminal,
		kind: 'normal',
	};
}

function iteratorGuardBypassTarget(
	region: Region,
	cfg: ImmutableCFG,
): number | null {
	switch (region.kind) {
		case 'terminalReference':
			return region.entry;
		case 'continue':
		case 'labelContinue':
		case 'labelBreak':
			return region.target;
		case 'sequence': {
			// A bypass that leaves an enclosing labelled scope carries its edge
			// action next to the break; the guard's own emission re-takes that
			// action, so the pair still names one target.
			const targets = region.regions.flatMap((child) =>
				child.kind === 'deferredExit'
					? []
					: [iteratorGuardBypassTarget(child, cfg)]
			);
			return targets.length === 1 ? targets[0]! : null;
		}
		case 'basic': {
			// A guard arm may own the shared terminal block rather than reference
			// it. The loop's own return/throw exit re-emits that block, so erasing
			// the redundant guard still leaves exactly one copy.
			const blocks = [...region.sourceBlocks];
			const terminator = blocks.length === 1
				? cfg.blocks.get(blocks[0]!)?.terminator
				: undefined;
			return terminator?.kind === 'return' || terminator?.kind === 'throw'
				? blocks[0]!
				: null;
		}
		default:
			return null;
	}
}

function emitConditionalRetryExit(
	retry: NonNullable<
		Extract<Region, { kind: 'tryCatch' }>['retryLoop']
	>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
): t.Statement[] {
	const conditional = retry.conditionalExit;
	if (!conditional) return [];
	const block = cfg.blocks.get(conditional.decision);
	if (!block || block.terminator.kind !== 'if') return [];
	const retryStatements = takePhiActionsForEdge(retry.backedge, phiState);
	const exitStatements = [
		...takePhiActionsForEdge(conditional.exit, phiState),
		t.breakStatement(),
	];
	const retriesOnTaken = block.terminator.taken === retry.header;
	return [t.ifStatement(
		t.cloneNode(block.terminator.test, true),
		t.blockStatement(retriesOnTaken ? retryStatements : exitStatements),
		t.blockStatement(retriesOnTaken ? exitStatements : retryStatements),
	)];
}

function emitIfArm(
	arm: Region,
	emptyArmEdge: CFGEdge | null,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	if (arm.kind === 'terminalReference') {
		return [
			...(arm.edge == null && emptyArmEdge != null
				? takePhiActionsForEdge(emptyArmEdge, phiState)
				: []),
			...emitRegion(
				arm,
				cfg,
				descriptors,
				phiState,
				diagnostics,
			),
		];
	}
	if (isEmptyRegion(arm)) {
		return emptyArmEdge == null
			? []
			: takePhiActionsForEdge(emptyArmEdge, phiState);
	}
	return [
		...(emptyArmEdge == null
			? []
			: takePhiActionsForEdge(emptyArmEdge, phiState)),
		...emitRegion(arm, cfg, descriptors, phiState, diagnostics),
		...takePhiActionsForRegionExits(arm, cfg, phiState),
	];
}

function conditionalPhiTargetsForIf(
	region: Extract<Region, { kind: 'if' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
): string[] {
	const candidate = region.conditionalValue;
	// A divergent branch has no continuation block, so there is no Phi to merge
	// and nothing to name as a conditional value.
	if (region.join == null) return [];
	if (candidate && candidate.join !== region.join) return [];
	const header = candidate?.branch ?? firstSourceBlock(region);
	const terminator = cfg.blocks.get(header)?.terminator;
	if (terminator?.kind !== 'if') return [];
	const consequentEntry = candidate?.consequentEntry ?? terminator.taken;
	const alternateEntry = candidate?.alternateEntry ?? terminator.fallthrough;
	const consequentSource = region.branchEdges?.consequent.from ?? header;
	const alternateSource = region.branchEdges?.alternate.from ?? header;

	const targets: string[] = [];
	for (const phi of descriptors.phis.phisByBlock.get(region.join) ?? []) {
		if (phiState.ambiguousConditionalPhiTargets.has(phi.target.name)) {
			continue;
		}
		const owner = phiState.conditionalPhiOwners.get(phi.target.name);
		if (owner) {
			if (owner === region) targets.push(phi.target.name);
			continue;
		}
		let hasConsequentIncoming = false;
		let hasAlternateIncoming = false;
		let isConditionalMerge = phi.incoming.size >= 2;
		for (const assignment of phi.incoming.values()) {
			const from = assignment.edge.from;
			const fromConsequent = region.consequent.sourceBlocks.has(from) ||
				(isEmptyRegion(region.consequent) &&
					from === consequentSource &&
					consequentEntry === region.join);
			const fromAlternate = region.alternate.sourceBlocks.has(from) ||
				(isEmptyRegion(region.alternate) && from === alternateSource &&
					alternateEntry === region.join);
			if (fromConsequent === fromAlternate) {
				isConditionalMerge = false;
				break;
			}
			hasConsequentIncoming ||= fromConsequent;
			hasAlternateIncoming ||= fromAlternate;

			// Same-value and otherwise-special Phis are not represented by ordinary
			// edge actions. Leave those on their existing lowering path.
			const action = phiState.actionsByEdge.get(edgeKey(assignment.edge));
			if (
				!action?.assignments.some((candidate) =>
					candidate.target.name === phi.target.name
				)
			) {
				isConditionalMerge = false;
				break;
			}
		}
		if (
			isConditionalMerge && hasConsequentIncoming &&
			hasAlternateIncoming
		) {
			targets.push(phi.target.name);
		}
	}
	return targets;
}
interface ConditionalPhiOwnership {
	owners: Map<string, Extract<Region, { kind: 'if' }>>;
	ambiguousTargets: Set<string>;
}

function collectConditionalPhiOwnership(
	root: Region,
	descriptors: CFGDescriptors,
): ConditionalPhiOwnership {
	const candidates = new Map<
		string,
		Array<Extract<Region, { kind: 'if' }>>
	>();
	visitRegions(root, (region) => {
		if (region.kind !== 'if' || region.join == null) return;
		for (const phi of descriptors.phis.phisByBlock.get(region.join) ?? []) {
			if (
				phi.incoming.size < 2 ||
				[...phi.incoming.values()].some((assignment) =>
					!region.sourceBlocks.has(assignment.edge.from)
				)
			) continue;
			const regions = candidates.get(phi.target.name) ?? [];
			regions.push(region);
			candidates.set(phi.target.name, regions);
		}
	});

	const owners = new Map<string, Extract<Region, { kind: 'if' }>>();
	const ambiguousTargets = new Set<string>();
	for (const [target, regions] of candidates) {
		const largestSize = Math.max(
			...regions.map((region) => region.sourceBlocks.size),
		);
		const largest = regions.filter((region) =>
			region.sourceBlocks.size === largestSize
		);
		if (largest.length === 1) owners.set(target, largest[0]);
		else ambiguousTargets.add(target);
	}
	return { owners, ambiguousTargets };
}

/**
 * A folded short-circuit predicate represents several CFG edges to its shared
 * arm with one JavaScript edge. `shortCircuitBranch` only permits that fold
 * when every Phi sees the same SSA value on those edges. Keep the action for
 * the representative branch edge and discard its equivalent absorbed copies;
 * otherwise the copies either become duplicate assignments or remain in the
 * edge ledger after emission.
 */
function discardEquivalentFoldedPredicatePhiActions(
	region: Extract<Region, { kind: 'if' }>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
) {
	if (!region.predicateBlocks || !region.branchEdges) return;
	for (
		const representative of [
			region.branchEdges.consequent,
			region.branchEdges.alternate,
		]
	) {
		const representativeAction = phiState.actionsByEdge.get(
			edgeKey(representative),
		);
		if (!representativeAction) continue;
		for (const source of region.predicateBlocks) {
			if (source === representative.from) continue;
			if (
				cfg.normalSuccessors.get(source)?.has(representative.to) !==
					true
			) {
				continue;
			}
			const edge = {
				from: source,
				to: representative.to,
				kind: 'normal' as const,
			};
			const action = phiState.actionsByEdge.get(edgeKey(edge));
			if (
				!action || !equivalentPhiAssignments(
					action.assignments,
					representativeAction.assignments,
				)
			) continue;
			phiState.actionsByEdge.delete(edgeKey(edge));
		}
	}
}

function equivalentPhiAssignments(
	left: PhiEdgeAction['assignments'],
	right: PhiEdgeAction['assignments'],
): boolean {
	if (left.length !== right.length) return false;
	return left.every((assignment) => {
		const candidate = right.find((other) =>
			other.target.name === assignment.target.name
		);
		return candidate != null &&
			t.isNodesEquivalent(candidate.value, assignment.value);
	});
}

function trySynthesizeConditionalPhis(
	test: t.Expression,
	targets: readonly string[],
	consequentStatements: readonly t.Statement[],
	alternateStatements: readonly t.Statement[],
	phiState: PhiEmitState,
): t.VariableDeclaration[] | null {
	if (targets.length === 0) return null;

	let values:
		| Array<{
			target: string;
			consequent: t.Expression;
			alternate: t.Expression;
		}>
		| null = null;
	if (targets.length === 1) {
		const [target] = targets;
		const consequent = conditionalPhiArmExpression(
			consequentStatements,
			target,
		);
		const alternate = conditionalPhiArmExpression(
			alternateStatements,
			target,
		);
		if (consequent && alternate) {
			values = [{ target, consequent, alternate }];
		}
	} else if (isPureCondition(test)) {
		const consequent = conditionalPhiArmAssignments(
			consequentStatements,
			targets,
		);
		const alternate = conditionalPhiArmAssignments(
			alternateStatements,
			targets,
		);
		if (consequent && alternate) {
			values = targets.map((target) => ({
				target,
				consequent: consequent.get(target)!,
				alternate: alternate.get(target)!,
			}));
		}
	}
	if (!values) return null;
	if (
		expressionsReferenceNames(
			[
				test,
				...values.flatMap(({ consequent, alternate }) => [
					consequent,
					alternate,
				]),
			],
			phiState.patternBoundNames,
		)
	) return null;

	for (const { target } of values) {
		phiState.declaredPhiTargets.delete(target);
	}
	return values.map(({ target, consequent, alternate }) =>
		t.variableDeclaration('const', [
			t.variableDeclarator(
				t.identifier(target),
				buildConditionalValueExpression(
					t.cloneNode(test, true),
					t.cloneNode(consequent, true),
					t.cloneNode(alternate, true),
				),
			),
		])
	);
}

function expressionsReferenceNames(
	expressions: readonly t.Expression[],
	names: ReadonlySet<string>,
): boolean {
	return nodesReferenceNames(expressions, names);
}

function localizeDeferredConditionalPhis(
	test: t.Expression,
	targets: readonly string[],
	consequentStatements: readonly t.Statement[],
	alternateStatements: readonly t.Statement[],
	phiState: PhiEmitState,
): t.VariableDeclaration[] {
	if (targets.length === 0) return [];
	if (
		nodesReferenceNames(
			[test, ...consequentStatements, ...alternateStatements],
			phiState.patternBoundNames,
		)
	) return [];

	const declarations = targets.map((target) => {
		const declaration = t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier(target)),
		]);
		(declaration as LiftedAST<t.VariableDeclaration>).extra = {
			...(declaration as LiftedAST<t.VariableDeclaration>).extra,
			isPotentialConditionalValue: true,
		};
		phiState.declaredPhiTargets.delete(target);
		return declaration;
	});
	return declarations;
}

function nodesReferenceNames(
	nodes: readonly t.Node[],
	names: ReadonlySet<string>,
): boolean {
	if (names.size === 0) return false;
	let found = false;
	for (const node of nodes) {
		t.traverseFast(node, (child) => {
			if (found) return t.traverseFast.skip;
			if (t.isIdentifier(child) && names.has(child.name)) found = true;
		});
		if (found) return true;
	}
	return false;
}

function conditionalPhiArmExpression(
	statements: readonly t.Statement[],
	target: string,
): t.Expression | null {
	if (statements.length === 1) {
		const assignment = simpleIdentifierAssignment(statements[0]);
		if (assignment?.target === target) return assignment.value;

		const statement = statements[0];
		if (!t.isIfStatement(statement) || !statement.alternate) return null;
		const consequent = conditionalPhiArmExpression(
			branchStatements(statement.consequent),
			target,
		);
		const alternate = conditionalPhiArmExpression(
			branchStatements(statement.alternate),
			target,
		);
		return consequent && alternate
			? buildConditionalValueExpression(
				statement.test,
				consequent,
				alternate,
			)
			: null;
	}

	if (statements.length !== 2) return null;
	const declaration = statements[0];
	const assignment = simpleIdentifierAssignment(statements[1]);
	if (
		!assignment || assignment.target !== target ||
		!t.isIdentifier(assignment.value) ||
		!t.isVariableDeclaration(declaration) ||
		declaration.declarations.length !== 1
	) return null;
	const [declarator] = declaration.declarations;
	if (
		!t.isIdentifier(declarator.id, { name: assignment.value.name }) ||
		!declarator.init || !t.isExpression(declarator.init)
	) return null;
	return declarator.init;
}

function conditionalPhiArmAssignments(
	statements: readonly t.Statement[],
	targets: readonly string[],
): Map<string, t.Expression> | null {
	if (statements.length !== targets.length) return null;
	const targetSet = new Set(targets);
	const values = new Map<string, t.Expression>();
	for (const statement of statements) {
		const assignment = simpleIdentifierAssignment(statement);
		if (
			!assignment || !targetSet.has(assignment.target) ||
			values.has(assignment.target)
		) return null;
		values.set(assignment.target, assignment.value);
	}
	return values.size === targets.length ? values : null;
}

function branchStatements(statement: t.Statement): t.Statement[] {
	return t.isBlockStatement(statement) ? statement.body : [statement];
}

function emitFinallyRegion(
	region: Region,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	const statements = emitRegion(
		region,
		cfg,
		descriptors,
		phiState,
		diagnostics,
	);
	const catchNames = new Set<string>();
	for (const statement of statements) {
		t.traverseFast(statement, (node) => {
			if (!t.isVariableDeclaration(node)) return;
			for (const decl of node.declarations) {
				if (
					t.isIdentifier(decl.id) &&
					t.isCallExpression(decl.init) &&
					t.isV8IntrinsicIdentifier(decl.init.callee, {
						name: 'Catch',
					})
				) catchNames.add(decl.id.name);
			}
		});
	}
	for (const statement of statements) {
		t.traverseFast(statement, (node) => {
			if (isCatchIntrinsicDeclaration(node as t.Statement)) {
				Object.assign(node, t.emptyStatement());
				return t.traverseFast.skip;
			}
			if (
				t.isThrowStatement(node) && t.isIdentifier(node.argument) &&
				catchNames.has(node.argument.name)
			) {
				Object.assign(node, t.emptyStatement());
				return t.traverseFast.skip;
			}
		});
	}
	const filtered = statements.filter((stmt) =>
		!t.isEmptyStatement(stmt) && !t.isThrowStatement(stmt)
	);
	for (let index = 0; index < filtered.length; index++) {
		const guard = filtered[index];
		if (
			!t.isIfStatement(guard) || guard.alternate != null ||
			!t.isBlockStatement(guard.consequent) ||
			!guard.consequent.body.every((stmt) => t.isEmptyStatement(stmt))
		) continue;
		const loopIndex = filtered.findIndex((candidate, candidateIndex) =>
			candidateIndex > index && t.isWhileStatement(candidate) &&
			t.isBooleanLiteral(candidate.test, { value: true })
		);
		if (loopIndex < 0) continue;
		const [loop] = filtered.splice(loopIndex, 1) as [t.WhileStatement];
		filtered[index] = t.ifStatement(
			invertTest(t.cloneNode(guard.test, true)),
			t.blockStatement([loop]),
		);
		break;
	}
	return filtered;
}

function emitFallbackFinalizerCandidate(
	region: Extract<Region, { kind: 'tryFinally' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
): t.Statement[] {
	const canonical = cfg.blocks.get(region.handlerAddress);
	if (
		canonical &&
		(canonical.terminator.kind === 'throw' ||
			canonical.terminator.kind === 'return')
	) {
		const statements = finalizerCandidateStatements(
			canonical.body,
			canonical.address,
			phiState,
		);
		if (statements.length > 0) return statements;
	}

	const descriptor = descriptors.exceptions.handlerByAddress.get(
		region.handlerAddress,
	);
	for (const addr of region.normalExitCandidates ?? []) {
		const block = cfg.blocks.get(addr);
		if (!block) continue;
		const ranges = descriptor?.kind === 'finally'
			? descriptor.finallyCopies
				.filter((copy) =>
					copy.kind === 'normalExit' &&
					(copy.next ?? copy.copyRoot) === addr
				)
				.flatMap((copy) => copy.skipRanges ?? [])
				.filter((range) => range.block === addr)
			: [];
		if (ranges.length > 0) {
			const statements = ranges.flatMap((range) =>
				finalizerCandidateStatements(
					block.body.slice(range.start, range.end),
					addr,
					phiState,
				)
			);
			if (statements.length > 0) return statements;
			continue;
		}
		const statements = finalizerCandidateStatements(
			block.body,
			addr,
			phiState,
		);
		if (statements.length === 0) continue;
		return statements;
	}
	return [];
}

function finalizerCandidateStatements(
	body: readonly t.Statement[],
	addr: number,
	phiState: PhiEmitState,
): t.Statement[] {
	return body.filter((stmt) =>
		!isCatchIntrinsicDeclaration(stmt) &&
		!t.isThrowStatement(stmt) &&
		!isCoveredPhiStatement(stmt, addr, phiState)
	).map((stmt) => t.cloneNode(stmt, true));
}

function isCatchIntrinsicDeclaration(stmt: t.Statement): boolean {
	if (!t.isVariableDeclaration(stmt)) return false;
	return stmt.declarations.some((decl) =>
		t.isCallExpression(decl.init) &&
		t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Catch' })
	);
}

function firstSourceBlock(region: Region): number {
	return [...region.sourceBlocks].toSorted((a, b) => a - b)[0];
}

function bindCatchIntrinsic(
	statements: t.Statement[],
	parameter: t.Identifier,
): t.Statement[] {
	for (const statement of statements) {
		t.traverseFast(statement, (node) => {
			if (
				!t.isCallExpression(node) ||
				!t.isV8IntrinsicIdentifier(node.callee, { name: 'Catch' })
			) return;
			Object.assign(node, t.cloneNode(parameter));
			return t.traverseFast.skip;
		});
	}
	return statements;
}

function soleTryCatchRegion(
	region: Region,
): Extract<Region, { kind: 'tryCatch' }> | null {
	if (region.kind === 'tryCatch') return region;
	if (region.kind !== 'sequence' || region.regions.length !== 1) return null;
	const [child] = region.regions;
	return child.kind === 'tryCatch' ? child : null;
}

function firstLabelBreak(
	region: Region,
	activeLabels: ReadonlySet<string> = new Set<string>(),
): string | null {
	if (region.kind === 'labelBreak') {
		return activeLabels.has(region.label) ? null : region.label;
	}

	let childLabels = activeLabels;
	if (region.kind === 'sequence' && region.exitLabel != null) {
		const labels = new Set(activeLabels);
		labels.add(region.exitLabel);
		childLabels = labels;
	}
	const firstIn = (children: readonly Region[]): string | null => {
		for (const child of children) {
			const label = firstLabelBreak(child, childLabels);
			if (label != null) return label;
		}
		return null;
	};

	switch (region.kind) {
		case 'sequence':
			return firstIn(region.regions);
		case 'if':
			return firstIn([region.consequent, region.alternate]);
		case 'switch':
			return firstIn([
				...region.cases.map((switchCase) => switchCase.body),
				region.defaultBody,
			]);
		case 'tryCatch':
			return firstIn([region.body, region.handler]);
		case 'tryFinally':
			return firstIn([region.body, region.finalizer]);
		case 'loop':
			return firstLabelBreak(region.body, childLabels);
		default:
			return null;
	}
}

function emitBasicRegion(
	region: Extract<Region, { kind: 'basic' }>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	const statements: t.Statement[] = [];
	for (const addr of region.sourceBlocks) {
		statements.push(
			...emitBlockStatements(addr, cfg, phiState, diagnostics, true),
		);
	}
	return statements;
}

function emitBlockStatements(
	addr: number,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
	diagnostics: string[],
	includeSameValuePhis: boolean,
	allowDuplicate = false,
): t.Statement[] {
	const trace = recursiveEmitTraceBlocks();
	const traceBlock = trace.has(addr);
	if (phiState.emittedBlocks.has(addr) && !allowDuplicate) {
		if (traceBlock) {
			const message = `[recursive-emit:block 0x${
				addr.toString(16)
			}] already-emitted`;
			console.error(message);
			diagnostics.push(message);
		}
		return [];
	}
	const block = cfg.blocks.get(addr);
	if (!block) {
		diagnostics.push(`missing basic block 0x${addr.toString(16)}`);
		return [];
	}
	// `allowDuplicate` marks a non-owning copy — a terminal leaf shared by
	// several paths, each of which emits its own. Claiming the block here would
	// suppress the Region that actually owns it if the copy is emitted first,
	// dropping the statements from the path that reaches them normally.
	if (!allowDuplicate) phiState.emittedBlocks.add(addr);
	const statements: t.Statement[] = [];
	statements.push(
		...takeExceptionalStateAssignmentsForBlock(addr, phiState),
	);
	if (traceBlock) {
		const message = `[recursive-emit:block 0x${addr.toString(16)}] ` +
			`body=${block.body.length} skipped=${
				[
					...(phiState.skippedBlockStatements.get(addr) ??
						new Set<number>()),
				].toSorted((a, b) => a - b).join(',')
			}`;
		console.error(message);
		diagnostics.push(message);
		block.body.forEach((stmt, index) => {
			const stmtMessage =
				`[recursive-emit:block 0x${addr.toString(16)}:${index}] ` +
				generate(stmt).code;
			console.error(stmtMessage);
			diagnostics.push(stmtMessage);
		});
	}
	if (includeSameValuePhis) {
		statements.push(...takeSameValuePhiAssignmentsForBlock(addr, phiState));
	}
	for (const stmt of block.body) {
		const index = block.body.indexOf(stmt);
		if (phiState.skippedBlockStatements.get(addr)?.has(index)) continue;
		if (isCoveredPhiStatement(stmt, addr, phiState)) continue;
		if (
			index === block.body.length - 1 &&
			(t.isReturnStatement(stmt) || t.isThrowStatement(stmt))
		) {
			statements.push(...takeFinalizerActionsForBlock(addr, phiState));
		}
		const cloned = t.cloneNode(stmt, true);
		if (
			t.isReturnStatement(cloned) &&
			t.isIdentifier(cloned.argument) &&
			!phiState.declaredPhiTargets.has(cloned.argument.name)
		) {
			const alias = uniqueCFGScalarAlias(cfg, cloned.argument.name);
			if (alias && !containsPhiIntrinsic(alias)) cloned.argument = alias;
		}
		if (
			(t.isReturnStatement(cloned) || t.isThrowStatement(cloned)) &&
			statementListIncludes(statements, cloned)
		) continue;
		statements.push(cloned);
	}
	statements.push(...takeFinalizerActionsForBlock(addr, phiState));
	if (traceBlock) {
		const message = `[recursive-emit:block 0x${
			addr.toString(16)
		}] emitted=${statements.length}`;
		console.error(message);
		diagnostics.push(message);
		statements.forEach((stmt, index) => {
			const stmtMessage =
				`[recursive-emit:block 0x${
					addr.toString(16)
				}:emitted:${index}] ` +
				generate(stmt).code;
			console.error(stmtMessage);
			diagnostics.push(stmtMessage);
		});
	}
	return statements;
}

/**
 * Rebuild a `VariableDeclaration` whose declarator list was filtered or split.
 *
 * Statement-level `extra` carries provenance later passes depend on --
 * `fromDestructuring` is what proves a pattern declaration came from a
 * recovered destructuring protocol rather than from an ordinary lifted
 * assignment, and parameter recovery declines any pattern without it. A plain
 * `t.variableDeclaration(...)` drops that, so every rebuild goes through here.
 */
function rebuiltVariableDeclaration(
	source: t.VariableDeclaration,
	declarations: t.VariableDeclarator[],
): t.VariableDeclaration {
	const rebuilt = t.variableDeclaration(source.kind, declarations);
	if (source.extra) rebuilt.extra = { ...source.extra };
	return rebuilt;
}

function uniqueCFGScalarAlias(
	cfg: ImmutableCFG,
	name: string,
): t.Expression | null {
	const values: t.Expression[] = [];
	for (const block of cfg.blocks.values()) {
		for (const statement of block.body) {
			if (!t.isVariableDeclaration(statement)) continue;
			for (const declaration of statement.declarations) {
				if (!t.isIdentifier(declaration.id, { name })) continue;
				if (!t.isExpression(declaration.init)) return null;
				if (
					!t.isIdentifier(declaration.init) &&
					!t.isLiteral(declaration.init)
				) return null;
				values.push(declaration.init);
			}
		}
	}
	if (values.length !== 1) return null;
	return t.cloneNode(values[0], true);
}

function recursiveEmitTraceBlocks(): Set<number> {
	let value: string | undefined;
	try {
		value = Deno.env.get('ARES_DEBUG_RECURSIVE_EMIT_BLOCKS');
	} catch {
		return new Set();
	}
	if (!value) return new Set();
	return new Set(
		value.split(',')
			.map((part) => part.trim())
			.filter((part) => part.length > 0)
			.map((part) =>
				part.startsWith('0x')
					? Number.parseInt(part.slice(2), 16)
					: Number.parseInt(part, 10)
			)
			.filter((addr) => Number.isFinite(addr)),
	);
}

interface PhiEmitState {
	actionsByEdge: Map<string, PhiEdgeAction>;
	exceptionalStateAssignmentsByBlock: Map<number, t.Statement[]>;
	finalizerActionsByBlock: Map<number, t.Statement[]>;
	sameValueAssignmentsByBlock: Map<number, t.Statement[]>;
	coveredPhiBlocks: Set<number>;
	loopSyntaxes: Array<
		NonNullable<Extract<Region, { kind: 'loop' }>['syntax']>
	>;
	skippedBlockStatements: Map<number, Set<number>>;
	emittedBlocks: Set<number>;
	/**
	 * Blocks the Region tree claims.
	 *
	 * A destination outside it is emitted by nobody, which is what separates a
	 * loop exit that needs its own completion from one a `break` reaches.
	 */
	regionBlocks: AddressSet<BlockAddr>;
	declaredPhiTargets: Set<string>;
	patternBoundNames: Set<string>;
	conditionalPhiOwners: Map<string, Extract<Region, { kind: 'if' }>>;
	ambiguousConditionalPhiTargets: Set<string>;
	enclosingLoopExitActions: Array<readonly LoopRegionExit[]>;
	nextTemp: number;
}

function inheritStructuredLoopExitActions(
	region: Extract<Region, { kind: 'loop' }>,
	phiState: PhiEmitState,
): Extract<Region, { kind: 'loop' }> {
	if (phiState.enclosingLoopExitActions.length === 0) return region;
	let changed = false;
	const exits = region.exits.map((embedded) => {
		for (
			const enclosing of phiState.enclosingLoopExitActions.toReversed()
		) {
			const structured = enclosing.find((exit) =>
				exit.from === embedded.from && exit.to === embedded.to &&
				(
					exit.trailer != null ||
					exit.normalCompletionFlag != null ||
					exit.sequenceExit != null
				)
			);
			if (!structured) continue;
			changed = true;
			return {
				...structured,
				kind: embedded.kind,
				label: embedded.label,
				targetLoop: embedded.targetLoop,
			};
		}
		return embedded;
	});
	return changed ? { ...region, exits } : region;
}

function withEnclosingLoopExitActions<T>(
	phiState: PhiEmitState,
	exits: readonly LoopRegionExit[],
	emit: () => T,
): T {
	phiState.enclosingLoopExitActions.push(exits);
	try {
		return emit();
	} finally {
		phiState.enclosingLoopExitActions.pop();
	}
}

interface PhiEdgeAction {
	edge: CFGEdge;
	assignments: Array<{ target: t.Identifier; value: t.Expression }>;
}

function buildPhiEmitState(
	region: Region,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
): PhiEmitState {
	const {
		owners: conditionalPhiOwners,
		ambiguousTargets: ambiguousConditionalPhiTargets,
	} = collectConditionalPhiOwnership(region, descriptors);
	const actionsByEdge = new Map<string, PhiEdgeAction>();
	const exceptionalStateAssignmentsByBlock = new Map<
		number,
		t.Statement[]
	>();
	const finalizerActionsByBlock = collectFinalizerActions(
		region,
		cfg,
		descriptors,
	);
	const sameValueAssignmentsByBlock = new Map<number, t.Statement[]>();
	const coveredPhiBlocks = new Set<number>();
	const loopSyntaxes = collectLoopSyntaxes(region);
	const skippedBlockStatements = mergeSkippedStatements(
		skippedStatementsForIteratorLoops(region),
		skippedStatementsForFinalizerCopies(cfg, descriptors, region),
		skippedStatementsForDelegateYields(region),
	);
	const declaredPhiTargets = new Set<string>();
	const patternBoundNames = collectPatternBoundNames(cfg);
	const finalizerPhiAliases = representedFinalizerPhiAliases(
		region,
		descriptors,
	);
	for (const phi of descriptors.phis.phis) {
		const target = finalizerPhiAliases.get(phi.target.name) ?? phi.target;
		declaredPhiTargets.add(target.name);
		// A landing-pad Phi is the register state at the instruction that threw,
		// not a copy that can be selected after control has reached `catch`.
		// Protected blocks are split whenever that state changes. Materialize the
		// state on normal entry to each such block, before its first possible
		// throw, and let the handler read the mutable Phi target.
		for (const assignment of phi.exceptionalIncoming.values()) {
			if (
				t.isIdentifier(assignment.value, {
					name: target.name,
				})
			) continue;
			const assignments = exceptionalStateAssignmentsByBlock.get(
				assignment.edge.from,
			) ?? [];
			assignments.push(assignmentStatement(
				target,
				assignment.value,
			));
			exceptionalStateAssignmentsByBlock.set(
				assignment.edge.from,
				assignments,
			);
		}
		const incoming = [...phi.incoming.values()];
		const nonSelf = incoming.filter((assignment) =>
			!(
				t.isIdentifier(assignment.value) &&
				target.name === assignment.value.name
			)
		);
		if (nonSelf.length === 0) {
			coveredPhiBlocks.add(phi.block);
			continue;
		}
		const firstValue = expressionKey(nonSelf[0].value);
		// Collapsing every edge onto one assignment in the Phi's own block is
		// only equivalent while that assignment is what each edge would have
		// carried. A self-referential source is dropped above rather than
		// assigned, so the block is also reachable carrying whatever the
		// in-place update left in the register -- and a header re-executed per
		// iteration would overwrite it. Keep those edge-local.
		const allSameValue = nonSelf.length === incoming.length &&
			nonSelf.every((assignment) =>
				expressionKey(assignment.value) === firstValue
			);
		if (allSameValue) {
			const assignments = sameValueAssignmentsByBlock.get(phi.block) ??
				[];
			for (const assignment of nonSelf.slice(0, 1)) {
				assignments.push(assignmentStatement(
					target,
					assignment.value,
				));
			}
			sameValueAssignmentsByBlock.set(phi.block, assignments);
		} else {
			for (const assignment of nonSelf) {
				const key = edgeKey(assignment.edge);
				const action = actionsByEdge.get(key) ?? {
					edge: assignment.edge,
					assignments: [],
				};
				action.assignments.push({
					target: t.cloneNode(target),
					value: assignment.value,
				});
				actionsByEdge.set(key, action);
			}
		}
		coveredPhiBlocks.add(phi.block);
	}
	const state: PhiEmitState = {
		actionsByEdge,
		exceptionalStateAssignmentsByBlock,
		finalizerActionsByBlock,
		sameValueAssignmentsByBlock,
		coveredPhiBlocks,
		loopSyntaxes,
		skippedBlockStatements,
		enclosingLoopExitActions: [],
		emittedBlocks: new Set(),
		regionBlocks: regionCoveredBlocks(region),
		declaredPhiTargets,
		patternBoundNames,
		ambiguousConditionalPhiTargets,
		conditionalPhiOwners,
		nextTemp: 0,
	};
	for (const syntax of loopSyntaxes) {
		discardIteratorInternalPhiActions(syntax, state);
	}
	return state;
}

/**
 * A represented finalizer commonly emits a normal/catch copy of its body while
 * the exceptional table points at a separate canonical handler. Their Phis are
 * different SSA versions of the same runtime register. JavaScript has only one
 * `finally`, so route the canonical handler's per-protected-block state updates
 * into the Phi target read by the represented copy.
 *
 * Keep the proof mechanical: both blocks must be Phis owned by this exact
 * try/finally Region, have the same original register index, and have one unique
 * emitted-copy candidate. General value/register coalescing remains a separate
 * binding pass.
 */
function representedFinalizerPhiAliases(
	region: Region,
	descriptors: CFGDescriptors,
): Map<string, t.Identifier> {
	const aliases = new Map<string, t.Identifier>();
	visitRegions(region, (candidate) => {
		if (candidate.kind !== 'tryFinally') return;
		const canonicalPhis = descriptors.phis.phisByBlock.get(
			candidate.handlerAddress,
		) ?? [];
		if (canonicalPhis.length === 0) return;
		const emittedPhis = [...candidate.finalizer.sourceBlocks].flatMap(
			(block) => descriptors.phis.phisByBlock.get(block) ?? [],
		);
		for (const canonical of canonicalPhis) {
			const family = generatedRegisterFamily(canonical.target.name);
			if (family == null) continue;
			const matches = emittedPhis.filter((copy) =>
				generatedRegisterFamily(copy.target.name) === family
			);
			if (matches.length !== 1) continue;
			aliases.set(
				canonical.target.name,
				t.cloneNode(matches[0]!.target),
			);
		}
	});
	return aliases;
}

function generatedRegisterFamily(name: string): number | null {
	const match = /^r(\d+)_\d+$/.exec(name);
	return match ? Number(match[1]) : null;
}

function collectPatternBoundNames(cfg: ImmutableCFG): Set<string> {
	const names = new Set<string>();
	for (const block of cfg.blocks.values()) {
		for (const statement of block.body) {
			t.traverseFast(statement, (node) => {
				if (
					!t.isVariableDeclarator(node) ||
					t.isIdentifier(node.id)
				) return;
				for (
					const name of Object.keys(t.getBindingIdentifiers(node.id))
				) {
					names.add(name);
				}
			});
		}
	}
	return names;
}

function phiTargetDeclarations(phiState: PhiEmitState): t.Statement[] {
	if (phiState.declaredPhiTargets.size === 0) return [];
	return [
		t.variableDeclaration(
			'let',
			[...phiState.declaredPhiTargets].toSorted().map((name) =>
				t.variableDeclarator(t.identifier(name))
			),
		),
	];
}

function emitIteratorLoop(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	const syntax = region.syntax;
	if (!syntax) return [];
	const completionSequenceExit = iteratorCompletionSequenceExit(region, cfg);
	const sharedExitPhiBreaks = completionSequenceExit == null &&
		iteratorSharedExitPhiBreaks(region, cfg, phiState);
	const normalCompletionFlag = iteratorNormalCompletionFlag(region, cfg) ??
		(sharedExitPhiBreaks
			? `_cfg_loop_${region.header.toString(16)}_completed`
			: undefined);
	if (normalCompletionFlag) {
		markIteratorBodyBreaks(
			region.body,
			region,
			cfg,
			normalCompletionFlag,
			sharedExitPhiBreaks,
		);
	}
	discardIteratorInternalPhiActions(syntax, phiState);
	const bodyRegion = rewriteDeferredExitsForLoop(
		region.body,
		region,
		cfg,
		descriptors,
		phiState.regionBlocks,
	);
	// Exit rewriting can materialize a break after a nonempty protected arm.
	// Mark that synthesized node as well as any break the Region already held.
	if (normalCompletionFlag) {
		markIteratorBodyBreaks(
			bodyRegion,
			region,
			cfg,
			normalCompletionFlag,
			sharedExitPhiBreaks,
		);
	}
	const bodyStatements = stripIteratorCloseOnlyFinallyStatements(emitRegion(
		bodyRegion,
		cfg,
		descriptors,
		phiState,
		diagnostics,
	));
	const referencedNames = referencedIdentifierNames(bodyStatements);
	const headerExitValues = iteratorHeaderExitValues(
		region,
		cfg,
		phiState,
		referencedNames,
	);
	for (const name of headerExitValues.referencedNames) {
		referencedNames.add(name);
	}
	const normalizedBodyStatements = [
		...headerExitValues.statements.map((statement) =>
			t.cloneNode(statement, true)
		),
		...bodyStatements,
	];
	const latchControl = emitLoopLatchControlFlow(
		region,
		cfg,
		descriptors,
		phiState,
		diagnostics,
	);
	normalizedBodyStatements.push(...latchControl);
	const backedgeActions = takePhiActionsForLoopBackedges(
		region,
		phiState,
		referencedNames,
	);
	normalizedBodyStatements.push(...backedgeActions);
	// The recovered `for` body is the only block scope in this emission: its
	// exit trailer and continuation are emitted after the loop, so a value the
	// body declares and one of them reads has to outlive the braces.
	const scopedBody = emitBlockScopedRegion(
		region.body,
		cfg,
		descriptors,
		phiState,
		diagnostics,
		{
			statements: normalizedBodyStatements,
			alsoInside: new AddressSet<BlockAddr>([region.header]),
		},
	);
	const left = t.variableDeclaration('const', [
		t.variableDeclarator(t.cloneNode(syntax.value)),
	]);
	const loop = syntax.kind === 'forOf'
		? t.forOfStatement(
			left,
			iteratorSourceExpression(syntax, cfg),
			t.blockStatement(scopedBody.statements),
		)
		: t.forInStatement(
			left,
			iteratorSourceExpression(syntax, cfg),
			t.blockStatement(scopedBody.statements),
		);
	loop.extra = { ...loop.extra, fromRecursiveCFG: true };
	const loopStatement = labelLoopWhenReferenced(loop, region.label);
	const headerExitActions = sharedExitPhiBreaks
		? takeIteratorHeaderExitPhiActions(region, phiState)
		: [];
	const exitContinuation = completionSequenceExit
		? [
			...emitLoopExitActions(
				completionSequenceExit,
				cfg,
				descriptors,
				phiState,
				diagnostics,
			),
			loopExitStatement(completionSequenceExit, region),
		]
		: emitIteratorLoopExitContinuation(
			region,
			cfg,
			phiState,
			diagnostics,
		);
	return [
		...takePhiActionsForElidedIteratorGuard(region, cfg, phiState),
		...takePhiActionsForLoopEntry(region, cfg, phiState, referencedNames),
		...(normalCompletionFlag
			? [t.variableDeclaration('let', [t.variableDeclarator(
				t.identifier(normalCompletionFlag),
				t.booleanLiteral(true),
			)])]
			: []),
		...generatedLetDeclaration(scopedBody.hoisted),
		loopStatement,
		...headerExitValues.statements,
		...(sharedExitPhiBreaks
			? [
				...(normalCompletionFlag && headerExitActions.length > 0
					? [t.ifStatement(
						t.identifier(normalCompletionFlag),
						t.blockStatement(headerExitActions),
					)]
					: headerExitActions),
				...exitContinuation,
			]
			: normalCompletionFlag && exitContinuation.length > 0
			? [t.ifStatement(
				t.identifier(normalCompletionFlag),
				t.blockStatement(exitContinuation),
			)]
			: exitContinuation),
	];
}

/**
 * `for...in` performs the zero-trip test itself, so the guard branch Hermes
 * emits around the loop is dropped. The guard's edge to the loop continuation
 * still carries the Phi copies describing the zero-iteration value: place them
 * before the loop, where the loop's own exit copies overwrite them as soon as
 * it iterates at all.
 */
function takePhiActionsForElidedIteratorGuard(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
): t.Statement[] {
	const syntax = region.syntax;
	const continuation = region.continuation;
	if (!syntax || continuation == null) return [];
	const guardNames = iteratorGuardTests(syntax, cfg);
	if (guardNames.length === 0) return [];
	const statements: t.Statement[] = [];
	for (const predecessor of cfg.normalPredecessors.get(region.header) ?? []) {
		if (region.loopBlocks.has(predecessor)) continue;
		const terminator = cfg.blocks.get(predecessor)?.terminator;
		if (terminator?.kind !== 'if') continue;
		const bypass = terminator.taken === region.header
			? terminator.fallthrough
			: terminator.taken;
		if (
			bypass !== continuation ||
			!guardNames.some((name) =>
				isIteratorUndefinedTest(terminator.test, name)
			)
		) continue;
		statements.push(...takePhiActionsForEdge(
			{ from: predecessor, to: continuation, kind: 'normal' },
			phiState,
		));
	}
	return statements;
}

function isIteratorHeaderCompletionExit(
	exit: LoopRegionExit,
	header: BlockAddr,
): boolean {
	return exit.from === header &&
		(
			exit.kind === 'break' ||
			exit.kind === 'return' ||
			exit.kind === 'throw'
		);
}

function markIteratorBodyBreaks(
	body: Region,
	loop: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	flag: string,
	includeSharedTargets = false,
) {
	const subsumedHandlerBlocks = new AddressSet<number>();
	const collectSubsumed = (region: Region) => {
		if (region.kind === 'tryCatch') {
			for (const block of region.subsumedHandlerBlocks ?? []) {
				subsumedHandlerBlocks.add(block);
			}
		}
		switch (region.kind) {
			case 'sequence':
				region.regions.forEach(collectSubsumed);
				break;
			case 'if':
				collectSubsumed(region.consequent);
				collectSubsumed(region.alternate);
				break;
			case 'switch':
				region.cases.forEach((switchCase) =>
					collectSubsumed(switchCase.body)
				);
				collectSubsumed(region.defaultBody);
				break;
			case 'tryCatch':
				collectSubsumed(region.body);
				collectSubsumed(region.handler);
				break;
			case 'tryFinally':
				collectSubsumed(region.body);
				collectSubsumed(region.finalizer);
				break;
			case 'loop':
				break;
		}
	};
	collectSubsumed(body);
	const headerTargets = new Set(
		loop.exits
			.filter((exit) => isIteratorHeaderCompletionExit(exit, loop.header))
			.map((exit) => normalizeIteratorLoopExit(exit.to, loop, cfg)),
	);
	const exits = loop.exits.filter((exit) =>
		exit.from !== loop.header && exit.kind === 'break' &&
		!subsumedHandlerBlocks.has(exit.from) &&
		(includeSharedTargets ||
			!headerTargets.has(normalizeIteratorLoopExit(exit.to, loop, cfg)))
	);
	const visit = (region: Region) => {
		if (
			(region.kind === 'break' || region.kind === 'labelBreak') &&
			region.exit &&
			exits.some((exit) =>
				exit.from === region.exit!.from && exit.to === region.exit!.to
			)
		) region.exit.normalCompletionFlag = flag;
		switch (region.kind) {
			case 'sequence':
				region.regions.forEach(visit);
				break;
			case 'if':
				visit(region.consequent);
				visit(region.alternate);
				break;
			case 'switch':
				region.cases.forEach((switchCase) => visit(switchCase.body));
				visit(region.defaultBody);
				break;
			case 'tryCatch':
				visit(region.body);
				visit(region.handler);
				break;
			case 'tryFinally':
				visit(region.body);
				visit(region.finalizer);
				break;
			// A nested loop owns and emits its own exit metadata.
			case 'loop':
				break;
		}
	};
	visit(body);
}

/**
 * A body `break` and iterator exhaustion may reach the same continuation while
 * carrying different values into one of its Phis. JavaScript gives both paths
 * the same lexical fallthrough, so guard only the header-edge Phi copies; the
 * continuation itself must still run after either path.
 */
function iteratorSharedExitPhiBreaks(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
): boolean {
	const headerExits = region.exits.filter((exit) =>
		exit.from === region.header && exit.kind === 'break'
	);
	for (const headerExit of headerExits) {
		const headerAction = phiState.actionsByEdge.get(edgeKey({
			from: headerExit.from,
			to: headerExit.to,
			kind: 'normal',
		}));
		if (!headerAction) continue;
		const headerTargets = new Set(
			headerAction.assignments.map((assignment) =>
				assignment.target.name
			),
		);
		const normalizedTarget = normalizeIteratorLoopExit(
			headerExit.to,
			region,
			cfg,
		);
		for (const bodyExit of region.exits) {
			if (
				bodyExit.from === region.header || bodyExit.kind !== 'break' ||
				normalizeIteratorLoopExit(bodyExit.to, region, cfg) !==
					normalizedTarget
			) continue;
			const bodyActions = iteratorExitPhiActions(
				bodyExit,
				region,
				cfg,
				phiState,
			);
			if (
				bodyActions.some((action) =>
					action.assignments.some((assignment) =>
						headerTargets.has(assignment.target.name)
					)
				)
			) return true;
		}
	}
	return false;
}

/**
 * Phi actions carried by an iterator exit, including an elided close trailer.
 *
 * A recovered `for...of` subsumes `%IteratorClose`, but a join Phi can be
 * attached to the close block's outgoing edge rather than the body's edge into
 * that block. Follow only the same close-only chain that exit normalization
 * accepts; arbitrary exit trailers still belong to ordinary Region emission.
 */
function iteratorExitPhiActions(
	exit: LoopRegionExit,
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
): PhiEdgeAction[] {
	const actions: PhiEdgeAction[] = [];
	let from = exit.from;
	let to = exit.to;
	const seen = new Set<BlockAddr>();
	for (;;) {
		const action = phiState.actionsByEdge.get(edgeKey({
			from,
			to,
			kind: 'normal',
		}));
		if (action) actions.push(action);
		if (seen.has(to) || region.loopBlocks.has(to)) break;
		seen.add(to);
		const block = cfg.blocks.get(to);
		if (!block || !blockContainsIntrinsic(block.body, 'IteratorClose')) {
			break;
		}
		const successors = [...(cfg.normalSuccessors.get(to) ?? [])];
		if (successors.length !== 1) break;
		from = to;
		[to] = successors;
	}
	return actions;
}

function takeIteratorHeaderExitPhiActions(
	region: Extract<Region, { kind: 'loop' }>,
	phiState: PhiEmitState,
): t.Statement[] {
	return region.exits
		.filter((exit) =>
			exit.from === region.header && exit.kind === 'break' &&
			!region.loopBlocks.has(exit.to)
		)
		.flatMap((exit) =>
			takePhiActionsForEdge({
				from: exit.from,
				to: exit.to,
				kind: 'normal',
			}, phiState)
		);
}

function iteratorNormalCompletionFlag(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
): string | undefined {
	const headerTargets = new Set(
		region.exits
			.filter((exit) =>
				isIteratorHeaderCompletionExit(exit, region.header)
			)
			.map((exit) => normalizeIteratorLoopExit(exit.to, region, cfg)),
	);
	if (headerTargets.size === 0) return;
	const bodyBreaks = region.exits.filter((exit) =>
		exit.from !== region.header && exit.kind === 'break'
	);
	if (
		bodyBreaks.length === 0 ||
		bodyBreaks.every((exit) =>
			headerTargets.has(normalizeIteratorLoopExit(exit.to, region, cfg))
		)
	) return;
	return `_cfg_loop_${region.header.toString(16)}_completed`;
}

/**
 * The exhausted-iterator exit a recovered loop spells as a labelled break.
 *
 * A `for...of` falls out of its own statement when the iterator is exhausted,
 * so only the normal completion flag tells that path apart from a body
 * `break`. When the header exit also leaves an enclosing labelled sequence,
 * the body break's destination is what lexically follows the loop: the
 * exhausted path has to jump past it instead of having its own destination
 * spliced in between.
 */
function iteratorCompletionSequenceExit(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
): LoopRegionExit | undefined {
	if (
		region.syntax == null ||
		iteratorNormalCompletionFlag(region, cfg) == null
	) return undefined;
	return region.exits.find((exit) =>
		exit.from === region.header && exit.kind === 'break' &&
		exit.sequenceExit?.label != null
	);
}

function discardIteratorInternalPhiActions(
	syntax: NonNullable<Extract<Region, { kind: 'loop' }>['syntax']>,
	phiState: PhiEmitState,
) {
	const internal = new Set(
		(syntax.internalValues ?? []).map((identifier) => identifier.name),
	);
	const machine = new Set([
		...internal,
		...(syntax.machineValues ?? []).map((identifier) => identifier.name),
	]);
	if (internal.size === 0 && machine.size === 0) return;
	closeOverInternalPhiTargets(internal, phiState, machine);
	for (const [key, action] of phiState.actionsByEdge) {
		action.assignments = action.assignments.filter((assignment) => {
			// Nothing declares an internal register any more, so an action that
			// reads one is as unlowerable as one that writes it.
			if (
				t.isIdentifier(assignment.value) &&
				internal.has(assignment.value.name)
			) return false;
			if (!internal.has(assignment.target.name)) return true;
			phiState.declaredPhiTargets.delete(assignment.target.name);
			return false;
		});
		if (action.assignments.length === 0) {
			phiState.actionsByEdge.delete(key);
		}
	}
	for (const [block, statements] of phiState.sameValueAssignmentsByBlock) {
		const retained = statements.filter((statement) => {
			const assignment = phiAssignmentStatement(statement);
			if (!assignment) return true;
			if (
				t.isIdentifier(assignment.value) &&
				internal.has(assignment.value.name)
			) return false;
			if (!internal.has(assignment.target.name)) return true;
			phiState.declaredPhiTargets.delete(assignment.target.name);
			return false;
		});
		if (retained.length > 0) {
			phiState.sameValueAssignmentsByBlock.set(block, retained);
		} else {
			phiState.sameValueAssignmentsByBlock.delete(block);
		}
	}
}

/**
 * A Phi whose every incoming value is an iterator-machine register carries the
 * machine's own state: the header Phi merging the iterator the preheader began
 * with the one `%IteratorNext` returns, for instance. Its target is subsumed by
 * the recovered syntax exactly like its sources are.
 *
 * The closure walks the Phi graph rather than the register's numeric family.
 * Registers are reused freely across a function, so `r4_10` may well carry a
 * value with nothing to do with the machine that happens to live in `r4_11`;
 * discarding it by family leaves that value unbound at its uses.
 */
function closeOverInternalPhiTargets(
	internal: Set<string>,
	phiState: PhiEmitState,
	machine: Set<string> = internal,
) {
	const incoming = new Map<string, t.Expression[]>();
	for (const action of phiState.actionsByEdge.values()) {
		for (const assignment of action.assignments) {
			const values = incoming.get(assignment.target.name) ?? [];
			values.push(assignment.value);
			incoming.set(assignment.target.name, values);
		}
	}
	for (const statements of phiState.sameValueAssignmentsByBlock.values()) {
		for (const statement of statements) {
			const assignment = phiAssignmentStatement(statement);
			if (!assignment) continue;
			const values = incoming.get(assignment.target.name) ?? [];
			values.push(assignment.value);
			incoming.set(assignment.target.name, values);
		}
	}
	for (let changed = true; changed;) {
		changed = false;
		for (const [target, values] of incoming) {
			if (internal.has(target)) continue;
			if (
				!values.every((value) =>
					t.isIdentifier(value) && machine.has(value.name)
				)
			) continue;
			internal.add(target);
			changed = true;
		}
	}
}

function iteratorSourceExpression(
	syntax: NonNullable<Extract<Region, { kind: 'loop' }>['syntax']>,
	cfg: ImmutableCFG,
): t.Expression {
	let source = t.cloneNode(syntax.source, true);
	if (!syntax.preheader || !t.isIdentifier(source)) return source;
	const statements = cfg.blocks.get(syntax.preheader.block)?.body ?? [];
	const seen = new Set<string>();
	while (t.isIdentifier(source) && !seen.has(source.name)) {
		seen.add(source.name);
		let replacement: t.Expression | null = null;
		for (let index = 0; index < syntax.preheader.statement; index++) {
			const statement = statements[index];
			if (!t.isVariableDeclaration(statement)) continue;
			for (const declaration of statement.declarations) {
				if (
					t.isIdentifier(declaration.id, { name: source.name }) &&
					t.isExpression(declaration.init)
				) {
					replacement = t.cloneNode(declaration.init, true);
				}
			}
		}
		if (!replacement || !t.isIdentifier(replacement)) break;
		source = replacement;
	}
	return source;
}

function iteratorHeaderExitValues(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
	bodyReferencedNames: ReadonlySet<string>,
): { referencedNames: Set<string>; statements: t.Statement[] } {
	const headerBody = cfg.blocks.get(region.header)?.body ?? [];
	const headerDeclarations = new Set<string>();
	for (const statement of headerBody) {
		if (!t.isVariableDeclaration(statement)) continue;
		for (const declaration of statement.declarations) {
			if (t.isIdentifier(declaration.id)) {
				headerDeclarations.add(declaration.id.name);
			}
		}
	}
	const referenced = new Set(
		[...bodyReferencedNames].filter((name) => headerDeclarations.has(name)),
	);
	for (const exit of region.exits) {
		if (exit.from !== region.header || region.loopBlocks.has(exit.to)) {
			continue;
		}
		const action = phiState.actionsByEdge.get(edgeKey({
			from: exit.from,
			to: exit.to,
			kind: 'normal',
		}));
		for (const assignment of action?.assignments ?? []) {
			if (t.isIdentifier(assignment.value)) {
				referenced.add(assignment.value.name);
			}
		}
	}
	if (referenced.size === 0) {
		return { referencedNames: referenced, statements: [] };
	}

	let changed = true;
	while (changed) {
		changed = false;
		for (const statement of headerBody) {
			if (!t.isVariableDeclaration(statement)) continue;
			for (const declaration of statement.declarations) {
				if (
					!t.isIdentifier(declaration.id) ||
					!referenced.has(declaration.id.name) ||
					declaration.init == null ||
					(t.isCallExpression(declaration.init) &&
						t.isV8IntrinsicIdentifier(declaration.init.callee, {
							name: 'Phi',
						}))
				) continue;
				t.traverseFast(declaration.init, (node) => {
					if (!t.isIdentifier(node) || referenced.has(node.name)) {
						return;
					}
					referenced.add(node.name);
					changed = true;
				});
			}
		}
	}
	const statements = headerBody.flatMap((statement) => {
		if (!t.isVariableDeclaration(statement)) return [];
		const declarations = statement.declarations.filter((declaration) =>
			t.isIdentifier(declaration.id) &&
			referenced.has(declaration.id.name) &&
			!(t.isCallExpression(declaration.init) &&
				t.isV8IntrinsicIdentifier(declaration.init.callee, {
					name: 'Phi',
				}))
		).map((declaration) => t.cloneNode(declaration, true));
		return declarations.length === 0
			? []
			: [rebuiltVariableDeclaration(statement, declarations)];
	});
	return { referencedNames: referenced, statements };
}

function emitNumericForLoop(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] | null {
	// Numeric-for recovery currently has no syntax slot for path-specific exit
	// trailers. Keep the generic loop emitter when an exit owns ordered work.
	if (region.exits.some((exit) => exit.trailer != null)) return null;
	const syntax = recoverNumericForLoopSyntax(region, cfg, phiState);
	if (!syntax) return null;
	const entryActions = takePhiActionsForLoopEntry(region, cfg, phiState);
	const headerStatements = emitBlockStatements(
		region.header,
		cfg,
		phiState,
		diagnostics,
		false,
	);
	const bodyRegion = rewriteDeferredExitsForLoop(
		region.body,
		region,
		cfg,
		descriptors,
		phiState.regionBlocks,
	);
	const bodyStatements = emitRegion(
		bodyRegion,
		cfg,
		descriptors,
		phiState,
		diagnostics,
	);
	const normalizedBodyStatements = [
		...headerStatements,
		...bodyStatements,
	];
	const loop = t.forStatement(
		null,
		t.cloneNode(syntax.test, true),
		t.cloneNode(syntax.update, true),
		t.blockStatement(normalizedBodyStatements),
	);
	loop.extra = { ...loop.extra, fromRecursiveCFG: true };
	return [
		...entryActions,
		labelLoopWhenReferenced(loop, region.label),
	];
}

interface NumericForLoopSyntax {
	test: t.Expression;
	update: t.Expression;
}

function recoverNumericForLoopSyntax(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
): NumericForLoopSyntax | null {
	if (!regionContainsKind(region.body, 'tryFinally')) return null;
	if (region.latches.length !== 1) return null;
	const [latch] = region.latches;
	const block = cfg.blocks.get(latch);
	if (!block || block.terminator.kind !== 'if') return null;
	if (block.body.length !== 1) return null;
	const nextDeclaration = singleExpressionDeclaration(block.body[0]);
	if (!nextDeclaration) return null;
	const fallthroughIsBackedge =
		block.terminator.fallthrough === region.header;
	const takenIsBackedge = block.terminator.taken === region.header;
	if (fallthroughIsBackedge === takenIsBackedge) return null;
	const exitTarget = fallthroughIsBackedge
		? block.terminator.taken
		: block.terminator.fallthrough;
	if (
		!region.exits.some((exit) =>
			exit.from === latch && exit.to === exitTarget
		)
	) {
		return null;
	}
	const edge = { from: latch, to: region.header, kind: 'normal' as const };
	const action = phiState.actionsByEdge.get(edgeKey(edge));
	if (!action || action.assignments.length !== 1) return null;
	const [assignment] = action.assignments;
	if (!t.isIdentifier(assignment.value, { name: nextDeclaration.name })) {
		return null;
	}
	const headerAlias = singleHeaderAlias(
		region.header,
		cfg,
		assignment.target.name,
	);
	const updateValue = headerAlias == null
		? t.cloneNode(nextDeclaration.value, true)
		: replaceIdentifier(
			nextDeclaration.value,
			headerAlias,
			t.cloneNode(assignment.target, true),
		);
	const testWithLoopVariable = replaceIdentifier(
		block.terminator.test,
		nextDeclaration.name,
		t.cloneNode(assignment.target, true),
	);
	phiState.actionsByEdge.delete(edgeKey(edge));
	const breakTest = exitTarget === block.terminator.taken
		? testWithLoopVariable
		: invertTest(testWithLoopVariable);
	return {
		test: invertTest(breakTest),
		update: t.assignmentExpression(
			'=',
			t.cloneNode(assignment.target, true),
			updateValue,
		),
	};
}

function singleHeaderAlias(
	header: number,
	cfg: ImmutableCFG,
	target: string,
): string | null {
	const block = cfg.blocks.get(header);
	if (!block) return null;
	const nonPhiStatements = block.body.filter((stmt) =>
		!isPhiDeclaration(stmt)
	);
	if (nonPhiStatements.length !== 1) return null;
	const alias = singleIdentifierDeclaration(nonPhiStatements[0]);
	if (!alias || alias.value.name !== target) return null;
	return alias.name;
}

function isPhiDeclaration(statement: t.Statement): boolean {
	if (
		!t.isVariableDeclaration(statement) ||
		statement.declarations.length !== 1
	) {
		return false;
	}
	const [declaration] = statement.declarations;
	return t.isCallExpression(declaration.init) &&
		t.isV8IntrinsicIdentifier(declaration.init.callee, { name: 'Phi' });
}

function singleExpressionDeclaration(
	statement: t.Statement,
): { name: string; value: t.Expression } | null {
	if (
		!t.isVariableDeclaration(statement) ||
		statement.declarations.length !== 1
	) {
		return null;
	}
	const [declaration] = statement.declarations;
	if (!t.isIdentifier(declaration.id) || !t.isExpression(declaration.init)) {
		return null;
	}
	return { name: declaration.id.name, value: declaration.init };
}

function replaceIdentifier(
	expr: t.Expression,
	name: string,
	replacement: t.Expression,
): t.Expression {
	if (t.isIdentifier(expr, { name })) return t.cloneNode(replacement, true);
	const cloned = t.cloneNode(expr, true);
	t.traverseFast(cloned, (node) => {
		if (!t.isIdentifier(node, { name })) return;
		Object.assign(node, t.cloneNode(replacement, true));
	});
	return cloned;
}

function emitLoopHeaderControlFlow(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	const header = cfg.blocks.get(region.header);
	if (!header || header.terminator.kind !== 'if') return [];
	const fallthroughClass = classifyLoopHeaderTarget(
		header.terminator.fallthrough,
		region,
	);
	const takenClass = classifyLoopHeaderTarget(
		header.terminator.taken,
		region,
	);
	if (fallthroughClass === takenClass) return [];
	if (fallthroughClass !== 'break' && takenClass !== 'break') return [];
	const breakTarget = fallthroughClass === 'break'
		? header.terminator.fallthrough
		: header.terminator.taken;
	const test = breakTarget === header.terminator.taken
		? t.cloneNode(header.terminator.test, true)
		: t.unaryExpression(
			'!',
			t.cloneNode(header.terminator.test, true),
			true,
		);
	const exit = region.exits.find((candidate) =>
		candidate.from === region.header && candidate.to === breakTarget
	);
	if (!exit) return [];
	const breakActions = emitLoopExitActions(
		exit,
		cfg,
		descriptors,
		phiState,
		diagnostics,
	);
	return [
		t.ifStatement(
			test,
			t.blockStatement([
				...breakActions,
				...emitLoopExitCompletion(
					exit,
					cfg,
					descriptors,
					region,
					phiState,
					diagnostics,
				),
			]),
		),
	];
}

function emitLoopHeaderLatchBranch(
	region: Extract<Region, { kind: 'loop' }>,
	bodyStatements: t.Statement[],
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
): t.Statement[] | null {
	const branch = region.headerLatchBranch;
	const header = cfg.blocks.get(region.header);
	if (!branch || !header || header.terminator.kind !== 'if') return null;
	const bodyOnTaken = header.terminator.taken === branch.bodyEntry;
	const bodyOnFallthrough =
		header.terminator.fallthrough === branch.bodyEntry;
	if (bodyOnTaken === bodyOnFallthrough) return null;
	const bodyLatchEdges = regionExitEdges(region.body, cfg).filter((edge) =>
		edge.to === branch.latch
	);
	const bodyArm = [
		...takePhiActionsForEdge({
			from: region.header,
			to: branch.bodyEntry,
			kind: 'normal',
		}, phiState),
		...bodyStatements,
		...(bodyLatchEdges.length === 1
			? takePhiActionsForEdge(bodyLatchEdges[0]!, phiState)
			: []),
	];
	const latchArm = takePhiActionsForEdge({
		from: region.header,
		to: branch.latch,
		kind: 'normal',
	}, phiState);
	return [t.ifStatement(
		t.cloneNode(header.terminator.test, true),
		t.blockStatement(bodyOnTaken ? bodyArm : latchArm),
		t.blockStatement(bodyOnTaken ? latchArm : bodyArm),
	)];
}

function emitLoopLatchControlFlow(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	const statements: t.Statement[] = [];
	for (const latch of region.latches) {
		if (regionEmbedsLoopExitFrom(region.body, latch)) continue;
		const block = cfg.blocks.get(latch);
		if (!block || block.terminator.kind !== 'if') continue;
		const fallthroughTarget = block.terminator.fallthrough;
		const takenTarget = block.terminator.taken;
		const fallthroughIsBackedge = fallthroughTarget === region.header;
		const takenIsBackedge = takenTarget === region.header;
		if (fallthroughIsBackedge === takenIsBackedge) continue;
		const exitTarget = fallthroughIsBackedge
			? takenTarget
			: fallthroughTarget;
		const exit = region.exits.find((candidate) =>
			candidate.from === latch && candidate.to === exitTarget
		);
		if (!exit) continue;
		const test = exitTarget === takenTarget
			? t.cloneNode(block.terminator.test, true)
			: t.unaryExpression(
				'!',
				t.cloneNode(block.terminator.test, true),
				true,
			);
		const actions = emitLoopExitActions(
			exit,
			cfg,
			descriptors,
			phiState,
			diagnostics,
		);

		statements.push(
			...emitBlockStatements(latch, cfg, phiState, diagnostics, true),
		);
		statements.push(t.ifStatement(
			test,
			t.blockStatement([
				...actions,
				...emitLoopExitCompletion(
					exit,
					cfg,
					descriptors,
					region,
					phiState,
					diagnostics,
				),
			]),
		));
	}
	return statements;
}

function regionEmbedsLoopExitFrom(region: Region, from: number): boolean {
	if (
		(region.kind === 'break' || region.kind === 'continue' ||
			region.kind === 'labelBreak' || region.kind === 'labelContinue' ||
			region.kind === 'terminalReference') &&
		region.exit?.from === from
	) return true;
	switch (region.kind) {
		case 'sequence':
			return region.regions.some((child) =>
				regionEmbedsLoopExitFrom(child, from)
			);
		case 'if':
			return regionEmbedsLoopExitFrom(region.consequent, from) ||
				regionEmbedsLoopExitFrom(region.alternate, from);
		case 'switch':
			return region.cases.some((switchCase) =>
				regionEmbedsLoopExitFrom(switchCase.body, from)
			) || regionEmbedsLoopExitFrom(region.defaultBody, from);
		case 'tryCatch':
			return regionEmbedsLoopExitFrom(region.body, from) ||
				regionEmbedsLoopExitFrom(region.handler, from);
		case 'tryFinally':
			return regionEmbedsLoopExitFrom(region.body, from) ||
				regionEmbedsLoopExitFrom(region.finalizer, from);
		case 'loop':
			return regionEmbedsLoopExitFrom(region.body, from);
		default:
			return false;
	}
}

function emitEmbeddedLoopExit(
	exit: LoopRegionExit | undefined,
	control: t.Statement,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	return exit
		? [
			...emitLoopExitActions(
				exit,
				cfg,
				descriptors,
				phiState,
				diagnostics,
			),
			control,
		]
		: [control];
}

function emitLoopExitActions(
	exit: LoopRegionExit,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	const statements = takePhiActionsForEdge(
		{ from: exit.from, to: exit.to, kind: 'normal' },
		phiState,
	);
	if (exit.trailer) {
		statements.push(...emitRegion(
			exit.trailer,
			cfg,
			descriptors,
			phiState,
			diagnostics,
		));
		statements.push(...takePhiActionsForRegionExits(
			exit.trailer,
			cfg,
			phiState,
		));
	}
	if (exit.normalCompletionFlag) {
		statements.push(t.expressionStatement(t.assignmentExpression(
			'=',
			t.identifier(exit.normalCompletionFlag),
			t.booleanLiteral(false),
		)));
	}
	return statements;
}

function loopExitStatement(
	exit: LoopRegionExit,
	loop?: Extract<Region, { kind: 'loop' }>,
): t.Statement {
	if (exit.sequenceExit?.target === loop?.header) {
		return t.continueStatement();
	}
	if (exit.sequenceExit?.label) {
		return t.breakStatement(t.identifier(exit.sequenceExit.label));
	}
	if (exit.kind === 'labelledBreak' && exit.label) {
		return t.breakStatement(t.identifier(exit.label));
	}
	if (exit.kind === 'labelledContinue' && exit.label) {
		return t.continueStatement(t.identifier(exit.label));
	}
	if (exit.kind === 'continue') return t.continueStatement();
	return t.breakStatement();
}

function emitLoopExitCompletion(
	exit: LoopRegionExit,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	loop: Extract<Region, { kind: 'loop' }>,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	const completion = loopExitTerminalCompletion(
		exit,
		cfg,
		descriptors,
		loop,
		phiState.regionBlocks,
	);
	if (completion) {
		return emitTerminalCompletion(
			completion,
			exit.from,
			cfg,
			phiState,
			diagnostics,
		);
	}
	return [loopExitStatement(exit, loop)];
}

/**
 * The statements a loop exit runs in place of `break`.
 *
 * The tail blocks belong to this edge alone, so they are claimed here; the
 * terminal is a leaf several paths share and each emits its own copy of.
 */
function emitTerminalCompletion(
	completion: LoopExitTerminalCompletion,
	from: BlockAddr,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	const statements: t.Statement[] = [];
	let previous = from;
	for (const block of completion.chain) {
		statements.push(...takePhiActionsForEdge({
			from: previous,
			to: block,
			kind: 'normal',
		}, phiState));
		statements.push(
			...emitBlockStatements(block, cfg, phiState, diagnostics, false),
		);
		previous = block;
	}
	statements.push(...takePhiActionsForEdge({
		from: previous,
		to: completion.terminal,
		kind: 'normal',
	}, phiState));
	statements.push(...emitBlockStatements(
		completion.terminal,
		cfg,
		phiState,
		diagnostics,
		false,
		true,
	));
	return statements;
}

interface LoopExitTerminalCompletion {
	/** Blocks this edge alone reaches, in execution order. */
	chain: BlockAddr[];
	/** The shared `return`/`throw` leaf the chain ends at. */
	terminal: BlockAddr;
}

/** A tail longer than this is a region in its own right, not a completion. */
const MAX_TERMINAL_COMPLETION_CHAIN = 8;

function loopExitTerminalCompletion(
	exit: LoopRegionExit,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	loop: Extract<Region, { kind: 'loop' }>,
	regionBlocks: AddressSet<BlockAddr>,
): LoopExitTerminalCompletion | null {
	const target = exit.kind === 'return' || exit.kind === 'throw'
		? exit.to
		: exit.sequenceExit?.label
		? null
		: exit.sequenceExit?.target ??
			(exit.trailer ? exit.continuation : exit.to);
	if (target == null) return null;
	if (
		exit.kind === 'break' && !exit.trailer &&
		exit.to === loop.continuation && regionBlocks.has(target)
	) return null;
	// The completion runs where the exit is emitted, so that is the site whose
	// handlers the blocks have to agree with.
	return terminalCompletionFrom(
		target,
		exit.from,
		cfg,
		descriptors,
		loop,
		regionBlocks,
	);
}

/**
 * Resolve `target` to the completion its edge runs, if it is one.
 *
 * A loop can express one continuation, so any other break destination has to
 * become an in-place completion or it is emitted as a `break` that transfers
 * somewhere else entirely. The destination qualifies when the blocks between
 * it and a `return`/`throw` leaf are reached by this edge alone: nothing else
 * can claim them, so emitting them here is the only copy.
 */
function terminalCompletionFrom(
	target: BlockAddr,
	from: BlockAddr,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	loop: Extract<Region, { kind: 'loop' }>,
	regionBlocks: AddressSet<BlockAddr>,
): LoopExitTerminalCompletion | null {
	const ledger = protectionLedger(from, descriptors);
	const chain: BlockAddr[] = [];
	const seen = new AddressSet<BlockAddr>();
	let cursor: BlockAddr | undefined = target;
	while (cursor != null && !seen.has(cursor)) {
		seen.add(cursor);
		const block = cfg.blocks.get(cursor);
		if (!block) return null;
		// The handler's own landing pad is emitted as a `catch` body, and loop
		// blocks are already emitted by the body they belong to.
		if (descriptors.exceptions.handlerByAddress.has(cursor)) return null;
		if (loop.loopBlocks.has(cursor)) return null;
		// Emitting the block at the exit site puts it under the handlers the
		// source sits in. Identical protection keeps that invisible; otherwise
		// only a block that cannot throw is safe to move across the boundary.
		if (
			protectionLedger(cursor, descriptors) !== ledger &&
			!blockCannotThrow(block)
		) return null;
		if (
			block.terminator.kind === 'throw' ||
			(block.terminator.kind === 'return' && !cfg.isScript)
		) return { chain, terminal: cursor };
		if (block.terminator.kind !== 'goto') return null;
		if (chain.length >= MAX_TERMINAL_COMPLETION_CHAIN) return null;
		// A Region already owns this block, so the enclosing composition places
		// it and an ordinary `break` reaches it. Only a destination nobody
		// emits has to carry its own copy.
		if (regionBlocks.has(cursor)) return null;
		// A block with another predecessor is emitted by whichever Region owns
		// that path; claiming it here would drop it from the other one.
		if ((cfg.normalPredecessors.get(cursor)?.size ?? 0) !== 1) return null;
		chain.push(cursor);
		cursor = block.terminator.target;
	}
	return null;
}

/** Handlers protecting `address`, as a stable key. */
function protectionLedger(
	address: BlockAddr,
	descriptors: CFGDescriptors,
): string {
	return descriptors.exceptions.handlers
		.filter((handler) => handler.protectedBlocks.has(address))
		.map((handler) => handler.handler)
		.toSorted((left, right) => left - right)
		.join(',');
}

/**
 * Whether a block's statements can raise.
 *
 * Environment slots are the decompiler's own register state, so reading and
 * writing one is not a user-visible operation that a handler could observe.
 */
function blockCannotThrow(block: CFGBlock): boolean {
	return block.body.every((statement) => {
		if (t.isVariableDeclaration(statement)) {
			return statement.declarations.every((declarator) =>
				declarator.init == null ||
				isNonThrowingValue(declarator.init)
			);
		}
		if (t.isReturnStatement(statement)) {
			return statement.argument == null ||
				isNonThrowingValue(statement.argument);
		}
		if (!t.isExpressionStatement(statement)) return false;
		const expression = statement.expression;
		if (!t.isAssignmentExpression(expression, { operator: '=' })) {
			return isNonThrowingValue(expression);
		}
		// Assigning a local or an environment slot cannot raise; assigning
		// through a user object can, because it may run a setter.
		return (t.isIdentifier(expression.left) ||
			isEnvironmentSlot(expression.left)) &&
			isNonThrowingValue(expression.right);
	});
}

function isNonThrowingValue(expression: t.Node): boolean {
	if (
		t.isIdentifier(expression) || t.isLiteral(expression) ||
		t.isThisExpression(expression)
	) return true;
	if (t.isMemberExpression(expression)) return isEnvironmentSlot(expression);
	// `%Phi` is not executable code at all -- it is lowered to assignments on
	// the incoming edges -- and the environment intrinsics read the
	// decompiler's own register state.
	if (
		t.isCallExpression(expression) &&
		t.isV8IntrinsicIdentifier(expression.callee) &&
		NON_THROWING_INTRINSICS.has(expression.callee.name)
	) {
		return expression.arguments.every((argument) =>
			t.isExpression(argument) && isNonThrowingValue(argument)
		);
	}
	return false;
}

const NON_THROWING_INTRINSICS = new Set([
	'Phi',
	'expectEnvironment',
	'GetParentEnvironment',
]);

function isEnvironmentSlot(expression: t.Node): boolean {
	return t.isMemberExpression(expression) &&
		t.isCallExpression(expression.object) &&
		t.isV8IntrinsicIdentifier(expression.object.callee, {
			name: 'expectEnvironment',
		});
}

/**
 * An exit through this region's own finalizer copy is a fallthrough.
 *
 * `protectedDeferredExitRegion` marks where the protected body leaves through
 * a copied finalizer, and only a loop rewrites those markers. In a try that no
 * loop encloses the marker lowers to a bare `break`, which names control the
 * function does not have: the copy's statements are suppressed because the real
 * `finally` emits them, and the block the copy resumes at is the region's
 * normal exit, which the enclosing composition emits after the `try`. Falling
 * out of the body is exactly that transfer.
 */
function rewriteFinalizerCopyExits(
	region: Extract<Region, { kind: 'tryFinally' }>,
): Region {
	if (region.normalExit == null) return region.body;
	const copyRoots = new AddressSet<BlockAddr>();
	for (const exit of region.deferredExits ?? []) {
		for (const action of exit.actions) {
			if (action.kind === 'finally') {
				copyRoots.add(action.action.copyRoot);
			}
		}
	}
	if (copyRoots.size === 0) return region.body;
	const rewrite = (candidate: Region): Region => {
		if (
			candidate.kind === 'deferredExit' &&
			candidate.exit.kind === 'loopExit' &&
			copyRoots.has(candidate.exit.target)
		) {
			return {
				...candidate,
				exit: { ...candidate.exit, kind: 'toJoin' },
				sourceBlocks: new AddressSet(candidate.sourceBlocks),
			};
		}
		// A nested loop owns its own markers; its emission rewrites them.
		if (candidate.kind === 'loop') return candidate;
		switch (candidate.kind) {
			case 'sequence':
				return {
					...candidate,
					regions: candidate.regions.map(rewrite),
				};
			case 'if':
				return {
					...candidate,
					consequent: rewrite(candidate.consequent),
					alternate: rewrite(candidate.alternate),
				};
			case 'switch':
				return {
					...candidate,
					cases: candidate.cases.map((switchCase) => ({
						...switchCase,
						body: rewrite(switchCase.body),
					})),
					defaultBody: rewrite(candidate.defaultBody),
				};
			case 'tryCatch':
				return {
					...candidate,
					body: rewrite(candidate.body),
					handler: rewrite(candidate.handler),
				};
			case 'tryFinally':
				return {
					...candidate,
					body: rewrite(candidate.body),
					finalizer: rewrite(candidate.finalizer),
				};
			default:
				return candidate;
		}
	};
	return rewrite(region.body);
}

function rewriteDeferredExitsForLoop(
	region: Region,
	loop: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	regionBlocks: AddressSet<BlockAddr>,
): Region {
	if (region.kind === 'deferredExit' && region.exit.kind === 'loopExit') {
		const deferredTarget = region.exit.target;
		const bodyOwnedExit = loop.bodyOwnedExits?.find((exit) => {
			if (!exit.trailer || exit.continuation == null) return false;
			if (!exit.trailer.sourceBlocks.has(deferredTarget)) return false;
			const block = cfg.blocks.get(deferredTarget);
			return block?.terminator.kind === 'goto' &&
				block.terminator.target === exit.continuation;
		});
		if (bodyOwnedExit?.continuation != null) {
			const completion = bodyOwnedExit.continuation;
			const completedExit: LoopRegionExit = {
				...bodyOwnedExit,
				from: deferredTarget,
				to: completion,
				trailer: undefined,
				continuation: undefined,
			};
			return {
				kind: 'sequence',
				regions: [
					{
						kind: 'basic',
						body: [],
						sourceBlocks: new AddressSet([deferredTarget]),
					},
					{
						kind: 'break',
						target: completion,
						exit: completedExit,
						sourceBlocks: new AddressSet(),
					},
				],
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		}
		const control = deferredLoopControlForTarget(region.exit.target, loop);
		const sequenceExit = sharedBreakSequenceExit(
			loop,
			region.exit.target,
		);
		if (sequenceExit?.label) {
			const transfer: Region = {
				kind: 'labelBreak',
				label: sequenceExit.label,
				target: sequenceExit.target,
				sourceBlocks: new AddressSet(),
			};
			if (region.exit.actions.length === 0) return transfer;
			const actions: Region = {
				...region,
				exit: { ...region.exit, kind: 'toJoin' },
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
			return {
				kind: 'sequence',
				regions: [actions, transfer],
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		}
		if (control === 'continue') {
			return {
				kind: 'continue',
				target: loop.header,
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		}
		if (control === 'break') {
			const exit = matchingBreakExit(loop, region.exit.target);
			const completion = exit &&
				breakCompletionForLoop(
					exit,
					loop,
					cfg,
					descriptors,
					regionBlocks,
				);
			if (exit && completion) {
				return terminalCompletionRegion(
					exit.from,
					{
						kind: 'deferredExit',
						exit: { ...region.exit, kind: 'toJoin' },
						sourceBlocks: new AddressSet(),
					},
					completion,
				);
			}
			return {
				kind: 'break',
				target: region.exit.target,
				sourceBlocks: new AddressSet(region.sourceBlocks),
			};
		}
	}
	if (region.kind === 'break') {
		// The builders emit the break directly when the arm is nothing but the
		// exit, so the same completion has to be recovered from the node.
		const exit = region.exit ?? matchingBreakExit(loop, region.target);
		const completion = exit &&
			breakCompletionForLoop(exit, loop, cfg, descriptors, regionBlocks);
		if (exit && completion) {
			return terminalCompletionRegion(exit.from, null, completion);
		}
	}
	const rewrite = (child: Region) =>
		rewriteDeferredExitsForLoop(
			child,
			loop,
			cfg,
			descriptors,
			regionBlocks,
		);
	const rewriteIfArm = (
		arm: Region,
		edge: CFGEdge | undefined,
	): Region => {
		const rewritten = rewrite(arm);
		if (!edge) return rewritten;
		const empty = isEmptyRegion(rewritten);
		const exit = loop.exits.find((candidate) =>
			candidate.kind === 'break' &&
			candidate.trailer != null &&
			(
				empty
					? candidate.from === edge.from && candidate.to === edge.to
					: rewritten.kind === 'basic' &&
						candidate.from === edge.to &&
						rewritten.sourceBlocks.has(candidate.from) &&
						cfg.normalSuccessors.get(candidate.from)?.has(
								candidate.to,
							) ===
							true
			)
		);
		if (!exit) return rewritten;
		// Owner-closed If Regions can omit the transfer for an out-of-loop arm.
		// An empty arm names that edge directly; a one-block arm can perform work
		// before its own exit edge. Materialize the transfer at either boundary so
		// its ordered trailer and Phi actions execute on the path that owns them.
		const transfer: Region = {
			kind: 'break',
			target: exit.to,
			exit,
			sourceBlocks: new AddressSet(),
		};
		if (empty) return transfer;
		return {
			kind: 'sequence',
			regions: [rewritten, transfer],
			sourceBlocks: new AddressSet(rewritten.sourceBlocks),
		};
	};
	switch (region.kind) {
		case 'sequence':
			return {
				...region,
				sourceBlocks: new AddressSet(region.sourceBlocks),
				regions: region.regions.map(rewrite),
			};
		case 'if': {
			const terminator = cfg.blocks.get(region.header)?.terminator;
			const consequentEdge = region.branchEdges?.consequent ??
				(terminator?.kind === 'if'
					? {
						from: region.header,
						to: terminator.taken,
						kind: 'normal' as const,
					}
					: undefined);
			const alternateEdge = region.branchEdges?.alternate ??
				(terminator?.kind === 'if'
					? {
						from: region.header,
						to: terminator.fallthrough,
						kind: 'normal' as const,
					}
					: undefined);
			return {
				...region,
				sourceBlocks: new AddressSet(region.sourceBlocks),
				consequent: rewriteIfArm(region.consequent, consequentEdge),
				alternate: rewriteIfArm(region.alternate, alternateEdge),
			};
		}
		case 'switch':
			return {
				...region,
				sourceBlocks: new AddressSet(region.sourceBlocks),
				cases: region.cases.map((switchCase) => ({
					...switchCase,
					body: rewrite(switchCase.body),
				})),
				defaultBody: rewrite(region.defaultBody),
			};
		case 'tryCatch':
			return {
				...region,
				sourceBlocks: new AddressSet(region.sourceBlocks),
				body: rewrite(region.body),
				handler: rewrite(region.handler),
			};
		case 'tryFinally':
			return {
				...region,
				sourceBlocks: new AddressSet(region.sourceBlocks),
				body: rewrite(region.body),
				finalizer: rewrite(region.finalizer),
			};
		case 'loop':
			return {
				...region,
				sourceBlocks: new AddressSet(region.sourceBlocks),
				body: rewriteDeferredExitsForLoop(
					region.body,
					region,
					cfg,
					descriptors,
					regionBlocks,
				),
			};
		default:
			return region;
	}
}

/**
 * The completion a body break runs, when `break` would not reach its target.
 *
 * One destination is the loop's own continuation and needs the plain `break`
 * the enclosing composition places the code after. Every other destination is
 * unreachable by `break` from here, so it has to carry its own completion or
 * the path is dropped from the emitted function.
 */
function breakCompletionForLoop(
	exit: LoopRegionExit,
	loop: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	regionBlocks: AddressSet<BlockAddr>,
): LoopExitTerminalCompletion | null {
	// A trailer, a completion flag or a labelled sequence exit all mean the
	// builders already placed this edge's control flow somewhere else.
	if (
		exit.trailer || exit.normalCompletionFlag || exit.sequenceExit?.label
	) return null;
	if (exit.to === ordinaryBreakTarget(loop)) return null;
	// The header and latch exits are completed by their own control flow, which
	// is emitted outside the body and would then run twice.
	if (
		exit.from === loop.header || loop.latches.includes(exit.from)
	) return null;
	return terminalCompletionFrom(
		exit.to,
		exit.from,
		cfg,
		descriptors,
		loop,
		regionBlocks,
	);
}

function sharedBreakSequenceExit(
	loop: Extract<Region, { kind: 'loop' }>,
	target: BlockAddr,
): NonNullable<LoopRegionExit['sequenceExit']> | null {
	const matches = loop.exits.filter((exit) =>
		exit.kind === 'break' && !exit.trailer && exit.to === target
	);
	if (matches.length === 0) return null;
	const [sequenceExit] = matches;
	if (
		sequenceExit?.sequenceExit?.label == null ||
		matches.some((exit) =>
			exit.sequenceExit?.target !== sequenceExit.sequenceExit?.target ||
			exit.sequenceExit?.label !== sequenceExit.sequenceExit?.label
		)
	) return null;
	return sequenceExit.sequenceExit;
}

/** The exit this break stands for, when exactly one edge leaves to it. */
function matchingBreakExit(
	loop: Extract<Region, { kind: 'loop' }>,
	target: BlockAddr,
): LoopRegionExit | null {
	const matches = loop.exits.filter((exit) =>
		exit.kind === 'break' && !exit.trailer && exit.to === target
	);
	return matches.length === 1 ? matches[0]! : null;
}

/** The one break destination the loop statement itself continues to. */
function ordinaryBreakTarget(
	loop: Extract<Region, { kind: 'loop' }>,
): BlockAddr | null {
	if (loop.continuation != null) return loop.continuation;
	const destinations = loopBreakDestinations(loop);
	return destinations.size === 1 ? [...destinations][0]! : null;
}

/**
 * Spell a completion as Regions: the edge's own actions, then the blocks it
 * owns, then the shared terminal leaf.
 *
 * The `toJoin` nodes carry nothing but the Phi actions for one edge, which is
 * what keeps a value assigned on the way out of the loop.
 */
function terminalCompletionRegion(
	from: BlockAddr,
	prelude: Region | null,
	completion: LoopExitTerminalCompletion,
): Region {
	const regions: Region[] = prelude ? [prelude] : [];
	let previous = from;
	for (const block of completion.chain) {
		regions.push(edgeActionsRegion(previous, block));
		regions.push({
			kind: 'basic',
			body: [],
			sourceBlocks: new AddressSet([block]),
		});
		previous = block;
	}
	regions.push(edgeActionsRegion(previous, completion.terminal));
	regions.push({
		kind: 'terminalReference',
		entry: completion.terminal,
		sourceBlocks: new AddressSet(),
	});
	return {
		kind: 'sequence',
		regions,
		sourceBlocks: new AddressSet(completion.chain),
	};
}

function edgeActionsRegion(from: BlockAddr, to: BlockAddr): Region {
	return {
		kind: 'deferredExit',
		exit: {
			kind: 'toJoin',
			edge: { from, to, kind: 'normal' },
			target: to,
			actions: [],
		},
		sourceBlocks: new AddressSet(),
	};
}

function deferredLoopControlForTarget(
	target: number,
	loop: Extract<Region, { kind: 'loop' }>,
): 'break' | 'continue' | null {
	if (target === loop.header || loop.latches.includes(target)) {
		return 'continue';
	}
	if (loop.exits.some((exit) => exit.to === target)) return 'break';
	return null;
}

function emitDeferredExit(
	exit: Extract<Region, { kind: 'deferredExit' }>['exit'],
	phiState: PhiEmitState,
): t.Statement[] {
	const statements = emitDeferredExitActions(exit, phiState);
	switch (exit.kind) {
		case 'loopBack':
			statements.push(t.continueStatement());
			break;
		case 'loopExit':
			statements.push(
				exit.label == null
					? t.breakStatement()
					: t.breakStatement(t.identifier(exit.label)),
			);
			break;
		case 'functionReturn':
			if (
				!statements.some((statement) => t.isReturnStatement(statement))
			) {
				statements.push(t.returnStatement());
			}
			break;
		case 'functionThrow':
			if (
				!statements.some((statement) => t.isThrowStatement(statement))
			) {
				statements.push(t.throwStatement(t.identifier('_e')));
			}
			break;
		case 'toJoin':
		case 'exception':
			break;
	}
	return statements;
}

function emitDeferredExitActions(
	exit: Extract<Region, { kind: 'deferredExit' }>['exit'],
	phiState: PhiEmitState,
): t.Statement[] {
	const statements: t.Statement[] = [];
	if ('edge' in exit && exit.edge) {
		statements.push(...takePhiActionsForEdge(exit.edge, phiState));
	}
	for (const action of exit.actions) {
		if (action.kind === 'statement') {
			statements.push(t.cloneNode(action.statement, true));
		} else if (action.kind === 'return') {
			statements.push(t.returnStatement(
				action.argument == null
					? null
					: t.cloneNode(action.argument, true),
			));
		} else if (action.kind === 'throw') {
			statements.push(
				t.throwStatement(t.cloneNode(action.argument, true)),
			);
		} else if (action.kind === 'placedPhi') {
			deletePlacedPhiActions(action, phiState);
		} else if (action.kind === 'phi') {
			for (const assignment of action.assignments) {
				statements.push(assignmentStatement(
					assignment.target,
					assignment.value,
				));
			}
		}
	}
	return statements;
}

function deletePlacedPhiActions(
	action: Extract<DeferredExit['actions'][number], { kind: 'placedPhi' }>,
	phiState: PhiEmitState,
) {
	for (
		const edge of new Map(
			action.assignments.map((assignment) => [
				edgeKey(assignment.edge),
				assignment.edge,
			]),
		).values()
	) {
		phiState.actionsByEdge.delete(edgeKey(edge));
	}
}

function loopBreakContinueCondition(
	statement: t.Statement,
	allowContinueAlternate: boolean,
): t.Expression | null {
	if (!t.isIfStatement(statement)) return null;
	const consequent = statementBody(statement.consequent);
	if (
		consequent.length !== 1 ||
		!t.isBreakStatement(consequent[0]) ||
		consequent[0].label
	) return null;
	const alternate = statementBody(statement.alternate);
	if (
		alternate.length > 0 &&
		(!allowContinueAlternate || alternate.length !== 1 ||
			!t.isContinueStatement(alternate[0]) || alternate[0].label)
	) return null;
	return invertTest(t.cloneNode(statement.test, true));
}

function containsContinueTargetingLoop(body: readonly t.Statement[]): boolean {
	let found = false;
	const visit = (node: t.Node, nestedLoops: number) => {
		if (found || t.isFunction(node) || t.isClass(node)) return;
		if (t.isContinueStatement(node)) {
			if (!node.label && nestedLoops === 0) found = true;
			return;
		}
		const childLoopDepth = t.isLoop(node) ? nestedLoops + 1 : nestedLoops;
		for (const key of t.VISITOR_KEYS[node.type] ?? []) {
			const value = (node as unknown as Record<string, unknown>)[key];
			for (const child of Array.isArray(value) ? value : [value]) {
				if (
					child && typeof child === 'object' &&
					typeof (child as t.Node).type === 'string'
				) visit(child as t.Node, childLoopDepth);
			}
		}
	};
	for (const statement of body) visit(statement, 0);
	return found;
}

function generatedConditionAlias(
	expression: t.Expression,
): t.Identifier | null {
	while (
		t.isUnaryExpression(expression, { operator: '!' }) &&
		t.isExpression(expression.argument)
	) {
		expression = expression.argument;
	}
	return t.isIdentifier(expression) && /^r\d+_\d+$/.test(expression.name)
		? expression
		: null;
}

function resolveGeneratedConditionAlias(
	resolve: (expression: t.Expression) => t.Expression,
	expression: t.Expression,
): t.Expression {
	return generatedConditionAlias(expression)
		? resolve(expression)
		: t.cloneNode(expression, true);
}

function foldGuardedLoopExitTestStatement(
	statement: t.Statement,
	prefix: t.Statement[],
): t.Statement {
	const conditions: t.Expression[] = [];
	let nested: t.Statement = statement;
	while (
		t.isIfStatement(nested) &&
		statementBody(nested.alternate).length === 0
	) {
		const consequent = statementBody(nested.consequent);
		if (consequent.length !== 1) return statement;
		conditions.push(t.cloneNode(nested.test, true));
		nested = consequent[0]!;
	}
	if (
		conditions.length === 0 ||
		!t.isWhileStatement(nested) ||
		!t.isBlockStatement(nested.body)
	) return statement;

	const loopBody = nested.body.body;
	const resolvePrefixCondition = createLatchConditionResolver(prefix);
	const resolveLoopCondition = createLatchConditionResolver(loopBody);
	const resolvedConditions = conditions.map((condition) =>
		resolveGeneratedConditionAlias(resolvePrefixCondition, condition)
	);
	if (loopBody.length < conditions.length) return statement;
	const firstGuard = loopBody.length - conditions.length;
	const continueConditions: t.Expression[] = [];
	for (let i = 0; i < conditions.length; i++) {
		const continueCondition = loopBreakContinueCondition(
			loopBody[firstGuard + i]!,
			i === conditions.length - 1,
		);
		const resolvedContinueCondition = continueCondition
			? resolveGeneratedConditionAlias(
				resolveLoopCondition,
				continueCondition,
			)
			: null;
		if (
			!continueCondition || !resolvedContinueCondition ||
			!t.isNodesEquivalent(
				resolvedContinueCondition,
				resolvedConditions[i]!,
			)
		) return statement;
		continueConditions.push(continueCondition);
	}
	const body = loopBody.slice(0, firstGuard);
	if (containsContinueTargetingLoop(body)) return statement;

	const testParts = [
		...resolvedConditions,
		...(t.isBooleanLiteral(nested.test, { value: true }) ? [] : [
			resolveGeneratedConditionAlias(
				resolveLoopCondition,
				nested.test,
			),
		]),
	];
	const preservedFoldNames = new Set<string>();
	for (const testPart of testParts) {
		for (
			const name of referencedIdentifierNames([
				t.expressionStatement(testPart),
			])
		) {
			preservedFoldNames.add(name);
		}
	}
	for (const name of referencedIdentifierNames(body)) {
		preservedFoldNames.add(name);
	}
	for (let i = 0; i < conditions.length; i++) {
		const entryAlias = generatedConditionAlias(conditions[i]!);
		const latchAlias = generatedConditionAlias(continueConditions[i]!);
		if (entryAlias) preservedFoldNames.delete(entryAlias.name);
		if (latchAlias) preservedFoldNames.delete(latchAlias.name);
		if (entryAlias) {
			removeLatchConditionDeclaration(
				{ body: prefix },
				entryAlias,
				preservedFoldNames,
			);
		}
		if (latchAlias) {
			removeLatchConditionDeclaration(
				{ body },
				latchAlias,
				preservedFoldNames,
			);
		}
	}
	const test = testParts.slice(1).reduce<t.Expression>(
		(left, right) =>
			t.logicalExpression(
				'&&',
				left,
				t.cloneNode(right, true),
			),
		t.cloneNode(testParts[0]!, true),
	);
	const loop = t.cloneNode(nested, false);
	loop.test = test;
	loop.body = t.blockStatement(body);
	return loop;
}

function singleResultDeclaration(
	statement: t.Statement | undefined,
): { name: string; init: t.Expression } | null {
	if (
		!statement || !t.isVariableDeclaration(statement) ||
		statement.declarations.length !== 1
	) return null;
	const [declaration] = statement.declarations;
	if (
		!t.isIdentifier(declaration.id) ||
		!declaration.init ||
		!t.isExpression(declaration.init)
	) return null;
	return { name: declaration.id.name, init: declaration.init };
}

function generatedResultDoneTest(
	expression: t.Expression,
	resultName: string,
): boolean {
	return t.isUnaryExpression(expression, { operator: '!' }) &&
		t.isMemberExpression(expression.argument, { computed: false }) &&
		t.isIdentifier(expression.argument.object, { name: resultName }) &&
		t.isIdentifier(expression.argument.property, { name: 'done' });
}

function identifierAssignment(
	statement: t.Statement | undefined,
	target: string,
	value: string,
): boolean {
	return !!statement &&
		t.isExpressionStatement(statement) &&
		t.isAssignmentExpression(statement.expression, { operator: '=' }) &&
		t.isIdentifier(statement.expression.left, { name: target }) &&
		t.isIdentifier(statement.expression.right, { name: value });
}

function hasUninitialisedGeneratedLet(
	statements: readonly t.Statement[],
	name: string,
): boolean {
	if (!/^r\d+_\d+$/.test(name)) return false;
	return statements.some((statement) =>
		t.isVariableDeclaration(statement, { kind: 'let' }) &&
		statement.declarations.some((declaration) =>
			t.isIdentifier(declaration.id, { name }) && declaration.init == null
		)
	);
}

function foldLoopCarriedResultGuard(
	statement: t.Statement,
	prefix: t.Statement[],
): t.WhileStatement | null {
	if (!t.isIfStatement(statement) || statement.alternate) return null;
	const guarded = statementBody(statement.consequent);
	if (guarded.length !== 2) return null;
	const [initialAssignment, candidateLoop] = guarded;
	if (
		!candidateLoop ||
		!t.isWhileStatement(candidateLoop) ||
		!t.isBooleanLiteral(candidateLoop.test, { value: true }) ||
		!t.isBlockStatement(candidateLoop.body)
	) return null;

	const initial = singleResultDeclaration(prefix.at(-1));
	if (
		!initial || !/^r\d+_\d+$/.test(initial.name) ||
		!t.isCallExpression(initial.init) ||
		!generatedResultDoneTest(statement.test, initial.name)
	) return null;
	if (
		!initialAssignment ||
		!t.isExpressionStatement(initialAssignment) ||
		!t.isAssignmentExpression(initialAssignment.expression, {
			operator: '=',
		}) ||
		!t.isIdentifier(initialAssignment.expression.left) ||
		!t.isIdentifier(initialAssignment.expression.right, {
			name: initial.name,
		})
	) return null;
	const carriedName = initialAssignment.expression.left.name;
	if (!hasUninitialisedGeneratedLet(prefix.slice(0, -1), carriedName)) {
		return null;
	}

	const loopBody = candidateLoop.body.body;
	if (loopBody.length < 2) return null;
	const next = singleResultDeclaration(loopBody.at(-2));
	const latch = loopBody.at(-1);
	if (
		!next || !/^r\d+_\d+$/.test(next.name) ||
		!t.isCallExpression(next.init) ||
		!t.isNodesEquivalent(initial.init, next.init) ||
		!latch || !t.isIfStatement(latch) ||
		!generatedResultDoneTest(latch.test, next.name)
	) return null;
	const continueArm = statementBody(latch.consequent);
	const breakArm = statementBody(latch.alternate);
	if (
		continueArm.length !== 2 ||
		!identifierAssignment(continueArm[0], carriedName, next.name) ||
		!t.isContinueStatement(continueArm[1]) ||
		continueArm[1].label ||
		breakArm.length !== 1 ||
		!t.isBreakStatement(breakArm[0]) ||
		breakArm[0].label
	) return null;

	prefix.pop();
	prefix.push(
		assignmentStatement(
			t.identifier(carriedName),
			t.cloneNode(initial.init, true),
		),
	);
	const loop = t.cloneNode(candidateLoop, false);
	loop.test = t.unaryExpression(
		'!',
		t.memberExpression(t.identifier(carriedName), t.identifier('done')),
	);
	loop.body = t.blockStatement([
		...loopBody.slice(0, -2).map((bodyStatement) =>
			t.cloneNode(bodyStatement, true)
		),
		assignmentStatement(
			t.identifier(carriedName),
			t.cloneNode(next.init, true),
		),
	]);
	return loop;
}

/**
 * Fold split loop entry/latch tests into one loop condition.
 *
 * Equal condition aliases can move directly. Iterator-result loops additionally
 * move their first and subsequent acquisitions onto one loop-carried result.
 */
export function foldGuardedLoopExitTests(
	statements: t.Statement[],
): t.Statement[] {
	const folded: t.Statement[] = [];
	for (let index = 0; index < statements.length; index++) {
		const statement = statements[index]!;
		const carriedResultLoop = index === statements.length - 1
			? foldLoopCarriedResultGuard(statement, folded)
			: null;
		folded.push(
			carriedResultLoop ??
				foldGuardedLoopExitTestStatement(statement, folded),
		);
	}
	return folded;
}

function simplifyEmittedStatements(
	statements: t.Statement[],
	removeWriteOnly = true,
): t.Statement[] {
	const simplified = mergeAdjacentIfsWithSameBody(
		flattenNestedGuardStatements(
			simplifyPhiInitializers(
				simplifyPostfixIndexUpdates(
					simplifyEmptyIfStatements(
						rewriteNestedStatementLists(
							statements,
							lowerFoldedControlPhis,
						),
					),
				),
			),
		),
	);
	const folded = foldGuardedLoopExitTests(simplified);
	// Dead-write analysis needs the whole emitted function. Running it while the
	// structural recursion is visiting one arm mistakes values read by sibling
	// arms or an outer continuation for local write-only temporaries.
	return removeWriteOnly
		? removeWriteOnlyIdentifierStatements(folded)
		: folded;
}

/**
 * Turn acyclic fallback labels back into ordinary conditionals when every exit
 * from the labelled block is a terminal arm of a top-level `if`.
 *
 * The bounded DAG composer deliberately emits forward edges as labelled
 * breaks.  Once inner scopes have been simplified, common guard forests have
 * the form `L: { if (a) break L; if (b) break L; tail; }`.  Retaining the
 * labels obscures an otherwise ordinary `if (!a && !b) { tail; }` and prevents
 *
 * This rewrite is intentionally conservative: an unsupported break shape
 * leaves its label untouched.  Break actions preceding the terminal break are
 * preserved in the exiting arm.
 */
export function simplifyForwardExitLabels(
	statements: readonly t.Statement[],
): t.Statement[] {
	const rewrittenStatements = statements.map((statement) =>
		rewriteForwardExitLabelChildren(statement)
	);
	const declarationCounts = new Map<string, number>();
	for (const statement of rewrittenStatements) {
		const candidates = t.isLabeledStatement(statement) &&
				t.isBlockStatement(statement.body)
			? statement.body.body
			: [statement];
		for (const name of directBlockScopedDeclarationNames(candidates)) {
			declarationCounts.set(name, (declarationCounts.get(name) ?? 0) + 1);
		}
	}

	return rewrittenStatements.flatMap((rewritten) => {
		if (
			!t.isLabeledStatement(rewritten) ||
			!t.isBlockStatement(rewritten.body)
		) return [rewritten];

		const lowered = lowerForwardLabelBody(
			rewritten.body.body,
			rewritten.label.name,
		);
		// Continuation-style lowering may place a shared suffix in more than one
		// mutually-exclusive arm. That preserves execution semantics but destroys
		// the forest's exact single-copy ownership and can multiply large trailers.
		// Reject any lowering that duplicates an observable leaf, then fall back
		// to conjoining the guards, which reaches the same shape without copying.
		// The duplication check compares fingerprints, so it also fires when a
		// guard's inverted test happens to read like an unrelated test already
		// in the block -- `!(a === b)` prints as `a !== b`, which may well
		// appear elsewhere. That is a coincidence, not a copied trailer. What
		// the check is really defending against is multiplication, so let a
		// lowering through when it did not actually grow anything.
		const multiplies = lowered != null &&
			duplicatesLeafStatements(rewritten.body.body, lowered) &&
			statementTreeSize(lowered) >
				statementTreeSize(rewritten.body.body);
		const usable = lowered && !multiplies
			? lowered
			: conjoinPureExitGuards(rewritten.body.body, rewritten.label.name);
		if (!usable) return [rewritten];
		// A lowering that leaves a `break <label>` standing has just removed the
		// only declaration of the label it transfers to.
		if (
			containsControlTransferToLabel(
				t.blockStatement(usable),
				rewritten.label.name,
			)
		) return [rewritten];
		const collides = directBlockScopedDeclarationNames(
			rewritten.body.body,
		).some((name) => (declarationCounts.get(name) ?? 0) > 1);
		return collides ? [t.blockStatement(usable)] : usable;
	});
}

/**
 * The condition under which a pure exit guard takes its `break`.
 *
 * A pure exit guard is a chain of `if`s with no `else` and nothing in them but
 * the next `if`, ending in `break label`. `if (a) if (b) break L` guards on
 * `a && b`. Anything else in the chain -- a statement beside the nested test,
 * an alternate arm -- means the guard does more than decide, so it is not one.
 */
function pureExitGuardCondition(
	statement: t.Statement,
	label: string,
): t.Expression | null {
	if (!t.isIfStatement(statement) || statement.alternate) return null;
	const consequent = statementBody(statement.consequent);
	if (consequent.length !== 1) return null;
	const [inner] = consequent;
	const test = t.cloneNode(statement.test, true);
	if (t.isBreakStatement(inner) && inner.label?.name === label) return test;
	const nested = pureExitGuardCondition(inner, label);
	return nested ? t.logicalExpression('&&', test, nested) : null;
}

/**
 * Collapse a forest of pure exit guards into one conjoined conditional.
 *
 * `L: { if (a) if (b) break L; if (c) if (d) break L; tail }` is only saying
 * `if (!(a && b) && !(c && d)) { tail }`. Continuation-style lowering cannot
 * reach that form: it pushes the remainder down every non-exiting path, so
 * `tail` lands in two arms and `duplicatesLeafStatements` rightly refuses it.
 * When every exit is nothing but tests, conjoining the guards says the same
 * thing with `tail` left in one piece.
 *
 * Evaluation order survives because `&&` short-circuits in the order the
 * guards were written, and a guard that is only tests has nothing else to
 * observe. A guard forest with no tail is left alone -- there would be nothing
 * to guard, and the tests may still be worth evaluating.
 */
function conjoinPureExitGuards(
	body: readonly t.Statement[],
	label: string,
): t.Statement[] | null {
	const guards: t.Expression[] = [];
	let index = 0;
	while (index < body.length) {
		const condition = pureExitGuardCondition(body[index]!, label);
		if (!condition) break;
		guards.push(condition);
		index++;
	}
	if (guards.length === 0) return null;
	const tail = body.slice(index);
	if (tail.length === 0) return null;
	// A reference left in the tail is a backward or mid-body exit, which a
	// conjunction cannot express.
	if (tail.some((statement) => containsBreakToLabel(statement, label))) {
		return null;
	}
	const test = guards
		.map((condition) => invertTest(condition))
		.reduce((left, right) => t.logicalExpression('&&', left, right));
	return [t.ifStatement(test, t.blockStatement([...tail]))];
}

/** Node count of a statement list, as a cheap stand-in for emitted size. */
function statementTreeSize(statements: readonly t.Statement[]): number {
	let size = 0;
	for (const statement of statements) {
		t.traverseFast(statement, () => {
			size++;
		});
	}
	return size;
}

function duplicatesLeafStatements(
	before: readonly t.Statement[],
	after: readonly t.Statement[],
): boolean {
	const counts = (statements: readonly t.Statement[]) => {
		const result = new Map<string, number>();
		for (const statement of statements) {
			t.traverseFast(statement, (node) => {
				if (node !== statement && t.isFunction(node)) {
					return t.traverseFast.skip;
				}
				const controlExpression = t.isIfStatement(node) ||
						(t.isWhileStatement(node) || t.isDoWhileStatement(node))
					? node.test
					: t.isForStatement(node)
					? node.test
					: t.isSwitchStatement(node)
					? node.discriminant
					: null;
				if (controlExpression) {
					const fingerprint = `control:${
						generate(controlExpression).code
					}`;
					result.set(
						fingerprint,
						(result.get(fingerprint) ?? 0) + 1,
					);
				}
				if (
					!t.isExpressionStatement(node) &&
					!t.isReturnStatement(node) && !t.isThrowStatement(node)
				) return;
				const fingerprint = generate(node).code;
				result.set(fingerprint, (result.get(fingerprint) ?? 0) + 1);
			});
		}
		return result;
	};
	const original = counts(before);
	for (const [fingerprint, count] of counts(after)) {
		const previous = original.get(fingerprint);
		if (previous != null && count > previous) return true;
	}
	return false;
}

function directBlockScopedDeclarationNames(
	statements: readonly t.Statement[],
): string[] {
	const names: string[] = [];
	for (const statement of statements) {
		if (
			!t.isVariableDeclaration(statement) || statement.kind === 'var'
		) continue;
		for (const declaration of statement.declarations) {
			t.traverseFast(declaration.id, (node) => {
				if (t.isIdentifier(node)) names.push(node.name);
			});
		}
	}
	return names;
}

function rewriteForwardExitLabelChildren(statement: t.Statement): t.Statement {
	const shallow = <T extends t.Node>(node: T): T => t.cloneNode(node, false);
	if (t.isBlockStatement(statement)) {
		const cloned = shallow(statement);
		cloned.body = simplifyForwardExitLabels(statement.body);
		return cloned;
	}
	if (t.isLabeledStatement(statement)) {
		const cloned = shallow(statement);
		cloned.body = rewriteForwardExitLabelChildren(statement.body);
		return cloned;
	}
	if (t.isIfStatement(statement)) {
		const cloned = shallow(statement);
		cloned.consequent = rewriteForwardExitLabelChildren(
			statement.consequent,
		);
		cloned.alternate = statement.alternate
			? rewriteForwardExitLabelChildren(statement.alternate)
			: null;
		return cloned;
	}
	if (
		t.isWhileStatement(statement) || t.isDoWhileStatement(statement) ||
		t.isForStatement(statement) || t.isForInStatement(statement) ||
		t.isForOfStatement(statement)
	) {
		const cloned = shallow(statement);
		cloned.body = rewriteForwardExitLabelChildren(statement.body);
		return cloned;
	}
	if (t.isTryStatement(statement)) {
		const cloned = shallow(statement);
		cloned.block = shallow(statement.block);
		cloned.block.body = simplifyForwardExitLabels(statement.block.body);
		if (statement.handler) {
			cloned.handler = shallow(statement.handler);
			cloned.handler.body = shallow(statement.handler.body);
			cloned.handler.body.body = simplifyForwardExitLabels(
				statement.handler.body.body,
			);
		}
		if (statement.finalizer) {
			cloned.finalizer = shallow(statement.finalizer);
			cloned.finalizer.body = simplifyForwardExitLabels(
				statement.finalizer.body,
			);
		}
		return cloned;
	}
	if (t.isSwitchStatement(statement)) {
		const cloned = shallow(statement);
		cloned.cases = statement.cases.map((switchCase) => {
			const rewrittenCase = shallow(switchCase);
			rewrittenCase.consequent = simplifyForwardExitLabels(
				switchCase.consequent,
			);
			return rewrittenCase;
		});
		return cloned;
	}
	return statement;
}

function containsBreakToLabel(node: t.Node, label: string): boolean {
	let found = false;
	t.traverseFast(node, (child) => {
		if (found) return t.traverseFast.skip;
		if (child !== node && t.isFunction(child)) {
			return t.traverseFast.skip;
		}
		if (
			t.isBreakStatement(child) &&
			child.label?.name === label
		) found = true;
	});
	return found;
}

/**
 * A nested natural loop only needs to label an ancestor when it actually
 * transfers control across that ancestor. The loop forest conservatively marks
 * every loop with children as label-capable, but emitting all of those labels
 * leaves inert `loop_*:` wrappers throughout otherwise structured output.
 * Decide from the final emitted body, where the requirement is exact.
 */
function labelLoopWhenReferenced<T extends t.Statement>(
	loop: T,
	label: string | undefined,
): T | t.LabeledStatement {
	if (!label || !containsControlTransferToLabel(loop, label)) return loop;
	return t.labeledStatement(t.identifier(label), loop);
}

function containsControlTransferToLabel(
	node: t.Node,
	label: string,
): boolean {
	let found = false;
	t.traverseFast(node, (child) => {
		if (found) return t.traverseFast.skip;
		if (child !== node && t.isFunction(child)) {
			return t.traverseFast.skip;
		}
		if (
			(t.isBreakStatement(child) || t.isContinueStatement(child)) &&
			child.label?.name === label
		) found = true;
	});
	return found;
}

function lowerForwardLabelBody(
	body: readonly t.Statement[],
	label: string,
): t.Statement[] | null {
	const lowered = lowerForwardLabelSequence(body, label, []);
	return lowered?.statements ?? null;
}

interface LoweredForwardLabelSequence {
	statements: t.Statement[];
	sawExit: boolean;
}

/**
 * Continuation-style lowering for a forward label. Normal paths receive the
 * remainder of the labelled body; `break label` paths do not. This also handles
 * exits nested in an if arm without introducing a flag variable.
 */
function lowerForwardLabelSequence(
	body: readonly t.Statement[],
	label: string,
	continuation: readonly t.Statement[],
): LoweredForwardLabelSequence | null {
	const firstExit = body.findIndex((statement) =>
		containsBreakToLabel(statement, label)
	);
	if (firstExit < 0) {
		const loweredContinuation = continuation.length === 0
			? { statements: [] as t.Statement[], sawExit: false }
			: lowerForwardLabelSequence(continuation, label, []);
		if (!loweredContinuation) return null;
		const bodyNames = new Set(directBlockScopedDeclarationNames(body));
		const continuationCollides = directBlockScopedDeclarationNames(
			loweredContinuation.statements,
		).some((name) => bodyNames.has(name));
		return {
			statements: continuationCollides
				? [
					...body,
					t.blockStatement(loweredContinuation.statements),
				]
				: [...body, ...loweredContinuation.statements],
			sawExit: loweredContinuation.sawExit,
		};
	}

	const prefix = body.slice(0, firstExit);
	const exitStatement = body[firstExit]!;
	if (
		t.isBreakStatement(exitStatement) &&
		exitStatement.label?.name === label
	) return { statements: [...prefix], sawExit: true };
	if (t.isBlockStatement(exitStatement)) {
		const loweredBlock = lowerForwardLabelSequence(
			exitStatement.body,
			label,
			[
				...body.slice(firstExit + 1),
				...continuation,
			],
		);
		if (!loweredBlock) return null;
		return {
			statements: [
				...prefix,
				t.blockStatement(loweredBlock.statements),
			],
			sawExit: loweredBlock.sawExit,
		};
	}
	if (!t.isIfStatement(exitStatement)) return null;

	const branchContinuation = [
		...body.slice(firstExit + 1),
		...continuation,
	];
	const consequent = lowerForwardLabelSequence(
		statementBody(exitStatement.consequent),
		label,
		branchContinuation,
	);
	if (!consequent) return null;
	const alternate = exitStatement.alternate
		? lowerForwardLabelSequence(
			statementBody(exitStatement.alternate),
			label,
			branchContinuation,
		)
		: lowerForwardLabelSequence(branchContinuation, label, []);
	if (!alternate || (!consequent.sawExit && !alternate.sawExit)) return null;

	return {
		statements: [
			...prefix,
			...forwardExitConditional(
				exitStatement.test,
				consequent.statements,
				alternate.statements,
			),
		],
		sawExit: true,
	};
}

function forwardExitConditional(
	test: t.Expression,
	consequent: t.Statement[],
	alternate: t.Statement[],
): t.Statement[] {
	if (consequent.length === 0 && alternate.length > 0) {
		return [t.ifStatement(
			invertTest(t.cloneNode(test, true)),
			t.blockStatement(alternate),
		)];
	}
	if (alternate.length === 0 && consequent.length > 0) {
		return [t.ifStatement(
			t.cloneNode(test, true),
			t.blockStatement(consequent),
		)];
	}
	if (consequent.length === 0 && alternate.length === 0) {
		return isPureCondition(test)
			? []
			: [t.expressionStatement(t.cloneNode(test, true))];
	}
	return [t.ifStatement(
		t.cloneNode(test, true),
		t.blockStatement(consequent),
		t.blockStatement(alternate),
	)];
}

function statementBody(
	statement: t.Statement | null | undefined,
): t.Statement[] {
	if (!statement) return [];
	return t.isBlockStatement(statement) ? statement.body : [statement];
}

function singleReturnStatement(
	statement: t.Statement,
): t.ReturnStatement | null {
	if (t.isReturnStatement(statement)) return statement;
	if (!t.isBlockStatement(statement) || statement.body.length !== 1) {
		return null;
	}
	const [only] = statement.body;
	return t.isReturnStatement(only) ? only : null;
}

function splitConjunction(
	expr: t.Expression,
	left: t.Expression,
): { left: t.Expression; right: t.Expression } | null {
	if (!t.isLogicalExpression(expr, { operator: '&&' })) return null;
	if (!sameExpression(expr.left, left)) return null;
	if (!t.isExpression(expr.right)) return null;
	return { left: expr.left, right: expr.right };
}

function splitRedundantOrGuard(
	expr: t.Expression,
): { left: t.Expression; right: t.Expression } | null {
	if (!t.isLogicalExpression(expr, { operator: '||' })) return null;
	const leftConjunction = splitConjunctionWithAnySide(expr.left, expr.right);
	if (leftConjunction) return leftConjunction;
	return splitConjunctionWithAnySide(expr.right, expr.left);
}

function splitConjunctionWithAnySide(
	conjunction: t.Expression | t.PrivateName,
	other: t.Expression | t.PrivateName,
): { left: t.Expression; right: t.Expression } | null {
	if (!t.isExpression(conjunction) || !t.isExpression(other)) return null;
	const direct = splitConjunction(conjunction, other);
	if (direct) return direct;
	if (!t.isLogicalExpression(conjunction, { operator: '&&' })) return null;
	if (!sameExpression(conjunction.right, other)) return null;
	if (!t.isExpression(conjunction.left)) return null;
	return { left: conjunction.right, right: conjunction.left };
}

function isNegationOf(expr: t.Expression, positive: t.Expression): boolean {
	if (
		t.isUnaryExpression(expr, { operator: '!' }) &&
		t.isExpression(expr.argument) &&
		sameExpression(expr.argument, positive)
	) return true;
	return sameExpression(expr, invertTest(t.cloneNode(positive, true)));
}

function sameExpression(
	a: t.Expression | t.PrivateName,
	b: t.Expression,
): boolean {
	if (!t.isExpression(a)) return false;

	return generate(a).code === generate(b).code;
}

/**
 * Spell a Phi merged by control a reducer already folded into a block body.
 *
 * Region recovery reads Phi provenance from CFG edges. Once a compatibility
 * pass has composed a branch into an `if` statement inside a block, the join
 * block has a single predecessor, so that Phi has no edge to carry its copies
 * and no descriptor is recovered for it. Assign the target on the folded paths
 * instead: the arm defining a source ends with the copy, and a source defined
 * before the statement is the target's initial value.
 */
function lowerFoldedControlPhis(statements: t.Statement[]): t.Statement[] {
	const lowered: t.Statement[] = [];
	for (const statement of statements) {
		const previous = lowered.at(-1);
		const merge = previous && t.isIfStatement(previous)
			? foldedControlPhiMerge(previous, statement)
			: null;
		if (!merge) {
			lowered.push(statement);
			continue;
		}
		lowered.pop();
		lowered.push(merge.declaration, merge.ifStatement);
	}
	return lowered;
}

function foldedControlPhiMerge(
	ifStatement: t.IfStatement,
	statement: t.Statement,
): { declaration: t.Statement; ifStatement: t.IfStatement } | null {
	const phi = phiIntrinsicDeclaration(statement);
	if (!phi) return null;
	const arms = [ifStatement.consequent, ifStatement.alternate];
	const armSources: Array<t.Identifier | undefined> = [undefined, undefined];
	let outerSource: t.Identifier | undefined;
	for (const source of phi.sources) {
		const owners = arms.map((arm, index) =>
			arm != null && branchDeclaredNames(arm).has(source.name)
				? index
				: -1
		).filter((index) => index >= 0);
		if (owners.length > 1) return null;
		if (owners.length === 0) {
			// More than one source from outside the statement would need the
			// branch structure this Phi no longer records.
			if (outerSource) return null;
			outerSource = source;
			continue;
		}
		const [owner] = owners;
		if (armSources[owner]) return null;
		armSources[owner] = source;
	}
	if (!armSources.some((source) => source != null)) return null;
	// Both arms plus a value from before the statement is three merged paths,
	// so the folded `if` is not the whole join and its arms cannot spell it.
	if (armSources[0] && armSources[1] && outerSource) return null;
	// A path the Phi merges but neither arm defines runs the value the code
	// before the statement left; without such a source that path is unmodelled.
	const unassignedPath = arms.some((arm, index) =>
		armSources[index] == null && (arm != null || index === 1)
	);
	if (unassignedPath && !outerSource) return null;
	const merged = t.cloneNode(ifStatement, false);
	const branches = arms.map((arm, index) => {
		const source = armSources[index];
		if (arm == null || source == null) return arm;
		const body = branchStatements(arm);
		if (body.some((entry) => isCompletionStatement(entry))) return null;
		return t.blockStatement([
			...body,
			assignmentStatement(phi.target, source),
		]);
	});
	if (
		branches.some((branch, index) => branch == null && arms[index] != null)
	) {
		return null;
	}
	merged.consequent = branches[0] ?? t.blockStatement([]);
	merged.alternate = branches[1] ?? null;
	return {
		declaration: t.variableDeclaration('let', [t.variableDeclarator(
			t.cloneNode(phi.target),
			outerSource ? t.cloneNode(outerSource) : null,
		)]),
		ifStatement: merged,
	};
}

/** `const x = %Phi(a, b);`, the shape edge placement never claimed. */
function phiIntrinsicDeclaration(
	statement: t.Statement,
): { target: t.Identifier; sources: t.Identifier[] } | null {
	if (!t.isVariableDeclaration(statement)) return null;
	const [declarator, ...rest] = statement.declarations;
	if (rest.length > 0 || !declarator || !t.isIdentifier(declarator.id)) {
		return null;
	}
	const init = declarator.init;
	if (
		!t.isCallExpression(init) ||
		!t.isV8IntrinsicIdentifier(init.callee, { name: 'Phi' }) ||
		init.arguments.length === 0 ||
		!init.arguments.every((argument) => t.isIdentifier(argument))
	) return null;
	return {
		target: declarator.id,
		sources: init.arguments as t.Identifier[],
	};
}

function branchDeclaredNames(branch: t.Statement): Set<string> {
	const names = new Set<string>();
	for (const statement of branchStatements(branch)) {
		if (!t.isVariableDeclaration(statement)) continue;
		for (const declarator of statement.declarations) {
			if (t.isIdentifier(declarator.id)) names.add(declarator.id.name);
		}
	}
	return names;
}

function isCompletionStatement(statement: t.Statement): boolean {
	return t.isReturnStatement(statement) || t.isThrowStatement(statement) ||
		t.isBreakStatement(statement) || t.isContinueStatement(statement);
}

/** Apply a list rewrite to every nested statement list, innermost first. */
function rewriteNestedStatementLists(
	statements: readonly t.Statement[],
	rewrite: (statements: t.Statement[]) => t.Statement[],
): t.Statement[] {
	const rewriteBlock = (block: t.BlockStatement): t.BlockStatement =>
		t.blockStatement(rewriteNestedStatementLists(block.body, rewrite));
	// A branch that was not a block stays unbraced when the rewrite leaves one
	// statement: `label: for (…)` and `label: { for (…) }` are different shapes
	// to the label and loop simplifications that run after this pass.
	const rewriteBranch = (branch: t.Statement): t.Statement => {
		if (t.isBlockStatement(branch)) return rewriteBlock(branch);
		const rewritten = rewriteNestedStatementLists([branch], rewrite);
		return rewritten.length === 1
			? rewritten[0]!
			: t.blockStatement(rewritten);
	};
	return rewrite(statements.map((statement) => {
		if (t.isBlockStatement(statement)) return rewriteBranch(statement);
		if (t.isIfStatement(statement)) {
			const cloned = t.cloneNode(statement, false);
			cloned.consequent = rewriteBranch(statement.consequent);
			cloned.alternate = statement.alternate
				? rewriteBranch(statement.alternate)
				: null;
			return cloned;
		}
		if (
			t.isLabeledStatement(statement) ||
			t.isWhileStatement(statement) ||
			t.isDoWhileStatement(statement) ||
			t.isForStatement(statement) ||
			t.isForInStatement(statement) ||
			t.isForOfStatement(statement)
		) {
			const cloned = t.cloneNode(statement, false);
			cloned.body = rewriteBranch(statement.body);
			return cloned;
		}
		if (t.isTryStatement(statement)) {
			const cloned = t.cloneNode(statement, false);
			cloned.block = rewriteBlock(statement.block);
			if (statement.handler) {
				cloned.handler = t.cloneNode(statement.handler, false);
				cloned.handler.body = rewriteBlock(statement.handler.body);
			}
			cloned.finalizer = statement.finalizer
				? rewriteBlock(statement.finalizer)
				: null;
			return cloned;
		}
		if (t.isSwitchStatement(statement)) {
			const cloned = t.cloneNode(statement, false);
			cloned.cases = statement.cases.map((switchCase) => {
				const clonedCase = t.cloneNode(switchCase, false);
				clonedCase.consequent = rewriteNestedStatementLists(
					switchCase.consequent,
					rewrite,
				);
				return clonedCase;
			});
			return cloned;
		}
		return statement;
	}));
}

function simplifyPhiInitializers(statements: t.Statement[]): t.Statement[] {
	const initializers = findSimpleInitializerAssignments(statements);
	if (initializers.size === 0) return statements;
	return statements.flatMap((statement) =>
		simplifyPhiInitializerStatement(statement, initializers)
	);
}

function findSimpleInitializerAssignments(
	statements: readonly t.Statement[],
): Map<string, { temp: string; init: t.Expression }> {
	const declarations = new Map<string, t.Expression>();
	const declarationIndexes = new Map<string, number>();
	const uninitializedLets = new Map<string, number>();
	const assignmentCounts = new Map<string, number>();
	const identifierCounts = new Map<string, number>();
	for (const [index, statement] of statements.entries()) {
		t.traverseFast(statement, (node) => {
			if (t.isIdentifier(node)) {
				identifierCounts.set(
					node.name,
					(identifierCounts.get(node.name) ?? 0) + 1,
				);
			}
			if (
				t.isAssignmentExpression(node) &&
				t.isIdentifier(node.left)
			) {
				assignmentCounts.set(
					node.left.name,
					(assignmentCounts.get(node.left.name) ?? 0) + 1,
				);
			} else if (
				t.isUpdateExpression(node) && t.isIdentifier(node.argument)
			) {
				assignmentCounts.set(
					node.argument.name,
					(assignmentCounts.get(node.argument.name) ?? 0) + 1,
				);
			}
		});
		if (t.isVariableDeclaration(statement)) {
			for (const declaration of statement.declarations) {
				if (t.isIdentifier(declaration.id)) {
					declarationIndexes.set(declaration.id.name, index);
				}
			}
		}
	}
	const initializers = new Map<
		string,
		{ temp: string; init: t.Expression }
	>();
	for (const [index, statement] of statements.entries()) {
		if (t.isVariableDeclaration(statement)) {
			for (const declaration of statement.declarations) {
				if (!t.isIdentifier(declaration.id)) continue;
				if (declaration.init == null && statement.kind === 'let') {
					uninitializedLets.set(declaration.id.name, index);
				} else if (
					declaration.init &&
					t.isExpression(declaration.init) &&
					isPureCondition(declaration.init)
				) {
					declarations.set(declaration.id.name, declaration.init);
				}
			}
			continue;
		}
		const assignment = simpleIdentifierAssignment(statement);
		if (!assignment) continue;
		const declarationIndex = uninitializedLets.get(assignment.target);
		if (declarationIndex == null) continue;
		if (assignmentCounts.get(assignment.target) !== 1) continue;
		if (!t.isIdentifier(assignment.value)) continue;
		// The source declaration can only disappear when this copy is its sole
		// use. Count identifiers structurally because statement-list rewrites do
		// not have Babel scopes, and nested loop/guard Phi copies are still uses.
		if (identifierCounts.get(assignment.value.name) !== 2) continue;
		const initializer = declarations.get(assignment.value.name);
		if (!initializer) continue;
		let movesBindingBeforeDeclaration = false;
		t.traverseFast(initializer, (node) => {
			if (!t.isIdentifier(node)) return;
			const dependencyIndex = declarationIndexes.get(node.name);
			if (
				dependencyIndex != null && dependencyIndex >= declarationIndex
			) movesBindingBeforeDeclaration = true;
		});
		if (movesBindingBeforeDeclaration) continue;
		initializers.set(assignment.target, {
			temp: assignment.value.name,
			init: initializer,
		});
	}
	return initializers;
}

function simplifyPhiInitializerStatement(
	statement: t.Statement,
	initializers: Map<string, { temp: string; init: t.Expression }>,
): t.Statement[] {
	const assignment = simpleIdentifierAssignment(statement);
	if (assignment && initializers.has(assignment.target)) return [];
	if (t.isVariableDeclaration(statement)) {
		const sourceTemps = new Set(
			[...initializers.values()].map((initializer) => initializer.temp),
		);
		const declarations = statement.declarations.flatMap((declaration) => {
			if (
				t.isIdentifier(declaration.id) &&
				sourceTemps.has(declaration.id.name)
			) {
				return [];
			}
			if (
				t.isIdentifier(declaration.id) &&
				declaration.init == null &&
				initializers.has(declaration.id.name)
			) {
				return [t.variableDeclarator(
					t.cloneNode(declaration.id),
					t.cloneNode(
						initializers.get(declaration.id.name)!.init,
						true,
					),
				)];
			}
			return [declaration];
		});
		return declarations.length === 0
			? []
			: [rebuiltVariableDeclaration(statement, declarations)];
	}
	return [statement];
}

function simpleIdentifierAssignment(
	statement: t.Statement,
): { target: string; value: t.Expression } | null {
	if (!t.isExpressionStatement(statement)) return null;
	const expression = statement.expression;
	if (!t.isAssignmentExpression(expression, { operator: '=' })) return null;
	if (!t.isIdentifier(expression.left)) return null;
	if (!t.isExpression(expression.right)) return null;
	return {
		target: expression.left.name,
		value: expression.right,
	};
}

function simplifyPostfixIndexUpdates(statements: t.Statement[]): t.Statement[] {
	return simplifyPostfixIndexUpdatesInStatements(
		statements,
		collectNumericOneConstants(statements),
	);
}

function simplifyPostfixIndexUpdatesInStatements(
	statements: t.Statement[],
	numericOnes: ReadonlySet<string>,
): t.Statement[] {
	const rewritten: t.Statement[] = [];
	for (let index = 0; index < statements.length; index++) {
		const first = statements[index];
		const second = statements[index + 1];
		const third = statements[index + 2];
		const fourth = statements[index + 3];
		const fifth = statements[index + 4];
		const sixth = statements[index + 5];
		const foldedWithObjectAlias = second && third && fourth && fifth
			? foldPostfixIndexUpdateWithObjectAlias(
				first,
				second,
				third,
				fourth,
				fifth,
				sixth,
				numericOnes,
			)
			: null;
		if (foldedWithObjectAlias) {
			rewritten.push(foldedWithObjectAlias.statement);
			index += foldedWithObjectAlias.consumed - 1;
			continue;
		}
		const folded = second && third
			? foldPostfixIndexUpdate(first, second, third, fourth, numericOnes)
			: null;
		if (folded) {
			rewritten.push(folded.statement);
			index += folded.consumed - 1;
			continue;
		}
		rewritten.push(
			simplifyPostfixIndexUpdatesInStatement(first, numericOnes),
		);
	}
	return rewritten;
}

function simplifyPostfixIndexUpdatesInStatement(
	statement: t.Statement,
	numericOnes: ReadonlySet<string>,
): t.Statement {
	if (t.isBlockStatement(statement)) {
		const cloned = t.cloneNode(statement, true);
		cloned.body = simplifyPostfixIndexUpdatesInStatements(
			cloned.body,
			numericOnes,
		);
		return cloned;
	}
	if (t.isIfStatement(statement)) {
		const cloned = t.cloneNode(statement, true);
		cloned.consequent = simplifyPostfixIndexUpdatesInBranch(
			cloned.consequent,
			numericOnes,
		);
		if (cloned.alternate) {
			cloned.alternate = simplifyPostfixIndexUpdatesInBranch(
				cloned.alternate,
				numericOnes,
			);
		}
		return cloned;
	}
	if (t.isTryStatement(statement)) {
		const cloned = t.cloneNode(statement, true);
		cloned.block.body = simplifyPostfixIndexUpdatesInStatements(
			cloned.block.body,
			numericOnes,
		);
		if (cloned.handler) {
			cloned.handler.body.body = simplifyPostfixIndexUpdatesInStatements(
				cloned.handler.body.body,
				numericOnes,
			);
		}
		if (cloned.finalizer) {
			cloned.finalizer.body = simplifyPostfixIndexUpdatesInStatements(
				cloned.finalizer.body,
				numericOnes,
			);
		}
		return cloned;
	}
	if (
		t.isWhileStatement(statement) ||
		t.isForStatement(statement) ||
		t.isForOfStatement(statement) ||
		t.isForInStatement(statement)
	) {
		const cloned = t.cloneNode(statement, true);
		if (t.isBlockStatement(cloned.body)) {
			cloned.body.body = simplifyPostfixIndexUpdatesInStatements(
				cloned.body.body,
				numericOnes,
			);
		}
		return cloned;
	}
	return statement;
}

function simplifyPostfixIndexUpdatesInBranch(
	statement: t.Statement,
	numericOnes: ReadonlySet<string>,
): t.Statement {
	return simplifyPostfixIndexUpdatesInStatement(statement, numericOnes);
}

function foldPostfixIndexUpdate(
	first: t.Statement,
	second: t.Statement,
	third: t.Statement,
	fourth: t.Statement | undefined,
	numericOnes: ReadonlySet<string>,
): { statement: t.Statement; consumed: number } | null {
	const alias = singleIdentifierDeclaration(first);
	if (!alias) return null;
	const update = simpleIncrementDeclaration(
		second,
		alias.name,
		alias.value.name,
		numericOnes,
	) ??
		toNumericIncrementPair(first, second, numericOnes);
	if (!update) return null;
	const assignment = memberAssignmentUsingIndex(third, update.indexName);
	if (!assignment) return null;
	const consumed = isAssignmentToIdentifier(
			fourth,
			update.counterName,
			update.nextName,
		)
		? 4
		: 3;
	return {
		statement: t.expressionStatement(
			t.assignmentExpression(
				'=',
				t.memberExpression(
					t.cloneNode(assignment.object, true),
					t.updateExpression(
						'++',
						t.identifier(update.counterName),
						false,
					),
					true,
				),
				t.cloneNode(assignment.value, true),
			),
		),
		consumed,
	};
}

function foldPostfixIndexUpdateWithObjectAlias(
	first: t.Statement,
	second: t.Statement,
	third: t.Statement,
	fourth: t.Statement,
	fifth: t.Statement,
	sixth: t.Statement | undefined,
	numericOnes: ReadonlySet<string>,
): { statement: t.Statement; consumed: number } | null {
	const objectAlias = singleIdentifierDeclaration(first);
	const indexAlias = singleIdentifierDeclaration(second);
	if (!objectAlias || !indexAlias) return null;
	const update = toNumericIncrementPair(third, fourth, numericOnes);
	if (!update || update.counterName !== indexAlias.name) return null;
	const counterName = indexAlias.value.name;
	const assignment = memberAssignmentUsingIndex(fifth, update.indexName);
	if (!assignment) return null;
	if (
		!t.isIdentifier(assignment.object, {
			name: objectAlias.name,
		})
	) return null;
	const consumed = isAssignmentToIdentifier(
			sixth,
			counterName,
			update.nextName,
		)
		? 6
		: 5;
	return {
		statement: t.expressionStatement(
			t.assignmentExpression(
				'=',
				t.memberExpression(
					t.cloneNode(objectAlias.value, true),
					t.updateExpression(
						'++',
						t.identifier(counterName),
						false,
					),
					true,
				),
				t.cloneNode(assignment.value, true),
			),
		),
		consumed,
	};
}

function singleIdentifierDeclaration(
	statement: t.Statement,
): { name: string; value: t.Identifier } | null {
	if (
		!t.isVariableDeclaration(statement) ||
		statement.declarations.length !== 1
	) {
		return null;
	}
	const [declaration] = statement.declarations;
	if (!t.isIdentifier(declaration.id) || !t.isIdentifier(declaration.init)) {
		return null;
	}
	return { name: declaration.id.name, value: declaration.init };
}

function simpleIncrementDeclaration(
	statement: t.Statement,
	indexName: string,
	counterName: string,
	numericOnes: ReadonlySet<string>,
): { counterName: string; indexName: string; nextName: string } | null {
	if (
		!t.isVariableDeclaration(statement) ||
		statement.declarations.length !== 1
	) {
		return null;
	}
	const [declaration] = statement.declarations;
	if (!t.isIdentifier(declaration.id)) return null;
	if (!t.isBinaryExpression(declaration.init, { operator: '+' })) return null;
	if (!t.isIdentifier(declaration.init.left, { name: indexName })) {
		return null;
	}
	if (!isNumericOneExpression(declaration.init.right, numericOnes)) {
		return null;
	}
	return { counterName, indexName, nextName: declaration.id.name };
}

function toNumericIncrementPair(
	first: t.Statement,
	second: t.Statement,
	numericOnes: ReadonlySet<string>,
): { counterName: string; indexName: string; nextName: string } | null {
	if (!t.isVariableDeclaration(first) || first.declarations.length !== 1) {
		return null;
	}
	if (!t.isVariableDeclaration(second) || second.declarations.length !== 1) {
		return null;
	}
	const [numericDeclaration] = first.declarations;
	const [incrementDeclaration] = second.declarations;
	if (!t.isIdentifier(numericDeclaration.id)) return null;
	if (!t.isCallExpression(numericDeclaration.init)) return null;
	if (
		!t.isV8IntrinsicIdentifier(numericDeclaration.init.callee, {
			name: 'ToNumeric',
		})
	) return null;
	const [argument] = numericDeclaration.init.arguments;
	if (!t.isIdentifier(argument)) return null;
	if (!t.isIdentifier(incrementDeclaration.id)) return null;
	if (!t.isBinaryExpression(incrementDeclaration.init, { operator: '+' })) {
		return null;
	}
	if (
		!t.isIdentifier(incrementDeclaration.init.left, {
			name: numericDeclaration.id.name,
		})
	) return null;
	if (!isNumericOneExpression(incrementDeclaration.init.right, numericOnes)) {
		return null;
	}
	return {
		counterName: argument.name,
		indexName: numericDeclaration.id.name,
		nextName: incrementDeclaration.id.name,
	};
}

function isAssignmentToIdentifier(
	statement: t.Statement | undefined,
	targetName: string,
	valueName: string,
): boolean {
	if (!statement || !t.isExpressionStatement(statement)) return false;
	const expression = statement.expression;
	return t.isAssignmentExpression(expression, { operator: '=' }) &&
		t.isIdentifier(expression.left, { name: targetName }) &&
		t.isIdentifier(expression.right, { name: valueName });
}

function isNumericOneExpression(
	expression: t.Expression,
	numericOnes: ReadonlySet<string>,
): boolean {
	return t.isNumericLiteral(expression, { value: 1 }) ||
		(t.isIdentifier(expression) && numericOnes.has(expression.name));
}

function collectNumericOneConstants(
	statements: readonly t.Statement[],
): Set<string> {
	const names = new Set<string>();
	for (const statement of statements) {
		if (!t.isVariableDeclaration(statement, { kind: 'const' })) continue;
		for (const declaration of statement.declarations) {
			if (
				t.isIdentifier(declaration.id) &&
				t.isNumericLiteral(declaration.init, { value: 1 })
			) {
				names.add(declaration.id.name);
			}
		}
	}
	return names;
}

function memberAssignmentUsingIndex(
	statement: t.Statement,
	indexName: string,
): { object: t.Expression; value: t.Expression } | null {
	if (!t.isExpressionStatement(statement)) return null;
	const expression = statement.expression;
	if (!t.isAssignmentExpression(expression, { operator: '=' })) return null;
	if (!t.isMemberExpression(expression.left) || !expression.left.computed) {
		return null;
	}
	if (!t.isExpression(expression.left.object)) return null;
	if (!t.isIdentifier(expression.left.property, { name: indexName })) {
		return null;
	}
	if (!t.isExpression(expression.right)) return null;
	return {
		object: expression.left.object,
		value: expression.right,
	};
}

function removeWriteOnlyIdentifierStatements(
	statements: t.Statement[],
): t.Statement[] {
	const usage = collectIdentifierUsage(t.program(statements));
	// Only remove identifiers declared within THIS scope. An identifier assigned here
	// but declared in an enclosing scope (e.g. a phi target `let r4_3` hoisted to the
	// function body, then assigned inside an `if` arm) looks write-only locally but is
	// read elsewhere — removing its assignment here would strand the outer read.
	const { declared, declaredGlobals } = collectDeclaredIdentifiers(
		statements,
	);
	// A `var x;` lifted from `DeclareGlobalVar` declares a global, and is never
	// dead: its reads and writes go through `global.x` member accesses, which
	// this usage walk does not attribute to `x` at all, and whole-file
	// composition needs the declarator's provenance to unqualify them again.
	// Removing it emitted `global.x = …` where the source wrote `var x = …`.
	const writeOnly = new Set(
		[...usage.writes].filter((name) =>
			!usage.reads.has(name) && declared.has(name) &&
			!declaredGlobals.has(name)
		),
	);
	if (writeOnly.size === 0) return statements;
	return statements.flatMap((statement) =>
		removeWriteOnlyIdentifierStatement(statement, writeOnly)
	);
}

// Identifiers declared (let/const/var) directly in `statements`, excluding any nested
// function bodies (which are separate scopes with their own declarations).
// `declaredGlobals` is the subset declared by `DeclareGlobalVar`.
function collectDeclaredIdentifiers(
	statements: readonly t.Statement[],
): { declared: Set<string>; declaredGlobals: Set<string> } {
	const declared = new Set<string>();
	const declaredGlobals = new Set<string>();
	const visit = (node: t.Node | null | undefined) => {
		if (!node) return;
		if (
			t.isFunctionDeclaration(node) || t.isFunctionExpression(node) ||
			t.isArrowFunctionExpression(node) || t.isObjectMethod(node) ||
			t.isClassMethod(node)
		) return;
		if (t.isVariableDeclarator(node)) {
			collectPatternWrites(node.id, declared);
			if (node.extra?.isDeclaredGlobal) {
				collectPatternWrites(node.id, declaredGlobals);
			}
			visit(node.init);
			return;
		}
		const visitorKeys = (t as unknown as {
			VISITOR_KEYS: Record<string, string[] | undefined>;
		}).VISITOR_KEYS[node.type] ?? [];
		for (const key of visitorKeys) {
			const value = (node as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const child of value) {
					if (t.isNode(child)) visit(child);
				}
			} else if (t.isNode(value)) {
				visit(value);
			}
		}
	};
	for (const statement of statements) visit(statement);
	return { declared, declaredGlobals };
}

function collectIdentifierUsage(node: t.Node): {
	reads: Set<string>;
	writes: Set<string>;
} {
	const reads = new Set<string>();
	const writes = new Set<string>();
	collectIdentifierUsageFromNode(node, reads, writes);
	return { reads, writes };
}

function collectIdentifierUsageFromNode(
	node: t.Node | null | undefined,
	reads: Set<string>,
	writes: Set<string>,
) {
	if (!node) return;
	if (t.isIdentifier(node)) {
		reads.add(node.name);
		return;
	}
	if (t.isVariableDeclarator(node)) {
		collectPatternWrites(node.id, writes);
		collectIdentifierUsageFromNode(node.init, reads, writes);
		return;
	}
	if (t.isAssignmentExpression(node)) {
		collectAssignmentTargetUsage(node.left, reads, writes);
		collectIdentifierUsageFromNode(node.right, reads, writes);
		return;
	}
	if (t.isUpdateExpression(node)) {
		if (t.isIdentifier(node.argument)) {
			reads.add(node.argument.name);
			writes.add(node.argument.name);
			return;
		}
		collectAssignmentTargetUsage(node.argument, reads, writes);
		return;
	}
	if (t.isFunctionDeclaration(node) || t.isFunctionExpression(node)) {
		if (node.id) writes.add(node.id.name);
		return;
	}
	const visitorKeys = (t as unknown as {
		VISITOR_KEYS: Record<string, string[] | undefined>;
	}).VISITOR_KEYS[node.type] ?? [];
	for (const key of visitorKeys) {
		const value = (node as unknown as Record<string, unknown>)[key];
		if (Array.isArray(value)) {
			for (const child of value) {
				if (t.isNode(child)) {
					collectIdentifierUsageFromNode(child, reads, writes);
				}
			}
		} else if (t.isNode(value)) {
			collectIdentifierUsageFromNode(value, reads, writes);
		}
	}
}

function collectPatternWrites(
	pattern: t.Node | null | undefined,
	writes: Set<string>,
) {
	if (t.isIdentifier(pattern)) {
		writes.add(pattern.name);
		return;
	}
	if (t.isRestElement(pattern)) {
		collectPatternWrites(pattern.argument, writes);
		return;
	}
	if (t.isAssignmentPattern(pattern)) {
		collectPatternWrites(pattern.left, writes);
		return;
	}
	if (t.isArrayPattern(pattern)) {
		for (const element of pattern.elements) {
			if (element) collectPatternWrites(element, writes);
		}
		return;
	}
	if (t.isObjectPattern(pattern)) {
		for (const property of pattern.properties) {
			if (t.isRestElement(property)) {
				collectPatternWrites(property.argument, writes);
			} else {
				collectPatternWrites(property.value, writes);
			}
		}
	}
}

function collectAssignmentTargetUsage(
	target: t.Node,
	reads: Set<string>,
	writes: Set<string>,
) {
	if (t.isIdentifier(target)) {
		writes.add(target.name);
		return;
	}
	if (t.isMemberExpression(target)) {
		collectIdentifierUsageFromNode(target.object, reads, writes);
		if (target.computed) {
			collectIdentifierUsageFromNode(target.property, reads, writes);
		}
		return;
	}
	if (t.isOptionalMemberExpression(target)) {
		collectIdentifierUsageFromNode(target.object, reads, writes);
		if (target.computed) {
			collectIdentifierUsageFromNode(target.property, reads, writes);
		}
		return;
	}
	if (
		t.isArrayPattern(target) ||
		t.isObjectPattern(target) ||
		t.isRestElement(target) ||
		t.isAssignmentPattern(target)
	) {
		collectPatternWrites(target, writes);
		return;
	}
	collectIdentifierUsageFromNode(target, reads, writes);
}

function removeWriteOnlyIdentifierStatement(
	statement: t.Statement,
	writeOnly: ReadonlySet<string>,
): t.Statement[] {
	// Every branch below rebuilds the child lists it is about to replace, so the
	// copies are shallow and untouched subtrees are shared. A deep copy here is
	// re-made at each level of the recursion, which costs a copy of the whole
	// subtree per node rather than one per rewrite.
	const shallow = <T extends t.Node>(node: T): T => t.cloneNode(node, false);
	if (
		t.isExpressionStatement(statement) &&
		t.isAssignmentExpression(statement.expression, { operator: '=' }) &&
		t.isIdentifier(statement.expression.left) &&
		writeOnly.has(statement.expression.left.name) &&
		isPureCondition(statement.expression.right)
	) {
		return [];
	}
	if (t.isVariableDeclaration(statement)) {
		const declarations = statement.declarations.filter((declaration) =>
			!(
				t.isIdentifier(declaration.id) &&
				writeOnly.has(declaration.id.name) &&
				declaration.init == null
			)
		);
		return declarations.length === 0
			? []
			: [rebuiltVariableDeclaration(statement, declarations)];
	}
	if (t.isBlockStatement(statement)) {
		const cloned = shallow(statement);
		cloned.body = statement.body.flatMap((child) =>
			removeWriteOnlyIdentifierStatement(child, writeOnly)
		);
		return [cloned];
	}
	if (t.isLabeledStatement(statement)) {
		const cloned = shallow(statement);
		cloned.body = removeWriteOnlyIdentifierBranch(
			statement.body,
			writeOnly,
		);
		return [cloned];
	}
	if (t.isIfStatement(statement)) {
		const cloned = shallow(statement);
		cloned.consequent = removeWriteOnlyIdentifierBranch(
			statement.consequent,
			writeOnly,
		);
		if (statement.alternate) {
			cloned.alternate = removeWriteOnlyIdentifierBranch(
				statement.alternate,
				writeOnly,
			);
			flattenElseIfBlock(cloned);
		}
		return [cloned];
	}
	if (t.isTryStatement(statement)) {
		const cloned = shallow(statement);
		cloned.block = shallow(statement.block);
		cloned.block.body = statement.block.body.flatMap((child) =>
			removeWriteOnlyIdentifierStatement(child, writeOnly)
		);
		if (statement.handler) {
			const handler = shallow(statement.handler);
			handler.body = shallow(statement.handler.body);
			handler.body.body = statement.handler.body.body.flatMap((child) =>
				removeWriteOnlyIdentifierStatement(child, writeOnly)
			);
			cloned.handler = handler;
		}
		if (statement.finalizer) {
			cloned.finalizer = shallow(statement.finalizer);
			cloned.finalizer.body = statement.finalizer.body.flatMap((child) =>
				removeWriteOnlyIdentifierStatement(child, writeOnly)
			);
		}
		return [cloned];
	}
	if (
		t.isWhileStatement(statement) ||
		t.isForStatement(statement) ||
		t.isForOfStatement(statement) ||
		t.isForInStatement(statement)
	) {
		const cloned = shallow(statement);
		if (t.isBlockStatement(statement.body)) {
			const body = shallow(statement.body);
			body.body = statement.body.body.flatMap((child) =>
				removeWriteOnlyIdentifierStatement(child, writeOnly)
			);
			cloned.body = body;
		}
		return [cloned];
	}
	return [statement];
}

function removeWriteOnlyIdentifierBranch(
	statement: t.Statement,
	writeOnly: ReadonlySet<string>,
): t.Statement {
	const statements = removeWriteOnlyIdentifierStatement(statement, writeOnly);
	return statements.length === 1
		? statements[0]
		: t.blockStatement(statements);
}

function simplifyEmptyIfStatements(
	statements: t.Statement[],
): t.Statement[] {
	return statements.flatMap((stmt) => simplifyEmptyIfStatement(stmt));
}

function simplifyEmptyIfStatement(stmt: t.Statement): t.Statement[] {
	// As in `removeWriteOnlyIdentifierStatement`: each case replaces the child
	// lists it recurses into, so the copies are shallow and untouched subtrees
	// are shared. `simplifyIfBranch`, `flattenNestedGuard` and
	// `collapseNestedTryCatchFinally` all build new nodes rather than mutating
	// their argument, so nothing shared is written through.
	const shallow = <T extends t.Node>(node: T): T => t.cloneNode(node, false);
	if (t.isBlockStatement(stmt)) {
		const cloned = shallow(stmt);
		cloned.body = simplifyEmittedStatements(stmt.body, false);
		return [cloned];
	}
	if (t.isTryStatement(stmt)) {
		const cloned = shallow(stmt);
		cloned.block = shallow(stmt.block);
		cloned.block.body = simplifyEmittedStatements(stmt.block.body, false);
		if (stmt.handler) {
			const handler = shallow(stmt.handler);
			handler.body = shallow(stmt.handler.body);
			handler.body.body = simplifyEmittedStatements(
				stmt.handler.body.body,
				false,
			);
			cloned.handler = handler;
		}
		if (stmt.finalizer) {
			cloned.finalizer = shallow(stmt.finalizer);
			cloned.finalizer.body = simplifyEmittedStatements(
				stmt.finalizer.body,
				false,
			);
		}
		return [collapseNestedTryCatchFinally(cloned)];
	}
	if (t.isLabeledStatement(stmt) && t.isBlockStatement(stmt.body)) {
		const cloned = shallow(stmt);
		const body = shallow(stmt.body);
		body.body = simplifyEmittedStatements(stmt.body.body, false);
		cloned.body = body;
		return [cloned];
	}
	if (
		t.isWhileStatement(stmt) || t.isDoWhileStatement(stmt) ||
		t.isForStatement(stmt) || t.isForOfStatement(stmt) ||
		t.isForInStatement(stmt)
	) {
		const cloned = shallow(stmt);
		if (t.isBlockStatement(stmt.body)) {
			const body = shallow(stmt.body);
			body.body = simplifyEmittedStatements(stmt.body.body, false);
			cloned.body = body;
		}
		return [cloned];
	}
	if (t.isSwitchStatement(stmt)) {
		const cloned = shallow(stmt);
		cloned.cases = stmt.cases.map((switchCase) => {
			const clonedCase = shallow(switchCase);
			clonedCase.consequent = simplifyEmittedStatements(
				switchCase.consequent,
				false,
			);
			return clonedCase;
		});
		return [cloned];
	}
	if (!t.isIfStatement(stmt)) return [stmt];

	const cloned = shallow(stmt);
	cloned.consequent = simplifyIfBranch(stmt.consequent);
	if (stmt.alternate) {
		cloned.alternate = simplifyIfBranch(stmt.alternate);
		flattenElseIfBlock(cloned);
	}
	if (
		cloned.alternate != null &&
		isEmptyStatementBranch(cloned.alternate)
	) {
		cloned.alternate = null;
	}
	const rotatedGuard = rotateTerminatingGuardIntoElseIf(cloned);
	if (rotatedGuard) return simplifyEmptyIfStatement(rotatedGuard);
	const flattened = flattenNestedGuard(cloned);
	if (flattened !== cloned) return simplifyEmptyIfStatement(flattened);

	const consequentEmpty = isEmptyStatementBranch(cloned.consequent);
	const alternateEmpty = cloned.alternate == null ||
		isEmptyStatementBranch(cloned.alternate);
	if (consequentEmpty && alternateEmpty) {
		return isPureCondition(cloned.test)
			? []
			: [t.expressionStatement(t.cloneNode(cloned.test, true))];
	}
	if (consequentEmpty && cloned.alternate) {
		return [
			t.ifStatement(
				invertTest(cloned.test),
				ensureStatementBlock(cloned.alternate),
			),
		];
	}
	if (alternateEmpty) {
		cloned.alternate = null;
	}
	return [cloned];
}

function collapseNestedTryCatchFinally(
	stmt: t.TryStatement,
): t.TryStatement {
	if (stmt.handler || !stmt.finalizer) return stmt;
	if (stmt.block.body.length !== 1) return stmt;
	const [inner] = stmt.block.body;
	if (!t.isTryStatement(inner)) return stmt;
	if (!inner.handler || inner.finalizer) return stmt;
	return t.tryStatement(
		t.cloneNode(inner.block, true),
		t.cloneNode(inner.handler, true),
		t.cloneNode(stmt.finalizer, true),
	);
}

function flattenNestedGuard(stmt: t.IfStatement): t.IfStatement {
	if (stmt.alternate != null) return stmt;
	const nested = singleNestedIf(stmt.consequent);
	if (!nested || nested.alternate != null) return stmt;
	return t.ifStatement(
		t.logicalExpression(
			'&&',
			t.cloneNode(stmt.test, true),
			t.cloneNode(nested.test, true),
		),
		t.cloneNode(nested.consequent, true),
	);
}

function flattenNestedGuardStatements(
	statements: t.Statement[],
): t.Statement[] {
	// Shallow copies with shared subtrees, as everywhere else in this file: each
	// case replaces the child list it recurses into.
	const shallow = <T extends t.Node>(node: T): T => t.cloneNode(node, false);
	return statements.map((stmt) => {
		if (t.isIfStatement(stmt)) return flattenNestedGuard(stmt);
		if (t.isBlockStatement(stmt)) {
			const cloned = shallow(stmt);
			cloned.body = flattenNestedGuardStatements(stmt.body);
			return cloned;
		}
		// A labelled block is still a block. Skipping it left every guard inside
		// a surviving label unflattened.
		if (t.isLabeledStatement(stmt) && t.isBlockStatement(stmt.body)) {
			const cloned = shallow(stmt);
			const body = shallow(stmt.body);
			body.body = flattenNestedGuardStatements(stmt.body.body);
			cloned.body = body;
			return cloned;
		}
		if (t.isTryStatement(stmt)) {
			const cloned = shallow(stmt);
			cloned.block = shallow(stmt.block);
			cloned.block.body = flattenNestedGuardStatements(stmt.block.body);
			if (stmt.handler) {
				const handler = shallow(stmt.handler);
				handler.body = shallow(stmt.handler.body);
				handler.body.body = flattenNestedGuardStatements(
					stmt.handler.body.body,
				);
				cloned.handler = handler;
			}
			if (stmt.finalizer) {
				cloned.finalizer = shallow(stmt.finalizer);
				cloned.finalizer.body = flattenNestedGuardStatements(
					stmt.finalizer.body,
				);
			}
			return cloned;
		}
		if (
			t.isWhileStatement(stmt) || t.isForStatement(stmt) ||
			t.isForOfStatement(stmt) || t.isForInStatement(stmt)
		) {
			const cloned = shallow(stmt);
			if (t.isBlockStatement(stmt.body)) {
				const body = shallow(stmt.body);
				body.body = flattenNestedGuardStatements(stmt.body.body);
				cloned.body = body;
			}
			return cloned;
		}
		return stmt;
	});
}

function simplifyIfBranch(stmt: t.Statement): t.Statement {
	const simplified = simplifyEmptyIfStatement(stmt);
	if (simplified.length === 1) return simplified[0];
	return t.blockStatement(simplified);
}

function isEmptyStatementBranch(stmt: t.Statement): boolean {
	return t.isEmptyStatement(stmt) ||
		(t.isBlockStatement(stmt) && stmt.body.length === 0);
}

function ensureStatementBlock(stmt: t.Statement): t.Statement {
	return t.isBlockStatement(stmt) ? stmt : t.blockStatement([stmt]);
}

function isPureCondition(expr: t.Expression): boolean {
	if (
		t.isIdentifier(expr) ||
		t.isBooleanLiteral(expr) ||
		t.isNumericLiteral(expr) ||
		t.isStringLiteral(expr) ||
		t.isNullLiteral(expr)
	) return true;
	if (t.isUnaryExpression(expr)) {
		return t.isExpression(expr.argument) && isPureCondition(expr.argument);
	}
	if (t.isBinaryExpression(expr) || t.isLogicalExpression(expr)) {
		return t.isExpression(expr.left) && isPureCondition(expr.left) &&
			isPureCondition(expr.right);
	}
	return false;
}

function mergeAdjacentIfsWithSameBody(
	statements: t.Statement[],
): t.Statement[] {
	const merged: t.Statement[] = [];
	for (const current of statements) {
		const previous = merged.at(-1);
		if (
			previous &&
			t.isIfStatement(previous) &&
			t.isIfStatement(current) &&
			previous.alternate == null &&
			current.alternate == null &&
			redundantNestedGuard(previous, current)
		) {
			merged[merged.length - 1] = current;
			continue;
		}
		if (
			previous &&
			t.isIfStatement(previous) &&
			t.isIfStatement(current) &&
			previous.alternate == null &&
			current.alternate == null &&
			statementBodyKey(previous.consequent) ===
				statementBodyKey(current.consequent)
		) {
			previous.test = t.logicalExpression(
				'||',
				t.cloneNode(previous.test, true),
				t.cloneNode(current.test, true),
			);
			continue;
		}
		merged.push(current);
	}
	return merged;
}

function redundantNestedGuard(
	previous: t.IfStatement,
	current: t.IfStatement,
): boolean {
	if (generate(previous.test).code !== generate(current.test).code) {
		return false;
	}
	const nested = singleNestedIf(previous.consequent);
	if (!nested || nested.alternate) return false;
	return statementBodyKey(nested.consequent) ===
		statementBodyKey(current.consequent);
}

function singleNestedIf(stmt: t.Statement): t.IfStatement | null {
	if (t.isIfStatement(stmt)) return stmt;
	if (!t.isBlockStatement(stmt) || stmt.body.length !== 1) return null;
	const [only] = stmt.body;
	return t.isIfStatement(only) ? only : null;
}

function statementBodyKey(stmt: t.Statement): string {
	return generate(ensureStatementBlock(stmt)).code;
}

function classifyLoopHeaderTarget(
	target: number,
	region: Extract<Region, { kind: 'loop' }>,
): 'continue' | 'body' | 'break' {
	if (target === region.header) return 'continue';
	if (region.loopBlocks.has(target)) return 'body';
	return 'break';
}

function emitIteratorLoopExitContinuation(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
	diagnostics: string[],
): t.Statement[] {
	const ordinaryExits = region.exits.filter((exit) =>
		isIteratorHeaderCompletionExit(exit, region.header)
	);
	const exits = new Set(
		ordinaryExits
			.map((exit) => normalizeIteratorLoopExit(exit.to, region, cfg)),
	);
	if (exits.size !== 1) return [];
	const [exit] = exits;
	if (
		[...(cfg.normalPredecessors.get(exit) ?? [])].some((predecessor) =>
			!region.loopBlocks.has(predecessor)
		)
	) return [];
	return emitBlockStatements(
		exit,
		cfg,
		phiState,
		diagnostics,
		true,
		ordinaryExits.some((candidate) =>
			candidate.kind === 'return' || candidate.kind === 'throw'
		),
	);
}

function normalizeIteratorLoopExit(
	exit: number,
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
): number {
	let current = exit;
	const seen = new Set<number>();
	while (!seen.has(current) && !region.loopBlocks.has(current)) {
		seen.add(current);
		const block = cfg.blocks.get(current);
		if (!block || !blockContainsIntrinsic(block.body, 'IteratorClose')) {
			break;
		}
		const successors = [...(cfg.normalSuccessors.get(current) ?? [])];
		if (successors.length !== 1) break;
		[current] = successors;
	}
	return current;
}

function blockContainsIntrinsic(
	statements: readonly t.Statement[],
	name: string,
): boolean {
	for (const stmt of statements) {
		let found = false;
		t.traverseFast(stmt, (node) => {
			if (found) return t.traverseFast.skip;
			if (
				t.isCallExpression(node) &&
				t.isV8IntrinsicIdentifier(node.callee, { name })
			) {
				found = true;
			}
		});
		if (found) return true;
	}
	return false;
}

/**
 * Remove the machine's explicit iterator close from a recovered loop body.
 *
 * `for...of` and `for...in` close their iterator on every abrupt completion, so
 * a lowered `%IteratorClose` on the register the syntax subsumed is redundant.
 * The machine reaches that register through copies, and those copies become
 * dead — and unbound, since nothing declares the iterator any more — once the
 * close is gone, so both are dropped together.
 */
function stripSubsumedIteratorCloses(
	statements: t.Statement[],
	syntax: NonNullable<Extract<Region, { kind: 'loop' }>['syntax']>,
): t.Statement[] {
	// The machine keeps its iterator in one register and hands later versions of
	// it to the close, so ownership is by register rather than by SSA version.
	const machine = new Set(
		(syntax.machineValues ?? []).flatMap((value) => {
			const match = /^r(\d+)_\d+$/.exec(value.name);
			return match ? [match[1]!] : [];
		}),
	);
	if (machine.size === 0) return statements;
	const copyOf = new Map<string, string>();
	t.traverseFast(t.blockStatement(statements), (node) => {
		if (
			t.isVariableDeclarator(node) && t.isIdentifier(node.id) &&
			t.isIdentifier(node.init)
		) copyOf.set(node.id.name, node.init.name);
		if (
			t.isAssignmentExpression(node, { operator: '=' }) &&
			t.isIdentifier(node.left) && t.isIdentifier(node.right)
		) copyOf.set(node.left.name, node.right.name);
	});
	const holdsMachineValue = (name: string) => {
		const seen = new Set<string>();
		let current: string | undefined = name;
		while (current != null && !seen.has(current)) {
			const match = /^r(\d+)_\d+$/.exec(current);
			if (match && machine.has(match[1]!)) return true;
			seen.add(current);
			current = copyOf.get(current);
		}
		return false;
	};
	const isSubsumedClose = (statement: t.Statement) => {
		if (
			!statementContainsOnlyIntrinsicCall(statement, 'IteratorClose') ||
			!t.isExpressionStatement(statement) ||
			!t.isCallExpression(statement.expression)
		) return false;
		const [iterator] = statement.expression.arguments;
		return t.isIdentifier(iterator) && holdsMachineValue(iterator.name);
	};
	let result = rewriteStatementList(statements, isSubsumedClose);
	// Copies of the iterator survive only to feed those closes. Drop each one
	// whose value is no longer read anywhere.
	for (let pass = 0; pass < 2; pass++) {
		const referenced = new Map<string, number>();
		t.traverseFast(t.blockStatement(result), (node) => {
			if (!t.isIdentifier(node)) return;
			referenced.set(node.name, (referenced.get(node.name) ?? 0) + 1);
		});
		const deadCopy = (statement: t.Statement) => {
			const [name, initializer] = copyDeclaration(statement) ?? [];
			return name != null && initializer != null &&
				holdsMachineValue(initializer) &&
				(referenced.get(name) ?? 0) <= 1;
		};
		const stripped = rewriteStatementList(result, deadCopy);
		if (stripped.length === result.length) {
			const before = generate(t.blockStatement(result)).code;
			const after = generate(t.blockStatement(stripped)).code;
			result = stripped;
			if (before === after) break;
			continue;
		}
		result = stripped;
	}
	return result;
}

/** `const a = b;` or `a = b;` between two identifiers. */
function copyDeclaration(
	statement: t.Statement,
): [string, string] | null {
	if (
		t.isVariableDeclaration(statement) &&
		statement.declarations.length === 1
	) {
		const [declaration] = statement.declarations;
		return t.isIdentifier(declaration.id) &&
				t.isIdentifier(declaration.init)
			? [declaration.id.name, declaration.init.name]
			: null;
	}
	if (
		t.isExpressionStatement(statement) &&
		t.isAssignmentExpression(statement.expression, { operator: '=' }) &&
		t.isIdentifier(statement.expression.left) &&
		t.isIdentifier(statement.expression.right)
	) {
		return [
			statement.expression.left.name,
			statement.expression.right.name,
		];
	}
	return null;
}

/** Drop matching statements anywhere in a nested statement list. */
function rewriteStatementList(
	statements: readonly t.Statement[],
	drop: (statement: t.Statement) => boolean,
): t.Statement[] {
	const rewriteBranch = (statement: t.Statement): t.Statement => {
		const rewritten = rewriteStatementList([statement], drop);
		return rewritten.length === 1
			? rewritten[0]!
			: t.blockStatement(rewritten);
	};
	return statements.filter((statement) => !drop(statement)).map(
		(statement) => {
			if (t.isBlockStatement(statement)) {
				return t.blockStatement(
					rewriteStatementList(statement.body, drop),
				);
			}
			if (t.isIfStatement(statement)) {
				const cloned = t.cloneNode(statement, false);
				cloned.consequent = rewriteBranch(statement.consequent);
				cloned.alternate = statement.alternate
					? rewriteBranch(statement.alternate)
					: null;
				return cloned;
			}
			if (
				t.isLabeledStatement(statement) ||
				t.isWhileStatement(statement) ||
				t.isDoWhileStatement(statement) ||
				t.isForStatement(statement) ||
				t.isForInStatement(statement) ||
				t.isForOfStatement(statement)
			) {
				const cloned = t.cloneNode(statement, false);
				cloned.body = rewriteBranch(statement.body);
				return cloned;
			}
			if (t.isTryStatement(statement)) {
				const cloned = t.cloneNode(statement, false);
				cloned.block = t.blockStatement(
					rewriteStatementList(statement.block.body, drop),
				);
				if (statement.handler) {
					cloned.handler = t.cloneNode(statement.handler, false);
					cloned.handler.body = t.blockStatement(
						rewriteStatementList(statement.handler.body.body, drop),
					);
				}
				if (statement.finalizer) {
					cloned.finalizer = t.blockStatement(
						rewriteStatementList(statement.finalizer.body, drop),
					);
				}
				return cloned;
			}
			if (t.isSwitchStatement(statement)) {
				const cloned = t.cloneNode(statement, false);
				cloned.cases = statement.cases.map((switchCase) => {
					const clonedCase = t.cloneNode(switchCase, false);
					clonedCase.consequent = rewriteStatementList(
						switchCase.consequent,
						drop,
					);
					return clonedCase;
				});
				return cloned;
			}
			return statement;
		},
	);
}

function stripIteratorCloseOnlyFinallyStatements(
	statements: t.Statement[],
): t.Statement[] {
	return statements.flatMap((statement) =>
		stripIteratorCloseOnlyFinallyStatement(statement)
	);
}

function stripIteratorCloseOnlyFinallyStatement(
	statement: t.Statement,
): t.Statement[] {
	if (
		t.isTryStatement(statement) &&
		!statement.handler &&
		statement.finalizer &&
		isIteratorCloseOnlyBlock(statement.finalizer)
	) {
		return stripIteratorCloseOnlyFinallyStatements(statement.block.body);
	}
	if (t.isBlockStatement(statement)) {
		const cloned = t.cloneNode(statement, true);
		cloned.body = stripIteratorCloseOnlyFinallyStatements(cloned.body);
		return [cloned];
	}
	if (t.isLabeledStatement(statement)) {
		const cloned = t.cloneNode(statement, true);
		cloned.body = stripIteratorCloseOnlyFinallyBranch(cloned.body);
		return [cloned];
	}
	if (t.isIfStatement(statement)) {
		const cloned = t.cloneNode(statement, true);
		cloned.consequent = stripIteratorCloseOnlyFinallyBranch(
			cloned.consequent,
		);
		if (cloned.alternate) {
			cloned.alternate = stripIteratorCloseOnlyFinallyBranch(
				cloned.alternate,
			);
		}
		return [cloned];
	}
	if (t.isTryStatement(statement)) {
		const cloned = t.cloneNode(statement, true);
		cloned.block.body = stripIteratorCloseOnlyFinallyStatements(
			cloned.block.body,
		);
		if (cloned.handler) {
			cloned.handler.body.body = stripIteratorCloseOnlyFinallyStatements(
				cloned.handler.body.body,
			);
		}
		if (cloned.finalizer) {
			cloned.finalizer.body = stripIteratorCloseOnlyFinallyStatements(
				cloned.finalizer.body,
			);
		}
		return [cloned];
	}
	if (
		t.isWhileStatement(statement) ||
		t.isForStatement(statement) ||
		t.isForOfStatement(statement) ||
		t.isForInStatement(statement)
	) {
		const cloned = t.cloneNode(statement, true);
		if (t.isBlockStatement(cloned.body)) {
			cloned.body.body = stripIteratorCloseOnlyFinallyStatements(
				cloned.body.body,
			);
		}
		return [cloned];
	}
	return [statement];
}

function stripIteratorCloseOnlyFinallyBranch(
	statement: t.Statement,
): t.Statement {
	const stripped = stripIteratorCloseOnlyFinallyStatement(statement);
	return stripped.length === 1 ? stripped[0] : t.blockStatement(stripped);
}

function isIteratorCloseOnlyBlock(block: t.BlockStatement): boolean {
	const effective = block.body.filter((statement) =>
		!isEmptyOrDirectiveStatement(statement)
	);
	return effective.length > 0 &&
		effective.every((statement) =>
			statementContainsOnlyIntrinsicCall(statement, 'IteratorClose')
		);
}

function isEmptyOrDirectiveStatement(statement: t.Statement): boolean {
	return t.isEmptyStatement(statement);
}

function statementContainsOnlyIntrinsicCall(
	statement: t.Statement,
	name: string,
): boolean {
	if (!t.isExpressionStatement(statement)) return false;
	const expression = statement.expression;
	return t.isCallExpression(expression) &&
		t.isV8IntrinsicIdentifier(expression.callee, { name });
}

function visitRegions(region: Region, visit: (region: Region) => void) {
	visit(region);
	switch (region.kind) {
		case 'sequence':
			for (const child of region.regions) visitRegions(child, visit);
			break;
		case 'if':
			visitRegions(region.consequent, visit);
			visitRegions(region.alternate, visit);
			break;
		case 'switch':
			for (const switchCase of region.cases) {
				visitRegions(switchCase.body, visit);
			}
			visitRegions(region.defaultBody, visit);
			break;
		case 'tryCatch':
			visitRegions(region.body, visit);
			visitRegions(region.handler, visit);
			break;
		case 'tryFinally':
			visitRegions(region.body, visit);
			visitRegions(region.finalizer, visit);
			break;
		case 'loop':
			visitRegions(region.body, visit);
			break;
	}
}

function regionContainsKind(region: Region, kind: Region['kind']): boolean {
	let found = false;
	visitRegions(region, (child) => {
		if (found) return;
		if (child.kind === kind) found = true;
	});
	return found;
}

function collectLoopSyntaxes(
	region: Region,
): Array<NonNullable<Extract<Region, { kind: 'loop' }>['syntax']>> {
	const syntaxes: Array<
		NonNullable<Extract<Region, { kind: 'loop' }>['syntax']>
	> = [];
	visitRegions(region, (child) => {
		if (child.kind === 'loop' && child.syntax) syntaxes.push(child.syntax);
	});
	return syntaxes;
}

function skippedStatementsForIteratorLoops(
	region: Region,
): Map<number, Set<number>> {
	const skipped = new Map<number, Set<number>>();
	visitRegions(region, (child) => {
		if (child.kind !== 'loop' || !child.syntax?.preheader) return;
		const statements = skipped.get(child.syntax.preheader.block) ??
			new Set();
		statements.add(child.syntax.preheader.statement);
		skipped.set(child.syntax.preheader.block, statements);
	});
	return skipped;
}

/**
 * A delegate whose normal-exit block belongs to enclosing control flow keeps
 * only that block's completion extraction: those statements are represented by
 * the `yield*` this Region emits, so the block must not emit them again.
 */
function skippedStatementsForDelegateYields(
	region: Region,
): Map<number, Set<number>> {
	const skipped = new Map<number, Set<number>>();
	visitRegions(region, (child) => {
		if (child.kind !== 'delegateYield') return;
		if (child.completionSkip) {
			addBlockStatementRange(
				skipped,
				child.completionSkip.block,
				child.completionSkip.start,
				child.completionSkip.end,
			);
		}
		if (!child.preludeSkip) return;
		const statements = skipped.get(child.preludeSkip.block) ?? new Set();
		for (const index of child.preludeSkip.statements) {
			statements.add(index);
		}
		skipped.set(child.preludeSkip.block, statements);
	});
	return skipped;
}

function skippedStatementsForFinalizerCopies(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	region: Region,
): Map<number, Set<number>> {
	const skipped = new Map<number, Set<number>>();
	const representedNormalCopyRoots = representedFinalizerCopyRoots(
		region,
		'normalExit',
	);
	// A per-exit-path finalizer copy that the structurer passed through
	// (copyDescriptorHandlers) is not a structured tryFinally, so the region walk
	// above misses its normal-exit copy roots. Register them here so the
	// un-suppression of their genuine successors below still fires (keeps e.g. the
	// real inner2 body after inner1's normal-exit finally copy).
	for (const descriptor of descriptors.exceptions.handlers) {
		if (
			!descriptors.exceptions.finalizerCopyModel.copyDescriptorHandlers
				.has(
					descriptor.handler,
				)
		) continue;
		for (const copy of descriptor.finallyCopies) {
			if (copy.kind === 'normalExit') {
				representedNormalCopyRoots.add(copy.copyRoot);
			}
		}
	}
	traceRecursiveEmit(
		`represented normal copy roots: ${
			[...representedNormalCopyRoots].map((root) =>
				`0x${root.toString(16)}`
			).join(',')
		}`,
	);
	const representedCanonicalBlocks = representedFinalizerCanonicalBlocks(
		region,
	);
	const allRepresentedCanonicalBlocks = new Set(
		[...representedCanonicalBlocks.values()].flatMap((blocks) => [
			...blocks,
		]),
	);
	const representedHandlers = representedFinalizerHandlers(
		region,
		cfg,
		descriptors,
	);
	const copyDescriptorHandlers =
		descriptors.exceptions.finalizerCopyModel.copyDescriptorHandlers;
	// A finalizer that the structurer passed through (a per-exit-path copy) is not
	// a represented region, so the main loop below skips it. Its normal-exit copy
	// carries a genuine continuation after a finally-body prefix (e.g. inner1's
	// finally-body copy immediately before `yield 13`); apply just that copy's
	// statement-level skipRanges so the duplicated prefix is suppressed while the
	// continuation survives. We deliberately do NOT run the broader
	// addLinearFinalizerCopyStatements path here — it would over-suppress a copy
	// whose canonical sibling is a real emitted finalizer (e.g. outer.finally.finally).
	for (const descriptor of descriptors.exceptions.handlers) {
		if (descriptor.kind !== 'finally') continue;
		if (!copyDescriptorHandlers.has(descriptor.handler)) continue;
		if (representedHandlers.has(descriptor.handler)) continue;
		for (const copy of descriptor.finallyCopies) {
			if (copy.kind !== 'normalExit' || !copy.skipRanges) continue;
			for (const range of copy.skipRanges) {
				addBlockStatementRange(
					skipped,
					range.block,
					range.start,
					range.end,
					`passthrough copy handler=0x${
						descriptor.handler.toString(16)
					}`,
				);
			}
		}
	}
	for (const descriptor of descriptors.exceptions.handlers) {
		if (descriptor.kind !== 'finally') continue;
		if (!representedHandlers.has(descriptor.handler)) continue;
		const canonical = new Set<number>([
			descriptor.handler,
			...(descriptor.finallyBodyBlocks ?? []),
			...(representedCanonicalBlocks.get(descriptor.handler) ?? []),
		]);
		const suffixSkipRanges = new Map<
			number,
			Array<{
				block: number;
				start: number;
				end: number;
			}>
		>();
		for (const suffix of descriptor.finallyCopySuffixes) {
			if (!suffix.skipRanges || suffix.skipRanges.length === 0) continue;
			suffixSkipRanges.set(suffix.copyRoot, suffix.skipRanges);
		}
		const normalCopyRoots = new Set(
			descriptor.finallyCopies.filter((copy) =>
				copy.kind === 'normalExit'
			).map((copy) => copy.copyRoot),
		);
		for (const copy of descriptor.finallyCopies) {
			if (allRepresentedCanonicalBlocks.has(copy.copyRoot)) continue;
			if (canonical.has(copy.copyRoot)) continue;
			const copySkipRanges = copy.skipRanges ??
				suffixSkipRanges.get(copy.copyRoot);
			if (
				representedNormalCopyRoots.has(copy.copyRoot) &&
				copy.kind !== 'normalExit'
			) continue;
			if (copySkipRanges) {
				traceRecursiveEmit(
					`skip ranged copy handler=0x${
						descriptor.handler.toString(16)
					} copy=0x${copy.copyRoot.toString(16)} ranges=${
						copySkipRanges.map((range) =>
							`0x${
								range.block.toString(16)
							}:${range.start}-${range.end}`
						).join(',')
					}`,
				);
				for (const range of copySkipRanges) {
					addBlockStatementRange(
						skipped,
						range.block,
						range.start,
						range.end,
						`ranged copy handler=0x${
							descriptor.handler.toString(16)
						} copy=0x${copy.copyRoot.toString(16)}`,
					);
				}
				continue;
			}
			if (copy.kind === 'normalExit') continue;
			addLinearFinalizerCopyStatements(
				skipped,
				cfg,
				descriptors,
				copy.copyRoot,
				canonical,
				representedNormalCopyRoots,
				`copy handler=0x${descriptor.handler.toString(16)} copy=0x${
					copy.copyRoot.toString(16)
				}`,
			);
		}
		for (const suffix of descriptor.finallyCopySuffixes) {
			if (allRepresentedCanonicalBlocks.has(suffix.copyRoot)) continue;
			if (canonical.has(suffix.copyRoot)) continue;
			if (representedNormalCopyRoots.has(suffix.copyRoot)) continue;
			if (suffix.skipRanges && suffix.skipRanges.length > 0) {
				traceRecursiveEmit(
					`skip suffix handler=0x${
						descriptor.handler.toString(16)
					} copy=0x${
						suffix.copyRoot.toString(16)
					} kind=${suffix.kind} ranges=${
						suffix.skipRanges.map((range) =>
							`0x${
								range.block.toString(16)
							}:${range.start}-${range.end}`
						).join(',')
					}`,
				);
				for (const range of suffix.skipRanges) {
					addBlockStatementRange(
						skipped,
						range.block,
						range.start,
						range.end,
						`suffix handler=0x${
							descriptor.handler.toString(16)
						} copy=0x${suffix.copyRoot.toString(16)}`,
					);
				}
			} else if (normalCopyRoots.has(suffix.copyRoot)) {
				continue;
			} else {
				addLinearFinalizerCopyStatements(
					skipped,
					cfg,
					descriptors,
					suffix.copyRoot,
					canonical,
					representedNormalCopyRoots,
					`suffix handler=0x${
						descriptor.handler.toString(16)
					} copy=0x${suffix.copyRoot.toString(16)}`,
				);
			}
		}
	}
	for (const descriptor of descriptors.exceptions.handlers) {
		if (descriptor.kind !== 'finally') continue;
		for (const copy of descriptor.enclosingFinallyCopyRoots) {
			if (!representedHandlers.has(copy.owner)) continue;
			if (allRepresentedCanonicalBlocks.has(copy.tailRoot)) continue;
			if (representedNormalCopyRoots.has(copy.tailRoot)) continue;
			traceRecursiveEmit(
				`skip enclosing owner=0x${copy.owner.toString(16)} copy=0x${
					copy.tailRoot.toString(16)
				}`,
			);
			addAllBlockStatements(
				skipped,
				cfg,
				copy.tailRoot,
				`enclosing owner=0x${copy.owner.toString(16)}`,
			);
		}
	}
	for (const root of representedNormalCopyRoots) {
		for (const successor of cfg.normalSuccessors.get(root) ?? []) {
			skipped.delete(successor);
		}
	}
	retainEscapingFinalizerCopyDefinitions(skipped, cfg);
	return skipped;
}

/**
 * Finalizer-copy suppression is only sound when every skipped SSA definition
 * is dead outside the skipped set. Retain escaping definitions and close over
 * their own dependencies so emitted successors and terminators stay bound.
 */
function retainEscapingFinalizerCopyDefinitions(
	skipped: Map<number, Set<number>>,
	cfg: ImmutableCFG,
): void {
	const definedNames = (statement: t.Statement): Set<string> => {
		const names = new Set(
			Object.keys(t.getBindingIdentifiers(statement)).filter((name) =>
				isGeneratedRegisterName(name)
			),
		);
		t.traverseFast(statement, (node) => {
			if (
				t.isAssignmentExpression(node, { operator: '=' }) &&
				t.isIdentifier(node.left) &&
				isGeneratedRegisterName(node.left.name)
			) names.add(node.left.name);
		});
		return names;
	};
	const dependencies = new Set<string>();
	const addReferences = (node: t.Node) => {
		const references = new Set<string>();
		t.traverseFast(node, (child) => {
			if (
				t.isIdentifier(child) &&
				isGeneratedRegisterName(child.name)
			) references.add(child.name);
		});
		if (t.isStatement(node)) {
			for (const name of definedNames(node)) references.delete(name);
		}
		for (const name of references) dependencies.add(name);
	};

	for (const [address, block] of cfg.blocks) {
		const skippedIndices = skipped.get(address);
		for (let index = 0; index < block.body.length; index++) {
			if (skippedIndices?.has(index)) continue;
			addReferences(block.body[index]);
		}
		switch (block.terminator.kind) {
			case 'if':
				addReferences(block.terminator.test);
				break;
			case 'switch':
				addReferences(block.terminator.discriminant);
				for (const edge of block.terminator.cases) {
					if (edge.test) addReferences(edge.test);
				}
				break;
			case 'return':
			case 'throw':
				if (block.terminator.argument) {
					addReferences(block.terminator.argument);
				}
				break;
		}
	}

	let changed: boolean;
	do {
		changed = false;
		for (const [address, indices] of skipped) {
			const block = cfg.blocks.get(address);
			if (!block) continue;
			for (const index of [...indices]) {
				const statement = block.body[index];
				if (!statement) continue;
				const definitions = definedNames(statement);
				let escapes = false;
				for (const name of definitions) {
					if (!dependencies.has(name)) continue;
					escapes = true;
					break;
				}
				if (!escapes) continue;
				indices.delete(index);
				addReferences(statement);
				changed = true;
			}
			if (indices.size === 0) skipped.delete(address);
		}
	} while (changed);
}

function representedFinalizerCopyRoots(
	region: Region,
	filterKind?: string,
): Set<number> {
	const roots = new Set<number>();
	visitRegions(region, (child) => {
		if (child.kind !== 'tryFinally') return;
		for (const copyKind of child.finallyCopyKinds ?? []) {
			if (filterKind != null && !copyKind.startsWith(`${filterKind}:`)) {
				continue;
			}
			const match = /:0x([0-9a-f]+)$/i.exec(copyKind);
			if (!match) continue;
			const root = Number.parseInt(match[1], 16);
			if (Number.isFinite(root)) roots.add(root);
		}
	});
	return roots;
}

function representedFinalizerCanonicalBlocks(
	region: Region,
): Map<number, Set<number>> {
	const blocks = new Map<number, Set<number>>();
	visitRegions(region, (child) => {
		if (child.kind !== 'tryFinally') return;
		const target = blocks.get(child.handlerAddress) ?? new Set<number>();
		for (const block of child.finalizer.sourceBlocks) {
			target.add(block);
		}
		blocks.set(child.handlerAddress, target);
	});
	return blocks;
}

function addAllBlockStatements(
	skipped: Map<number, Set<number>>,
	cfg: ImmutableCFG,
	block: number,
	reason?: string,
) {
	const source = cfg.blocks.get(block);
	if (!source) return;
	if (recursiveEmitTraceBlocks().has(block)) {
		console.error(
			`[recursive-emit:skip 0x${block.toString(16)}] all statements${
				reason ? ` (${reason})` : ''
			}`,
		);
	}
	const statements = skipped.get(block) ?? new Set<number>();
	for (let index = 0; index < source.body.length; index++) {
		statements.add(index);
	}
	skipped.set(block, statements);
}

function addBlockStatementRange(
	skipped: Map<number, Set<number>>,
	block: number,
	start: number,
	end: number,
	reason?: string,
) {
	if (start >= end) return;
	if (recursiveEmitTraceBlocks().has(block)) {
		console.error(
			`[recursive-emit:skip 0x${
				block.toString(16)
			}] range ${start}-${end}${reason ? ` (${reason})` : ''}`,
		);
	}
	const statements = skipped.get(block) ?? new Set<number>();
	for (let index = start; index < end; index++) statements.add(index);
	skipped.set(block, statements);
}

function addLinearFinalizerCopyStatements(
	skipped: Map<number, Set<number>>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	entry: number,
	canonical: ReadonlySet<number>,
	boundary: ReadonlySet<number> = new Set(),
	reason?: string,
) {
	const seen = new Set<number>();
	let cursor: number | undefined = entry;
	while (cursor != null && !seen.has(cursor)) {
		seen.add(cursor);
		if (canonical.has(cursor)) break;
		if (descriptors.exceptions.handlerByAddress.has(cursor)) break;
		if (boundary.has(cursor)) {
			traceRecursiveEmit(
				`stop linear skip at represented root 0x${cursor.toString(16)}${
					reason ? ` (${reason})` : ''
				}`,
			);
			break;
		}
		addAllBlockStatements(skipped, cfg, cursor, reason);
		const successors: Iterable<number> = cfg.normalSuccessors.get(cursor) ??
			[];
		const successorList = [...successors];
		if (successorList.length !== 1) break;
		const [next]: number[] = successorList;
		if (canonical.has(next)) break;
		if (descriptors.exceptions.handlerByAddress.has(next)) break;
		if (boundary.has(next)) break;
		cursor = next;
	}
}

function traceRecursiveEmit(message: string) {
	if (recursiveEmitTraceBlocks().size === 0) return;
	console.error(`[recursive-emit] ${message}`);
}

function mergeSkippedStatements(
	...sources: Array<Map<number, Set<number>>>
): Map<number, Set<number>> {
	const merged = new Map<number, Set<number>>();
	for (const source of sources) {
		for (const [block, statements] of source) {
			const target = merged.get(block) ?? new Set<number>();
			for (const statement of statements) target.add(statement);
			merged.set(block, target);
		}
	}
	return merged;
}

function collectFinalizerActions(
	region: Region,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
): Map<number, t.Statement[]> {
	const actions = new Map<number, t.Statement[]>();
	const representedCopyRoots = representedFinalizerCopyRoots(region);
	const representedHandlers = representedFinalizerHandlers(
		region,
		cfg,
		descriptors,
	);
	const ownership = descriptors.exceptions.finalizerEdgeActions;
	const ownedAction = (
		action: Extract<EdgeAction, { kind: 'finally' }>['action'],
	) => ownership.find((candidate) =>
		candidate.canonical === action.canonical &&
		candidate.copyRoot === action.copyRoot &&
		(action.ownerBlock == null ||
			candidate.ownerBlock === action.ownerBlock)
	);
	visitRegions(region, (child) => {
		for (const exit of child.deferredExits ?? []) {
			let owner: number | null = null;
			let terminalOwner: number | null = null;
			let emittedFinallyAction = false;
			const orderedActions = [...exit.actions].toSorted((left, right) => {
				if (left.kind !== 'finally' || right.kind !== 'finally') {
					return 0;
				}
				return (ownedAction(right.action)?.depth ?? 0) -
					(ownedAction(left.action)?.depth ?? 0);
			});
			for (const action of orderedActions) {
				if (action.kind !== 'finally') continue;
				const owned = ownedAction(action.action);
				owner = owned?.ownerBlock ?? action.action.ownerBlock ?? null;
				if (
					representedHandlers.has(action.action.canonical) &&
					implicitCopiedFinalizerRethrow(
						exit,
						action.action,
						region,
					)
				) {
					continue;
				}
				if (representedHandlers.has(action.action.canonical)) {
					// A nested iterator cleanup can propagate through an enclosing
					// iterator cleanup. When both landing pads are represented by
					// their respective for-of loops, the language supplies both closes
					// and rethrows the original exception; no explicit terminal action
					// remains to attach to the outer handler block.
					if (!representedHandlers.has(action.action.copyRoot)) {
						terminalOwner ??= action.action.terminalOwnerBlock ??
							action.action.copyRoot;
					}
					continue;
				}
				if (
					action.action.kind === 'catchTrailer' &&
					representedCopyRoots.has(action.action.copyRoot)
				) {
					terminalOwner ??= action.action.terminalOwnerBlock ??
						action.action.copyRoot;
					continue;
				}
				if (owner == null || !action.action.statements) continue;
				const statements = actions.get(owner) ?? [];
				statements.push(
					...action.action.statements.map((stmt) =>
						t.cloneNode(stmt, true)
					),
				);
				actions.set(owner, statements);
				emittedFinallyAction = true;
			}
			if (!emittedFinallyAction && terminalOwner != null) {
				appendTerminalActions(actions, terminalOwner, exit.actions);
				continue;
			}
			if (owner == null || !emittedFinallyAction) continue;
			appendTerminalActions(actions, owner, exit.actions);
		}
	});
	return actions;
}

function implicitCopiedFinalizerRethrow(
	exit: DeferredExit,
	action: Extract<EdgeAction, { kind: 'finally' }>['action'],
	region: Region,
): boolean {
	if (exit.kind !== 'functionThrow') return false;
	if (regionCoveredBlocks(region).has(action.copyRoot)) return false;
	const terminalOwner = action.terminalOwnerBlock ?? action.copyRoot;
	return !regionCoveredBlocks(region).has(terminalOwner);
}

function appendTerminalActions(
	actions: Map<number, t.Statement[]>,
	owner: number,
	exitActions: readonly EdgeAction[],
) {
	for (const action of exitActions) {
		const statements = actions.get(owner) ?? [];
		if (action.kind === 'phi') {
			for (const assignment of action.assignments) {
				pushUniqueStatement(
					statements,
					assignmentStatement(
						assignment.target,
						assignment.value,
					),
				);
			}
		} else if (action.kind === 'return') {
			pushUniqueStatement(
				statements,
				t.returnStatement(
					action.argument == null
						? null
						: t.cloneNode(action.argument, true),
				),
			);
		} else if (action.kind === 'throw') {
			pushUniqueStatement(
				statements,
				t.throwStatement(
					t.cloneNode(action.argument, true),
				),
			);
		}
		if (statements.length > 0) actions.set(owner, statements);
	}
}

function pushUniqueStatement(
	statements: t.Statement[],
	statement: t.Statement,
) {
	if (statementListIncludes(statements, statement)) return;
	statements.push(statement);
}

function statementListIncludes(
	statements: readonly t.Statement[],
	statement: t.Statement,
): boolean {
	const key = generate(statement).code;
	return statements.some((existing) => generate(existing).code === key);
}

function representedFinalizerHandlers(
	region: Region,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
): Set<number> {
	const handlers = new Set<number>();
	visitRegions(region, (child) => {
		if (child.kind === 'tryFinally') {
			handlers.add(child.handlerAddress);
			return;
		}
		if (!descriptors.exceptions.iteratorCleanupActionElision) return;
		if (child.kind !== 'loop' || child.syntax?.kind !== 'forOf') return;
		const machineNames = new Set([
			...(child.syntax.machineValues ?? []),
			...(child.syntax.internalValues ?? []),
		].map((identifier) => identifier.name));
		for (const descriptor of descriptors.exceptions.handlers) {
			if (descriptor.kind !== 'finally') continue;
			if (
				descriptor.protectedBlocks.size === 0 ||
				![...descriptor.protectedBlocks].every((block) =>
					child.sourceBlocks.has(block) ||
					descriptors.exceptions.handlerByAddress.has(block)
				)
			) continue;
			const closeRegister = iteratorCleanupRethrowRegister(
				cfg.blocks.get(descriptor.handler)?.body ?? [],
			);
			if (closeRegister != null && machineNames.has(closeRegister)) {
				handlers.add(descriptor.handler);
			}
		}
	});
	return handlers;
}

/**
 * Hermes lowers the exceptional close of a for-of iterator to a tiny finally
 * landing pad. Once the same iterator machine is emitted as `for...of`, that
 * syntax performs the close and JavaScript propagates the caught exception.
 */
function takeFinalizerActionsForBlock(
	addr: number,
	phiState: PhiEmitState,
): t.Statement[] {
	const actions = phiState.finalizerActionsByBlock.get(addr);
	if (!actions) return [];
	phiState.finalizerActionsByBlock.delete(addr);
	return actions.map((stmt) => t.cloneNode(stmt, true));
}

/**
 * The zero-trip guard Hermes emits around `for...in`: `%GetPNameList` yields an
 * undefined property list for a nullish or property-less object, and the branch
 * on it skips the loop entirely. `for (k in o)` performs that test itself, so
 * the guard is redundant and its arm is empty.
 *
 * Only that test qualifies. An ordinary conditional whose other arm happens to
 * be empty is not a guard, and dropping it would emit the loop unconditionally
 * and strand the empty arm's Phi copies, which is what the emitter reports as
 * an unplaced edge action.
 */
function redundantIteratorGuardBody(
	region: Extract<Region, { kind: 'if' }>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
): { body: Region; bypassEdge: CFGEdge } | null {
	const guardedLoopBody = phiState.loopSyntaxes.find((syntax) =>
		syntax.kind === 'forIn' &&
		(region.consequent.sourceBlocks.has(syntax.header) ||
			region.alternate.sourceBlocks.has(syntax.header))
	);
	if (!guardedLoopBody) return null;
	const body = region.consequent.sourceBlocks.has(guardedLoopBody.header)
		? region.consequent
		: region.alternate;
	const emptyArm = body === region.consequent
		? region.alternate
		: region.consequent;
	if (emptyArm.sourceBlocks.size !== 0) return null;
	const terminator = cfg.blocks.get(region.header)?.terminator;
	if (terminator?.kind !== 'if') return null;
	const emptyTarget = body === region.consequent
		? terminator.fallthrough
		: terminator.taken;
	const bypassEdge: CFGEdge = {
		from: region.header,
		to: emptyTarget,
		kind: 'normal',
	};
	return iteratorGuardTests(guardedLoopBody, cfg).some((name) =>
			isIteratorUndefinedTest(terminator.test, name)
		)
		? { body, bypassEdge }
		: null;
}

/**
 * Registers whose undefined-test decides whether the recovered loop runs at
 * all: the property list `%GetPNameList` declares, plus the machine registers
 * the syntax already subsumes so a guard reading a copy still matches.
 */
function iteratorGuardTests(
	syntax: NonNullable<Extract<Region, { kind: 'loop' }>['syntax']>,
	cfg: ImmutableCFG,
): string[] {
	const names = [
		...(syntax.machineValues ?? []),
		...(syntax.internalValues ?? []),
	].map((identifier) => identifier.name);
	if (!syntax.preheader) return names;
	const statement = cfg.blocks.get(syntax.preheader.block)
		?.body[syntax.preheader.statement];
	if (!t.isVariableDeclaration(statement)) return names;
	const declaration = statement.declarations[0];
	if (!t.isArrayPattern(declaration?.id)) return names;
	const propertyList = declaration.id.elements[0];
	if (t.isIdentifier(propertyList)) names.push(propertyList.name);
	return names;
}

function isIteratorUndefinedTest(test: t.Expression, name: string): boolean {
	if (
		!t.isBinaryExpression(test, { operator: '===' }) &&
		!t.isBinaryExpression(test, { operator: '!==' })
	) return false;
	return (
		t.isIdentifier(test.left, { name }) &&
		t.isIdentifier(test.right, { name: 'undefined' })
	) || (
		t.isIdentifier(test.right, { name }) &&
		t.isIdentifier(test.left, { name: 'undefined' })
	);
}

function expressionKey(expr: t.Expression): string {
	if (t.isIdentifier(expr)) return expr.name;
	if (t.isNumericLiteral(expr)) return String(expr.value);
	if (t.isStringLiteral(expr)) return JSON.stringify(expr.value);
	if (t.isBooleanLiteral(expr)) return String(expr.value);
	if (t.isNullLiteral(expr)) return 'null';
	return expr.type;
}

function takeSameValuePhiAssignmentsForBlock(
	addr: number,
	phiState: PhiEmitState,
): t.Statement[] {
	const assignments = phiState.sameValueAssignmentsByBlock.get(addr);
	if (!assignments) return [];
	phiState.sameValueAssignmentsByBlock.delete(addr);
	return assignments.map((stmt) => t.cloneNode(stmt, true));
}

function phiAssignmentStatement(
	statement: t.Statement,
): { target: t.Identifier; value: t.Expression } | null {
	if (!t.isExpressionStatement(statement)) return null;
	const expression = statement.expression;
	if (
		!t.isAssignmentExpression(expression, { operator: '=' }) ||
		!t.isIdentifier(expression.left) ||
		!t.isExpression(expression.right)
	) return null;
	return {
		target: expression.left,
		value: expression.right,
	};
}

function takeExceptionalStateAssignmentsForBlock(
	addr: number,
	phiState: PhiEmitState,
): t.Statement[] {
	const assignments = phiState.exceptionalStateAssignmentsByBlock.get(addr);
	if (!assignments) return [];
	phiState.exceptionalStateAssignmentsByBlock.delete(addr);
	return assignments.map((stmt) => t.cloneNode(stmt, true));
}

function takePhiActionsForRegionExits(
	region: Region,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
): t.Statement[] {
	const exits = regionExitEdges(region, cfg);
	const statements = exits.flatMap((edge) =>
		takePhiActionsForEdge(edge, phiState)
	);
	const exitSources = new Set(exits.map((edge) => edge.from));
	if (exitSources.size !== 1) return statements;

	// A copied finally/catch trailer is deliberately omitted from the Region.
	// Its Phi descriptor nevertheless retains the protected predecessor as its
	// provenance, even though the concrete CFG first routes that predecessor
	// through the canonical finalizer. Place that virtual edge action at the
	// unique lexical exit of the protected arm. With more than one exit source
	// the copy is path-dependent and must remain for a narrower child Region.
	const [exitSource] = exitSources;
	const deferredEdges = [...phiState.actionsByEdge.values()]
		.map((action) => action.edge)
		.filter((edge) =>
			edge.kind === 'normal' &&
			edge.from === exitSource &&
			!region.sourceBlocks.has(edge.to)
		);
	for (const edge of deferredEdges) {
		statements.push(...takePhiActionsForEdge(edge, phiState));
	}
	return statements;
}

function takePhiActionsForSwitchEntry(
	source: number | undefined,
	target: number,
	discriminant: t.Expression,
	test: t.Expression | null,
	phiState: PhiEmitState,
): t.Statement[] {
	if (source == null) return [];
	const actions = takePhiActionsForEdge(
		{ from: source, to: target, kind: 'normal' },
		phiState,
	);
	if (actions.length === 0 || test == null) return actions;
	// A JavaScript case body is also entered by source-level fallthrough. Phi
	// assignments attached to the dispatch edge must only run when this case was
	// selected by the switch itself; otherwise they overwrite the value carried
	// by the preceding case's CFG edge.
	return [
		t.ifStatement(
			t.binaryExpression(
				'===',
				t.cloneNode(discriminant, true),
				t.cloneNode(test, true),
			),
			t.blockStatement(actions),
		),
	];
}

function takePhiActionsForLoopBackedges(
	region: Extract<Region, { kind: 'loop' }>,
	phiState: PhiEmitState,
	emitTargets?: ReadonlySet<string>,
): t.Statement[] {
	const edges = new Map<string, CFGEdge>();
	for (const latch of region.latches) {
		const edge = {
			from: latch,
			to: region.header,
			kind: 'normal' as const,
		};
		edges.set(edgeKey(edge), edge);
	}
	for (const action of phiState.actionsByEdge.values()) {
		if (action.edge.to !== region.header) continue;
		if (!region.loopBlocks.has(action.edge.from)) continue;
		edges.set(edgeKey(action.edge), action.edge);
	}
	return [...edges.values()].flatMap((edge) =>
		takePhiActionsForEdge(edge, phiState, emitTargets)
	);
}

function takePhiActionsForLoopEntry(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
	emitTargets?: ReadonlySet<string>,
): t.Statement[] {
	const predecessors = cfg.normalPredecessors.get(region.header) ?? [];
	return [...predecessors].flatMap((from) => {
		if (region.loopBlocks.has(from)) return [];
		return takePhiActionsForEdge(
			{
				from,
				to: region.header,
				kind: 'normal',
			},
			phiState,
			emitTargets,
		);
	});
}

function takePhiActionsForFinallyEntry(
	region: Extract<Region, { kind: 'tryFinally' }>,
	phiState: PhiEmitState,
): t.Statement[] {
	return [...region.body.sourceBlocks].flatMap((from) =>
		takePhiActionsForEdge(
			{
				from,
				to: region.handlerAddress,
				kind: 'normal',
			},
			phiState,
		)
	);
}

/**
 * The canonical landing pad is entered only while unwinding an exception.
 * Its bytecode successor may flow through the same continuation Phi as the
 * protected fallthrough, but source-level `finally` resumes the pending throw
 * instead of executing that continuation. The protected edge assignment is
 * emitted before entering `finally`; the landing-pad assignment is therefore
 * dead after structuring and must not overwrite the normal value every time the
 * JavaScript finalizer runs.
 */
function discardExceptionalFinalizerContinuationPhis(
	region: Extract<Region, { kind: 'tryFinally' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
) {
	const normalExits = new Set([
		...(region.normalExit == null ? [] : [region.normalExit]),
		...region.normalExitCandidates ?? [],
	]);
	if (normalExits.size === 0) return;
	const normalPredecessors = cfg.normalPredecessors.get(
		region.handlerAddress,
	);
	if (
		[...normalPredecessors ?? []].some((predecessor) =>
			region.body.sourceBlocks.has(predecessor)
		)
	) return;
	const exceptionalPredecessors = cfg.exceptionalPredecessors.get(
		region.handlerAddress,
	);
	if (!exceptionalPredecessors || exceptionalPredecessors.size === 0) return;
	for (const action of [...phiState.actionsByEdge.values()]) {
		if (
			action.edge.kind !== 'normal' ||
			!region.finalizer.sourceBlocks.has(action.edge.from) ||
			!normalExits.has(action.edge.to)
		) continue;
		const continuationPhis = descriptors.phis.phisByBlock.get(
			action.edge.to,
		) ?? [];
		const allTargetsHaveProtectedFallthrough = action.assignments.every(
			(assignment) =>
				continuationPhis.some((phi) =>
					phi.target.name === assignment.target.name &&
					[...phi.incoming.keys()].some((predecessor) =>
						region.body.sourceBlocks.has(predecessor)
					)
				),
		);
		if (!allTargetsHaveProtectedFallthrough) continue;
		phiState.actionsByEdge.delete(edgeKey(action.edge));
	}
}

function finalizerCopyPhiAssignmentsForTryFinally(
	region: Extract<Region, { kind: 'tryFinally' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	nestedTryCatch: Extract<Region, { kind: 'tryCatch' }> | null,
): { body: t.Statement[]; handler: t.Statement[] } {
	const descriptor = descriptors.exceptions.handlerByAddress.get(
		region.handlerAddress,
	);
	if (descriptor?.kind !== 'finally') return { body: [], handler: [] };
	const bodyRegion = nestedTryCatch?.body ?? region.body;
	const handlerRegion = nestedTryCatch?.handler;
	const bodyExitKeys = new Set(
		regionExitEdges(bodyRegion, cfg).map(edgeKey),
	);
	const handlerExitKeys = handlerRegion == null
		? new Set<string>()
		: new Set(regionExitEdges(handlerRegion, cfg).map(edgeKey));
	const result = {
		body: [] as t.Statement[],
		handler: [] as t.Statement[],
	};
	const seen = {
		body: new Set<string>(),
		handler: new Set<string>(),
	};
	for (const copy of descriptor.finallyCopies) {
		if (copy.kind !== 'catchTrailer' || copy.next == null) continue;
		const copyPhis = phiInstructions(cfg.blocks.get(copy.copyRoot));
		const continuationPhis = phiInstructions(cfg.blocks.get(copy.next));
		if (copyPhis.length === 0 || continuationPhis.length === 0) continue;
		for (const copyPhi of copyPhis) {
			const copyTarget = registerName(copyPhi.destination);
			for (const continuationPhi of continuationPhis) {
				const carried = continuationPhi.sources.get(copy.copyRoot);
				if (
					!carried || !sameSSARegister(carried, copyPhi.destination)
				) {
					continue;
				}
				const continuationTarget = registerName(
					continuationPhi.destination,
				);
				if (
					!phiTargetEscapesFromBlock(
						continuationTarget,
						copy.next,
						phiState,
					)
				) continue;
				for (const [owner, source] of copyPhi.sources) {
					const edge = {
						from: owner,
						to: copy.copyRoot,
						kind: 'normal' as const,
					};
					const edgeKeyValue = edgeKey(edge);
					const arm = bodyExitKeys.has(edgeKeyValue)
						? 'body'
						: handlerExitKeys.has(edgeKeyValue)
						? 'handler'
						: null;
					if (arm == null) continue;
					const statement = assignmentStatement(
						t.identifier(continuationTarget),
						expressionForSSARegister(source),
					);
					const statementKey = generate(statement).code;
					if (seen[arm].has(statementKey)) continue;
					seen[arm].add(statementKey);
					result[arm].push(statement);
					discardPhiAssignmentsForEdge(
						edge,
						new Set([copyTarget]),
						phiState,
					);
				}
				discardPhiAssignmentsForEdge(
					{
						from: copy.copyRoot,
						to: copy.next,
						kind: 'normal',
					},
					new Set([continuationTarget]),
					phiState,
				);
			}
		}
	}
	return result;
}

function phiInstructions(block: CFGBlock | undefined): PhiInst[] {
	if (!block) return [];
	return block.ssaInstructions.filter((instruction): instruction is PhiInst =>
		instruction.instruction === 'Phi'
	);
}

function sameSSARegister(left: SSARegister, right: SSARegister): boolean {
	return left.index === right.index && left.version === right.version;
}

function expressionForSSARegister(register: SSARegister): t.Expression {
	if (register.version === 0) return t.identifier('undefined');
	return t.identifier(registerName(register));
}

function phiTargetEscapesFromBlock(
	target: string,
	block: BlockAddr,
	phiState: PhiEmitState,
): boolean {
	for (const action of phiState.actionsByEdge.values()) {
		if (action.edge.from !== block) continue;
		if (
			action.assignments.some((assignment) =>
				t.isIdentifier(assignment.value, { name: target })
			)
		) return true;
	}
	return false;
}

function discardPhiAssignmentsForEdge(
	edge: CFGEdge,
	targets: ReadonlySet<string>,
	phiState: PhiEmitState,
) {
	const key = edgeKey(edge);
	const action = phiState.actionsByEdge.get(key);
	if (!action) return;
	action.assignments = action.assignments.filter((assignment) =>
		!targets.has(assignment.target.name)
	);
	if (action.assignments.length === 0) {
		phiState.actionsByEdge.delete(key);
	}
}

function takePhiActionsForEdge(
	edge: CFGEdge,
	phiState: PhiEmitState,
	emitTargets?: ReadonlySet<string>,
): t.Statement[] {
	const action = phiState.actionsByEdge.get(edgeKey(edge));
	if (!action) return [];
	phiState.actionsByEdge.delete(edgeKey(edge));
	const assignments = emitTargets == null ? action.assignments : action
		.assignments.filter((assignment) =>
			emitTargets.has(assignment.target.name)
		);
	if (assignments.length === 0) return [];
	return lowerSimultaneousAssignments(assignments, phiState);
}

function lowerSimultaneousAssignments(
	assignments: PhiEdgeAction['assignments'],
	phiState: PhiEmitState,
): t.Statement[] {
	if (!requiresSimultaneousTemps(assignments)) {
		return assignments.map((assignment) =>
			assignmentStatement(assignment.target, assignment.value)
		);
	}
	const temps = assignments.map((assignment, index) => ({
		name: `_phi${phiState.nextTemp + index}`,
		value: assignment.value,
		target: assignment.target,
	}));
	phiState.nextTemp += assignments.length;
	return [
		...temps.map((temp) =>
			t.variableDeclaration('const', [
				t.variableDeclarator(
					t.identifier(temp.name),
					t.cloneNode(temp.value, true),
				),
			])
		),
		...temps.map((temp) =>
			assignmentStatement(temp.target, t.identifier(temp.name))
		),
	];
}

function requiresSimultaneousTemps(
	assignments: PhiEdgeAction['assignments'],
): boolean {
	const targets = new Set(
		assignments.map((assignment) => assignment.target.name),
	);
	for (const assignment of assignments) {
		let readsOtherTarget = false;
		t.traverseFast(assignment.value, (node) => {
			if (readsOtherTarget) return t.traverseFast.skip;
			if (
				t.isIdentifier(node) &&
				node.name !== assignment.target.name &&
				targets.has(node.name)
			) {
				readsOtherTarget = true;
			}
		});
		if (readsOtherTarget) return true;
	}
	return false;
}

function assignmentStatement(
	target: t.Identifier,
	value: t.Expression,
): t.Statement {
	return t.expressionStatement(
		t.assignmentExpression(
			'=',
			t.cloneNode(target),
			t.cloneNode(value, true),
		),
	);
}

function regionExitEdges(region: Region, cfg: ImmutableCFG): CFGEdge[] {
	const edges: CFGEdge[] = [];
	for (const from of region.sourceBlocks) {
		for (const to of cfg.normalSuccessors.get(from) ?? []) {
			if (region.sourceBlocks.has(to)) continue;
			edges.push({ from, to, kind: 'normal' });
		}
	}
	return edges;
}

/**
 * Place Phi copies carried by the single linear edge between adjacent sequence
 * children. Structured children place their own branching exit copies, but a
 * plain `basic -> basic` boundary has no other emission site.
 *
 * More than one boundary edge represents a merge rather than a linear
 * sequence. Leave those actions for the owning structured region instead of
 * emitting path-dependent copies unconditionally.
 */
function takePhiActionsBetweenRegions(
	left: Region,
	right: Region,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
): t.Statement[] {
	const boundaryEdges = regionExitEdges(left, cfg).filter((edge) =>
		right.kind === 'terminalReference'
			? edge.to === right.entry
			: right.sourceBlocks.has(edge.to)
	);
	if (boundaryEdges.length !== 1) return [];
	return takePhiActionsForEdge(boundaryEdges[0]!, phiState);
}

function takePhiActionsForTrailingSequenceRegion(
	region: Region,
	cfg: ImmutableCFG,
	phiState: PhiEmitState,
): t.Statement[] {
	const boundaryEdges = regionExitEdges(region, cfg);
	if (boundaryEdges.length !== 1) return [];
	return takePhiActionsForEdge(boundaryEdges[0]!, phiState);
}

/**
 * The structurer only produces divergent breaks when it has no ordered suffix
 * Region to leave (see `classifyAbruptLoopCompletions`), so report them rather
 * than emit them: the candidate is rejected and the reducer keeps a faithful
 * body. A labelled sequence exit can skip a control-only trailer, but a
 * Phi-carrying exit still needs edge-local value placement before the break.
 */
function reportDivergentLoopBreaks(
	region: Extract<Region, { kind: 'loop' }>,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
) {
	const destinations = new AddressSet<BlockAddr>();
	// The exhausted-iterator exit leaves through a completion-flag guarded
	// labelled break that carries its own edge actions, so it never competes
	// with a body break for the loop's fallthrough.
	const completionSequenceExit = iteratorCompletionSequenceExit(region, cfg);
	for (const exit of region.exits) {
		if (exit.kind !== 'break' || exit === completionSequenceExit) continue;
		// A destination that carries its own completion never needs the loop's
		// continuation, so it cannot disagree with another break about it.
		if (
			loopExitTerminalCompletion(
				exit,
				cfg,
				descriptors,
				region,
				phiState.regionBlocks,
			) != null
		) continue;
		// A named sequence exit is a complete transfer to its own destination.
		// Its labelBreak emits this edge's Phi actions before leaving the span;
		// unplaced-edge validation below remains the proof that state was kept.
		const endsTheLoop = region.syntax != null &&
			exit.from === region.header;
		if (exit.sequenceExit?.label && !endsTheLoop) continue;
		const destination = exit.trailer ? exit.continuation : exit.to;
		if (destination != null) destinations.add(destination);
	}
	if (destinations.size < 2) return;
	diagnostics.push(
		`divergent loop breaks at 0x${region.header.toString(16)}: ${
			[...destinations].toSorted((left, right) => left - right)
				.map((address) => `0x${address.toString(16)}`)
				.join(',')
		}`,
	);
}

function reportUnplacedPhis(
	phiState: PhiEmitState,
	diagnostics: string[],
) {
	for (const action of phiState.actionsByEdge.values()) {
		diagnostics.push(
			`unplaced edge phi action ${action.edge.kind}:0x${
				action.edge.from.toString(16)
			}->0x${action.edge.to.toString(16)}`,
		);
	}
	for (const block of phiState.exceptionalStateAssignmentsByBlock.keys()) {
		diagnostics.push(
			`unplaced exceptional phi state at 0x${block.toString(16)}`,
		);
	}
	for (const block of phiState.sameValueAssignmentsByBlock.keys()) {
		diagnostics.push(
			`unplaced same-value phi assignment at 0x${block.toString(16)}`,
		);
	}
	for (const block of phiState.finalizerActionsByBlock.keys()) {
		diagnostics.push(
			`unplaced finalizer action at 0x${block.toString(16)}`,
		);
	}
}

function edgeKey(edge: CFGEdge): string {
	return `${edge.kind}:${edge.from}->${edge.to}`;
}

function isCoveredPhiStatement(
	stmt: t.Statement,
	addr: number,
	phiState: PhiEmitState,
): boolean {
	if (!phiState.coveredPhiBlocks.has(addr)) return false;
	if (!t.isVariableDeclaration(stmt)) return false;
	return stmt.declarations.some((decl) =>
		t.isCallExpression(decl.init) &&
		t.isV8IntrinsicIdentifier(decl.init.callee, { name: 'Phi' })
	);
}

function containsPhiIntrinsic(node: t.Node): boolean {
	let found = false;
	t.traverseFast(node, (candidate) => {
		if (
			t.isCallExpression(candidate) &&
			t.isV8IntrinsicIdentifier(candidate.callee, { name: 'Phi' })
		) {
			found = true;
			return t.traverseFast.skip;
		}
	});
	return found;
}

function referencedIdentifierNames(
	statements: readonly t.Statement[],
): Set<string> {
	const names = new Set<string>();
	for (const stmt of statements) {
		t.traverseFast(stmt, (node) => {
			if (t.isIdentifier(node)) names.add(node.name);
		});
	}
	return names;
}

/**
 * Emit a Region that becomes a JavaScript block, hoisting whatever escapes it.
 *
 * `try`, `catch`, `finally` and a recovered `for` body are all block scopes. A
 * value the block computes and the code after it reads has to be declared
 * outside the block, or it is emitted as a block-local `const` and read where
 * nothing declares it. Every such construct needs this; writing it out per
 * construct is how `try`/`finally` came to be missing it.
 */
function emitBlockScopedRegion(
	region: Region,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	phiState: PhiEmitState,
	diagnostics: string[],
	options: {
		/** Blocks outside the Region whose copies are emitted within it anyway. */
		alsoInside?: AddressSet<BlockAddr>;
		/** Already-emitted statements, when the caller assembled them itself. */
		statements?: t.Statement[];
	} = {},
): { statements: t.Statement[]; hoisted: Set<string> } {
	return hoistEscapingDeclarations(
		options.statements ??
			emitRegion(region, cfg, descriptors, phiState, diagnostics),
		regionEscapingDeclaredNames(
			region,
			cfg,
			descriptors,
			options.alsoInside,
		),
	);
}

interface RegisterUseIndex {
	declaredByBlock: Map<BlockAddr, Set<string>>;
	referencedByBlock: Map<BlockAddr, Set<string>>;
	phiIncomingByPredecessor: Map<
		BlockAddr,
		Array<{ block: BlockAddr; name: string }>
	>;
}

const registerUseIndexes = new WeakMap<ImmutableCFG, RegisterUseIndex>();

/**
 * Where each generated register is declared and read, indexed once per CFG.
 *
 * Every block-scoped construct asks which of its declarations escape it, and
 * answering that from the AST costs a walk of the whole function. A function
 * whose regions nest -- a `try` inside a `finally` inside a loop -- asks once
 * per construct, so the walk has to happen once per function instead.
 */
function registerUseIndex(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
): RegisterUseIndex {
	const cached = registerUseIndexes.get(cfg);
	if (cached) {
		return cached;
	}
	const declaredByBlock = new Map<BlockAddr, Set<string>>();
	const referencedByBlock = new Map<BlockAddr, Set<string>>();
	const phiIncomingByPredecessor = new Map<
		BlockAddr,
		Array<{ block: BlockAddr; name: string }>
	>();
	const addTo = (
		map: Map<BlockAddr, Set<string>>,
		address: BlockAddr,
		name: string,
	) => {
		const names = map.get(address);
		if (names) names.add(name);
		else map.set(address, new Set([name]));
	};
	for (const [address, block] of cfg.blocks) {
		for (const statement of block.body) {
			t.traverseFast(statement, (node) => {
				if (
					t.isVariableDeclarator(node) &&
					t.isIdentifier(node.id) &&
					isGeneratedRegisterName(node.id.name)
				) addTo(declaredByBlock, address, node.id.name);
				if (
					t.isIdentifier(node) &&
					isGeneratedRegisterName(node.name)
				) {
					addTo(referencedByBlock, address, node.name);
				}
			});
		}
		for (const expression of terminatorExpressions(block.terminator)) {
			t.traverseFast(expression, (node) => {
				if (
					t.isIdentifier(node) &&
					isGeneratedRegisterName(node.name)
				) {
					addTo(referencedByBlock, address, node.name);
				}
			});
		}
	}
	for (const phi of descriptors.phis.phis) {
		for (const [predecessor, assignment] of phi.incoming) {
			if (!t.isIdentifier(assignment.value)) continue;
			const incoming = phiIncomingByPredecessor.get(predecessor);
			const entry = { block: phi.block, name: assignment.value.name };
			if (incoming) incoming.push(entry);
			else phiIncomingByPredecessor.set(predecessor, [entry]);
		}
		for (const [protectedBlock, assignment] of phi.exceptionalIncoming) {
			if (!t.isIdentifier(assignment.value)) continue;
			addTo(
				referencedByBlock,
				protectedBlock,
				assignment.value.name,
			);
		}
	}
	const index = {
		declaredByBlock,
		referencedByBlock,
		phiIncomingByPredecessor,
	};
	registerUseIndexes.set(cfg, index);
	return index;
}

function isGeneratedRegisterName(name: string): boolean {
	return /^r\d+_\d+$/.test(name);
}

/**
 * The generated registers a Region declares and something outside it reads.
 *
 * `alsoInside` names blocks the Region does not own whose copies are emitted
 * within it anyway -- a loop header's backedge Phi actions, for instance.
 */
function regionEscapingDeclaredNames(
	region: Region,
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
	alsoInside?: ReadonlySet<BlockAddr>,
): Set<string> {
	const index = registerUseIndex(cfg, descriptors);
	const declared = new Set<string>();
	for (const address of region.sourceBlocks) {
		for (const name of index.declaredByBlock.get(address) ?? []) {
			declared.add(name);
		}
	}
	const escaping = new Set<string>();
	if (declared.size === 0) return escaping;
	const isInside = (address: BlockAddr) =>
		region.sourceBlocks.has(address) ||
		alsoInside?.has(address) === true;
	for (const [address, names] of index.referencedByBlock) {
		if (isInside(address)) continue;
		for (const name of names) {
			if (declared.has(name)) escaping.add(name);
		}
	}
	// A Phi edge action is not a block statement. When a value produced inside
	// this region feeds a join outside it, the copy is emitted at the boundary
	// and the declaration has to outlive the label.
	for (const [predecessor, incoming] of index.phiIncomingByPredecessor) {
		if (!region.sourceBlocks.has(predecessor)) continue;
		for (const { block, name } of incoming) {
			if (isInside(block) || !declared.has(name)) continue;
			escaping.add(name);
		}
	}
	return escaping;
}

function terminatorExpressions(
	terminator: Terminator,
): t.Expression[] {
	switch (terminator.kind) {
		case 'if':
			return [terminator.test];
		case 'switch':
			return [
				terminator.discriminant,
				...terminator.cases.flatMap((switchCase) =>
					switchCase.test ? [switchCase.test] : []
				),
			];
		case 'return':
		case 'throw':
			return terminator.argument ? [terminator.argument] : [];
		case 'goto':
		case 'unreachable':
			return [];
	}
}

function hoistEscapingDeclarations(
	statements: t.Statement[],
	escaping: ReadonlySet<string>,
): { statements: t.Statement[]; hoisted: Set<string> } {
	const hoisted = new Set<string>();
	if (escaping.size === 0) return { statements, hoisted };
	const file = t.file(t.program(statements));
	try {
		traverse(file, {
			noScope: true,
			Function(path) {
				path.skip();
			},
			VariableDeclaration(path) {
				if (!path.inList) return;
				const replacements: t.Statement[] = [];
				let changed = false;
				for (const declaration of path.node.declarations) {
					if (
						t.isIdentifier(declaration.id) &&
						escaping.has(declaration.id.name)
					) {
						changed = true;
						hoisted.add(declaration.id.name);
						if (
							declaration.init && t.isExpression(declaration.init)
						) {
							replacements.push(t.expressionStatement(
								t.assignmentExpression(
									'=',
									t.cloneNode(declaration.id),
									t.cloneNode(declaration.init, true),
								),
							));
						}
						continue;
					}
					replacements.push(rebuiltVariableDeclaration(path.node, [
						t.cloneNode(declaration, true),
					]));
				}
				if (!changed) return;
				path.replaceWithMultiple(replacements);
				path.skip();
			},
		});
	} finally {
		traverse.cache.clear();
	}
	return { statements: file.program.body, hoisted };
}

function generatedLetDeclaration(names: ReadonlySet<string>): t.Statement[] {
	if (names.size === 0) return [];
	return [t.variableDeclaration(
		'let',
		[...names].toSorted().map((name) =>
			t.variableDeclarator(t.identifier(name))
		),
	)];
}
