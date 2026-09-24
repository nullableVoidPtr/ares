import * as t from '@babel/types';
import generate from '@babel/generator';
import {
	copyFunctionForSSA,
	SSAFunction,
	type SSAInstruction,
	SSARegister,
	ssaRegisterEquals,
} from '../../ssa.ts';
import {
	BigIntRef,
	type LoadConstInst,
	StringRef,
} from '../../hbc/disassembly/instruction.ts';
import traverse, { NodePath } from '@babel/traverse';
import { HBCFile, SerializedLiteralValue } from '../../parser/file.ts';
import {
	BlockAddr,
	FunctionExceptionHandler,
	FunctionKind,
} from '../../hbc/disassembly/function.ts';
import {
	capturePlainObjectProjectionSources,
	objectRestProtocolBindingNames,
	recordResidualObjectRestTelemetry,
	recoverGuardedObjectDestructuring,
	reduceArgumentsCopyRest,
	reduceDanglingGuardTail,
	reduceDirectEvalDiamonds,
	reduceGuardedBooleanPhiPredicate,
	reduceInlineTerminal,
	reduceIteratorDestructuringDefaults,
	reduceIteratorDestructuringSequence,
	reduceMergedGuardPhiTerminal,
	reduceNaturalLoop,
	reduceNestedRecoveredDestructuring,
	reduceNullishDefaultReturnPhi,
	reduceOrChain,
	reducePredicateGuardChains,
	reduceProtectedArrayDestructuring,
	reduceSequence,
	reduceSequentialArrayDestructuring,
	reduceSequentialObjectDestructuring,
	reduceSharedAlternateGuard,
	reduceSharedGuardedPrelude,
	reduceSharedLeadingPhi,
	reduceSharedSequenceEdge,
	reduceSharedTerminalPhi,
	reduceSideEffectOnlyOverflowDefault,
	reduceSimpleIf,
	reduceSwitch,
	reduceTryCatch,
} from './cfg/mod.ts';
import {
	reduceDelegateYieldCFG,
	reduceDelegateYieldStructuredBodies,
} from './cfg/delegateYield.ts';
import { registerName } from './cfg/phi.ts';
import {
	structureCFG,
	type StructuringResult,
} from './cfg/structure/structureRegion.ts';
import { runRecursiveCFGAnalysis } from './cfg/recursiveAnalysis.ts';
import {
	foldGuardedLoopExitTests,
	simplifyForwardExitLabels,
} from './cfg/emit/emitRegion.ts';
import { type CFGReducerOptions, envCFGReducerOptions } from './cfg/options.ts';
import {
	containsDestructuringProtocol,
	destructuringSourceDefault,
	destructuringUndefinedAliases,
	identifierOccurrences,
} from './cfg/destructuringPlan.ts';
import { type ReductionPass, runFixpoint } from './cfg/reductionPipeline.ts';
import {
	attachDirectParameterPatterns,
	attachParameterPatternAssignmentDefaults,
	attachPatternBindingDefaults,
	attachProjectedObjectParameterPatterns,
	captureParameterProjections,
	cloneParameterPlan,
	createParameterPlan,
	materializeParameterPlan,
	type ParameterPlan,
	recoverOverflowParameters,
	setRestParameter,
	synchronizeParameterPlan,
} from './cfg/parameterPlan.ts';
import {
	containsRawSwitchIntrinsic,
	type RecursiveCFGBindingPlacementAudit,
	type RecursiveCFGCompatibilityEvent,
	type RecursiveCFGCompatibilityPath,
	type RecursiveCFGEmission,
	type RecursiveCFGSummary,
	summarizeRecursiveCFG,
} from './cfg/recursiveSummary.ts';
export type { RecursiveCFGSummary } from './cfg/recursiveSummary.ts';
import { statementFingerprint } from './cfg/descriptors/subgraphMatch.ts';
import {
	repairLabelledLoopFinally,
	repairNestedLabelledBreakLoops,
} from './cfg/descriptors/loopRepairs.ts';
import {
	cleanupLocalPNameForInLoops,
	cleanupLocalSyncIteratorForOfLoops,
	stripIteratorCloseBeforeIteratorAbruptExits,
} from './cfg/iterator.ts';
import {
	IRBlock,
	isFromIRCall,
	isFromIRCreateClass,
	LiftedAST,
} from '../ast/mod.ts';
import { liftSSABlocktoIR } from '../ast/lift.ts';
import {
	comparableAst,
	extractFunctionRef,
	isReadOnlyEnvironmentLookup,
	isUndefinedNode,
} from '../ast/utils.ts';
import { LiftError } from './../error.ts';
import { AddressSet } from '../../utils/set.ts';
import { ssaLivenessAnalysis } from '../../utils/liveness.ts';
import { AddressMap } from '../../utils/map.ts';
import { AddressGraph } from '../../utils/graph.ts';
import { HandlerGraph, HandlerGraphSnapshot } from './except/mod.ts';
import {
	recordLoweredGeneratorWrapperSlotAliases,
	tryInitializeLoweredGeneratorStateMachine,
} from './loweredGenerator/mod.ts';
import {
	constIdentifierInit,
	extractRegisterAssign,
	nodePathIsAttached,
} from '../ast/utils.ts';
import { coalesceParameterAliases, tagStorageLocation } from '../ast/alias.ts';
import {
	type BindingPlacementTreeResult,
	placeGeneratedBindingsInTree,
} from '../ast/placement.ts';
import { preserveDuplicateRegisterScopesInBody } from '../ast/registerScope.ts';
import {
	type ElidedWrapperEnvironmentCapture,
	isEnvironmentSlotName,
} from '../environment.ts';
import {
	assignmentUpdateExpression,
	flattenElseIfBlock,
	inlineNullPrototypeObjectLiteral,
	inlineObjectConstruction,
	inlineObjectConstructionsToFixpoint,
	invertTest,
	invertTestSimplifies,
	liftHermesApplyCall,
	liftHermesConcatCall,
	postfixUpdateFromToNumericTemp,
	rewriteTwoArgumentCopyDataProperties,
	rotateTerminatingGuardIntoElseIf,
	toCompoundAssignment,
} from '../ast/expression.ts';
import {
	foldConditionalValuesInBody,
	liftLoopHeaderPhiAssignments,
	liftPhiNodesInBody,
	refoldConditionalValues,
	removeUnusedPhiExpressions,
	simplifyGuardedPrimitivePhiCalls,
	simplifyNullGuardedPhiDeclarations,
	simplifyProvenanceResolvedPhiCalls,
	simplifyScopedPhiAssignments,
	simplifyScopedPhiCalls,
	simplifyScopedPhiDeclarations,
	simplifySelfUpdatePhiAssignments,
	simplifyTerminalReturnPhis,
} from '../ast/phi.ts';
import { phiContext } from './cfg/phi.ts';
import { chainSharedRegisterAssignmentsInBody } from '../ast/assignment.ts';
import { rewriteStructuredStatementLists } from '../ast/statementLists.ts';
import {
	liftCommonTerminalSuffixToFinally,
	splitNestedTerminalFinalizer,
	statementAlwaysTerminates,
	stripAdjacentRethrowFinalizerCopies,
	stripLeadingFinalizerCopyBeforeTerminalTail,
	stripOwnedAdjacentRethrowFinalizerCopies,
	stripOwnedTerminalEnclosingFinalizerCopies,
	stripStatementBeforeTerminal,
	stripStatementBeforeTerminalTail,
	stripStatementSuffix,
	stripTerminalEnclosingFinalizerCopies,
} from './finalizer.ts';
import {
	cleanupBaseConstructorBody,
	cleanupDerivedConstructorBody,
} from '../ast/module/class/native.ts';
import {
	createThisMatchesConstructTarget,
	crossesControlBoundary,
	expressionsEqual,
	identifierUseCount,
	implicitConstructExpression,
	isCreateThisCall,
	isDuplicableScalarExpression,
	isFreelyDuplicableInit,
	isHermesEnsureObjectArgument,
	isSelectObjectThisArgument,
	singleDeclarator,
	tryGetByIdCallCallee,
} from './utils.ts';

let DEBUG_DUP_SSA = false;
try {
	DEBUG_DUP_SSA = Deno.env.get('ARES_DEBUG_DUP_SSA') === '1';
} catch {
	DEBUG_DUP_SSA = false;
}

function debugDupSSA(...args: unknown[]) {
	if (DEBUG_DUP_SSA) console.error('[dup-ssa]', ...args);
}

// Lowering is linear in the incoming edges and consumes the Phi
// transactionally. Large decision DAGs can legitimately converge from more
// than sixteen edges (Discord #11476 has 31); leaving that Phi in place forces
// the compatibility reducer to duplicate the shared decision continuation.
const SAFE_SHARED_LEADING_PHI_PREDECESSORS = 16;
const MAX_SHARED_LEADING_PHI_PREDECESSORS = 64;

function singleStatementFromBranch(
	branch: NodePath<t.Statement | null>,
): NodePath<t.Statement> | null {
	if (!branch.hasNode()) return null;
	if (branch.isBlockStatement()) {
		const body = branch.get('body');
		if (body.length !== 1) return null;
		return body[0] as NodePath<t.Statement>;
	}
	return branch as NodePath<t.Statement>;
}

function nextSiblingStatement(
	stmt: NodePath<t.Statement>,
): NodePath<t.Statement> | undefined {
	if (
		!stmt.parentPath.isBlockStatement() &&
		!stmt.parentPath.isProgram()
	) return undefined;
	const siblings = stmt.parentPath.get('body');
	const index = siblings.findIndex((sibling) => sibling.node === stmt.node);
	return index >= 0 ? siblings[index + 1] : undefined;
}

function isHermesInternalMemberAccess(
	expr: NodePath<t.Expression | null>,
): expr is NodePath<t.MemberExpression> {
	if (!expr.isMemberExpression({ computed: false })) return false;
	if (!expr.get('object').isIdentifier({ name: 'HermesInternal' })) {
		return false;
	}
	return expr.get('property').isIdentifier();
}

function branchRootForReference(
	reference: NodePath,
	branch: NodePath,
): NodePath | null {
	let child: NodePath | null = reference;
	while (child?.parentPath && child.parentPath !== branch) {
		child = child.parentPath;
	}
	return child?.parentPath === branch ? child : null;
}

function referenceIsUnconditionalWithinBranch(
	reference: NodePath,
	branch: NodePath,
): boolean {
	if (
		branch.isFunction() ||
		branch.isConditionalExpression() ||
		branch.isLogicalExpression() ||
		branch.isIfStatement() ||
		branch.isSwitchStatement() ||
		branch.isTryStatement() ||
		branch.isWhileStatement() ||
		branch.isDoWhileStatement() ||
		branch.isForStatement() ||
		branch.isForInStatement() ||
		branch.isForOfStatement() ||
		branch.isOptionalCallExpression() ||
		branch.isOptionalMemberExpression()
	) {
		return false;
	}
	for (
		let path = reference.parentPath;
		path && path !== branch;
		path = path.parentPath
	) {
		if (
			path.isFunction() ||
			path.isConditionalExpression() ||
			path.isLogicalExpression() ||
			path.isIfStatement() ||
			path.isSwitchStatement() ||
			path.isTryStatement() ||
			path.isWhileStatement() ||
			path.isDoWhileStatement() ||
			path.isForStatement() ||
			path.isForInStatement() ||
			path.isForOfStatement() ||
			path.isOptionalCallExpression() ||
			path.isOptionalMemberExpression()
		) {
			return false;
		}
	}
	return true;
}

function conditionalBranchForReference(
	reference: NodePath,
): { node: t.Node; arm: 'consequent' | 'alternate' } | null {
	for (let path = reference.parentPath; path; path = path.parentPath) {
		if (path.isFunction()) return null;
		if (path.isConditionalExpression()) {
			const branch = branchRootForReference(reference, path);
			if (!branch) return null;
			if (branch.key !== 'consequent' && branch.key !== 'alternate') {
				return null;
			}
			if (!referenceIsUnconditionalWithinBranch(reference, branch)) {
				return null;
			}
			return { node: path.node, arm: branch.key };
		}
		if (path.isIfStatement()) {
			if (!path.node.alternate) return null;
			const branch = branchRootForReference(reference, path);
			if (!branch) return null;
			if (branch.key !== 'consequent' && branch.key !== 'alternate') {
				return null;
			}
			if (!referenceIsUnconditionalWithinBranch(reference, branch)) {
				return null;
			}
			return { node: path.node, arm: branch.key };
		}
	}
	return null;
}

function referencesAreBalancedConditionalBranches(
	references: NodePath[],
): boolean {
	if (references.length !== 2) return false;
	const left = conditionalBranchForReference(references[0]);
	const right = conditionalBranchForReference(references[1]);
	return !!left && !!right &&
		left.node === right.node &&
		left.arm !== right.arm;
}

function ssaInstructionUsesRegister(
	instruction: SSAInstruction,
	register: SSARegister,
): boolean {
	if (!('uses' in instruction)) return false;
	for (const value of Object.values(instruction.uses)) {
		const uses = Array.isArray(value) ? value : [value];
		if (uses.some((use) => ssaRegisterEquals(use, register))) return true;
	}
	return false;
}

function exactRegisterUseCountInBlock(
	instructions: SSAInstruction[],
	register: SSARegister,
): number {
	let count = 0;
	for (const instruction of instructions) {
		if (ssaInstructionUsesRegister(instruction, register)) count++;
	}
	return count;
}

function hasBalancedBranchLiveness(
	func: IRFunction,
	register: SSARegister,
): boolean {
	const liveness = ssaLivenessAnalysis(func.ssa);
	for (const [address, block] of func.ssa.basicBlocks) {
		if (block.consequentAddresses.length !== 2) continue;
		if (!liveness.blockLiveness.get(address)?.liveOut.has(register.index)) {
			continue;
		}

		let usedOnceInEverySuccessor = true;
		for (const successorAddress of block.consequentAddresses) {
			if (
				!liveness.blockLiveness.get(successorAddress)?.liveIn.has(
					register.index,
				)
			) {
				usedOnceInEverySuccessor = false;
				break;
			}
			const successor = func.ssa.basicBlocks.get(successorAddress);
			if (
				!successor ||
				exactRegisterUseCountInBlock(
						successor.ssaInstructions,
						register,
					) !== 1
			) {
				usedOnceInEverySuccessor = false;
				break;
			}
		}
		if (usedOnceInEverySuccessor) return true;
	}
	return false;
}

function parseGeneratedSSARegisterName(name: string): SSARegister | null {
	const match = /^r(\d+)_(\d+)$/.exec(name);
	if (!match) return null;
	return {
		type: 'register',
		index: Number(match[1]),
		version: Number(match[2]),
	};
}

function isValueIdentifierReference(path: NodePath<t.Identifier>): boolean {
	const parent = path.parentPath;
	if (!parent) return true;
	if (parent.isVariableDeclarator() && path.key === 'id') return false;
	if (
		(parent.isFunctionDeclaration() || parent.isFunctionExpression()) &&
		path.key === 'id'
	) return false;
	if (
		parent.isMemberExpression() &&
		path.key === 'property' &&
		!parent.node.computed
	) return false;
	if (
		(parent.isObjectProperty() || parent.isObjectMethod()) &&
		path.key === 'key' &&
		!parent.node.computed
	) return false;
	if (parent.isLabeledStatement()) return false;
	if (
		(parent.isBreakStatement() || parent.isContinueStatement()) &&
		path.key === 'label'
	) return false;
	if (parent.isCatchClause() && path.key === 'param') return false;
	return true;
}

function isIdentifierWrite(path: NodePath<t.Identifier>): boolean {
	const parent = path.parentPath;
	if (!parent) return false;
	if (parent.isAssignmentExpression() && path.key === 'left') return true;
	if (parent.isUpdateExpression() && path.key === 'argument') return true;
	if (
		parent.isUnaryExpression({ operator: 'delete' }) &&
		path.key === 'argument'
	) return true;
	return false;
}

function deoptimizeHermesInternalConditionalMemberAccessesInProgram(
	program: t.Program,
	func: IRFunction,
): boolean {
	const candidatesByName = new Map<
		string,
		{
			declaration: NodePath<t.VariableDeclaration>;
			init: t.MemberExpression;
			register: SSARegister;
			references: NodePath[];
			invalid: boolean;
		}
	>();

	traverse(t.file(program), {
		noScope: true,
		Function(path) {
			path.skip();
		},
		VariableDeclaration(path) {
			if (path.node.declarations.length !== 1) return;
			const declarator = path.get('declarations.0');
			if (!declarator.isVariableDeclarator()) return;
			const id = declarator.get('id');
			if (!id.isIdentifier()) return;
			const register = (id.node as LiftedAST<t.Identifier>).extra
				?.sourceRegister ?? parseGeneratedSSARegisterName(id.node.name);
			if (!register) return;
			const init = declarator.get('init');
			if (!isHermesInternalMemberAccess(init)) return;
			if (candidatesByName.has(id.node.name)) {
				candidatesByName.get(id.node.name)!.invalid = true;
				return;
			}
			candidatesByName.set(id.node.name, {
				declaration: path,
				init: init.node,
				register,
				references: [],
				invalid: false,
			});
		},
	});

	traverse(t.file(program), {
		noScope: true,
		Function(path) {
			path.skip();
		},
		Identifier(path) {
			const candidate = candidatesByName.get(path.node.name);
			if (!candidate) return;
			if (
				path.parentPath?.isVariableDeclarator() &&
				path.parentPath.node ===
					candidate.declaration.node.declarations[0] &&
				path.key === 'id'
			) {
				return;
			}
			if (!isValueIdentifierReference(path)) return;
			if (isIdentifierWrite(path)) {
				candidate.invalid = true;
				return;
			}
			candidate.references.push(path);
		},
	});

	let changed = false;
	for (const candidate of candidatesByName.values()) {
		const { declaration, init, register, references } = candidate;
		if (candidate.invalid) continue;
		if (references.length !== 2) continue;
		if (!referencesAreBalancedConditionalBranches(references)) continue;
		if (!hasBalancedBranchLiveness(func, register)) continue;
		if (declaration.removed) continue;
		for (const reference of references) {
			if (reference.removed) continue;
			reference.replaceWith(t.cloneNode(init, true));
		}
		declaration.remove();
		changed = true;
	}
	return changed;
}

export function reduceHermesInternalConditionalMemberAccesses(
	func: IRFunction,
): boolean {
	let changed = false;
	for (const block of func.blocks.values()) {
		const { wrapped, commit } = blockProgramWithBranch(block);
		if (
			deoptimizeHermesInternalConditionalMemberAccessesInProgram(
				wrapped.program,
				func,
			)
		) {
			commit();
			changed = true;
		}
	}
	return changed;
}

function functionPrototypeDispatchSource(
	test: NodePath<t.Expression>,
	scope: NodePath['scope'],
): { operator: '===' | '!=='; kind: 'call' | 'apply' } | null {
	if (
		!test.isBinaryExpression() ||
		(test.node.operator !== '===' && test.node.operator !== '!==')
	) return null;

	const left = test.get('left') as NodePath<t.Expression>;
	const right = test.get('right') as NodePath<t.Expression>;
	let src = left;
	let builtin = right;
	if (
		!t.matchesPattern(builtin.node, [
			'HermesInternal',
			'functionPrototypeCall',
		]) &&
		!t.matchesPattern(builtin.node, [
			'HermesInternal',
			'functionPrototypeApply',
		])
	) {
		src = right;
		builtin = left;
	}

	if (!src.isMemberExpression({ computed: false })) {
		if (!src.isIdentifier()) return null;
		const resolved = constIdentifierInit(scope, src.node.name);
		if (!resolved?.isMemberExpression()) return null;
		src = resolved;
	}

	if (
		t.matchesPattern(builtin.node, [
			'HermesInternal',
			'functionPrototypeCall',
		])
	) {
		if (!src.get('property').isIdentifier({ name: 'call' })) return null;
		return { operator: test.node.operator, kind: 'call' };
	}
	if (
		t.matchesPattern(builtin.node, [
			'HermesInternal',
			'functionPrototypeApply',
		])
	) {
		if (!src.get('property').isIdentifier({ name: 'apply' })) return null;
		return { operator: test.node.operator, kind: 'apply' };
	}
	return null;
}

function isUnreferencedClosureCreation(
	path: NodePath<t.Expression | null>,
): boolean {
	if (!path.isCallExpression()) return false;
	const callee = path.get('callee');
	if (!callee.isV8IntrinsicIdentifier()) return false;
	return [
		'CreateClosure',
		'CreateGeneratorClosure',
		'CreateAsyncClosure',
	].includes(callee.node.name);
}

function constructIntrinsicNewExpression(
	constructCall: NodePath<t.CallExpression>,
	thisName: string,
	thisInit?: NodePath<t.Expression | null>,
) {
	if (
		!constructCall.get('callee').isV8IntrinsicIdentifier({
			name: 'Construct',
		})
	) return null;

	const constructArgs = constructCall.get('arguments');
	if (constructArgs.length < 2) return null;

	const [constructorRef, receiver, ...constructorArgs] = constructArgs;
	if (!constructorRef.isExpression()) return null;

	const receiverMatchesThisRegister = receiver.isIdentifier({
		name: thisName,
	});
	const receiverMatchesCreateThis = receiver.isExpression() &&
		createThisMatchesConstructTarget(
				receiver.node,
				constructorRef.node,
			) != null;
	if (!receiverMatchesThisRegister && !receiverMatchesCreateThis) {
		return null;
	}

	if (
		thisInit?.node &&
		createThisMatchesConstructTarget(
				thisInit.node,
				constructorRef.node,
			) == null
	) return null;

	const args = constructorArgs.flatMap((arg) =>
		arg.isExpression() || arg.isSpreadElement()
			? [t.cloneNode(arg.node, true)]
			: []
	);

	return t.newExpression(t.cloneNode(constructorRef.node, true), args);
}

function standaloneConstructNewExpression(call: NodePath<t.CallExpression>) {
	const args = call.get('arguments');
	if (args.length < 2) return null;

	const [constructorRef, receiver, ...constructorArgs] = args;
	if (!constructorRef.isExpression()) return null;
	if (
		!isUndefinedNode(receiver.node) &&
		!(
			receiver.isExpression() &&
			createThisMatchesConstructTarget(
					receiver.node,
					constructorRef.node,
				) != null
		)
	) return null;

	const newArgs = constructorArgs.flatMap((arg) =>
		arg.isExpression() || arg.isSpreadElement()
			? [t.cloneNode(arg.node, true)]
			: []
	);
	return t.newExpression(t.cloneNode(constructorRef.node, true), newArgs);
}

function resolvedPrototypeExpression(
	expr: t.Expression,
	scope: NodePath['scope'],
) {
	const resolved = t.isIdentifier(expr)
		? constIdentifierInit(scope, expr.name)?.node ?? expr
		: expr;
	if (!t.isMemberExpression(resolved, { computed: false })) return null;
	if (!t.isExpression(resolved.object)) return null;
	if (!t.isIdentifier(resolved.property, { name: 'prototype' })) return null;
	return resolved;
}

function objectCreatePrototypeArgument(
	expr: t.Expression,
	scope: NodePath['scope'],
) {
	if (!t.isCallExpression(expr)) return null;
	const callee = expr.callee;
	if (!t.isMemberExpression(callee, { computed: false })) return null;
	if (!t.isIdentifier(callee.object, { name: 'Object' })) return null;
	if (!t.isIdentifier(callee.property, { name: 'create' })) return null;
	if (expr.arguments.length !== 1) return null;

	const [prototype] = expr.arguments;
	if (!t.isExpression(prototype)) return null;
	return resolvedPrototypeExpression(prototype, scope);
}

function callReceivesArgument(
	call: t.CallExpression,
	expectedArg: t.Expression,
	scope: NodePath['scope'],
) {
	return call.arguments.some((arg) => {
		if (!t.isExpression(arg)) return false;
		const resolved = resolvedPrototypeExpression(arg, scope) ?? arg;
		return expressionsEqual(resolved, expectedArg);
	});
}

function selectObjectCallWithPrototypeArgument(
	call: NodePath<t.CallExpression>,
) {
	const args = call.node.arguments;
	if (args.length !== 2) return null;

	const [receiver, selected] = args;
	if (!t.isExpression(receiver) || !t.isCallExpression(selected)) {
		return null;
	}

	const prototype = objectCreatePrototypeArgument(receiver, call.scope);
	if (!prototype) return null;
	if (!callReceivesArgument(selected, prototype, call.scope)) return null;

	return t.cloneNode(selected, true);
}

function stripGeneratorCompletionReturnAfterYield(
	body: t.Statement[],
	completionRegisters: Set<string>,
) {
	let changed = false;

	for (let i = body.length - 1; i > 0; i--) {
		const stmt = body[i];
		const prev = body[i - 1];
		if (!t.isReturnStatement(stmt)) continue;
		if (!t.isIdentifier(stmt.argument)) continue;
		if (!completionRegisters.has(stmt.argument.name)) continue;
		if (i === body.length - 1) {
			body.splice(i, 1);
			changed = true;
			continue;
		}
		if (
			!t.isExpressionStatement(prev) ||
			!t.isYieldExpression(prev.expression)
		) continue;

		body.splice(i, 1);
		changed = true;
	}

	return changed;
}

/**
 * A parameter binds its register names, so a hoisted `let` for the same
 * register redeclares them: `function ({ error: r10_2 }) { let r10_2; }` is
 * not valid JavaScript. The parameter is the binding, so the hoisted
 * declarator goes.
 *
 * Only a declarator without an initializer, and only at the top level of the
 * body: one with a value still has to assign it, and a nested block legally
 * shadows a parameter. `var` is left alone — redeclaring a parameter with it
 * is allowed.
 */
function removeParameterShadowedDeclarations(
	body: t.Statement[],
	params: readonly t.Node[],
) {
	const bound = new Set<string>();
	for (const param of params) {
		for (const name of Object.keys(t.getBindingIdentifiers(param))) {
			bound.add(name);
		}
	}
	if (bound.size === 0) return;
	for (let index = body.length - 1; index >= 0; index--) {
		const statement = body[index];
		if (
			!t.isVariableDeclaration(statement) || statement.kind === 'var'
		) continue;
		const kept = statement.declarations.filter((declaration) =>
			declaration.init != null || !t.isIdentifier(declaration.id) ||
			!bound.has(declaration.id.name)
		);
		if (kept.length === statement.declarations.length) continue;
		if (kept.length === 0) body.splice(index, 1);
		else statement.declarations = kept;
	}
}

function normalizeDuplicateRegisterDeclarationsInBody(
	body: t.Statement[],
	context = 'body',
	sharedNames?: ReadonlySet<string>,
) {
	preserveDuplicateRegisterScopesInBody(body, {
		context,
		sharedNames,
		onPreserve(event) {
			debugDupSSA('preserve IR duplicate register scope', event);
		},
	});
	const assignedNames = new Set<string>();
	for (const stmt of body) {
		t.traverseFast(stmt, (node) => {
			if (
				t.isAssignmentExpression(node) &&
				t.isIdentifier(node.left) &&
				/^r\d+_\d+$/.test(node.left.name)
			) {
				assignedNames.add(node.left.name);
			}
			if (
				t.isUpdateExpression(node) &&
				t.isIdentifier(node.argument) &&
				/^r\d+_\d+$/.test(node.argument.name)
			) {
				assignedNames.add(node.argument.name);
			}
		});
	}
	const declarations = new Map<string, t.VariableDeclaration>();
	for (let i = 0; i < body.length; i++) {
		const stmt = body[i];
		if (t.isBlockStatement(stmt)) {
			normalizeDuplicateRegisterDeclarationsInBody(
				stmt.body,
				`${context}.block`,
				sharedNames,
			);
			continue;
		}
		if (t.isSwitchStatement(stmt)) {
			const hoisted = normalizeDuplicateSwitchRegisterDeclarations(
				stmt,
				`${context}.switch@${i}`,
			);
			if (hoisted.length > 0) {
				body.splice(i, 0, ...hoisted);
				i += hoisted.length;
			}
			for (const switchCase of stmt.cases) {
				normalizeDuplicateRegisterDeclarationsInBody(
					switchCase.consequent,
					`${context}.switch@${i}.case:${
						switchCase.test?.type ?? 'default'
					}`,
					sharedNames,
				);
			}
		}
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				normalizeDuplicateRegisterDeclarationsInBody(
					stmt.consequent.body,
					`${context}.if.consequent`,
					sharedNames,
				);
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				normalizeDuplicateRegisterDeclarationsInBody(
					stmt.alternate.body,
					`${context}.if.alternate`,
					sharedNames,
				);
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isDoWhileStatement(stmt) ||
				t.isForStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			normalizeDuplicateRegisterDeclarationsInBody(
				stmt.body.body,
				`${context}.${stmt.type}.body`,
				sharedNames,
			);
		} else if (t.isTryStatement(stmt)) {
			normalizeDuplicateRegisterDeclarationsInBody(
				stmt.block.body,
				`${context}.try`,
				sharedNames,
			);
			if (stmt.handler) {
				normalizeDuplicateRegisterDeclarationsInBody(
					stmt.handler.body.body,
					`${context}.catch`,
					sharedNames,
				);
			}
			if (stmt.finalizer) {
				normalizeDuplicateRegisterDeclarationsInBody(
					stmt.finalizer.body,
					`${context}.finally`,
					sharedNames,
				);
			}
		}

		if (
			!t.isVariableDeclaration(stmt) ||
			stmt.declarations.length !== 1
		) continue;
		const decl = stmt.declarations[0];
		if (
			t.isVariableDeclarator(decl) &&
			t.isPatternLike(decl.id) &&
			decl.init &&
			t.isExpression(decl.init)
		) {
			const ids: t.Identifier[] = [];
			t.traverseFast(decl.id, (node) => {
				if (t.isIdentifier(node) && /^r\d+_\d+$/.test(node.name)) {
					ids.push(node);
				}
			});
			if (ids.some((id) => assignedNames.has(id.name))) {
				stmt.kind = 'let';
			}
			const duplicates = ids.filter((id) => declarations.has(id.name));
			if (duplicates.length > 0) {
				for (const id of duplicates) {
					const previous = declarations.get(id.name);
					if (previous?.kind === 'const') previous.kind = 'let';
				}
				const newIds = ids.filter((id) => !declarations.has(id.name));
				if (newIds.length > 0) {
					const hoist = t.variableDeclaration(
						'let',
						newIds.map((id) =>
							t.variableDeclarator(t.cloneNode(id))
						),
					);
					body.splice(i, 0, hoist);
					for (const id of newIds) declarations.set(id.name, hoist);
					i++;
				}
				body[i] = t.expressionStatement(t.assignmentExpression(
					'=',
					t.cloneNode(decl.id) as t.LVal,
					t.cloneNode(decl.init, true),
				));
				continue;
			}
			for (const id of ids) {
				if (!declarations.has(id.name)) declarations.set(id.name, stmt);
			}
			continue;
		}
		if (
			!t.isVariableDeclarator(decl) ||
			!t.isIdentifier(decl.id) ||
			!/^r\d+_\d+$/.test(decl.id.name)
		) continue;
		if (assignedNames.has(decl.id.name)) stmt.kind = 'let';

		const previous = declarations.get(decl.id.name);
		if (!previous) {
			declarations.set(decl.id.name, stmt);
			continue;
		}

		debugDupSSA('rewrite IR duplicate register', {
			context,
			name: decl.id.name,
			index: i,
			previousKind: previous.kind,
			currentKind: stmt.kind,
			previousInit: previous.declarations[0]?.init?.type ?? null,
			currentInit: decl.init?.type ?? null,
		});
		if (previous.kind === 'const') previous.kind = 'let';
		if (decl.init && t.isExpression(decl.init)) {
			body[i] = t.expressionStatement(t.assignmentExpression(
				'=',
				t.cloneNode(decl.id),
				t.cloneNode(decl.init, true),
			));
		} else {
			body.splice(i, 1);
			i--;
		}
	}
}

function statementAssignsName(stmt: t.Statement, name: string): boolean {
	let found = false;
	t.traverseFast(stmt, (node) => {
		if (found) return t.traverseFast.skip;
		if (
			t.isAssignmentExpression(node) &&
			t.isIdentifier(node.left, { name })
		) found = true;
		if (
			t.isUpdateExpression(node) &&
			t.isIdentifier(node.argument, { name })
		) found = true;
	});
	return found;
}

/**
 * Whether an assignment to `name` separates `declaration` from any of its
 * `references`.
 *
 * Asked once for the whole reference set, not once per reference. Every
 * reference shares the declaration's position and the caller only needs to know
 * whether *some* reference is crossed, so the question collapses to one: is
 * `name` assigned anywhere between the declaration and the furthest reference?
 *
 * Asking per reference re-walked the same span once for each of them, and each
 * step walks a statement's whole subtree. Over the handful of statements this
 * usually spans that costs nothing; over a container holding tens of thousands
 * -- the Metro root of a large bundle has one block of 83,000 statements -- it
 * is quadratic with a tree walk per step, and profiling put about two thirds of
 * the time spent lifting that function right here.
 *
 * Deliberately not a cached index over the container. Answers would then have
 * to survive the mutations this runs among, and the dangerous direction is
 * silent: a statement replaced by an assignment adds a crossing the index does
 * not know about, and a missed crossing lets the caller move a declaration it
 * should have left alone. One scan per declaration needs no such reasoning.
 */
function safeStatementParent(path: NodePath): NodePath | null {
	let current: NodePath | null = path;
	while (current && !t.isStatement(current.node)) {
		current = current.parentPath;
	}
	return current;
}

function referencesCrossAssignmentToName(
	declaration: NodePath,
	references: readonly NodePath[],
	name: string,
): boolean {
	const declarationStmt = safeStatementParent(declaration);
	if (!declarationStmt) return false;
	const container = declarationStmt.container;
	if (!Array.isArray(container)) return false;
	const start = declarationStmt.key;
	if (typeof start !== 'number') return false;

	// Scanned once, in step with the references, never rescanned and never
	// ahead of need: each reference only extends the span, and the first
	// crossing found answers for all of them. Sweeping every reference up front
	// to find the furthest would give the same answer but forfeit the early
	// exit, which is what made the per-reference version cheap whenever a
	// crossing sits close to the declaration.
	let scannedTo = start;
	for (const reference of references) {
		const referenceStmt = safeStatementParent(reference);
		if (!referenceStmt) continue;
		if (referenceStmt.parentPath !== declarationStmt.parentPath) continue;
		const end = referenceStmt.key;
		if (typeof end !== 'number' || end - 1 <= scannedTo) continue;
		for (let i = scannedTo + 1; i < end; i++) {
			const stmt = container[i];
			if (t.isStatement(stmt) && statementAssignsName(stmt, name)) {
				return true;
			}
		}
		scannedTo = end - 1;
	}
	return false;
}

/**
 * Would inlining an init that mutates `name` move that mutation across a read
 * of it?
 *
 * `const old = i--` is only substitutable into its use while nothing between
 * the two looks at `i`. Otherwise the read that used to see the old value
 * would see the new one -- and the reference's own statement counts, since
 * `[i, old]` becoming `[i, i--]` reorders the pair.
 */
function referencesCrossUseOfName(
	declaration: NodePath,
	references: readonly NodePath[],
	name: string,
): boolean {
	const declarationStmt = safeStatementParent(declaration);
	if (!declarationStmt) return true;
	const container = declarationStmt.container;
	if (!Array.isArray(container)) return true;
	const start = declarationStmt.key;
	if (typeof start !== 'number') return true;

	let scannedTo = start;
	for (const reference of references) {
		const referenceStmt = safeStatementParent(reference);
		if (!referenceStmt) return true;
		// A reference in another statement list is not ordered against the
		// declaration by anything this scan can see.
		if (referenceStmt.parentPath !== declarationStmt.parentPath) {
			return true;
		}
		const end = referenceStmt.key;
		if (typeof end !== 'number' || end < start) return true;
		for (let i = Math.max(scannedTo + 1, start + 1); i <= end; i++) {
			const stmt = container[i];
			if (
				t.isStatement(stmt) && identifierUseCount([stmt], name) > 0
			) return true;
		}
		scannedTo = Math.max(scannedTo, end);
	}
	return false;
}

/** The register an init mutates in passing, if it mutates one. */
function initMutatesName(init: NodePath<t.Expression | null>): string | null {
	const node = init.node;
	if (t.isUpdateExpression(node) && t.isIdentifier(node.argument)) {
		return node.argument.name;
	}
	if (t.isAssignmentExpression(node) && t.isIdentifier(node.left)) {
		return node.left.name;
	}
	return null;
}

function bindingPlacementAudit(
	result: BindingPlacementTreeResult,
): RecursiveCFGBindingPlacementAudit {
	const reasons: Record<string, number> = {};
	for (const entry of result.entries) {
		for (const placement of entry.result.placed.values()) {
			for (const reason of placement.reasons) {
				reasons[reason] = (reasons[reason] ?? 0) + 1;
			}
		}
	}
	return {
		reasons,
		placed: result.placed,
		localized: result.localized,
		unresolved: result.unresolved,
	};
}

function meaningfulBindingPlacementAudit(
	audit: RecursiveCFGBindingPlacementAudit,
): boolean {
	return audit.placed > 0 || audit.unresolved > 0;
}

function mergeBindingPlacementAudits(
	current: RecursiveCFGBindingPlacementAudit | undefined,
	next: RecursiveCFGBindingPlacementAudit,
): RecursiveCFGBindingPlacementAudit {
	if (!current) {
		return {
			...next,
			reasons: { ...next.reasons },
		};
	}
	const reasons = { ...current.reasons };
	for (const [reason, count] of Object.entries(next.reasons)) {
		reasons[reason] = (reasons[reason] ?? 0) + count;
	}
	return {
		reasons,
		placed: current.placed + next.placed,
		localized: current.localized + next.localized,
		unresolved: current.unresolved + next.unresolved,
	};
}

function hasUnboundGeneratedRegister(program: t.Program): boolean {
	const wrapped = t.file(t.cloneNode(program, true));
	let unbound = false;
	try {
		traverse(wrapped, {
			Identifier(path) {
				if (!/^r\d+_\d+$/.test(path.node.name)) return;
				const isAssignmentTarget =
					(path.parentPath.isAssignmentExpression() &&
						path.key === 'left') ||
					(path.parentPath.isUpdateExpression() &&
						path.key === 'argument');
				if (!path.isReferencedIdentifier() && !isAssignmentTarget) {
					return;
				}
				if (path.scope.hasBinding(path.node.name)) return;
				unbound = true;
				path.stop();
			},
		});
	} catch {
		// Invalid binding structure (for example a duplicate declaration) is not
		// safe to install as the function's canonical materialized body.
		return true;
	} finally {
		traverse.cache.clear();
	}
	return unbound;
}

function hasUnwrittenGeneratedRegister(program: t.Program): boolean {
	const wrapped = t.file(t.cloneNode(program, true));
	let unwritten = false;
	try {
		traverse(wrapped, {
			Identifier(path) {
				if (
					!/^r\d+_\d+$/.test(path.node.name) ||
					!path.isReferencedIdentifier()
				) return;
				const binding = path.scope.getBinding(path.node.name);
				if (!binding?.path.isVariableDeclarator()) return;
				const declaration = binding.path.parentPath;
				const iterationBinding = declaration.isVariableDeclaration() &&
					declaration.key === 'left' &&
					(declaration.parentPath.isForInStatement() ||
						declaration.parentPath.isForOfStatement());
				if (
					binding.path.node.init != null ||
					iterationBinding ||
					binding.constantViolations.length > 0
				) return;
				unwritten = true;
				path.stop();
			},
		});
	} catch {
		// Treat an invalid scope tree exactly like an unbound register: neither is
		// safe to install as the function's canonical body.
		return true;
	} finally {
		traverse.cache.clear();
	}
	return unwritten;
}

function hoistUnboundGeneratedBindings(
	program: t.Program,
	requireExistingDeclaration = false,
): boolean {
	type Owner = t.Program | t.BlockStatement;
	const unboundByOwner = new Map<Owner, Set<string>>();
	const declarationsByOwner = new Map<
		Owner,
		Map<string, number>
	>();
	const wrapped = t.file(program);
	const ownerFor = (path: NodePath): Owner | null => {
		const functionPath = path.getFunctionParent();
		if (!functionPath) return program;
		return t.isBlockStatement(functionPath.node.body)
			? functionPath.node.body
			: null;
	};
	traverse.cache.clear();
	traverse(wrapped, {
		VariableDeclaration(path) {
			if (!path.inList) return;
			const owner = ownerFor(path);
			if (!owner) return;
			const declarations = declarationsByOwner.get(owner) ?? new Map();
			for (const declarator of path.node.declarations) {
				if (
					!t.isIdentifier(declarator.id) ||
					!/^r\d+_\d+$/.test(declarator.id.name)
				) continue;
				declarations.set(
					declarator.id.name,
					(declarations.get(declarator.id.name) ?? 0) + 1,
				);
			}
			declarationsByOwner.set(owner, declarations);
		},
		Identifier(path) {
			const name = path.node.name;
			if (!/^r\d+_\d+$/.test(name)) return;
			const isAssignmentTarget =
				(path.parentPath.isAssignmentExpression() &&
					path.key === 'left') ||
				(path.parentPath.isUpdateExpression() &&
					path.key === 'argument');
			if (!path.isReferencedIdentifier() && !isAssignmentTarget) return;
			if (path.scope.hasBinding(name)) return;
			const owner = ownerFor(path);
			if (!owner) return;
			const names = unboundByOwner.get(owner) ?? new Set<string>();
			names.add(name);
			unboundByOwner.set(owner, names);
		},
	});
	traverse.cache.clear();

	const hoistedByOwner = new Map<Owner, Set<string>>();
	for (const [owner, names] of unboundByOwner) {
		const declarations = declarationsByOwner.get(owner) ?? new Map();
		const hoisted = new Set(
			[...names].filter((name) => {
				const count = declarations.get(name) ?? 0;
				// Recursive composition can emit one declaration per mutually
				// exclusive arm for the same SSA version. An outside reference proves
				// those declarations are placements of one function-wide binding, not
				// independent lexical values, so coalesce every occurrence into the
				// single hoisted declaration below. The generated SSA name keeps this
				// narrower than general JavaScript declaration repair.
				return !requireExistingDeclaration || count > 0;
			}),
		);
		if (hoisted.size > 0) hoistedByOwner.set(owner, hoisted);
	}
	if (hoistedByOwner.size === 0) return false;

	traverse(wrapped, {
		VariableDeclaration(path) {
			if (!path.inList) return;
			const owner = ownerFor(path);
			const hoisted = owner == null ? null : hoistedByOwner.get(owner);
			if (!hoisted) return;
			const replacements: t.Statement[] = [];
			let changed = false;
			for (const declarator of path.node.declarations) {
				if (
					t.isIdentifier(declarator.id) &&
					hoisted.has(declarator.id.name)
				) {
					changed = true;
					if (t.isExpression(declarator.init)) {
						replacements.push(t.expressionStatement(
							t.assignmentExpression(
								'=',
								t.cloneNode(declarator.id),
								t.cloneNode(declarator.init, true),
							),
						));
					}
					continue;
				}
				replacements.push(t.variableDeclaration(path.node.kind, [
					t.cloneNode(declarator, true),
				]));
			}
			if (changed) path.replaceWithMultiple(replacements);
		},
	});
	traverse.cache.clear();

	for (const [owner, names] of hoistedByOwner) {
		owner.body.unshift(t.variableDeclaration(
			'let',
			[...names].toSorted().map((name) =>
				t.variableDeclarator(t.identifier(name))
			),
		));
	}
	return true;
}

function normalizeDuplicateSwitchRegisterDeclarations(
	stmt: t.SwitchStatement,
	context = 'switch',
) {
	const counts = new Map<string, number>();
	for (const switchCase of stmt.cases) {
		for (const consequent of switchCase.consequent) {
			if (
				!t.isVariableDeclaration(consequent) ||
				consequent.declarations.length !== 1
			) continue;
			const decl = consequent.declarations[0];
			if (
				!t.isVariableDeclarator(decl) ||
				!t.isIdentifier(decl.id) ||
				!/^r\d+_\d+$/.test(decl.id.name)
			) continue;
			counts.set(decl.id.name, (counts.get(decl.id.name) ?? 0) + 1);
		}
	}
	const duplicateNames = new Set(
		[...counts].filter(([, count]) => count > 1).map(([name]) => name),
	);
	if (duplicateNames.size === 0) return [];
	debugDupSSA('rewrite IR switch duplicate registers', {
		context,
		names: [...duplicateNames].toSorted(),
		cases: stmt.cases.length,
	});

	for (const switchCase of stmt.cases) {
		for (let i = 0; i < switchCase.consequent.length; i++) {
			const consequent = switchCase.consequent[i];
			if (
				!t.isVariableDeclaration(consequent) ||
				consequent.declarations.length !== 1
			) continue;
			const decl = consequent.declarations[0];
			if (
				!t.isVariableDeclarator(decl) ||
				!t.isIdentifier(decl.id) ||
				!duplicateNames.has(decl.id.name)
			) continue;
			if (decl.init && t.isExpression(decl.init)) {
				switchCase.consequent[i] = t.expressionStatement(
					t.assignmentExpression(
						'=',
						t.cloneNode(decl.id),
						t.cloneNode(decl.init, true),
					),
				);
			} else {
				switchCase.consequent.splice(i, 1);
				i--;
			}
		}
	}

	return [...duplicateNames].toSorted().map((name) =>
		t.variableDeclaration('let', [
			t.variableDeclarator(t.identifier(name)),
		])
	);
}

function hasSmallTimerClosureFanIn(func: IRFunction): boolean {
	if (func.id === 0 || func.blocks.size > 8) return false;
	for (const block of func.blocks.values()) {
		for (const stmt of block.body as t.Statement[]) {
			let found = false;
			t.traverseFast(stmt, (node) => {
				if (found) return t.traverseFast.skip;
				if (
					t.isMemberExpression(node) &&
					t.isIdentifier(node.property) &&
					[
						'setTimeout',
						'clearTimeout',
						'nativeRuntimeScheduler',
					].includes(node.property.name)
				) {
					found = true;
					return t.traverseFast.skip;
				}
				if (!t.isCallExpression(node)) return;
				if (!t.isIdentifier(node.callee, { name: 'setTimeout' })) {
					return;
				}
				const [callback] = node.arguments;
				if (
					t.isCallExpression(callback) &&
					t.isV8IntrinsicIdentifier(callback.callee, {
						name: 'CreateClosure',
					})
				) {
					found = true;
					return t.traverseFast.skip;
				}
			});
			if (found) return true;
		}
	}
	return false;
}

function containsRecoveredDestructuring(node: t.Node): boolean {
	let found = false;
	t.traverseFast(node, (child) => {
		if (child.extra?.fromDestructuring) found = true;
	});
	return found;
}

function isEmptyDestructuringCatch(stmt: t.TryStatement): boolean {
	return !stmt.finalizer &&
		stmt.handler != null &&
		stmt.handler.body.body.length === 0 &&
		(!stmt.handler.param ||
			(t.isIdentifier(stmt.handler.param) &&
				/^e_\d+$/.test(stmt.handler.param.name))) &&
		containsRecoveredDestructuring(stmt.block);
}

function foldEmptyCatchFinallyWrapper(stmt: t.TryStatement) {
	if (
		!stmt.finalizer ||
		!stmt.handler ||
		stmt.handler.body.body.length !== 0 ||
		stmt.block.body.length !== 1
	) return null;
	const inner = stmt.block.body[0];
	if (!t.isTryStatement(inner) || inner.finalizer) return null;
	return t.tryStatement(
		t.cloneNode(inner.block, true),
		inner.handler ? t.cloneNode(inner.handler, true) : null,
		t.cloneNode(stmt.finalizer, true),
	);
}

function stringLiteralsInNode(node: t.Node): Set<string> {
	const literals = new Set<string>();
	t.traverseFast(node, (child) => {
		if (t.isStringLiteral(child)) literals.add(child.value);
	});
	return literals;
}

function statementEndsWithThrow(stmt: t.Statement): boolean {
	if (t.isThrowStatement(stmt)) return true;
	if (t.isBlockStatement(stmt)) {
		const last = stmt.body.at(-1);
		return !!last && statementEndsWithThrow(last);
	}
	if (t.isTryStatement(stmt)) {
		return !!stmt.finalizer && statementEndsWithThrow(stmt.finalizer);
	}
	return false;
}

function stripConsecutiveRethrowFinalizerCopy(body: t.Statement[]) {
	for (let i = 0; i < body.length - 1; i++) {
		const previous = body[i];
		const next = body[i + 1];
		if (!t.isTryStatement(previous) || !previous.finalizer) continue;
		if (!statementEndsWithThrow(next)) continue;

		const finalizerStrings = stringLiteralsInNode(previous.finalizer);
		if (finalizerStrings.size === 0) continue;
		const nextStrings = stringLiteralsInNode(next);
		if (![...finalizerStrings].some((value) => nextStrings.has(value))) {
			continue;
		}

		body.splice(i + 1, 1);
		return true;
	}
	return false;
}

function stripStatementsAfterTerminal(body: t.Statement[]) {
	for (let i = 0; i < body.length - 1; i++) {
		if (!statementAlwaysTerminates(body[i])) continue;
		body.splice(i + 1);
		return true;
	}
	return false;
}

function assignmentStatement(stmt: t.Statement | undefined) {
	if (!stmt || !t.isExpressionStatement(stmt)) return;
	if (!t.isAssignmentExpression(stmt.expression, { operator: '=' })) return;
	return stmt.expression;
}

function isEnvironmentAssignmentTarget(expr: t.Expression) {
	if (t.isIdentifier(expr) && isEnvironmentSlotName(expr.name)) {
		return true;
	}
	return !!envMemberAccess(expr);
}

function removeOverwrittenEnvironmentStores(body: t.Statement[]) {
	for (let i = 0; i < body.length - 1; i++) {
		const first = assignmentStatement(body[i]);
		const second = assignmentStatement(body[i + 1]);
		if (!first || !second) continue;
		if (!t.isExpression(first.left) || !t.isExpression(second.left)) {
			continue;
		}
		if (!isEnvironmentAssignmentTarget(first.left)) continue;
		if (!expressionsEqual(first.left, second.left)) continue;
		body.splice(i, 1);
		return true;
	}
	return false;
}

function isGeneratedName(name: string) {
	return /^(?:r\d+_\d+|e_\d+)$/.test(name) || isEnvironmentSlotName(name);
}

function finalizerFeatureSignature(statement: t.Statement) {
	const features: string[] = [];
	t.traverseFast(statement, (node) => {
		if (t.isIdentifier(node)) {
			if (!isGeneratedName(node.name) && node.name !== 'undefined') {
				features.push(`id:${node.name}`);
			}
			return;
		}
		if (t.isNumericLiteral(node)) {
			features.push(`num:${node.value}`);
			return;
		}
		if (t.isStringLiteral(node)) {
			features.push(`str:${node.value}`);
		}
	});
	return features.sort().join('|');
}

function finalizerCopyLooksEquivalent(
	catchCopy: t.Statement,
	normalCopy: t.Statement,
) {
	if (
		JSON.stringify(comparableAst(catchCopy)) ===
			JSON.stringify(comparableAst(normalCopy))
	) return true;
	if (catchCopy.type !== normalCopy.type) return false;
	const catchFeatures = finalizerFeatureSignature(catchCopy);
	return catchFeatures.length > 0 &&
		catchFeatures === finalizerFeatureSignature(normalCopy);
}

function bodyReferencesIdentifier(body: t.Statement[], name: string) {
	let found = false;
	for (const stmt of body) {
		t.traverseFast(stmt, (node) => {
			if (t.isIdentifier(node, { name })) found = true;
		});
		if (found) return true;
	}
	return false;
}

function rewriteRethrowCatchTrailingFinalizer(body: t.Statement[]) {
	for (let i = 0; i < body.length - 2; i++) {
		const stmt = body[i];
		const trailingFinalizer = body[i + 1];
		const terminal = body[i + 2];
		if (
			!t.isTryStatement(stmt) ||
			stmt.finalizer ||
			!stmt.handler ||
			!t.isIdentifier(stmt.handler.param) ||
			!statementAlwaysTerminates(terminal)
		) continue;

		const catchBody = stmt.handler.body.body;
		const throwStmt = catchBody.at(-1);
		if (
			!t.isThrowStatement(throwStmt) ||
			!t.isIdentifier(throwStmt.argument, {
				name: stmt.handler.param.name,
			})
		) continue;

		const catchFinalizer = catchBody.slice(0, -1);
		if (catchFinalizer.length !== 1) continue;
		if (bodyReferencesIdentifier(catchFinalizer, stmt.handler.param.name)) {
			continue;
		}
		if (
			!finalizerCopyLooksEquivalent(
				catchFinalizer[0],
				trailingFinalizer,
			)
		) continue;

		stmt.block.body.push(t.cloneNode(terminal, true));
		body.splice(
			i,
			3,
			t.tryStatement(
				stmt.block,
				null,
				t.blockStatement([t.cloneNode(trailingFinalizer, true)]),
			),
		);
		return true;
	}
	return false;
}

function uniqueFingerprintSequences(sequences: string[][]): string[][] {
	const seen = new Set<string>();
	const result: string[][] = [];
	for (const sequence of sequences) {
		const key = JSON.stringify(sequence);
		if (seen.has(key)) continue;
		seen.add(key);
		result.push(sequence);
	}
	return result;
}

function applyFinalizerCleanupPlan(func: IRFunction): boolean {
	const plan = func.exceptions.finalizerCleanupPlan();
	const enclosingEdgeActionCount = Math.max(
		plan.enclosingEdgeActionCount,
		func.recursiveCFGSummary?.finalizerEdgeActions.filter((action) =>
			action.kind === 'enclosing-copy'
		).length ?? 0,
	);
	const embeddedCatchReplacementFingerprints = new Set(
		plan.embeddedCatchActions.flatMap((action) =>
			action.replacementFingerprints
		),
	);
	const embeddedCatchTerminalSuffixFingerprints = uniqueFingerprintSequences(
		plan.embeddedCatchActions.flatMap((action) =>
			action.terminalSuffixFingerprints
		),
	);
	const byBlock = new AddressMap<
		Array<{ start: number; end: number; replacement?: t.Statement }>
	>();
	for (const range of plan.removeRanges) {
		byBlock.getWithDefault(range.block, () => []).push({
			start: range.start,
			end: range.end,
		});
	}
	for (const range of plan.replaceWithReturnRanges) {
		byBlock.getWithDefault(range.block, () => []).push({
			start: range.start,
			end: range.end,
			replacement: t.returnStatement(),
		});
	}

	let changed = false;
	for (const [blockAddr, ranges] of byBlock) {
		const block = func.blocks.get(blockAddr);
		if (!block) continue;
		const body = block.body as t.Statement[];
		for (
			const range of ranges.toSorted((left, right) =>
				right.start - left.start || right.end - left.end
			)
		) {
			if (range.start < 0 || range.end > body.length) continue;
			if (range.start >= range.end) continue;
			const replacement = range.replacement
				? [t.cloneNode(range.replacement, true)]
				: [];
			// Only real progress counts. The plan is recomputed from scratch
			// on every call, so a range whose replacement is identical to what
			// is already there gets re-identified forever -- splicing a bare
			// `return;` over a bare `return;` mutates nothing while reporting
			// that it did. The enclosing `do { ... } while (changed)` then
			// never exits: function #14219 of the 127k-function bundle spun
			// 15,225 times on block 0x3b6 range [2,3), pinning a lift worker
			// indefinitely with no diagnostic.
			const removed = body.slice(range.start, range.end);
			const rewritesNothing = removed.length === replacement.length &&
				removed.every((statement, index) =>
					statementFingerprint(statement) ===
						statementFingerprint(replacement[index])
				);
			body.splice(range.start, range.end - range.start, ...replacement);
			// The splice still happens -- it is idempotent here, and skipping
			// it would change which node object survives -- but a rewrite that
			// produced an identical body must not claim progress.
			if (!rewritesNothing) changed = true;
		}
		if (embeddedCatchReplacementFingerprints.size > 0) {
			changed = replaceEmbeddedCatchFinalizerCopies(
				body,
				embeddedCatchReplacementFingerprints,
				embeddedCatchTerminalSuffixFingerprints,
			) || changed;
		}
	}
	if (embeddedCatchReplacementFingerprints.size > 0) {
		for (const [blockAddr, block] of func.blocks) {
			if (byBlock.has(blockAddr)) continue;
			changed = replaceEmbeddedCatchFinalizerCopies(
				block.body as t.Statement[],
				embeddedCatchReplacementFingerprints,
				embeddedCatchTerminalSuffixFingerprints,
			) || changed;
		}
	}
	if (enclosingEdgeActionCount > 0) {
		for (const block of func.blocks.values()) {
			changed = stripOwnedAdjacentRethrowFinalizerCopies(
				block.body as t.Statement[],
				enclosingEdgeActionCount,
			) || changed;
			changed = stripOwnedTerminalEnclosingFinalizerCopies(
				block.body as t.Statement[],
				enclosingEdgeActionCount,
			) || changed;
		}
	}
	return changed;
}

function replaceEmbeddedCatchFinalizerCopies(
	body: t.Statement[],
	fingerprints: Set<string>,
	terminalSuffixes: string[][],
): boolean {
	let changed = false;

	const scanStatementBody = (statements: t.Statement[]) => {
		for (const statement of statements) scanStatement(statement);
	};

	const scanCatchBody = (statements: t.Statement[]) => {
		for (let i = 0; i < statements.length; i++) {
			const statement = statements[i];
			if (
				fingerprints.has(statementFingerprint(statement)) ||
				terminalFinalizerCopyMatches(statement, terminalSuffixes)
			) {
				statements.splice(i, 1, t.returnStatement());
				changed = true;
				continue;
			}
			scanStatement(statement);
		}
	};

	const scanStatement = (statement: t.Statement) => {
		if (t.isBlockStatement(statement)) {
			scanStatementBody(statement.body);
			return;
		}
		if (t.isTryStatement(statement)) {
			scanStatementBody(statement.block.body);
			if (statement.handler) {
				scanCatchBody(statement.handler.body.body);
			}
			if (statement.finalizer) {
				scanStatementBody(statement.finalizer.body);
			}
			return;
		}
		if (t.isLabeledStatement(statement)) {
			scanStatement(statement.body);
			return;
		}
		if (
			t.isWhileStatement(statement) ||
			t.isDoWhileStatement(statement) ||
			t.isForStatement(statement) ||
			t.isForInStatement(statement) ||
			t.isForOfStatement(statement)
		) {
			if (t.isStatement(statement.body)) scanStatement(statement.body);
			return;
		}
		if (t.isIfStatement(statement)) {
			scanStatement(statement.consequent);
			if (statement.alternate) scanStatement(statement.alternate);
			return;
		}
		if (t.isSwitchStatement(statement)) {
			for (const switchCase of statement.cases) {
				scanStatementBody(switchCase.consequent);
			}
		}
	};

	scanStatementBody(body);
	return changed;
}

function terminalFinalizerCopyMatches(
	statement: t.Statement,
	terminalSuffixes: string[][],
): boolean {
	if (terminalSuffixes.length === 0) return false;
	if (!statementAlwaysTerminates(statement)) return false;
	return terminalStatementSuffixes(statement).some((suffix) =>
		terminalSuffixes.some((target) =>
			target.length === suffix.length &&
			target.every((fingerprint, index) => fingerprint === suffix[index])
		)
	);
}

function terminalStatementSuffixes(statement: t.Statement): string[][] {
	const result: string[][] = [];
	const addTail = (statements: t.Statement[]) => {
		if (statements.length === 0) return;
		const last = statements.at(-1)!;
		if (t.isReturnStatement(last) || t.isThrowStatement(last)) {
			result.push(
				statements.slice(Math.max(0, statements.length - 2)).map(
					statementFingerprint,
				),
			);
		}
		result.push(...terminalStatementSuffixes(last));
	};

	if (t.isBlockStatement(statement)) {
		addTail(statement.body);
	} else if (t.isTryStatement(statement)) {
		addTail(statement.block.body);
		if (statement.handler) addTail(statement.handler.body.body);
		if (statement.finalizer) addTail(statement.finalizer.body);
	} else if (t.isIfStatement(statement)) {
		result.push(...terminalStatementSuffixes(statement.consequent));
		if (statement.alternate) {
			result.push(...terminalStatementSuffixes(statement.alternate));
		}
	} else if (t.isLabeledStatement(statement)) {
		result.push(...terminalStatementSuffixes(statement.body));
	}

	return result;
}

function normalizeGlobalObjectRegisterUses(func: IRFunction) {
	const globalObjectNames = new Set<string>();
	const undefinedNames = new Set<string>();
	for (const block of func.ssa.basicBlocks.values()) {
		for (const instr of block.ssaInstructions) {
			if (!('defs' in instr)) continue;
			if (!('destination' in instr.defs)) continue;
			const destination = instr.defs.destination;
			if (destination == null) continue;
			const name = `r${destination.index}_${destination.version}`;
			if (instr.instruction === 'GetGlobalObject') {
				globalObjectNames.add(name);
			} else if (
				instr.instruction === 'LoadConst' &&
				instr.value === undefined
			) {
				undefinedNames.add(name);
			}
		}
	}
	if (globalObjectNames.size === 0 && undefinedNames.size === 0) {
		return false;
	}

	let changed = false;
	for (const block of func.blocks.values()) {
		for (const stmt of block.body) {
			t.traverseFast(stmt as t.Node, (node) => {
				if (!t.isCallExpression(node)) return;
				if (
					t.isV8IntrinsicIdentifier(node.callee, {
						name: 'TryGetById',
					})
				) {
					const [object] = node.arguments;
					if (
						t.isIdentifier(object) &&
						globalObjectNames.has(object.name)
					) {
						node.arguments[0] = t.identifier('global');
						changed = true;
					}
				}
				if (
					t.isMemberExpression(node.callee, {
						computed: false,
					}) &&
					t.isIdentifier(node.callee.property, { name: 'call' }) &&
					t.isIdentifier(node.arguments[0]) &&
					undefinedNames.has(node.arguments[0].name)
				) {
					node.arguments[0] = t.identifier('undefined');
					changed = true;
				}
			});
		}
	}
	return changed;
}

function isYieldUndefinedStatement(stmt: t.Statement | undefined) {
	return !!stmt &&
		t.isExpressionStatement(stmt) &&
		t.isYieldExpression(stmt.expression, { delegate: false }) &&
		isUndefinedNode(stmt.expression.argument);
}

function containsPhiCall(root: t.Node): boolean {
	if (t.isFunction(root)) return false;
	let found = false;
	t.traverseFast(root, (node) => {
		if (t.isFunction(node)) return t.traverseFast.skip;
		if (
			t.isCallExpression(node) &&
			t.isV8IntrinsicIdentifier(node.callee, { name: 'Phi' })
		) found = true;
	});
	return found;
}

function phiOperandNames(root: t.Node): Set<string> {
	const names = new Set<string>();
	t.traverseFast(root, (node) => {
		if (t.isFunction(node)) return t.traverseFast.skip;
		if (
			!t.isCallExpression(node) ||
			!t.isV8IntrinsicIdentifier(node.callee, { name: 'Phi' })
		) return;
		for (const arg of node.arguments) {
			if (!t.isExpression(arg)) continue;
			t.traverseFast(arg, (candidate) => {
				if (t.isFunction(candidate)) return t.traverseFast.skip;
				if (
					t.isIdentifier(candidate) &&
					/^r\d+_\d+$/.test(candidate.name)
				) names.add(candidate.name);
			});
		}
	});
	return names;
}

/**
 * Drop a statement without reindexing its siblings.
 *
 * `NodePath.remove()` splices the container and then walks every cached
 * sibling path to correct its `key`, which is linear in the number of
 * statements for each removal. SSA register inlining removes one declaration
 * per inlined register -- 49,357 of them on the v96 main sample, out of one
 * materialized block body -- so that walk was 45% of the whole decompile.
 *
 * Above `MIN_DEFERRED_REMOVAL_STATEMENTS`, the statement is replaced with an
 * `EmptyStatement` instead: every sibling index stays valid, so the cost is
 * constant, and `stripEmptyStatements` sweeps the holes before the block is
 * committed. Smaller bodies keep `remove()` exactly as it was -- comments
 * shared with siblings, parent removal hooks, and no placeholder standing in
 * for the statement mid-traversal -- because the walk costs nothing there and
 * shape-matching reducers work on bodies that size.
 */
const MIN_DEFERRED_REMOVAL_STATEMENTS = 256;

function removeStatementWithoutReindex(path: NodePath<t.Statement>): void {
	const container = path.container;
	if (
		!Array.isArray(container) ||
		container.length < MIN_DEFERRED_REMOVAL_STATEMENTS
	) {
		path.remove();
		return;
	}
	for (const name of Object.keys(path.getBindingIdentifiers())) {
		path.scope.removeBinding(name);
	}
	path.replaceWith(t.emptyStatement());
}

/**
 * Sweep the holes `removeStatementWithoutReindex` leaves behind.
 *
 * An `EmptyStatement` carrying a comment is left alone: Metro module
 * extraction uses exactly that as a boundary marker, and a comment is the only
 * thing an empty statement can still be carrying.
 */
function stripEmptyStatements(root: t.Node): void {
	const droppable = (statement: t.Statement) =>
		t.isEmptyStatement(statement) &&
		(statement.leadingComments?.length ?? 0) === 0 &&
		(statement.innerComments?.length ?? 0) === 0 &&
		(statement.trailingComments?.length ?? 0) === 0;
	t.traverseFast(root, (node) => {
		if (t.isProgram(node) || t.isBlockStatement(node)) {
			if (!node.body.some(droppable)) return;
			node.body = node.body.filter((statement) => !droppable(statement));
			return;
		}
		if (!t.isSwitchCase(node)) return;
		if (!node.consequent.some(droppable)) return;
		node.consequent = node.consequent.filter((statement) =>
			!droppable(statement)
		);
	});
}

function blockProgramWithBranch(block: IRBlock) {
	const body = <t.Statement[]> block.body;
	const branchStmt = block.branch
		? t.expressionStatement(
			t.cloneNode(block.branch as t.Expression, true),
		)
		: undefined;
	const wrapped = t.file(t.program(
		branchStmt ? [...body, branchStmt] : body,
	));

	return {
		wrapped,
		commit() {
			if (!branchStmt) {
				block.body = wrapped.program.body;
				return;
			}

			const nextBody = wrapped.program.body.slice();
			const nextBranchStmt = nextBody.pop();
			if (t.isExpressionStatement(nextBranchStmt)) {
				block.branch = nextBranchStmt.expression;
				block.body = nextBody;
			} else {
				block.body = wrapped.program.body;
			}
		},
	};
}

interface ReadOnlyEnvironmentHandleCandidate {
	declaration: NodePath<t.VariableDeclaration>;
	declarator: NodePath<t.VariableDeclarator>;
	id: t.Identifier;
	init: t.CallExpression;
	register: SSARegister;
	references: NodePath<t.Identifier>[];
	invalid: boolean;
}

/**
 * Inline stable environment handles across basic blocks while SSA provenance
 * still identifies every use exactly. Per-block Babel cleanup cannot perform
 * this rewrite: a handle defined in a short-circuit predicate is live into the
 * selected arm until composition resolves both slot accesses.
 */
function propagateReadOnlyEnvironmentSSAHandles(func: IRFunction): number {
	const wrappedBlocks = [...func.blocks.values()].map((block) => ({
		block,
		...blockProgramWithBranch(block),
	}));
	const candidates = new Map<string, ReadOnlyEnvironmentHandleCandidate>();

	for (const { wrapped } of wrappedBlocks) {
		traverse(wrapped, {
			noScope: true,
			Function(path) {
				path.skip();
			},
			VariableDeclarator(path) {
				const id = path.get('id');
				const init = path.get('init');
				if (
					!id.isIdentifier() ||
					!isReadOnlyEnvironmentLookup(init.node)
				) {
					return;
				}
				const register = (id.node as LiftedAST<t.Identifier>).extra
					?.sourceRegister;
				if (
					!register ||
					id.node.name !== `r${register.index}_${register.version}`
				) return;
				const declaration = path.parentPath;
				if (!declaration.isVariableDeclaration()) return;
				const existing = candidates.get(id.node.name);
				if (existing) {
					existing.invalid = true;
					return;
				}
				candidates.set(id.node.name, {
					declaration,
					declarator: path,
					id: id.node,
					init: init.node,
					register,
					references: [],
					invalid: false,
				});
			},
		});
	}
	if (candidates.size === 0) return 0;

	for (const { wrapped } of wrappedBlocks) {
		traverse(wrapped, {
			noScope: true,
			Function(path) {
				path.skip();
			},
			Identifier(path) {
				const candidate = candidates.get(path.node.name);
				if (!candidate || path.node === candidate.id) return;
				if (isIdentifierWrite(path)) {
					candidate.invalid = true;
					return;
				}
				if (!isValueIdentifierReference(path)) return;
				const register = (path.node as LiftedAST<t.Identifier>).extra
					?.sourceRegister;
				if (
					!register ||
					!ssaRegisterEquals(register, candidate.register) ||
					(path.parentPath?.isCallExpression() &&
						t.isV8IntrinsicIdentifier(path.parentPath.node.callee, {
							name: 'Phi',
						}))
				) {
					candidate.invalid = true;
					return;
				}
				candidate.references.push(path);
			},
		});
	}

	let propagated = 0;
	const ordered = [...candidates.values()].toSorted((left, right) => {
		const leftAddress = (left.init as LiftedAST<t.CallExpression>).extra
			?.address ?? Number.MAX_SAFE_INTEGER;
		const rightAddress = (right.init as LiftedAST<t.CallExpression>).extra
			?.address ?? Number.MAX_SAFE_INTEGER;
		return leftAddress - rightAddress;
	});
	for (const candidate of ordered) {
		if (candidate.invalid || candidate.declarator.removed) continue;
		for (const reference of candidate.references) {
			if (!nodePathIsAttached(reference)) continue;
			reference.replaceWith(t.cloneNode(candidate.init, true));
		}
		candidate.declarator.remove();
		if (
			candidate.declaration.node &&
			candidate.declaration.node.declarations.length === 0
		) candidate.declaration.remove();
		propagated++;
	}
	if (propagated === 0) return 0;
	for (const { commit } of wrappedBlocks) commit();
	return propagated;
}

function generatorStartsWithYieldUndefined(func: t.FunctionExpression) {
	return isYieldUndefinedStatement(func.body.body[0]);
}

function isNextCallStatement(stmt: t.Statement | undefined, name: string) {
	return !!stmt &&
		t.isExpressionStatement(stmt) &&
		t.isCallExpression(stmt.expression) &&
		t.isMemberExpression(stmt.expression.callee, { computed: false }) &&
		t.isIdentifier(stmt.expression.callee.object, { name }) &&
		t.isIdentifier(stmt.expression.callee.property, { name: 'next' }) &&
		stmt.expression.arguments.length === 0;
}

function elidedWrapperEnvironmentCapture(
	body: t.Statement[],
	env: t.Node | null | undefined,
	seenNames = new Set<string>(),
): ElidedWrapperEnvironmentCapture {
	if (
		t.isCallExpression(env) &&
		(
			t.isV8IntrinsicIdentifier(env.callee, {
				name: 'CreateFunctionEnvironment',
			}) ||
			t.isV8IntrinsicIdentifier(env.callee, {
				name: 'CreateTopLevelEnvironment',
			})
		)
	) return { kind: 'local' };
	if (
		t.isCallExpression(env) &&
		t.isV8IntrinsicIdentifier(env.callee, {
			name: 'GetParentEnvironment',
		}) &&
		t.isNumericLiteral(env.arguments[0])
	) return { kind: 'parent', depth: env.arguments[0].value };
	if (t.isIdentifier(env)) {
		if (seenNames.has(env.name)) return { kind: 'parent', depth: 0 };
		seenNames.add(env.name);
		for (const stmt of body) {
			if (t.isVariableDeclaration(stmt)) {
				for (const decl of stmt.declarations) {
					if (
						t.isIdentifier(decl.id, { name: env.name }) &&
						decl.init
					) {
						return elidedWrapperEnvironmentCapture(
							body,
							decl.init,
							seenNames,
						);
					}
				}
			}
			if (
				t.isExpressionStatement(stmt) &&
				t.isAssignmentExpression(stmt.expression, { operator: '=' }) &&
				t.isIdentifier(stmt.expression.left, { name: env.name })
			) {
				return elidedWrapperEnvironmentCapture(
					body,
					stmt.expression.right,
					seenNames,
				);
			}
		}
	}
	// An undefined closure environment is emitted when the inner body captures
	// nothing outside its own wrapper-local environment. Treat it as the
	// wrapper's captured environment for naming purposes; no valid bytecode path
	// can then read beyond the local environment.
	return { kind: 'parent', depth: 0 };
}

function createGeneratorTarget(expr: t.CallExpression):
	| {
		functionId: number;
		environmentCapture: ElidedWrapperEnvironmentCapture;
	}
	| undefined {
	if (
		!t.isV8IntrinsicIdentifier(expr.callee, { name: 'CreateGenerator' }) ||
		expr.arguments.length !== 2
	) return;

	const [env, funcRefArg] = expr.arguments;
	if (!t.isCallExpression(env)) return;
	const isFunctionEnv = t.isV8IntrinsicIdentifier(env.callee, {
		name: 'CreateFunctionEnvironment',
	});
	const isParentEnv = t.isV8IntrinsicIdentifier(env.callee, {
		name: 'GetParentEnvironment',
	}) &&
		env.arguments.length === 1 &&
		t.isNumericLiteral(env.arguments[0]);
	if (!isFunctionEnv && !isParentEnv) return;

	const functionId = extractFunctionRef(funcRefArg);
	if (functionId == null) return;
	return {
		functionId,
		environmentCapture: elidedWrapperEnvironmentCapture([], env),
	};
}

function createGeneratorTargetWithEnvironmentName(
	expr: t.CallExpression,
	envName: string,
):
	| {
		functionId: number;
		environmentCapture: ElidedWrapperEnvironmentCapture;
	}
	| undefined {
	if (
		!t.isV8IntrinsicIdentifier(expr.callee, { name: 'CreateGenerator' }) ||
		expr.arguments.length !== 2
	) return;

	const [env, funcRefArg] = expr.arguments;
	if (!t.isIdentifier(env, { name: envName })) return;
	const functionId = extractFunctionRef(funcRefArg);
	if (functionId == null) return;
	return { functionId, environmentCapture: { kind: 'local' } };
}

function isEnvironmentStoreToName(stmt: t.Statement, envName: string) {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	if (!t.isAssignmentExpression(expr, { operator: '=' })) return false;
	if (!t.isMemberExpression(expr.left) || !expr.left.computed) return false;
	if (!t.isCallExpression(expr.left.object)) return false;
	if (
		!t.isV8IntrinsicIdentifier(expr.left.object.callee, {
			name: 'expectEnvironment',
		})
	) return false;
	const [envArg] = expr.left.object.arguments;
	return t.isIdentifier(envArg, { name: envName });
}

function generatorPrimingEnvironmentPrelude(
	body: t.Statement[],
	end: number,
) {
	let envName: string | undefined;
	for (let i = 0; i < end; i++) {
		const stmt = body[i];
		const decl = singleDeclarator(stmt, 'const') ??
			singleDeclarator(stmt, 'let') ??
			singleDeclarator(stmt, 'var');
		if (
			decl &&
			t.isIdentifier(decl.id) &&
			t.isCallExpression(decl.init) &&
			t.isV8IntrinsicIdentifier(decl.init.callee, {
				name: 'CreateFunctionEnvironment',
			})
		) {
			if (envName != null) return;
			envName = decl.id.name;
			continue;
		}

		if (envName != null && isEnvironmentStoreToName(stmt, envName)) {
			continue;
		}

		return;
	}
	return envName;
}

type GeneratorClosureAnalysis =
	| t.FunctionExpression
	| {
		functionId: number;
		environmentCapture: ElidedWrapperEnvironmentCapture;
		skipInitialYieldUndefined?: boolean;
		inlineThroughWrapper?: boolean;
	};

interface AsyncClosureAnalysis {
	functionId: number;
	environmentCapture: ElidedWrapperEnvironmentCapture;
}

type AddressSetSnapshot<T = BlockAddr> = T[];
type AddressMapSnapshot<V> = [BlockAddr, V][];

interface GeneratorResumeInitializer {
	destination: SSARegister;
	value: LoadConstInst['value'];
	address: number;
}

type IRBlockSnapshot =
	& Omit<
		IRBlock,
		'sourceAddresses' | 'handlerFor'
	>
	& {
		sourceAddresses?: AddressSetSnapshot;
		handlerFor?: AddressSetSnapshot;
	};

export interface IRFunctionSnapshot {
	id: number;
	params: t.Function['params'];
	parameterPlan?: ParameterPlan;
	plainObjectProjectionSources?: string[];
	exceptionHandlers: FunctionExceptionHandler[];
	mergedBlocks: AddressMapSnapshot<AddressSetSnapshot>;
	isGenerator: boolean;
	isNativeGenerator: boolean;
	isLoweredGenerator: boolean;
	isAsync: boolean;
	yieldingBlocks: AddressMapSnapshot<SSARegister>;
	yieldEndBlocks: AddressMapSnapshot<{
		destination: SSARegister;
		continuation: BlockAddr;
		return: BlockAddr;
		spills: [SSARegister, SSARegister][];
		initializers: GeneratorResumeInitializer[];
	}>;
	yieldRetBlocks: AddressMapSnapshot<SSARegister>;
	returnBlocks: AddressSetSnapshot;
	blocks: AddressMapSnapshot<IRBlockSnapshot>;
	objectShapeKeysByRegister: [string, SerializedLiteralValue[]][];
	referencedFunctionIds: [number, number][];
	exceptions: HandlerGraphSnapshot;
	recursiveCFGSummary?: RecursiveCFGSummary;
}

function cloneReductionSnapshot(
	snapshot: IRFunctionSnapshot,
): IRFunctionSnapshot {
	return {
		...snapshot,
		params: snapshot.params.map((param) => t.cloneNode(param, true)),
		parameterPlan: snapshot.parameterPlan == null
			? undefined
			: cloneParameterPlan(snapshot.parameterPlan),
		plainObjectProjectionSources: [
			...(snapshot.plainObjectProjectionSources ?? []),
		],
		blocks: snapshot.blocks.map(([address, block]) => [address, {
			...block,
			body: block.body.map((stmt) =>
				t.cloneNode(stmt as t.Statement, true) as LiftedAST<t.Statement>
			),
			branch: block.branch == null
				? undefined
				: t.cloneNode(block.branch as t.Expression, true) as LiftedAST<
					t.Expression
				>,
			sourceAddresses: block.sourceAddresses == null
				? undefined
				: [...block.sourceAddresses],
			handlerFor: block.handlerFor == null
				? undefined
				: [...block.handlerFor],
		}]),
	};
}

interface IteratorEmissionFeatures {
	highLevelLoops: number;
	protocolCalls: number;
}

function iteratorEmissionFeatures(
	program: t.Program,
): IteratorEmissionFeatures {
	const features: IteratorEmissionFeatures = {
		highLevelLoops: 0,
		protocolCalls: 0,
	};
	const protocolIntrinsics = new Set([
		'IteratorBegin',
		'IteratorNext',
		'IteratorClose',
		'GetPNameList',
		'GetNextPName',
	]);
	t.traverseFast(program, (node) => {
		if (t.isForOfStatement(node) || t.isForInStatement(node)) {
			features.highLevelLoops++;
			return;
		}
		if (
			t.isCallExpression(node) &&
			[...protocolIntrinsics].some((name) =>
				t.isV8IntrinsicIdentifier(node.callee, { name })
			)
		) features.protocolCalls++;
	});
	return features;
}

function iteratorEmissionRegresses(
	current: t.Program,
	candidate: t.Program,
): boolean {
	const before = iteratorEmissionFeatures(current);
	const after = iteratorEmissionFeatures(candidate);
	return after.highLevelLoops < before.highLevelLoops &&
		after.protocolCalls > before.protocolCalls;
}

export interface IRFunctionOptions {
	cfgReducer?: CFGReducerOptions;
	/** Tooling-only: stop after SSA-to-AST lifting, before CFG structuring. */
	skipCFGReduction?: boolean;
	/** Tooling-only observer for recursive CFG analyses and retries. */
	onRecursiveCFGAnalysis?: (result: StructuringResult) => void;
	/** Tooling-only observer for compatibility reduction passes. */
	onCFGReductionPass?: (event: CFGReductionPassEvent) => void;
	/**
	 * Internal reduction controls, set only by the speculative-transform
	 * rollback in `runCFGReduction` when it re-lifts a function.
	 */
	reduction?: {
		skipShortCircuitCollapse?: boolean;
		skipWideLeadingPhi?: boolean;
		requireCollapsedNaturalLoopBody?: boolean;
		/** False on a re-lift, so a rollback never starts another one. */
		rollback?: boolean;
	};
}

export interface CFGReductionPassEvent {
	stage: string;
	pass: string;
	result: boolean | 'restart';
	blocksBefore: number;
	blocksAfter: number;
	phisBefore: number;
	phisAfter: number;
}

function snapshotAddressSet<T>(set: Set<T> | undefined): T[] | undefined {
	return set == null ? undefined : [...set];
}

function restoreAddressSet<T>(values?: Iterable<T>): AddressSet<T> {
	return new AddressSet(values ?? []);
}

function envMemberAccess(expr: t.Expression | null | undefined) {
	if (
		!t.isMemberExpression(expr) ||
		!expr.computed ||
		!t.isCallExpression(expr.object) ||
		!t.isV8IntrinsicIdentifier(expr.object.callee, {
			name: 'expectEnvironment',
		}) ||
		!t.isNumericLiteral(expr.property)
	) return;
	const [env] = expr.object.arguments;
	if (!t.isIdentifier(env)) return;
	return { envName: env.name, slot: expr.property.value };
}

function renameDuplicateLabels(node: t.Node): void {
	const active: string[] = [];
	let nextId = 0;
	const visit = (current: t.Node) => {
		if (t.isLabeledStatement(current)) {
			const original = current.label.name;
			let name = original;
			if (active.includes(original)) {
				name = `${original}_${nextId++}`;
				current.label.name = name;
				t.traverseFast(current.body, (child) => {
					if (
						(t.isBreakStatement(child) ||
							t.isContinueStatement(child)) &&
						child.label?.name === original
					) {
						child.label!.name = name;
					}
				});
			}
			active.push(name);
			visit(current.body);
			active.pop();
			return;
		}
		t.VISITOR_KEYS[current.type]?.forEach((key) => {
			const value = (current as unknown as Record<string, unknown>)[key];
			if (Array.isArray(value)) {
				for (const item of value) {
					if (t.isNode(item)) visit(item);
				}
			} else if (t.isNode(value)) {
				visit(value);
			}
		});
	};
	visit(node);
}

function isCopyRestArgsCall(
	node: t.Node | null | undefined,
	restIdx: number,
): node is t.CallExpression {
	if (!t.isCallExpression(node)) return false;
	const { callee } = node;
	if (!t.isMemberExpression(callee, { computed: false })) return false;
	if (!t.isIdentifier(callee.object, { name: 'HermesInternal' })) {
		return false;
	}
	if (!t.isIdentifier(callee.property)) return false;
	const { name } = callee.property;
	if (name !== 'copyRestArgs' && name !== 'copyRestArgsFast') return false;
	if (node.arguments.length !== 1) return false;
	return t.isNumericLiteral(node.arguments[0], { value: restIdx });
}

/**
 * How many times a snapshot-restored function has had to build SSA on demand.
 *
 * Composition never reads `.ssa` -- every use is in CFG reduction, which has
 * already happened by the time a snapshot exists -- so on the composition path
 * this must stay at zero. It is a counter rather than a throw because the
 * lazy path is genuinely reachable (`relift`, and any future caller that
 * restores a function in order to reduce it again); a non-zero count on a
 * compose run means something started paging disassembly back in.
 */
export let snapshotSSAForcedCount = 0;

export function resetSnapshotSSAForcedCount(): void {
	snapshotSSAForcedCount = 0;
}

export class IRFunction {
	file: HBCFile;
	id: number;
	params: t.Function['params'];
	parameterPlan: ParameterPlan;
	plainObjectProjectionSources = new Set<string>();

	_exceptionHandlers: FunctionExceptionHandler[];

	entryAddress: BlockAddr = 0;
	mergedBlocks: AddressGraph;

	isGenerator = false;
	isNativeGenerator = false;
	isLoweredGenerator = false;
	isAsync = false;
	yieldingBlocks = new AddressMap<SSARegister>();
	yieldEndBlocks = new AddressMap<{
		destination: SSARegister;
		continuation: BlockAddr;
		return: BlockAddr;
		spills: [SSARegister, SSARegister][];
		initializers: GeneratorResumeInitializer[];
	}>();
	yieldRetBlocks = new AddressMap<SSARegister>();
	returnBlocks = new AddressSet();

	blocks = new AddressMap<IRBlock>();
	predecessorMap = new AddressMap<AddressSet>();

	// Maps a NewObjectWithBuffer destination register to its buffer shape keys (property
	// names). Hoisted to the function (rather than kept local to liftSSABlocktoIR) so that
	// slot accesses lifted in a later/split block can still resolve named keys instead of
	// falling back to numeric indices like `obj[2]`.
	objectShapeKeysByRegister = new Map<string, SerializedLiteralValue[]>();

	exceptions: HandlerGraph;

	referencedFunctionIds = new Map<number, number>();
	options: IRFunctionOptions;
	recursiveCFGSummary?: RecursiveCFGSummary;
	/**
	 * Why the recursive-CFG summary could not be emitted, when it could not.
	 *
	 * Deliberately not part of `IRFunctionSnapshot`: the function itself is
	 * fully reduced and safe to compose either way, and this is a diagnostic
	 * about one run rather than state a restored function needs.
	 */
	recursiveCFGSummaryEmissionError?: string;
	guardedPhiMode: 'enabled' | 'disabled' = 'disabled';
	/** Prevent cleanup fixpoints from counting one structural blocker repeatedly. */
	bindingCleanupObservationKeys = new Set<string>();

	/**
	 * Backing state for the lazy `ssa` accessor.
	 *
	 * Plain properties rather than `#private` fields: `fromSnapshot` builds its
	 * instance with `Object.create`, which never runs the constructor, and a
	 * private field that was never installed throws on every access.
	 */
	_ssaValue?: SSAFunction;
	_ssaSource?: () => SSAFunction;

	/**
	 * The SSA form this function was lifted from.
	 *
	 * Eager when the function was built by the constructor, because reduction is
	 * about to read it. Lazy when it was restored from a snapshot, because the
	 * blocks are already lifted ASTs and rebuilding SSA over them costs a
	 * liveness analysis and a dominance graph for an answer nothing on the
	 * composition path asks for.
	 */
	get ssa(): SSAFunction {
		if (this._ssaValue) return this._ssaValue;
		const source = this._ssaSource;
		if (!source) {
			throw new Error(
				`IRFunction #${this.id} has no SSA form and no way to build one`,
			);
		}
		snapshotSSAForcedCount++;
		this._ssaSource = undefined;
		this._ssaValue = source();
		return this._ssaValue;
	}

	set ssa(value: SSAFunction) {
		this._ssaValue = value;
		this._ssaSource = undefined;
	}

	constructor(
		file: HBCFile,
		ssa: SSAFunction,
		options: IRFunctionOptions = {},
	) {
		this.file = file;
		this.ssa = ssa;
		this.options = options;
		this.skipShortCircuitCollapse =
			options.reduction?.skipShortCircuitCollapse === true;
		this.skipWideLeadingPhi =
			options.reduction?.skipWideLeadingPhi === true;
		this.requireCollapsedNaturalLoopBody =
			options.reduction?.requireCollapsedNaturalLoopBody === true;
		this.id = this.ssa.id;
		this.params = [];
		for (let i = 1; i < this.paramCount; i++) {
			this.params.push(this.getParam(i) as t.Identifier);
		}
		this.parameterPlan = createParameterPlan(this.id, this.params);

		this._exceptionHandlers = this.ssa.exceptionHandlers.map((exc) => ({
			...exc,
		}));
		this.exceptions = new HandlerGraph(this);

		const { basicBlocks } = this.ssa;
		this.mergedBlocks = AddressGraph.fromBasicBlocks(basicBlocks);

		if (!basicBlocks.has(0)) return;

		if (
			!this.detectFunctionKind()
		) {
			return;
		}
		this.liftSSABlocks();
		// Runs before every reducer: once a reducer structures the guard, the
		// eval arm's constant rematerializations and the call arm's receiver
		// register are inlined away, and the idiom is no longer provable.
		reduceDirectEvalDiamonds(this);
		propagateReadOnlyEnvironmentSSAHandles(this);
		capturePlainObjectProjectionSources(this);
		if (reduceSideEffectOnlyOverflowDefault(this)) {
			this.params = materializeParameterPlan(this.parameterPlan);
		}
		captureParameterProjections(
			this.id,
			[...this.blocks.values()].map((block) =>
				block.body as t.Statement[]
			),
			this.parameterPlan,
		);
		if (reduceArgumentsCopyRest(this)) {
			this.params = materializeParameterPlan(this.parameterPlan);
		}
		if (options.skipCFGReduction) {
			this.rebuildPredecessorMap();
			this.refreshReferencedFunctionIds();
			return;
		}
		this.runCFGReduction();
	}

	snapshot(): IRFunctionSnapshot {
		return {
			id: this.id,
			// Snapshot users routinely run speculative cleanup, including parameter
			// destructuring hoists. Sharing this mutable array lets a temporary
			// emission candidate change the live function's signature without its
			// corresponding body being selected.
			params: this.params.map((param) => t.cloneNode(param, true)),
			parameterPlan: cloneParameterPlan(this.parameterPlan),
			plainObjectProjectionSources: [
				...this.plainObjectProjectionSources,
			],
			exceptionHandlers: this._exceptionHandlers.map((handler) => ({
				...handler,
			})),
			mergedBlocks: [...this.mergedBlocks].map(([addr, blocks]) => [
				addr,
				[...blocks],
			]),
			isGenerator: this.isGenerator,
			isNativeGenerator: this.isNativeGenerator,
			isLoweredGenerator: this.isLoweredGenerator,
			isAsync: this.isAsync,
			yieldingBlocks: [...this.yieldingBlocks],
			yieldEndBlocks: [...this.yieldEndBlocks].map(([addr, info]) => [
				addr,
				{
					...info,
					spills: info.spills.map(([left, right]) => [
						{ ...left },
						{ ...right },
					]),
					initializers: info.initializers.map((initializer) => ({
						...initializer,
						destination: { ...initializer.destination },
					})),
				},
			]),
			yieldRetBlocks: [...this.yieldRetBlocks],
			returnBlocks: [...this.returnBlocks],
			blocks: [...this.blocks].map(([addr, block]) => [
				addr,
				{
					...block,
					body: block.body,
					sourceAddresses: snapshotAddressSet(
						block.sourceAddresses,
					),
					handlerFor: snapshotAddressSet(block.handlerFor),
				},
			]),
			objectShapeKeysByRegister: [...this.objectShapeKeysByRegister].map(
				([key, values]) => [key, [...values]],
			),
			referencedFunctionIds: [...this.referencedFunctionIds],
			exceptions: this.exceptions.snapshot(),
			recursiveCFGSummary: this.recursiveCFGSummary,
		};
	}

	static fromSnapshot(
		file: HBCFile,
		snapshot: IRFunctionSnapshot,
	): IRFunction {
		const func = Object.create(IRFunction.prototype) as IRFunction;
		func.file = file;
		// Deferred, and over a copy: see the `ssa` accessor. The copy matters
		// because `SSAFunction` rewrites the disassembly it is handed, and a
		// restored function does not own `file.functions[id]`.
		func._ssaValue = undefined;
		func._ssaSource = () =>
			new SSAFunction(
				copyFunctionForSSA(file.functions[snapshot.id]),
			);
		func.id = snapshot.id;
		func.params = snapshot.params;
		func.parameterPlan = snapshot.parameterPlan == null
			? createParameterPlan(func.id, func.params)
			: cloneParameterPlan(snapshot.parameterPlan);
		func.plainObjectProjectionSources = new Set(
			snapshot.plainObjectProjectionSources ?? [],
		);
		func._exceptionHandlers = snapshot.exceptionHandlers.map((handler) => ({
			...handler,
		}));
		func.entryAddress = 0;
		func.mergedBlocks = new AddressGraph();
		for (const [addr, blocks] of snapshot.mergedBlocks) {
			func.mergedBlocks.set(addr, new AddressSet(blocks));
		}
		func.isGenerator = snapshot.isGenerator;
		func.isNativeGenerator = snapshot.isNativeGenerator;
		func.isLoweredGenerator = snapshot.isLoweredGenerator;
		func.isAsync = snapshot.isAsync;
		func.yieldingBlocks = new AddressMap(snapshot.yieldingBlocks);
		func.yieldEndBlocks = new AddressMap(snapshot.yieldEndBlocks);
		func.yieldRetBlocks = new AddressMap(snapshot.yieldRetBlocks);
		func.returnBlocks = new AddressSet(snapshot.returnBlocks);
		func.blocks = new AddressMap();
		for (const [addr, block] of snapshot.blocks) {
			func.blocks.set(addr, {
				...block,
				sourceAddresses: block.sourceAddresses == null
					? undefined
					: restoreAddressSet(block.sourceAddresses),
				handlerFor: block.handlerFor == null
					? undefined
					: restoreAddressSet(block.handlerFor),
			});
		}
		func.predecessorMap = new AddressMap<AddressSet>();
		func.objectShapeKeysByRegister = new Map(
			snapshot.objectShapeKeysByRegister.map(([key, values]) => [
				key,
				[...values],
			]),
		);
		func.referencedFunctionIds = new Map(snapshot.referencedFunctionIds);
		func.options = {};
		func.guardedPhiMode = 'disabled';
		func.bindingCleanupObservationKeys = new Set<string>();
		func.recursiveCFGSummary = snapshot.recursiveCFGSummary;
		func.exceptions = HandlerGraph.fromSnapshot(func, snapshot.exceptions);
		func.rebuildPredecessorMap();
		return func;
	}

	private detectFunctionKind(): boolean {
		const { basicBlocks } = this.ssa;
		const startBlock = basicBlocks.get(0)!;
		this.isNativeGenerator =
			startBlock.instructions[0]?.instruction === 'StartGenerator';
		if (
			this.ssa._func.functionKind === FunctionKind.GeneratorFunction ||
			this.isNativeGenerator
		) {
			this.isGenerator = true;
		}

		if (this.ssa._func.functionKind === FunctionKind.AsyncFunction) {
			this.isAsync = true;
		}

		if (
			!this.isNativeGenerator &&
			tryInitializeLoweredGeneratorStateMachine(this)
		) {
			this.isLoweredGenerator = true;
			return false;
		}
		return true;
	}

	private liftSSABlocks(): void {
		const { basicBlocks } = this.ssa;
		for (const [addr, block] of basicBlocks) {
			let firstNonPhiIndex = 0;
			while (
				block.ssaInstructions[firstNonPhiIndex]?.instruction === 'Phi'
			) {
				firstNonPhiIndex++;
			}
			const firstNonPhi = block.ssaInstructions[firstNonPhiIndex];
			if (
				this.isNativeGenerator &&
				firstNonPhi?.instruction == 'ResumeGenerator'
			) {
				const destination = firstNonPhi.defs.destination;
				const spills: [SSARegister, SSARegister][] = [];
				const initializers: GeneratorResumeInitializer[] = [];
				let current;
				for (
					let i = firstNonPhiIndex + 1;
					i < block.ssaInstructions.length;
					i++
				) {
					current = block.ssaInstructions[i];
					if (current?.instruction != 'Mov') break;
					spills.push([
						current.defs.destination,
						current.uses.source,
					]);
				}
				while (current?.instruction === 'LoadConst') {
					initializers.push({
						destination: current.defs.destination,
						value: current.value,
						address: current.functionLocalOffset,
					});
					current = block.ssaInstructions[
						firstNonPhiIndex + spills.length + initializers.length +
						1
					];
				}

				let returnAddress, continuation;
				if (current?.instruction == 'JmpTrue') {
					continuation = block.consequentAddresses[0];
					returnAddress = block.consequentAddresses[1];
				} else if (current?.instruction == 'JmpFalse') {
					continuation = block.consequentAddresses[1];
					returnAddress = block.consequentAddresses[0];
				} else {
					const location = current && 'functionLocalOffset' in current
						? `:${current.functionLocalOffset.toString(16)}`
						: '';
					throw new LiftError(
						`Unhandled instruction after ResumeGenerator: ` +
							`${
								current?.instruction ?? '<end>'
							} at ${this.id}${location}`,
					);
				}

				this.yieldEndBlocks.set(addr, {
					destination,
					continuation,
					return: returnAddress,
					spills,
					initializers,
				});

				this.yieldRetBlocks.set(returnAddress, destination);
				this.returnBlocks.add(returnAddress);
			} else {
				const retInst = block.ssaInstructions.at(-1);
				if (retInst?.instruction != 'Ret') continue;

				if (this.isNativeGenerator) {
					const prev = block.ssaInstructions.at(-2);
					if (prev?.instruction == 'SaveGenerator') {
						this.yieldingBlocks.set(addr, retInst.uses.argument);
						continue;
					} else if (prev?.instruction != 'CompleteGenerator') {
						console.log(prev);
						throw new LiftError('');
					}
				}

				this.returnBlocks.add(addr);
			}
		}

		for (const [addr, block] of basicBlocks) {
			if (
				this.yieldEndBlocks.has(addr) ||
				(this.yieldRetBlocks.has(addr) &&
					!this.yieldingBlocks.has(addr))
			) continue;

			this.blocks.set(addr, liftSSABlocktoIR(this, block));
		}

		if (this.isNativeGenerator) {
			for (const addr of [0, ...this.yieldingBlocks.keys()]) {
				const block = this.blocks.get(addr);
				if (block?.consequentAddresses?.length !== 1) {
					throw new LiftError('bruh');
				}

				const endInfo = this.yieldEndBlocks.get(
					block.consequentAddresses[0],
				);
				if (!endInfo) throw new LiftError('Uncorresponding end error');

				const returnBlock = basicBlocks.get(endInfo.return);
				if (!returnBlock) {
					throw new LiftError('Missing .return handler');
				}

				const [compGen, ret] = returnBlock.ssaInstructions;
				if (compGen?.instruction === 'CompleteGenerator') {
					if (
						returnBlock.ssaInstructions.length !== 2 ||
						ret.instruction !== 'Ret' ||
						!ssaRegisterEquals(
							endInfo.destination,
							ret.uses.argument,
						)
					) {
						throw new LiftError(
							`Malformed generator return block 0x${
								endInfo.return.toString(16)
							}`,
						);
					}

					block.consequentAddresses = [endInfo.continuation];
					continue;
				}

				// A yield inside a protected range can have a generator-close edge that
				// runs pending finally code before completing, and that cleanup may
				// itself suspend. The structured try/finally preserves that behavior.
				block.consequentAddresses = [endInfo.continuation];
			}
		}
	}

	private sharedLeadingPhiPredecessorLimit(): number {
		return this.skipWideLeadingPhi
			? SAFE_SHARED_LEADING_PHI_PREDECESSORS
			: MAX_SHARED_LEADING_PHI_PREDECESSORS;
	}

	private shouldUseCompatibilityReducersForLargeProtectedDAG(): boolean {
		const summary = this.recursiveCFGSummary;
		return summary != null &&
			summary.blockCount > 256 &&
			summary.loopCount === 0 &&
			summary.exceptionHandlerCount > 0;
	}

	private noteSharedLeadingPhiRewrite(predecessorCount: number): void {
		if (predecessorCount > SAFE_SHARED_LEADING_PHI_PREDECESSORS) {
			this.appliedWideLeadingPhi = true;
		}
	}

	/**
	 * Rewrite shared leading Phis into predecessor assignments before the
	 * recursive structurer runs.
	 *
	 * This is the `recursive-leading-phi` healing pass below, hoisted. For eight
	 * of the functions that still select post-reduction it is the only change
	 * healing makes — no block moves at all, one Phi fewer — after which the
	 * recursive structurer represents the whole function. Running it first means
	 * those functions never need the legacy reducer to heal them.
	 *
	 * The pass is already gated on recursive mode, so legacy reduction is
	 * unaffected; it stays in the fixpoint for the candidates that reach it.
	 */

	private normalizeLeadingPhisForRegions(): boolean {
		// Each rewrite removes leading Phis from one block, so the fixpoint
		// terminates; the bound only guards against a pass that reports progress
		// without making any.
		let changed = false;
		for (let iteration = 0; iteration < 64; iteration++) {
			if (this.blocks.size > 256) break;
			if (
				!reduceSharedLeadingPhi(this, {
					maxPhis: 8,
					maxPredecessors: this.sharedLeadingPhiPredecessorLimit(),
					onApplied: ({ predecessorCount }) =>
						this.noteSharedLeadingPhiRewrite(predecessorCount),
				})
			) break;
			changed = true;
		}
		return changed;
	}

	/**
	 * Collapse short-circuit condition chains into single branches.
	 *
	 * `reduceOrChain` already does this for the legacy reducer and refuses any
	 * collapse that would merge two of a live Phi's source edges. It has to run
	 * before the first structuring attempt rather than as an incompleteness
	 * retry: a skeleton covers every block, so a function that fell back to one
	 * does not report as incomplete and a retry would never fire for it.
	 */
	private collapseShortCircuitsForRegions(): boolean {
		let changed = false;
		// Each collapse removes a branch, so the fixpoint terminates; the bound
		// only guards a pass that reports progress without making any.
		for (let iteration = 0; iteration < 64; iteration++) {
			if (!reduceOrChain(this)) break;
			changed = true;
		}
		return changed;
	}

	private lowerBranchingPhiJoinsForRegions(): boolean {
		let changed = false;
		// Each simple-if rewrite merges at least one block. Keep the same defensive
		// bound used by the other recursive pre-normalisers.
		for (let iteration = 0; iteration < 64; iteration++) {
			if (
				!reduceSimpleIf(this, {
					requireBranchingPhiSuccessor: true,
				})
			) break;
			changed = true;
		}
		return changed;
	}

	private reduceSimpleIfsForRegions(): boolean {
		let changed = false;
		for (let iteration = 0; iteration < 64; iteration++) {
			let iterationChanged = false;
			if (reduceSequence(this)) iterationChanged = true;
			if (reduceSimpleIf(this, { preserveSuccessorPhis: true })) {
				iterationChanged = true;
			}
			if (!iterationChanged) break;
			changed = true;
		}
		return changed;
	}

	private inlineSharedTerminalsForRegions(): boolean {
		let changed = false;
		// Recursive Regions already model terminal references, but only when the
		// shared terminal is visible inside the selected weak-SESE scope. Inline the
		// same small terminal branches the compatibility reducer accepts, then fold
		// the newly linear block boundaries.
		for (let iteration = 0; iteration < 64; iteration++) {
			let iterationChanged = false;
			if (reduceInlineTerminal(this)) iterationChanged = true;
			if (reduceSequence(this)) iterationChanged = true;
			if (!iterationChanged) break;
			changed = true;
		}
		return changed;
	}

	private tryReduceNaturalLoopSpeculatively(
		options: { allowPartialBody?: boolean } = {},
	): boolean {
		let beforeNaturalLoop: IRFunctionSnapshot | undefined;
		const beforeSummary = this.recursiveCFGSummary;
		try {
			return reduceNaturalLoop(
				this,
				() => {
					beforeNaturalLoop = cloneReductionSnapshot(this.snapshot());
				},
				options,
			);
		} catch (error) {
			if (beforeNaturalLoop) {
				const original = IRFunction.fromSnapshot(
					this.file,
					beforeNaturalLoop,
				);
				original.options = this.options;
				this.adoptReductionState(original);
				this.recursiveCFGSummary = beforeSummary;
			}
			if (Deno.env.get('ARES_TRACE_FIXPOINT') != null) {
				const message = error instanceof Error
					? error.message
					: String(error);
				Deno.stderr.writeSync(
					new TextEncoder().encode(
						`[nl] abandoned speculative natural loop: ${message}\n`,
					),
				);
			}
			return false;
		}
	}

	// Recursive Region analysis may retain a partial loop long enough to prove
	// full CFG coverage. Emitted bodies still pass the whole-function safety gate
	// below; an unsafe result is re-lifted with every loop required to collapse.
	private tryReduceNaturalLoopWithPolicy(): boolean {
		const allowPartialBody =
			this.options.cfgReducer?.mode === 'recursive' &&
			!this.requireCollapsedNaturalLoopBody;
		const changed = this.tryReduceNaturalLoopSpeculatively({
			allowPartialBody,
		});
		if (changed && allowPartialBody) {
			this.appliedPartialNaturalLoop = true;
		}
		return changed;
	}

	public tryReduceNaturalLoop(): boolean {
		return this.tryReduceNaturalLoopWithPolicy();
	}
	public tryReduceCompleteNaturalLoop(): boolean {
		return this.tryReduceNaturalLoopSpeculatively({
			allowPartialBody: false,
		});
	}

	private tryReduceNaturalLoopForRegions(): boolean {
		return this.tryReduceNaturalLoopWithPolicy();
	}

	private reduceNaturalLoopsForRegions(): boolean {
		let changed = false;
		// Natural-loop lowering already performs its own inner reductions. Run it
		// as a speculative pre-normaliser only while it makes progress; the caller
		// keeps the result only when recursive Region analysis becomes complete.
		for (let iteration = 0; iteration < 64; iteration++) {
			if (!this.tryReduceNaturalLoopForRegions()) break;
			reduceSequence(this);
			changed = true;
		}
		return changed;
	}

	private reduceControlForestForRegions(): boolean {
		let changed = false;
		// Some candidates need these simple reducers in combination: a terminal
		// clone exposes a sequence, which exposes an if/else, which finally exposes
		// a natural loop. Keep the set deliberately below the full compatibility
		// pipeline: no handler rewrites, shared-edge cloning, switch lowering, or
		// post-cleanup AST repair.
		for (let iteration = 0; iteration < 64; iteration++) {
			let iterationChanged = false;
			if (reduceSequence(this)) iterationChanged = true;
			if (reduceInlineTerminal(this)) iterationChanged = true;
			if (reduceSimpleIf(this, { preserveSuccessorPhis: true })) {
				iterationChanged = true;
			}
			if (this.tryReduceNaturalLoopForRegions()) iterationChanged = true;
			if (!iterationChanged) break;
			changed = true;
		}
		return changed;
	}

	private reduceProtectedControlForestForRegions(): boolean {
		let changed = false;
		const tryCatchOptions = {
			preferProtectedRegionOrder: this.file.version >= 97,
			mergeSplitTryFinallyBody: this.isNativeGenerator ||
				(!this.isGenerator) ||
				this.file.version >= 97,
		};
		for (let iteration = 0; iteration < 64; iteration++) {
			let iterationChanged = false;
			if (reduceSequence(this)) iterationChanged = true;
			if (reduceInlineTerminal(this)) iterationChanged = true;
			if (reduceSimpleIf(this, { preserveSuccessorPhis: true })) {
				iterationChanged = true;
			}
			if (this.tryReduceNaturalLoopForRegions()) iterationChanged = true;
			if (reduceTryCatch(this, tryCatchOptions)) iterationChanged = true;
			if (!iterationChanged) break;
			changed = true;
		}
		return changed;
	}

	private containsDestructuringProtocol(): boolean {
		const body: t.Statement[] = [];
		for (const block of this.blocks.values()) {
			body.push(...block.body as t.Statement[]);
			if (block.branch) {
				body.push(t.expressionStatement(
					t.cloneNode(block.branch as t.Expression, true),
				));
			}
		}
		return containsDestructuringProtocol(t.program(body));
	}

	/** The recursive structurer left blocks or Phi copies unrepresented. */
	private recursiveRegionIncomplete(): boolean {
		const summary = this.recursiveCFGSummary;
		return summary != null &&
			(summary.misses.length > 0 ||
				summary.rawEmission.diagnostics.length > 0);
	}

	/** Set while re-running the pipeline with the collapse suppressed. */
	private skipShortCircuitCollapse = false;
	/** Whether this run collapsed any short-circuit chain. */
	private collapsedShortCircuits = false;
	/** Whether widened leading-Phi rewrites are disabled on a retry. */
	private skipWideLeadingPhi = false;
	/** Whether this run applied a widened leading-Phi rewrite. */
	private appliedWideLeadingPhi = false;
	/** Whether recursive reduction accepted a partially collapsed natural loop. */
	private appliedPartialNaturalLoop = false;
	/** Require every natural-loop body block to merge on a safety re-lift. */
	private requireCollapsedNaturalLoopBody = false;

	/**
	 * Whether the reduced body reads a generated register nothing declares.
	 *
	 * This is the verdict on a speculative collapse, and it can only be reached
	 * here: the collapse can fold away the block computing a condition's value
	 * while the merged test still reads it, and that surfaces after the legacy
	 * reducer has run, not in the Region emission the collapse produced.
	 */
	private reducedBodyIsUnsound(): boolean {
		const statements: t.Statement[] = [];
		for (const block of this.blocks.values()) {
			statements.push(...(block.body as t.Statement[]));
		}
		if (statements.length === 0) return false;
		// A surviving `%Phi` is the other half of the verdict: the collapse
		// merged edges the Phi still needed to tell apart.
		if (this.unresolvedPhiCount() > 0) return true;
		return hasUnboundGeneratedRegister(t.program(statements));
	}

	private runCFGReduction(): void {
		this.runCFGReductionInner();
		const recursiveSummary = this.recursiveCFGSummary;
		// Graph-normalizing reductions are speculative: keep them unless the final
		// body retains a Phi or reads a generated register nothing declares. Judge
		// them together because either transform can expose the other's unsafe
		// predecessor shape.
		const rollbackShortCircuits = this.collapsedShortCircuits;
		const rollbackWidePhi = this.appliedWideLeadingPhi;
		const rollbackNaturalLoop = this.appliedPartialNaturalLoop;
		if (
			this.options.reduction?.rollback !== false &&
			(rollbackShortCircuits || rollbackWidePhi || rollbackNaturalLoop) &&
			this.reducedBodyIsUnsound()
		) {
			// Re-lifted, not restored from a checkpoint. The checkpoint was a
			// deep clone of every block body, taken before reduction on every
			// function, to serve a rollback that fires on almost none of them.
			// Lifting is deterministic, so the pre-reduction state is
			// reproducible on demand; the clone was not reclaimable.
			//
			// `rollback: false` keeps this one level deep. A natural-loop failure
			// takes the fully conservative path because its changed graph can expose
			// either of the other speculative rewrites only during the re-lift.
			const fallback = new IRFunction(
				this.file,
				new SSAFunction(
					copyFunctionForSSA(this.file.functions[this.id]),
				),
				{
					...this.options,
					reduction: {
						skipShortCircuitCollapse: rollbackShortCircuits ||
							rollbackNaturalLoop,
						skipWideLeadingPhi: rollbackWidePhi ||
							rollbackNaturalLoop,
						requireCollapsedNaturalLoopBody: rollbackNaturalLoop,
						rollback: false,
					},
				},
			);
			const fallbackIsBetter = !fallback.reducedBodyIsUnsound();
			// A collapsed short circuit is unsound as emitted, so its re-lift is
			// adopted either way. A wide leading-Phi rollback is a preference:
			// declining it keeps this function's own state, which is still the
			// primary candidate and so needs no copy.
			const adopted = rollbackShortCircuits || rollbackNaturalLoop ||
				fallbackIsBetter;
			if (adopted) {
				this.adoptReductionState(fallback);
				// The fallback replaces an unsound compatibility body, not a
				// recursive candidate already proven clean before reduction.
				// Keep that candidate available to audit-only/nonmaterializing
				// runs while using the fallback's blocks as the incumbent.
				if (recursiveSummary?.selectedEmission) {
					this.recursiveCFGSummary = recursiveSummary;
				}
			}
			if (rollbackShortCircuits) {
				this.recordCompatibilityPath(
					'short-circuit-rollback',
					'attempt',
					'collapsed short circuit left an unresolved Phi or unbound register',
				);
				this.recordCompatibilityPath(
					'short-circuit-rollback',
					'selection',
					'reduction was rerun with short-circuit collapse disabled',
				);
			}
			if (rollbackWidePhi && fallbackIsBetter) {
				this.recordCompatibilityPath(
					'wide-leading-phi-rollback',
					'attempt',
					'wide leading-Phi reduction left an unresolved Phi or unbound register',
				);
				this.recordCompatibilityPath(
					'wide-leading-phi-rollback',
					'selection',
					'reduction was rerun with wide leading-Phi disabled',
				);
			}
			if (rollbackNaturalLoop) {
				this.recordCompatibilityPath(
					'natural-loop-rollback',
					'attempt',
					'partial natural-loop reduction left an unresolved Phi or unbound register',
				);
				this.recordCompatibilityPath(
					'natural-loop-rollback',
					'selection',
					'reduction was rerun with full loop-body collapse required',
				);
			}
			if (adopted && recursiveSummary?.selectedEmission) {
				this.finalizeMigrationAudit();
			}
		}
		this.recoverParameterPlan();
	}

	/** Materialize the shared signature after the entry CFG is structured. */
	private recoverParameterPlan(): void {
		const entry = this.entryBlock();
		if (!entry) return;
		const body = entry.body as t.Statement[];
		const allBodies = [...this.reachableBlocksFromEntry()]
			.flatMap((address) => {
				const block = this.blocks.get(address);
				return block ? [block.body as t.Statement[]] : [];
			});
		const singleBlock = this.blocks.size === 1;
		const overflowRecovered = recoverOverflowParameters({
			functionId: this.id,
			headerParamCount: this.paramCount,
			body,
			plan: this.parameterPlan,
		});
		// A prologue copy of a parameter is a second binding for storage that
		// already has one, and it also stands between the entry and a later
		// slot's recovered destructuring. Folding it here, rather than leaving it
		// to whole-file composition, is what lets that pattern reach the
		// signature; the attachment below deliberately refuses to reorder around
		// statements it cannot prove inert.
		coalesceParameterAliases(body, allBodies.flat());
		this.params = materializeParameterPlan(this.parameterPlan);
		// One pass is not a fixpoint. Folding a slot's guarded default removes the
		// statements between the entry and a later slot's destructuring, and
		// attaching that pattern can expose the next slot in turn. Every pass only
		// consumes statements, so this terminates.
		let attached = 0;
		for (;;) {
			const passAttached = attachDirectParameterPatterns(
				body,
				this.parameterPlan,
				allBodies,
			) + (singleBlock
				? attachProjectedObjectParameterPatterns(
					this.id,
					body,
					this.parameterPlan,
				) + attachParameterPatternAssignmentDefaults(
					body,
					this.parameterPlan,
				)
				: 0);
			if (passAttached === 0) break;
			attached += passAttached;
			this.params = materializeParameterPlan(this.parameterPlan);
		}
		if (!overflowRecovered && attached === 0) return;
		this.params = materializeParameterPlan(this.parameterPlan);
		attachPatternBindingDefaults(body);
		this.hoistDestructuredParams();
	}

	private runCFGReductionInner(): void {
		const cfgReducer = this.options.cfgReducer ?? envCFGReducerOptions();
		if (cfgReducer.mode === 'recursive') {
			const analysisOptions = {
				strict: cfgReducer.strict,
				debug: cfgReducer.debug,
				// Region always consumes the canonical reachable graph. This matters
				// most on retries after a graph-level cleanup such as short-circuit
				// collapse: that cleanup can detach old branch blocks even when the
				// bytecode CFG itself started fully reachable. Leaving those blocks in
				// normal mode made the same Region succeed only under debug/audit.
				normalizeForRegions: true,
				validateNormalization: cfgReducer.migrationAudit != null ||
					cfgReducer.debug === true,
				observer: this.options.onRecursiveCFGAnalysis,
				retainArtifacts: cfgReducer.retainArtifacts,
			};
			// Protected iterator destructuring is clearest before Region turns its
			// exception edges into labelled completion carries. Collapse every
			// disjoint protocol first; the pass verifies and removes its handlers.
			for (let iteration = 0; iteration < 64; iteration++) {
				if (!reduceProtectedArrayDestructuring(this)) break;
			}
			runRecursiveCFGAnalysis(this, analysisOptions);
			// A short-circuit condition lifts to two blocks whose fallthrough arm
			// branches into the taken arm's entry, which no weak SESE can
			// express, so the branch and everything under it falls to a
			// skeleton. Collapsing the chain gives the structurer an ordinary
			// two-way branch over a logical test.
			// Selection has not run yet, so `candidate` is still `none` here. A
			// structurally complete Region must keep its original CFG: collapsing an
			// already-folded predicate can detach the edge-local Phi assignments that
			// make every short-circuit path define the join value.
			const needsShortCircuitCollapse =
				this.recursiveRegionIncomplete() &&
				!this.shouldUseCompatibilityReducersForLargeProtectedDAG();
			if (
				needsShortCircuitCollapse &&
				!this.skipShortCircuitCollapse &&
				!this.containsDestructuringProtocol() &&
				this.collapseShortCircuitsForRegions()
			) {
				this.collapsedShortCircuits = true;
				runRecursiveCFGAnalysis(this, analysisOptions);
			}
			// A plain if/else whose merge block is itself a branch has no single
			// linear boundary where recursive emission can place edge-local Phi
			// copies. Speculate narrowly before Region analysis, but keep it only
			// when that candidate becomes complete; otherwise the compatibility
			// reducer can still combine this with its broader sequence/loop passes.
			if (this.recursiveRegionIncomplete()) {
				const beforeBranchingPhi = cloneReductionSnapshot(
					this.snapshot(),
				);
				const beforeSummary = this.recursiveCFGSummary;
				if (this.lowerBranchingPhiJoinsForRegions()) {
					runRecursiveCFGAnalysis(this, analysisOptions);
					if (this.recursiveRegionIncomplete()) {
						const original = IRFunction.fromSnapshot(
							this.file,
							beforeBranchingPhi,
						);
						original.options = this.options;
						this.adoptReductionState(original);
						this.recursiveCFGSummary = beforeSummary;
					}
				}
			}
			// Some raw misses only need the boring acyclic reducers that collapse
			// linear chains and ordinary if/else joins. Keep them separate from the
			// shared-terminal pass so simple branch forests do not wait for a terminal
			// clone to expose a complete Region.
			if (this.recursiveRegionIncomplete()) {
				const beforeSimpleIfs = cloneReductionSnapshot(this.snapshot());
				const beforeSummary = this.recursiveCFGSummary;
				if (this.reduceSimpleIfsForRegions()) {
					runRecursiveCFGAnalysis(this, analysisOptions);
					if (this.recursiveRegionIncomplete()) {
						const original = IRFunction.fromSnapshot(
							this.file,
							beforeSimpleIfs,
						);
						original.options = this.options;
						this.adoptReductionState(original);
						this.recursiveCFGSummary = beforeSummary;
					}
				}
			}
			// Shared return/throw blocks inside an otherwise acyclic branch forest can
			// keep those branch headers as Basic Regions. Speculate the existing
			// terminal inliner before the full compatibility pipeline; if it does not
			// produce a complete Region candidate, restore and let the ordinary
			// reducer combine it with loops, handlers, or wider Phi repairs.
			if (this.recursiveRegionIncomplete()) {
				const beforeSharedTerminals = cloneReductionSnapshot(
					this.snapshot(),
				);
				const beforeSummary = this.recursiveCFGSummary;
				if (this.inlineSharedTerminalsForRegions()) {
					runRecursiveCFGAnalysis(this, analysisOptions);
					if (this.recursiveRegionIncomplete()) {
						const original = IRFunction.fromSnapshot(
							this.file,
							beforeSharedTerminals,
						);
						original.options = this.options;
						this.adoptReductionState(original);
						this.recursiveCFGSummary = beforeSummary;
					}
				}
			}
			// Remaining raw misses skew toward loops whose internal branch forest is
			// already compatible with the legacy natural-loop reducer. Try exactly
			// that reduction before the full pipeline, but keep it only when it
			// yields a complete recursive Region.
			if (this.recursiveRegionIncomplete()) {
				const beforeNaturalLoops = cloneReductionSnapshot(
					this.snapshot(),
				);
				const beforeSummary = this.recursiveCFGSummary;
				if (this.reduceNaturalLoopsForRegions()) {
					runRecursiveCFGAnalysis(this, analysisOptions);
					if (this.recursiveRegionIncomplete()) {
						const original = IRFunction.fromSnapshot(
							this.file,
							beforeNaturalLoops,
						);
						original.options = this.options;
						this.adoptReductionState(original);
						this.recursiveCFGSummary = beforeSummary;
					}
				}
			}
			// Last pre-region structural attempt: combine the safe graph-local
			// reducers above instead of accepting only one family at a time. This
			// catches the remaining multi-pass branch/loop forests while still
			// restoring anything that needs full compatibility reduction.
			if (this.recursiveRegionIncomplete()) {
				const beforeControlForest = cloneReductionSnapshot(
					this.snapshot(),
				);
				const beforeSummary = this.recursiveCFGSummary;
				if (this.reduceControlForestForRegions()) {
					runRecursiveCFGAnalysis(this, analysisOptions);
					if (
						this.recursiveRegionIncomplete() &&
						this.normalizeLeadingPhisForRegions()
					) {
						runRecursiveCFGAnalysis(this, analysisOptions);
					}
					if (this.recursiveRegionIncomplete()) {
						const original = IRFunction.fromSnapshot(
							this.file,
							beforeControlForest,
						);
						original.options = this.options;
						this.adoptReductionState(original);
						this.recursiveCFGSummary = beforeSummary;
					}
				}
			}
			// Protected branches are held back when a catch/finally reducer must first
			// expose the same acyclic/loop shapes. This is still speculative and
			// complete-or-restore, so incomplete handler CFGs stay on the normal
			// compatibility path.
			if (this.recursiveRegionIncomplete()) {
				const beforeProtectedForest = cloneReductionSnapshot(
					this.snapshot(),
				);
				const beforeSummary = this.recursiveCFGSummary;
				if (this.reduceProtectedControlForestForRegions()) {
					runRecursiveCFGAnalysis(this, analysisOptions);
					if (
						this.recursiveRegionIncomplete() &&
						this.normalizeLeadingPhisForRegions()
					) {
						runRecursiveCFGAnalysis(this, analysisOptions);
					}
					if (this.recursiveRegionIncomplete()) {
						const original = IRFunction.fromSnapshot(
							this.file,
							beforeProtectedForest,
						);
						original.options = this.options;
						this.adoptReductionState(original);
						this.recursiveCFGSummary = beforeSummary;
					}
				}
			}
			// Retry rather than normalize up front: a function the structurer
			// already represents keeps its Phis exactly as lifted, which the
			// generator state-machine descriptors depend on.
			if (
				this.recursiveRegionIncomplete() &&
				this.normalizeLeadingPhisForRegions()
			) {
				runRecursiveCFGAnalysis(this, analysisOptions);
			}
			// A structurally complete Region can still be rejected solely because
			// object/array spread or destructuring protocol calls remain in its AST.
			// Consume those protocols before deciding whether compatibility CFG
			// reduction is needed; otherwise those reductions can regress an already
			// complete protected Region before cleanup gets its first opportunity.
			const regionProgram = this.recursiveCFGSummary?.rawEmission.program;
			if (
				!this.recursiveRegionIncomplete() && regionProgram &&
				containsDestructuringProtocol(regionProgram)
			) {
				let destructuringChanged = false;
				for (let iteration = 0; iteration < 64; iteration++) {
					if (
						!reduceSequentialObjectDestructuring(this) &&
						!reduceSequentialArrayDestructuring(this) &&
						!reduceNestedRecoveredDestructuring(this)
					) break;
					destructuringChanged = true;
				}
				if (destructuringChanged) {
					runRecursiveCFGAnalysis(this, analysisOptions);
				}
			}
			// Preserve a complete recursive Region before compatibility reducers run.
			// Those reducers can improve incomplete graphs, but on already exact
			// protected forests they may linearize the same CFG back into a multi-block
			// legacy shape and lose the materializable candidate.
			this.initializeMigrationAudit(cfgReducer);
			if (
				!this.recursiveRegionIncomplete() &&
				this.recursiveCFGSummary?.selection.candidate === 'none'
			) {
				this.cleanupRecursiveCFGSummaryEmission();
			}
		}
		if (cfgReducer.materialize !== false) {
			this.tryMaterializeRecursiveCFGEmission(true);
			this.liftFinalBlockPhis();
		}
		this.finalizeMigrationAudit();
		return;
	}

	initializeMigrationAudit(reducer: CFGReducerOptions): void {
		const summary = this.recursiveCFGSummary;
		const mode = reducer.migrationAudit;
		if (!summary || !mode) return;
		summary.migrationAudit = {
			mode,
			normalization: summary.normalization,
			classification: {
				bytecodeVersion: this.file.version,
				generator: this.isNativeGenerator
					? 'native'
					: this.isLoweredGenerator
					? 'lowered'
					: this.isGenerator
					? 'other'
					: 'none',
				async: this.isAsync,
				exceptionHandlerCount: this.exceptions.records.size,
				cfgSize: summary.blockCount <= 16
					? 'small'
					: summary.blockCount <= 64
					? 'medium'
					: 'large',
				branchShapes: summary.unstructuredBranches.map((branch) => ({
					block: branch.block,
					shapes: branch.shapes.slice(),
				})),
			},
			initial: {
				blockCount: summary.blockCount,
				uncoveredBlockCount: summary.uncoveredBlocks.length,
				unresolvedPhiCount: this.unresolvedPhiCount(),
				duplicatedSSABlockCounts: {
					...summary.duplicatedSSABlockCounts,
				},
				misses: summary.misses.slice(),
				loopCoverageIssues: summary.loopCoverageIssues,
				emitDiagnostics: summary.rawEmission.diagnostics.slice(),
				emissionStatus: summary.rawEmission.status,
				programAvailable: summary.rawEmission.program != null,
			},
			passTrace: [],
			firstHealingPass: null,
			guardedPhiRetry: {
				eligible: false,
				attempted: false,
				adopted: false,
				blocksBefore: null,
				blocksAfter: null,
				phisBefore: null,
				phisAfter: null,
			},
			legacyPhiRescue: {
				eligible: false,
				attempted: false,
				shadowOnly: true,
				wouldImprove: false,
				adopted: false,
				blocksBefore: null,
				blocksAfter: null,
				phisBefore: null,
				phisAfter: null,
				error: null,
			},
			destructuringLegacyRescue: {
				eligible: false,
				attempted: false,
				shadowOnly: true,
				wouldImprove: false,
				adopted: false,
				blocksBefore: null,
				blocksAfter: null,
				phisBefore: null,
				phisAfter: null,
				error: null,
			},
			compatibilityPaths: summary.compatibilityPaths.map((event) => ({
				...event,
				entries: event.entries.slice(),
				reasons: event.reasons.slice(),
			})),
			candidateRejections: [],
			bindingCleanupTelemetry: {},
			bindingPerformance: {
				cleanupCalls: 0,
				cleanupIterations: 0,
				cleanupMilliseconds: 0,
				placementChecks: 0,
				placementRewrites: 0,
				placementMilliseconds: 0,
			},
		};
		const reasons = [
			...summary.misses.map((miss) => `miss:${miss}`),
			...summary.rawEmission.diagnostics.map((diagnostic) =>
				`emit:${diagnostic}`
			),
			...(summary.rawEmission.program == null
				? [`status:${summary.rawEmission.status}`]
				: []),
		];
		if (reasons.length > 0) {
			summary.migrationAudit.candidateRejections.push({
				candidate: 'raw-region',
				reasons,
			});
		}
	}

	private recordMigrationPass(
		stage: string,
		name: string,
		result: boolean | 'restart',
		blocksBefore: number,
		phisBefore: number,
	): void {
		const audit = this.recursiveCFGSummary?.migrationAudit;
		if (!audit || !result) return;
		const trace = {
			stage,
			pass: name,
			result: result === 'restart'
				? 'restart' as const
				: 'changed' as const,
			blocksBefore,
			blocksAfter: this.blocks.size,
			phisBefore,
			phisAfter: this.unresolvedPhiCount(),
		};
		if (
			audit.firstHealingPass == null &&
			(audit.initial.misses.length > 0 ||
				audit.initial.emitDiagnostics.length > 0)
		) {
			const result = structureCFG(this, {
				strict: false,
				normalizeForRegions: true,
				validateNormalization: true,
			});
			const summary = summarizeRecursiveCFG(this.id, result);
			const misses = summary.misses.slice();
			const diagnostics = summary.rawEmission.diagnostics.slice();
			const previousTrace = audit.passTrace.findLast((candidate) =>
				candidate.regionMissesAfter != null
			);
			const previousMisses = previousTrace?.regionMissesAfter ??
				audit.initial.misses;
			const previousDiagnostics =
				previousTrace?.regionEmitDiagnosticsAfter ??
					audit.initial.emitDiagnostics;
			Object.assign(trace, {
				regionMissesAfter: misses,
				regionEmitDiagnosticsAfter: diagnostics,
				healedMisses: previousMisses.filter((miss) =>
					!misses.includes(miss)
				),
				healedEmitDiagnostics: previousDiagnostics.filter((
					diagnostic,
				) => !diagnostics.includes(diagnostic)),
				regressedMisses: misses.filter((miss) =>
					!previousMisses.includes(miss)
				),
				regressedEmitDiagnostics: diagnostics.filter((diagnostic) =>
					!previousDiagnostics.includes(diagnostic)
				),
			});
			if (misses.length === 0 && diagnostics.length === 0) {
				audit.firstHealingPass = `${stage}/${name}`;
			}
		}
		audit.passTrace.push(trace);
	}

	finalizeMigrationAudit(): void {
		const summary = this.recursiveCFGSummary;
		const audit = summary?.migrationAudit;
		if (!summary || !audit) return;
		const analysis = summary.postReductionAnalysis ?? summary;
		const finalSingleBlockClean = this.singleBlockReductionIsClean();
		const finalMisses = finalSingleBlockClean
			? []
			: analysis.misses.slice();
		const finalEmitDiagnostics = finalSingleBlockClean
			? []
			: analysis.rawEmission.diagnostics.slice();
		if (
			audit.firstHealingPass == null &&
			(audit.initial.misses.length > 0 ||
				audit.initial.emitDiagnostics.length > 0) &&
			finalMisses.length === 0 &&
			finalEmitDiagnostics.length === 0
		) {
			audit.firstHealingPass = 'multiple-passes-required';
		}
		const postReduction = summary.postReductionAnalysis;
		if (
			postReduction &&
			summary.selection.candidate !== 'post-reduction-region'
		) {
			const reasons = [
				...postReduction.misses.map((miss) => `miss:${miss}`),
				...postReduction.rawEmission.diagnostics.map((diagnostic) =>
					`emit:${diagnostic}`
				),
				...(postReduction.rawEmission.program == null
					? [`status:${postReduction.rawEmission.status}`]
					: []),
			];
			if (reasons.length > 0) {
				audit.candidateRejections.push({
					candidate: 'post-reduction-region',
					reasons,
				});
			}
		}
		const selected = summary.selectedEmission;
		if (selected?.program) {
			recordResidualObjectRestTelemetry(this, selected.program);
			this.placeGeneratedBindings(selected.program);
			if (!this.recursiveMaterializationAnalysisIsClean()) {
				this.recordMigrationCandidateRejection(
					selected.source,
					'CFG analysis is incomplete',
				);
			}
			if (
				!this.isNativeGenerator &&
				hasUnboundGeneratedRegister(selected.program)
			) {
				this.recordMigrationCandidateRejection(
					selected.source,
					'generated registers are unbound',
				);
			}
			if (
				!this.isNativeGenerator &&
				hasUnwrittenGeneratedRegister(selected.program)
			) {
				this.recordMigrationCandidateRejection(
					selected.source,
					'generated registers are never written',
				);
			}
			let hasUnresolvedPhi = false;
			t.traverseFast(selected.program, (node) => {
				if (
					t.isCallExpression(node) &&
					t.isV8IntrinsicIdentifier(node.callee, { name: 'Phi' })
				) {
					hasUnresolvedPhi = true;
					return t.traverseFast.skip;
				}
			});
			if (hasUnresolvedPhi) {
				this.recordMigrationCandidateRejection(
					selected.source,
					'Phi calls remain',
				);
			}
			if (containsRawSwitchIntrinsic(selected.program)) {
				this.recordMigrationCandidateRejection(
					selected.source,
					'raw switch intrinsics remain',
				);
			}
			if (containsDestructuringProtocol(selected.program)) {
				this.recordMigrationCandidateRejection(
					selected.source,
					'destructuring protocol remains',
				);
			}
		}
		audit.final = {
			blockCount: this.blocks.size,
			uncoveredBlockCount: analysis.uncoveredBlocks.length,
			unresolvedPhiCount: this.unresolvedPhiCount(),
			duplicatedSSABlockCounts: {
				...summary.duplicatedSSABlockCounts,
			},
			misses: finalMisses,
			loopCoverageIssues: finalSingleBlockClean
				? []
				: analysis.loopCoverageIssues,
			emitDiagnostics: finalEmitDiagnostics,
			emissionStatus: finalSingleBlockClean
				? 'emitted'
				: analysis.rawEmission.status,
			programAvailable: finalSingleBlockClean ||
				analysis.rawEmission.program != null,
			selectedCandidate: summary.selection.candidate,
			materialized: summary.selection.materialized,
			singleBlockReferenceAvailable:
				summary.reducedFallbackEmission != null ||
				this.blocks.size === 1,
		};
	}

	private recordMigrationCandidateRejection(
		candidate: RecursiveCFGEmission['source'],
		reason: string,
	): void {
		const audit = this.recursiveCFGSummary?.migrationAudit;
		if (!audit) return;
		const existing = audit.candidateRejections.find((rejection) =>
			rejection.candidate === candidate
		);
		if (existing) {
			if (!existing.reasons.includes(reason)) {
				existing.reasons.push(reason);
			}
			return;
		}
		audit.candidateRejections.push({
			candidate,
			reasons: [reason],
		});
	}

	private placeGeneratedBindings(
		program: t.Program,
		recordUnresolved = true,
	): BindingPlacementTreeResult {
		const audit = this.recursiveCFGSummary?.migrationAudit;
		const started = audit ? performance.now() : 0;
		const result = placeGeneratedBindingsInTree(program);
		if (!audit) return result;

		const placement = bindingPlacementAudit(result);
		if (!recordUnresolved) placement.unresolved = 0;
		if (meaningfulBindingPlacementAudit(placement)) {
			audit.bindingPlacement = mergeBindingPlacementAudits(
				audit.bindingPlacement,
				placement,
			);
		}
		audit.bindingPerformance.placementChecks++;
		audit.bindingPerformance.placementMilliseconds += performance.now() -
			started;
		if (result.placed > 0) {
			audit.bindingPerformance.placementRewrites++;
		}
		return result;
	}

	recordBindingCleanupObservation(reason: string, identity: string): void {
		const key = `${reason}:${identity}`;
		if (this.bindingCleanupObservationKeys.has(key)) return;
		this.bindingCleanupObservationKeys.add(key);
		const telemetry = this.recursiveCFGSummary?.migrationAudit
			?.bindingCleanupTelemetry;
		if (!telemetry) return;
		telemetry[reason] = (telemetry[reason] ?? 0) + 1;
	}

	private mergeCompatibilityEvent(
		event: RecursiveCFGCompatibilityEvent,
	): void {
		const audit = this.recursiveCFGSummary?.migrationAudit;
		if (!audit) return;
		const existing = audit.compatibilityPaths.find((candidate) =>
			candidate.path === event.path && candidate.phase === event.phase
		);
		if (!existing) {
			audit.compatibilityPaths.push({
				...event,
				entries: event.entries.slice(),
				reasons: event.reasons.slice(),
			});
			return;
		}
		existing.attempts += event.attempts;
		existing.selections += event.selections;
		existing.entries = [
			...new Set([
				...existing.entries,
				...event.entries,
			]),
		].toSorted((left, right) => left - right);
		existing.reasons = [
			...new Set([
				...existing.reasons,
				...event.reasons,
			]),
		].toSorted();
	}

	private recordCompatibilityPath(
		path: RecursiveCFGCompatibilityPath,
		kind: 'attempt' | 'selection',
		reason: string,
		entry = this.entryAddress,
	): void {
		this.mergeCompatibilityEvent({
			path,
			phase: 'reduction',
			attempts: kind === 'attempt' ? 1 : 0,
			selections: kind === 'selection' ? 1 : 0,
			entries: [entry],
			reasons: [reason],
		});
	}

	private unresolvedPhiCount(): number {
		let count = 0;
		const visit = (node: t.Node) => {
			t.traverseFast(node, (candidate) => {
				if (
					t.isCallExpression(candidate) &&
					t.isV8IntrinsicIdentifier(candidate.callee, { name: 'Phi' })
				) count++;
			});
		};
		for (const block of this.blocks.values()) {
			for (const statement of block.body) {
				visit(statement as t.Statement);
			}
			if (block.branch) visit(block.branch as t.Expression);
		}
		return count;
	}

	/**
	 * Whether Region emission artifacts outlive the materialization decision.
	 *
	 * the recursive CFG output modes and the migration audit read them. They also
	 * ride along in `IRFunctionSnapshot`, where they dominated cold snapshot heads
	 * -- 1,400,491 of 1,469,731 bytes across the v99 generator sample -- so a
	 * plain decompile keeps them only for as long
	 * as materialization needs them and stores a compact summary.
	 */
	private get retainsRecursiveArtifacts(): boolean {
		return this.options.cfgReducer?.retainArtifacts !== false;
	}

	private adoptReductionState(other: IRFunction): void {
		this.params = other.params;
		this.parameterPlan = other.parameterPlan;
		this.plainObjectProjectionSources = other.plainObjectProjectionSources;
		this._exceptionHandlers = other._exceptionHandlers;
		this.mergedBlocks = other.mergedBlocks;
		this.isGenerator = other.isGenerator;
		this.isNativeGenerator = other.isNativeGenerator;
		this.isLoweredGenerator = other.isLoweredGenerator;
		this.isAsync = other.isAsync;
		this.yieldingBlocks = other.yieldingBlocks;
		this.yieldEndBlocks = other.yieldEndBlocks;
		this.yieldRetBlocks = other.yieldRetBlocks;
		this.returnBlocks = other.returnBlocks;
		this.blocks = other.blocks;
		this.objectShapeKeysByRegister = other.objectShapeKeysByRegister;
		this.referencedFunctionIds = other.referencedFunctionIds;
		this.recursiveCFGSummary = other.recursiveCFGSummary;
		this.exceptions = HandlerGraph.fromSnapshot(
			this,
			other.exceptions.snapshot(),
		);
		this.rebuildPredecessorMap();
	}

	private shouldRefreshRecursiveCFGSummaryAfterReduction(): boolean {
		const summary = this.recursiveCFGSummary;
		if (!summary) return false;
		if (summary.misses.length > 0) return true;
		if (summary.emitDiagnostics.length > 0) return true;
		if (this.blocks.size === 1) {
			return summary.selection.candidate === 'none';
		}
		const reachable = this.reachableBlocksFromEntry();
		return reachable.size === 1 &&
			reachable.has(this.entryAddress) &&
			summary.diagnostics.some((diagnostic) =>
				diagnostic.kind === 'unreachableBlock'
			);
	}

	private recursiveMissesPreventMaterialization(
		misses: readonly string[],
	): boolean {
		return misses.some((miss) => miss !== 'loop-control-not-structured');
	}

	private recursiveMaterializationAnalysisIsClean(): boolean {
		const summary = this.recursiveCFGSummary;
		if (!summary) return false;
		if (summary.selectedEmission?.source === 'reduced-fallback') {
			return this.singleBlockReductionIsClean();
		}
		const analysis = summary.selectedEmission?.source === 'raw-region'
			? summary
			: summary.postReductionAnalysis ?? summary;
		const diagnostics = summary.selectedEmission?.diagnostics ??
			analysis.rawEmission.diagnostics;
		return !this.recursiveMissesPreventMaterialization(analysis.misses) &&
			(diagnostics.length === 0 ||
				this.canMaterializeWithFinalizerActionDiagnostics(diagnostics));
	}

	private canMaterializeWithFinalizerActionDiagnostics(
		diagnostics: readonly string[],
	): boolean {
		if (
			!this.isGenerator &&
			!this.isNativeGenerator &&
			!this.isLoweredGenerator
		) return false;
		return diagnostics.length > 0 &&
			diagnostics.every((diagnostic) =>
				diagnostic.startsWith('unplaced finalizer action at ')
			);
	}

	private singleBlockReductionIsClean(): boolean {
		return this.blocks.size === 1 && this.unresolvedPhiCount() === 0;
	}

	private trailingBytecodeReturnRegister(): SSARegister | null {
		let bestAddress = -Infinity;
		let best: SSARegister | null = null;
		for (const [address, block] of this.ssa.basicBlocks) {
			const instruction = block.ssaInstructions.at(-1);
			if (instruction?.instruction !== 'Ret') continue;
			if (address < bestAddress) continue;
			bestAddress = address;
			best = instruction.uses.argument;
		}
		return best;
	}

	private appendMissingSingleBlockReturn(body: t.Statement[]): void {
		if (body.length > 0 && statementAlwaysTerminates(body.at(-1)!)) return;
		const returned = this.trailingBytecodeReturnRegister();
		if (returned == null) return;
		const name = `r${returned.index}_${returned.version}`;
		let referenced = false;
		for (const statement of body) {
			t.traverseFast(statement, (node) => {
				if (t.isIdentifier(node, { name })) referenced = true;
			});
			if (referenced) break;
		}
		if (!referenced) return;
		body.push(t.returnStatement(t.identifier(name)));
	}

	/** Lift Phis left in a single reduced or materialized block. */
	private liftFinalBlockPhis(): void {
		if (this.blocks.size !== 1) return;
		const finalBlock = this.blocks.values().next().value;
		if (!finalBlock) return;
		while (
			liftPhiNodesInBody(finalBlock.body as t.Statement[], {
				includePatternBindings: true,
			})
		) {
			// A lifted join can expose a later Phi with the same pattern source.
		}
		// Phi lifting is deliberately late: materialized Region bodies and the
		// compatibility reducer can both leave their final value selection in Phi
		// form.  Those Phis are also the last obstacle to recognizing the iterator
		// and property protocols emitted for destructuring defaults.  Run only the
		// focused, monotonically consuming destructuring cleanups here rather than
		// replaying the whole post-lift pipeline.
		while (
			reduceSequentialObjectDestructuring(this) ||
			reduceSequentialArrayDestructuring(this) ||
			reduceNestedRecoveredDestructuring(this)
		) {
			// Each successful cleanup consumes at least one protocol sequence.
		}
		if (this.options.cfgReducer?.mode === 'recursive') {
			this.appendMissingSingleBlockReturn(
				finalBlock.body as t.Statement[],
			);
		}
	}

	/**
	 * Why the emitted Region must not replace this function's blocks.
	 *
	 * Two of the reasons are correctness claims -- an unbound register or a
	 * surviving `%Phi` means materialization lost a definition -- and those are
	 * absolute. The other two are quality claims: the emission is semantically
	 * faithful, just not reduced to idiomatic JavaScript, and they exist to give
	 * the compatibility reducer first refusal.
	 *
	 * `lastResort` is set on the final attempt, after every reduction phase has
	 * run. A quality rejection there would leave the function unstructured, and
	 * an unstructured root is not a lesser output -- composition takes only its
	 * entry block, so the rest of the program is silently dropped. A complete
	 * emission carrying a raw intrinsic is strictly better than that, and the
	 * intrinsic is what generated-output validation reports.
	 */
	private recursiveEmissionMaterializationRejection(
		lastResort = false,
	): string | null {
		const emission = this.recursiveCFGSummary?.selectedEmission;
		if (!emission?.program) return 'no Region emission';
		if (!this.recursiveMaterializationAnalysisIsClean()) {
			return 'not materialized because CFG analysis is incomplete';
		}
		// Native generator resume values are modelled outside ordinary lexical
		// bindings until generator cleanup has consumed the Region body. Apply the
		// scope gate to ordinary/lowered functions, where an unbound SSA register is
		// always evidence that Region materialization lost a definition.
		if (
			!this.isNativeGenerator &&
			hasUnboundGeneratedRegister(emission.program)
		) {
			return 'not materialized because generated registers are unbound';
		}
		if (
			!this.isNativeGenerator &&
			hasUnwrittenGeneratedRegister(emission.program)
		) {
			return 'not materialized because generated registers are never written';
		}
		let hasUnresolvedPhi = false;
		t.traverseFast(emission.program, (node) => {
			if (
				t.isCallExpression(node) &&
				t.isV8IntrinsicIdentifier(node.callee, { name: 'Phi' })
			) {
				hasUnresolvedPhi = true;
				return t.traverseFast.skip;
			}
		});
		if (hasUnresolvedPhi) {
			return 'not materialized because Phi calls remain';
		}
		// Quality rejections, deferrable now that recursive materialization has no
		// compatibility reducer fallback.
		if (
			!lastResort &&
			!this.isNativeGenerator &&
			hasUnwrittenGeneratedRegister(emission.program)
		) {
			return 'not materialized because generated registers are never written';
		}
		if (!lastResort && containsRawSwitchIntrinsic(emission.program)) {
			return 'not materialized because raw switch intrinsics remain';
		}
		if (!lastResort && containsDestructuringProtocol(emission.program)) {
			return 'not materialized because destructuring protocol remains';
		}
		return null;
	}

	private tryMaterializeRecursiveCFGEmission(lastResort = false): boolean {
		const summary = this.recursiveCFGSummary;
		const emission = summary?.selectedEmission;
		if (!summary || !emission?.program) return false;
		const rejection = this.recursiveEmissionMaterializationRejection(
			lastResort,
		);
		if (rejection != null) {
			summary.selection.reason =
				`${summary.selection.reason}; ${rejection}`;
			this.recordMigrationCandidateRejection(
				emission.source,
				rejection,
			);
			return false;
		}

		const body = emission.program.body.map((stmt) =>
			t.cloneNode(stmt, true) as LiftedAST<t.Statement>
		);
		const sourceAddresses = new AddressSet<BlockAddr>();
		for (const block of this.blocks.values()) {
			for (const addr of block.sourceAddresses ?? [block.address]) {
				sourceAddresses.add(addr);
			}
		}

		this.blocks = new AddressMap([
			[0, {
				address: 0,
				body,
				consequentAddresses: [],
				kind: 'normal',
				sourceAddresses,
			}],
		]);
		this.rebuildPredecessorMap();
		reduceHermesInternalConditionalMemberAccesses(this);
		this.cleanupLiftedBlocks({ removeUnusedStructuredBindings: true });
		this.refreshReferencedFunctionIds();
		summary.selection.materialized = true;
		return true;
	}

	private recoverEnvironmentInitializers(program: t.Program): void {
		const environmentNames = new Set<string>();
		traverse(program, {
			noScope: true,
			CallExpression(path) {
				if (
					!t.isV8IntrinsicIdentifier(path.node.callee, {
						name: 'expectEnvironment',
					})
				) return;
				const [environment] = path.node.arguments;
				if (t.isIdentifier(environment)) {
					environmentNames.add(environment.name);
				}
			},
		});
		if (environmentNames.size === 0) return;
		const assignedEnvironmentNames = new Set<string>();
		traverse(program, {
			noScope: true,
			AssignmentExpression(path) {
				const left = path.node.left;
				if (t.isIdentifier(left) && environmentNames.has(left.name)) {
					assignedEnvironmentNames.add(left.name);
				}
			},
		});
		const initializers = this.environmentInitializersByRegister();
		const fallbackInitializer = this.environmentInitializerCall(
			'CreateFunctionEnvironment',
			[],
		);
		traverse(program, {
			noScope: true,
			VariableDeclarator(path) {
				const id = path.node.id;
				if (
					!t.isIdentifier(id) || path.node.init != null ||
					!environmentNames.has(id.name) ||
					assignedEnvironmentNames.has(id.name)
				) return;
				path.node.init = t.cloneNode(
					initializers.get(id.name) ?? fallbackInitializer,
					true,
				);
			},
		});
	}

	private environmentInitializerCall(
		name:
			| 'CreateFunctionEnvironment'
			| 'CreateTopLevelEnvironment'
			| 'CreateEnvironment',
		args: t.Expression[],
		address?: number,
	): t.CallExpression {
		const call = t.callExpression(t.v8IntrinsicIdentifier(name), args);
		call.extra = {
			...call.extra,
			parentFunctionId: this.id,
			...(address == null ? {} : { address }),
		};
		return call;
	}

	private environmentInitializersByRegister(): Map<string, t.Expression> {
		const initializers = new Map<string, t.Expression>();
		for (const block of this.ssa.basicBlocks.values()) {
			for (const instruction of block.ssaInstructions) {
				switch (instruction.instruction) {
					case 'CreateFunctionEnvironment':
					case 'CreateTopLevelEnvironment': {
						const args: t.Expression[] = [];
						if (typeof instruction.envSize !== 'undefined') {
							args.push(t.numericLiteral(instruction.envSize));
						}
						initializers.set(
							registerName(instruction.defs.destination),
							this.environmentInitializerCall(
								instruction.instruction,
								args,
								instruction.functionLocalOffset,
							),
						);
						break;
					}
					case 'CreateEnvironment': {
						initializers.set(
							registerName(instruction.defs.destination),
							this.environmentInitializerCall(
								instruction.instruction,
								[
									t.identifier(
										registerName(instruction.uses.parent),
									),
									t.numericLiteral(instruction.envSize),
								],
								instruction.functionLocalOffset,
							),
						);
						break;
					}
				}
			}
		}
		return initializers;
	}

	cleanupRecursiveCFGSummaryEmission(
		emission?: RecursiveCFGEmission,
	): boolean {
		const summary = this.recursiveCFGSummary;
		const candidate = emission ?? summary?.rawEmission;
		if (!summary || !candidate?.program) return false;
		const analysis = emission == null
			? summary
			: summary.postReductionAnalysis ?? summary;
		if (this.recursiveMissesPreventMaterialization(analysis.misses)) {
			return false;
		}
		if (
			candidate.diagnostics.length > 0 &&
			!this.canMaterializeWithFinalizerActionDiagnostics(
				candidate.diagnostics,
			)
		) return false;
		if (!this.file.functions?.[this.id]) return false;

		const temp = IRFunction.fromSnapshot(this.file, this.snapshot());
		temp.options = this.options;
		temp.blocks = new AddressMap([
			[0, {
				address: 0,
				body: candidate.program!.body.map((stmt) =>
					t.cloneNode(stmt, true) as LiftedAST<t.Statement>
				),
				consequentAddresses: [],
				kind: 'normal',
			}],
		]);
		temp.mergedBlocks = new AddressGraph([
			[0, new AddressSet<BlockAddr>([0])],
		]);
		temp.rebuildPredecessorMap();
		// Region emission may place the same SSA definition in mutually exclusive
		// arms even though its uses follow the enclosing statement. Establish that
		// function-wide binding before per-block cleanup; afterwards Babel sees no
		// reference in either arm and can only preserve the initializers as bare
		// expressions, which is too late to recover their destination.
		const materializedProgram = t.program(
			temp.blocks.get(0)!.body as t.Statement[],
		);
		placeGeneratedBindingsInTree(materializedProgram);
		// Region emission can repeat one SSA declaration in sibling arms (or
		// copied protected regions). Babel refuses to construct any scopes for
		// that intermediate tree, so normalize those placements before the
		// binding-based hoist below. cleanupLiftedBlocks performs this again after
		// subsequent rewrites; this early call is specifically its prerequisite.
		normalizeDuplicateRegisterDeclarationsInBody(
			materializedProgram.body,
			`IRFunction:${this.id}.recursiveSummaryEmission`,
		);
		if (hoistUnboundGeneratedBindings(materializedProgram, true)) {
			temp.blocks.get(0)!.body = materializedProgram.body;
		}
		temp.recoverEnvironmentInitializers(materializedProgram);
		// The Region snapshot is captured before the ordinary reducer pipeline
		// normalizes SSA registers defined by GetGlobalObject. Apply that same
		// provenance-based rewrite to the candidate before cleanup; otherwise a
		// hoisted `let rN; rN = global` gives the register a binding and the
		// whole-file TryGetById cleanup deliberately refuses to guess that it is
		// the global object.
		if (temp.file.functions?.[temp.id]) {
			normalizeGlobalObjectRegisterUses(temp);
		}
		reduceHermesInternalConditionalMemberAccesses(temp);
		temp.cleanupLiftedBlocks({
			preserveStructuredTerminalSiblings: true,
			hoistDestructuredParams: false,
			removeUnusedStructuredBindings: true,
		});
		if (reduceDelegateYieldStructuredBodies(temp)) {
			temp.cleanupLiftedBlocks({
				preserveStructuredTerminalSiblings: true,
				hoistDestructuredParams: false,
				removeUnusedStructuredBindings: true,
			});
		}
		rewriteStructuredStatementLists(
			temp.blocks.get(0)!.body as t.Statement[],
			stripStatementsAfterTerminal,
		);

		const block = temp.blocks.get(0);
		if (!block) return false;
		const body = (block.body as t.Statement[]).map((stmt) =>
			t.cloneNode(stmt, true)
		);
		const program = t.program(body);
		hoistUnboundGeneratedBindings(program);
		temp.recoverEnvironmentInitializers(program);
		renameDuplicateLabels(program);

		let selectedProgram = program;
		if (!this.isNativeGenerator) {
			const cleanupHasUnbound = hasUnboundGeneratedRegister(program);
			const cleanupHasUnwritten = hasUnwrittenGeneratedRegister(program);
			if (cleanupHasUnbound) {
				this.recordMigrationCandidateRejection(
					candidate.source,
					'generated registers are unbound after cleanup',
				);
				return false;
			}
			if (cleanupHasUnwritten) {
				const uncleanedProgram = t.program(
					candidate.program!.body.map((stmt) =>
						t.cloneNode(stmt, true) as t.Statement
					),
				);
				hoistUnboundGeneratedBindings(uncleanedProgram);
				temp.recoverEnvironmentInitializers(uncleanedProgram);
				renameDuplicateLabels(uncleanedProgram);
				const uncleanedIsSafe =
					!hasUnboundGeneratedRegister(uncleanedProgram) &&
					!hasUnwrittenGeneratedRegister(uncleanedProgram);
				if (uncleanedIsSafe) {
					selectedProgram = uncleanedProgram;
					this.recordMigrationCandidateRejection(
						candidate.source,
						'cleanup introduced unwritten generated registers; retaining uncleaned Region emission',
					);
				} else {
					this.recordMigrationCandidateRejection(
						candidate.source,
						'generated registers are never written; accepting as recursive last-resort output',
					);
				}
			}
		}
		const selected = summary.selectedEmission?.program;
		if (
			candidate.source === 'post-reduction-region' && selected &&
			iteratorEmissionRegresses(selected, selectedProgram)
		) {
			this.recordMigrationCandidateRejection(
				candidate.source,
				'post-reduction Region emission loses a high-level iterator loop and reintroduces iterator protocol calls',
			);
			return false;
		}
		this.selectRecursiveCFGEmission(
			{
				...candidate,
				statementCount: selectedProgram.body.length,
				program: selectedProgram,
				code: this.retainsRecursiveArtifacts
					? generate(selectedProgram).code
					: undefined,
			},
			candidate.source === 'post-reduction-region'
				? 'post-reduction Region emission is complete'
				: 'raw Region emission is complete',
			analysis.duplicatedSSABlockCounts,
		);
		return true;
	}

	private selectRecursiveCFGEmission(
		emission: RecursiveCFGEmission,
		reason: string,
		duplicatedSSABlockCounts: Readonly<Record<string, number>>,
	): void {
		const summary = this.recursiveCFGSummary;
		if (!summary) return;
		summary.selectedEmission = emission;
		summary.duplicatedSSABlockCounts = {
			...duplicatedSSABlockCounts,
		};
		summary.selection = {
			candidate: emission.source,
			reason,
			materialized: false,
		};
		const audit = summary.migrationAudit;
		if (audit) {
			audit.candidateRejections = audit.candidateRejections.filter(
				(rejection) => rejection.candidate !== emission.source,
			);
		}
		// Compatibility mirrors for external tooling. The independent raw and
		// fallback candidates above remain unchanged.
		summary.emittedProgram = emission.program;
		summary.emittedCode = emission.code;
		summary.emittedStatementCount = emission.statementCount;
		summary.emissionStatus = emission.status;
		summary.emitDiagnostics = emission.diagnostics;
		if (emission.source === 'post-reduction-region') {
			const analysis = summary.postReductionAnalysis;
			if (analysis) {
				summary.misses = analysis.misses.slice();
				summary.loopCoverageIssues = analysis.loopCoverageIssues;
				summary.regionKind = analysis.regionKind;
				summary.regionText = analysis.regionText;
			}
		} else if (emission.source === 'reduced-fallback') {
			summary.misses = [];
			summary.loopCoverageIssues = [];
			summary.regionKind = undefined;
			summary.regionText = undefined;
		}
	}

	private refreshReferencedFunctionIds(): void {
		this.referencedFunctionIds.clear();
		for (const block of this.blocks.values()) {
			const { wrapped } = blockProgramWithBranch(block);
			traverse(
				wrapped,
				{
					noScope: true,
					CallExpression: (call) => {
						if (
							!t.isV8IntrinsicIdentifier(call.node.callee, {
								name: 'getFunctionById',
							})
						) return;

						const index = call.node.arguments[0];
						if (!t.isNumericLiteral(index)) {
							throw new LiftError(
								'Unexpected call to %getFunctionById',
								{ functionId: this.id },
							);
						}

						this.referencedFunctionIds.set(
							index.value,
							(this.referencedFunctionIds.get(index.value) ?? 0) +
								1,
						);
					},
				},
			);
		}
	}

	cleanupLiftedBlocks(
		options: {
			preserveStructuredTerminalSiblings?: boolean;
			hoistDestructuredParams?: boolean;
			removeUnusedStructuredBindings?: boolean;
		} = {},
	) {
		const bindingPerformance = this.recursiveCFGSummary?.migrationAudit
			?.bindingPerformance;
		const cleanupStarted = bindingPerformance ? performance.now() : 0;
		let cleanupIterations = 0;
		const preserveStructuredTerminalSiblings =
			options.preserveStructuredTerminalSiblings === true;
		const removeUnusedStructuredBindings =
			options.removeUnusedStructuredBindings === true;
		const generatorCompletionRegisters = new Set(
			[...this.yieldRetBlocks.values()].map((reg) =>
				`r${reg.index}_${reg.version}`
			),
		);
		for (const block of this.ssa.basicBlocks.values()) {
			for (const instr of block.ssaInstructions) {
				if (instr.instruction !== 'ResumeGenerator') continue;
				generatorCompletionRegisters.add(
					`r${instr.defs.destination.index}_${instr.defs.destination.version}`,
				);
			}
		}

		// Per-block cleanup cannot see uses which still live in another CFG block.
		// Preserve every declaration with a genuine cross-block use until a
		// function-wide binding-placement pass can prove where it belongs. Filtering
		// by initializer shape is unsound: member reads, object construction, and
		// calls are precisely the values most likely to be needed by a successor or
		// handler. Keep an existing marker after Region materialization too, because
		// one materialized block may still contain sibling `if`/`try` scopes which
		// Babel correctly treats as distinct lexical scopes.
		const registerBlocks = new Map<string, Set<BlockAddr>>();
		const registerDeclarations = new Map<
			string,
			LiftedAST<t.VariableDeclaration>[]
		>();
		for (const block of this.blocks.values()) {
			const visit = (root: t.Node) => {
				t.traverseFast(root, (node) => {
					if (node !== root && t.isFunction(node)) {
						return t.traverseFast.skip;
					}
					if (t.isIdentifier(node) && /^r\d+_\d+$/.test(node.name)) {
						const owners = registerBlocks.get(node.name) ??
							new Set();
						owners.add(block.address);
						registerBlocks.set(node.name, owners);
					}
					if (!t.isVariableDeclaration(node)) return;
					const declaration = node as LiftedAST<
						t.VariableDeclaration
					>;
					for (const declarator of node.declarations) {
						if (!t.isIdentifier(declarator.id)) continue;
						if (!/^r\d+_\d+$/.test(declarator.id.name)) continue;
						const declarations = registerDeclarations.get(
							declarator.id.name,
						) ?? [];
						declarations.push(
							declaration,
						);
						registerDeclarations.set(
							declarator.id.name,
							declarations,
						);
					}
				});
			};
			for (const statement of block.body) {
				visit(statement as t.Statement);
			}
			if (block.branch) visit(block.branch as t.Expression);
		}
		for (const [name, declarations] of registerDeclarations) {
			if ((registerBlocks.get(name)?.size ?? 0) < 2) continue;
			for (const declaration of declarations) {
				declaration.extra = {
					...declaration.extra,
					preserveAcrossBlocks: true,
				};
			}
		}

		let provenance: ReturnType<typeof phiContext> | null = null;
		for (const block of this.blocks.values()) {
			simplifyProvenanceResolvedPhiCalls(
				<t.Statement[]> block.body,
				(name) =>
					(provenance ??= phiContext(this)).recoverExpressionForName(
						name,
					),
			);
			liftPhiNodesInBody(<t.Statement[]> block.body);
		}

		const useLegacyFinalizerASTCleanup = false;
		let changed: boolean;
		do {
			cleanupIterations++;
			changed = applyFinalizerCleanupPlan(this);
			changed = reduceSequentialObjectDestructuring(this) ||
				changed;
			for (const block of this.blocks.values()) {
				changed = recoverGuardedObjectDestructuring(
					block.body as t.Statement[],
					this.id,
				) || changed;
			}
			const objectRestBindings = objectRestProtocolBindingNames(this);
			// Phi operands are cross-block by construction: the definition lives in a
			// predecessor while the `%Phi(...)` consuming it sits in the join block.
			// Collecting operands per block would leave such a definition looking
			// unreferenced, and the cleanup below would strip its binding (leaving a bare
			// expression statement), stranding the Phi with operands that no longer have a
			// definition to lift from -- so the protected set spans the whole function.
			const phiSources = new Set<string>();
			for (const block of this.blocks.values()) {
				for (
					const name of phiOperandNames(
						t.program(<t.Statement[]> block.body),
					)
				) phiSources.add(name);
				if (block.branch) {
					for (
						const name of phiOperandNames(block.branch as t.Node)
					) phiSources.add(name);
				}
			}
			for (const block of this.blocks.values()) {
				const scopedProgram = t.program(
					block.body as t.Statement[],
				);
				const placement = this.placeGeneratedBindings(
					scopedProgram,
					false,
				);
				if (placement.placed > 0) {
					block.body = scopedProgram.body as LiftedAST<t.Statement>[];
					changed = true;
				}
				normalizeDuplicateRegisterDeclarationsInBody(
					<t.Statement[]> block.body,
					`IRFunction:${this.id}.cleanupLiftedBlocks.block:${block.address}`,
				);
				changed = foldConditionalValuesInBody(
					<t.Statement[]> block.body,
				) || changed;
				for (const stmt of <t.Statement[]> block.body) {
					changed = refoldConditionalValues(stmt) || changed;
				}
				changed = chainSharedRegisterAssignmentsInBody(
					<t.Statement[]> block.body,
				) || changed;
				const construction = blockProgramWithBranch(block);
				if (
					inlineObjectConstructionsToFixpoint(construction.wrapped) >
						0
				) {
					construction.commit();
					changed = true;
				}
				const { wrapped, commit } = blockProgramWithBranch(block);
				let bindingsStale = false;
				traverse.cache.clear();
				traverse(
					wrapped,
					{
						ExpressionStatement: {
							enter(path) {
								const expr = path.get('expression');
								if (expr.isAssignmentExpression()) {
									const update = assignmentUpdateExpression(
										expr.node,
									);
									if (update) {
										expr.replaceWith(update);
										changed = true;
										return;
									}
									const compound = toCompoundAssignment(
										expr.node as t.AssignmentExpression,
									);
									if (compound) {
										expr.replaceWith(compound);
										changed = true;
										return;
									}
								}
							},
							exit(path) {
								if (inlineNullPrototypeObjectLiteral(path)) {
									changed = true;
									return;
								}
								// Build-up via assignment to a phi register: `rN = {}; rN.x = …`.
								if (inlineObjectConstruction(path)) {
									bindingsStale = true;
									changed = true;
									path.stop();
								}
							},
						},
						VariableDeclaration: {
							exit(decn) {
								if (
									!removeUnusedStructuredBindings &&
									(decn.node as LiftedAST<
										t.VariableDeclaration
									>)
										.extra?.preserveAcrossBlocks
								) return;
								if (postfixUpdateFromToNumericTemp(decn)) {
									changed = true;
									return;
								} else if (inlineObjectConstruction(decn)) {
									bindingsStale = true;
									changed = true;
									decn.stop();
									return;
								}

								const assign = extractRegisterAssign(decn);
								if (!assign) return;

								const { id, init } = assign;
								if (phiSources.has(id.node.name)) return;
								if (objectRestBindings.has(id.node.name)) {
									return;
								}
								// Phi lifting only recognises `%Phi(...)` in declaration or
								// assignment-RHS position. Inlining such an initializer into a
								// larger expression buries the Phi where no later pass can lift
								// it, so leave the declaration alone.
								if (containsPhiCall(init.node)) return;
								if (bindingsStale) return;
								const binding = decn.scope.getBinding(
									id.node.name,
								);
								if (!binding?.constant) return;
								const referencePaths = binding.referencePaths
									.filter((ref) =>
										ref.isIdentifier({
											name: id.node.name,
										}) &&
										nodePathIsAttached(ref)
									);

								const initIsFreelyMovable =
									isFreelyDuplicableInit(init);
								// TODO: remove need for binding
								// at AST lift, populate map of SSA regs to { valueNode, refCount }
								// and replace by traversing at ReferencedIdentifier
								if (
									isCreateThisCall(init) &&
									referencePaths.some(
										isSelectObjectThisArgument,
									)
								) return;
								if (isFromIRCreateClass(init.node)) return;
								if (
									!initIsFreelyMovable &&
									referencePaths.some(
										isHermesEnsureObjectArgument,
									)
								) return;
								if (
									init.isIdentifier() &&
									referencesCrossAssignmentToName(
										decn,
										referencePaths,
										init.node.name,
									)
								) return;
								const mutated = initMutatesName(init);
								if (
									mutated != null &&
									referencePaths.length > 0 &&
									referencesCrossUseOfName(
										decn,
										referencePaths,
										mutated,
									)
								) return;

								if (!initIsFreelyMovable) {
									if (referencePaths.length === 0) {
										if (
											!removeUnusedStructuredBindings &&
											/^r\d+_\d+$/.test(id.node.name) &&
											decn.findParent((path) =>
												path.isTryStatement() &&
												path.node.finalizer != null
											)
										) return;
										if (!init.node.extra?.consumed) {
											if (
												isUnreferencedClosureCreation(
													init,
												) ||
												isDuplicableScalarExpression(
													init.node,
												) || init.isPure()
											) {
												removeStatementWithoutReindex(
													decn,
												);
											} else {
												decn.replaceWith(
													t.expressionStatement(
														init.node,
													),
												);
											}
										} else {
											removeStatementWithoutReindex(decn);
										}
										changed = true;
										return;
									}
									if (referencePaths.length !== 1) return;
									if (
										referencePaths.some((ref) =>
											crossesControlBoundary(decn, ref)
										)
									) return;
								}

								for (const ref of referencePaths) {
									ref.replaceWith(
										t.cloneNode(init.node, true),
									);
								}

								removeStatementWithoutReindex(decn);
								changed = true;
							},
						},
						UnaryExpression: {
							exit(path) {
								if (path.node.operator !== '!') return;
								const argument = path.node.argument;
								// Only rewrite when `invertTest` has a rule for
								// this shape; otherwise it rebuilds the same
								// `!argument` and the fixpoint loop never ends.
								// Structuring inverted this predicate while it
								// was still a bare SSA register, so no rule could
								// fire then. The register's definition has since
								// been inlined underneath, so retry now.
								if (!invertTestSimplifies(argument)) return;
								path.replaceWith(invertTest(
									t.cloneNode(argument, true),
								));
								changed = true;
							},
						},
						CallExpression: {
							enter(call) {
								const callee = call.get('callee');
								const args = call.node.arguments;

								if (
									callee.isV8IntrinsicIdentifier({
										name: 'TryGetById',
									})
								) {
									if (args.length !== 2) return;

									const [g, id] = args;
									if (
										!t.isIdentifier(g, { name: 'global' })
									) return;
									if (!t.isStringLiteral(id)) return;

									call.replaceWith(t.identifier(id.value));
									call.node.extra = {
										isReferencedGlobal: true,
									};
									changed = true;
								} else if (
									callee.isV8IntrinsicIdentifier({
										name: 'ReifyArguments',
									})
								) {
									if (!isUndefinedNode(args[0])) return;
									call.replaceWith(t.identifier('arguments'));
									changed = true;
								} else if (
									callee.isV8IntrinsicIdentifier({
										name: 'SelectObject',
									})
								) {
									const callWithPrototypeArgument =
										selectObjectCallWithPrototypeArgument(
											call,
										);
									if (callWithPrototypeArgument) {
										call.replaceWith(
											callWithPrototypeArgument,
										);
										changed = true;
										return;
									}

									if (!t.isIdentifier(args[0])) return;
									const thisName = args[0].name;
									const thisInit = constIdentifierInit(
										call.scope,
										thisName,
									);
									const newCall = args[1];
									let newCallPath: NodePath<t.CallExpression>;
									let consumedConstructInit:
										| NodePath<t.Expression | null>
										| undefined;
									if (t.isCallExpression(newCall)) {
										newCallPath = call.get(
											'arguments.1',
										) as NodePath<t.CallExpression>;
									} else if (t.isIdentifier(newCall)) {
										const init = constIdentifierInit(
											call.scope,
											newCall.name,
										);
										if (!init?.isCallExpression()) return;
										newCallPath = init;
										consumedConstructInit = init;
									} else return;

									const newCallNode = newCallPath.node;
									if (
										t.isMemberExpression(
											newCallNode.callee,
										) &&
										t.isIdentifier(
											newCallNode.callee.property,
											{ name: 'call' },
										)
									) {
										// TODO: hoist this up into module
										const constructorRef =
											newCallNode.callee.object;
										if (!t.isExpression(constructorRef)) {
											return;
										}
										const resolvedConstructorRef =
											t.isIdentifier(constructorRef)
												? constIdentifierInit(
													call.scope,
													constructorRef.name,
												)?.node ?? constructorRef
												: constructorRef;

										const receiver = newCallNode.arguments[
											0
										];
										const constructNewTarget = thisInit
											? createThisMatchesConstructTarget(
												thisInit.node,
												constructorRef,
											)
											: createThisMatchesConstructTarget(
												receiver,
												constructorRef,
											);
										if (constructNewTarget) {
											const normalizedNewTarget =
												expressionsEqual(
														constructNewTarget,
														constructorRef,
													)
													? resolvedConstructorRef
													: constructNewTarget;
											const implicitConstruct =
												implicitConstructExpression(
													call,
													resolvedConstructorRef,
													newCallNode.arguments
														.slice(1)
														.flatMap((arg) =>
															t.isExpression(
																	arg,
																) ||
																t.isSpreadElement(
																	arg,
																)
																? [t.cloneNode(
																	arg,
																	true,
																)]
																: []
														),
													normalizedNewTarget,
												);
											if (!implicitConstruct) return;

											call.replaceWith(implicitConstruct);

											if (thisInit?.node) {
												thisInit.node.extra ??= {};
												thisInit.node.extra.consumed =
													true;
											}
											changed = true;
											return;
										}
									}

									const replacement =
										constructIntrinsicNewExpression(
											newCallPath,
											thisName,
											thisInit,
										);
									if (!replacement) return;

									call.replaceWith(replacement);

									if (thisInit?.node) {
										thisInit.node.extra ??= {};
										thisInit.node.extra.consumed = true;
									}
									if (consumedConstructInit?.node) {
										consumedConstructInit.node.extra ??= {};
										consumedConstructInit.node.extra
											.consumed = true;
									}
									changed = true;
								} else if (
									callee.isV8IntrinsicIdentifier({
										name: 'Construct',
									})
								) {
									const replacement =
										standaloneConstructNewExpression(call);
									if (!replacement) return;

									call.replaceWith(replacement);
									changed = true;
								} else if (liftHermesApplyCall(call)) {
									changed = true;
								} else if (liftHermesConcatCall(call)) {
									changed = true;
								} else if (
									callee.matchesPattern(
										'HermesInternal.exponentiationOperator',
									)
								) {
									if (args.length !== 2) return;
									const [left, right] = args;
									if (
										!t.isExpression(left) ||
										!t.isExpression(right)
									) return;
									call.replaceWith(
										t.binaryExpression('**', left, right),
									);
									changed = true;
								}
							},
							exit(call) {
								const callee = call.get('callee');
								const args = call.node.arguments;

								if (
									callee.isMemberExpression({
										computed: false,
									}) &&
									callee.get('property').isIdentifier({
										name: 'call',
									}) && args.length >= 1
								) {
									const func = callee.get('object');
									const [receiver, ...callArgs] = args;

									if (!isFromIRCall(call.node)) return;

									if (func.isCallExpression()) {
										const directCallee =
											tryGetByIdCallCallee(
												func.node,
												receiver,
											);
										if (directCallee) {
											call.replaceWith(t.callExpression(
												directCallee,
												callArgs,
											))[0].skip();
											changed = true;
											return;
										}
									}

									if (
										func.isIdentifier() &&
										t.isIdentifier(receiver)
									) {
										const methodInit = constIdentifierInit(
											call.scope,
											func.node.name,
										);
										if (
											methodInit?.isMemberExpression({
												computed: false,
											}) &&
											t.isIdentifier(
												methodInit.node.object,
												{ name: receiver.name },
											)
										) {
											if (methodInit?.node) {
												methodInit.node.extra ??= {};
												methodInit.node.extra.consumed =
													true;
											}
											call.replaceWith(t.callExpression(
												t.cloneNode(
													methodInit.node,
													true,
												),
												callArgs,
											))[0].skip();
											bindingsStale = true;
											changed = true;
											call.stop();
											return;
										}
									}

									if (isUndefinedNode(receiver)) {
										call.replaceWith(t.callExpression(
											func.node,
											callArgs,
										))[0].skip();
										changed = true;
									} else if (func.isMemberExpression()) {
										const object = func.get('object');
										if (object.isIdentifier()) {
											if (
												!t.isIdentifier(receiver, {
													name: object.node.name,
												})
											) return;
										} else if (object.isThisExpression()) {
											if (
												!t.isThisExpression(receiver)
											) return;
										} else {
											return;
										}

										call.replaceWith(t.callExpression(
											func.node,
											callArgs,
										))[0].skip();
										changed = true;
									}
								}
							},
						},
						ReturnStatement(ret) {
							const argument = ret.get('argument');
							if (
								argument.node &&
								argument.isIdentifier() &&
								generatorCompletionRegisters.has(
									argument.node.name,
								) &&
								ret.parentPath.isBlockStatement()
							) {
								const body = ret.parentPath.get('body');
								const index = body.findIndex((stmt) =>
									stmt.node === ret.node
								);
								const prev = index > 0
									? body[index - 1]
									: undefined;
								if (
									prev?.isExpressionStatement() &&
									prev.get('expression').isYieldExpression()
								) {
									ret.remove();
									changed = true;
									return;
								}
							}
							if (isUndefinedNode(ret.node.argument)) {
								ret.node.argument = undefined;
								changed = true;
							}
						},
						IfStatement(ifStmt) {
							const rotated = rotateTerminatingGuardIntoElseIf(
								ifStmt.node,
							);
							if (rotated) {
								ifStmt.replaceWith(rotated);
								changed = true;
								return;
							}
							changed = flattenElseIfBlock(ifStmt.node) ||
								changed;
							const test = ifStmt.get('test');
							const dispatch = functionPrototypeDispatchSource(
								test,
								ifStmt.scope,
							);
							if (!dispatch) return;

							// The fast/slow `functionPrototype{Apply,Call}` dispatch arms compute
							// the same value; the slow (canonical) arm is always correct. When the
							// arms were not reduced to a single statement (e.g. each is
							// `{ pure setup; T = value }`), splice the canonical arm body in place
							// of the whole `if` so downstream inlining sees a straight-line result.
							const canonicalBranch = dispatch.operator === '==='
								? ifStmt.get('alternate')
								: ifStmt.get('consequent');
							const otherBranch = dispatch.operator === '==='
								? ifStmt.get('consequent')
								: ifStmt.get('alternate');
							if (
								otherBranch.hasNode() &&
								canonicalBranch.isBlockStatement() &&
								canonicalBranch.node.body.length > 1
							) {
								ifStmt.replaceWithMultiple(
									canonicalBranch.node.body.map((stmt) =>
										t.cloneNode(stmt, true)
									),
								);
								changed = true;
								return;
							}

							let replacementStmt: NodePath<t.Statement> | null;
							let siblingToRemove: NodePath<t.Statement> | null =
								null;
							if (dispatch.operator === '===') {
								replacementStmt = singleStatementFromBranch(
									ifStmt.get('alternate'),
								);
								if (!replacementStmt) {
									const sibling = nextSiblingStatement(
										ifStmt,
									);
									const consequent =
										singleStatementFromBranch(
											ifStmt.get('consequent'),
										);
									if (
										!sibling ||
										!consequent ||
										!statementAlwaysTerminates(
											<t.Statement> consequent.node,
										) ||
										!statementAlwaysTerminates(
											<t.Statement> sibling.node,
										)
									) return;
									replacementStmt = sibling;
									siblingToRemove = sibling;
								}
							} else {
								replacementStmt = singleStatementFromBranch(
									ifStmt.get('consequent'),
								);
								if (!replacementStmt) return;
								if (!ifStmt.get('alternate').hasNode()) {
									const sibling = nextSiblingStatement(
										ifStmt,
									);
									if (
										!sibling ||
										!statementAlwaysTerminates(
											<t.Statement> replacementStmt.node,
										) ||
										!statementAlwaysTerminates(
											<t.Statement> sibling.node,
										)
									) return;
									siblingToRemove = sibling;
								}
							}

							if (replacementStmt.isExpressionStatement()) {
								const assign = replacementStmt.get(
									'expression',
								);
								if (
									assign.isAssignmentExpression({
										operator: '=',
									})
								) {
									const target = assign.get('left');
									if (target.isIdentifier()) {
										const binding = target.scope.getBinding(
											target.node.name,
										);
										if (
											binding &&
											binding.constantViolations.every((
												p,
											) => ifStmt.isAncestor(p))
										) {
											const decl = binding.path;
											if (decl.isVariableDeclarator()) {
												const decn = decl.parentPath;
												if (
													decn.isVariableDeclaration() &&
													decn.node.declarations
															.length === 1
												) {
													decn.node.kind = 'const';
													decl.get('init')
														.replaceWith(
															assign.node.right,
														);
													ifStmt.remove();
													siblingToRemove?.remove();
													changed = true;
													return;
												}
											}
										}
									}
								}
							}

							const replacement = t.cloneNode(
								replacementStmt.node,
								true,
							);
							ifStmt.replaceWith(replacement);
							siblingToRemove?.remove();
							changed = true;
						},
						ConditionalExpression(expr) {
							const test = expr.get('test');
							const dispatch = functionPrototypeDispatchSource(
								test,
								expr.scope,
							);
							if (!dispatch) return;

							const replacement = dispatch.operator === '==='
								? expr.get('alternate')
								: expr.get('consequent');
							if (!replacement.node) return;
							expr.replaceWith(replacement.node);
							changed = true;
						},
						TryStatement: {
							enter(tryPath) {
								const finalizer = tryPath.get('finalizer');
								if (!finalizer.node) return;

								this.finallyStack.push(finalizer.node.body);
								this.finallyBlocks.add(finalizer.node);
							},
							exit(tryPath) {
								const finalizer = tryPath.get('finalizer');
								if (finalizer.node) {
									this.finallyStack.pop();
									for (
										const suffix of this.finallyStack
											.toReversed()
									) {
										if (
											stripStatementSuffix(
												finalizer.node.body,
												suffix,
											) ||
											stripStatementBeforeTerminalTail(
												finalizer.node.body,
												suffix,
											) ||
											(useLegacyFinalizerASTCleanup &&
												stripLeadingFinalizerCopyBeforeTerminalTail(
													finalizer.node.body,
													suffix,
												))
										) {
											changed = true;
											break;
										}
									}
								}

								const handler = tryPath.get('handler');
								if (handler.node) {
									for (
										const suffix of this.finallyStack
											.toReversed()
									) {
										if (
											stripStatementBeforeTerminalTail(
												handler.node.body.body,
												suffix,
												true,
											) ||
											(useLegacyFinalizerASTCleanup &&
												stripLeadingFinalizerCopyBeforeTerminalTail(
													handler.node.body.body,
													suffix,
													true,
												))
										) {
											changed = true;
											break;
										}
									}
								}

								if (
									tryPath.findParent((path) =>
										path.isBlockStatement() &&
										this.finallyBlocks.has(path.node)
									) &&
									liftCommonTerminalSuffixToFinally(
										tryPath.node,
									)
								) {
									changed = true;
									return;
								}

								const split = splitNestedTerminalFinalizer(
									tryPath.node,
								);
								if (split) {
									tryPath.replaceWith(split);
									tryPath.skip();
									changed = true;
									return;
								}

								const folded = foldEmptyCatchFinallyWrapper(
									tryPath.node,
								);
								if (folded) {
									tryPath.replaceWith(folded);
									tryPath.skip();
									changed = true;
									return;
								}

								if (
									isEmptyDestructuringCatch(tryPath.node)
								) {
									tryPath.replaceWithMultiple(
										tryPath.node.block.body,
									);
									tryPath.skip();
									changed = true;
								}
							},
						},
						BlockStatement: {
							exit(blockPath) {
								if (this.finallyBlocks.has(blockPath.node)) {
									return;
								}
								if (
									stripGeneratorCompletionReturnAfterYield(
										blockPath.node.body,
										generatorCompletionRegisters,
									)
								) {
									changed = true;
									return;
								}
								if (
									blockPath.findParent((path) =>
										path.isBlockStatement() &&
										this.finallyBlocks.has(path.node)
									)
								) return;
								if (
									removeOverwrittenEnvironmentStores(
										blockPath.node.body,
									) ||
									rewriteRethrowCatchTrailingFinalizer(
										blockPath.node.body,
									) ||
									stripConsecutiveRethrowFinalizerCopy(
										blockPath.node.body,
									) ||
									(!preserveStructuredTerminalSiblings &&
										stripStatementsAfterTerminal(
											blockPath.node.body,
										))
								) {
									changed = true;
									return;
								}
								const preserveAbruptCompletion = blockPath
									.parentPath.isCatchClause();

								for (
									const suffix of this.finallyStack
										.toReversed()
								) {
									if (
										stripStatementSuffix(
											blockPath.node.body,
											suffix,
											preserveAbruptCompletion,
										) ||
										stripStatementBeforeTerminal(
											blockPath.node.body,
											suffix,
										) ||
										stripStatementBeforeTerminalTail(
											blockPath.node.body,
											suffix,
											preserveAbruptCompletion,
										) ||
										(useLegacyFinalizerASTCleanup &&
											stripLeadingFinalizerCopyBeforeTerminalTail(
												blockPath.node.body,
												suffix,
												preserveAbruptCompletion,
											))
									) {
										changed = true;
										return;
									}
								}
							},
						},
					},
					undefined,
					{
						finallyStack: <t.Statement[][]> [],
						finallyBlocks: new WeakSet<t.BlockStatement>(),
						seenTerminalTails: new Set<string>(),
					},
				);
				stripEmptyStatements(wrapped);
				commit();
				changed = simplifyScopedPhiCalls(
					block.body as t.Statement[],
				) || changed;
				changed = simplifyScopedPhiDeclarations(
					block.body as t.Statement[],
				) || changed;
				changed = simplifyScopedPhiAssignments(
					block.body as t.Statement[],
				) || changed;
				changed = simplifyGuardedPrimitivePhiCalls(
					block.body as t.Statement[],
				) || changed;
				changed = simplifyTerminalReturnPhis(
					block.body as t.Statement[],
				) || changed;
				changed = liftLoopHeaderPhiAssignments(
					block.body as t.Statement[],
				) || changed;
				changed = simplifyNullGuardedPhiDeclarations(
					block.body as t.Statement[],
				) || changed;
				changed = simplifySelfUpdatePhiAssignments(
					block.body as t.Statement[],
				) || changed;
				changed = removeUnusedPhiExpressions(
					block.body as t.Statement[],
				) || changed;
				if (
					removeOverwrittenEnvironmentStores(
						block.body as t.Statement[],
					) ||
					repairNestedLabelledBreakLoops(
						block.body as t.Statement[],
					) ||
					repairLabelledLoopFinally(
						block.body as t.Statement[],
					) ||
					rewriteRethrowCatchTrailingFinalizer(
						block.body as t.Statement[],
					) ||
					stripConsecutiveRethrowFinalizerCopy(
						block.body as t.Statement[],
					) ||
					(!preserveStructuredTerminalSiblings &&
						stripStatementsAfterTerminal(
							block.body as t.Statement[],
						))
				) {
					changed = true;
				}
			}
			changed = reduceSequentialArrayDestructuring(this) ||
				changed;
			for (const block of this.blocks.values()) {
				changed = cleanupLocalPNameForInLoops(
					block.body as t.Statement[],
				) || changed;
				if (!useLegacyFinalizerASTCleanup) {
					changed = cleanupLocalSyncIteratorForOfLoops(
						block.body as t.Statement[],
					) || changed;
				}
			}
		} while (changed);

		// Forward-exit labels get one more look here, after the fixpoint.
		// `emitRegionToAST` runs the same simplification, but at that point the
		// guards are still spelled out in registers -- the shape it recognises,
		// a chain of bare tests ending in `break`, only appears once the
		// reductions above have folded those registers into the tests. Only the
		// recursive structurer emits these labels, so only it needs the pass.
		if (!useLegacyFinalizerASTCleanup) {
			for (const block of this.blocks.values()) {
				const body = block.body as t.Statement[];
				const simplified = foldGuardedLoopExitTests(
					simplifyForwardExitLabels(body),
				);
				body.splice(0, body.length, ...simplified);
			}
		}
		for (const block of this.blocks.values()) {
			const body = block.body as t.Statement[];
			if (rewriteTwoArgumentCopyDataProperties(t.program(body)) > 0) {
				block.body = body as LiftedAST<t.Statement>[];
			}
		}

		for (const block of this.blocks.values()) {
			stripGeneratorCompletionReturnAfterYield(
				<t.Statement[]> block.body,
				generatorCompletionRegisters,
			);
		}
		this.referencedFunctionIds.clear();
		for (const block of this.blocks.values()) {
			normalizeDuplicateRegisterDeclarationsInBody(
				<t.Statement[]> block.body,
				`IRFunction:${this.id}.referencedFunctionIds.block:${block.address}`,
			);
			const { wrapped } = blockProgramWithBranch(block);
			traverse(
				wrapped,
				{
					noScope: true,
					CallExpression(call) {
						if (
							!t.isV8IntrinsicIdentifier(call.node.callee, {
								name: 'getFunctionById',
							})
						) return;

						const index = call.node.arguments[0];
						if (!t.isNumericLiteral(index)) {
							throw new LiftError(
								'Unexpected call to %getFunctionById',
								{ functionId: this.id },
							);
						}

						this.referencedFunctionIds.set(
							index.value,
							(this.referencedFunctionIds.get(index.value) ?? 0) +
								1,
						);
					},
				},
				undefined,
				this,
			);
		}

		if (this.blocks.size === 1) {
			const entry = this.entryBlock();
			const last = <t.Statement> entry?.body.at(-1);
			if (t.isReturnStatement(last) && !last.argument) {
				entry!.body.pop();
			}
		}

		if (options.hoistDestructuredParams !== false) {
			this.hoistDestructuredParams();
		}
		if (bindingPerformance) {
			bindingPerformance.cleanupCalls++;
			bindingPerformance.cleanupIterations += cleanupIterations;
			bindingPerformance.cleanupMilliseconds += performance.now() -
				cleanupStarted;
		}
	}

	hoistDestructuredParams(): boolean {
		const entry = this.entryBlock();
		if (!entry) return false;
		const body = <t.Statement[]> entry.body;
		const undefinedAliases = destructuringUndefinedAliases(
			t.program(body),
		);
		let changed = false;

		for (let paramIndex = 0; paramIndex < this.params.length;) {
			const paramName = `_param_${this.id}_${paramIndex}_`;
			const currentParam = this.params[paramIndex];
			const existingDefault = t.isAssignmentPattern(currentParam) &&
					t.isIdentifier(currentParam.left, { name: paramName }) &&
					t.isExpression(currentParam.right)
				? currentParam.right
				: undefined;
			const stmt = body[0];
			if (stmt?.extra?.retainParameterSource === true) break;
			const decl = singleDeclarator(stmt);
			if (
				!decl ||
				!(
					t.isArrayPattern(decl.id) ||
					t.isObjectPattern(decl.id) ||
					t.isAssignmentPattern(decl.id)
				) || !t.isExpression(decl.init)
			) break;
			const defaulted = destructuringSourceDefault(
				decl.init,
				paramName,
				undefinedAliases,
			);
			if (
				!defaulted &&
				!t.isIdentifier(decl.init, { name: paramName })
			) break;
			if (
				identifierUseCount(body, paramName) !==
					identifierOccurrences(decl.init, paramName)
			) break;

			this.params[paramIndex] = defaulted || existingDefault
				? t.assignmentPattern(
					decl.id as Parameters<typeof t.assignmentPattern>[0],
					t.cloneNode(
						defaulted?.defaultValue ?? existingDefault!,
						true,
					),
				)
				: decl.id;
			body.shift();
			changed = true;
			paramIndex++;
		}
		if (changed) {
			this.parameterPlan.telemetry.compatibilityFallbackUses++;
			synchronizeParameterPlan(this.parameterPlan, this.params);
			this.params = materializeParameterPlan(this.parameterPlan);
		}
		return changed;
	}

	get name() {
		return this.ssa.name;
	}
	get paramCount() {
		return this.ssa.paramCount;
	}

	entryBlock() {
		return this.blocks.get(0);
	}

	rebuildPredecessorMap() {
		const predecessors = new AddressMap<AddressSet>();
		for (const addr of this.blocks.keys()) {
			predecessors.set(addr, new AddressSet());
		}
		for (const [addr, block] of this.blocks) {
			for (const succ of block.consequentAddresses) {
				const predSet = predecessors.get(succ) ?? new AddressSet();
				predSet.add(addr);
				predecessors.set(succ, predSet);
			}
		}
		this.predecessorMap = predecessors;
		return predecessors;
	}

	cfgPredecessorsOf(target: BlockAddr) {
		const predecessors = new AddressSet<BlockAddr>();
		for (const [addr, block] of this.blocks) {
			if (block.consequentAddresses.includes(target)) {
				predecessors.add(addr);
			}
		}
		return predecessors;
	}

	predecessorsOf(target: BlockAddr) {
		const predecessors = this.cfgPredecessorsOf(target);
		for (const { tryStart, catchOffset } of this._exceptionHandlers) {
			if (catchOffset === target) {
				predecessors.add(tryStart);
			}
		}

		return predecessors;
	}

	setBlock(addr: BlockAddr, block: IRBlock) {
		this.blocks.set(addr, block);
		this.rebuildPredecessorMap();
	}

	setSuccessors(addr: BlockAddr, successors: BlockAddr[]) {
		const block = this.blocks.get(addr);
		if (!block) return;
		block.consequentAddresses = successors;
		this.rebuildPredecessorMap();
	}

	deleteBlock(addr: BlockAddr) {
		const deleted = this.blocks.delete(addr);
		if (deleted) {
			this.predecessorMap.delete(addr);
			for (const predecessors of this.predecessorMap.values()) {
				predecessors.delete(addr);
			}
		}
		return deleted;
	}

	pruneOrphanedBlocks() {
		let changed = false;
		if (this.blocks.has(this.entryAddress)) {
			// A reduction can absorb an entry path into structured AST while leaving
			// behind an SCC whose nodes all still have predecessors. The old
			// predecessor-count pruning cannot remove such a detached loop. Preserve
			// exceptional entry roots, then discard every ordinary block unreachable
			// from either the function entry or a live handler.
			const reachable = new AddressSet<BlockAddr>();
			const pending = [
				this.entryAddress,
				...this.exceptions.liveHandlers(),
			].filter((address) => this.blocks.has(address));
			while (pending.length > 0) {
				const address = pending.pop()!;
				if (reachable.has(address)) continue;
				reachable.add(address);
				const block = this.blocks.get(address);
				if (block) pending.push(...block.consequentAddresses);
			}
			for (const address of [...this.blocks.keys()]) {
				if (reachable.has(address)) continue;
				this.deleteBlock(address);
				this.mergedBlocks.delete(address);
				changed = true;
			}
		}
		// TODO: workaround. remove orphaned blocks with no predecessors that are
		// not the entry point or a live catch handler target. These arise when a
		// catch/finally block is merged but its successor blocks lose all their
		// predecessors; the reducer that performs the merge should own this cleanup.
		for (const addr of [...this.blocks.keys()]) {
			if (addr === 0) continue;
			if (this._exceptionHandlers.some((h) => h.catchOffset === addr)) {
				if (!this.exceptions.liveHandlers().has(addr)) {
					this.deleteBlock(addr);
					changed = true;
					continue;
				}
				const finallyRecord = this.exceptions.finallyRecords.get(addr);
				const hasLiveProtectedBlock = finallyRecord != null &&
					this._exceptionHandlers.some((h) =>
						h.catchOffset === addr &&
						[...this.blocks.keys()].some((blockAddr) =>
							blockAddr !== addr && h.tryStart <= blockAddr &&
							blockAddr < h.tryEnd
						)
					);
				if (finallyRecord == null || hasLiveProtectedBlock) continue;
				this.deleteBlock(addr);
				changed = true;
				continue;
			}
			if (this.predecessorsOf(addr).size === 0) {
				this.deleteBlock(addr);
				changed = true;
			}
		}
		return changed;
	}

	markMergedBlocks(parentAddr: BlockAddr, childAddr: BlockAddr) {
		this.exceptions.notifyBlocksMerged(parentAddr, childAddr);
		this.deleteBlock(childAddr);
		this.mergedBlocks.set(
			parentAddr,
			new AddressSet([parentAddr, childAddr]).union(
				this.mergedBlocks.get(parentAddr) ?? new AddressSet(),
			).union(this.mergedBlocks.get(childAddr) ?? new AddressSet()),
		);
		this.mergedBlocks.delete(childAddr);
	}

	fromIdentifierRef(ref: StringRef) {
		const name = this.file.getIdentifier(ref.stringTableIndex);
		let id;
		if (t.isValidIdentifier(name, true)) {
			id = t.identifier(name);
		} else {
			id = t.stringLiteral(name);
		}
		id.extra = { ref };

		return id;
	}

	/**
	 * A BigIntLiteral carries digits only, so a negative value has to be the
	 * negation of its magnitude rather than a literal of its own.
	 */
	fromBigIntRef(
		ref: BigIntRef,
	): LiftedAST<t.BigIntLiteral> | LiftedAST<t.UnaryExpression> {
		const value = this.file.getBigInt(ref.bigintTableIndex);
		const digits: LiftedAST<t.BigIntLiteral> = t.bigIntLiteral(
			value < 0n ? -value : value,
		);
		if (value >= 0n) {
			digits.extra = { ref };
			return digits;
		}

		const negated: LiftedAST<t.UnaryExpression> = t.unaryExpression(
			'-',
			digits,
		);
		negated.extra = { ref };

		return negated;
	}

	fromStringRef(ref: StringRef) {
		const id: LiftedAST<t.StringLiteral> = t.stringLiteral(
			this.file.getString(ref.stringTableIndex),
		);
		id.extra = { ref };

		return id;
	}

	getBuiltin(builtinNo: number) {
		const builtin = t.cloneNode(
			this.file.versionInfo.builtins[builtinNo],
			true,
		);
		builtin.extra = { isBuiltin: true };

		return builtin;
	}

	getParam(paramIndex: number) {
		// Both spellings are tagged with the same unshifted `LoadParam` index,
		// so a consumer asking `locationOf` gets one answer for `this` and for
		// `_param_<fn>_<i>_` instead of a name test that only sees the latter.
		return tagStorageLocation(
			paramIndex > 0
				? t.identifier(`_param_${this.id}_${paramIndex - 1}_`)
				: t.thisExpression(),
			{
				kind: 'parameter',
				owner: { functionId: this.id },
				parameter: {
					index: paramIndex,
					form: paramIndex > 0 ? 'named' : 'this',
				},
			},
		);
	}

	private liftRestParam(body: t.Statement[]): void {
		if (
			this.params.length > 0 &&
			t.isRestElement(this.params[this.params.length - 1])
		) return;

		// <=v96 miscounted `function.length` (`paramCount`) to include rest parameters
		let restIdx = this.params.length;
		if (this.file.version < 97) {
			restIdx -= 1;
		}
		if (restIdx < 0) return;

		// Case 1: rest is assigned to a var — var _name = HermesInternal.copyRestArgs(N)
		for (let i = 0; i < body.length; i++) {
			const decl = singleDeclarator(body[i], 'var');
			if (
				!decl || !t.isIdentifier(decl.id) ||
				!isCopyRestArgsCall(decl.init, restIdx)
			) continue;
			const sourceName = decl.id.name;
			const restName = `_rest_${this.id}_`;
			body.splice(i, 1);
			if (sourceName !== restName) {
				const wrapped = t.file(t.program(body));
				traverse(wrapped, {
					Identifier(path) {
						if (
							path.isReferencedIdentifier({ name: sourceName })
						) path.replaceWith(t.identifier(restName));
					},
				});
			}
			setRestParameter(
				this.parameterPlan,
				this.id,
				restIdx,
				'copy-rest-intrinsic',
			);
			this.params = materializeParameterPlan(this.parameterPlan);
			return;
		}

		// Case 2: rest is used inline — replace HermesInternal.copyRestArgs(N) nodes in-place
		const restName = `_rest_${this.id}_`;
		let found = false;
		for (const stmt of body) {
			t.traverseFast(stmt, (node) => {
				if (
					node !== stmt &&
					(t.isFunctionExpression(node) ||
						t.isFunctionDeclaration(node) ||
						t.isArrowFunctionExpression(node) ||
						t.isObjectMethod(node) ||
						t.isClassMethod(node))
				) return t.traverseFast.skip;
				if (!isCopyRestArgsCall(node, restIdx)) return;
				found = true;
				const replacement = t.identifier(restName);
				for (const key of Object.keys(node)) {
					delete (node as unknown as Record<string, unknown>)[key];
				}
				Object.assign(node, replacement);
				return t.traverseFast.skip;
			});
		}
		if (found) {
			setRestParameter(
				this.parameterPlan,
				this.id,
				restIdx,
				'copy-rest-intrinsic',
			);
			this.params = materializeParameterPlan(this.parameterPlan);
		}
	}

	getFunctionExpr() {
		const reachable = this.reachableBlocksFromEntry();
		for (const addr of this.blocks.keys()) {
			if (addr !== this.entryAddress && reachable.has(addr)) {
				throw new LiftError(
					`Body is not structured in function ${this.id}; reachable blocks: ${
						[...reachable].sort((a, b) => a - b).map((addr) =>
							`0x${addr.toString(16)}`
						).join(', ')
					}`,
				);
			}
		}
		let body: t.Statement[];
		if (this.blocks.has(0)) {
			body = this.entryBlock()!.body.slice() as t.Statement[];

			const envDecls: t.VariableDeclarator[] = [];
			for (let i = 0; i < this.ssa.envSize; i++) {
				envDecls.push(t.variableDeclarator(
					t.identifier(`_env_${this.id}_${i}`),
				));
			}

			if (envDecls.length) {
				body.unshift(
					t.variableDeclaration('var', envDecls),
				);
			}
			this.liftRestParam(body);
			const placementProgram = t.program(body);
			placeGeneratedBindingsInTree(placementProgram);
			body = placementProgram.body as t.Statement[];
			normalizeDuplicateRegisterDeclarationsInBody(
				body,
				`IRFunction:${this.id}.getFunctionExpr`,
			);
			removeParameterShadowedDeclarations(body, this.params);
		} else if (this.blocks.size === 0) {
			body = [];
		} else {
			throw new LiftError('');
		}

		const func = t.functionExpression(
			this.name && t.isValidIdentifier(this.name)
				? t.identifier(this.name)
				: null,
			this.params as Parameters<typeof t.functionExpression>[1],
			t.blockStatement(body),
			this.isGenerator,
			this.isAsync,
		);
		func.extra = { ...func.extra, parentFunctionId: this.id };
		return func;
	}

	reachableBlocksFromEntry() {
		if (!this.blocks.has(0)) return new Set<BlockAddr>();
		const reachable = new Set<BlockAddr>([0]);
		const stack: BlockAddr[] = [0];
		while (stack.length > 0) {
			const addr = stack.pop()!;
			const block = this.blocks.get(addr);
			if (!block) continue;
			for (const succ of block.consequentAddresses) {
				if (!this.blocks.has(succ) || reachable.has(succ)) continue;
				reachable.add(succ);
				stack.push(succ);
			}
		}
		return reachable;
	}

	tryGetFunctionExpr() {
		if (!this.blocks.has(0) && this.blocks.size > 0) return;
		if (
			[...this.reachableBlocksFromEntry()].some((addr) =>
				addr !== this.entryAddress
			)
		) {
			return;
		}
		return this.getFunctionExpr();
	}

	analyseGeneratorClosure(): GeneratorClosureAnalysis | undefined {
		if (!this.blocks.has(0)) return;
		if (this.blocks.size === 2) {
			const entry = this.blocks.get(0);
			if (
				entry &&
				entry.consequentAddresses.length === 1 &&
				entry.body.length === 1
			) {
				const [succAddr] = entry.consequentAddresses;
				const succ = this.blocks.get(succAddr);
				const yieldStmt = entry.body[0] as t.Statement;
				const retStmt = succ?.body[0] as t.Statement | undefined;
				if (
					succ &&
					succ.consequentAddresses.length === 0 &&
					succ.body.length === 1 &&
					t.isExpressionStatement(yieldStmt) &&
					t.isYieldExpression(yieldStmt.expression, {
						delegate: false,
					}) &&
					t.isReturnStatement(retStmt)
				) {
					return t.functionExpression(
						null,
						this.params.map((param) =>
							t.cloneNode(param, true)
						) as t.FunctionParameter[],
						t.blockStatement([
							t.returnStatement(
								t.cloneNode(yieldStmt.expression, true),
							),
						]),
						true,
					);
				}
			}
		}
		if (this.blocks.size > 1) return;

		const body = <t.Statement[]> this.entryBlock()!.body;
		if (body.length === 3) {
			const [declStmt, nextStmt, retStmt] = body;
			const decl = singleDeclarator(declStmt, 'const') ??
				singleDeclarator(declStmt, 'let') ??
				singleDeclarator(declStmt, 'var');
			if (
				decl &&
				t.isIdentifier(decl.id) &&
				t.isCallExpression(decl.init) &&
				t.isFunctionExpression(decl.init.callee, { generator: true }) &&
				generatorStartsWithYieldUndefined(decl.init.callee) &&
				isNextCallStatement(nextStmt, decl.id.name) &&
				t.isReturnStatement(retStmt) &&
				t.isIdentifier(retStmt.argument, { name: decl.id.name })
			) {
				return t.cloneNode(decl.init.callee, true);
			}

			if (
				decl &&
				t.isIdentifier(decl.id) &&
				t.isCallExpression(decl.init) &&
				t.isV8IntrinsicIdentifier(decl.init.callee, {
					name: 'CreateGenerator',
				}) &&
				isNextCallStatement(nextStmt, decl.id.name) &&
				t.isReturnStatement(retStmt) &&
				t.isIdentifier(retStmt.argument, { name: decl.id.name })
			) {
				const target = createGeneratorTarget(decl.init);
				if (target != null) {
					recordLoweredGeneratorWrapperSlotAliases(
						this.file,
						target.functionId,
						body,
						decl.init.arguments[0],
					);
					return {
						...target,
						skipInitialYieldUndefined: true,
						inlineThroughWrapper: true,
					};
				}
			}
		}

		for (let i = 1; i <= body.length - 3; i++) {
			const declStmt = body[i];
			const nextStmt = body[i + 1];
			const retStmt = body[i + 2];
			if (i + 3 !== body.length) continue;
			const envName = generatorPrimingEnvironmentPrelude(body, i);
			if (envName == null) continue;
			const decl = singleDeclarator(declStmt, 'const') ??
				singleDeclarator(declStmt, 'let') ??
				singleDeclarator(declStmt, 'var');
			if (
				!decl ||
				!t.isIdentifier(decl.id) ||
				!t.isCallExpression(decl.init) ||
				!t.isV8IntrinsicIdentifier(decl.init.callee, {
					name: 'CreateGenerator',
				}) ||
				!isNextCallStatement(nextStmt, decl.id.name) ||
				!t.isReturnStatement(retStmt) ||
				!t.isIdentifier(retStmt.argument, { name: decl.id.name })
			) continue;

			const target = createGeneratorTargetWithEnvironmentName(
				decl.init,
				envName,
			);
			if (target == null) continue;
			recordLoweredGeneratorWrapperSlotAliases(
				this.file,
				target.functionId,
				body,
				decl.init.arguments[0],
			);
			return {
				...target,
				skipInitialYieldUndefined: true,
				inlineThroughWrapper: true,
			};
		}

		if (body.length > 1) {
			const ret = body.at(-1);
			const envName = generatorPrimingEnvironmentPrelude(
				body,
				body.length - 1,
			);
			if (envName != null && t.isReturnStatement(ret)) {
				const arg = ret.argument;
				if (
					t.isCallExpression(arg) &&
					t.isV8IntrinsicIdentifier(arg.callee, {
						name: 'CreateGenerator',
					})
				) {
					const target = createGeneratorTargetWithEnvironmentName(
						arg,
						envName,
					);
					if (target != null) {
						recordLoweredGeneratorWrapperSlotAliases(
							this.file,
							target.functionId,
							body,
							arg.arguments[0],
						);
						return {
							...target,
							skipInitialYieldUndefined: false,
							inlineThroughWrapper: true,
						};
					}
				}
			}
		}

		if (body.length !== 1) return;

		const ret = body[0];
		if (!t.isReturnStatement(ret)) return;

		const arg = ret.argument;
		if (
			!t.isCallExpression(arg) ||
			!t.isV8IntrinsicIdentifier(arg.callee, { name: 'CreateGenerator' })
		) return;

		const target = createGeneratorTarget(arg);
		if (target != null) {
			recordLoweredGeneratorWrapperSlotAliases(
				this.file,
				target.functionId,
				body,
				arg.arguments[0],
			);
			return target;
		}
	}

	analyseAsyncClosure() {
		if (this.blocks.size > 1) return;

		const body = <t.Statement[]> this.entryBlock()!.body;
		const [ret] = body;
		if (!t.isReturnStatement(ret)) return;
		const arg = ret.argument;
		if (
			!t.isCallExpression(arg) || !arg.callee.extra?.isBuiltin ||
			!t.matchesPattern(arg.callee, ['HermesInternal', 'spawnAsync'])
		) return;

		if (arg.arguments.length !== 3) return;
		const [genClosureRef, thisRef, argumentsRef] = arg.arguments;
		if (!t.isThisExpression(thisRef)) return;
		if (!t.isIdentifier(argumentsRef, { name: 'arguments' })) return;

		if (
			!t.isCallExpression(genClosureRef) ||
			!t.isV8IntrinsicIdentifier(genClosureRef.callee, {
				name: this.file.version >= 97
					? 'CreateClosure'
					: 'CreateGeneratorClosure',
			})
		) return;

		const functionId = extractFunctionRef(genClosureRef.arguments[0]);
		if (functionId == null) return;
		return {
			functionId,
			environmentCapture: elidedWrapperEnvironmentCapture(
				body,
				genClosureRef.arguments[1],
			),
		};
	}

	analyseAsyncGeneratorClosure() {
		if (!this.blocks.has(0)) return;
		if (this.blocks.size > 1) return;

		const body = <t.Statement[]> this.entryBlock()!.body;
		return asyncGeneratorFromSingleReturn(body, this.file.version) ??
			asyncGeneratorFromWrapApply(body, this.file.version);
	}

	classExpressionFromFunction(superClass: t.Expression | null) {
		const constructorFunc = this.getFunctionExpr();
		let fields: t.ClassProperty[] = [];
		if (superClass) cleanupDerivedConstructorBody(constructorFunc.body);
		else fields = cleanupBaseConstructorBody(constructorFunc.body);

		const classBody = t.classBody(fields);
		if (constructorFunc.body.body.length > 0) {
			classBody.body.push(
				t.classMethod(
					'constructor',
					t.identifier('constructor'),
					constructorFunc.params,
					constructorFunc.body,
				),
			);
		}

		return t.classExpression(
			constructorFunc.id,
			superClass,
			classBody,
		);
	}
}

// `return _wrapAsyncGenerator(CreateClosure(fn)).apply(this, arguments)` — the legacy
// reducer's shape. Keep snapshot-safe analyses outside IRFunction: worker-restored
// functions are created with Object.create(IRFunction.prototype), which intentionally
// does not carry JavaScript private-field brands.
/**
 * The expression a body hands back, seeing through one temporary.
 *
 * The legacy reducer returned the wrapper call outright; the recursive one
 * routes it through a register first -- `let rX; rX = <call>; return rX;` --
 * so matching only the direct return missed every async generator it lowered.
 */
function returnedExpression(
	body: t.Statement[],
): t.Expression | null | undefined {
	const ret = body.at(-1);
	if (!t.isReturnStatement(ret)) return;
	if (!t.isIdentifier(ret.argument)) return ret.argument;

	const { name } = ret.argument;
	for (const stmt of body) {
		if (
			t.isExpressionStatement(stmt) &&
			t.isAssignmentExpression(stmt.expression, { operator: '=' }) &&
			t.isIdentifier(stmt.expression.left, { name })
		) return stmt.expression.right;

		// `let rX;` declares the temporary without initialising it; the value
		// arrives in the assignment below, so an empty declarator is not the
		// definition being looked for.
		const decl = singleDeclarator(stmt);
		if (decl && t.isIdentifier(decl.id, { name }) && decl.init) {
			return decl.init;
		}
	}
	return;
}

function asyncGeneratorFromSingleReturn(
	body: t.Statement[],
	version: number,
) {
	const arg = returnedExpression(body);
	if (
		!t.isCallExpression(arg) ||
		!t.isMemberExpression(arg.callee, { computed: false })
	) return;

	if (arg.arguments.length !== 2) return;
	const [thisRef, argumentsRef] = arg.arguments;
	if (!t.isThisExpression(thisRef)) return;
	if (!t.isIdentifier(argumentsRef, { name: 'arguments' })) return;

	return asyncGeneratorClosureTarget(body, arg.callee.object, version);
}

// The recursive reducer lowers the `_wrapAsyncGenerator(...).apply(this, arguments)`
// fast/slow dispatch to a multi-statement form:
//   let rX; const rW = _wrapAsyncGenerator(CreateClosure(fn)); rW.apply;
//   rX = HermesInternal.applyArguments(rW, this); return rX;
// Recover it by finding the `_wrapAsyncGenerator` binding and confirming the function
// returns `applyArguments(rW, this)` (directly or via a single temp).
function asyncGeneratorFromWrapApply(body: t.Statement[], version: number) {
	let wrapName: string | null = null;
	let wrapCall: t.Expression | null = null;
	for (const stmt of body) {
		const decl = singleDeclarator(stmt);
		if (
			decl && t.isIdentifier(decl.id) &&
			t.isCallExpression(decl.init) &&
			t.matchesPattern(decl.init.callee, [
				'HermesAsyncIteratorsInternal',
				'_wrapAsyncGenerator',
			])
		) {
			wrapName = decl.id.name;
			wrapCall = decl.init;
		}
	}
	if (wrapName == null || wrapCall == null) return;

	const isApply = (expr: t.Node | null | undefined): boolean =>
		t.isCallExpression(expr) &&
		t.matchesPattern(expr.callee, [
			'HermesInternal',
			'applyArguments',
		]) &&
		expr.arguments.length === 2 &&
		t.isIdentifier(expr.arguments[0], { name: wrapName! }) &&
		t.isThisExpression(expr.arguments[1]);

	const ret = body.at(-1);
	if (!t.isReturnStatement(ret) || ret.argument == null) return;
	if (isApply(ret.argument)) {
		return asyncGeneratorClosureTarget(body, wrapCall, version);
	}
	if (!t.isIdentifier(ret.argument)) return;
	const retName = ret.argument.name;
	for (const stmt of body) {
		if (
			t.isExpressionStatement(stmt) &&
			t.isAssignmentExpression(stmt.expression, { operator: '=' }) &&
			t.isIdentifier(stmt.expression.left, { name: retName }) &&
			isApply(stmt.expression.right)
		) {
			return asyncGeneratorClosureTarget(body, wrapCall, version);
		}
	}
	return;
}

function asyncGeneratorClosureTarget(
	body: t.Statement[],
	wrapCall: t.Node,
	version: number,
): AsyncClosureAnalysis | undefined {
	if (
		!t.isCallExpression(wrapCall) ||
		!t.matchesPattern(wrapCall.callee, [
			'HermesAsyncIteratorsInternal',
			'_wrapAsyncGenerator',
		])
	) return;
	if (wrapCall.arguments.length !== 1) return;
	const [genClosureRef] = wrapCall.arguments;
	if (
		!t.isCallExpression(genClosureRef) ||
		!t.isV8IntrinsicIdentifier(genClosureRef.callee, {
			name: version >= 97 ? 'CreateClosure' : 'CreateGeneratorClosure',
		})
	) return;
	const functionId = extractFunctionRef(genClosureRef.arguments[0]);
	if (functionId == null) return;
	return {
		functionId,
		environmentCapture: elidedWrapperEnvironmentCapture(
			body,
			genClosureRef.arguments[1],
		),
	};
}
