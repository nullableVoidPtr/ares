import * as t from '@babel/types';
import traverse, { NodePath } from '@babel/traverse';
import type { BlockAddr } from '../../../hbc/disassembly/function.ts';
import type {
	SSABasicBlock,
	SSAInstruction,
	SSARegister,
} from '../../../ssa.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import type { IRBlock, LiftedAST } from '../../ast/mod.ts';
import type { DominatorInfo } from '../cfg/algorithms/dominators.ts';
import { CFGAnalyses } from '../cfg/algorithms/mod.ts';
import { debug } from './debug.ts';
import { ImmutableCFG } from '../cfg/immutableCFG.ts';
import type { IRFunction } from '../mod.ts';

interface RewrittenBlock {
	body: t.Statement[];
	branch?: t.Expression;
}
interface PromotedPhi {
	name: string;
	block: BlockAddr;
	destination: SSARegister;
	sources: AddressMap<SSARegister>;
}

function registerIdentifier(func: IRFunction, register: SSARegister) {
	const identifier = t.identifier(
		`r${register.index}_${register.version}`,
	) as LiftedAST<t.Identifier>;
	identifier.extra = {
		sourceRegister: register,
		bindingOwnerFunctionId: func.id,
		recoveredEnvironmentSSA: true,
	};
	return identifier;
}

function candidateDeclaration(
	stmt: t.Statement,
	name: string,
): t.VariableDeclarator | null {
	if (!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1) {
		return null;
	}
	const declaration = stmt.declarations[0];
	return t.isVariableDeclarator(declaration) &&
			t.isIdentifier(declaration.id, { name })
		? declaration
		: null;
}

function candidateAssignment(
	stmt: t.Statement,
	name: string,
): t.AssignmentExpression | null {
	if (!t.isExpressionStatement(stmt)) return null;
	const expression = stmt.expression;
	return t.isAssignmentExpression(expression, { operator: '=' }) &&
			t.isIdentifier(expression.left, { name })
		? expression
		: null;
}

function patternContainsName(pattern: t.Node, name: string) {
	let found = false;
	t.traverseFast(pattern, (node) => {
		if (t.isIdentifier(node, { name })) found = true;
	});
	return found;
}

function containsUnsupportedWrite(node: t.Node, name: string) {
	let found = false;
	const wrapped = t.file(t.program([
		t.isStatement(node)
			? t.cloneNode(node, true)
			: t.expressionStatement(t.cloneNode(node as t.Expression, true)),
	]));
	traverse(wrapped, {
		AssignmentExpression(path: NodePath<t.AssignmentExpression>) {
			if (patternContainsName(path.node.left, name)) found = true;
		},
		UpdateExpression(path: NodePath<t.UpdateExpression>) {
			if (patternContainsName(path.node.argument, name)) found = true;
		},
		VariableDeclarator(path: NodePath<t.VariableDeclarator>) {
			if (patternContainsName(path.node.id, name)) found = true;
		},
	});
	return found;
}

function referencesName(node: t.Node, name: string) {
	let found = false;
	const wrapped = t.file(t.program([
		t.isStatement(node)
			? t.cloneNode(node, true)
			: t.expressionStatement(t.cloneNode(node as t.Expression, true)),
	]));
	traverse(wrapped, {
		Identifier(path: NodePath<t.Identifier>) {
			if (
				path.isReferencedIdentifier() && path.node.name === name
			) found = true;
		},
	});
	return found;
}

function rewriteStatementReferences(
	func: IRFunction,
	stmt: t.Statement,
	name: string,
	current: SSARegister | undefined,
) {
	let missing = false;
	const wrapped = t.file(t.program([stmt]));
	traverse(wrapped, {
		Identifier(path: NodePath<t.Identifier>) {
			if (!path.isReferencedIdentifier() || path.node.name !== name) {
				return;
			}
			if (!current) {
				missing = true;
				return;
			}
			path.replaceWith(registerIdentifier(func, current));
		},
	});
	return { stmt: wrapped.program.body[0], missing };
}

function rewriteExpressionReferences(
	func: IRFunction,
	expr: t.Expression,
	name: string,
	current: SSARegister | undefined,
) {
	const statement = t.expressionStatement(expr);
	const rewritten = rewriteStatementReferences(
		func,
		statement,
		name,
		current,
	);
	return {
		expr: (rewritten.stmt as t.ExpressionStatement).expression,
		missing: rewritten.missing,
	};
}

function materializedDefinition(
	stmt: t.Statement,
	names: ReadonlySet<string>,
): { name: string; value: t.Expression | null } | null {
	if (
		t.isVariableDeclaration(stmt) && stmt.declarations.length === 1
	) {
		const declaration = stmt.declarations[0];
		if (
			t.isIdentifier(declaration.id) && names.has(declaration.id.name)
		) {
			return {
				name: declaration.id.name,
				value: t.isExpression(declaration.init)
					? declaration.init
					: null,
			};
		}
	}
	if (!t.isExpressionStatement(stmt)) return null;
	const expression = stmt.expression;
	if (
		!t.isAssignmentExpression(expression, { operator: '=' }) ||
		!t.isIdentifier(expression.left) ||
		!names.has(expression.left.name) ||
		!t.isExpression(expression.right)
	) return null;
	return { name: expression.left.name, value: expression.right };
}

function definitionCanThrow(value: t.Expression | null) {
	if (value == null || t.isIdentifier(value)) return false;
	return !(
		t.isNullLiteral(value) ||
		t.isBooleanLiteral(value) ||
		t.isNumericLiteral(value) ||
		t.isStringLiteral(value) ||
		t.isBigIntLiteral(value) ||
		t.isFunctionExpression(value) ||
		t.isArrowFunctionExpression(value)
	);
}

/**
 * A landing-pad Phi has one source per predecessor block. Split protected
 * blocks around environment writes so an exceptional edge never needs to
 * represent both the value before a throwing write and the value visible
 * after that write succeeds.
 */
function splitProtectedEnvironmentDefinitions(
	func: IRFunction,
	names: ReadonlySet<string>,
) {
	const sampleBefore = new AddressMap<AddressSet<string>>();
	let nextAddress = Math.max(
		0,
		...func.blocks.keys(),
		...func.ssa.basicBlocks.keys(),
	) + 1;

	for (const [address, original] of [...func.blocks]) {
		const activeHandlers = func.exceptions.activeHandlersAtBlock(address);
		if (activeHandlers.size === 0) continue;
		const segments: Array<{
			body: t.Statement[];
			definition?: { name: string; value: t.Expression | null };
		}> = [];
		let pending: t.Statement[] = [];
		for (const statement of original.body as t.Statement[]) {
			const definition = materializedDefinition(statement, names);
			if (!definition) {
				pending.push(statement);
				continue;
			}
			if (pending.length > 0) {
				segments.push({ body: pending });
				pending = [];
			}
			segments.push({ body: [statement], definition });
		}
		if (segments.length === 0) continue;
		if (pending.length > 0 || original.branch) {
			segments.push({ body: pending });
		}

		const sourceAddresses = new AddressSet(
			original.sourceAddresses ??
				func.mergedBlocks.get(address) ??
				[address],
		);
		const addresses = segments.map((_, index) => {
			if (index === 0) return address;
			while (
				func.blocks.has(nextAddress) ||
				func.ssa.basicBlocks.has(nextAddress)
			) nextAddress++;
			return nextAddress++ as BlockAddr;
		});
		for (let index = 0; index < segments.length; index++) {
			const segment = segments[index];
			const segmentAddress = addresses[index];
			const last = index === segments.length - 1;
			const block: IRBlock = {
				...original,
				address: segmentAddress,
				body: segment.body as LiftedAST<t.Statement>[],
				branch: last ? original.branch : undefined,
				consequentAddresses: last
					? [...original.consequentAddresses]
					: [addresses[index + 1]],
				kind: index === 0 ? original.kind : 'synthetic',
				sourceAddresses: new AddressSet([
					segmentAddress,
					...sourceAddresses,
				]),
				syntheticReason: index === 0
					? original.syntheticReason
					: 'environment-mem2reg-exception-split',
			};
			if (!last) delete block.terminalKind;
			if (index > 0) delete block.handlerFor;
			func.blocks.set(segmentAddress, block);
			func.mergedBlocks.set(
				segmentAddress,
				new AddressSet([segmentAddress, ...sourceAddresses]),
			);
			if (
				segment.definition &&
				definitionCanThrow(segment.definition.value)
			) {
				sampleBefore.getWithDefault(
					segmentAddress,
					() => new AddressSet(),
				).add(segment.definition.name);
			}
		}
		for (const handler of activeHandlers) {
			func.exceptions.addDirectRecord(handler, addresses.slice(1));
		}
	}
	func.rebuildPredecessorMap();
	return sampleBefore;
}

function combinedDominanceFrontier(
	cfg: ImmutableCFG,
	dominators: DominatorInfo,
) {
	const frontiers = new AddressMap<AddressSet<BlockAddr>>();
	for (const address of cfg.blocks.keys()) {
		frontiers.set(address, new AddressSet());
	}
	for (const address of cfg.blocks.keys()) {
		const predecessors = new AddressSet([
			...(cfg.normalPredecessors.get(address) ?? []),
			...(cfg.exceptionalPredecessors.get(address) ?? []),
		]);
		if (predecessors.size < 2) continue;
		for (const predecessor of predecessors) {
			let runner: BlockAddr | null = predecessor;
			while (runner != null && runner !== dominators.idom.get(address)) {
				frontiers.get(runner)?.add(address);
				runner = dominators.idom.get(runner) ?? null;
			}
		}
	}
	return frontiers;
}

/**
 * Compute block-entry liveness for one recovered environment cell before
 * renaming. Protected definitions have already been split into their own
 * blocks, so an exceptional edge either samples the entry value explicitly or
 * the value after the block's definition.
 */
function candidateLiveInBlocks(
	func: IRFunction,
	cfg: ImmutableCFG,
	exceptionSamplesBefore: AddressMap<AddressSet<string>>,
	name: string,
) {
	const usesBeforeDefinition = new AddressSet<BlockAddr>();
	const definitionBlocks = new AddressSet<BlockAddr>();

	for (const [address, block] of func.blocks) {
		let defined = false;
		for (const statement of block.body as t.Statement[]) {
			const declaration = candidateDeclaration(statement, name);
			const assignment = candidateAssignment(statement, name);
			if (declaration || assignment) {
				const value = declaration?.init ?? assignment?.right;
				if (
					!defined && t.isExpression(value) &&
					referencesName(value, name)
				) {
					usesBeforeDefinition.add(address);
				}
				defined = true;
				definitionBlocks.add(address);
				continue;
			}
			if (!defined && referencesName(statement, name)) {
				usesBeforeDefinition.add(address);
			}
		}
		if (
			!defined && block.branch &&
			referencesName(block.branch as t.Expression, name)
		) {
			usesBeforeDefinition.add(address);
		}
	}

	const liveIn = new AddressSet<BlockAddr>(usesBeforeDefinition);
	let changed: boolean;
	do {
		changed = false;
		for (const address of cfg.blocks.keys()) {
			if (liveIn.has(address)) continue;
			const normalNeedsValue = [
				...(cfg.normalSuccessors.get(address) ?? []),
			].some((successor) => liveIn.has(successor));
			const exceptionalNeedsValue = [
				...(cfg.exceptionalSuccessors.get(address) ?? []),
			].some((successor) => liveIn.has(successor));
			if (
				(!definitionBlocks.has(address) &&
					(normalNeedsValue || exceptionalNeedsValue)) ||
				(exceptionalNeedsValue &&
					exceptionSamplesBefore.get(address)?.has(name))
			) {
				liveIn.add(address);
				changed = true;
			}
		}
	} while (changed);
	return liveIn;
}

function promoteCandidate(
	func: IRFunction,
	cfg: ImmutableCFG,
	analyses: CFGAnalyses,
	exceptionSamplesBefore: AddressMap<AddressSet<string>>,
	name: string,
): { blocks: AddressMap<RewrittenBlock>; phis: PromotedPhi[] } | null {
	const declarationSites: Array<{ block: BlockAddr; index: number }> = [];
	const definitionBlocks = new AddressSet<BlockAddr>();
	const accessBlocks = new AddressSet<BlockAddr>();

	for (const [address, block] of func.blocks) {
		for (let i = 0; i < block.body.length; i++) {
			const stmt = block.body[i] as t.Statement;
			if (candidateDeclaration(stmt, name)) {
				declarationSites.push({ block: address, index: i });
				definitionBlocks.add(address);
				accessBlocks.add(address);
				continue;
			}
			if (candidateAssignment(stmt, name)) {
				definitionBlocks.add(address);
				accessBlocks.add(address);
				continue;
			}
			if (containsUnsupportedWrite(stmt, name)) return null;
			if (referencesName(stmt, name)) accessBlocks.add(address);
		}
		if (block.branch) {
			if (
				containsUnsupportedWrite(block.branch as t.Expression, name)
			) return null;
			if (referencesName(block.branch as t.Expression, name)) {
				accessBlocks.add(address);
			}
		}
	}
	if (declarationSites.length !== 1 || definitionBlocks.size === 0) {
		return null;
	}
	for (const address of accessBlocks) {
		if (!analyses.reachability.allReachable.has(address)) return null;
	}

	// TODO: Treat loop-carried iterator cells as a separate proof obligation:
	// prove the header Phi, latch update, and exceptional IteratorClose value
	// before promotion instead of relying on the generic combined frontier.
	const dominators = analyses.loopDominators;
	const dominanceFrontiers = combinedDominanceFrontier(cfg, dominators);
	const liveInBlocks = candidateLiveInBlocks(
		func,
		cfg,
		exceptionSamplesBefore,
		name,
	);
	const phiBlocks = new AddressSet<BlockAddr>();
	for (const definition of definitionBlocks) {
		for (const handler of cfg.exceptionalSuccessors.get(definition) ?? []) {
			if (liveInBlocks.has(handler)) phiBlocks.add(handler);
		}
	}
	const work = [...definitionBlocks, ...phiBlocks];
	while (work.length > 0) {
		const definition = work.pop()!;
		for (const frontier of dominanceFrontiers.get(definition) ?? []) {
			if (!liveInBlocks.has(frontier)) continue;
			if (phiBlocks.has(frontier)) continue;
			phiBlocks.add(frontier);
			if (!definitionBlocks.has(frontier)) work.push(frontier);
		}
	}

	const registerIndex = func.ssa.allocateSyntheticRegisterIndex();
	const rewritten = new AddressMap<RewrittenBlock>();
	for (const [address, block] of func.blocks) {
		rewritten.set(address, {
			body: (block.body as t.Statement[]).map((stmt) =>
				t.cloneNode(stmt, true)
			),
			branch: block.branch
				? t.cloneNode(block.branch as t.Expression, true)
				: undefined,
		});
	}
	const stack: SSARegister[] = [];
	const phiDestinations = new AddressMap<SSARegister>();
	const phiSources = new AddressMap<AddressMap<SSARegister>>();
	for (const address of phiBlocks) {
		phiSources.set(address, new AddressMap());
	}
	const visited = new AddressSet<BlockAddr>();
	let failed = false;

	const visit = (address: BlockAddr) => {
		if (failed) return;
		visited.add(address);
		const block = rewritten.get(address);
		if (!block) {
			failed = true;
			return;
		}
		let definitions = 0;
		if (phiBlocks.has(address)) {
			const destination = func.ssa.allocateRegisterVersion(registerIndex);
			phiDestinations.set(address, destination);
			stack.push(destination);
			definitions++;
		}
		const exceptionalEntry = stack.at(-1);

		for (let i = 0; i < block.body.length; i++) {
			const stmt = block.body[i];
			const declaration = candidateDeclaration(stmt, name);
			const assignment = candidateAssignment(stmt, name);
			if (declaration) {
				const initial = t.isExpression(declaration.init)
					? declaration.init
					: t.identifier('undefined');
				const value = rewriteExpressionReferences(
					func,
					initial,
					name,
					stack.at(-1),
				);
				if (value.missing) {
					failed = true;
					return;
				}
				const destination = func.ssa.allocateRegisterVersion(
					registerIndex,
				);
				block.body[i] = t.variableDeclaration('const', [
					t.variableDeclarator(
						registerIdentifier(func, destination),
						value.expr,
					),
				]);
				stack.push(destination);
				definitions++;
				continue;
			}
			if (assignment) {
				const value = rewriteExpressionReferences(
					func,
					assignment.right,
					name,
					stack.at(-1),
				);
				if (value.missing) {
					failed = true;
					return;
				}
				const destination = func.ssa.allocateRegisterVersion(
					registerIndex,
				);
				block.body[i] = t.variableDeclaration('const', [
					t.variableDeclarator(
						registerIdentifier(func, destination),
						value.expr,
					),
				]);
				stack.push(destination);
				definitions++;
				continue;
			}
			const statement = rewriteStatementReferences(
				func,
				stmt,
				name,
				stack.at(-1),
			);
			if (statement.missing) {
				failed = true;
				return;
			}
			block.body[i] = statement.stmt;
		}
		if (block.branch) {
			const branch = rewriteExpressionReferences(
				func,
				block.branch,
				name,
				stack.at(-1),
			);
			if (branch.missing) {
				failed = true;
				return;
			}
			block.branch = branch.expr;
		}

		const current = stack.at(-1);
		const exceptionalCurrent =
			exceptionSamplesBefore.get(address)?.has(name)
				? exceptionalEntry
				: current;
		const addSource = (
			successor: BlockAddr,
			source: SSARegister | undefined,
		) => {
			const sources = phiSources.get(successor);
			if (!sources) return;
			if (!source) {
				failed = true;
				return;
			}
			const existing = sources.get(address);
			if (
				existing &&
				(existing.index !== source.index ||
					existing.version !== source.version)
			) {
				failed = true;
				return;
			}
			sources.set(address, source);
		};
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			addSource(successor, current);
		}
		for (const successor of cfg.exceptionalSuccessors.get(address) ?? []) {
			addSource(successor, exceptionalCurrent);
		}
		for (const child of dominators.children.get(address) ?? []) {
			visit(child);
		}
		stack.splice(stack.length - definitions, definitions);
	};
	visit(cfg.entry);
	if (failed || [...accessBlocks].some((address) => !visited.has(address))) {
		debug('environment mem2reg rename declined', {
			name,
			failed,
			unvisited: [...accessBlocks].filter((address) =>
				!visited.has(address)
			),
		});
		return null;
	}

	const phis: PromotedPhi[] = [];
	for (const address of phiBlocks) {
		const destination = phiDestinations.get(address);
		const sources = phiSources.get(address);
		if (!destination || !sources) return null;
		const predecessors = new AddressSet([
			...(cfg.normalPredecessors.get(address) ?? []),
			...(cfg.exceptionalPredecessors.get(address) ?? []),
		]).intersection(analyses.reachability.allReachable);
		if (!predecessors.equals(new AddressSet(sources.keys()))) {
			debug('environment mem2reg Phi declined', {
				name,
				block: address,
				predecessors: [...predecessors],
				sources: [...sources.keys()],
			});
			return null;
		}
		const orderedSources = new AddressMap(
			[...sources].toSorted(([left], [right]) => left - right),
		);
		const block = rewritten.get(address);
		if (!block) return null;
		block.body.unshift(t.variableDeclaration('const', [
			t.variableDeclarator(
				registerIdentifier(func, destination),
				t.callExpression(
					t.v8IntrinsicIdentifier('Phi'),
					[...orderedSources.values()].map((source) =>
						registerIdentifier(func, source)
					),
				),
			),
		]));
		phis.push({
			name,
			block: address,
			destination,
			sources: orderedSources,
		});
	}
	return { blocks: rewritten, phis };
}

/** Promote proven non-escaping recovered environment cells into ordinary SSA. */
function materializeExceptionalPhi(
	func: IRFunction,
	cfg: ImmutableCFG,
	phi: PromotedPhi,
	exceptionSamplesBefore: AddressMap<AddressSet<string>>,
) {
	const normalPredecessors = cfg.normalPredecessors.get(phi.block) ??
		new AddressSet<BlockAddr>();
	const exceptionalPredecessors =
		cfg.exceptionalPredecessors.get(phi.block) ??
			new AddressSet<BlockAddr>();
	if (
		normalPredecessors.size > 0 ||
		exceptionalPredecessors.size === 0 ||
		!exceptionalPredecessors.equals(new AddressSet(phi.sources.keys()))
	) return false;

	const targetName = `r${phi.destination.index}_${phi.destination.version}`;
	const targetBlock = func.blocks.get(phi.block);
	const entry = func.blocks.get(func.entryAddress);
	if (!targetBlock || !entry) return false;
	const declarationIndex = (targetBlock.body as t.Statement[]).findIndex(
		(statement) => {
			const declaration = t.isVariableDeclaration(statement) &&
					statement.declarations.length === 1
				? statement.declarations[0]
				: null;
			return declaration != null &&
				t.isIdentifier(declaration.id, { name: targetName }) &&
				t.isCallExpression(declaration.init) &&
				t.isV8IntrinsicIdentifier(declaration.init.callee, {
					name: 'Phi',
				});
		},
	);
	if (declarationIndex < 0) return false;

	targetBlock.body.splice(declarationIndex, 1);
	entry.body.unshift(t.variableDeclaration('let', [
		t.variableDeclarator(registerIdentifier(func, phi.destination)),
	]));
	for (const [predecessor, source] of phi.sources) {
		if (
			source.index === phi.destination.index &&
			source.version === phi.destination.version
		) continue;
		const block = func.blocks.get(predecessor);
		if (!block) return false;
		const assignment = t.expressionStatement(t.assignmentExpression(
			'=',
			registerIdentifier(func, phi.destination),
			registerIdentifier(func, source),
		));
		const definesCell = (block.body as t.Statement[]).some((statement) =>
			materializedDefinition(statement, new Set([phi.name])) != null
		);
		if (
			definesCell &&
			!exceptionSamplesBefore.get(predecessor)?.has(phi.name)
		) {
			block.body.push(assignment);
		} else {
			block.body.unshift(assignment);
		}
	}
	return true;
}

export function promoteRecoveredEnvironmentSlots(
	func: IRFunction,
	materializedNames: ReadonlySet<string>,
) {
	if (materializedNames.size === 0) return 0;
	const exceptionSamplesBefore = splitProtectedEnvironmentDefinitions(
		func,
		materializedNames,
	);
	const cfg = ImmutableCFG.fromIRFunction(func);
	const analyses = new CFGAnalyses(cfg);
	const syntheticInstructions = new AddressMap<SSAInstruction[]>();
	let promoted = 0;
	for (const name of materializedNames) {
		const plan = promoteCandidate(
			func,
			cfg,
			analyses,
			exceptionSamplesBefore,
			name,
		);
		if (!plan) continue;
		for (const [address, rewritten] of plan.blocks) {
			const block = func.blocks.get(address);
			if (!block) continue;
			block.body = rewritten.body;
			block.branch = rewritten.branch;
		}
		for (const phi of plan.phis) {
			if (
				materializeExceptionalPhi(
					func,
					cfg,
					phi,
					exceptionSamplesBefore,
				)
			) continue;
			syntheticInstructions.getWithDefault(phi.block, () => []).push({
				instruction: 'Phi',
				destination: phi.destination,
				sources: phi.sources,
			});
		}
		promoted++;
	}

	let nextSourceAddress = Math.max(
		0,
		...func.blocks.keys(),
		...func.ssa.basicBlocks.keys(),
	) + 1;
	for (const [blockAddress, instructions] of syntheticInstructions) {
		while (
			func.blocks.has(nextSourceAddress) ||
			func.ssa.basicBlocks.has(nextSourceAddress)
		) nextSourceAddress++;
		const sourceAddress = nextSourceAddress++ as BlockAddr;
		func.ssa.basicBlocks.set(sourceAddress, {
			address: sourceAddress,
			instructions: [],
			ssaInstructions: instructions,
			predicate: null,
			consequentAddresses: [],
		} as SSABasicBlock);
		const block = func.blocks.get(blockAddress);
		if (!block) continue;
		block.sourceAddresses = new AddressSet(
			block.sourceAddresses ?? [blockAddress],
		);
		block.sourceAddresses.add(sourceAddress);
	}
	return promoted;
}
