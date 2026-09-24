import * as t from '@babel/types';
import traverse from '@babel/traverse';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import {
	HermesEmpty,
	isStringRef,
} from '../../../hbc/disassembly/instruction.ts';
import type { IRBlock, LiftedAST } from '../../ast/mod.ts';
import { comparableAst } from '../../ast/utils.ts';
import type { PhiInst, SSAInstruction, SSARegister } from '../../../ssa.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import type { IRFunction } from '../mod.ts';

export function registerName(register: SSARegister): string {
	return `r${register.index}_${register.version}`;
}

type Definition = {
	block: BlockAddr;
	instruction: SSAInstruction;
};

export type PhiUse = {
	name: string;
	instruction: PhiInst;
};

export type ResolvedPhiUses = {
	targets: PhiUse[];
	body: t.Statement[];
	inlineCount: number;
};

function isSSARegister(value: unknown): value is SSARegister {
	return value != null && typeof value === 'object' &&
		'index' in value && 'version' in value;
}

/**
 * Indexed SSA provenance used by CFG phi reducers.
 *
 * Definition and phi indexes are immutable because the underlying SSA graph is
 * immutable during CFG reduction. Live owners are refreshed separately because
 * IR blocks are continually merged and deleted.
 */
export class PhiContext {
	readonly #definitions = new Map<string, Definition>();
	readonly #phisByBlock = new AddressMap<PhiInst[]>();
	readonly #canonicalSources = new Map<string, SSARegister>();
	#liveOwnersBySource = new AddressMap<AddressSet<BlockAddr>>();

	constructor(readonly func: IRFunction) {
		for (const [block, basicBlock] of func.ssa.basicBlocks) {
			const phis: PhiInst[] = [];
			for (const instruction of basicBlock.ssaInstructions) {
				if (instruction.instruction === 'Phi') {
					phis.push(instruction);
					this.#definitions.set(
						registerName(instruction.destination),
						{
							block,
							instruction,
						},
					);
					continue;
				}
				for (
					const definition of Object.values(instruction.defs ?? {})
				) {
					if (!isSSARegister(definition)) continue;
					this.#definitions.set(registerName(definition), {
						block,
						instruction,
					});
				}
			}
			this.#phisByBlock.set(block, phis);
		}
		this.refreshLiveOwners();
	}

	refreshLiveOwners(): this {
		this.#liveOwnersBySource = new AddressMap<AddressSet<BlockAddr>>();
		for (const liveAddress of this.func.blocks.keys()) {
			for (
				const sourceAddress of this.mergedSourceAddresses(liveAddress)
			) {
				const owners = this.#liveOwnersBySource.get(sourceAddress) ??
					new AddressSet<BlockAddr>();
				owners.add(liveAddress);
				this.#liveOwnersBySource.set(sourceAddress, owners);
			}
		}
		return this;
	}

	mergedSourceAddresses(address: BlockAddr): AddressSet<BlockAddr> {
		return new AddressSet([address]).union(
			this.func.mergedBlocks.get(address) ?? new AddressSet(),
		);
	}

	liveOwners(sourceAddresses: Iterable<BlockAddr>): AddressSet<BlockAddr> {
		const owners = new AddressSet<BlockAddr>();
		for (const sourceAddress of sourceAddresses) {
			for (
				const owner of this.#liveOwnersBySource.get(sourceAddress) ?? []
			) owners.add(owner);
		}
		return owners;
	}

	phisInMergedBlock(address: BlockAddr): PhiInst[] {
		return [...this.mergedSourceAddresses(address)].flatMap((
			sourceAddress,
		) => this.#phisByBlock.get(sourceAddress) ?? []);
	}

	phiInMergedBlock(address: BlockAddr, name: string): PhiInst | null {
		return this.phisInMergedBlock(address).find((instruction) =>
			registerName(instruction.destination) === name
		) ?? null;
	}

	phiForCall(
		call: t.CallExpression,
		candidates: readonly PhiInst[],
		used: ReadonlySet<PhiInst>,
	): PhiInst | null {
		const arguments_ = call.arguments.filter(t.isIdentifier).map((
			{ name },
		) => name).toSorted();
		if (
			arguments_.length !== call.arguments.length ||
			arguments_.length === 0
		) return null;
		return candidates.find((candidate) => {
			if (used.has(candidate)) return false;
			const sources = [...candidate.sources.values()].map(registerName)
				.toSorted();
			return arguments_.length === sources.length &&
				arguments_.every((name, index) => name === sources[index]);
		}) ?? null;
	}

	/** Resolve leading and inline Phi uses in a detached clone of a body. */
	resolveUses(
		address: BlockAddr,
		leadingNames: readonly string[],
		sourceBody: readonly t.Statement[],
	): ResolvedPhiUses | null {
		const body = sourceBody.map((statement) =>
			t.cloneNode(statement, true)
		) as t.Statement[];
		const candidates = this.phisInMergedBlock(address);
		const used = new Set<PhiInst>();
		const targets: PhiUse[] = [];
		for (const name of leadingNames) {
			const instruction = this.phiInMergedBlock(address, name);
			if (!instruction) return null;
			used.add(instruction);
			targets.push({ name, instruction });
		}

		let complete = true;
		let inlineCount = 0;
		traverse(t.file(t.program(body)), {
			noScope: true,
			Function(path) {
				path.skip();
			},
			CallExpression: (path) => {
				if (
					!t.isV8IntrinsicIdentifier(path.node.callee, {
						name: 'Phi',
					})
				) return;
				inlineCount++;
				const instruction = this.phiForCall(
					path.node,
					candidates,
					used,
				);
				if (!instruction) {
					complete = false;
					return;
				}
				used.add(instruction);
				const name = registerName(instruction.destination);
				targets.push({ name, instruction });
				path.replaceWith(t.identifier(name));
			},
		});
		return complete ? { targets, body, inlineCount } : null;
	}

	sourceForPredecessor(
		phi: Pick<PhiInst, 'sources'>,
		predecessorAddress: BlockAddr,
	): SSARegister | null {
		const predecessorSources = this.mergedSourceAddresses(
			predecessorAddress,
		);
		const sources = [...phi.sources]
			.filter(([sourceAddress]) => predecessorSources.has(sourceAddress))
			.map(([, source]) => source);
		if (sources.length === 0) return null;
		if (sources.length === 1) return sources[0];

		const canonical = sources.map((source) => this.canonicalSource(source));
		const [first] = canonical;
		if (
			canonical.some((source) =>
				registerName(source) !== registerName(first)
			)
		) return null;
		return first;
	}

	canonicalSource(register: SSARegister): SSARegister {
		const originalName = registerName(register);
		const cached = this.#canonicalSources.get(originalName);
		if (cached) return cached;

		let current = register;
		const path: string[] = [];
		const seen = new Set<string>();
		while (!seen.has(registerName(current))) {
			const name = registerName(current);
			seen.add(name);
			path.push(name);
			const definition = this.#definitions.get(name)?.instruction;
			if (definition?.instruction !== 'Mov') break;
			current = definition.uses.source;
		}
		for (const name of path) this.#canonicalSources.set(name, current);
		return current;
	}

	definitionBlock(register: SSARegister): BlockAddr | null {
		return this.#definitions.get(registerName(register))?.block ?? null;
	}

	recoverExpression(register: SSARegister): t.Expression | null {
		const canonical = this.canonicalSource(register);
		const definition = this.#definitions.get(registerName(canonical))
			?.instruction;
		if (!definition) return null;
		if (definition.instruction === 'LoadConst') {
			const { value } = definition;
			if (isStringRef(value)) return this.func.fromStringRef(value);
			if (value === HermesEmpty) return t.identifier('__hermes_empty__');
			if (
				value === undefined || value === null ||
				typeof value === 'boolean' || typeof value === 'number' ||
				typeof value === 'string'
			) return t.valueToNode(value);
			return null;
		}
		if (
			definition.instruction !== 'CreateClosure' &&
			definition.instruction !== 'CreateGeneratorClosure' &&
			definition.instruction !== 'CreateAsyncClosure'
		) return null;
		return t.callExpression(
			t.v8IntrinsicIdentifier(definition.instruction),
			[
				t.callExpression(
					t.v8IntrinsicIdentifier('getFunctionById'),
					[t.numericLiteral(definition.function.functionId)],
				),
				t.identifier(registerName(definition.uses.environment)),
			],
		);
	}

	recoverExpressionForName(name: string): t.Expression | null {
		const definition = this.#definitions.get(name)?.instruction;
		if (!definition) return null;
		if (definition.instruction === 'Phi') {
			return this.recoverExpression(definition.destination);
		}
		const register = Object.values(definition.defs ?? {}).find((
			candidate,
		) => isSSARegister(candidate) && registerName(candidate) === name);
		return isSSARegister(register)
			? this.recoverExpression(register)
			: null;
	}

	sourceExpressionForPredecessor(
		phi: Pick<PhiInst, 'sources'>,
		predecessorAddress: BlockAddr,
	): t.Expression | null {
		const predecessorSources = this.mergedSourceAddresses(
			predecessorAddress,
		);
		const sources = [...phi.sources]
			.filter(([sourceAddress]) => predecessorSources.has(sourceAddress))
			.map(([, source]) => source);
		if (sources.length === 0) return null;

		const canonical = sources.map((source) => this.canonicalSource(source));
		const [first] = canonical;
		const recovered = canonical.map((source) =>
			this.recoverExpression(source)
		);
		if (recovered.every((value): value is t.Expression => value != null)) {
			const [firstRecovered] = recovered;
			const key = JSON.stringify(comparableAst(firstRecovered));
			if (
				recovered.every((value) =>
					JSON.stringify(comparableAst(value)) === key
				)
			) return t.cloneNode(firstRecovered, true);
		}
		if (
			canonical.every((source) =>
				registerName(source) === registerName(first)
			)
		) return t.identifier(registerName(first));
		return null;
	}
}

const contexts = new WeakMap<IRFunction, PhiContext>();

export function phiContext(func: IRFunction): PhiContext {
	let context = contexts.get(func);
	if (!context) {
		context = new PhiContext(func);
		contexts.set(func, context);
	}
	return context.refreshLiveOwners();
}

type BodyRemoval = {
	address: BlockAddr;
	block: IRBlock;
	index: number;
	count: number;
	expected?: t.Node;
};

type ControlFlowReplacement = {
	block: IRBlock;
	branch: IRBlock['branch'];
	successors: BlockAddr[];
};

type ReturnReplacement = {
	statement: t.ReturnStatement;
	expected: t.ReturnStatement['argument'];
	replacement: t.Expression;
};

/** A validated, all-at-once mutation of phi declarations and edge values. */
export class PhiLoweringPlan {
	readonly #appends = new AddressMap<LiftedAST<t.Statement>[]>();
	readonly #bodyReplacements = new AddressMap<LiftedAST<t.Statement>[]>();
	readonly #removals: BodyRemoval[] = [];
	readonly #claimedInitializers = new Set<string>();
	readonly #controlFlow = new AddressMap<ControlFlowReplacement>();
	readonly #returns: ReturnReplacement[] = [];

	constructor(readonly func: IRFunction) {}

	append(address: BlockAddr, ...statements: t.Statement[]): boolean {
		if (!this.func.blocks.has(address)) return false;
		const existing = this.#appends.get(address) ?? [];
		existing.push(...statements as LiftedAST<t.Statement>[]);
		this.#appends.set(address, existing);
		return true;
	}

	declare(
		address: BlockAddr,
		names: readonly string[],
		preserveAcrossBlocks = false,
	): boolean {
		const declaration = t.variableDeclaration(
			'let',
			names.map((name) => t.variableDeclarator(t.identifier(name))),
		) as LiftedAST<t.VariableDeclaration>;
		if (preserveAcrossBlocks) {
			declaration.extra = { preserveAcrossBlocks: true };
		}
		return this.append(address, declaration);
	}

	assign(
		address: BlockAddr,
		target: string,
		source: t.Expression,
	): boolean {
		return this.append(
			address,
			t.expressionStatement(t.assignmentExpression(
				'=',
				t.identifier(target),
				source,
			)),
		);
	}

	replaceBody(
		address: BlockAddr,
		body: Array<t.Statement | LiftedAST<t.Statement>>,
	): boolean {
		if (!this.func.blocks.has(address)) return false;
		this.#bodyReplacements.set(
			address,
			body as LiftedAST<t.Statement>[],
		);
		return true;
	}

	removeBody(address: BlockAddr, index: number, count: number): boolean {
		const block = this.func.blocks.get(address);
		if (!block || index < 0 || index + count > block.body.length) {
			return false;
		}
		this.#removals.push({ address, block, index, count });
		return true;
	}

	replaceControlFlow(
		address: BlockAddr,
		branch: IRBlock['branch'],
		successors: readonly BlockAddr[],
	): boolean {
		const block = this.func.blocks.get(address);
		if (!block) return false;
		this.#controlFlow.set(address, {
			block,
			branch,
			successors: [...successors],
		});
		return true;
	}

	replaceReturnArgument(
		statement: t.ReturnStatement,
		replacement: t.Expression,
	): void {
		this.#returns.push({
			statement,
			expected: statement.argument,
			replacement,
		});
	}

	consumeUnusedInitializer(
		address: BlockAddr,
		name: string,
	): t.Expression | null {
		const claim = `${address}:${name}`;
		if (this.#claimedInitializers.has(claim)) return null;
		const block = this.func.blocks.get(address);
		if (!block) return null;
		const declarationIndex = block.body.findIndex((statement) => {
			if (
				!t.isVariableDeclaration(statement as t.Node, {
					kind: 'const',
				}) ||
				(statement as t.VariableDeclaration).declarations.length !== 1
			) return false;
			const [declaration] =
				(statement as t.VariableDeclaration).declarations;
			return t.isIdentifier(declaration.id, { name }) &&
				declaration.init != null && t.isExpression(declaration.init);
		});
		if (declarationIndex < 0) return null;

		let referenced = false;
		const inspect = (node: t.Node) => {
			t.traverseFast(node, (child) => {
				if (t.isIdentifier(child, { name })) referenced = true;
			});
		};
		for (let index = 0; index < block.body.length; index++) {
			if (index !== declarationIndex) {
				inspect(block.body[index] as t.Node);
			}
		}
		if (block.branch) inspect(block.branch as t.Node);
		if (referenced) return null;

		const declaration = block
			.body[declarationIndex] as t.VariableDeclaration;
		const init = declaration.declarations[0].init;
		if (!init || !t.isExpression(init)) return null;
		this.#claimedInitializers.add(claim);
		this.#removals.push({
			address,
			block,
			index: declarationIndex,
			count: 1,
			expected: declaration,
		});
		return t.cloneNode(init, true);
	}

	commit(): boolean {
		for (const [address] of this.#appends) {
			if (!this.func.blocks.has(address)) return false;
		}
		for (const [address] of this.#bodyReplacements) {
			if (!this.func.blocks.has(address)) return false;
		}
		for (const removal of this.#removals) {
			if (this.func.blocks.get(removal.address) !== removal.block) {
				return false;
			}
			if (
				removal.expected &&
				removal.block.body[removal.index] !== removal.expected
			) return false;
		}
		for (const [address, replacement] of this.#controlFlow) {
			if (this.func.blocks.get(address) !== replacement.block) {
				return false;
			}
		}
		for (const replacement of this.#returns) {
			if (replacement.statement.argument !== replacement.expected) {
				return false;
			}
		}
		for (const removal of this.#removals) {
			if (this.#bodyReplacements.has(removal.address)) return false;
		}

		for (const [address, body] of this.#bodyReplacements) {
			this.func.blocks.get(address)!.body = body;
		}
		const removals = this.#removals.toSorted((left, right) =>
			left.address === right.address
				? right.index - left.index
				: left.address - right.address
		);
		for (const { block, index, count } of removals) {
			block.body.splice(index, count);
		}
		for (const [address, statements] of this.#appends) {
			const body = this.func.blocks.get(address)!.body;
			const markerIndex = trailingSwitchMarkerIndex(body);
			body.splice(markerIndex, 0, ...statements);
		}
		for (const replacement of this.#returns) {
			replacement.statement.argument = replacement.replacement;
		}
		for (
			const { block, branch, successors } of this.#controlFlow.values()
		) {
			block.branch = branch;
			block.consequentAddresses = successors;
		}
		return true;
	}
}

function trailingSwitchMarkerIndex(
	body: readonly LiftedAST<t.Statement>[],
): number {
	const index = body.length - 1;
	const statement = body[index] as t.Statement | undefined;
	if (!t.isExpressionStatement(statement)) return body.length;
	const expression = statement.expression;
	if (!t.isCallExpression(expression)) return body.length;
	if (
		!t.isV8IntrinsicIdentifier(expression.callee, {
			name: 'UIntSwitchImm',
		}) &&
		!t.isV8IntrinsicIdentifier(expression.callee, {
			name: 'StringSwitchImm',
		})
	) return body.length;
	return index;
}
