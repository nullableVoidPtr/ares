import * as t from '@babel/types';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import type { SSAInstruction, SSARegister } from '../../../../ssa.ts';
import { AddressMap } from '../../../../utils/map.ts';
import type { CFGEdge, ImmutableCFG } from '../immutableCFG.ts';

export interface EdgePhiAssignment {
	edge: CFGEdge;
	target: t.Identifier;
	value: t.Expression;
}

export interface PhiDescriptor {
	block: BlockAddr;
	target: t.Identifier;
	incoming: Map<BlockAddr, EdgePhiAssignment>;
	exceptionalIncoming: Map<BlockAddr, EdgePhiAssignment>;
}

export interface PhiDescriptorInfo {
	phis: PhiDescriptor[];
	phisByBlock: AddressMap<PhiDescriptor[]>;
	phisByEdgeKey: Map<string, EdgePhiAssignment[]>;
}

export function recoverPhiDescriptors(cfg: ImmutableCFG): PhiDescriptorInfo {
	const phis: PhiDescriptor[] = [];
	const phisByBlock = new AddressMap<PhiDescriptor[]>();
	const phisByEdgeKey = new Map<string, EdgePhiAssignment[]>();
	const definitions = indexDefinitions(cfg);
	const sourceResolver = new PhiSourceResolver(definitions);
	for (const [addr, block] of cfg.blocks) {
		const unresolvedUses = unresolvedPhiUses(block.body);
		const phiInstructions = block.ssaInstructions.filter(isPhiInstruction);
		const usedInstructions = new Set<typeof phiInstructions[number]>();
		for (const use of unresolvedUses) {
			const instr = matchingPhiInstruction(
				use,
				phiInstructions,
				usedInstructions,
			);
			if (!instr) continue;
			usedInstructions.add(instr);
			const target = t.identifier(use.target);
			// Post-reduction Region analysis reuses the original SSA instructions.
			// Once a legacy reducer has lowered a Phi into predecessor assignments,
			// however, replaying the original edge actions duplicates those writes and
			// can leave an otherwise structured edge action unplaceable. The lifted
			// `%Phi` use is the authoritative signal that edge lowering is still
			// required in this CFG snapshot. Its target may have been renamed by a
			// Phi-to-Phi cleanup, so fall back to matching the SSA source multiset.
			const incoming = new Map<BlockAddr, EdgePhiAssignment>();
			const exceptionalIncoming = new Map<
				BlockAddr,
				EdgePhiAssignment
			>();
			const normalSourceKeys = new Map<BlockAddr, string>();
			const exceptionalSourceKeys = new Map<BlockAddr, string>();
			let ambiguous = false;
			for (const [pred, source] of instr.sources) {
				const resolved = sourceResolver.resolve(source);
				for (
					const owner of livePredecessorOwners(
						cfg,
						addr,
						pred,
						'normal',
					)
				) {
					const edge = {
						from: owner,
						to: addr,
						kind: 'normal' as const,
					};
					const assignment = {
						edge,
						target: t.cloneNode(target),
						value: t.cloneNode(resolved.expression, true),
					};
					ambiguous = !setIncoming(
						incoming,
						normalSourceKeys,
						owner,
						resolved.key,
						assignment,
					) || ambiguous;
				}
				for (
					const owner of livePredecessorOwners(
						cfg,
						addr,
						pred,
						'exceptional',
					)
				) {
					const edge = {
						from: owner,
						to: addr,
						kind: 'exceptional' as const,
					};
					const assignment = {
						edge,
						target: t.cloneNode(target),
						value: t.cloneNode(resolved.expression, true),
					};
					ambiguous = !setIncoming(
						exceptionalIncoming,
						exceptionalSourceKeys,
						owner,
						resolved.key,
						assignment,
					) || ambiguous;
				}
			}
			// Contracting two genuinely different Phi edges into one owner loses
			// the control-flow fact needed to choose a value. Leave the intrinsic
			// intact so materialization reports the unsupported contraction rather
			// than silently selecting one source.
			if (ambiguous) continue;
			const descriptor = {
				block: addr,
				target,
				incoming,
				exceptionalIncoming,
			};
			phis.push(descriptor);
			phisByBlock.getWithDefault(addr, () => []).push(descriptor);
			for (const assignment of incoming.values()) {
				const key = edgeKey(assignment.edge);
				const assignments = phisByEdgeKey.get(key) ?? [];
				assignments.push(assignment);
				phisByEdgeKey.set(key, assignments);
			}
		}
	}
	return { phis, phisByBlock, phisByEdgeKey };
}

type DefinitionIndex = Map<string, SSAInstruction>;

interface ResolvedSource {
	key: string;
	expression: t.Expression;
}

function indexDefinitions(cfg: ImmutableCFG): DefinitionIndex {
	const definitions = new Map<string, SSAInstruction>();
	for (const block of cfg.blocks.values()) {
		for (const instruction of block.ssaInstructions) {
			if (instruction.instruction === 'Phi') {
				definitions.set(
					registerKey(instruction.destination),
					instruction,
				);
				continue;
			}
			for (const definition of Object.values(instruction.defs ?? {})) {
				if (!isSSARegister(definition)) continue;
				definitions.set(registerKey(definition), instruction);
			}
		}
	}
	return definitions;
}

/**
 * Resolve same-valued Phi aliases without recursively expanding the SSA graph.
 *
 * Phi dependencies are condensed into SCCs first. A cyclic component carries a
 * loop value whose equality cannot be proved by local source comparison, so it
 * remains unresolved. The acyclic condensation graph is then evaluated once,
 * dependencies first. This is linear in the Phi graph and avoids exponentially
 * revisiting shared subgraphs such as zlib's large inflate state machine.
 */
class PhiSourceResolver {
	readonly #canonicalKeys = new Map<string, string>();
	readonly #collapsedPhis = new Map<string, ResolvedSource>();

	constructor(readonly definitions: DefinitionIndex) {
		this.#analyzePhiGraph();
	}

	resolve(source: SSARegister): ResolvedSource {
		return this.#resolveKnownSource(source);
	}

	#analyzePhiGraph(): void {
		const phiDefinitions = new Map<string, PhiInstruction>();
		for (const [key, definition] of this.definitions) {
			if (isPhiInstruction(definition)) {
				phiDefinitions.set(key, definition);
			}
		}
		const dependencies = new Map<string, Set<string>>();
		for (const [key, definition] of phiDefinitions) {
			const sourcePhis = new Set<string>();
			for (const source of definition.sources.values()) {
				const sourceKey = this.#canonicalKey(source);
				if (phiDefinitions.has(sourceKey)) sourcePhis.add(sourceKey);
			}
			dependencies.set(key, sourcePhis);
		}

		const { components, componentOf } = computePhiComponents(dependencies);
		const componentDependencies = components.map(() => new Set<number>());
		const componentDependents = components.map(() => new Set<number>());
		for (const [from, successors] of dependencies) {
			const fromComponent = componentOf.get(from)!;
			for (const successor of successors) {
				const successorComponent = componentOf.get(successor)!;
				if (fromComponent === successorComponent) continue;
				componentDependencies[fromComponent].add(successorComponent);
				componentDependents[successorComponent].add(fromComponent);
			}
		}

		const remainingDependencies = componentDependencies.map(({ size }) =>
			size
		);
		const ready = remainingDependencies.flatMap((count, component) =>
			count === 0 ? [component] : []
		);
		for (let cursor = 0; cursor < ready.length; cursor++) {
			const componentIndex = ready[cursor];
			const component = components[componentIndex];
			const cyclic = component.length > 1 ||
				dependencies.get(component[0])?.has(component[0]) === true;
			if (!cyclic) {
				const key = component[0];
				this.#tryCollapsePhi(key, phiDefinitions.get(key)!);
			}
			for (const dependent of componentDependents[componentIndex]) {
				remainingDependencies[dependent]--;
				if (remainingDependencies[dependent] === 0) {
					ready.push(dependent);
				}
			}
		}
	}

	#tryCollapsePhi(key: string, definition: PhiInstruction): void {
		let first: ResolvedSource | undefined;
		for (const source of definition.sources.values()) {
			const resolved = this.#resolveKnownSource(source);
			if (!first) {
				first = resolved;
				continue;
			}
			// Once two sources differ this Phi cannot be a transparent alias.
			// Avoid inspecting the remainder of a wide join unnecessarily.
			if (resolved.key !== first.key) return;
		}
		if (first) {
			this.#collapsedPhis.set(key, {
				key: first.key,
				expression: t.cloneNode(first.expression, true),
			});
		}
	}

	#resolveKnownSource(source: SSARegister): ResolvedSource {
		if (source.version === 0) {
			return {
				key: primitiveConstantKey(undefined),
				expression: t.identifier('undefined'),
			};
		}
		const canonicalKey = this.#canonicalKey(source);
		const definition = this.definitions.get(canonicalKey);
		if (definition?.instruction === 'LoadConst') {
			const expression = primitiveConstantExpression(definition.value);
			if (expression) {
				return {
					key: primitiveConstantKey(definition.value),
					expression,
				};
			}
		}
		const collapsed = this.#collapsedPhis.get(canonicalKey);
		if (collapsed) {
			return {
				key: collapsed.key,
				expression: t.cloneNode(collapsed.expression, true),
			};
		}
		return {
			key: canonicalKey,
			expression: identifierForRegister(source),
		};
	}

	#canonicalKey(source: SSARegister): string {
		const sourceKey = registerKey(source);
		const cached = this.#canonicalKeys.get(sourceKey);
		if (cached) return cached;

		let canonical = source;
		const path: string[] = [];
		const seen = new Set<string>();
		let canonicalKey = sourceKey;
		while (true) {
			const key = registerKey(canonical);
			const cachedKey = this.#canonicalKeys.get(key);
			if (cachedKey) {
				canonicalKey = cachedKey;
				break;
			}
			if (seen.has(key)) {
				canonicalKey = key;
				break;
			}
			seen.add(key);
			path.push(key);
			const definition = this.definitions.get(key);
			if (definition?.instruction !== 'Mov') {
				canonicalKey = key;
				break;
			}
			canonical = definition.uses.source;
		}
		for (const key of path) this.#canonicalKeys.set(key, canonicalKey);
		return canonicalKey;
	}
}

interface PhiComponents {
	components: string[][];
	componentOf: Map<string, number>;
}

/** Iterative Kosaraju decomposition; avoids moving the recursion hazard here. */
function computePhiComponents(
	graph: ReadonlyMap<string, ReadonlySet<string>>,
): PhiComponents {
	const order: string[] = [];
	const visited = new Set<string>();
	for (const root of graph.keys()) {
		if (visited.has(root)) continue;
		visited.add(root);
		const stack = [{
			node: root,
			successors: [...(graph.get(root) ?? [])],
			cursor: 0,
		}];
		while (stack.length > 0) {
			const frame = stack.at(-1)!;
			const successor = frame.successors[frame.cursor++];
			if (successor != null) {
				if (visited.has(successor)) continue;
				visited.add(successor);
				stack.push({
					node: successor,
					successors: [...(graph.get(successor) ?? [])],
					cursor: 0,
				});
				continue;
			}
			order.push(frame.node);
			stack.pop();
		}
	}

	const reverse = new Map<string, Set<string>>();
	for (const node of graph.keys()) reverse.set(node, new Set());
	for (const [from, successors] of graph) {
		for (const to of successors) reverse.get(to)!.add(from);
	}
	const components: string[][] = [];
	const componentOf = new Map<string, number>();
	for (let index = order.length - 1; index >= 0; index--) {
		const root = order[index];
		if (componentOf.has(root)) continue;
		const componentIndex = components.length;
		const component: string[] = [];
		const stack = [root];
		componentOf.set(root, componentIndex);
		while (stack.length > 0) {
			const node = stack.pop()!;
			component.push(node);
			for (const predecessor of reverse.get(node) ?? []) {
				if (componentOf.has(predecessor)) continue;
				componentOf.set(predecessor, componentIndex);
				stack.push(predecessor);
			}
		}
		components.push(component);
	}
	return { components, componentOf };
}

function primitiveConstantExpression(value: unknown): t.Expression | null {
	if (
		value !== undefined && value !== null &&
		typeof value !== 'boolean' && typeof value !== 'number' &&
		typeof value !== 'string'
	) return null;
	return t.valueToNode(value) as t.Expression;
}

function primitiveConstantKey(value: unknown): string {
	if (typeof value === 'number') {
		if (Number.isNaN(value)) return 'constant:number:NaN';
		if (Object.is(value, -0)) return 'constant:number:-0';
	}
	return `constant:${typeof value}:${String(value)}`;
}

function livePredecessorOwners(
	cfg: ImmutableCFG,
	target: BlockAddr,
	source: BlockAddr,
	kind: CFGEdge['kind'],
): BlockAddr[] {
	const predecessors = kind === 'normal'
		? cfg.normalPredecessors.get(target)
		: cfg.exceptionalPredecessors.get(target);
	if (!predecessors) return [];
	return [...cfg.ownersOfSource(source)].filter((owner) =>
		predecessors.has(owner)
	);
}

function setIncoming(
	incoming: Map<BlockAddr, EdgePhiAssignment>,
	sourceKeys: Map<BlockAddr, string>,
	owner: BlockAddr,
	sourceKey: string,
	assignment: EdgePhiAssignment,
): boolean {
	const previousKey = sourceKeys.get(owner);
	if (previousKey != null) return previousKey === sourceKey;
	sourceKeys.set(owner, sourceKey);
	incoming.set(owner, assignment);
	return true;
}

function registerKey(reg: SSARegister): string {
	return `r${reg.index}_${reg.version}`;
}

function isSSARegister(value: unknown): value is SSARegister {
	return value != null && typeof value === 'object' &&
		'type' in value && (value as { type?: unknown }).type === 'register' &&
		'index' in value && 'version' in value;
}

interface UnresolvedPhiUse {
	target: string;
	sources: string[];
}

interface PhiInstruction {
	instruction: 'Phi';
	destination: SSARegister;
	sources: AddressMap<SSARegister>;
}

function unresolvedPhiUses(
	body: readonly t.Statement[],
): UnresolvedPhiUse[] {
	const uses: UnresolvedPhiUse[] = [];
	for (const statement of body) {
		if (!t.isVariableDeclaration(statement)) continue;
		for (const declaration of statement.declarations) {
			if (!t.isIdentifier(declaration.id)) continue;
			if (
				!t.isCallExpression(declaration.init) ||
				!t.isV8IntrinsicIdentifier(declaration.init.callee, {
					name: 'Phi',
				})
			) continue;
			uses.push({
				target: declaration.id.name,
				sources: declaration.init.arguments
					.filter(t.isIdentifier)
					.map(({ name }) => name)
					.toSorted(),
			});
		}
	}
	return uses;
}

function matchingPhiInstruction(
	use: UnresolvedPhiUse,
	instructions: readonly PhiInstruction[],
	used: ReadonlySet<PhiInstruction>,
): PhiInstruction | null {
	const available = instructions.filter((instruction) =>
		!used.has(instruction)
	);
	const direct = available.filter((instruction) =>
		registerKey(instruction.destination) === use.target
	);
	if (direct.length === 1) return direct[0];
	if (direct.length > 1 || use.sources.length === 0) return null;
	const matchingSources = available.filter((instruction) => {
		const sources = [...instruction.sources.values()]
			.map(registerKey)
			.toSorted();
		return sources.length === use.sources.length &&
			sources.every((source, index) => source === use.sources[index]);
	});
	return matchingSources.length === 1 ? matchingSources[0] : null;
}

export function edgeKey(edge: CFGEdge): string {
	return `${edge.kind}:${edge.from}->${edge.to}`;
}

function isPhiInstruction(instr: unknown): instr is PhiInstruction {
	return !!instr &&
		typeof instr === 'object' &&
		(instr as { instruction?: unknown }).instruction === 'Phi';
}

function identifierForRegister(reg: SSARegister): t.Identifier {
	return t.identifier(`r${reg.index}_${reg.version}`);
}
