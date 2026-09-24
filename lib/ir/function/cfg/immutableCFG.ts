import * as t from '@babel/types';
import type { BlockAddr } from '../../../hbc/disassembly/function.ts';
import { AddressGraph } from '../../../utils/graph.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import type { IRBlock } from '../../ast/mod.ts';
import type { IRFunction } from '../mod.ts';
import type { SSAInstruction } from '../../../ssa.ts';
import { StructuringDiagnostics } from './diagnostics.ts';
import {
	normalTerminatorSuccessors,
	type SwitchCaseEdge,
	type Terminator,
} from './terminator.ts';

export type CFGEdgeKind = 'normal' | 'exceptional';

export interface CFGEdge {
	from: BlockAddr;
	to: BlockAddr;
	kind: CFGEdgeKind;
}

export interface CFGBlock {
	address: BlockAddr;
	body: readonly t.Statement[];
	ssaInstructions: readonly SSAInstruction[];
	terminator: Terminator;
	sourceAddresses: AddressSet<BlockAddr>;
	original: IRBlock;
}

export class ImmutableCFG {
	readonly entry: BlockAddr;
	/** Hermes function 0 is the script body, not a JavaScript function body. */
	readonly isScript: boolean;
	/** Terminal-copy ownership must stay with the exception Region reducer. */
	readonly hasExceptionRegions: boolean;
	readonly blocks: AddressMap<CFGBlock>;
	/** Live CFG blocks which own each original SSA/basic-block address. */
	readonly sourceOwners: AddressMap<AddressSet<BlockAddr>>;
	readonly normalSuccessors: AddressGraph;
	readonly normalPredecessors: AddressGraph;
	readonly exceptionalSuccessors: AddressGraph;
	readonly exceptionalPredecessors: AddressGraph;
	readonly diagnostics = new StructuringDiagnostics();

	private constructor(
		entry: BlockAddr,
		blocks: AddressMap<CFGBlock>,
		exceptionalEdges: readonly CFGEdge[] = [],
		isScript = false,
		hasExceptionRegions = false,
	) {
		this.entry = entry;
		this.isScript = isScript;
		this.hasExceptionRegions = hasExceptionRegions;
		this.blocks = blocks;
		this.sourceOwners = indexSourceOwners(blocks);
		this.normalSuccessors = AddressGraph.fromBasicBlocks(blocks);
		this.normalPredecessors = AddressGraph.fromBasicBlocks(blocks);
		this.exceptionalSuccessors = AddressGraph.fromBasicBlocks(blocks);
		this.exceptionalPredecessors = AddressGraph.fromBasicBlocks(blocks);
		this.indexEdges();
		for (const edge of exceptionalEdges) {
			if (edge.kind !== 'exceptional') continue;
			if (!blocks.has(edge.from) || !blocks.has(edge.to)) continue;
			this.exceptionalSuccessors.addEdge(edge.from, edge.to);
			this.exceptionalPredecessors.addEdge(edge.to, edge.from);
		}
	}

	static fromIRFunction(func: IRFunction): ImmutableCFG {
		const blocks = new AddressMap<CFGBlock>();
		for (const [addr, block] of func.blocks) {
			const blockSources = block.sourceAddresses;
			const mergedSources = func.mergedBlocks.get(addr);
			const sourceAddresses =
				blockSources != null && blockSources.size > 0
					? blockSources
					: mergedSources != null && mergedSources.size > 0
					? mergedSources
					: [addr];
			const originalAddresses = new AddressSet<BlockAddr>([addr]).union(
				new AddressSet(sourceAddresses),
			);
			blocks.set(addr, {
				address: addr,
				body: Object.freeze(
					block.body.map((stmt) =>
						t.cloneNode(stmt as t.Statement, true)
					),
				),
				ssaInstructions: Object.freeze(
					[...originalAddresses]
						.toSorted((left, right) => left - right)
						.flatMap((source) =>
							func.ssa.basicBlocks.get(source)?.ssaInstructions ??
								[]
						),
				),
				terminator: terminatorFromIRBlock(addr, block),
				sourceAddresses: new AddressSet(sourceAddresses),
				original: block,
			});
		}
		for (const [addr, block] of blocks) {
			const terminator = pruneMissingSuccessors(block.terminator, blocks);
			if (terminator === block.terminator) continue;
			blocks.set(addr, { ...block, terminator });
		}
		const cfg = new ImmutableCFG(
			func.entryAddress,
			blocks,
			[],
			func.id === 0,
			func.exceptions.records.size > 0,
		);
		cfg.indexExceptionalEdges(func);
		cfg.validate();
		return cfg;
	}

	/**
	 * Return a CFG restricted to `addresses`, preserving block payloads,
	 * provenance, normal terminators, and exceptional edges. This is the only
	 * construction path used by Region graph normalization: normalization never
	 * mutates the function-level IR or emits structured statements.
	 */
	restrictTo(addresses: ReadonlySet<BlockAddr>): ImmutableCFG {
		const blocks = new AddressMap<CFGBlock>();
		for (
			const address of [...addresses].toSorted((left, right) =>
				left - right
			)
		) {
			const block = this.blocks.get(address);
			if (block) blocks.set(address, block);
		}
		const cfg = new ImmutableCFG(
			this.entry,
			blocks,
			this.exceptionalEdges(),
			this.isScript,
			this.hasExceptionRegions,
		);
		cfg.validate();
		return cfg;
	}

	normalEdges(): CFGEdge[] {
		return [...this.normalSuccessors].flatMap(([from, successors]) =>
			[...successors].map((to) => ({ from, to, kind: 'normal' as const }))
		);
	}

	exceptionalEdges(): CFGEdge[] {
		return [...this.exceptionalSuccessors].flatMap(([from, successors]) =>
			[...successors].map((to) => ({
				from,
				to,
				kind: 'exceptional' as const,
			}))
		);
	}

	allEdges(): CFGEdge[] {
		return [...this.normalEdges(), ...this.exceptionalEdges()];
	}

	/** Resolve an original SSA/basic-block address to its current CFG owners. */
	ownersOfSource(source: BlockAddr): AddressSet<BlockAddr> {
		return new AddressSet(this.sourceOwners.get(source) ?? []);
	}

	private indexEdges() {
		for (const [addr, block] of this.blocks) {
			for (const succ of normalTerminatorSuccessors(block.terminator)) {
				if (!this.blocks.has(succ)) continue;
				this.normalSuccessors.addEdge(addr, succ);
				this.normalPredecessors.addEdge(succ, addr);
			}
		}
	}

	private indexExceptionalEdges(func: IRFunction) {
		for (const [handler, record] of func.exceptions.records) {
			const handlerOwners = this.ownersOfSource(handler);
			for (const source of record.protectedBlocks) {
				for (const sourceOwner of this.ownersOfSource(source)) {
					for (const handlerOwner of handlerOwners) {
						// A reduction may merge a protected instruction and its
						// landing pad into one structured block. There is then no
						// inter-block exceptional edge left to index.
						if (sourceOwner === handlerOwner) continue;
						this.exceptionalSuccessors.addEdge(
							sourceOwner,
							handlerOwner,
						);
						this.exceptionalPredecessors.addEdge(
							handlerOwner,
							sourceOwner,
						);
					}
				}
			}
		}
	}

	private validate() {
		for (const [addr, block] of this.blocks) {
			for (const succ of normalTerminatorSuccessors(block.terminator)) {
				if (this.blocks.has(succ)) continue;
				this.diagnostics.add({
					kind: 'invalidTerminator',
					entry: addr,
					message: `normal successor 0x${
						succ.toString(16)
					} is missing`,
				});
			}
		}
	}
}

function indexSourceOwners(
	blocks: AddressMap<CFGBlock>,
): AddressMap<AddressSet<BlockAddr>> {
	const owners = new AddressMap<AddressSet<BlockAddr>>();
	for (const [liveAddress, block] of blocks) {
		for (
			const source of new AddressSet<BlockAddr>([liveAddress]).union(
				block.sourceAddresses,
			)
		) {
			owners.getWithDefault(source, () => new AddressSet()).add(
				liveAddress,
			);
		}
	}
	return owners;
}

function terminatorFromIRBlock(addr: BlockAddr, block: IRBlock): Terminator {
	const successors = block.consequentAddresses;
	const switchTerminator = switchTerminatorFromIRBlock(block);
	if (switchTerminator) return switchTerminator;

	if (block.branch) {
		if (successors.length === 2) {
			return {
				kind: 'if',
				test: t.cloneNode(block.branch as t.Expression, true),
				fallthrough: successors[0],
				taken: successors[1],
			};
		}
		if (successors.length === 0) {
			return { kind: 'unreachable' };
		}
		return { kind: 'goto', target: successors[0] };
	}

	const terminal = block.body.at(-1) as t.Statement | undefined;
	if (t.isReturnStatement(terminal)) {
		return {
			kind: 'return',
			argument: terminal.argument
				? t.cloneNode(terminal.argument, true)
				: terminal.argument,
		};
	}
	if (t.isThrowStatement(terminal) && t.isExpression(terminal.argument)) {
		return {
			kind: 'throw',
			argument: t.cloneNode(terminal.argument, true),
		};
	}
	if (successors.length === 1) return { kind: 'goto', target: successors[0] };
	if (successors.length === 0) return { kind: 'unreachable' };
	return { kind: 'goto', target: successors[0] };
}

function pruneMissingSuccessors(
	terminator: Terminator,
	blocks: AddressMap<CFGBlock>,
): Terminator {
	switch (terminator.kind) {
		case 'goto':
			return blocks.has(terminator.target)
				? terminator
				: { kind: 'unreachable' };
		case 'if': {
			const hasFallthrough = blocks.has(terminator.fallthrough);
			const hasTaken = blocks.has(terminator.taken);
			if (hasFallthrough && hasTaken) return terminator;
			if (hasFallthrough) {
				return { kind: 'goto', target: terminator.fallthrough };
			}
			if (hasTaken) return { kind: 'goto', target: terminator.taken };
			return { kind: 'unreachable' };
		}
		case 'switch': {
			const cases = terminator.cases.filter((edge) =>
				blocks.has(edge.target)
			);
			const hasDefault = blocks.has(terminator.defaultTarget);
			if (cases.length === terminator.cases.length && hasDefault) {
				return terminator;
			}
			if (hasDefault) return { ...terminator, cases };
			if (cases.length === 1) {
				return { kind: 'goto', target: cases[0].target };
			}
			if (cases.length === 0) return { kind: 'unreachable' };
			return {
				...terminator,
				cases: cases.slice(0, -1),
				defaultTarget: cases.at(-1)!.target,
			};
		}
		case 'return':
		case 'throw':
		case 'unreachable':
			return terminator;
	}
}

function switchTerminatorFromIRBlock(block: IRBlock): Terminator | null {
	const marker = block.body.at(-1) as t.Statement | undefined;
	if (!t.isExpressionStatement(marker)) return null;
	if (!t.isCallExpression(marker.expression)) return null;
	const call = marker.expression;
	if (
		t.isV8IntrinsicIdentifier(call.callee, { name: 'UIntSwitchImm' })
	) {
		const [discriminant, min, max] = call.arguments;
		if (
			!t.isExpression(discriminant) ||
			!t.isNumericLiteral(min) ||
			!t.isNumericLiteral(max)
		) return null;
		const cases = numericSwitchCases(
			min.value,
			max.value,
			block.consequentAddresses,
		);
		if (!cases) return null;
		return {
			kind: 'switch',
			discriminant: t.cloneNode(discriminant, true),
			cases: cases.cases,
			defaultTarget: cases.defaultTarget,
		};
	}
	if (
		t.isV8IntrinsicIdentifier(call.callee, { name: 'StringSwitchImm' })
	) {
		const [discriminant, labels] = call.arguments;
		if (!t.isExpression(discriminant) || !t.isArrayExpression(labels)) {
			return null;
		}
		const cases = stringSwitchCases(labels, block.consequentAddresses);
		if (!cases) return null;
		return {
			kind: 'switch',
			discriminant: t.cloneNode(discriminant, true),
			cases: cases.cases,
			defaultTarget: cases.defaultTarget,
		};
	}
	return null;
}

function numericSwitchCases(
	min: number,
	max: number,
	successors: BlockAddr[],
): { cases: SwitchCaseEdge[]; defaultTarget: BlockAddr } | null {
	const caseCount = max - min + 1;
	if (!Number.isSafeInteger(caseCount) || caseCount <= 0) return null;
	if (successors.length < caseCount + 1) return null;
	const defaultTarget = successors[0];
	return {
		cases: Array.from({ length: caseCount }, (_, index) => ({
			test: t.numericLiteral(min + index),
			target: successors[index + 1],
		})).filter((edge) => edge.target !== defaultTarget),
		defaultTarget,
	};
}

function stringSwitchCases(
	labels: t.ArrayExpression,
	successors: BlockAddr[],
): { cases: SwitchCaseEdge[]; defaultTarget: BlockAddr } | null {
	if (successors.length < labels.elements.length + 1) return null;
	const defaultTarget = successors[0];
	const cases: SwitchCaseEdge[] = [];
	for (let i = 0; i < labels.elements.length; i++) {
		const label = labels.elements[i];
		if (!t.isStringLiteral(label)) return null;
		const target = successors[i + 1];
		if (target === defaultTarget) continue;
		cases.push({
			test: t.cloneNode(label, true),
			target,
		});
	}
	return {
		cases,
		defaultTarget,
	};
}
