import * as t from '@babel/types';
import type { BlockAddr } from '../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../utils/set.ts';
import type { IRFunction } from '../mod.ts';
import type { CFGDescriptors } from './descriptors/mod.ts';
import { statementFingerprint } from './descriptors/subgraphMatch.ts';
import { type CFGEdge, ImmutableCFG } from './immutableCFG.ts';
import { normalTerminatorSuccessors, type Terminator } from './terminator.ts';

export type CFGNormalizationInvariantKind =
	| 'missing-entry'
	| 'unreachable-block'
	| 'invalid-block-address'
	| 'missing-source-provenance'
	| 'missing-normal-successor'
	| 'normal-edge-asymmetry'
	| 'exceptional-edge-asymmetry'
	| 'invalid-phi-edge'
	| 'invalid-handler-ownership'
	| 'invalid-generator-metadata';

export interface CFGNormalizationInvariantIssue {
	kind: CFGNormalizationInvariantKind;
	message: string;
	address?: BlockAddr;
}

export interface CFGNormalizationPassSummary {
	name: 'prune-unreachable';
	changed: boolean;
	blocksBefore: number;
	blocksAfter: number;
	removedBlocks: BlockAddr[];
}

export interface CFGNormalizationSummary {
	enabled: boolean;
	changed: boolean;
	blocksBefore: number;
	blocksAfter: number;
	passes: CFGNormalizationPassSummary[];
	/** Graph rewrites across protected boundaries are not permitted in Phase 1. */
	protectedRegionPolicy: 'no-edge-rewrites';
	idempotent: boolean;
	fingerprintBefore: string;
	fingerprintAfter: string;
	invariantIssues: CFGNormalizationInvariantIssue[];
}

export interface CFGNormalizationResult {
	cfg: ImmutableCFG;
	summary: CFGNormalizationSummary;
}

export interface CFGNormalizationOptions {
	enabled?: boolean;
	validate?: boolean;
}

/**
 * Establish the canonical graph boundary consumed by Region descriptor
 * recovery. Phase 1 intentionally starts with the one universally safe graph
 * rewrite: discard blocks unreachable through normal or explicit exceptional
 * flow. No branch, loop, switch, try, or other structured AST is produced here.
 *
 * Edge splitting/merging is deliberately excluded until it can mechanically
 * update Phi actions and HandlerGraph ownership. This makes the protected-region
 * rule explicit instead of relying on individual reducer conventions.
 */
export function normalizeCFGForRegions(
	input: ImmutableCFG,
	options: CFGNormalizationOptions = {},
): CFGNormalizationResult {
	const enabled = options.enabled === true;
	// Both fingerprints and the idempotence re-run exist to describe the pass:
	// the audit reports them and `validate` proves them. Each one serialises
	// `comparableAst` of every statement in every block, and structuring runs
	// several times per function, so computing them unconditionally cost ~9% of
	// a plain decompile for a summary nothing read.
	const validate = options.validate !== false;
	const fingerprintBefore = validate ? cfgFingerprint(input) : '';
	if (!enabled) {
		return {
			cfg: input,
			summary: {
				enabled: false,
				changed: false,
				blocksBefore: input.blocks.size,
				blocksAfter: input.blocks.size,
				passes: [],
				protectedRegionPolicy: 'no-edge-rewrites',
				idempotent: true,
				fingerprintBefore,
				fingerprintAfter: fingerprintBefore,
				invariantIssues: [],
			},
		};
	}

	const first = pruneUnreachable(input);
	const cfg = first.cfg;
	const fingerprintAfter = validate ? cfgFingerprint(cfg) : '';
	const idempotent = !validate ||
		cfgFingerprint(pruneUnreachable(cfg).cfg) === fingerprintAfter;
	const invariantIssues = options.validate === false
		? []
		: validateNormalizedCFG(cfg);
	if (!idempotent) {
		invariantIssues.push({
			kind: 'invalid-block-address',
			message: 'Region CFG normalization is not idempotent',
		});
	}

	return {
		cfg,
		summary: {
			enabled: true,
			changed: first.summary.changed,
			blocksBefore: input.blocks.size,
			blocksAfter: cfg.blocks.size,
			passes: [first.summary],
			protectedRegionPolicy: 'no-edge-rewrites',
			idempotent,
			fingerprintBefore,
			fingerprintAfter,
			invariantIssues,
		},
	};
}

export function validateNormalizedCFG(
	cfg: ImmutableCFG,
): CFGNormalizationInvariantIssue[] {
	const issues: CFGNormalizationInvariantIssue[] = [];
	if (!cfg.blocks.has(cfg.entry)) {
		issues.push({
			kind: 'missing-entry',
			address: cfg.entry,
			message: `entry block 0x${cfg.entry.toString(16)} is missing`,
		});
		return issues;
	}

	const reachable = reachableBlocks(cfg);
	for (const [address, block] of cfg.blocks) {
		if (block.address !== address) {
			issues.push({
				kind: 'invalid-block-address',
				address,
				message:
					`block map key 0x${address.toString(16)} does not match ` +
					`payload address 0x${block.address.toString(16)}`,
			});
		}
		if (!reachable.has(address)) {
			issues.push({
				kind: 'unreachable-block',
				address,
				message: `block 0x${
					address.toString(16)
				} is unreachable after normalization`,
			});
		}
		if (block.sourceAddresses.size === 0) {
			issues.push({
				kind: 'missing-source-provenance',
				address,
				message: `block 0x${
					address.toString(16)
				} has no source addresses`,
			});
		}
		const expected = new AddressSet(
			normalTerminatorSuccessors(block.terminator),
		);
		for (const successor of expected) {
			if (!cfg.blocks.has(successor)) {
				issues.push({
					kind: 'missing-normal-successor',
					address,
					message:
						`block 0x${
							address.toString(16)
						} targets missing block ` +
						`0x${successor.toString(16)}`,
				});
				continue;
			}
			if (
				!cfg.normalSuccessors.get(address)?.has(successor) ||
				!cfg.normalPredecessors.get(successor)?.has(address)
			) {
				issues.push(edgeAsymmetry('normal', address, successor));
			}
		}
		for (const successor of cfg.normalSuccessors.get(address) ?? []) {
			if (!expected.has(successor)) {
				issues.push(edgeAsymmetry('normal', address, successor));
			}
		}
	}

	for (const edge of cfg.exceptionalEdges()) {
		if (
			!cfg.blocks.has(edge.from) || !cfg.blocks.has(edge.to) ||
			!cfg.exceptionalPredecessors.get(edge.to)?.has(edge.from)
		) {
			issues.push(edgeAsymmetry('exceptional', edge.from, edge.to));
		}
	}
	for (const [target, predecessors] of cfg.exceptionalPredecessors) {
		for (const predecessor of predecessors) {
			if (!cfg.exceptionalSuccessors.get(predecessor)?.has(target)) {
				issues.push(edgeAsymmetry('exceptional', predecessor, target));
			}
		}
	}
	return issues;
}

export function validateRegionDescriptorInvariants(
	cfg: ImmutableCFG,
	descriptors: CFGDescriptors,
): CFGNormalizationInvariantIssue[] {
	const issues: CFGNormalizationInvariantIssue[] = [];
	for (const phi of descriptors.phis.phis) {
		if (!cfg.blocks.has(phi.block)) {
			issues.push({
				kind: 'invalid-phi-edge',
				address: phi.block,
				message: `Phi target block 0x${
					phi.block.toString(16)
				} is missing`,
			});
			continue;
		}
		for (const assignment of phi.incoming.values()) {
			if (
				assignment.edge.to !== phi.block ||
				!cfg.normalSuccessors.get(assignment.edge.from)?.has(phi.block)
			) {
				issues.push({
					kind: 'invalid-phi-edge',
					address: phi.block,
					message:
						`Phi edge 0x${assignment.edge.from.toString(16)} -> ` +
						`0x${
							phi.block.toString(16)
						} is absent from the normalized CFG`,
				});
			}
		}
	}

	for (const descriptor of descriptors.exceptions.handlers) {
		if (!cfg.blocks.has(descriptor.handler)) {
			issues.push({
				kind: 'invalid-handler-ownership',
				address: descriptor.handler,
				message: `handler 0x${
					descriptor.handler.toString(16)
				} is missing`,
			});
			continue;
		}
		for (const protectedBlock of descriptor.protectedBlocks) {
			// A descriptor names the addresses the disassembler protected. Ordinary
			// reduction absorbs blocks into structured AST or merges them, so a
			// protected block that no longer exists is not an ownership failure;
			// one that does exist must still carry its explicit handler edge.
			if (!cfg.blocks.has(protectedBlock)) continue;
			if (
				!cfg.exceptionalSuccessors.get(protectedBlock)?.has(
					descriptor.handler,
				)
			) {
				issues.push({
					kind: 'invalid-handler-ownership',
					address: descriptor.handler,
					message:
						`handler 0x${
							descriptor.handler.toString(16)
						} does not own ` +
						`an explicit edge from 0x${
							protectedBlock.toString(16)
						}`,
				});
			}
		}
	}
	return issues;
}

export function validateRegionFunctionMetadata(
	cfg: ImmutableCFG,
	func: IRFunction,
): CFGNormalizationInvariantIssue[] {
	if (!func.isGenerator) return [];
	const issues: CFGNormalizationInvariantIssue[] = [];
	// Generator metadata names the addresses the disassembler produced. Ordinary
	// reduction merges blocks and keeps their provenance in `sourceAddresses`, so
	// a metadata address is still represented when some block was built from it.
	const represented = new AddressSet<BlockAddr>();
	for (const [address, block] of cfg.blocks) {
		represented.add(address);
		for (const source of block.sourceAddresses) represented.add(source);
	}
	const check = (address: BlockAddr, role: string) => {
		if (represented.has(address)) return;
		issues.push({
			kind: 'invalid-generator-metadata',
			address,
			message:
				`${role} block 0x${address.toString(16)} is absent from the ` +
				'normalized generator CFG',
		});
	};
	// Generator reconstruction replaces the suspension machinery with high-level
	// syntax and drops the blocks it stood for, so metadata whose own block is
	// gone describes a machine that no longer exists. What must still resolve is
	// every block a *live* suspension names.
	for (const [address, end] of func.yieldEndBlocks) {
		if (!represented.has(address)) continue;
		check(end.continuation, 'yield continuation');
		check(end.return, 'yield return');
	}
	return issues;
}

export function cfgFingerprint(cfg: ImmutableCFG): string {
	const serialized = JSON.stringify({
		entry: cfg.entry,
		blocks: [...cfg.blocks].toSorted(([left], [right]) => left - right).map(
			([address, block]) => ({
				address,
				body: block.body.map(statementFingerprint),
				terminator: terminatorFingerprint(block.terminator),
				sources: [...block.sourceAddresses].toSorted((left, right) =>
					left - right
				),
			}),
		),
		exceptionalEdges: cfg.exceptionalEdges().map(edgeFingerprint)
			.toSorted(),
	});
	return stableHash(serialized);
}

function pruneUnreachable(cfg: ImmutableCFG): {
	cfg: ImmutableCFG;
	summary: CFGNormalizationPassSummary;
} {
	const reachable = reachableBlocks(cfg);
	const removedBlocks = [...cfg.blocks.keys()].filter((address) =>
		!reachable.has(address)
	).toSorted((left, right) => left - right);
	const normalized = removedBlocks.length === 0
		? cfg
		: cfg.restrictTo(reachable);
	return {
		cfg: normalized,
		summary: {
			name: 'prune-unreachable',
			changed: removedBlocks.length > 0,
			blocksBefore: cfg.blocks.size,
			blocksAfter: normalized.blocks.size,
			removedBlocks,
		},
	};
}

function reachableBlocks(cfg: ImmutableCFG): AddressSet<BlockAddr> {
	const reachable = new AddressSet<BlockAddr>();
	const pending = [cfg.entry];
	while (pending.length > 0) {
		const address = pending.pop()!;
		if (reachable.has(address) || !cfg.blocks.has(address)) continue;
		reachable.add(address);
		const successors = new AddressSet([
			...(cfg.normalSuccessors.get(address) ?? []),
			...(cfg.exceptionalSuccessors.get(address) ?? []),
		]);
		for (
			const successor of [...successors].toSorted((left, right) =>
				right - left
			)
		) {
			if (!reachable.has(successor)) pending.push(successor);
		}
	}
	return reachable;
}

function edgeAsymmetry(
	kind: CFGEdge['kind'],
	from: BlockAddr,
	to: BlockAddr,
): CFGNormalizationInvariantIssue {
	return {
		kind: kind === 'normal'
			? 'normal-edge-asymmetry'
			: 'exceptional-edge-asymmetry',
		address: from,
		message:
			`${kind} edge 0x${from.toString(16)} -> 0x${to.toString(16)} ` +
			'is not symmetric',
	};
}

function edgeFingerprint(edge: CFGEdge): string {
	return `${edge.kind}:${edge.from}->${edge.to}`;
}

function terminatorFingerprint(terminator: Terminator): unknown {
	switch (terminator.kind) {
		case 'goto':
			return { kind: terminator.kind, target: terminator.target };
		case 'if':
			return {
				kind: terminator.kind,
				test: expressionFingerprint(terminator.test),
				fallthrough: terminator.fallthrough,
				taken: terminator.taken,
			};
		case 'switch':
			return {
				kind: terminator.kind,
				discriminant: expressionFingerprint(terminator.discriminant),
				cases: terminator.cases.map((edge) => ({
					test: edge.test == null
						? null
						: expressionFingerprint(edge.test),
					target: edge.target,
				})),
				defaultTarget: terminator.defaultTarget,
			};
		case 'return':
			return {
				kind: terminator.kind,
				argument: terminator.argument == null
					? null
					: expressionFingerprint(terminator.argument),
			};
		case 'throw':
			return {
				kind: terminator.kind,
				argument: terminator.argument == null
					? null
					: expressionFingerprint(terminator.argument),
			};
		case 'unreachable':
			return { kind: terminator.kind };
	}
}

function expressionFingerprint(expression: t.Expression): string {
	return statementFingerprint(t.expressionStatement(expression));
}

function stableHash(value: string): string {
	let left = 0x811c9dc5;
	let right = 0x9e3779b9;
	for (let index = 0; index < value.length; index++) {
		const code = value.charCodeAt(index);
		left = Math.imul(left ^ code, 0x01000193);
		right = Math.imul(right ^ code, 0x85ebca6b);
	}
	return `${(left >>> 0).toString(16).padStart(8, '0')}` +
		`${(right >>> 0).toString(16).padStart(8, '0')}`;
}
