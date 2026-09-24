import * as t from '@babel/types';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import { containsDestructuringProtocol } from '../destructuringPlan.ts';

export interface DestructuringDescriptor {
	entry: BlockAddr;
	kind: 'array' | 'object';
	mode: 'binding' | 'assignment';
	pattern: t.ArrayPattern | t.ObjectPattern;
	source: t.Expression;
	sourceBlocks: AddressSet<BlockAddr>;
}

export interface DestructuringProtocolCandidate {
	entry: BlockAddr;
	kind: 'iterator' | 'object-rest';
	sourceBlocks: AddressSet<BlockAddr>;
	reason: 'semantic-pattern-not-yet-recovered';
}

export interface DestructuringDescriptorInfo {
	descriptors: DestructuringDescriptor[];
	descriptorByEntry: AddressMap<DestructuringDescriptor[]>;
	protocolCandidates: DestructuringProtocolCandidate[];
}

function semanticPatternDeclaration(
	stmt: t.Statement,
): DestructuringDescriptor | null {
	if (
		!t.isVariableDeclaration(stmt) || stmt.declarations.length !== 1
	) return null;
	const [declaration] = stmt.declarations;
	if (
		(!t.isArrayPattern(declaration.id) &&
			!t.isObjectPattern(declaration.id)) ||
		!declaration.init || !t.isExpression(declaration.init) ||
		containsDestructuringProtocol(declaration.init)
	) return null;
	return {
		entry: 0,
		kind: t.isArrayPattern(declaration.id) ? 'array' : 'object',
		mode: 'binding',
		pattern: t.cloneNode(declaration.id, true),
		source: t.cloneNode(declaration.init, true),
		sourceBlocks: new AddressSet(),
	};
}

function semanticPatternAssignment(
	stmt: t.Statement,
): DestructuringDescriptor | null {
	if (
		!t.isExpressionStatement(stmt) ||
		!t.isAssignmentExpression(stmt.expression, { operator: '=' }) ||
		(!t.isArrayPattern(stmt.expression.left) &&
			!t.isObjectPattern(stmt.expression.left)) ||
		!t.isExpression(stmt.expression.right) ||
		containsDestructuringProtocol(stmt.expression.right)
	) return null;
	return {
		entry: 0,
		kind: t.isArrayPattern(stmt.expression.left) ? 'array' : 'object',
		mode: 'assignment',
		pattern: t.cloneNode(stmt.expression.left, true),
		source: t.cloneNode(stmt.expression.right, true),
		sourceBlocks: new AddressSet(),
	};
}

function objectRestProtocol(node: t.Node): boolean {
	let found = false;
	t.traverseFast(node, (candidate) => {
		if (
			t.isCallExpression(candidate) &&
			t.isMemberExpression(candidate.callee, { computed: false }) &&
			t.isIdentifier(candidate.callee.object, {
				name: 'HermesInternal',
			}) &&
			t.isIdentifier(candidate.callee.property, {
				name: 'copyDataProperties',
			})
		) {
			found = true;
			return t.traverseFast.skip;
		}
	});
	return found;
}

function iteratorProtocol(node: t.Node): boolean {
	let found = false;
	t.traverseFast(node, (candidate) => {
		if (
			t.isCallExpression(candidate) &&
			t.isV8IntrinsicIdentifier(candidate.callee, {
				name: 'IteratorBegin',
			})
		) {
			found = true;
			return t.traverseFast.skip;
		}
	});
	return found;
}

/**
 * Index destructuring that is already semantic at the immutable-CFG boundary
 * and record compiler-protocol candidates that still require contraction.
 * The latter are deliberately diagnostics, not descriptors: Region emission
 * must never treat protocol temporaries as a source-level array pattern.
 */
export function recoverDestructuringDescriptors(
	cfg: ImmutableCFG,
): DestructuringDescriptorInfo {
	const descriptors: DestructuringDescriptor[] = [];
	const descriptorByEntry = new AddressMap<DestructuringDescriptor[]>();
	const protocolCandidates: DestructuringProtocolCandidate[] = [];
	for (const [address, block] of cfg.blocks) {
		for (const statement of block.body) {
			const descriptor = semanticPatternDeclaration(statement) ??
				semanticPatternAssignment(statement);
			if (descriptor) {
				descriptor.entry = address;
				descriptor.sourceBlocks.add(address);
				descriptors.push(descriptor);
				descriptorByEntry.getWithDefault(address, () => []).push(
					descriptor,
				);
			}
		}
		const program = t.program(
			block.body.map((statement) => t.cloneNode(statement, true)),
		);
		if (iteratorProtocol(program)) {
			protocolCandidates.push({
				entry: address,
				kind: 'iterator',
				sourceBlocks: new AddressSet([address]),
				reason: 'semantic-pattern-not-yet-recovered',
			});
		}
		if (objectRestProtocol(program)) {
			protocolCandidates.push({
				entry: address,
				kind: 'object-rest',
				sourceBlocks: new AddressSet([address]),
				reason: 'semantic-pattern-not-yet-recovered',
			});
		}
	}
	return { descriptors, descriptorByEntry, protocolCandidates };
}
