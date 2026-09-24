import type * as t from '@babel/types';
import type { BlockAddr } from '../../../hbc/disassembly/function.ts';

export interface SwitchCaseEdge {
	test: t.Expression | null;
	target: BlockAddr;
}

export type Terminator =
	| { kind: 'goto'; target: BlockAddr }
	| {
		kind: 'if';
		test: t.Expression;
		/** Successor reached when the lifted jump predicate is false. */
		fallthrough: BlockAddr;
		/** Successor reached when the lifted jump predicate is true. */
		taken: BlockAddr;
	}
	| {
		kind: 'switch';
		discriminant: t.Expression;
		cases: SwitchCaseEdge[];
		defaultTarget: BlockAddr;
	}
	| { kind: 'return'; argument?: t.Expression | null }
	| { kind: 'throw'; argument?: t.Expression }
	| { kind: 'unreachable' };

export function normalTerminatorSuccessors(
	terminator: Terminator,
): BlockAddr[] {
	switch (terminator.kind) {
		case 'goto':
			return [terminator.target];
		case 'if':
			return [terminator.fallthrough, terminator.taken];
		case 'switch':
			return [
				...terminator.cases.map((edge) => edge.target),
				terminator.defaultTarget,
			];
		case 'return':
		case 'throw':
		case 'unreachable':
			return [];
	}
}
