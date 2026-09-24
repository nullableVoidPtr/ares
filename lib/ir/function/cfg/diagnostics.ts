import type { BlockAddr } from '../../../hbc/disassembly/function.ts';
import type { AddressSet } from '../../../utils/set.ts';
import type { CFGEdge } from './immutableCFG.ts';

export type StructuringDiagnosticKind =
	| 'unstructuredRegion'
	| 'irreducibleSCC'
	| 'missingPostdominatorJoin'
	| 'invalidSESE'
	| 'invalidWeakSESE'
	| 'invalidLoopHeader'
	| 'unplacedPhi'
	| 'liveOutConflict'
	| 'unmatchedFinalizer'
	| 'ambiguousSwitch'
	| 'exceptionRegionConflict'
	| 'invalidNormalization'
	| 'invalidTerminator'
	| 'unreachableBlock';

export interface StructuringDiagnostic {
	kind: StructuringDiagnosticKind;
	entry: BlockAddr;
	allowed?: AddressSet<BlockAddr>;
	relevantEdges?: CFGEdge[];
	relevantSCC?: AddressSet<BlockAddr>;
	seseCandidate?: {
		entry: BlockAddr;
		exit?: BlockAddr;
		body: AddressSet<BlockAddr>;
	};
	idom?: BlockAddr | null;
	ipdom?: BlockAddr | null;
	message: string;
}

export class StructuringDiagnostics {
	readonly items: StructuringDiagnostic[] = [];

	add(diagnostic: StructuringDiagnostic) {
		this.items.push(diagnostic);
	}

	get hasErrors() {
		return this.items.length > 0;
	}
}
