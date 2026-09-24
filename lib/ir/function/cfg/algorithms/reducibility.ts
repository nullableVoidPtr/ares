import { AddressSet } from '../../../../utils/set.ts';
import type { DominatorInfo } from './dominators.ts';
import type { SCCInfo } from './tarjanSCC.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';

export interface ReducibilityInfo {
	isReducible: boolean;
	irreducibleSCCs: AddressSet[];
}

export function computeReducibility(
	cfg: ImmutableCFG,
	sccs: SCCInfo,
	dominators: DominatorInfo,
	normalReachable: AddressSet<BlockAddr>,
): ReducibilityInfo {
	const irreducibleSCCs: AddressSet[] = [];
	for (const component of sccs.components) {
		if ([...component].every((addr) => !normalReachable.has(addr))) {
			continue;
		}
		const hasCycle = component.size > 1 ||
			[...component].some((addr) =>
				cfg.normalSuccessors.get(addr)?.has(addr)
			);
		if (!hasCycle) continue;

		const entries = [...component].filter((addr) =>
			[...(cfg.normalPredecessors.get(addr) ?? [])].some((pred) =>
				normalReachable.has(pred) && !component.has(pred)
			)
		);
		if (entries.length <= 1) continue;
		const headers = entries.length > 0 ? entries : [...component];
		const reducible = headers.some((header) =>
			[...component].every((addr) => dominators.dominates(header, addr))
		);
		if (!reducible) irreducibleSCCs.push(component);
	}
	return {
		isReducible: irreducibleSCCs.length === 0,
		irreducibleSCCs,
	};
}
