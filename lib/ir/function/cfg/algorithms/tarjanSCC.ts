import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressGraph } from '../../../../utils/graph.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';
import type { ImmutableCFG } from '../immutableCFG.ts';

export interface SCCInfo {
	components: AddressSet<BlockAddr>[];
	componentOf: AddressMap<number>;
	componentGraph: AddressGraph<number, number>;
}

export function computeSCCs(cfg: ImmutableCFG): SCCInfo {
	let index = 0;
	const stack: BlockAddr[] = [];
	const onStack = new AddressSet<BlockAddr>();
	const indexes = new AddressMap<number>();
	const lowlinks = new AddressMap<number>();
	const components: AddressSet<BlockAddr>[] = [];
	const componentOf = new AddressMap<number>();

	const strongConnect = (addr: BlockAddr) => {
		indexes.set(addr, index);
		lowlinks.set(addr, index);
		index++;
		stack.push(addr);
		onStack.add(addr);

		for (const succ of cfg.normalSuccessors.get(addr) ?? []) {
			if (!indexes.has(succ)) {
				strongConnect(succ);
				lowlinks.set(
					addr,
					Math.min(lowlinks.get(addr)!, lowlinks.get(succ)!),
				);
			} else if (onStack.has(succ)) {
				lowlinks.set(
					addr,
					Math.min(lowlinks.get(addr)!, indexes.get(succ)!),
				);
			}
		}

		if (lowlinks.get(addr) !== indexes.get(addr)) return;
		const component = new AddressSet<BlockAddr>();
		while (true) {
			const member = stack.pop()!;
			onStack.delete(member);
			component.add(member);
			componentOf.set(member, components.length);
			if (member === addr) break;
		}
		components.push(component);
	};

	for (const addr of cfg.blocks.keys()) {
		if (!indexes.has(addr)) strongConnect(addr);
	}

	const componentGraph = new AddressGraph<number, number>();
	for (let i = 0; i < components.length; i++) {
		componentGraph.set(i, new AddressSet<number>());
	}
	for (const [from, successors] of cfg.normalSuccessors) {
		const fromComponent = componentOf.get(from);
		if (fromComponent == null) continue;
		for (const to of successors) {
			const toComponent = componentOf.get(to);
			if (toComponent == null || toComponent === fromComponent) {
				continue;
			}
			componentGraph.addEdge(fromComponent, toComponent);
		}
	}

	return { components, componentOf, componentGraph };
}
