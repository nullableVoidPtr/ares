import { BlockAddr } from '../disassembly/function.ts';
import { AddressMap } from './map.ts';
import { AddressSet } from './set.ts';

export class AddressGraph<K extends BlockAddr = BlockAddr, V extends BlockAddr = BlockAddr> extends AddressMap<AddressSet<V>, K> {
	static fromBasicBlocks<K extends BlockAddr, V extends BlockAddr>(basicBlocks: Map<K, unknown>) {
		const map = new AddressGraph<K, V>();
		for (const addr of basicBlocks.keys()) {
			map.set(addr, new AddressSet());
		}

		return map;
	}

	addEdge(source: K, destination: V) {
		this.getWithDefault(source, () => new AddressSet()).add(destination);
	}

	removeEdge(source: K, destination: V) {
		this.getWithDefault(source, () => new AddressSet()).delete(destination);
	}
}