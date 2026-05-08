import { inspect, InspectOptionsStylized } from 'node:util';
import { BlockAddr } from '../hbc/disassembly/function.ts';

export class MapWithDefault<K, V> extends Map<K, V> {
	getWithDefault(key: K, factory: () => V) {
		if (this.has(key)) return this.get(key)!;

		const value = factory();
		this.set(key, value);

		return value;
	}
}

export class AddressMap<V = unknown, K extends BlockAddr = BlockAddr> extends MapWithDefault<K, V> {
	static mapEachBlock<B, R>(basicBlocks: Map<BlockAddr, B>, callback: () => R): AddressMap<R> {
		const map = new this<R>();
		for (const addr of basicBlocks.keys()) {
			map.set(addr, callback());
		}

		return map;
	}

	toDebugString(depth?: number, options?: InspectOptionsStylized, inspect?: (o: any, options: InspectOptionsStylized) => any) {
		const base = `AddressMap(${this.size})`;
		if (depth != null && depth < 0) {
			if (!options) throw new Error();
			return base;
		}

		if (this.size === 0) return `${base} {}`
		const valueStr = [...this.entries().map(([key, value]) => {
			let keyStr = key.toString(16);
			if (options) keyStr = options.stylize(keyStr, 'number');

			let valueStr;
			if (options && inspect) {
				const newOptions = {
					...options ?? {},
					depth: options?.depth != null ? options.depth - 1 : null,
				};
				valueStr = inspect(value, newOptions);
			} else {
				valueStr = value;
			}

			return `  ${keyStr} => ${valueStr},`
		})].join('\n');

		return `${base} {\n${valueStr}\n}`
	}

	[inspect.custom](depth: number, options: InspectOptionsStylized, inspect: (o: any, options: InspectOptionsStylized) => any) { return this.toDebugString(depth, options, inspect); }
}