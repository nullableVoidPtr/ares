import { inspect, InspectOptionsStylized } from 'node:util';
import { BlockAddr } from '../hbc/disassembly/function.ts';

export function setEquals<U, L extends Set<U>, R extends Set<U>>(
	a: L,
	b: R,
): boolean {
	if (a.size !== b.size) return false;
	for (const x of a) if (!b.has(x)) return false;
	return true;
}

export class AddressSet<U = BlockAddr> extends Set<U> {
	override difference<V>(other: ReadonlySetLike<V>): AddressSet<U> {
		return new AddressSet(super.difference(other));
	}

	override union<V>(other: ReadonlySetLike<V>): AddressSet<U | V> {
		return new AddressSet(super.union(other));
	}

	override intersection<V>(other: ReadonlySetLike<V>): AddressSet<U & V> {
		return new AddressSet(super.intersection(other));
	}

	equals<T extends Set<U> | AddressSet<U>>(other: T) {
		if (this.size !== other.size) return false;
		for (const x of this) if (!other.has(x)) return false;
		return true;
	}

	/* deno-coverage-ignore */
	toDebugString(depth?: number, options?: InspectOptionsStylized) {
		const base = `AddressSet(${this.size})`;
		if (depth != null && depth < 0) {
			if (!options) throw new Error();
			return base;
		}

		if (this.size === 0) return `${base} {}`;
		const valueStr = '{ ' + [...this.values()].toSorted().map((a) => {
			const value = Number(a).toString(16);
			return options ? options.stylize(value, 'number') : value;
		}).join(' ') + ' }';

		return `${base} ${valueStr}`;
	}

	[inspect.custom]() {
		return this.toDebugString(...arguments);
	}
}
