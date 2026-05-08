import { inspect, InspectOptionsStylized } from 'node:util';
import { BlockAddr } from '../hbc/disassembly/function.ts';

export function setEquals<U, L extends Set<U>, R extends Set<U>>(a: L, b: R): boolean {
	if (a.size !== b.size) return false;
	for (const x of a) if (!b.has(x)) return false;
	return true;
}

export class AddressSet<U extends BlockAddr = BlockAddr> extends Set<U> {
    override difference(other: ReadonlySetLike<U>): AddressSet<U> {
        return new AddressSet(super.difference(other));
    }

	override union(other: ReadonlySetLike<U>): AddressSet<U> {
		return new AddressSet(super.union(other));
	}

	override intersection(other: ReadonlySetLike<U>): AddressSet<U> {
		return new AddressSet(super.intersection(other));
	}

	equals<T extends Set<U> | AddressSet<U>>(other: T) {
		if (this.size !== other.size) return false;
		for (const x of this) if (!other.has(x)) return false;
		return true;
	}

	toDebugString(depth?: number, options?: InspectOptionsStylized) {
		const base = `AddressSet(${this.size})`;
		if (depth != null && depth < 0) {
			if (!options) throw new Error();
			return base;
		}

		if (this.size === 0) return `${base} {}`
		const valueStr = "{ " + [...this.values()].toSorted().map(a => options ? options.stylize(a.toString(16), 'number') : a.toString(16)).join(" ") + " }";

		return `${base} ${valueStr}`
	}

	[inspect.custom]() { return this.toDebugString(...arguments); }
}