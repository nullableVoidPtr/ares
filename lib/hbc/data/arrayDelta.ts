export type ArrayDelta<T> = {
	exclude?: T[];
	prepend?: T[];
	append?: T[];
	insertAfter?: [T, T[]][];
} | T[];

export type ArrayElementEquals<T> = (left: T, right: T) => boolean;

/** Apply one version delta without mutating either the base or the delta. */
export function applyArrayDelta<T>(
	base: T[] | undefined,
	delta: ArrayDelta<T> | undefined,
	equals: ArrayElementEquals<T> = Object.is,
): T[] | undefined {
	if (delta == null) return base;
	if (Array.isArray(delta)) return delta.slice();
	if (base == null) return undefined;

	let result = base.slice();
	if (delta.exclude) {
		result = result.filter((item) =>
			!delta.exclude!.some((excluded) => equals(item, excluded))
		);
	}
	if (delta.prepend) result.unshift(...delta.prepend);
	if (delta.append) result.push(...delta.append);
	for (const [after, values] of delta.insertAfter ?? []) {
		const index = result.findIndex((item) => equals(item, after));
		if (index !== -1) result.splice(index + 1, 0, ...values);
	}
	return result;
}
