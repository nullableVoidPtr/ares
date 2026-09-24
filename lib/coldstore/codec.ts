/**
 * The two values msgpackr cannot carry, and how they get to disk anyway.
 *
 * **`HermesEmpty`** is a `Symbol` (`lib/hbc/disassembly/instruction.ts`), which
 * the encoder refuses outright with `Unknown type: symbol`. It reaches records
 * as `LoadConstEmpty`'s lifted value.
 *
 * **Negative zero** is worse, because it fails silently: msgpackr encodes `-0`
 * as the integer `0`, and nothing complains. It is not a theoretical concern --
 * React's profiler initialises `actualDuration = -0`, Babel prints a
 * `NumericLiteral` holding `-0` as `-0`, and a byte-comparison of the composed
 * TestApp bundle turns up 452 lines that differ for exactly this reason.
 *
 * Both are replaced with tagged placeholders by a copy-on-write walk. The walk
 * returns its input unchanged when there is nothing to do, and records whether
 * it changed anything so the decode side can skip the walk entirely -- which is
 * the common case for every record in the store.
 */
import { HermesEmpty } from '../hbc/disassembly/instruction.ts';

const EMPTY_TAG = '__ares_hermes_empty__';
const NEGATIVE_ZERO_TAG = '__ares_negative_zero__';

/** A record plus whether decoding it needs a walk. */
export interface TaggedRecord<T> {
	value: T;
	/** True when the value contains a placeholder. */
	tagged: boolean;
}

function isTaggedObject(value: unknown, tag: string): boolean {
	return typeof value === 'object' && value !== null &&
		(value as Record<string, unknown>)[tag] === true;
}

/**
 * Replace unencodable values, copying only the path to each one.
 *
 * Structural sharing matters here: a snapshot body is the bulk of the store and
 * almost none of them contain either value, so an unconditional deep clone
 * would be the most expensive thing in the write path.
 */
export function encodeForStore<T>(value: T): TaggedRecord<T> {
	let tagged = false;

	const walk = (node: unknown): unknown => {
		if (typeof node === 'symbol') {
			if (node !== HermesEmpty) {
				throw new Error(
					`Cannot store the symbol ${String(node)}: only ` +
						'HermesEmpty has a stored form',
				);
			}
			tagged = true;
			return { [EMPTY_TAG]: true };
		}
		if (typeof node === 'number') {
			// `Object.is` rather than `===`, which cannot tell -0 from 0.
			if (Object.is(node, -0)) {
				tagged = true;
				return { [NEGATIVE_ZERO_TAG]: true };
			}
			return node;
		}
		if (node === null || typeof node !== 'object') return node;

		if (Array.isArray(node)) {
			let copy: unknown[] | undefined;
			for (let i = 0; i < node.length; i++) {
				const replaced = walk(node[i]);
				if (replaced !== node[i]) {
					copy ??= node.slice();
					copy[i] = replaced;
				}
			}
			return copy ?? node;
		}

		const source = node as Record<string, unknown>;
		let copy: Record<string, unknown> | undefined;
		for (const key of Object.keys(source)) {
			const replaced = walk(source[key]);
			if (replaced !== source[key]) {
				// Spread rather than assignment into a fresh object, so key
				// order survives -- the AST nodes in here are walked with
				// `Object.keys` downstream.
				copy ??= { ...source };
				copy[key] = replaced;
			}
		}
		return copy ?? node;
	};

	const encoded = walk(value) as T;
	return { value: encoded, tagged };
}

/** Undo `encodeForStore`. Only call it when the record was tagged. */
export function decodeFromStore<T>(value: T): T {
	const walk = (node: unknown): unknown => {
		if (node === null || typeof node !== 'object') return node;

		if (isTaggedObject(node, EMPTY_TAG)) return HermesEmpty;
		if (isTaggedObject(node, NEGATIVE_ZERO_TAG)) return -0;

		if (Array.isArray(node)) {
			let copy: unknown[] | undefined;
			for (let i = 0; i < node.length; i++) {
				const replaced = walk(node[i]);
				if (replaced !== node[i]) {
					copy ??= node.slice();
					copy[i] = replaced;
				}
			}
			return copy ?? node;
		}

		const source = node as Record<string, unknown>;
		let copy: Record<string, unknown> | undefined;
		for (const key of Object.keys(source)) {
			const replaced = walk(source[key]);
			if (replaced !== source[key]) {
				copy ??= { ...source };
				copy[key] = replaced;
			}
		}
		return copy ?? node;
	};

	return walk(value) as T;
}

/** Read back a record written as `{ value, tagged }`. */
export function unwrapStored<T>(
	stored: TaggedRecord<T> | undefined,
): T | undefined {
	if (!stored) return undefined;
	return stored.tagged ? decodeFromStore(stored.value) : stored.value;
}
