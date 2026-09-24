import * as t from '@babel/types';
import { comparableAst } from '../../../ast/utils.ts';
import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';

export interface TraceBlock {
	address: BlockAddr;
	body: readonly t.Statement[];
}

export function buildFailureTable<T>(
	pattern: readonly T[],
	equals: (left: T, right: T) => boolean,
): number[] {
	const table = new Array(pattern.length).fill(0);
	let prefix = 0;
	for (let cursor = 1; cursor < pattern.length; cursor++) {
		while (
			prefix > 0 &&
			!equals(pattern[cursor], pattern[prefix])
		) {
			prefix = table[prefix - 1];
		}
		if (equals(pattern[cursor], pattern[prefix])) prefix++;
		table[cursor] = prefix;
	}
	return table;
}

export function kmpSearch<T>(
	haystack: readonly T[],
	pattern: readonly T[],
	equals: (left: T, right: T) => boolean,
): number {
	if (pattern.length === 0) return 0;
	if (haystack.length < pattern.length) return -1;
	const table = buildFailureTable(pattern, equals);
	let matched = 0;
	for (let cursor = 0; cursor < haystack.length; cursor++) {
		while (
			matched > 0 &&
			!equals(haystack[cursor], pattern[matched])
		) {
			matched = table[matched - 1];
		}
		if (equals(haystack[cursor], pattern[matched])) matched++;
		if (matched === pattern.length) return cursor - pattern.length + 1;
	}
	return -1;
}

export function kmpPrefixMatchLength<T>(
	pattern: readonly T[],
	haystack: readonly T[],
	equals: (left: T, right: T) => boolean,
): number {
	if (pattern.length === 0 || haystack.length === 0) return 0;
	const table = buildFailureTable(pattern, equals);
	let matched = 0;
	let best = 0;
	for (const token of haystack) {
		while (
			matched > 0 &&
			!equals(token, pattern[matched])
		) {
			matched = table[matched - 1];
		}
		if (equals(token, pattern[matched])) matched++;
		if (matched > best) best = matched;
		if (matched === pattern.length) return matched;
	}
	return best;
}

export function statementFingerprint(statement: t.Statement): string {
	return JSON.stringify(comparableAst(statement));
}

export function traceFingerprints(blocks: readonly TraceBlock[]): string[] {
	return blocks.flatMap((block) => block.body.map(statementFingerprint));
}

export function tracePrefixLength(
	pattern: readonly TraceBlock[],
	haystack: readonly TraceBlock[],
): number {
	const patternFingerprints = traceFingerprints(pattern);
	if (patternFingerprints.length === 0) return 0;
	const haystackFingerprints = traceFingerprints(haystack);
	if (haystackFingerprints.length === 0) return 0;
	return kmpPrefixMatchLength(
		patternFingerprints,
		haystackFingerprints,
		(left, right) => left === right,
	);
}

export function traceMatchesPrefix(
	pattern: readonly TraceBlock[],
	haystack: readonly TraceBlock[],
): boolean {
	return tracePrefixLength(pattern, haystack) > 0;
}
