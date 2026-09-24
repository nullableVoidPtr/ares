import * as t from '@babel/types';
import { rewriteStructuredStatementLists } from '../ast/statementLists.ts';
import { comparableAst } from '../ast/utils.ts';

function comparableFinalizerAst(value: unknown, key?: string): unknown {
	// A BigIntLiteral carries a native bigint, which JSON.stringify refuses.
	if (typeof value === 'bigint') return value.toString();
	if (Array.isArray(value)) {
		return value.map((entry) => comparableFinalizerAst(entry));
	}
	if (value && typeof value === 'object') {
		if (t.isCallExpression(value as t.Node)) {
			const call = value as t.CallExpression;
			const normalized = normalizeCallReceiverShape(call);
			if (normalized) return normalized;
		}
		const base = comparableAst(value, key);
		if (Array.isArray(base)) {
			return base.map((entry) => comparableFinalizerAst(entry));
		}
		if (base && typeof base === 'object') {
			const result: Record<string, unknown> = {};
			for (const [childKey, childValue] of Object.entries(base)) {
				result[childKey] = comparableFinalizerAst(
					childValue,
					childKey,
				);
			}
			return result;
		}
		return base;
	}
	return comparableAst(value, key);
}

function normalizeCallReceiverShape(call: t.CallExpression): unknown {
	if (
		!t.isMemberExpression(call.callee, { computed: false }) ||
		!t.isIdentifier(call.callee.property, { name: 'call' })
	) return null;
	const target = call.callee.object;
	const [receiver, ...args] = call.arguments;
	if (!t.isExpression(receiver)) return null;
	if (
		t.isIdentifier(target) &&
		(
			isUndefinedLikeReceiver(receiver) ||
			(t.isIdentifier(receiver) && /^r\d+_\d+$/.test(receiver.name))
		)
	) {
		return {
			type: 'CallExpression',
			callee: comparableFinalizerAst(target),
			arguments: args.map((arg) => comparableFinalizerAst(arg)),
		};
	}
	if (!t.isMemberExpression(target)) return null;
	if (
		JSON.stringify(comparableAst(receiver)) !==
			JSON.stringify(comparableAst(target.object))
	) return null;
	return {
		type: 'CallExpression',
		callee: comparableFinalizerAst(target),
		arguments: args.map((arg) => comparableFinalizerAst(arg)),
	};
}

function isUndefinedLikeReceiver(node: t.Expression): boolean {
	return t.isIdentifier(node, { name: 'undefined' }) ||
		(t.isUnaryExpression(node, { operator: 'void' }) &&
			t.isNumericLiteral(node.argument, { value: 0 }));
}

function statementsEqual(left: t.Statement, right: t.Statement) {
	return JSON.stringify(comparableFinalizerAst(left)) ===
		JSON.stringify(comparableFinalizerAst(right));
}

function normalizeCopiedFinalizerStatement(statement: t.Statement) {
	return t.cloneNode(statement, true);
}

export function statementMatchesFinalizerPrefix(
	copy: t.Statement,
	finalizer: t.Statement,
): boolean {
	if (statementsEqual(copy, finalizer)) return true;
	if (
		statementsEqual(
			normalizeCopiedFinalizerStatement(copy),
			normalizeCopiedFinalizerStatement(finalizer),
		)
	) return true;

	if (t.isTryStatement(copy) && t.isTryStatement(finalizer)) {
		if (
			!statementListMatchesFinalizerPrefix(
				copy.block.body,
				finalizer.block.body,
			)
		) return false;

		if (!!copy.handler !== !!finalizer.handler) return false;
		if (copy.handler && finalizer.handler) {
			if (
				!statementListMatchesFinalizerPrefix(
					copy.handler.body.body,
					finalizer.handler.body.body,
				)
			) return false;
		}

		if (!!copy.finalizer !== !!finalizer.finalizer) return false;
		if (copy.finalizer && finalizer.finalizer) {
			return statementListMatchesFinalizerPrefix(
				copy.finalizer.body,
				finalizer.finalizer.body,
			);
		}

		return true;
	}

	return false;
}

export function statementListMatchesFinalizerPrefix(
	copy: t.Statement[],
	finalizer: t.Statement[],
) {
	if (copy.length > finalizer.length) return false;

	for (let i = 0; i < copy.length; i++) {
		if (!statementMatchesFinalizerPrefix(copy[i], finalizer[i])) {
			return false;
		}
	}

	return true;
}

function statementListsEqualAsFinalizer(
	left: t.Statement[],
	right: t.Statement[],
) {
	return left.length === right.length &&
		statementListMatchesFinalizerPrefix(left, right);
}

/**
 * Strip the rethrowing copy Hermes can place immediately after a try/finally
 * which already owns the same nested finalizer. The copied form wraps the
 * try/catch inside another try/finally only to carry a pending exception; on
 * normal fallthrough it would otherwise execute the finalizer twice.
 */
export function stripAdjacentRethrowFinalizerCopies(
	body: t.Statement[],
): boolean {
	return rewriteStructuredStatementLists(
		body,
		stripAdjacentRethrowFinalizerCopiesInList,
	);
}

/** HandlerGraph-owned variant of the adjacent rethrow projection. */
export function stripOwnedAdjacentRethrowFinalizerCopies(
	body: t.Statement[],
	ownedCopyCount: number,
): boolean {
	if (ownedCopyCount === 0) return false;
	return rewriteStructuredStatementLists(
		body,
		stripAdjacentRethrowFinalizerCopiesInList,
	);
}

function stripAdjacentRethrowFinalizerCopiesInList(
	body: t.Statement[],
): boolean {
	let changed = false;
	for (let i = 0; i < body.length - 1; i++) {
		const owner = body[i];
		const copy = body[i + 1];
		if (
			!t.isTryStatement(owner) || !owner.finalizer ||
			owner.finalizer.body.length !== 1 ||
			!t.isTryStatement(copy) || copy.handler || !copy.finalizer ||
			copy.block.body.length !== 1
		) continue;
		const canonical = owner.finalizer.body[0];
		const rethrowing = copy.block.body[0];
		if (
			!t.isTryStatement(canonical) ||
			!t.isTryStatement(rethrowing) ||
			canonical.finalizer == null || rethrowing.finalizer != null ||
			!!canonical.handler !== !!rethrowing.handler
		) continue;
		const rethrow = rethrowing.block.body.at(-1);
		if (!rethrow || !t.isThrowStatement(rethrow)) continue;
		if (
			!statementListsEqualAsFinalizer(
				canonical.block.body,
				rethrowing.block.body.slice(0, -1),
			) ||
			!statementListsEqualAsFinalizer(
				canonical.finalizer.body,
				copy.finalizer.body,
			) ||
			(canonical.handler && rethrowing.handler &&
				!statementListsEqualAsFinalizer(
					canonical.handler.body.body,
					rethrowing.handler.body.body,
				))
		) continue;
		body.splice(i + 1, 1);
		changed = true;
	}
	return changed;
}

function finalizerFeatureSet(node: t.Node): Set<string> {
	const features = new Set<string>();
	t.traverseFast(node, (child) => {
		if (t.isStringLiteral(child)) {
			features.add(`string:${child.value}`);
		} else if (
			t.isIdentifier(child) && child.name !== 'undefined' &&
			!/^(?:r\d+_\d+|e_\d+|_e)$/.test(child.name)
		) {
			features.add(`identifier:${child.name}`);
		}
	});
	return features;
}

function setsEqual<T>(left: Set<T>, right: Set<T>) {
	return left.size === right.size &&
		[...left].every((value) => right.has(value));
}

/**
 * Remove a terminal control-flow copy of an enclosing finally from the end of
 * its own try body. Split Hermes finalizers can duplicate the same effects in
 * several catch/return paths, so compare feature sets rather than multiplicity;
 * both sides must be abrupt, non-empty try-shaped regions.
 */
export function stripTerminalEnclosingFinalizerCopies(
	body: t.Statement[],
): boolean {
	return rewriteStructuredStatementLists(
		body,
		stripTerminalEnclosingFinalizerCopiesInList,
	);
}

/**
 * Project a HandlerGraph-proven enclosing-finalizer copy out of structured
 * output. Unlike the legacy cleanup above, callers must provide ownership
 * evidence recovered from bytecode edges before this AST shape is considered.
 */
export function stripOwnedTerminalEnclosingFinalizerCopies(
	body: t.Statement[],
	ownedCopyCount: number,
): boolean {
	if (ownedCopyCount === 0) return false;
	return rewriteStructuredStatementLists(
		body,
		stripTerminalEnclosingFinalizerCopiesInList,
	);
}

function stripTerminalEnclosingFinalizerCopiesInList(
	body: t.Statement[],
): boolean {
	let changed = false;
	for (const statement of body) {
		if (t.isTryStatement(statement)) {
			const copy = statement.block.body.at(-1);
			if (
				!statement.finalizer || !copy || !t.isTryStatement(copy) ||
				!statementAlwaysTerminates(copy) ||
				!statementAlwaysTerminates(statement.finalizer)
			) continue;
			const canonicalFeatures = finalizerFeatureSet(statement.finalizer);
			if (canonicalFeatures.size === 0) continue;
			if (!setsEqual(canonicalFeatures, finalizerFeatureSet(copy))) {
				continue;
			}
			statement.block.body.pop();
			changed = true;
		}
	}
	return changed;
}

function containsEscapingBreak(
	node: t.Node,
	nestedBreakable = false,
): boolean {
	if (t.isFunction(node)) return false;
	if (t.isBreakStatement(node)) {
		return node.label != null || !nestedBreakable;
	}
	const childIsBreakable = nestedBreakable ||
		t.isLoop(node) ||
		t.isSwitchStatement(node);
	for (const key of t.VISITOR_KEYS[node.type] ?? []) {
		const value = (node as unknown as Record<string, unknown>)[key];
		if (Array.isArray(value)) {
			for (const child of value) {
				if (
					t.isNode(child) &&
					containsEscapingBreak(child, childIsBreakable)
				) return true;
			}
		} else if (
			t.isNode(value) &&
			containsEscapingBreak(value, childIsBreakable)
		) return true;
	}
	return false;
}

function switchAlwaysTerminates(statement: t.SwitchStatement): boolean {
	if (!statement.cases.some((switchCase) => switchCase.test == null)) {
		return false;
	}
	for (let entry = 0; entry < statement.cases.length; entry++) {
		let terminates = false;
		for (
			let caseIndex = entry;
			caseIndex < statement.cases.length && !terminates;
			caseIndex++
		) {
			for (const consequent of statement.cases[caseIndex].consequent) {
				if (containsEscapingBreak(consequent)) return false;
				if (!statementAlwaysTerminates(consequent)) continue;
				terminates = true;
				break;
			}
		}
		if (!terminates) return false;
	}
	return true;
}

export function statementAlwaysTerminates(statement: t.Statement): boolean {
	if (t.isReturnStatement(statement) || t.isThrowStatement(statement)) {
		return true;
	}

	if (t.isBlockStatement(statement)) {
		const last = statement.body.at(-1);
		return !!last && statementAlwaysTerminates(last);
	}

	if (t.isIfStatement(statement)) {
		return !!statement.alternate &&
			statementAlwaysTerminates(statement.consequent) &&
			statementAlwaysTerminates(statement.alternate);
	}

	if (t.isTryStatement(statement)) {
		if (
			statement.finalizer &&
			statementAlwaysTerminates(statement.finalizer)
		) return true;
		const tryTerminates = statementAlwaysTerminates(statement.block);
		if (!statement.handler) return tryTerminates;
		const catchTerminates = statement.handler != null &&
			statementAlwaysTerminates(statement.handler.body);
		return tryTerminates && catchTerminates;
	}

	if (t.isSwitchStatement(statement)) {
		return switchAlwaysTerminates(statement);
	}

	if (
		(t.isWhileStatement(statement) &&
			t.isBooleanLiteral(statement.test, { value: true })) ||
		(t.isDoWhileStatement(statement) &&
			t.isBooleanLiteral(statement.test, { value: true })) ||
		(t.isForStatement(statement) && statement.test == null)
	) {
		return !containsEscapingBreak(statement.body);
	}

	return false;
}

export function stripStatementSuffix(
	body: t.Statement[],
	suffix: t.Statement[],
	preserveAbruptCompletion = false,
) {
	if (suffix.length === 0 || body.length < suffix.length) return false;

	const offset = body.length - suffix.length;
	for (let i = 0; i < suffix.length; i++) {
		if (!statementMatchesFinalizerPrefix(body[offset + i], suffix[i])) {
			return false;
		}
	}

	if (
		preserveAbruptCompletion &&
		statementAlwaysTerminates(t.blockStatement(suffix))
	) {
		body.splice(offset, body.length - offset, t.returnStatement());
	} else {
		body.splice(offset);
	}
	return true;
}

export function stripStatementBeforeTerminal(
	body: t.Statement[],
	suffix: t.Statement[],
) {
	if (suffix.length === 0 || body.length < suffix.length + 1) return false;

	const terminal = body.at(-1);
	// TODO: Expand terminal statement handling once loops are implemented. A
	// terminal enclosing loop can also make the preceding finalizer copy dead.
	if (!terminal || !statementAlwaysTerminates(terminal)) return false;

	const offset = body.length - suffix.length - 1;
	for (let i = 0; i < suffix.length; i++) {
		if (!statementMatchesFinalizerPrefix(body[offset + i], suffix[i])) {
			return false;
		}
	}

	body.splice(offset, suffix.length);
	return true;
}

export function stripStatementBeforeTerminalTail(
	body: t.Statement[],
	suffix: t.Statement[],
	preserveAbruptCompletion = false,
) {
	if (suffix.length === 0 || body.length < suffix.length + 1) return false;

	for (let offset = 0; offset <= body.length - suffix.length - 1; offset++) {
		let matches = true;
		for (let i = 0; i < suffix.length; i++) {
			if (!statementMatchesFinalizerPrefix(body[offset + i], suffix[i])) {
				matches = false;
				break;
			}
		}
		if (!matches) continue;

		const tail = body.slice(offset + suffix.length);
		if (tail.length === 0) continue;
		const last = tail.at(-1);
		if (!last || !statementAlwaysTerminates(last)) continue;

		if (preserveAbruptCompletion) {
			body.splice(offset, body.length - offset, t.returnStatement());
		} else {
			body.splice(offset, suffix.length);
		}
		return true;
	}

	return false;
}

export function stripLeadingFinalizerCopyBeforeTerminalTail(
	body: t.Statement[],
	finalizer: t.Statement[],
	preserveAbruptCompletion = false,
) {
	if (finalizer.length < 2 || body.length < 3) return false;

	for (let offset = 0; offset < body.length - 1; offset++) {
		const maxLength = Math.min(finalizer.length, body.length - offset - 1);
		for (let length = maxLength; length >= 2; length--) {
			const candidate = body.slice(offset, offset + length);
			if (
				!statementListMatchesFinalizerPrefix(
					candidate,
					finalizer.slice(0, length),
				)
			) continue;

			const tail = body.slice(offset + length);
			const last = tail.at(-1);
			if (!last || !statementAlwaysTerminates(last)) continue;

			if (preserveAbruptCompletion) {
				body.splice(offset, body.length - offset, t.returnStatement());
			} else {
				body.splice(offset, length);
			}
			return true;
		}
	}

	return false;
}

export function commonTerminalSuffixLength(
	left: t.Statement[],
	right: t.Statement[],
) {
	const maxLength = Math.min(left.length, right.length);
	let length = 0;
	while (
		length < maxLength &&
		statementsEqual(
			left[left.length - length - 1],
			right[right.length - length - 1],
		)
	) {
		length++;
	}

	if (length < 2) return 0;
	const suffix = left.slice(left.length - length);
	const last = suffix.at(-1);
	if (!last || !statementAlwaysTerminates(last)) return 0;

	return length;
}

export function liftCommonTerminalSuffixToFinally(statement: t.TryStatement) {
	if (statement.finalizer || !statement.handler) return false;

	const tryBody = statement.block.body;
	const catchBody = statement.handler.body.body;
	const length = commonTerminalSuffixLength(tryBody, catchBody);
	if (length !== 0) {
		const finalizer = tryBody.slice(tryBody.length - length);
		tryBody.splice(tryBody.length - length);
		catchBody.splice(catchBody.length - length);
		statement.finalizer = t.blockStatement(finalizer);
		return true;
	}

	const lastTryStatement = tryBody.at(-1);
	if (!t.isTryStatement(lastTryStatement) || !lastTryStatement.finalizer) {
		return false;
	}

	const innerFinallyBody = lastTryStatement.finalizer.body;
	const innerLength = commonTerminalSuffixLength(innerFinallyBody, catchBody);
	if (innerLength === 0) return false;

	const finalizer = innerFinallyBody.slice(
		innerFinallyBody.length - innerLength,
	);
	innerFinallyBody.splice(innerFinallyBody.length - innerLength);
	if (innerFinallyBody.length === 0) {
		lastTryStatement.finalizer = null;
	}
	catchBody.splice(catchBody.length - innerLength);
	statement.finalizer = t.blockStatement(finalizer);
	return true;
}

export function splitNestedTerminalFinalizer(
	statement: t.TryStatement,
): t.TryStatement | null {
	if (!statement.finalizer) return null;
	if (statement.finalizer.body.length !== 1) return null;

	const nested = statement.finalizer.body[0];
	if (!t.isTryStatement(nested) || !nested.finalizer) return null;

	const nestedFinalizer = nested.finalizer.body;
	if (nestedFinalizer.length < 3) return null;

	for (let offset = 1; offset < nestedFinalizer.length - 1; offset++) {
		const tail = nestedFinalizer.slice(offset);
		if (!statementAlwaysTerminates(t.blockStatement(tail))) continue;

		nested.finalizer.body = nestedFinalizer.slice(0, offset);
		return t.tryStatement(
			t.blockStatement([statement]),
			null,
			t.blockStatement(tail),
		);
	}

	return null;
}
