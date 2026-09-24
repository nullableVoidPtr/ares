import * as t from '@babel/types';
import { SSARegister, ssaRegisterEquals } from '../../ssa.ts';
import { LiftedAST } from './mod.ts';

// Reconstructs chained assignment expressions (`a = b = c = R`) from the flat
// sequence of stores Hermes emits for a single SSA register. e.g.
//   _param_5_.X = r3_17;          →   const _env_1 = _param_5_.X = r3_17;
//   const _env_1 = r3_17;
// Folding the stores into one chain leaves exactly one textual reference to the
// register, which is what unblocks inlineObjectConstruction (its refs.size === 1
// guard) from collapsing the object literal into the chain.
//
// The "same value" test is by SSA register identity via the `sourceRegister`
// LiftedExtra tag (set in registerAsIdentifier), never by the textual rN_M name.

function registerOfIdentifier(node: t.Node): SSARegister | null {
	if (!t.isIdentifier(node)) return null;
	return (node as LiftedAST<t.Identifier>).extra?.sourceRegister ?? null;
}

type RegisterStore =
	| {
		kind: 'assign';
		target: t.LVal;
		rhs: t.Identifier;
		register: SSARegister;
	}
	| {
		kind: 'decl';
		declKind: 'const' | 'let' | 'var';
		id: t.LVal;
		rhs: t.Identifier;
		register: SSARegister;
	};

// `target = R` or `const name = R`, where R is a register-use identifier.
function asRegisterStore(stmt: t.Statement): RegisterStore | null {
	if (t.isExpressionStatement(stmt)) {
		const expr = stmt.expression;
		if (!t.isAssignmentExpression(expr, { operator: '=' })) return null;
		if (!t.isMemberExpression(expr.left) && !t.isIdentifier(expr.left)) {
			return null;
		}
		const register = registerOfIdentifier(expr.right);
		if (!register) return null;
		return {
			kind: 'assign',
			target: expr.left,
			rhs: expr.right as t.Identifier,
			register,
		};
	}

	if (t.isVariableDeclaration(stmt) && stmt.declarations.length === 1) {
		const [decl] = stmt.declarations;
		if (!decl.init) return null;
		const register = registerOfIdentifier(decl.init);
		if (!register) return null;
		if (t.isVoidPattern(decl.id)) return null;
		return {
			kind: 'decl',
			declKind: stmt.kind as 'const' | 'let' | 'var',
			id: decl.id,
			rhs: decl.init as t.Identifier,
			register,
		};
	}

	return null;
}

export function chainSharedRegisterAssignmentsInBody(
	body: t.Statement[],
): boolean {
	let changed = false;

	// Recurse into nested blocks first.
	for (const stmt of body) {
		if (t.isIfStatement(stmt)) {
			if (t.isBlockStatement(stmt.consequent)) {
				changed = chainSharedRegisterAssignmentsInBody(
					stmt.consequent.body,
				) || changed;
			}
			if (stmt.alternate && t.isBlockStatement(stmt.alternate)) {
				changed = chainSharedRegisterAssignmentsInBody(
					stmt.alternate.body,
				) || changed;
			}
		} else if (
			(t.isWhileStatement(stmt) || t.isForInStatement(stmt) ||
				t.isForOfStatement(stmt) || t.isForStatement(stmt)) &&
			t.isBlockStatement(stmt.body)
		) {
			changed = chainSharedRegisterAssignmentsInBody(stmt.body.body) ||
				changed;
		} else if (t.isTryStatement(stmt)) {
			changed = chainSharedRegisterAssignmentsInBody(stmt.block.body) ||
				changed;
			if (stmt.handler) {
				changed = chainSharedRegisterAssignmentsInBody(
					stmt.handler.body.body,
				) || changed;
			}
			if (stmt.finalizer) {
				changed = chainSharedRegisterAssignmentsInBody(
					stmt.finalizer.body,
				) || changed;
			}
		}
	}

	for (let i = 0; i < body.length; i++) {
		const first = asRegisterStore(body[i]);
		if (!first) continue;

		// Collect the maximal adjacent run storing the same SSA register. A `const`
		// binding can only be the outermost (leftmost) target, so it must come last.
		const run: RegisterStore[] = [];
		let j = i;
		while (j < body.length) {
			const store = asRegisterStore(body[j]);
			if (!store || !ssaRegisterEquals(store.register, first.register)) {
				break;
			}
			run.push(store);
			j++;
			if (store.kind === 'decl') break; // var decl terminates the chain
		}

		if (run.length < 2) continue;

		const trailingDecl = run[run.length - 1].kind === 'decl'
			? run[run.length - 1] as Extract<RegisterStore, { kind: 'decl' }>
			: null;

		if (!trailingDecl || t.isVoidPattern(trailingDecl.id)) continue;

		const assigns = (trailingDecl ? run.slice(0, -1) : run) as Extract<
			RegisterStore,
			{ kind: 'assign' }
		>[];

		// Build right-associatively with the first (topmost) store innermost, so the
		// store order matches the original top-to-bottom statement order.
		let chain: t.Expression = run[0].rhs; // the single surviving register reference
		for (const store of assigns) {
			chain = t.assignmentExpression('=', store.target, chain);
		}

		const folded: t.Statement = t.isIdentifier(trailingDecl?.id)
			? t.variableDeclaration(trailingDecl.declKind, [
				t.variableDeclarator(trailingDecl.id, chain),
			])
			: t.expressionStatement(chain);

		body.splice(i, run.length, folded);
		changed = true;
	}

	return changed;
}
