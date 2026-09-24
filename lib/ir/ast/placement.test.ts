import * as assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { parse } from '@babel/parser';
import * as t from '@babel/types';
import generate from '@babel/generator';
import {
	analyseBindingPlacement,
	analyseBindingPlacementInTree,
	placeGeneratedBindings,
	placeGeneratedBindingsInTree,
} from './placement.ts';
import { tagStorageLocation } from './alias.ts';

function analyse(source: string) {
	const file = parse(source, { sourceType: 'script' });
	return analyseBindingPlacement(file.program);
}

/**
 * Build a program directly.
 *
 * The shapes this pass exists to repair -- two `const rN_M` in one scope, a
 * `var` colliding with an outer `let` -- are ones Babel's *parser* rejects
 * outright, which is exactly why they have to be repaired before anything asks
 * Babel for scopes. They can only be expressed as a built tree.
 */
function build(...body: t.Statement[]) {
	return analyseBindingPlacement(t.program(body));
}

const call = (name: string) => t.callExpression(t.identifier(name), []);
const declare = (
	kind: 'const' | 'let' | 'var',
	name: string,
	init?: t.Expression,
) => t.variableDeclaration(kind, [
	t.variableDeclarator(t.identifier(name), init ?? null),
]);
const ssaIdentifier = (index: number, version: number) => {
	return tagStorageLocation(t.identifier(`r${index}_${version}`), {
		kind: 'register',
		owner: { functionId: 3 },
		register: { type: 'register', index, version },
	});
};

/** Which statement list a name was placed in, as its printed first statement. */
function placedScopeHead(
	result: ReturnType<typeof analyse>,
	name: string,
): string | null {
	const placement = result.placed.get(name);
	if (!placement) return null;
	const [first] = placement.scope;
	return first ? first.type : 'empty';
}

describe('analyseBindingPlacement', () => {
	it('leaves a binding whose uses are all in scope alone', () => {
		const result = analyse(`
			const r1_0 = f();
			g(r1_0);
		`);
		assert.ok(result.localized.has('r1_0'));
		assert.equal(result.placed.size, 0);
		assert.equal(result.unresolved.size, 0);
	});

	it('promotes a try declaration used from catch', () => {
		const result = analyse(`
			try {
				const r1_0 = f();
				g(r1_0);
			} catch (e) {
				h(r1_0);
			}
		`);
		const placement = result.placed.get('r1_0');
		assert.ok(placement, 'expected r1_0 to be placed');
		assert.ok(placement.reasons.includes('out-of-scope-use'));
		// The lowest list containing both the try body and the handler is the
		// program body.
		assert.equal(placedScopeHead(result, 'r1_0'), 'TryStatement');
	});

	it('promotes a declaration used after its block', () => {
		const result = analyse(`
			{
				const r2_1 = f();
			}
			g(r2_1);
		`);
		assert.ok(result.placed.get('r2_1'));
		assert.ok(
			result.placed.get('r2_1')!.reasons.includes('out-of-scope-use'),
		);
	});

	it('reports a duplicate declaration in one scope', () => {
		const result = build(
			declare('const', 'r3_0', call('f')),
			declare('const', 'r3_0', call('g')),
		);
		const placement = result.placed.get('r3_0');
		assert.ok(placement);
		assert.ok(placement.reasons.includes('same-scope-duplicate'));
	});

	it('keeps independent sibling scopes local', () => {
		// Two loops each declaring their own copy, neither escaping: these are
		// per-iteration bindings, not one binding declared twice.
		const result = analyse(`
			while (a) {
				const r4_0 = f();
				g(r4_0);
			}
			while (b) {
				const r5_0 = f();
				g(r5_0);
			}
		`);
		assert.ok(result.localized.has('r4_0'));
		assert.ok(result.localized.has('r5_0'));
		assert.equal(result.placed.size, 0);
	});

	it('keeps per-arm declarations of one name independent', () => {
		// Region emission declares the same SSA version in each arm of a
		// branch. Only one ever executes, so these are independent bindings and
		// consolidating them would discard a correct localization.
		const result = analyse(`
			if (a) {
				const r20_0 = f();
				g(r20_0);
			} else {
				const r20_0 = h();
				g(r20_0);
			}
		`);
		assert.ok(result.localized.has('r20_0'));
		assert.equal(result.placed.size, 0);
	});

	it('consolidates per-arm declarations once one escapes', () => {
		// An outside reference proves the arms are placements of one binding.
		const result = analyse(`
			if (a) {
				const r21_0 = f();
			} else {
				const r21_0 = h();
			}
			g(r21_0);
		`);
		const placement = result.placed.get('r21_0');
		assert.ok(placement);
		assert.ok(placement.reasons.includes('out-of-scope-use'));
		assert.equal(
			placement.reasons.includes('same-scope-duplicate'),
			false,
			'two arms are not one scope',
		);
	});

	it('treats a nested var as function-scoped when it collides', () => {
		const result = build(
			declare('let', 'r6_0'),
			t.tryStatement(
				t.blockStatement([declare('var', 'r6_0', call('f'))]),
				t.catchClause(t.identifier('e'), t.blockStatement([])),
			),
		);
		const placement = result.placed.get('r6_0');
		assert.ok(placement);
		assert.ok(placement.reasons.includes('var-lexical-collision'));
	});

	it('promotes a whole destructuring pattern', () => {
		const result = analyse(`
			{
				const { a: r7_0, b: r7_1 } = f();
			}
			g(r7_0);
		`);
		assert.ok(result.placed.get('r7_0'));
		assert.ok(
			result.placed.get('r7_0')!.reasons.includes('pattern-closure'),
		);
	});

	it('places an assignment-only binding with SSA provenance', () => {
		const target = ssaIdentifier(8, 0);
		const result = build(
			t.ifStatement(
				t.identifier('a'),
				t.blockStatement([
					t.expressionStatement(t.assignmentExpression(
						'=',
						target,
						call('f'),
					)),
				]),
			),
			t.expressionStatement(t.callExpression(t.identifier('g'), [
				ssaIdentifier(8, 0),
			])),
		);
		const placement = result.placed.get('r8_0');
		assert.ok(placement);
		assert.ok(
			placement.reasons.includes('assignment-without-declaration'),
		);
		assert.equal(result.unresolved.has('r8_0'), false);
	});

	it('does not treat an untagged assignment as an SSA definition', () => {
		const result = analyse(`r8_1 = f(); g(r8_1);`);
		assert.ok(result.unresolved.has('r8_1'));
		assert.equal(result.placed.has('r8_1'), false);
	});

	it('leaves a reference-only register unresolved', () => {
		// The lost-definition rule: no declaration and no write means the CFG
		// lost a definition. Inventing one would turn a rejected candidate into
		// wrong output.
		const result = analyse(`g(r9_0);`);
		assert.ok(result.unresolved.has('r9_0'));
		assert.equal(result.placed.has('r9_0'), false);
		assert.equal(result.localized.has('r9_0'), false);
	});

	it('projects a switch case out to the enclosing list', () => {
		const result = build(
			t.switchStatement(t.identifier('a'), [
				t.switchCase(t.numericLiteral(1), [
					declare('const', 'r10_0', call('f')),
					t.breakStatement(),
				]),
				t.switchCase(t.numericLiteral(2), [
					declare('const', 'r10_0', call('g')),
					t.breakStatement(),
				]),
			]),
		);
		const placement = result.placed.get('r10_0');
		assert.ok(placement);
		assert.ok(placement.reasons.includes('same-scope-duplicate'));
		assert.equal(placedScopeHead(result, 'r10_0'), 'SwitchStatement');
	});

	it('promotes a for-header binding used after the loop', () => {
		// `for (let x …)` does not bind `x` after the loop, so the trailing use
		// is out of scope and the declaration has to move to the list the loop
		// sits in -- the header itself is not somewhere a declaration can go.
		const result = analyse(`
			for (let r11_0 = 0; r11_0 < n; r11_0++) {
				g(r11_0);
			}
			h(r11_0);
		`);
		const placement = result.placed.get('r11_0');
		assert.ok(placement, 'expected r11_0 to be placed');
		assert.ok(placement.reasons.includes('out-of-scope-use'));
		assert.equal(placedScopeHead(result, 'r11_0'), 'ForStatement');
	});

	it('keeps a for-header binding local when nothing escapes', () => {
		const result = analyse(`
			for (let r15_0 = 0; r15_0 < n; r15_0++) {
				g(r15_0);
			}
		`);
		assert.ok(result.localized.has('r15_0'));
		assert.equal(result.placed.size, 0);
	});

	it('analyses nested functions independently', () => {
		// The inner `r12_0` is a different binding; the outer analysis must not
		// see the inner one's uses and promote on their account.
		const result = analyse(`
			const r12_0 = f();
			g(r12_0);
			h(function () {
				const r12_0 = k();
				return r12_0;
			});
		`);
		assert.ok(result.localized.has('r12_0'));
		assert.equal(result.placed.size, 0);
	});

	it('refuses one spelling owned by two inlined functions', () => {
		const first = tagStorageLocation(t.identifier('r12_1'), {
			kind: 'register',
			owner: { functionId: 3 },
			register: { type: 'register', index: 12, version: 1 },
		});
		const second = tagStorageLocation(t.identifier('r12_1'), {
			kind: 'register',
			owner: { functionId: 4 },
			register: { type: 'register', index: 12, version: 1 },
		});
		const result = build(
			t.variableDeclaration('const', [
				t.variableDeclarator(first, call('f')),
			]),
			t.expressionStatement(second),
		);
		assert.ok(result.unresolved.has('r12_1'));
		assert.equal(result.placed.has('r12_1'), false);
		assert.equal(result.localized.has('r12_1'), false);
	});

	it('ignores user identifiers and property spellings', () => {
		const result = analyse(`
			const value = f();
			g(value, obj.r13_0);
		`);
		assert.equal(result.placed.size, 0);
		assert.equal(result.unresolved.size, 0);
		assert.equal(result.localized.size, 0);
	});

	it('defers environment slots until creation-site identity is attached', () => {
		const result = analyse(`
			{
				var _env_3_1 = f();
			}
			g(_env_3_1);
		`);
		assert.equal(result.localized.has('_env_3_1'), false);
		assert.equal(result.placed.has('_env_3_1'), false);
		assert.equal(result.unresolved.has('_env_3_1'), false);
	});

	it('is stable when run twice', () => {
		const source = `
			try {
				const r14_0 = f();
			} catch (e) {
				g(r14_0);
			}
		`;
		const first = analyse(source);
		const second = analyse(source);
		assert.deepEqual([...first.placed.keys()], [...second.placed.keys()]);
		assert.deepEqual(
			first.placed.get('r14_0')!.reasons,
			second.placed.get('r14_0')!.reasons,
		);
	});
});

describe('placeGeneratedBindings', () => {
	const print = (node: t.Program) =>
		generate(node, { concise: true }).code.replace(/\s+/g, ' ').trim();

	function rewrite(source: string) {
		const file = parse(source, { sourceType: 'script' });
		const result = placeGeneratedBindings(file.program);
		return { code: print(file.program), result, program: file.program };
	}

	function rewriteBuilt(...body: t.Statement[]) {
		const program = t.program(body);
		const result = placeGeneratedBindings(program);
		return { code: print(program), result, program };
	}

	it('hoists a try declaration used from catch', () => {
		const { code } = rewrite(`
			try {
				const r1_0 = f();
			} catch (e) {
				g(r1_0);
			}
		`);
		assert.equal(
			code,
			'let r1_0; try { r1_0 = f(); } catch (e) { g(r1_0); }',
		);
	});

	it('collapses duplicate declarations into one binding', () => {
		const { code } = rewriteBuilt(
			declare('const', 'r3_0', call('f')),
			declare('const', 'r3_0', call('g')),
		);
		assert.equal(code, 'let r3_0; r3_0 = f(); r3_0 = g();');
	});

	it('splits a multi-declarator statement in evaluation order', () => {
		const { code } = rewrite(`
			{
				const r2_0 = f(), r2_1 = g();
			}
			h(r2_0, r2_1);
		`);
		// `f()` still runs before `g()`.
		assert.equal(
			code,
			'let r2_0, r2_1; { r2_0 = f(); r2_1 = g(); } h(r2_0, r2_1);',
		);
	});

	it('keeps an unplaced declarator declared when splitting', () => {
		const { code } = rewrite(`
			{
				const r4_0 = f(), r4_9 = g();
				k(r4_9);
			}
			h(r4_0);
		`);
		assert.match(code, /let r4_0;/);
		assert.match(code, /const r4_9 = g\(\);/);
		assert.match(code, /r4_0 = f\(\);/);
	});

	it('drops a promoted declaration that has no initialiser', () => {
		const { code } = rewrite(`
			{
				let r5_0;
				r5_0 = f();
			}
			h(r5_0);
		`);
		assert.equal(code, 'let r5_0; { r5_0 = f(); } h(r5_0);');
	});

	it('merges an unwritten outer register with its nested definition', () => {
		const { code, result } = rewrite(`
			while (condition) {
				let r5_0;
				r5_0 = next();
			}
			let r5_0;
			consume(r5_0);
		`);
		assert.equal(
			code,
			'let r5_0; while (condition) { r5_0 = next(); } consume(r5_0);',
		);
		assert.ok(
			result.placed.get('r5_0')?.reasons.includes(
				'unwritten-ancestor-declaration',
			),
		);
	});

	it('converts a for initialiser to an assignment', () => {
		const { code } = rewrite(`
			for (let r6_0 = 0; r6_0 < n; r6_0++) {}
			h(r6_0);
		`);
		assert.equal(
			code,
			'let r6_0; for (r6_0 = 0; r6_0 < n; r6_0++) {} h(r6_0);',
		);
	});

	it('promotes every generated declarator in a partial for header', () => {
		const { code, result } = rewrite(`
			for (let r6_1 = 0, r6_2 = 1; r6_1 < 2; r6_1++) {
				use(r6_2);
			}
			use(r6_1);
		`);
		assert.ok(result.placed.has('r6_1'));
		assert.ok(result.placed.has('r6_2'));
		assert.equal(
			code,
			'let r6_1, r6_2; for (r6_1 = 0, r6_2 = 1; r6_1 < 2; r6_1++) { use(r6_2); } use(r6_1);',
		);
	});

	it('converts a for-of target to an assignment target', () => {
		const { code } = rewrite(`
			for (const r7_0 of xs) {}
			h(r7_0);
		`);
		assert.equal(code, 'let r7_0; for (r7_0 of xs) {} h(r7_0);');
	});

	it('promotes a destructuring pattern as one unit', () => {
		const { code, result } = rewrite(`
			{
				const { a: r8_0, b: r8_1 } = f();
			}
			h(r8_0);
		`);
		// `r8_1` did not escape on its own, but its sibling did and the
		// declarator is one syntactic unit.
		assert.ok(result.placed.has('r8_1'));
		assert.match(code, /let r8_0, r8_1;/);
		assert.match(code, /\{\s*a: r8_0,\s*b: r8_1\s*\} = f\(\)/);
	});

	it('refuses mixed user/generated destructuring without shadowing', () => {
		const { code, result } = rewrite(`
			{
				const { a: r8_2, b: value } = source;
				use(value);
			}
			use(r8_2);
		`);
		assert.ok(result.unresolved.has('r8_2'));
		assert.equal(result.placed.has('r8_2'), false);
		assert.doesNotMatch(code, /^let r8_2;/);
		assert.match(code, /const \{\s*a: r8_2,\s*b: value\s*\} = source/);
	});

	it('converts a colliding var pattern', () => {
		const { code } = rewriteBuilt(
			declare('let', 'r9_0'),
			t.tryStatement(
				t.blockStatement([
					t.variableDeclaration('var', [
						t.variableDeclarator(
							t.objectPattern([
								t.objectProperty(
									t.identifier('x'),
									t.identifier('r9_0'),
								),
							]),
							call('f'),
						),
					]),
				]),
				t.catchClause(t.identifier('e'), t.blockStatement([])),
			),
		);
		assert.match(code, /let r9_0;/);
		assert.match(code, /\{\s*x: r9_0\s*\} = f\(\)/);
		assert.doesNotMatch(code, /var \{/);
	});

	it('leaves an already-correct tree untouched', () => {
		const source = `const r10_0 = f(); g(r10_0);`;
		const { code, result } = rewrite(source);
		assert.equal(result.placed.size, 0);
		assert.equal(code, 'const r10_0 = f(); g(r10_0);');
	});

	it('never invents a declaration for a lost definition', () => {
		const { code, result } = rewrite(`g(r11_0);`);
		assert.ok(result.unresolved.has('r11_0'));
		assert.equal(code, 'g(r11_0);');
	});

	it('is idempotent', () => {
		const source = `
			try {
				const r12_0 = f();
			} catch (e) {
				g(r12_0);
			}
		`;
		const first = rewrite(source);
		const second = placeGeneratedBindings(first.program);
		assert.equal(second.placed.size, 0);
		assert.equal(print(first.program), first.code);
	});

	it('produces a tree Babel can build scopes for', () => {
		const { code } = rewrite(`
			try {
				const r13_0 = f();
			} catch (e) {
				g(r13_0);
			}
		`);
		// Re-parsing is the real test: the shapes this pass repairs are ones
		// Babel's parser rejects outright.
		assert.doesNotThrow(() => parse(code, { sourceType: 'script' }));
	});

	it('skips a tree with no generated bindings', () => {
		const { result, code } = rewrite(`const value = f(); g(value);`);
		assert.equal(result.placed.size, 0);
		assert.equal(result.localized.size, 0, 'early-out short-circuits');
		assert.equal(code, 'const value = f(); g(value);');
	});

	it('still reports a flat tree with no nesting', () => {
		// No nested statement list, but a duplicate declaration and a lost
		// definition are both problems that need no nesting at all.
		const { result } = rewrite(`const r16_0 = f(); g(r16_0, r16_9);`);
		assert.ok(result.localized.has('r16_0'));
		assert.ok(result.unresolved.has('r16_9'));
	});

	it('inserts after a directive prologue', () => {
		const { code } = rewrite(`
			"use strict";
			try {
				const r15_0 = f();
			} catch (e) {
				g(r15_0);
			}
		`);
		assert.match(code, /^"use strict"; let r15_0;/);
	});
});

describe('function-tree placement', () => {
	it('analyses nested functions as independent owners', () => {
		const file = parse(
			`
			const r1_0 = outer();
			use(r1_0);
			const fn = function () {
				try { const r1_0 = inner(); }
				catch (error) { use(r1_0); }
			};
		`,
			{ sourceType: 'script' },
		);
		const result = analyseBindingPlacementInTree(file.program);
		assert.equal(result.entries.length, 2);
		assert.equal(result.entries[0].result.placed.size, 0);
		assert.ok(result.entries[1].result.placed.has('r1_0'));
	});

	it('rewrites nested functions bottom-up without merging equal names', () => {
		const file = parse(
			`
			try { const r2_0 = outer(); }
			catch (error) { use(r2_0); }
			const fn = function () {
				try { const r2_0 = inner(); }
				catch (error) { use(r2_0); }
			};
		`,
			{ sourceType: 'script' },
		);
		const result = placeGeneratedBindingsInTree(file.program);
		assert.equal(result.entries.length, 2);
		assert.equal(result.placed, 2);
		const code = generate(file.program, { concise: true }).code;
		assert.equal((code.match(/let r2_0/g) ?? []).length, 2);
	});
});
