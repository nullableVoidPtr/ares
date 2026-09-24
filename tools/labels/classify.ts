import { parse } from '@babel/parser';
import _traverse from '@babel/traverse';
import type { NodePath } from '@babel/traverse';
import * as t from '@babel/types';

// deno-lint-ignore no-explicit-any
const traverse = ((_traverse as any).default ?? _traverse) as typeof _traverse;

const SYNTH =
	/^(cfg_exit_|cfg_cont_|cfg_forest_|cfg_scope_|cfg_dag_|scope_|loop_\d+$|loop\d+_body_)/;

function family(name: string): string {
	if (name.startsWith('cfg_exit_')) return 'cfg_exit';
	if (name.startsWith('cfg_cont_')) return 'cfg_cont';
	if (name.startsWith('cfg_forest_')) return 'cfg_forest';
	if (name.startsWith('cfg_scope_')) return 'cfg_scope';
	if (name.startsWith('cfg_dag_')) return 'cfg_dag';
	if (/^loop\d+_body_/.test(name)) return 'loopN_body';
	if (/^loop_\d+$/.test(name)) return 'loop_n';
	if (name.startsWith('scope_')) return 'scope';
	return 'other';
}

const isLoop = (n: t.Node) =>
	t.isForStatement(n) || t.isForInStatement(n) || t.isForOfStatement(n) ||
	t.isWhileStatement(n) || t.isDoWhileStatement(n);
const isBreakable = (n: t.Node) => isLoop(n) || t.isSwitchStatement(n);

type Cat =
	| 'dead'
	| 'redundant-direct'
	| 'tail-block'
	| 'block-exit'
	| 'required-multilevel';

const counts = new Map<string, Map<Cat, number>>();
const wraps = new Map<string, Map<string, number>>();
let labels = 0, parseFailures = 0, modulesParsed = 0;

function bump(m: Map<string, Map<string, number>>, k: string, v: string) {
	let inner = m.get(k);
	if (!inner) m.set(k, inner = new Map());
	inner.set(v, (inner.get(v) ?? 0) + 1);
}

const src = await Deno.readTextFile(Deno.args[0]);
const lines = src.split('\n');
const chunks: string[] = [];
let cur: string[] = [];
for (const line of lines) {
	if (line.startsWith('__d(') && cur.length) {
		chunks.push(cur.join('\n'));
		cur = [];
	}
	cur.push(line);
}
if (cur.length) chunks.push(cur.join('\n'));

const labelDecl = /(^|[^A-Za-z0-9_$.])(cfg_(exit|cont|forest|scope|dag)_[0-9a-f]+|scope_[0-9a-f_]+|loop\d+_body_[0-9a-f_]+|loop_\d+)\s*:/m;

for (const chunk of chunks) {
	if (!labelDecl.test(chunk)) continue;
	let file;
	try {
		file = parse(chunk, {
			sourceType: 'script',
			plugins: ['v8intrinsic'],
			errorRecovery: true,
		});
	} catch {
		parseFailures++;
		continue;
	}
	modulesParsed++;
	traverse(file, {
		LabeledStatement(path: NodePath<t.LabeledStatement>) {
			const name = path.node.label.name;
			if (!SYNTH.test(name)) return;
			labels++;
			const body = path.node.body;
			bump(wraps, family(name), body.type);

			const refs: NodePath<t.BreakStatement | t.ContinueStatement>[] = [];
			path.traverse({
				'BreakStatement|ContinueStatement'(
					p: NodePath<t.BreakStatement | t.ContinueStatement>,
				) {
					if (p.node.label?.name === name) refs.push(p);
				},
			});

			let cat: Cat;
			if (refs.length === 0) {
				cat = 'dead';
			} else {
				// Does any reference cross an intervening construct that would
				// capture a bare break/continue?
				let crosses = false;
				for (const ref of refs) {
					const wantLoop = t.isContinueStatement(ref.node);
					let p: NodePath | null = ref.parentPath;
					while (p && p.node !== path.node) {
						const n = p.node;
						if (wantLoop ? isLoop(n) : isBreakable(n)) {
							if (n !== body) { crosses = true; break; }
						}
						p = p.parentPath;
					}
					if (crosses) break;
				}
				if (crosses) cat = 'required-multilevel';
				else if (isBreakable(body)) cat = 'redundant-direct';
				else if (t.isBlockStatement(body)) {
					const stmts = body.body;
					const allTail = refs.every((r) =>
						r.node === stmts[stmts.length - 1]
					);
					cat = allTail ? 'tail-block' : 'block-exit';
				} else cat = 'block-exit';
			}
			bump(counts as never, family(name), cat);
		},
	});
}

console.log(`modules with labels parsed: ${modulesParsed}  parseFailures: ${parseFailures}`);
console.log(`labelled statements classified: ${labels}\n`);

const cats: Cat[] = ['dead', 'redundant-direct', 'tail-block', 'block-exit', 'required-multilevel'];
const fams = [...counts.keys()].sort();
console.log(
	'family'.padEnd(12) + cats.map((c) => c.padStart(20)).join('') + 'total'.padStart(8),
);
const totals = new Map<string, number>();
for (const f of fams) {
	const row = counts.get(f)!;
	let tot = 0;
	let line = f.padEnd(12);
	for (const c of cats) {
		const v = row.get(c) ?? 0;
		tot += v;
		totals.set(c, (totals.get(c) ?? 0) + v);
		line += String(v).padStart(20);
	}
	console.log(line + String(tot).padStart(8));
}
let gt = 0;
let last = 'TOTAL'.padEnd(12);
for (const c of cats) { const v = totals.get(c) ?? 0; gt += v; last += String(v).padStart(20); }
console.log(last + String(gt).padStart(8));

console.log('\n=== what each family wraps ===');
for (const f of [...wraps.keys()].sort()) {
	const inner = [...wraps.get(f)!.entries()].sort((a, b) => b[1] - a[1]);
	console.log(`${f.padEnd(12)} ${inner.map(([k, v]) => `${k}:${v}`).join('  ')}`);
}
