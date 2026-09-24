import { parse } from '@babel/parser';
import _traverse from '@babel/traverse';
import type { NodePath } from '@babel/traverse';
import * as t from '@babel/types';
// deno-lint-ignore no-explicit-any
const traverse = ((_traverse as any).default ?? _traverse) as typeof _traverse;
const SYNTH =
	/^(cfg_exit_|cfg_cont_|cfg_forest_|cfg_scope_|cfg_dag_|scope_|loop_\d+$|loop\d+_body_)/;
const bump = (m: Map<string, number>, k: string) => m.set(k, (m.get(k) ?? 0) + 1);
const kinds = new Map<string, number>();
let total = 0;
const depths = new Map<number, number>();

const src = await Deno.readTextFile(Deno.args[0]);
const chunks: string[] = []; let cur: string[] = [];
for (const line of src.split('\n')) {
	if (line.startsWith('__d(') && cur.length) { chunks.push(cur.join('\n')); cur = []; }
	cur.push(line);
}
if (cur.length) chunks.push(cur.join('\n'));
const decl =
	/(cfg_(exit|cont|forest|scope|dag)_[0-9a-f]+|scope_[0-9a-f_]+|loop\d+_body_[0-9a-f_]+|loop_\d+)\s*:/;

for (const chunk of chunks) {
	if (!decl.test(chunk)) continue;
	let file;
	try { file = parse(chunk, { sourceType: 'script', plugins: ['v8intrinsic'], errorRecovery: true }); }
	catch { continue; }
	traverse(file, {
		LabeledStatement(path: NodePath<t.LabeledStatement>) {
			const name = path.node.label.name;
			if (!SYNTH.test(name)) return;
			total++;
			// nesting depth of synthetic labels above this one
			let depth = 0;
			let a: NodePath | null = path.parentPath;
			while (a) {
				if (t.isLabeledStatement(a.node) && SYNTH.test(a.node.label.name)) depth++;
				a = a.parentPath;
			}
			depths.set(depth, (depths.get(depth) ?? 0) + 1);
			// does every break to this label originate inside a NESTED synthetic label?
			let refs = 0, fromNested = 0;
			path.traverse({
				'BreakStatement|ContinueStatement'(
					p: NodePath<t.BreakStatement | t.ContinueStatement>,
				) {
					if (p.node.label?.name !== name) return;
					refs++;
					let q: NodePath | null = p.parentPath;
					while (q && q.node !== path.node) {
						if (t.isLabeledStatement(q.node) && SYNTH.test(q.node.label.name)) {
							fromNested++; return;
						}
						q = q.parentPath;
					}
				},
			});
			bump(kinds, refs === 0 ? 'no refs'
				: fromNested === refs ? 'ENCLOSING CASCADE (all breaks from inside a nested label)'
				: fromNested > 0 ? 'mixed (some breaks from nested labels)'
				: 'own breaks only (innermost owner)');
		},
	});
}
console.log(`labels: ${total}`);
console.log('\nrole in the ladder:');
for (const [k, v] of [...kinds].sort((a, b) => b[1] - a[1])) {
	console.log(`  ${String(v).padStart(4)}  ${(100*v/total).toFixed(1).padStart(5)}%  ${k}`);
}
console.log('\nnesting depth (synthetic labels enclosing this one):');
for (const [k, v] of [...depths].sort((a, b) => a[0] - b[0])) {
	console.log(`  depth ${String(k).padStart(2)}: ${String(v).padStart(4)}`);
}
