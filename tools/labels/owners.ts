import { parse } from '@babel/parser';
import _traverse from '@babel/traverse';
import type { NodePath } from '@babel/traverse';
import * as t from '@babel/types';
// deno-lint-ignore no-explicit-any
const traverse = ((_traverse as any).default ?? _traverse) as typeof _traverse;
const SYNTH =
	/^(cfg_exit_|cfg_cont_|cfg_forest_|cfg_scope_|cfg_dag_|scope_|loop_\d+$|loop\d+_body_)/;

const src = await Deno.readTextFile(Deno.args[0]);
const chunks: string[] = []; let cur: string[] = [];
for (const line of src.split('\n')) {
	if (line.startsWith('__d(') && cur.length) { chunks.push(cur.join('\n')); cur = []; }
	cur.push(line);
}
if (cur.length) chunks.push(cur.join('\n'));
const decl =
	/(cfg_(exit|cont|forest|scope|dag)_[0-9a-f]+|scope_[0-9a-f_]+|loop\d+_body_[0-9a-f_]+|loop_\d+)\s*:/;
const pid = /_(?:param|env)_(\d+)_/;

type Row = { fn: string; owners: number; cascades: number; total: number };
const rows = new Map<string, Row>();

for (const chunk of chunks) {
	if (!decl.test(chunk)) continue;
	let file;
	try { file = parse(chunk, { sourceType: 'script', plugins: ['v8intrinsic'], errorRecovery: true }); }
	catch { continue; }
	traverse(file, {
		LabeledStatement(path: NodePath<t.LabeledStatement>) {
			const name = path.node.label.name;
			if (!SYNTH.test(name)) return;
			const fnPath = path.getFunctionParent();
			const src2 = fnPath ? chunk.slice(fnPath.node.start ?? 0, (fnPath.node.start ?? 0) + 400) : '';
			const key = (src2.match(pid)?.[1]) ?? 'unknown';
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
			const row = rows.get(key) ?? { fn: key, owners: 0, cascades: 0, total: 0 };
			row.total++;
			if (refs > 0 && fromNested === refs) row.cascades++;
			else row.owners++;
			rows.set(key, row);
		},
	});
}
const all = [...rows.values()].sort((a, b) => b.total - a.total);
const totLabels = all.reduce((n, r) => n + r.total, 0);
const totOwners = all.reduce((n, r) => n + r.owners, 0);
console.log(`functions carrying labels: ${all.length}`);
console.log(`labels ${totLabels}   innermost owners ${totOwners}   cascades ${totLabels - totOwners}`);
let cum = 0, i = 0;
console.log('\ntop functions by label count:');
for (const r of all.slice(0, 10)) {
	cum += r.total; i++;
	console.log(`  fn ${r.fn.padStart(7)}  labels=${String(r.total).padStart(3)}  owners=${String(r.owners).padStart(3)}  cascades=${String(r.cascades).padStart(3)}  cum=${(100*cum/totLabels).toFixed(1)}%`);
}
const n5 = all.slice(0, 5).reduce((n, r) => n + r.total, 0);
const o5 = all.slice(0, 5).reduce((n, r) => n + r.owners, 0);
console.log(`\ntop 5 functions: ${n5} labels (${(100*n5/totLabels).toFixed(1)}%) from ${o5} innermost owners`);
