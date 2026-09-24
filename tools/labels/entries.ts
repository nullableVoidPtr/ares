import { parse } from '@babel/parser';
import _traverse from '@babel/traverse';
import type { NodePath } from '@babel/traverse';
import * as t from '@babel/types';
// deno-lint-ignore no-explicit-any
const traverse = ((_traverse as any).default ?? _traverse) as typeof _traverse;

const SYNTH =
	/^(cfg_exit_|cfg_cont_|cfg_forest_|cfg_scope_|cfg_dag_|scope_|loop_\d+$|loop\d+_body_)/;
const fam = (n: string) =>
	n.startsWith('cfg_exit_') ? 'cfg_exit'
	: n.startsWith('cfg_cont_') ? 'cfg_cont'
	: n.startsWith('cfg_forest_') ? 'cfg_forest'
	: n.startsWith('cfg_scope_') ? 'cfg_scope'
	: n.startsWith('cfg_dag_') ? 'cfg_dag'
	: /^loop\d+_body_/.test(n) ? 'loopN_body'
	: /^loop_\d+$/.test(n) ? 'loop_n' : 'scope';

/** Whether a statement always completes abruptly (never falls out its end). */
function alwaysTerminates(s: t.Statement | null | undefined): boolean {
	if (!s) return false;
	if (t.isReturnStatement(s) || t.isThrowStatement(s)) return true;
	if (t.isBreakStatement(s) || t.isContinueStatement(s)) return true;
	if (t.isBlockStatement(s)) return alwaysTerminates(s.body[s.body.length - 1]);
	if (t.isIfStatement(s)) {
		return !!s.alternate && alwaysTerminates(s.consequent) &&
			alwaysTerminates(s.alternate);
	}
	if (t.isLabeledStatement(s)) return alwaysTerminates(s.body);
	if (t.isTryStatement(s)) {
		if (s.finalizer && alwaysTerminates(s.finalizer)) return true;
		return alwaysTerminates(s.block) &&
			(!s.handler || alwaysTerminates(s.handler.body));
	}
	if (t.isSwitchStatement(s)) {
		return s.cases.length > 0 &&
			s.cases.some((c) => c.test == null) &&
			s.cases.every((c) =>
				c.consequent.length === 0 ||
				alwaysTerminates(c.consequent[c.consequent.length - 1])
			);
	}
	return false;
}

const src = await Deno.readTextFile(Deno.args[0]);
const chunks: string[] = [];
let cur: string[] = [];
for (const line of src.split('\n')) {
	if (line.startsWith('__d(') && cur.length) { chunks.push(cur.join('\n')); cur = []; }
	cur.push(line);
}
if (cur.length) chunks.push(cur.join('\n'));
const decl =
	/(cfg_(exit|cont|forest|scope|dag)_[0-9a-f]+|scope_[0-9a-f_]+|loop\d+_body_[0-9a-f_]+|loop_\d+)\s*:/;

const buckets = new Map<number, number>();
const byFamSingle = new Map<string, number>();
const byFam = new Map<string, number>();
let total = 0, transfers = 0, fnCount = 0;
const fns = new Set<string>();

for (const chunk of chunks) {
	if (!decl.test(chunk)) continue;
	let file;
	try { file = parse(chunk, { sourceType: 'script', plugins: ['v8intrinsic'], errorRecovery: true }); }
	catch { continue; }
	traverse(file, {
		LabeledStatement(path: NodePath<t.LabeledStatement>) {
			const name = path.node.label.name;
			if (!SYNTH.test(name)) return;
			let refs = 0;
			path.traverse({
				'BreakStatement|ContinueStatement'(
					p: NodePath<t.BreakStatement | t.ContinueStatement>,
				) { if (p.node.label?.name === name) refs++; },
			});
			const fallsOut = !alwaysTerminates(path.node.body);
			const entries = refs + (fallsOut ? 1 : 0);
			total++; transfers += refs;
			buckets.set(entries, (buckets.get(entries) ?? 0) + 1);
			byFam.set(fam(name), (byFam.get(fam(name)) ?? 0) + 1);
			if (entries <= 1) {
				byFamSingle.set(fam(name), (byFamSingle.get(fam(name)) ?? 0) + 1);
			}
			const fn = path.getFunctionParent();
			if (fn) fns.add(String(fn.node.start));
		},
	});
	fnCount = fns.size;
}
console.log(`labels: ${total}   labelled transfers: ${transfers}   functions: ${fnCount}`);
console.log('\nentries in the continuation:');
for (const [k, v] of [...buckets].sort((a, b) => a[0] - b[0])) {
	console.log(`  ${k === 1 ? '1 (placement artifact)' : String(k).padEnd(22)} ${String(v).padStart(4)}  ${(100*v/total).toFixed(1)}%`);
}
console.log('\nsingle-entry share by family:');
for (const [k, v] of [...byFam].sort((a, b) => b[1] - a[1])) {
	const s = byFamSingle.get(k) ?? 0;
	console.log(`  ${k.padEnd(12)} ${String(s).padStart(3)} of ${String(v).padStart(3)}  ${(100*s/v).toFixed(0)}%`);
}
