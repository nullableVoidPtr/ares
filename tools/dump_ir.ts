import generate from '@babel/generator';
import * as t from '@babel/types';
import { HBCFile } from '../lib/parser/file.ts';
import { IRFunction } from '../lib/ir/function/mod.ts';
import { SSAFunction } from '../lib/ssa.ts';

const [path, functionIdArg] = Deno.args;
const file = HBCFile.fromFile(path);
const functionId = Number(functionIdArg ?? 0);
const bytecodeFunction = file.functions[functionId];
if (!bytecodeFunction) {
	console.error(`function id ${functionId} does not exist`);
	Deno.exit(1);
}

const ir = new IRFunction(file, new SSAFunction(bytecodeFunction));
console.log(
	`PARAMS ${
		ir.params.map((param) => generate(param as t.Node).code).join(', ')
	}`,
);
for (const [addr, block] of ir.blocks) {
	const succ = block.consequentAddresses.map((a) => `0x${a.toString(16)}`)
		.join(', ');
	const metadata = [
		block.syntheticReason ? `reason=${block.syntheticReason}` : null,
		block.generatorState == null ? null : `state=${block.generatorState}`,
		block.pairedFinallyState == null
			? null
			: `pairedFinally=${block.pairedFinallyState}`,
		block.recoveredFinalizerOwner == null
			? null
			: `finalizerOwner=0x${block.recoveredFinalizerOwner.toString(16)}`,
		block.recoveredFinalizerRole == null
			? null
			: `finalizerRole=${block.recoveredFinalizerRole}`,
	].filter((item): item is string => item != null).join(' ');
	console.log(
		`BLOCK 0x${addr.toString(16)} -> [${succ}]${
			metadata ? ` ${metadata}` : ''
		}`,
	);
	if (block.branch) {
		console.log(`  branch: ${generate(block.branch as t.Node).code}`);
	}
	for (const stmt of block.body) {
		console.log(
			generate(stmt as t.Node).code.split('\n').map((line) => `  ${line}`)
				.join('\n'),
		);
	}
}
