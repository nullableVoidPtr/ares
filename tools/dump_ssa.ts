import generate from '@babel/generator';
import * as t from '@babel/types';
import { HBCFile } from '../lib/parser/file.ts';
import { IRFunction } from '../lib/ir/function/mod.ts';
import { liftSSABlocktoIR } from '../lib/ir/ast/lift.ts';
import { SSAFunction, type SSARegister } from '../lib/ssa.ts';

const [path, functionIdArg] = Deno.args;
const file = HBCFile.fromFile(path);
const functionId = Number(functionIdArg ?? 0);
const bytecodeFunction = file.functions[functionId];
if (!bytecodeFunction) {
	console.error(`function id ${functionId} does not exist`);
	Deno.exit(1);
}

function regName(reg: SSARegister): string {
	return `r${reg.index}_${reg.version}`;
}

const ssa = new SSAFunction(bytecodeFunction);
const irFunc = Object.create(IRFunction.prototype) as IRFunction;
Object.assign(irFunc, {
	file,
	ssa,
	id: bytecodeFunction.id,
	objectShapeKeysByRegister: new Map(),
});

for (const [addr, block] of ssa.basicBlocks) {
	const succ = block.consequentAddresses.map((a) => `0x${a.toString(16)}`)
		.join(', ');
	console.log(`BLOCK 0x${addr.toString(16)} -> [${succ}]`);
	for (const instr of block.ssaInstructions) {
		if (instr.instruction !== 'Phi') continue;
		const sources = [...instr.sources].map(([pred, source]) =>
			`0x${pred.toString(16)}:${regName(source)}`
		).join(', ');
		console.log(`  phi ${regName(instr.destination)} <- ${sources}`);
	}
	const lifted = liftSSABlocktoIR(irFunc, block);
	if (lifted.branch) {
		console.log(`  branch: ${generate(lifted.branch as t.Node).code}`);
	}
	for (const stmt of lifted.body) {
		console.log(
			generate(stmt as t.Node).code.split('\n').map((line) => `  ${line}`).join(
				'\n',
			),
		);
	}
}
