import { HBCFile } from '../lib/parser/file.ts';

const verbose = Deno.args.includes('--verbose') || Deno.args.includes('-v');
const args = Deno.args.filter((arg) => arg !== '--verbose' && arg !== '-v');
const [path, functionIdArg] = args;
if (!path) {
	console.error(
		'usage: deno run --allow-read --allow-env tools/dump_blocks.ts <file.hbc> [function-id]',
	);
	Deno.exit(1);
}

const functionId = Number(functionIdArg ?? 0);
if (!Number.isInteger(functionId) || functionId < 0) {
	console.error(`invalid function id: ${functionIdArg}`);
	Deno.exit(1);
}

const file = HBCFile.fromFile(path);
const func = file.functions[functionId];
if (!func) {
	console.error(
		`function id ${functionId} does not exist; file has ${file.functions.length} functions`,
	);
	Deno.exit(1);
}

console.log('Exception handlers:', JSON.stringify(func.exceptionHandlers));
console.log('\nBasic blocks before SSA:');
for (const [addr, block] of func.basicBlocks) {
	const instrs = block.instructions
		.map((instr) =>
			`${instr.functionLocalOffset.toString(16)}:${instr.instruction}`
		)
		.join(', ');
	const consequents = block.consequentAddresses
		.map((consequent) => consequent.toString(16))
		.join(', ');
	console.log(`  0x${addr.toString(16)}: [${instrs}] -> [${consequents}]`);
	if (verbose) {
		for (const instr of block.instructions) {
			console.log(`    ${JSON.stringify(instr)}`);
		}
	}
}
