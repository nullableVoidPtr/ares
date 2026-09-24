import { liftFile } from './lib/ir/lift.ts';
import { HBCFile } from './lib/parser/file.ts';
import {
	formatGeneratedOutputIssue,
	type GeneratedOutputIssue,
	validateGeneratedOutput,
} from './tools/generated_output_validation.ts';

type Options = {
	verbose: boolean;
	samplesDir: string;
	paths: string[];
	cfgReducer: 'recursive';
};

function parseArgs(args: string[]): Options {
	let verbose = false;
	let samplesDir = 'samples';
	let cfgReducer: 'recursive' = 'recursive';
	const paths: string[] = [];

	for (let i = 0; i < args.length; i++) {
		const arg = args[i];
		if (arg === '--verbose' || arg === '-v') {
			verbose = true;
			continue;
		}
		if (arg === '--samples-dir') {
			const value = args[++i];
			if (!value) throw new Error('--samples-dir requires a path');
			samplesDir = value;
			continue;
		}
		if (arg.startsWith('--samples-dir=')) {
			samplesDir = arg.slice('--samples-dir='.length);
			continue;
		}
		if (arg === '--cfg-reducer') {
			const value = args[++i];
			if (!value) throw new Error('--cfg-reducer requires a value');
			cfgReducer = parseCFGReducer(value);
			continue;
		}
		if (arg.startsWith('--cfg-reducer=')) {
			cfgReducer = parseCFGReducer(arg.slice('--cfg-reducer='.length));
			continue;
		}
		paths.push(arg);
	}

	return { verbose, samplesDir, paths, cfgReducer };
}

function parseCFGReducer(value: string): 'recursive' {
	if (value === 'recursive') return value;
	throw new Error(
		`Invalid CFG reducer: ${value} (expected recursive)`,
	);
}

async function defaultSamplePaths(samplesDir: string) {
	const paths: string[] = [];
	for await (const entry of Deno.readDir(samplesDir)) {
		if (!entry.isDirectory) continue;
		for await (const file of Deno.readDir(`${samplesDir}/${entry.name}`)) {
			if (!file.isFile || !file.name.endsWith('.hbc')) continue;
			paths.push(`${samplesDir}/${entry.name}/${file.name}`);
		}
	}
	paths.sort();
	return paths;
}

function decompile(
	path: string,
	verbose: boolean,
	cfgReducer: 'recursive',
) {
	const originalLog = console.log;
	if (!verbose) {
		console.log = () => {};
	}

	const file = HBCFile.fromFile(path);
	try {
		return liftFile(file, { cfgReducer: { mode: cfgReducer } });
	} finally {
		console.log = originalLog;
	}
}

class GeneratedOutputValidationError extends Error {
	constructor(path: string, issues: GeneratedOutputIssue[]) {
		super(
			`generated output validation failed for ${path}:\n` +
				issues.map((issue) => `  ${formatGeneratedOutputIssue(issue)}`)
					.join('\n'),
		);
		this.name = 'GeneratedOutputValidationError';
	}
}

const options = parseArgs(Deno.args);
const paths = options.paths.length > 0
	? options.paths
	: await defaultSamplePaths(options.samplesDir);

if (paths.length === 0) {
	console.error(`No .hbc samples found in ${options.samplesDir}`);
	Deno.exit(1);
}

const failures: Array<{ path: string; error: unknown }> = [];
for (const path of paths) {
	try {
		const code = decompile(path, options.verbose, options.cfgReducer);
		const issues = validateGeneratedOutput(code);
		if (issues.length > 0) {
			throw new GeneratedOutputValidationError(path, issues);
		}
		console.error(`ok ${path}`);
	} catch (error) {
		failures.push({ path, error });
		console.error(`not ok ${path}`);
		if (error instanceof Error) {
			console.error(error.stack ?? error.message);
		} else {
			console.error(error);
		}
	}
}

console.error(
	`passed decompilation and generated-output validation for ${
		paths.length - failures.length
	}/${paths.length} samples`,
);

if (failures.length > 0) {
	Deno.exit(1);
}
