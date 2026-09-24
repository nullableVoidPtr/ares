export {};

type Options = {
	samplesDir: string;
	paths: string[];
	verbose: boolean;
	failFast: boolean;
	json: boolean;
	recursiveJs: boolean;
	categorize: boolean;
};

type OutputAudit = {
	residualIntrinsics: Record<string, number>;
};

type SampleResult = {
	path: string;
	ok: boolean;
	recursiveJsOk: boolean;
	misses: string[];
	stdout: string;
	stderr: string;
	code: number;
	audit?: OutputAudit;
};

function parseArgs(args: string[]): Options {
	let samplesDir = 'samples';
	let verbose = false;
	let failFast = false;
	let json = false;
	let recursiveJs = false;
	let categorize = false;
	const paths: string[] = [];

	for (let i = 0; i < args.length; i++) {
		const arg = args[i];
		if (arg === '--verbose' || arg === '-v') {
			verbose = true;
			continue;
		}
		if (arg === '--fail-fast') {
			failFast = true;
			continue;
		}
		if (arg === '--json') {
			json = true;
			continue;
		}
		if (arg === '--recursive-js') {
			recursiveJs = true;
			continue;
		}
		if (arg === '--require-output-match') {
			// Retained as a no-op for old task invocations. There is no legacy output
			// to compare after recursive CFG became the only reducer.
			continue;
		}
		if (arg === '--categorize') {
			categorize = true;
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
		paths.push(arg);
	}

	return {
		samplesDir,
		paths,
		verbose,
		failFast,
		json,
		recursiveJs,
		categorize,
	};
}

async function defaultSamplePaths(samplesDir: string): Promise<string[]> {
	const paths: string[] = [];
	await collectSamples(samplesDir, paths);
	paths.sort();
	return paths;
}

async function collectSamples(dir: string, paths: string[]) {
	for await (const entry of Deno.readDir(dir)) {
		const path = `${dir}/${entry.name}`;
		if (entry.isDirectory) {
			await collectSamples(path, paths);
			continue;
		}
		if (entry.isFile && entry.name.endsWith('.hbc')) {
			paths.push(path);
		}
	}
}

async function runAres(path: string, extraArgs: string[]): Promise<{
	stdout: string;
	stderr: string;
	code: number;
	success: boolean;
}> {
	const command = new Deno.Command(Deno.execPath(), {
		args: [
			'run',
			'--allow-read',
			'--allow-env',
			'src/ares.ts',
			path,
			...extraArgs,
			'--no-progress',
		],
		stdout: 'piped',
		stderr: 'piped',
	});
	const output = await command.output();
	const decoder = new TextDecoder();
	return {
		stdout: decoder.decode(output.stdout),
		stderr: decoder.decode(output.stderr),
		code: output.code,
		success: output.success,
	};
}

async function auditSample(
	path: string,
	recursiveJs: boolean,
	categorize: boolean,
): Promise<SampleResult> {
	const output = await runAres(path, []);
	const recursive = recursiveJs
		? await runAres(path, ['--cfg-recursive-js'])
		: null;
	const recursiveJsOk = !recursive || parseRecursiveJsOk(recursive.stdout);
	const misses = recursive ? parseMisses(recursive.stdout) : [];
	const stdout = [output.stdout, recursive?.stdout ?? ''].filter(Boolean)
		.join('\n');
	const stderr = [output.stderr, recursive?.stderr ?? ''].filter(Boolean)
		.join('\n');
	return {
		path,
		ok: output.success && (recursive?.success ?? true) && recursiveJsOk &&
			misses.length === 0,
		recursiveJsOk,
		misses,
		stdout,
		stderr,
		code: output.code || recursive?.code || 0,
		audit: categorize
			? { residualIntrinsics: residualIntrinsics(output.stdout) }
			: undefined,
	};
}

function residualIntrinsics(code: string): Record<string, number> {
	const counts = new Map<string, number>();
	for (const match of code.matchAll(/%([A-Za-z][A-Za-z0-9]*)/g)) {
		counts.set(match[1], (counts.get(match[1]) ?? 0) + 1);
	}
	return Object.fromEntries(
		[...counts].toSorted(([left], [right]) => left.localeCompare(right)),
	);
}

function parseRecursiveJsOk(stdout: string): boolean {
	const match = stdout.match(
		/Recursive CFG emitted JS:\s+(\d+)\/(\d+) functions emitted without diagnostics/,
	);
	return !!match && match[1] === match[2];
}

function parseMisses(stdout: string): string[] {
	const misses = new Set<string>();
	for (const line of stdout.split('\n')) {
		const countMatch = line.match(/^\s*\d+\s+(.+)$/);
		if (countMatch) {
			misses.add(countMatch[1].trim());
			continue;
		}
		const functionMatch = line.match(/\bmisses=(.+)$/);
		if (functionMatch) {
			for (const miss of functionMatch[1].split(',')) {
				const trimmed = miss.trim();
				if (trimmed) misses.add(trimmed);
			}
		}
	}
	return [...misses].toSorted();
}

function summarize(results: SampleResult[]) {
	const failures = results.filter((result) => !result.ok);
	const recursiveJsFailureCount =
		results.filter((result) => !result.recursiveJsOk).length;
	const missCounts = new Map<string, number>();
	const intrinsicCounts = new Map<string, number>();
	for (const result of results) {
		for (const miss of result.misses) {
			missCounts.set(miss, (missCounts.get(miss) ?? 0) + 1);
		}
		if (result.audit) {
			for (
				const [name, count] of Object.entries(
					result.audit.residualIntrinsics,
				)
			) {
				intrinsicCounts.set(
					name,
					(intrinsicCounts.get(name) ?? 0) + count,
				);
			}
		}
	}
	return {
		total: results.length,
		ok: results.length - failures.length,
		failed: failures.length,
		recursiveJsFailureCount,
		misses: [...missCounts].toSorted((left, right) =>
			right[1] - left[1] || left[0].localeCompare(right[0])
		).map(([kind, count]) => ({ kind, count })),
		residualIntrinsics: Object.fromEntries([...intrinsicCounts].toSorted()),
		failures: failures.map((result) => ({
			path: result.path,
			code: result.code,
			recursiveJsOk: result.recursiveJsOk,
			misses: result.misses,
		})),
	};
}

function printHumanResult(result: SampleResult, verbose: boolean) {
	const status = result.ok ? 'ok' : 'not ok';
	const missText = result.misses.length === 0
		? ''
		: ` misses=${result.misses.join(',')}`;
	const recursiveText = result.recursiveJsOk ? '' : ' recursive-js-failed';
	console.error(`${status} ${result.path}${recursiveText}${missText}`);
	if (!result.ok || verbose) {
		if (result.stdout.trim()) console.error(result.stdout.trimEnd());
		if (result.stderr.trim()) console.error(result.stderr.trimEnd());
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

const results: SampleResult[] = [];
for (const path of paths) {
	const result = await auditSample(
		path,
		options.recursiveJs,
		options.categorize,
	);
	results.push(result);
	if (!options.json) printHumanResult(result, options.verbose);
	if (!result.ok && options.failFast) break;
}

const summary = summarize(results);
if (options.json) {
	await Deno.stdout.write(new TextEncoder().encode(
		JSON.stringify(
			{
				summary,
				results: results.map((result) =>
					jsonResult(result, options.verbose)
				),
			},
			null,
			2,
		) + '\n',
	));
} else {
	console.error(
		`audited ${summary.ok}/${summary.total} samples successfully`,
	);
	if (summary.misses.length > 0) {
		console.error('recursive miss counts:');
		for (const miss of summary.misses) {
			console.error(
				`  ${String(miss.count).padStart(4)} ${miss.kind}`,
			);
		}
	}
	if (options.categorize) {
		console.error('recursive residual intrinsics:');
		for (
			const [name, count] of Object.entries(summary.residualIntrinsics)
		) {
			console.error(`  ${String(count).padStart(4)} %${name}`);
		}
	}
}

if (summary.failed > 0) {
	Deno.exitCode = 1;
}

function jsonResult(result: SampleResult, includeOutput: boolean) {
	const base = {
		path: result.path,
		ok: result.ok,
		code: result.code,
		recursiveJsOk: result.recursiveJsOk,
		misses: result.misses,
		audit: result.audit,
	};
	if (!includeOutput) return base;
	return {
		...base,
		stdout: result.stdout,
		stderr: result.stderr,
	};
}
