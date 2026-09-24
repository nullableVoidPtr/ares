type ExpectationKind = 'region' | 'js' | 'output';

type Expectation = {
	name: string;
	kind: ExpectationKind;
	patterns: RegExp[];
};

type SampleExpectation = {
	sample: string;
	versions?: string[];
	expectations: Expectation[];
};

type Options = {
	paths: string[];
	json: boolean;
	verbose: boolean;
	failFast: boolean;
};

type ExpectationResult = {
	sample: string;
	ok: boolean;
	failures: string[];
	regionCode: string;
	jsCode: string;
	outputCode: string;
};

const DEFAULT_EXPECTATIONS: SampleExpectation[] = [
	{
		sample: 'for.hbc',
		expectations: [
			{
				name: 'Region IR recovers for-in syntax',
				kind: 'region',
				patterns: [/loop id=\d+ syntax=forIn/],
			},
			{
				name: 'Region IR recovers for-of syntax',
				kind: 'region',
				patterns: [/loop id=\d+ syntax=forOf/],
			},
			{
				name: 'recursive JS emits for-in',
				kind: 'js',
				patterns: [/for \(const [^)]+ in [^)]+\)/],
			},
			{
				name: 'recursive JS emits for-of',
				kind: 'js',
				patterns: [/for \(const [^)]+ of [^)]+\)/],
			},
		],
	},
	{
		sample: 'forOf.hbc',
		expectations: [
			{
				name: 'recursive JS emits for-of loops',
				kind: 'js',
				patterns: [/for \(const [^)]+ of [^)]+\)/],
			},
			{
				name: 'function 3 keeps break',
				kind: 'js',
				patterns: [
					/\/\/ function #3[\s\S]*?for \(const [^)]+ of [^)]+\)[\s\S]*?\bbreak;/,
				],
			},
			{
				name: 'function 4 keeps continue',
				kind: 'js',
				patterns: [
					/\/\/ function #4[\s\S]*?for \(const [^)]+ of [^)]+\)[\s\S]*?\bcontinue;/,
				],
			},
			{
				name: 'recursive JS omits lowered IteratorClose in for-of',
				kind: 'js',
				patterns: [/^(?![\s\S]*%IteratorClose\()/],
			},
			{
				name: 'recursive JS omits try-exit labels in for-of',
				kind: 'js',
				patterns: [/^(?![\s\S]*try_exit_)/],
			},
			{
				name: 'function 2 recovers postfix index update',
				kind: 'js',
				patterns: [
					/\/\/ function #2[\s\S]*?for \(const [^)]+ of [^)]+\)[\s\S]*?\[[^\]]+\+\+\]/,
				],
			},
		],
	},
	{
		sample: 'tryCatch.test.hbc',
		versions: ['v96'],
		expectations: [
			{
				name: 'recursive JS emits outer finalizer body',
				kind: 'js',
				patterns: [/"outer\.finally\.finally"/],
			},
			{
				name: 'recursive JS emits nested finalizer body',
				kind: 'js',
				patterns: [/"inner1\.finally\.finally"/],
			},
			{
				name: 'recursive JS emits catch',
				kind: 'js',
				patterns: [/\bcatch \([^)]+\)/],
			},
			{
				name: 'recursive JS emits finally',
				kind: 'js',
				patterns: [/\bfinally \{/],
			},
			{
				name: 'recursive JS keeps initial yield outside outer try',
				kind: 'js',
				patterns: [
					/\/\/ function #2[\s\S]*?\n(?:const [^=]+ = )?yield [^;]+;[\s\S]{0,120}?\ntry \{[\s\S]*?\n\s*(?:const [^=]+ = )?yield [^;]+;/,
				],
			},
			{
				name: 'recursive JS omits copied finalizer return flood',
				kind: 'js',
				patterns: [/^(?![\s\S]*return r4_33[\s\S]*return r4_54)/],
			},
			{
				name: 'recursive JS omits copied outer finally in inner0 catch',
				kind: 'js',
				patterns: [
					/^(?![\s\S]*console\.log\("inner0\.catch"\);\n\s*console\.log\("outer\.finally"\))/,
				],
			},
			{
				name: 'recursive JS omits copied outer finally in outer catch',
				kind: 'js',
				patterns: [
					/^(?![\s\S]*console\.log\("outer\.catch\.catch"\);\n\s*console\.log\("outer\.finally"\))/,
				],
			},
			{
				name: 'recursive JS omits duplicate outer finalizer terminal',
				kind: 'output',
				patterns: [/^(?![\s\S]*return 22;\n\s*return 22;)/],
			},
		],
	},
	{
		sample: 'tryCatch.test.annotated.hbc',
		versions: ['v99'],
		expectations: [
			{
				name: 'Region IR recovers lowered generator loop',
				kind: 'region',
				patterns: [/loop id=\d+/],
			},
			{
				name: 'recursive JS preserves lowered generator creation',
				kind: 'js',
				patterns: [/%CreateGenerator\(/],
			},
			{
				name: 'recursive JS emits generator polling loop',
				kind: 'js',
				patterns: [/\bwhile \(true\) \{/],
			},
		],
	},
	{
		sample: 'tryCatch.test.hbc',
		versions: ['v99'],
		expectations: [
			{
				name: 'recursive JS keeps initial yield outside outer try',
				kind: 'js',
				patterns: [
					/\/\/ function #2[\s\S]*?\nyield 0;\ntry \{[\s\S]*?\n\s*yield 1;/,
				],
			},
			{
				name: 'recursive JS emits outer finalizer body',
				kind: 'js',
				patterns: [/console\.log\("outer\.finally\.finally"\)/],
			},
		],
	},
	{
		sample: 'tryFinally.hbc',
		expectations: [
			{
				name: 'Region IR recovers try/finally',
				kind: 'region',
				patterns: [/tryFinally handler=/],
			},
			{
				name: 'recursive JS emits finally',
				kind: 'js',
				patterns: [/\bfinally \{/],
			},
		],
	},
	{
		sample: 'simplyTryFinally.hbc',
		expectations: [
			{
				name: 'recursive JS preserves finalizer return values',
				kind: 'js',
				patterns: [
					/"return1"[\s\S]*?return 1;/,
					/"return2"[\s\S]*?return 2;/,
				],
			},
			{
				name: 'recursive JS does not append a duplicate bare return',
				kind: 'js',
				patterns: [
					/^(?![\s\S]*"return1"[\s\S]*?return 1;\n\s*return;)/,
				],
			},
		],
	},
	{
		sample: 'labelledLoopFinally.hbc',
		versions: ['v99'],
		expectations: [
			{
				name: 'Region IR recovers for-of loop syntax',
				kind: 'region',
				patterns: [/loop id=\d+ syntax=forOf/],
			},
			{
				name: 'Region IR recovers labelled nested loop break',
				kind: 'region',
				patterns: [/labelledBreak:loop_\d+/],
			},
			{
				name: 'Region IR structures loop-contained try/finally',
				kind: 'region',
				patterns: [
					/function #3[\s\S]*?loop id=\d+[\s\S]*?body[\s\S]*?tryFinally handler=/,
				],
			},
			{
				name: 'Region IR defers nonterminal protected exits',
				kind: 'region',
				patterns: [/deferredExit loopExit target=0x[0-9a-f]+/],
			},
			{
				name: 'Region IR recovers standalone try/finally',
				kind: 'region',
				patterns: [/tryFinally handler=/],
			},
			{
				name: 'recursive JS emits for-of loop',
				kind: 'js',
				patterns: [/for \(const [^)]+ of [^)]+\)/],
			},
			{
				name: 'recursive JS emits labelled loops',
				kind: 'js',
				patterns: [/loop_\d+: while \(true\)/],
			},
			{
				name: 'recursive JS normalizes labelled try/finally exits',
				kind: 'js',
				patterns: [
					/function #3[\s\S]*?try \{[\s\S]*?continue;[\s\S]*?\} finally \{/,
				],
			},
			{
				name: 'recursive JS preserves branch-exit intent',
				kind: 'js',
				patterns: [
					/function #3[\s\S]*?for \(; r5_2 < (?:r0_1|3); r5_2 = r5_2 \+ (?:r2_1|1)\)/,
					/function #3[\s\S]*?try \{[\s\S]*?continue;[\s\S]*?\} finally \{/,
					/^(?![\s\S]*function #3[\s\S]*?try_exit_)/,
				],
			},
			{
				name: 'recursive JS emits finally',
				kind: 'js',
				patterns: [/\bfinally \{/],
			},
		],
	},
	{
		sample: 'generator.hbc',
		versions: ['v96'],
		expectations: [
			{
				name: 'recursive JS emits yield',
				kind: 'js',
				patterns: [/\byield\b/],
			},
			{
				// Every generator loop in this sample is a `yield*` machine or a
				// recovered for-in, so a surviving raw loop Region means one of
				// them was not recognized.
				name: 'Region IR recovers generator delegate machines',
				kind: 'region',
				patterns: [/delegateYield completion=/, /^(?![\s\S]*loop id=)/],
			},
			{
				name: 'Region IR recovers generator finalizers',
				kind: 'region',
				patterns: [/tryFinally handler=/],
			},
			{
				name: 'recursive JS keeps for-in generator loop reachable',
				kind: 'js',
				patterns: [
					/\/\/ function #36[\s\S]*?for \(const [^)]+ in [^)]+\)/,
					/^(?![\s\S]*\/\/ function #36(?:(?!\/\/ function #37)[\s\S])*r8_1 === undefined)/,
				],
			},
			{
				name: 'recursive JS recovers simple delegated yield',
				kind: 'js',
				patterns: [
					/\/\/ function #17[\s\S]*?yield\* \[1, 2, 3\];[\s\S]*?\/\/ function #18/,
				],
			},
			{
				name: 'recursive JS recovers long-jump delegated yield',
				kind: 'js',
				patterns: [
					/\/\/ function #34[\s\S]*?yield\* \[1\];[\s\S]*?\/\/ function #35/,
				],
			},
			{
				name:
					'materialized generator output lowers iterator parameters',
				kind: 'output',
				patterns: [
					/function\* f\(\[[^\]]+\]\)/,
					/^(?![\s\S]*%(?:IteratorBegin|IteratorNext|IteratorClose)\()/,
				],
			},
			{
				name:
					'materialized generator output composes delegated generator wrappers',
				kind: 'output',
				patterns: [
					/function\* simpleDelegate\(\) \{[\s\S]*?yield\* \[1, 2, 3\];/,
					/function\* tryCatchDelegate\(\) \{[\s\S]*?print\("out of the try", yield\*/,
					/^(?![\s\S]*%CreateGenerator\()/,
				],
			},
			{
				name:
					'recursive JS recovers delegated yield from a stable local object',
				kind: 'js',
				patterns: [
					/\/\/ function #27[\s\S]*?yield\* (?:r2_1|\{[\s\S]*?\[Symbol\.iterator\])[\s\S]*?\/\/ function #28/,
				],
			},
		],
	},
	{
		sample: 'deeplyNestedFinally.hbc',
		expectations: [
			{
				name:
					'recursive JS emits every nested catch and finalizer body',
				kind: 'js',
				patterns: [
					/"inner1\.inner\.finally"/,
					/"inner1\.catch\.finally"/,
					/"inner1\.finally\.try"/,
					/"outer\.catch\.catch"/,
					/"outer\.catch\.finally"/,
					/"outer\.finally\.catch"/,
				],
			},
			{
				name: 'recursive output emits nested finalizer markers once',
				kind: 'output',
				patterns: [
					/^(?![\s\S]*"inner1\.finally\.finally"[\s\S]*"inner1\.finally\.finally")(?![\s\S]*"outer\.finally"[\s\S]*"outer\.finally")/,
				],
			},
			{
				name: 'recursive JS nests catch and finally syntax',
				kind: 'js',
				patterns: [/\bcatch \([^)]+\)/, /\bfinally \{/],
			},
			{
				name: 'recursive JS records no unresolved exception handler',
				kind: 'js',
				patterns: [/^(?![\s\S]*\/\/ misses:)/],
			},
		],
	},
	{
		sample: 'while-finally-nested.hbc',
		expectations: [
			{
				name: 'recursive JS emits the looping finalizer',
				kind: 'js',
				patterns: [
					/try \{[\s\S]*?\} finally \{[\s\S]*?while \(true\) \{[\s\S]*?\.push\(/,
				],
			},
			{
				name:
					'recursive JS preserves the zero-iteration finalizer guard',
				kind: 'js',
				patterns: [
					/if \([^)]*\.length < 10\) \{[\s\S]*?while \(true\)/,
				],
			},
			{
				name: 'recursive JS removes landing-pad throw mechanics',
				kind: 'js',
				patterns: [/^(?![\s\S]*%Catch\()/, /^(?![\s\S]*throw r0_3)/],
			},
		],
	},
	{
		sample: 'generator.hbc',
		versions: ['v99'],
		expectations: [
			{
				name: 'recursive JS preserves lowered generator creation',
				kind: 'js',
				patterns: [/%CreateGenerator\(/],
			},
			{
				name: 'Region IR recovers available exception structure',
				kind: 'region',
				patterns: [/tryCatch handler=/],
			},
			{
				name: 'materialized generator output lowers for-in intrinsics',
				kind: 'output',
				patterns: [
					/function\* testForIn\([^)]*\) \{\s*for \(const [^)]+ in [^)]+\)/,
					/^(?![\s\S]*%(?:GetPNameList|GetNextPName)\()/,
				],
			},
		],
	},
	{
		sample: 'async.hbc',
		versions: ['v96'],
		expectations: [{
			name: 'materialized async output hoists destructured parameter',
			kind: 'output',
			patterns: [
				/async function nonSimpleArrayDestructuring\(\[[^\]]+\]\)/,
				/^(?![\s\S]*%(?:IteratorBegin|IteratorNext|IteratorClose)\()/,
			],
		}],
	},
	{
		sample: 'destructuring-init.hbc',
		versions: ['v96'],
		expectations: [{
			name: 'materialized root output lowers iterator destructuring',
			kind: 'output',
			patterns: [
				/abc: def = function def\(\) \{\}/,
				/\[foo = function foo\(\) \{\}, bar = function bar\(\) \{\}\] = \[\];/,
				/\[undefined\]: x = 1,\s+\.\.\.x/,
				/\[null\]: y = 1,\s+\.\.\.y/,
				/^(?![\s\S]*%(?:IteratorBegin|IteratorNext|IteratorClose)\()/,
				/^(?![\s\S]*HermesInternal\.copyDataProperties\()/,
				/^(?![\s\S]*\breturn print\(typeof y\))/,
			],
		}],
	},
	{
		sample: 'delegateYield.hbc',
		versions: ['v96'],
		expectations: [
			{
				name: 'recursive JS reconstructs delegated yield',
				kind: 'js',
				patterns: [/yield\* /],
			},
			{
				name: 'Region IR recovers delegated-yield region',
				kind: 'region',
				patterns: [/delegateYield/],
			},
		],
	},
	{
		sample: 'delegateYield.hbc',
		versions: ['v99'],
		expectations: [
			{
				name: 'recursive JS preserves lowered generator creation',
				kind: 'js',
				patterns: [/%CreateGenerator\(/],
			},
		],
	},
	{
		sample: 'async-generator-for-await.hbc',
		versions: ['v99'],
		expectations: [
			{
				name: 'recursive JS preserves async generator wrapper',
				kind: 'js',
				patterns: [/_wrapAsyncGenerator/],
			},
			{
				name: 'recursive JS preserves lowered generator creation',
				kind: 'js',
				patterns: [/%CreateGenerator\(/],
			},
			{
				name: 'Region IR recovers async wrapper apply branches',
				kind: 'region',
				patterns: [/if join=/],
			},
		],
	},
	{
		sample: 'switch.hbc',
		expectations: [
			{
				name: 'Region IR recovers switch',
				kind: 'region',
				patterns: [/\bswitch\b/],
			},
			{
				name: 'recursive JS emits switch',
				kind: 'js',
				patterns: [/\bswitch \(/],
			},
			{
				name: 'recursive JS emits compare-chain switch function 1',
				kind: 'js',
				patterns: [/\/\/ function #1[\s\S]*?\bswitch \(/],
			},
			{
				name: 'recursive JS emits compare-chain switch function 4',
				kind: 'js',
				patterns: [/\/\/ function #4[\s\S]*?\bswitch \(/],
			},
			{
				name: 'recursive JS guards the direct switch-entry phi',
				kind: 'js',
				patterns: [
					/\/\/ function #1[\s\S]*?case 3:[\s\S]*?= "fall";[\s\S]*?case 4:[\s\S]*?if \([^)]* === 4\) \{[\s\S]*?= "";[\s\S]*?"through"/,
				],
			},
		],
	},
	{
		sample: 'switch-2.hbc',
		expectations: [
			{
				name: 'Region IR recovers switch',
				kind: 'region',
				patterns: [/\bswitch\b/],
			},
			{
				name: 'recursive JS emits switch',
				kind: 'js',
				patterns: [/\bswitch \(/],
			},
		],
	},
];

function parseArgs(args: string[]): Options {
	let json = false;
	let verbose = false;
	let failFast = false;
	const paths: string[] = [];
	for (const arg of args) {
		if (arg === '--json') {
			json = true;
			continue;
		}
		if (arg === '--verbose' || arg === '-v') {
			verbose = true;
			continue;
		}
		if (arg === '--fail-fast') {
			failFast = true;
			continue;
		}
		paths.push(arg);
	}
	return { paths, json, verbose, failFast };
}

function defaultSamplePaths(): string[] {
	const paths: string[] = [];
	for (const version of ['v96', 'v99']) {
		for (const expectation of DEFAULT_EXPECTATIONS) {
			if (
				expectation.versions &&
				!expectation.versions.includes(version)
			) continue;
			const path = `samples/${version}/${expectation.sample}`;
			try {
				if (Deno.statSync(path).isFile) paths.push(path);
			} catch {
				// Not every source sample exists for every bytecode version.
			}
		}
	}
	return paths;
}

function expectationForPath(path: string): SampleExpectation | null {
	const name = path.split('/').at(-1);
	const version = path.split('/').find((part) => /^v\d+$/.test(part));
	return DEFAULT_EXPECTATIONS.find((expectation) =>
		expectation.sample === name &&
		(!expectation.versions || !version ||
			expectation.versions.includes(version))
	) ?? null;
}

async function runAres(
	path: string,
	mode: '--cfg-recursive-ast' | '--cfg-recursive-js' | 'output',
) {
	const modeArgs = mode === 'output' ? [] : [mode];
	const command = new Deno.Command(Deno.execPath(), {
		args: [
			'run',
			'--allow-read',
			'--allow-env',
			'src/ares.ts',
			path,
			...modeArgs,
			'--no-progress',
		],
		stdout: 'piped',
		stderr: 'piped',
	});
	const output = await command.output();
	const decoder = new TextDecoder();
	const stdout = decoder.decode(output.stdout);
	const stderr = decoder.decode(output.stderr);
	if (!output.success) {
		throw new Error(
			`${mode} failed for ${path} with code ${output.code}\n${stdout}${stderr}`,
		);
	}
	return stdout;
}

async function checkSample(path: string): Promise<ExpectationResult> {
	const expectation = expectationForPath(path);
	if (!expectation) {
		return {
			sample: path,
			ok: false,
			failures: ['no expectations registered for sample'],
			regionCode: '',
			jsCode: '',
			outputCode: '',
		};
	}
	const [regionCode, jsCode, outputCode] = await Promise.all([
		runAres(path, '--cfg-recursive-ast'),
		runAres(path, '--cfg-recursive-js'),
		runAres(path, 'output'),
	]);
	const failures: string[] = [];
	for (const check of expectation.expectations) {
		const haystack = check.kind === 'region'
			? regionCode
			: check.kind === 'output'
			? outputCode
			: jsCode;
		if (check.patterns.every((pattern) => pattern.test(haystack))) {
			continue;
		}
		failures.push(check.name);
	}
	return {
		sample: path,
		ok: failures.length === 0,
		failures,
		regionCode,
		jsCode,
		outputCode,
	};
}

function printResult(result: ExpectationResult, verbose: boolean) {
	const status = result.ok ? 'ok' : 'not ok';
	console.error(`${status} ${result.sample}`);
	for (const failure of result.failures) {
		console.error(`  missing: ${failure}`);
	}
	if (!result.ok || verbose) {
		if (result.regionCode.trim()) {
			console.error('  recursive region IR available');
		}
		if (result.jsCode.trim()) {
			console.error('  recursive JS available');
		}
		if (result.outputCode.trim()) {
			console.error('  recursive output available');
		}
	}
}

const options = parseArgs(Deno.args);
const paths = options.paths.length > 0 ? options.paths : defaultSamplePaths();
const results: ExpectationResult[] = [];
for (const path of paths) {
	const result = await checkSample(path);
	results.push(result);
	if (!options.json) printResult(result, options.verbose);
	if (!result.ok && options.failFast) break;
}

const failed = results.filter((result) => !result.ok);
const summary = {
	total: results.length,
	ok: results.length - failed.length,
	failed: failed.length,
	failures: failed.map((result) => ({
		sample: result.sample,
		failures: result.failures,
	})),
};

if (options.json) {
	console.log(JSON.stringify(
		{
			summary,
			results: results.map((result) => ({
				sample: result.sample,
				ok: result.ok,
				failures: result.failures,
			})),
		},
		null,
		2,
	));
} else {
	console.error(
		`checked ${summary.ok}/${summary.total} recursive CFG expectations`,
	);
}

if (failed.length > 0) Deno.exit(1);
