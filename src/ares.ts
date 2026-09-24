import { setProgressEnabled } from '../lib/utils/progress.ts';
import { readFileSync, writeFileSync } from 'node:fs';
import { HBCFile } from '../lib/parser/file.ts';
import { SSAFunction, type SSAInstruction } from '../lib/ssa.ts';
import { FunctionKind } from '../lib/hbc/disassembly/function.ts';
import { HermesBytecode } from '../lib/parser/wasm/hermes_bytecode_parser.js';
import { getVersionInfo } from '../lib/hbc/data/VersionInfo.ts';
import { RAW_OPERANDS } from '../lib/hbc/disassembly/instruction.ts';
import { DataReader } from '../lib/utils/DataReader.ts';
import type * as t from '@babel/types';
import type { LiftedAST } from '../lib/ir/ast/mod.ts';
import type { IRFunction } from '../lib/ir/function/mod.ts';
import type {
	HandlerGraphFinalizerEdgeAction,
	HandlerGraphRegionDescriptor,
	HandlerGraphRegionForestNode,
} from '../lib/ir/function/except/mod.ts';
import type {
	RecursiveCFGMigrationAudit,
	RecursiveCFGSelection,
} from '../lib/ir/function/cfg/recursiveSummary.ts';
import type {
	collectRecursiveCFGMigrationSummaries,
	collectRecursiveCFGMigrationSummariesParallel,
	LiftAnalysisResult,
	LiftedFunctionArtifact,
	liftFile,
	liftFileParallel,
	liftFileParallelWithAnalysis,
	liftFileWithAnalysis,
	liftFunctionsIncrementally,
	RecursiveCFGMigrationFunctionSummary,
} from '../lib/ir/lift.ts';

// ---------------------------------------------------------------------------
// Arg parsing
// ---------------------------------------------------------------------------

type Mode =
	| 'decompile'
	| 'list-functions'
	| 'disasm'
	| 'ssa'
	| 'blocks'
	| 'ir-json';
type FunctionRange = { start: number; end: number };
type CFGReducerCLI = 'recursive';
type CFGMigrationAuditCLI = false | 'observe' | 'strict';

interface Args {
	file: string;
	mode: Mode;
	functionRange: FunctionRange | null;
	composeSelected: boolean;
	output: string | null;
	metroModulesOutput: string | null;
	noProgress: boolean;
	debugFeatures: Set<string>;
	parallelLift: boolean;
	liftOnly: boolean;
	workers: number | null;
	spillDir: string | null;
	spillReuse: boolean;
	spillKeep: boolean;
	cfgReducer: CFGReducerCLI;
	cfgRecursiveAst: boolean;
	cfgRecursiveBabelAst: boolean;
	cfgRecursiveJs: boolean;
	cfgMigrationAudit: CFGMigrationAuditCLI;
	cfgMigrationAuditJSONL: boolean;
	cfgMigrationProtectedOnly: boolean;
}

const USAGE = `\
Usage: ares <bundle.hbc> [options]

Modes (default: decompile):
  --list-functions      Print a table of all functions
  --disasm              Raw bytecode disassembly (safe for unimplemented mnemonics)
  --ssa                 SSA basic blocks after register renaming
  --blocks              Basic block graph (addresses and successors)
  --ir-json             Dump unstructured lifted IR as JSON for manual CFG
                        reduction; includes exception handler metadata

Options:
  -f, --function <id>   Operate on a single function (e.g. 42)
  -f, --function <r>    Operate on a range (e.g. 10-20)
      --compose         Compose each selected function with the descendants it
                        owns, instead of emitting them standalone. Composition
                        is where environment resolution and slot placement run,
                        so this is what makes those visible for one subtree.
  -o, --output <file>   Write output to file instead of stdout
  --metro-modules <dir> Extract top-level Metro __d modules into this directory
  --lift-only           Emit standalone functions without whole-file composition
  --parallel-lift       Build per-function IR in worker threads (decompile only)
  --workers <n>         Worker count for --parallel-lift
  --spill-dir <dir>     Where --parallel-lift keeps its on-disk store
                        (default: $XDG_CACHE_HOME/ares/spill)
  --spill-reuse         Reuse a store matching this bundle and these options,
                        skipping lifting entirely, and keep it afterwards
  --spill-keep          Keep the store after the run without reusing one
  --cfg-reducer <mode>  recursive (accepted for compatibility; default)
  --cfg-recursive-ast   Print recursive CFG Region IR instead of JS
  --cfg-recursive-babel-ast
                        Print recursive CFG-emitted Babel AST JSON
  --cfg-recursive-js    Print recursive CFG-emitted JS snippets
  --cfg-migration-audit[=strict]
                        Normalize/validate the Region CFG and emit migration JSON;
                        strict records strict audit mode in the report
  --cfg-migration-audit=jsonl
                        Stream metadata/function/footer records as JSONL without
                        retaining all per-function audit entries
  --cfg-migration-protected-only
                        Audit only functions with exception handlers
  --no-progress         Suppress lifting and composition progress output
  --debug <feature>     Enable a debug feature; may be repeated
                        Features: lowered-generator, lowered-generator-model,
                                  dup-ssa, recursive-cfg
  -h, --help            Show this help
`;

function parseArgs(argv: string[]): Args {
	let file: string | null = null;
	let mode: Mode = 'decompile';
	let functionRange: FunctionRange | null = null;
	let composeSelected = false;
	let output: string | null = null;
	let metroModulesOutput: string | null = null;
	let noProgress = false;
	const debugFeatures = new Set<string>();
	let parallelLift = false;
	let liftOnly = false;
	let workers: number | null = null;
	let spillDir: string | null = null;
	let spillReuse = false;
	let spillKeep = false;
	let cfgReducer: CFGReducerCLI = 'recursive';
	let cfgRecursiveAst = false;
	let cfgRecursiveBabelAst = false;
	let cfgRecursiveJs = false;
	let cfgMigrationAudit: CFGMigrationAuditCLI = false;
	let cfgMigrationAuditJSONL = false;
	let cfgMigrationProtectedOnly = false;

	for (let i = 0; i < argv.length; i++) {
		const arg = argv[i];

		if (arg === '-h' || arg === '--help') {
			console.log(USAGE);
			Deno.exit(0);
		}

		if (arg === '--list-functions') {
			mode = 'list-functions';
			continue;
		}
		if (arg === '--disasm') {
			mode = 'disasm';
			continue;
		}
		if (arg === '--ssa') {
			mode = 'ssa';
			continue;
		}
		if (arg === '--blocks') {
			mode = 'blocks';
			continue;
		}
		if (arg === '--ir-json') {
			mode = 'ir-json';
			continue;
		}
		if (arg === '--no-progress') {
			noProgress = true;
			continue;
		}
		if (arg === '--parallel-lift') {
			parallelLift = true;
			continue;
		}
		if (arg === '--spill-reuse') {
			spillReuse = true;
			continue;
		}
		if (arg === '--spill-keep') {
			spillKeep = true;
			continue;
		}
		if (arg === '--spill-dir') {
			spillDir = argv[++i] ?? null;
			if (spillDir == null) die('--spill-dir requires a directory');
			continue;
		}
		if (arg === '--lift-only') {
			liftOnly = true;
			continue;
		}
		if (arg === '--cfg-recursive-ast') {
			cfgRecursiveAst = true;
			cfgReducer = 'recursive';
			continue;
		}
		if (arg === '--cfg-recursive-babel-ast') {
			cfgRecursiveBabelAst = true;
			cfgReducer = 'recursive';
			continue;
		}
		if (arg === '--cfg-recursive-js') {
			cfgRecursiveJs = true;
			cfgReducer = 'recursive';
			continue;
		}
		if (arg === '--cfg-migration-audit') {
			cfgMigrationAudit = 'observe';
			cfgReducer = 'recursive';
			continue;
		}
		if (arg.startsWith('--cfg-migration-audit=')) {
			const value = arg.slice('--cfg-migration-audit='.length);
			if (value === 'jsonl') {
				cfgMigrationAudit = 'observe';
				cfgMigrationAuditJSONL = true;
			} else {
				cfgMigrationAudit = parseCFGMigrationAudit(value);
			}
			cfgReducer = 'recursive';
			continue;
		}
		if (arg === '--cfg-migration-protected-only') {
			cfgMigrationProtectedOnly = true;
			continue;
		}

		if (arg === '--workers') {
			const val = argv[++i];
			if (!val) die('--workers requires a value');
			workers = parseWorkerCount(val);
			continue;
		}
		if (arg.startsWith('--workers=')) {
			workers = parseWorkerCount(arg.slice('--workers='.length));
			continue;
		}
		if (arg === '--cfg-reducer') {
			const val = argv[++i];
			if (!val) die('--cfg-reducer requires a value');
			cfgReducer = parseCFGReducer(val);
			continue;
		}
		if (arg.startsWith('--cfg-reducer=')) {
			cfgReducer = parseCFGReducer(arg.slice('--cfg-reducer='.length));
			continue;
		}

		if (arg === '-f' || arg === '--function') {
			const val = argv[++i];
			if (!val) die(`${arg} requires a value`);
			functionRange = parseFunctionRange(val);
			continue;
		}
		if (arg.startsWith('--function=') || arg.startsWith('-f=')) {
			functionRange = parseFunctionRange(arg.slice(arg.indexOf('=') + 1));
			continue;
		}

		if (arg === '--compose') {
			composeSelected = true;
			continue;
		}

		if (arg === '-o' || arg === '--output') {
			output = argv[++i];
			if (!output) die(`${arg} requires a path`);
			continue;
		}
		if (arg.startsWith('--output=') || arg.startsWith('-o=')) {
			output = arg.slice(arg.indexOf('=') + 1);
			continue;
		}

		if (arg === '--metro-modules') {
			metroModulesOutput = argv[++i];
			if (!metroModulesOutput) die('--metro-modules requires a path');
			continue;
		}
		if (arg.startsWith('--metro-modules=')) {
			metroModulesOutput = arg.slice(arg.indexOf('=') + 1);
			continue;
		}

		if (arg === '--debug') {
			const feat = argv[++i];
			if (!feat) die('--debug requires a feature name');
			debugFeatures.add(feat);
			continue;
		}
		if (arg.startsWith('--debug=')) {
			debugFeatures.add(arg.slice('--debug='.length));
			continue;
		}

		if (arg.startsWith('-')) die(`Unknown option: ${arg}`);
		if (file) die(`Unexpected argument: ${arg}`);
		file = arg;
	}

	if (!file) {
		console.log(USAGE);
		Deno.exit(1);
	}

	return {
		file,
		mode,
		functionRange,
		composeSelected,
		output,
		metroModulesOutput,
		noProgress,
		debugFeatures,
		parallelLift,
		spillDir,
		spillReuse,
		spillKeep,
		liftOnly,
		workers,
		cfgReducer,
		cfgRecursiveAst,
		cfgRecursiveBabelAst,
		cfgRecursiveJs,
		cfgMigrationAudit,
		cfgMigrationAuditJSONL,
		cfgMigrationProtectedOnly,
	};
}

function parseCFGMigrationAudit(value: string): Exclude<
	CFGMigrationAuditCLI,
	false
> {
	if (value === 'observe' || value === 'strict') return value;
	die(
		`Invalid CFG migration audit mode: ${value} ` +
			'(expected observe or strict)',
	);
}

function parseCFGReducer(value: string): CFGReducerCLI {
	if (value === 'recursive') return value;
	die(`Invalid CFG reducer: ${value} (expected recursive)`);
}

function parseFunctionRange(s: string): FunctionRange {
	const m = s.match(/^(\d+)(?:-(\d+))?$/);
	if (!m) die(`Invalid function range: ${s} (expected e.g. 42 or 10-20)`);
	const start = Number(m[1]);
	const end = m[2] != null ? Number(m[2]) : start;
	if (end < start) die(`Invalid range: ${start}-${end}`);
	return { start, end };
}

function die(msg: string): never {
	console.error(`ares: ${msg}`);
	Deno.exit(1);
	throw new Error(msg);
}

function parseWorkerCount(s: string): number {
	const value = Number(s);
	if (!Number.isInteger(value) || value < 1) {
		die(`Invalid worker count: ${s}`);
	}
	return value;
}

// ---------------------------------------------------------------------------
// Progress bar
// ---------------------------------------------------------------------------

const enc = new TextEncoder();

function writeStderr(s: string) {
	Deno.stderr.writeSync(enc.encode(s));
}

function renderBar(n: number, total: number, name: string) {
	const width = 36;
	const pct = total > 0 ? n / total : 0;
	const filled = Math.round(pct * width);
	const bar = '='.repeat(Math.max(0, filled - 1)) +
		(filled > 0 ? '>' : '') +
		' '.repeat(width - filled);
	const label = name ? ` ${name}`.slice(0, 20) : '';
	const pctStr = (pct * 100).toFixed(1).padStart(5);
	writeStderr(
		`\r[${bar}] ${
			String(n).padStart(String(total).length)
		}/${total} ${pctStr}%${label}\x1b[K`,
	);
}

function withProgress(
	total: number,
	noProgress: boolean,
	fn: () => void | Promise<void>,
): Promise<void> {
	if (noProgress) {
		// Silence progress where it is produced rather than by muting the
		// stream it happens to travel on: `console.error` also carries
		// diagnostics and every `--debug` feature's output, none of which this
		// flag is meant to touch.
		const previous = setProgressEnabled(false);
		return Promise.resolve(fn()).finally(() => {
			setProgressEnabled(previous);
		});
	}

	type ProgressState = {
		completed: Set<number>;
		current: number;
		total: number;
		/**
		 * Work already done before this run started.
		 *
		 * A resumed run only lifts what is outstanding, so counting just the
		 * functions it touches makes the bar open at zero and stop well short
		 * of the end -- on a bundle resumed at 95,344 of 127,282 it would never
		 * pass 25%.
		 */
		offset: number;
		lastName: string;
		lastRenderTime: number;
	};
	const liftProgress: ProgressState = {
		completed: new Set(),
		current: 0,
		total,
		offset: 0,
		lastName: '',
		lastRenderTime: 0,
	};
	let composeProgress: ProgressState | null = null;
	let activeProgress = liftProgress;
	let showingBar = false;
	const startTime = Date.now();
	const origErr = console.error;
	const redraw = () =>
		renderBar(
			activeProgress.current,
			activeProgress.total,
			activeProgress.lastName,
		);
	const finishActiveBar = () => {
		if (!showingBar) return;
		redraw();
		writeStderr('\n');
		showingBar = false;
	};
	const update = (
		progress: ProgressState,
		id: number,
		name: string,
		args: unknown[],
	) => {
		if (activeProgress !== progress) {
			finishActiveBar();
			activeProgress = progress;
		}
		progress.completed.add(id);
		progress.current = progress.completed.size + progress.offset;
		progress.lastName = name;
		const now = Date.now();
		if (
			now - startTime >= 5000 &&
			(now - progress.lastRenderTime >= 100 ||
				progress.current === progress.total)
		) {
			showingBar = true;
			progress.lastRenderTime = now;
			redraw();
		} else if (!showingBar) {
			origErr(...args);
		}
	};

	console.error = (...args: unknown[]) => {
		const msg = String(args[0] ?? '');
		// A resumed run announces how much the cold store already holds; seed
		// the bar with it so it continues from there rather than restarting.
		const resumeMatch = msg.match(
			/^\[lift\] resuming: (\d+) of (\d+) functions already in the cold store$/,
		);
		if (resumeMatch) {
			liftProgress.offset = Number(resumeMatch[1]);
			liftProgress.total = Number(resumeMatch[2]);
			liftProgress.current = liftProgress.offset;
			origErr(...args);
			return;
		}
		const liftMatch = msg.match(/^currently lifting function #(\d+)$/);
		if (liftMatch) {
			const functionId = Number(liftMatch[1]);
			update(liftProgress, functionId, `#${functionId}`, args);
			return;
		}
		const composeMatch = msg.match(
			/^currently composing module #(\d+) of (\d+)$/,
		);
		if (composeMatch) {
			const functionId = Number(composeMatch[1]);
			const composeTotal = Number(composeMatch[2]);
			if (!composeProgress || composeProgress.total !== composeTotal) {
				composeProgress = {
					completed: new Set(),
					current: 0,
					offset: 0,
					total: composeTotal,
					lastName: '',
					lastRenderTime: 0,
				};
			}
			update(
				composeProgress,
				functionId,
				`module #${functionId}`,
				args,
			);
		} else {
			// Preserve non-progress output; if bar is active, clear and redraw around it
			if (showingBar) writeStderr('\r\x1b[K');
			origErr(...args);
			if (showingBar) redraw();
		}
	};

	return Promise.resolve(fn()).finally(() => {
		console.error = origErr;
		finishActiveBar();
	});
}

// ---------------------------------------------------------------------------
// Output capture (for --output)
// ---------------------------------------------------------------------------

async function withOutputCapture(
	outputPath: string | null,
	fn: () => void | Promise<void>,
): Promise<void> {
	if (!outputPath) {
		await fn();
		return;
	}

	const lines: string[] = [];
	const origLog = console.log;
	console.log = (...args: unknown[]) =>
		lines.push(args.map(String).join(' '));
	try {
		await fn();
	} finally {
		console.log = origLog;
	}
	writeFileSync(outputPath, lines.join('\n') + '\n');
}

interface TextSink {
	write(text: string): void;
}

async function withStreamingOutput(
	outputPath: string | null,
	fn: (sink: TextSink) => void | Promise<void>,
): Promise<void> {
	const output = outputPath
		? Deno.openSync(outputPath, {
			create: true,
			truncate: true,
			write: true,
		})
		: Deno.stdout;
	const sink: TextSink = {
		write(text) {
			const bytes = enc.encode(text);
			let written = 0;
			while (written < bytes.length) {
				written += output.writeSync(bytes.subarray(written));
			}
		},
	};
	try {
		await fn(sink);
	} finally {
		if (outputPath) output.close();
	}
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const KIND_LABEL: Record<FunctionKind, string> = {
	[FunctionKind.NormalFunction]: 'func',
	[FunctionKind.GeneratorFunction]: 'gen ',
	[FunctionKind.AsyncFunction]: 'async',
};

function funcRange(file: HBCFile, range: FunctionRange | null) {
	const funcs = file.functions;
	if (!range) return funcs;
	return funcs.slice(range.start, range.end + 1);
}

function selectedFunctionIds(
	file: HBCFile,
	range: FunctionRange | null,
): number[] {
	if (!range) {
		return Array.from({ length: file.functions.length }, (_, id) => id);
	}
	if (
		range.start >= file.functions.length ||
		range.end >= file.functions.length
	) {
		die(
			`Function range ${range.start}-${range.end} is outside 0-${
				file.functions.length - 1
			}`,
		);
	}
	return Array.from(
		{ length: range.end - range.start + 1 },
		(_, offset) => range.start + offset,
	);
}

function hex(n: number, pad = 4) {
	return '0x' + n.toString(16).padStart(pad, '0');
}

function fmtRawOperand(val: unknown): string {
	if (typeof val !== 'object' || val === null) return String(val);
	const v = val as Record<string, unknown>;
	if (v.type === 'register') return `r${v.index}`;
	if (v.type === 'string') return `str#${v.stringTableIndex}`;
	if (v.type === 'function') return `func#${v.functionId}`;
	if (v.type === 'bigint') return `bigint#${v.bigintTableIndex}`;
	return JSON.stringify(val);
}

function fmtSSAReg(reg: { index: number; version: number }) {
	return `r${reg.index}_${reg.version}`;
}

function fmtSSAInstr(instr: SSAInstruction, file: HBCFile): string {
	if ('sources' in instr) {
		const srcs = [...instr.sources.entries()]
			.map(([addr, reg]) => `${hex(addr)}→${fmtSSAReg(reg)}`)
			.join(', ');
		return `  φ  ${fmtSSAReg(instr.destination)} = [${srcs}]`;
	}
	const destination = 'destination' in instr.defs
		? instr.defs.destination
		: undefined;
	const dst = destination ? `${fmtSSAReg(destination)} ← ` : '         ';
	const parts: string[] = [
		`  ${hex(instr.functionLocalOffset)}:  ${dst}${instr.instruction}`,
	];
	const source = 'source' in instr.uses ? instr.uses.source : undefined;
	if (source) parts.push(`src=${fmtSSAReg(source)}`);
	const left = 'left' in instr.uses ? instr.uses.left : undefined;
	if (left) parts.push(`l=${fmtSSAReg(left)}`);
	const right = 'right' in instr.uses ? instr.uses.right : undefined;
	if (right) parts.push(`r=${fmtSSAReg(right)}`);
	const environment = 'environment' in instr.uses
		? instr.uses.environment
		: undefined;
	if (environment) parts.push(`env=${fmtSSAReg(environment)}`);
	const value = 'value' in instr.uses ? instr.uses.value : undefined;
	if (value) {
		parts.push(`val=${fmtSSAReg(value)}`);
	} else if (
		'value' in instr && instr.value !== undefined &&
		typeof instr.value !== 'object'
	) {
		parts.push(`val=${JSON.stringify(instr.value)}`);
	}
	if ('slotIndex' in instr && instr.slotIndex !== undefined) {
		parts.push(`slot=${instr.slotIndex}`);
	}
	if ('levelIndex' in instr && instr.levelIndex !== undefined) {
		parts.push(`level=${instr.levelIndex}`);
	}
	if ('parameterIndex' in instr && instr.parameterIndex !== undefined) {
		parts.push(`param=${instr.parameterIndex}`);
	}
	if ('envSize' in instr && instr.envSize !== undefined) {
		parts.push(`envSize=${instr.envSize}`);
	}
	const argument = 'argument' in instr.uses ? instr.uses.argument : undefined;
	if (argument) parts.push(`arg=${fmtSSAReg(argument)}`);
	if ('function' in instr && instr.function !== undefined) {
		parts.push(`func=${JSON.stringify(instr.function)}`);
	}
	if (
		'stringTableIndex' in instr &&
		typeof instr.stringTableIndex === 'number'
	) {
		try {
			parts.push(
				`str=${JSON.stringify(file.getString(instr.stringTableIndex))}`,
			);
		} catch {}
	}
	return parts.join('  ');
}

// ---------------------------------------------------------------------------
// Modes
// ---------------------------------------------------------------------------

function doListFunctions(file: HBCFile, range: FunctionRange | null) {
	const funcs = funcRange(file, range);
	const idW = String(file.functions.length - 1).length;
	console.log(
		'id'.padEnd(idW) + '  kind   params  envSize  name',
	);
	console.log('-'.repeat(idW + 40));
	for (const f of funcs) {
		const id = String(f.id).padStart(idW);
		const kind = KIND_LABEL[f.functionKind] ?? '?    ';
		const params = String(f.paramCount).padStart(6);
		const env = String(f.envSize).padStart(7);
		const name = f.name ?? '<anonymous>';
		console.log(`${id}  ${kind}  ${params}  ${env}  ${name}`);
	}
}

function doDisasm(filePath: string, range: FunctionRange | null) {
	const data = readFileSync(filePath);
	const parsed = new HermesBytecode(data);
	const { opcodeMap, legacyOperands } = getVersionInfo(parsed.version);

	const start = range?.start ?? 0;
	const end = range?.end ?? (parsed.functions.length - 1);

	for (let funcId = start; funcId <= end; funcId++) {
		const func = parsed.functions[funcId];
		if (!func) {
			console.log(`Function ${funcId} not found`);
			continue;
		}

		const name = parsed.strings[func.functionNameID]?.value ??
			'<anonymous>';
		console.log(
			`\nFunction<${name}> #${funcId} (${func.paramCount} params, ${func.frameSize} regs):`,
		);

		const bytecode = func.bytecode;
		const io = new DataReader(bytecode);
		let instrIdx = 0;

		while (io.remaining) {
			const offset = io.pos;
			const opcode = io.UInt8();
			const mnemonic = opcodeMap[opcode];
			if (!mnemonic) {
				console.log(
					`  [${instrIdx}] ${hex(offset)}: UNKNOWN opcode ${
						hex(opcode, 2)
					}`,
				);
				break;
			}
			const spec = (legacyOperands as any)[mnemonic] ??
				(RAW_OPERANDS as any)[mnemonic];
			if (!spec) {
				console.log(
					`  [${instrIdx}] ${
						hex(offset)
					}: ${mnemonic} (no operand spec)`,
				);
				break;
			}
			const operands: string[] = [];
			try {
				for (const reader of spec) {
					operands.push(fmtRawOperand(reader(io)));
				}
			} catch (e) {
				console.log(
					`  [${instrIdx}] ${hex(offset)}: ${mnemonic} ERROR: ${e}`,
				);
				break;
			}
			console.log(
				`  [${instrIdx}] ${hex(offset)}: ${mnemonic}${
					operands.length ? '  ' + operands.join(', ') : ''
				}`,
			);
			instrIdx++;
		}
	}
}

function doSSA(file: HBCFile, range: FunctionRange | null) {
	for (const f of funcRange(file, range)) {
		const name = f.name ?? '<anonymous>';
		const kindLabel = KIND_LABEL[f.functionKind] ?? '?';
		console.log(
			`\n=== Function #${f.id} (${name}) ${kindLabel}, ${f.paramCount} params, envSize=${f.envSize} ===`,
		);
		if (f.exceptionHandlers.length) {
			console.log(`  handlers: ${JSON.stringify(f.exceptionHandlers)}`);
		}

		const ssa = new SSAFunction(f);
		for (const [addr, block] of ssa.basicBlocks) {
			const succs = block.consequentAddresses.map(hex).join(', ');
			console.log(`\n  BLOCK ${hex(addr)}  →  [${succs}]`);
			for (const instr of block.ssaInstructions) {
				console.log(fmtSSAInstr(instr, file));
			}
		}
	}
}

function doBlocks(file: HBCFile, range: FunctionRange | null) {
	for (const f of funcRange(file, range)) {
		const name = f.name ?? '<anonymous>';
		console.log(
			`\n=== Function #${f.id} (${name}) ${
				KIND_LABEL[f.functionKind] ?? '?'
			}, ${f.paramCount} params ===`,
		);
		if (f.exceptionHandlers.length) {
			console.log(`  handlers: ${JSON.stringify(f.exceptionHandlers)}`);
		}
		for (const [addr, block] of f.basicBlocks) {
			const succs = block.consequentAddresses.map(hex).join(', ');
			const last = (block.instructions.at(-1) as any)?.instruction ?? '?';
			console.log(`  ${hex(addr)}  last=${last}  →  [${succs}]`);
		}
	}
}

type CodeGenerator = (node: t.Node) => { code: string };

function sortedAddresses(values: Iterable<number> | null | undefined) {
	return values == null ? null : [...values].toSorted((a, b) => a - b);
}

function generatedCode(
	generateCode: CodeGenerator,
	node: t.Node | LiftedAST<t.Node>,
): string {
	return generateCode(node as t.Node).code;
}

function serializeSSARegister(value: unknown): unknown {
	if (
		typeof value === 'object' && value !== null &&
		'index' in value && 'version' in value
	) {
		const register = value as { index: number; version: number };
		return {
			index: register.index,
			version: register.version,
			name: fmtSSAReg(register),
		};
	}
	return value;
}

function serializeLiftedExtra(extra: LiftedAST<t.Node>['extra']) {
	if (!extra) return null;
	const out: Record<string, unknown> = {};
	const scalarKeys = [
		'parentFunctionId',
		'address',
		'instruction',
		'isBuiltin',
		'isNonVolatile',
		'isDeclaredGlobal',
		'isReferencedGlobal',
		'isHomeObject',
		'isLocalEnvironment',
		'isPotentialConditionalValue',
		'preserveAcrossBlocks',
		'bindingOwnerFunctionId',
		'recoveredEnvironmentSSA',
		'recoveredEnvironmentLocal',
		'loweredGeneratorResumeValue',
		'consumed',
	] as const;
	for (const key of scalarKeys) {
		if (extra[key] !== undefined) out[key] = extra[key];
	}
	if (extra.sourceRegister) {
		out.sourceRegister = serializeSSARegister(extra.sourceRegister);
	}
	if (extra.memberReadDestination) {
		out.memberReadDestination = serializeSSARegister(
			extra.memberReadDestination,
		);
	}
	if (extra.recoveredEnvironmentSlot) {
		out.recoveredEnvironmentSlot = { ...extra.recoveredEnvironmentSlot };
	}
	if (extra.liftedPhiSources) {
		out.liftedPhiSources = extra.liftedPhiSources.slice();
	}
	if (extra.recoveredIteratorNames) {
		out.recoveredIteratorNames = extra.recoveredIteratorNames.slice();
	}
	if (extra.recoveredAsyncIteratorNames) {
		out.recoveredAsyncIteratorNames = extra.recoveredAsyncIteratorNames
			.slice();
	}
	if (extra.objectShapeKeys) {
		out.objectShapeKeys = extra.objectShapeKeys.slice();
	}
	if (extra.ref) out.ref = { ...extra.ref };
	if (extra.storageLocation) out.storageLocation = extra.storageLocation;
	if (Object.keys(out).length === 0) return null;
	return out;
}

function serializeLiftedNode(
	generateCode: CodeGenerator,
	node: LiftedAST<t.Node>,
) {
	const extra = serializeLiftedExtra(node.extra);
	return {
		code: generatedCode(generateCode, node),
		...(extra == null ? {} : { extra }),
	};
}

function serializeHandlerDescriptor(
	generateCode: CodeGenerator,
	descriptor: HandlerGraphRegionDescriptor,
) {
	return {
		handler: descriptor.handler,
		kind: descriptor.kind,
		protectedBlocks: sortedAddresses(descriptor.protectedBlocks),
		protectedEntries: sortedAddresses(descriptor.protectedEntries),
		catchBody: sortedAddresses(descriptor.catchBody),
		canonicalFinallyAddress: descriptor.canonicalFinallyAddress,
		canonicalFinallyOwnership: descriptor.canonicalFinallyOwnership == null
			? null
			: {
				finallyAddress:
					descriptor.canonicalFinallyOwnership.finallyAddress,
				protectsCatch:
					descriptor.canonicalFinallyOwnership.protectsCatch,
				missingProtectedBlocks: sortedAddresses(
					descriptor.canonicalFinallyOwnership.missingProtectedBlocks,
				),
				valid: descriptor.canonicalFinallyOwnership.valid,
			},
		finallyCopyRoots: sortedAddresses(descriptor.finallyCopyRoots),
		finallyBodyBlocks: descriptor.finallyBodyBlocks,
		finallyCopies: descriptor.finallyCopies.map((copy) => ({
			...copy,
			skipRanges: copy.skipRanges?.map((range) => ({ ...range })),
		})),
		finallyCopySuffixes: descriptor.finallyCopySuffixes.map((suffix) => ({
			canonical: suffix.canonical,
			copyRoot: suffix.copyRoot,
			ownerBlock: suffix.ownerBlock,
			next: suffix.next,
			kind: suffix.kind,
			statements: suffix.statements.map((stmt) =>
				generatedCode(generateCode, stmt)
			),
			skipRanges: suffix.skipRanges?.map((range) => ({ ...range })),
		})),
		enclosingFinallyCopyRoots: descriptor.enclosingFinallyCopyRoots.map((
			copy,
		) => ({ ...copy })),
	};
}

function serializeFinalizerEdgeAction(
	generateCode: CodeGenerator,
	action: HandlerGraphFinalizerEdgeAction,
) {
	return {
		handler: action.handler,
		edge: { ...action.edge },
		canonical: action.canonical,
		copyRoot: action.copyRoot,
		ownerBlock: action.ownerBlock,
		next: action.next,
		kind: action.kind,
		completion: action.completion,
		statements: action.statements.map((stmt) =>
			generatedCode(generateCode, stmt)
		),
		skipRanges: action.skipRanges.map((range) => ({ ...range })),
		depth: action.depth,
	};
}

function serializeHandlerForest(func: IRFunction) {
	const forest = func.exceptions.structuredRegionForest();
	const node = (item: HandlerGraphRegionForestNode): unknown => ({
		handler: item.descriptor.handler,
		children: item.children.map(node),
	});
	return {
		roots: forest.roots.map(node),
		parentByHandler: [...forest.parentByHandler]
			.toSorted((a, b) => a[0] - b[0])
			.map(([handler, parent]) => ({ handler, parent })),
	};
}

function serializeIRFunction(
	file: HBCFile,
	func: IRFunction,
	generateCode: CodeGenerator,
) {
	const bytecodeFunction = file.functions[func.id];
	const descriptors = func.exceptions.structuredRegionDescriptors();
	return {
		functionId: func.id,
		name: bytecodeFunction.name ?? null,
		functionKind: bytecodeFunction.functionKind,
		functionKindLabel: KIND_LABEL[bytecodeFunction.functionKind] ?? null,
		paramCount: bytecodeFunction.paramCount,
		frameSize: bytecodeFunction.frameSize,
		environmentSize: bytecodeFunction.envSize,
		flags: {
			isGenerator: func.isGenerator,
			isNativeGenerator: func.isNativeGenerator,
			isLoweredGenerator: func.isLoweredGenerator,
			isAsync: func.isAsync,
		},
		params: func.params.map((param) => generatedCode(generateCode, param)),
		referencedFunctions: [...func.referencedFunctionIds]
			.toSorted((a, b) => a[0] - b[0])
			.map(([functionId, count]) => ({ functionId, count })),
		bytecodeExceptionHandlers: func._exceptionHandlers.map((handler) => ({
			...handler,
		})),
		exceptionHandlers: {
			snapshot: func.exceptions.snapshot(),
			descriptors: descriptors.map((descriptor) =>
				serializeHandlerDescriptor(generateCode, descriptor)
			),
			forest: serializeHandlerForest(func),
			finalizerEdgeActions: func.exceptions.finalizerEdgeActions().map((
				action,
			) => serializeFinalizerEdgeAction(generateCode, action)),
		},
		blocks: [...func.blocks]
			.toSorted((a, b) => a[0] - b[0])
			.map(([address, block]) => ({
				address,
				label: hex(address),
				kind: block.kind ?? 'normal',
				terminalKind: block.terminalKind ?? null,
				consequentAddresses: block.consequentAddresses.slice(),
				cfgPredecessors: sortedAddresses(
					func.cfgPredecessorsOf(address),
				),
				predecessors: sortedAddresses(func.predecessorsOf(address)),
				activeHandlers: sortedAddresses(
					func.exceptions.activeHandlersAtBlock(address),
				),
				protectedBy: block.protectedBy ?? null,
				handlerFor: sortedAddresses(block.handlerFor),
				sourceAddresses: sortedAddresses(block.sourceAddresses),
				syntheticReason: block.syntheticReason ?? null,
				generatorState: block.generatorState ?? null,
				activeHandlerState: block.activeHandlerState ?? null,
				pairedFinallyState: block.pairedFinallyState ?? null,
				recoveredFinalizerOwner: block.recoveredFinalizerOwner ?? null,
				recoveredFinalizerRole: block.recoveredFinalizerRole ?? null,
				branch: block.branch == null
					? null
					: serializeLiftedNode(generateCode, block.branch),
				body: block.body.map((stmt) =>
					serializeLiftedNode(generateCode, stmt)
				),
			})),
	};
}

async function doIRJSON(file: HBCFile, args: Args) {
	if (args.parallelLift) {
		die('--ir-json cannot be combined with --parallel-lift');
	}
	if (args.liftOnly) die('--ir-json cannot be combined with --lift-only');
	if (args.composeSelected) {
		die('--compose cannot be combined with --ir-json');
	}
	if (args.metroModulesOutput) {
		die('--metro-modules cannot be combined with --ir-json');
	}
	if (
		args.cfgRecursiveAst || args.cfgRecursiveBabelAst ||
		args.cfgRecursiveJs || args.cfgMigrationAudit
	) {
		die('--ir-json cannot be combined with recursive CFG output modes');
	}
	const [{ IRFunction }, { default: generateCode }] = await Promise.all([
		import('../lib/ir/function/mod.ts'),
		import('@babel/generator'),
	]);
	const functionIds = selectedFunctionIds(file, args.functionRange);
	await withStreamingOutput(args.output, (sink) => {
		sink.write('{\n');
		sink.write('  "schemaVersion": 1,\n');
		sink.write('  "kind": "ares-unstructured-ir",\n');
		sink.write(
			`  "input": ${
				JSON.stringify({
					path: args.file,
					bytecodeVersion: file.version,
					functionRange: args.functionRange,
					functionCount: functionIds.length,
				})
			},\n`,
		);
		sink.write('  "functions": [\n');
		for (let index = 0; index < functionIds.length; index++) {
			const functionId = functionIds[index];
			const bytecodeFunction = file.functions[functionId];
			const func = new IRFunction(
				file,
				new SSAFunction(bytecodeFunction),
				{ skipCFGReduction: true },
			);
			const serialized = serializeIRFunction(
				file,
				func,
				generateCode as CodeGenerator,
			);
			sink.write(
				JSON.stringify(serialized, null, 2).split('\n').map((line) =>
					`    ${line}`
				).join('\n'),
			);
			sink.write(index + 1 === functionIds.length ? '\n' : ',\n');
		}
		sink.write('  ]\n');
		sink.write('}\n');
	});
}

interface DecompileImports {
	liftFile: typeof liftFile;
	liftFileParallel: typeof liftFileParallel;
	liftFileWithAnalysis: typeof liftFileWithAnalysis;
	liftFileParallelWithAnalysis: typeof liftFileParallelWithAnalysis;
	liftFunctionsIncrementally: typeof liftFunctionsIncrementally;
	collectRecursiveCFGMigrationSummaries:
		typeof collectRecursiveCFGMigrationSummaries;
	collectRecursiveCFGMigrationSummariesParallel:
		typeof collectRecursiveCFGMigrationSummariesParallel;
}

async function decompileWithReducer(
	file: HBCFile,
	args: Args,
	imports: DecompileImports,
	materialize = true,
	outputSink?: (chunk: string) => void,
) {
	const functionIds = args.functionRange
		? selectedFunctionIds(file, args.functionRange)
		: undefined;
	const options = {
		workers: args.workers ?? undefined,
		spill: {
			dir: args.spillDir ?? undefined,
			reuse: args.spillReuse,
			keep: args.spillKeep,
		},
		functionIds,
		composeRoots: args.composeSelected ? functionIds : undefined,
		compose: functionIds == null,
		metroModules: args.metroModulesOutput
			? { outputDir: args.metroModulesOutput }
			: undefined,
		cfgReducer: {
			mode: 'recursive' as const,
			debug: args.debugFeatures.has('recursive-cfg'),
			materialize,
			migrationAudit: args.cfgMigrationAudit || undefined,
			// This entry point returns code only. Every mode that reads Region
			// programs or their generated source -- the recursive CFG output
			// modes and the migration audit -- goes through
			// `decompileWithReducerAnalysis` instead.
			retainArtifacts: false,
		},
		outputSink,
	};
	return args.parallelLift
		? await imports.liftFileParallel(file, options)
		: imports.liftFile(file, options);
}

async function decompileWithReducerAnalysis(
	file: HBCFile,
	args: Args,
	imports: DecompileImports,
	materialize = true,
): Promise<LiftAnalysisResult> {
	const functionIds = args.functionRange
		? selectedFunctionIds(file, args.functionRange)
		: undefined;
	const options = {
		workers: args.workers ?? undefined,
		spill: {
			dir: args.spillDir ?? undefined,
			reuse: args.spillReuse,
			keep: args.spillKeep,
		},
		functionIds,
		composeRoots: args.composeSelected ? functionIds : undefined,
		compose: functionIds == null,
		metroModules: args.metroModulesOutput
			? { outputDir: args.metroModulesOutput }
			: undefined,
		cfgReducer: {
			mode: 'recursive' as const,
			debug: args.debugFeatures.has('recursive-cfg'),
			materialize,
			migrationAudit: args.cfgMigrationAudit || undefined,
			retainArtifacts: true,
		},
	};
	return args.parallelLift
		? await imports.liftFileParallelWithAnalysis(file, options)
		: imports.liftFileWithAnalysis(file, options);
}

function reportRecursiveCFGMisses(result: LiftAnalysisResult) {
	const summaries = result.recursiveCFGSummaries;
	const missed = summaries.filter((summary) =>
		effectiveRecursiveMisses(summary).length > 0
	);
	if (missed.length === 0) {
		console.log('Recursive CFG summary: no misses recorded');
		return;
	}

	const counts = new Map<string, number>();
	for (const summary of missed) {
		for (const miss of effectiveRecursiveMisses(summary)) {
			counts.set(miss, (counts.get(miss) ?? 0) + 1);
		}
	}
	console.log(
		`Recursive CFG summary: ${missed.length}/${summaries.length} ` +
			'functions have misses',
	);
	for (
		const [miss, count] of [...counts].toSorted((a, b) =>
			b[1] - a[1] || a[0].localeCompare(b[0])
		)
	) {
		console.log(`  ${String(count).padStart(4)} ${miss}`);
	}

	for (const summary of missed.slice(0, 20)) {
		console.log(
			`  #${summary.functionId}: blocks=${summary.blockCount} ` +
				`loops=${summary.loopCount} phis=${summary.phiCount} ` +
				`switches=${summary.switchCount} exceptions=${summary.exceptionHandlerCount} region=${
					summary.regionKind ?? 'none'
				} misses=${effectiveRecursiveMisses(summary).join(',')}`,
		);
	}
	if (missed.length > 20) {
		console.log(`  ... ${missed.length - 20} more functions omitted`);
	}
}

function formatRecursiveRegionIR(result: LiftAnalysisResult): string {
	const lines: string[] = [];
	const summaries = result.recursiveCFGSummaries.toSorted((a, b) =>
		a.functionId - b.functionId
	);
	for (const summary of summaries) {
		lines.push(
			`function #${summary.functionId} ` +
				`blocks=${summary.blockCount} edges=${summary.normalEdgeCount}` +
				`+${summary.exceptionalEdgeCount} ` +
				`sccs=${summary.sccCount} loops=${summary.loopCount} ` +
				`phis=${summary.phiCount} switches=${summary.switchCount} ` +
				`exceptions=${summary.exceptionHandlerCount}` +
				(summary.controlForestLabels
					? ` forestLabels=${summary.controlForestLabels}`
					: ''),
		);
		const effectiveMisses = effectiveRecursiveMisses(summary);
		if (effectiveMisses.length > 0) {
			lines.push(`  misses: ${effectiveMisses.join(', ')}`);
		}
		if (summary.diagnostics.length > 0) {
			for (const diagnostic of summary.diagnostics) {
				lines.push(
					`  diagnostic ${diagnostic.kind}: ${diagnostic.message}`,
				);
			}
		}
		if (summary.phiEdges.length > 0) {
			lines.push('  phi edge actions:');
			for (const edge of summary.phiEdges) {
				const assignments = edge.assignments.map((assignment) =>
					`${assignment.target} = ${assignment.value}`
				).join(', ');
				lines.push(
					`    ${edge.kind}:0x${edge.from.toString(16)}->0x${
						edge.to.toString(16)
					}: ${assignments}`,
				);
			}
		}
		if (summary.exceptionHandlers.length > 0) {
			lines.push('  exception handlers:');
			for (const handler of summary.exceptionHandlers) {
				lines.push(
					`    handler=0x${handler.handler.toString(16)} ` +
						`kind=${handler.kind} ` +
						`entries=${
							handler.protectedEntries.map((addr) =>
								`0x${addr.toString(16)}`
							).join(',')
						} ` +
						`protected=${
							handler.protectedBlocks.map((addr) =>
								`0x${addr.toString(16)}`
							).join(',')
						}` +
						(handler.catchBody == null
							? ''
							: ` catchBody=${
								handler.catchBody.map((addr) =>
									`0x${addr.toString(16)}`
								).join(',')
							}`) +
						(handler.finallyCopyRoots.length === 0
							? ''
							: ` finallyCopies=${
								handler.finallyCopyRoots.map((addr) =>
									`0x${addr.toString(16)}`
								).join(',')
							}`) +
						(handler.enclosingFinallyCopyRoots.length === 0
							? ''
							: ` enclosingFinallyCopies=${
								handler.enclosingFinallyCopyRoots.map((copy) =>
									`0x${copy.owner.toString(16)}:0x${
										copy.copyRoot.toString(16)
									}`
								).join(',')
							}`),
				);
			}
		}
		if (summary.regionText) {
			for (const line of summary.regionText.split('\n')) {
				lines.push(`  ${line}`);
			}
		} else {
			lines.push('  <no region>');
		}
		lines.push('');
	}
	return lines.join('\n');
}

function formatRecursiveBabelAST(
	result: LiftAnalysisResult,
	range: FunctionRange | null,
): string {
	const summaries = result.recursiveCFGSummaries
		.filter((summary) => functionIdInRange(summary.functionId, range))
		.toSorted((a, b) => a.functionId - b.functionId);
	return JSON.stringify(
		summaries.map((summary) => ({
			functionId: summary.functionId,
			normalization: summary.normalization,
			misses: effectiveRecursiveMisses(summary),
			initialMisses: summary.migrationAudit?.initial.misses ??
				summary.misses,
			diagnostics: summary.diagnostics,
			emitDiagnostics: summary.emitDiagnostics,
			statementCount: summary.emittedStatementCount ?? 0,
			program: summary.emittedProgram ?? null,
			rawEmission: summary.rawEmission,
			postReductionAnalysis: summary.postReductionAnalysis ?? null,
			reducedFallbackEmission: summary.reducedFallbackEmission ?? null,
			selectedEmission: summary.selectedEmission ?? null,
			selection: summary.selection,
			migrationAudit: summary.migrationAudit ?? null,
		})),
		null,
		2,
	);
}

function incrementCount(
	counts: Map<string, number>,
	key: string,
	by = 1,
): void {
	counts.set(key, (counts.get(key) ?? 0) + by);
}

function sortedCounts(counts: Map<string, number>): Record<string, number> {
	return Object.fromEntries(
		[...counts].toSorted(([left], [right]) => left.localeCompare(right)),
	);
}

function repositoryRevision(): string | null {
	try {
		const gitRoot = new URL('../.git/', import.meta.url);
		const head = readFileSync(new URL('HEAD', gitRoot), 'utf8').trim();
		if (!head.startsWith('ref: ')) return head || null;
		const ref = head.slice('ref: '.length);
		try {
			return readFileSync(new URL(ref, gitRoot), 'utf8').trim() || null;
		} catch {
			const packed = readFileSync(
				new URL('packed-refs', gitRoot),
				'utf8',
			);
			for (const line of packed.split('\n')) {
				if (line.startsWith('#') || line.startsWith('^')) continue;
				const [revision, name] = line.trim().split(/\s+/, 2);
				if (name === ref) return revision || null;
			}
		}
	} catch {
		// Reports remain usable outside a git checkout.
	}
	return null;
}

interface CFGMigrationReportEntry {
	functionId: number;
	selection: RecursiveCFGSelection | null;
	audit: RecursiveCFGMigrationAudit | null;
	postReductionAvailable: boolean;
	postReductionProgramAvailable: boolean;
	skippedReason: string | null;
}

function cfgMigrationSkippedReason(file: HBCFile, functionId: number): string {
	return file.functions[functionId]?.basicBlocks.has(0)
		? 'recursive-summary-unavailable'
		: 'no-entry-block';
}

function cfgMigrationReportEntryFromSummary(
	file: HBCFile,
	summary: RecursiveCFGMigrationFunctionSummary,
): CFGMigrationReportEntry {
	const audit = summary.migrationAudit;
	if (!summary.selection || !audit) {
		return {
			functionId: summary.functionId,
			selection: null,
			audit: null,
			postReductionAvailable: false,
			postReductionProgramAvailable: false,
			skippedReason: summary.skippedReason ?? cfgMigrationSkippedReason(
				file,
				summary.functionId,
			),
		};
	}
	return {
		functionId: summary.functionId,
		selection: summary.selection,
		audit,
		postReductionAvailable: summary.postReductionAvailable,
		postReductionProgramAvailable: summary.postReductionProgramAvailable,
		skippedReason: null,
	};
}

function incrementObjectCount(
	counts: Record<string, number>,
	key: string,
): void {
	counts[key] = (counts[key] ?? 0) + 1;
}

function cfgMigrationFunctionIds(file: HBCFile, args: Args): number[] {
	const functionIds = args.functionRange
		? selectedFunctionIds(file, args.functionRange)
		: selectedFunctionIds(file, null);
	return args.cfgMigrationProtectedOnly
		? functionIds.filter((id) =>
			file.functions[id].exceptionHandlers.length > 0
		)
		: functionIds;
}

async function writeCFGMigrationJSONL(
	file: HBCFile,
	args: Args,
	imports: DecompileImports,
	sink: TextSink,
): Promise<void> {
	const functionIds = cfgMigrationFunctionIds(file, args);
	const generatedAt = new Date().toISOString();
	sink.write(
		JSON.stringify({
			record: 'metadata',
			schemaVersion: 5,
			format: 'jsonl',
			input: {
				path: args.file,
				bytecodeVersion: file.version,
				functionCount: functionIds.length,
				functionRange: args.functionRange,
			},
			run: {
				gitRevision: repositoryRevision(),
				generatedAt,
				reducer: 'recursive',
				mode: args.cfgMigrationAudit,
				materialize: false,
				passTracing: true,
				shadowLegacy: true,
				normalizeForRegions: true,
				parallelLift: args.parallelLift,
				workers: args.parallelLift ? args.workers : null,
			},
		}) + '\n',
	);

	let analyzed = 0;
	let protectedFunctions = 0;
	let initialRegionComplete = 0;
	let finalRegionComplete = 0;
	let legacyWouldImprove = 0;
	let missRegressions = 0;
	const selection: Record<string, number> = {};
	const skipped: Record<string, number> = {};
	const collectFunctionIds =
		args.functionRange || args.cfgMigrationProtectedOnly
			? functionIds
			: undefined;
	const collectOptions = {
		functionIds: collectFunctionIds,
		retainSummaries: false,
		cfgReducer: {
			mode: 'recursive' as const,
			debug: args.debugFeatures.has('recursive-cfg'),
			materialize: false,
			migrationAudit: args.cfgMigrationAudit || undefined,
		},
	};
	const onSummary = (summary: RecursiveCFGMigrationFunctionSummary) => {
		const entry = cfgMigrationReportEntryFromSummary(file, summary);
		sink.write(JSON.stringify({ record: 'function', ...entry }) + '\n');
		if (!entry.audit || !entry.selection) {
			incrementObjectCount(
				skipped,
				entry.skippedReason ?? 'recursive-summary-unavailable',
			);
			incrementObjectCount(selection, 'not-analyzed');
			return;
		}
		const audit = entry.audit;
		analyzed++;
		if (audit.classification.exceptionHandlerCount > 0) {
			protectedFunctions++;
		}
		if (
			audit.initial.misses.length === 0 &&
			audit.initial.emitDiagnostics.length === 0 &&
			audit.initial.programAvailable
		) initialRegionComplete++;
		if (
			audit.final?.misses.length === 0 &&
			audit.final.emitDiagnostics.length === 0 &&
			audit.final.programAvailable
		) finalRegionComplete++;
		if (audit.legacyPhiRescue.wouldImprove) legacyWouldImprove++;
		for (const trace of audit.passTrace) {
			missRegressions += trace.regressedMisses?.length ?? 0;
		}
		incrementObjectCount(selection, entry.selection.candidate);
	};
	if (args.parallelLift) {
		await imports.collectRecursiveCFGMigrationSummariesParallel(
			file,
			{
				...collectOptions,
				workers: args.workers ?? undefined,
				spill: {
					dir: args.spillDir ?? undefined,
					reuse: args.spillReuse,
					keep: args.spillKeep,
				},
			},
			onSummary,
		);
	} else {
		imports.collectRecursiveCFGMigrationSummaries(
			file,
			collectOptions,
			onSummary,
		);
	}
	sink.write(
		JSON.stringify({
			record: 'footer',
			totals: {
				functions: functionIds.length,
				analyzed,
				protected: protectedFunctions,
				initialRegionComplete,
				finalRegionComplete,
				selection,
				skipped,
				legacyWouldImprove,
				missRegressions,
			},
		}) + '\n',
	);
}

/** The rejection reason recorded by `IRFunction` for an unbound register. */
const UNBOUND_REGISTER_REJECTION = 'generated registers are unbound';

function formatCFGMigrationAudit(
	entries: readonly CFGMigrationReportEntry[],
	file: HBCFile,
	args: Args,
	environmentIdentity?: LiftAnalysisResult['environmentIdentity'],
): string {
	const selection = new Map<string, number>();
	const initialMisses = new Map<string, number>();
	const firstHealingPasses = new Map<string, number>();
	const generatorKinds = new Map<string, number>();
	const cfgSizes = new Map<string, number>();
	const exceptionKinds = new Map<string, number>();
	const candidateRejections = new Map<string, number>();
	/**
	 * Candidates rejected because a generated register had no binding, split
	 * by which candidate was rejected.
	 *
	 * Broken out of `candidateRejections` because this is the population the
	 * unified placement work is measured against: every one of these is either
	 * a lexical placement this pass should fix, or a definition the CFG lost
	 * and it must not. See `BINDING-TODO.md` Phase 2.
	 */
	const unboundGeneratedRegisters = new Map<string, number>();
	const bindingCleanupTelemetry = new Map<string, number>();
	/** Applied binding-placement outcomes, summed over analysed functions. */
	const placementReasons = new Map<string, number>();
	const placementFunctions = new Map<string, number>();
	let placementPlaced = 0;
	let placementLocalized = 0;
	let placementUnresolved = 0;
	const missRegressions = new Map<string, number>();
	const skippedReasons = new Map<string, number>();
	const healingByMiss = new Map<string, Map<string, number>>();
	const healingTransitions = new Map<string, number>();
	const normalizationPasses = new Map<string, number>();
	const normalizationIssues = new Map<string, number>();
	const branchShapes = new Map<string, number>();
	const branchShapeRepresentatives = new Map<string, Set<number>>();
	const compatibilityAttempts = new Map<string, number>();
	const compatibilitySelections = new Map<string, number>();
	const compatibilityRepresentatives = new Map<string, Set<number>>();
	let initialClean = 0;
	let finalClean = 0;
	let rawRegionCandidates = 0;
	let postReductionCandidates = 0;
	let singleBlockReferences = 0;
	let materialized = 0;
	let guardedEligible = 0;
	let guardedAttempted = 0;
	let guardedAdopted = 0;
	let legacyEligible = 0;
	let legacyAttempted = 0;
	let legacyWouldImprove = 0;
	let legacyAdopted = 0;
	let legacyErrors = 0;
	let destructuringLegacyEligible = 0;
	let destructuringLegacyAttempted = 0;
	let destructuringLegacyWouldImprove = 0;
	let destructuringLegacyAdopted = 0;
	let destructuringLegacyErrors = 0;
	let normalizationEnabled = 0;
	let normalizationChanged = 0;
	let normalizationBlocksRemoved = 0;
	let normalizationNonIdempotent = 0;

	const functions = entries
		.toSorted((left, right) => left.functionId - right.functionId)
		.map((entry) => {
			const { audit } = entry;
			if (!audit || !entry.selection) {
				const reason = entry.skippedReason ??
					'recursive-summary-unavailable';
				incrementCount(skippedReasons, reason);
				incrementCount(selection, 'not-analyzed');
				return {
					functionId: entry.functionId,
					selection: null,
					audit: null,
					skippedReason: reason,
				};
			}
			incrementCount(selection, entry.selection.candidate);
			if (audit.normalization.enabled) normalizationEnabled++;
			if (audit.normalization.changed) normalizationChanged++;
			normalizationBlocksRemoved += audit.normalization.blocksBefore -
				audit.normalization.blocksAfter;
			if (!audit.normalization.idempotent) normalizationNonIdempotent++;
			for (const pass of audit.normalization.passes) {
				if (pass.changed) {
					incrementCount(normalizationPasses, pass.name);
				}
			}
			for (const issue of audit.normalization.invariantIssues) {
				incrementCount(normalizationIssues, issue.kind);
			}
			incrementCount(generatorKinds, audit.classification.generator);
			for (const branch of audit.classification.branchShapes) {
				for (const shape of branch.shapes) {
					incrementCount(branchShapes, shape);
					const representatives =
						branchShapeRepresentatives.get(shape) ??
							new Set<number>();
					if (representatives.size < 8) {
						representatives.add(entry.functionId);
					}
					branchShapeRepresentatives.set(shape, representatives);
				}
			}
			incrementCount(cfgSizes, audit.classification.cfgSize);
			incrementCount(
				exceptionKinds,
				audit.classification.exceptionHandlerCount === 0
					? 'none'
					: 'protected',
			);
			const placement = audit.bindingPlacement;
			if (placement) {
				placementPlaced += placement.placed;
				placementLocalized += placement.localized;
				placementUnresolved += placement.unresolved;
				for (
					const [reason, count] of Object.entries(placement.reasons)
				) {
					incrementCount(placementReasons, reason, count);
				}
				incrementCount(
					placementFunctions,
					placement.placed > 0 ? 'moved' : 'observed',
				);
				if (placement.unresolved > 0) {
					incrementCount(placementFunctions, 'has-unresolved');
				}
			}
			for (
				const [outcome, count] of Object.entries(
					audit.bindingCleanupTelemetry ?? {},
				)
			) incrementCount(bindingCleanupTelemetry, outcome, count);
			for (const rejection of audit.candidateRejections) {
				for (const reason of rejection.reasons) {
					incrementCount(
						candidateRejections,
						`${rejection.candidate}:${reason}`,
					);
					if (reason === UNBOUND_REGISTER_REJECTION) {
						incrementCount(
							unboundGeneratedRegisters,
							rejection.candidate,
						);
					}
				}
			}
			for (const event of audit.compatibilityPaths) {
				const key = `${event.phase}:${event.path}`;
				if (event.attempts > 0) {
					compatibilityAttempts.set(
						key,
						(compatibilityAttempts.get(key) ?? 0) + event.attempts,
					);
				}
				if (event.selections > 0) {
					compatibilitySelections.set(
						key,
						(compatibilitySelections.get(key) ?? 0) +
							event.selections,
					);
				}
				const representatives = compatibilityRepresentatives.get(key) ??
					new Set<number>();
				if (representatives.size < 32) {
					representatives.add(entry.functionId);
				}
				compatibilityRepresentatives.set(key, representatives);
			}
			for (const trace of audit.passTrace) {
				for (const miss of trace.regressedMisses ?? []) {
					incrementCount(
						missRegressions,
						`${trace.stage}/${trace.pass}:${miss}`,
					);
				}
			}
			if (
				audit.initial.misses.length === 0 &&
				audit.initial.emitDiagnostics.length === 0 &&
				audit.initial.programAvailable
			) initialClean++;
			if (audit.initial.programAvailable) rawRegionCandidates++;
			for (const miss of audit.initial.misses) {
				incrementCount(initialMisses, miss);
				const byPass = healingByMiss.get(miss) ??
					new Map<string, number>();
				const healingTrace = audit.passTrace.find((trace) =>
					trace.healedMisses?.includes(miss)
				);
				const healingPass = healingTrace == null
					? 'unhealed'
					: `${healingTrace.stage}/${healingTrace.pass}`;
				incrementCount(
					byPass,
					healingPass,
				);
				healingByMiss.set(miss, byPass);
				incrementCount(
					healingTransitions,
					JSON.stringify({
						miss,
						healingPass,
						bytecodeVersion: audit.classification.bytecodeVersion,
						generator: audit.classification.generator,
						async: audit.classification.async,
						exceptions:
							audit.classification.exceptionHandlerCount === 0
								? 'none'
								: 'protected',
						cfgSize: audit.classification.cfgSize,
					}),
				);
			}
			incrementCount(
				firstHealingPasses,
				audit.firstHealingPass ?? 'not-required',
			);
			if (
				audit.final?.misses.length === 0 &&
				audit.final.emitDiagnostics.length === 0 &&
				audit.final.programAvailable
			) finalClean++;
			if (entry.postReductionProgramAvailable) postReductionCandidates++;
			if (audit.final?.singleBlockReferenceAvailable) {
				singleBlockReferences++;
			}
			if (entry.selection.materialized) materialized++;
			if (audit.guardedPhiRetry.eligible) guardedEligible++;
			if (audit.guardedPhiRetry.attempted) guardedAttempted++;
			if (audit.guardedPhiRetry.adopted) guardedAdopted++;
			if (audit.legacyPhiRescue.eligible) legacyEligible++;
			if (audit.legacyPhiRescue.attempted) legacyAttempted++;
			if (audit.legacyPhiRescue.wouldImprove) legacyWouldImprove++;
			if (audit.legacyPhiRescue.adopted) legacyAdopted++;
			if (audit.legacyPhiRescue.error != null) legacyErrors++;
			if (audit.destructuringLegacyRescue.eligible) {
				destructuringLegacyEligible++;
			}
			if (audit.destructuringLegacyRescue.attempted) {
				destructuringLegacyAttempted++;
			}
			if (audit.destructuringLegacyRescue.wouldImprove) {
				destructuringLegacyWouldImprove++;
			}
			if (audit.destructuringLegacyRescue.adopted) {
				destructuringLegacyAdopted++;
			}
			if (audit.destructuringLegacyRescue.error != null) {
				destructuringLegacyErrors++;
			}
			return {
				functionId: entry.functionId,
				selection: entry.selection,
				audit,
			};
		});

	return JSON.stringify(
		{
			schemaVersion: 5,
			input: {
				path: args.file,
				bytecodeVersion: file.version,
				functionCount: functions.length,
				functionRange: args.functionRange,
			},
			run: {
				gitRevision: repositoryRevision(),
				generatedAt: new Date().toISOString(),
				reducer: 'recursive',
				mode: args.cfgMigrationAudit,
				materialize: false,
				passTracing: true,
				shadowLegacy: true,
				normalizeForRegions: true,
				parallelLift: args.parallelLift,
				workers: args.workers,
			},
			totals: {
				functions: functions.length,
				initialRegionComplete: initialClean,
				finalRegionComplete: finalClean,
				analyzed: functions.length -
					[...skippedReasons.values()].reduce(
						(total, count) => total + count,
						0,
					),
				skipped: sortedCounts(skippedReasons),
				selection: sortedCounts(selection),
				initialMisses: sortedCounts(initialMisses),
				firstHealingPasses: sortedCounts(firstHealingPasses),
				healingByMiss: Object.fromEntries(
					[...healingByMiss]
						.toSorted(([left], [right]) =>
							left.localeCompare(right)
						)
						.map(([miss, counts]) => [miss, sortedCounts(counts)]),
				),
				healingTransitions: [...healingTransitions]
					.map(([key, count]) => ({
						...JSON.parse(key) as {
							miss: string;
							healingPass: string;
							bytecodeVersion: number;
							generator: string;
							async: boolean;
							exceptions: string;
							cfgSize: string;
						},
						count,
					}))
					.toSorted((left, right) =>
						left.miss.localeCompare(right.miss) ||
						left.healingPass.localeCompare(right.healingPass) ||
						left.bytecodeVersion - right.bytecodeVersion ||
						left.generator.localeCompare(right.generator) ||
						left.cfgSize.localeCompare(right.cfgSize)
					),
				classifications: {
					bytecodeVersion: {
						[String(file.version)]: functions.length,
					},
					generator: sortedCounts(generatorKinds),
					exceptions: sortedCounts(exceptionKinds),
					cfgSize: sortedCounts(cfgSizes),
					branchShape: sortedCounts(branchShapes),
					branchShapeRepresentatives: Object.fromEntries(
						[...branchShapeRepresentatives]
							.toSorted(([left], [right]) =>
								left.localeCompare(right)
							)
							.map(([shape, ids]) => [shape, [...ids]]),
					),
				},
				candidateRejections: sortedCounts(candidateRejections),
				bindings: {
					unboundGeneratedRegisters: sortedCounts(
						unboundGeneratedRegisters,
					),
					cleanupTelemetry: sortedCounts(bindingCleanupTelemetry),
					environmentIdentity: environmentIdentity ?? null,
					placement: {
						functions: sortedCounts(placementFunctions),
						reasons: sortedCounts(placementReasons),
						placed: placementPlaced,
						localized: placementLocalized,
						unresolved: placementUnresolved,
					},
				},
				missRegressions: sortedCounts(missRegressions),
				candidateAvailability: {
					rawRegion: rawRegionCandidates,
					postReductionRegion: postReductionCandidates,
					singleBlockReference: singleBlockReferences,
				},
				materialized,
				normalization: {
					enabled: normalizationEnabled,
					changed: normalizationChanged,
					blocksRemoved: normalizationBlocksRemoved,
					nonIdempotent: normalizationNonIdempotent,
					changedPasses: sortedCounts(normalizationPasses),
					invariantIssues: sortedCounts(normalizationIssues),
				},
				guardedPhiRetry: {
					eligible: guardedEligible,
					attempted: guardedAttempted,
					adopted: guardedAdopted,
				},
				legacyPhiRescue: {
					eligible: legacyEligible,
					attempted: legacyAttempted,
					wouldImprove: legacyWouldImprove,
					adopted: legacyAdopted,
					errors: legacyErrors,
				},
				destructuringLegacyRescue: {
					eligible: destructuringLegacyEligible,
					attempted: destructuringLegacyAttempted,
					wouldImprove: destructuringLegacyWouldImprove,
					adopted: destructuringLegacyAdopted,
					errors: destructuringLegacyErrors,
				},
				compatibilityPaths: {
					attempts: sortedCounts(compatibilityAttempts),
					selections: sortedCounts(compatibilitySelections),
					representatives: Object.fromEntries(
						[...compatibilityRepresentatives]
							.toSorted(([left], [right]) =>
								left.localeCompare(right)
							)
							.map(([key, ids]) => [key, [...ids]]),
					),
				},
			},
			functions,
		},
		null,
		2,
	);
}

function functionIdInRange(id: number, range: FunctionRange | null): boolean {
	return range == null || (id >= range.start && id <= range.end);
}

function formatRecursiveEmittedJS(result: LiftAnalysisResult): string {
	const lines: string[] = [];
	const summaries = result.recursiveCFGSummaries.toSorted((a, b) =>
		a.functionId - b.functionId
	);
	for (const summary of summaries) {
		lines.push(`// function #${summary.functionId}`);
		const effectiveMisses = effectiveRecursiveMisses(summary);
		if (effectiveMisses.length > 0) {
			lines.push(`// misses: ${effectiveMisses.join(', ')}`);
		}
		if (summary.emitDiagnostics.length > 0) {
			for (const diagnostic of summary.emitDiagnostics) {
				lines.push(`// emit diagnostic: ${diagnostic}`);
			}
		}
		lines.push(summary.emittedCode ?? '/* no recursive region */');
		lines.push('');
	}
	return lines.join('\n');
}

function effectiveRecursiveMisses(
	summary: LiftAnalysisResult['recursiveCFGSummaries'][number],
): string[] {
	if (
		summary.selectedEmission?.source === 'reduced-fallback' &&
		summary.reducedFallbackEmission?.status === 'emitted' &&
		summary.reducedFallbackEmission.diagnostics.length === 0
	) {
		return [];
	}
	return summary.postReductionAnalysis?.misses ?? summary.misses;
}

function firstDifference(legacy: string, recursive: string) {
	const legacyLines = legacy.split('\n');
	const recursiveLines = recursive.split('\n');
	const length = Math.max(legacyLines.length, recursiveLines.length);
	for (let i = 0; i < length; i++) {
		const left = legacyLines[i] ?? '<missing>';
		const right = recursiveLines[i] ?? '<missing>';
		if (left === right) continue;
		return {
			line: i + 1,
			legacy: left,
			recursive: right,
		};
	}
	return { line: 0, legacy: '', recursive: '' };
}

function formatLiftedFunctionArtifact(artifact: LiftedFunctionArtifact) {
	const summary = artifact.summary;
	const name = summary.name == null ? '<anonymous>' : summary.name;
	const references = summary.referencedFunctions.length === 0
		? 'none'
		: summary.referencedFunctions.map((reference) =>
			`#${reference.functionId}x${reference.count}`
		).join(',');
	const createdEnvironments = summary.createdEnvironments.length === 0
		? ''
		: ` created-env=${
			summary.createdEnvironments.map((environment) =>
				`${environment.kind}:${environment.size ?? '?'}`
			).join(',')
		}`;
	const recursive = summary.recursiveCFG
		? ` recursive=${summary.recursiveCFG.emissionStatus}` +
			(summary.recursiveCFG.misses.length > 0
				? ` misses=${summary.recursiveCFG.misses.join(',')}`
				: '')
		: '';
	const structure = summary.structured
		? 'structured'
		: `unstructured blocks=${summary.remainingBlocks.length}`;
	return `/* Function #${summary.functionId} (${name}) ` +
		`params=${summary.paramCount} frame=${summary.frameSize} ` +
		`env=${summary.environmentSize}${createdEnvironments} ` +
		`refs=${references} ${structure}${recursive} */\n` +
		`${artifact.code}\n\n`;
}

async function liftOnly(
	file: HBCFile,
	args: Args,
	imports: DecompileImports,
) {
	if (args.parallelLift) {
		die(
			'--lift-only cannot be combined with --parallel-lift; ' +
				'incremental lifting is deliberately serial and memory-bounded',
		);
	}
	if (args.metroModulesOutput) {
		die('--lift-only cannot be combined with --metro-modules');
	}
	if (
		args.cfgRecursiveAst || args.cfgRecursiveBabelAst ||
		args.cfgRecursiveJs
	) {
		die('--lift-only cannot be combined with recursive CFG output modes');
	}

	const functionIds = selectedFunctionIds(file, args.functionRange);
	await withStreamingOutput(args.output, async (sink) => {
		await withProgress(functionIds.length, args.noProgress, () => {
			imports.liftFunctionsIncrementally(
				file,
				{
					functionIds,
					retainSummaries: false,
					cfgReducer: {
						mode: 'recursive',
						debug: args.debugFeatures.has('recursive-cfg'),
						materialize: true,
						retainArtifacts: false,
					},
				},
				(artifact) =>
					sink.write(formatLiftedFunctionArtifact(artifact)),
			);
		});
	});
}

async function doDecompile(
	file: HBCFile,
	args: Args,
) {
	if (args.cfgMigrationAudit) {
		if (args.liftOnly) {
			die('--cfg-migration-audit cannot be combined with --lift-only');
		}
		if (
			args.cfgRecursiveAst || args.cfgRecursiveBabelAst ||
			args.cfgRecursiveJs
		) {
			die(
				'--cfg-migration-audit cannot be combined with another CFG output mode',
			);
		}
		if (args.metroModulesOutput) {
			die('--cfg-migration-audit cannot be combined with --metro-modules');
		}
		if (args.cfgMigrationProtectedOnly && !args.cfgMigrationAuditJSONL) {
			die(
				'--cfg-migration-protected-only currently requires ' +
					'--cfg-migration-audit=jsonl',
			);
		}
	}
	if (args.cfgMigrationProtectedOnly && !args.cfgMigrationAudit) {
		die('--cfg-migration-protected-only requires --cfg-migration-audit');
	}
	// Apply debug env vars before importing lift.ts (which reads them at init time)
	if (args.debugFeatures.has('lowered-generator')) {
		Deno.env.set('ARES_DEBUG_LOWERED_GENERATOR', '1');
	}
	if (args.debugFeatures.has('lowered-generator-model')) {
		Deno.env.set('ARES_DEBUG_LOWERED_GENERATOR_MODEL', '1');
	}
	if (args.debugFeatures.has('dup-ssa')) {
		Deno.env.set('ARES_DEBUG_DUP_SSA', '1');
	}

	const {
		liftFile,
		liftFileParallel,
		liftFileWithAnalysis,
		liftFileParallelWithAnalysis,
		liftFunctionsIncrementally,
		collectRecursiveCFGMigrationSummaries,
		collectRecursiveCFGMigrationSummariesParallel,
	} = await import('../lib/ir/lift.ts');
	const { default: { default: highlight } } = await import(
		'@babel/highlight'
	);
	const imports = {
		liftFile,
		liftFileParallel,
		liftFileWithAnalysis,
		liftFileParallelWithAnalysis,
		liftFunctionsIncrementally,
		collectRecursiveCFGMigrationSummaries,
		collectRecursiveCFGMigrationSummariesParallel,
	};

	if (args.liftOnly) {
		if (args.composeSelected) {
			die('--compose cannot be combined with --lift-only');
		}
		await liftOnly(file, args, imports);
		return;
	}

	if (args.functionRange && args.metroModulesOutput) {
		die('--function cannot be combined with --metro-modules');
	}
	if (args.composeSelected) {
		if (!args.functionRange) {
			die('--compose requires --function to say what to compose from');
		}
		if (args.parallelLift) {
			// The parallel path composes whole Metro units through its own
			// scheduler, which has no notion of an arbitrary root.
			die('--compose cannot be combined with --parallel-lift');
		}
	}

	const functionCount = args.cfgMigrationAuditJSONL
		? cfgMigrationFunctionIds(file, args).length
		: args.functionRange
		? selectedFunctionIds(file, args.functionRange).length
		: file.functions.length;

	if (args.cfgMigrationAudit) {
		if (args.cfgMigrationAuditJSONL) {
			await withStreamingOutput(args.output, async (sink) => {
				await withProgress(
					functionCount,
					args.noProgress,
					() => writeCFGMigrationJSONL(file, args, imports, sink),
				);
			});
			return;
		}
		await withOutputCapture(args.output, async () => {
			await withProgress(
				functionCount,
				args.noProgress,
				async () => {
					let entries: CFGMigrationReportEntry[];
					let environmentIdentity: LiftAnalysisResult[
						'environmentIdentity'
					];
					if (args.parallelLift) {
						const result = await decompileWithReducerAnalysis(
							file,
							args,
							imports,
							false,
						);
						environmentIdentity = result.environmentIdentity;
						const summaries = new Map(
							result.recursiveCFGSummaries.map((summary) => [
								summary.functionId,
								summary,
							]),
						);
						const functionIds = args.functionRange
							? selectedFunctionIds(file, args.functionRange)
							: selectedFunctionIds(file, null);
						entries = functionIds.map((functionId) => {
							const summary = summaries.get(functionId);
							const audit = summary?.migrationAudit;
							if (!summary || !audit) {
								return {
									functionId,
									selection: null,
									audit: null,
									postReductionAvailable: false,
									postReductionProgramAvailable: false,
									skippedReason: cfgMigrationSkippedReason(
										file,
										functionId,
									),
								};
							}
							return {
								functionId,
								selection: summary.selection,
								audit,
								postReductionAvailable:
									summary.postReductionAnalysis != null,
								postReductionProgramAvailable:
									summary.postReductionAnalysis?.rawEmission
										.program != null,
								skippedReason: null,
							};
						});
					} else {
						const functionIds = args.functionRange
							? selectedFunctionIds(file, args.functionRange)
							: selectedFunctionIds(file, null);
						const summaries = imports
							.collectRecursiveCFGMigrationSummaries(
								file,
								{
									functionIds,
									retainSummaries: true,
									cfgReducer: {
										mode: 'recursive',
										debug: args.debugFeatures.has(
											'recursive-cfg',
										),
										materialize: false,
										migrationAudit:
											args.cfgMigrationAudit ||
											undefined,
									},
								},
							);
						entries = summaries.map((summary) => {
							const audit = summary.migrationAudit;
							if (!summary.selection || !audit) {
								return {
									functionId: summary.functionId,
									selection: null,
									audit: null,
									postReductionAvailable: false,
									postReductionProgramAvailable: false,
									skippedReason: summary.skippedReason,
								};
							}
							return {
								functionId: summary.functionId,
								selection: summary.selection,
								audit,
								postReductionAvailable:
									summary.postReductionAvailable,
								postReductionProgramAvailable:
									summary.postReductionProgramAvailable,
								skippedReason: null,
							};
						});
					}
					console.log(
						formatCFGMigrationAudit(
							entries,
							file,
							args,
							environmentIdentity,
						),
					);
				},
			);
		});
		return;
	}

	if (args.cfgRecursiveAst) {
		await withOutputCapture(args.output, async () => {
			await withProgress(
				functionCount,
				args.noProgress,
				async () => {
					const result = await decompileWithReducerAnalysis(
						file,
						args,
						imports,
						false,
					);
					console.log(formatRecursiveRegionIR(result));
				},
			);
		});
		return;
	}

	if (args.cfgRecursiveBabelAst) {
		await withOutputCapture(args.output, async () => {
			await withProgress(
				functionCount,
				args.noProgress,
				async () => {
					const result = await decompileWithReducerAnalysis(
						file,
						args,
						imports,
						false,
					);
					console.log(
						formatRecursiveBabelAST(result, args.functionRange),
					);
				},
			);
		});
		return;
	}

	if (args.cfgRecursiveJs) {
		await withOutputCapture(args.output, async () => {
			await withProgress(
				functionCount,
				args.noProgress,
				async () => {
					const result = await decompileWithReducerAnalysis(
						file,
						args,
						imports,
						false,
					);
					console.log(formatRecursiveEmittedJS(result));
				},
			);
		});
		return;
	}

	const decompile = async (outputSink?: (chunk: string) => void) => {
		await withProgress(functionCount, args.noProgress, async () => {
			const code = await decompileWithReducer(
				file,
				args,
				imports,
				true,
				outputSink,
			);
			if (outputSink) {
				outputSink('\n');
			} else {
				console.log(highlight(code));
			}
		});
	};
	if (args.output) {
		await withStreamingOutput(
			args.output,
			(sink) => decompile((chunk) => sink.write(chunk)),
		);
	} else {
		await decompile();
	}
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

const args = parseArgs(Deno.args);
if (args.cfgMigrationAudit && args.mode !== 'decompile') {
	die('--cfg-migration-audit is only available in decompile mode');
}

let file: HBCFile;
try {
	file = HBCFile.fromFile(args.file);
} catch (e) {
	die(`Cannot open ${args.file}: ${e instanceof Error ? e.message : e}`);
}

switch (args.mode) {
	case 'list-functions':
		doListFunctions(file, args.functionRange);
		break;
	case 'disasm':
		doDisasm(args.file, args.functionRange);
		break;
	case 'ssa':
		doSSA(file, args.functionRange);
		break;
	case 'blocks':
		doBlocks(file, args.functionRange);
		break;
	case 'ir-json':
		await doIRJSON(file, args);
		break;
	case 'decompile':
		await doDecompile(file, args);
		break;
}
