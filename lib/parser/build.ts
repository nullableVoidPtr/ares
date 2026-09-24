#!/usr/bin/env -S deno run -A
// Build script for hermes-bytecode-parser WASM.
// Replaces @deno/wasmbuild so we can use an unpinned wasm-bindgen version.

const dir = import.meta.dirname!;

async function run(cmd: string[], cwd: string) {
	const result = await new Deno.Command(cmd[0], {
		args: cmd.slice(1),
		stdout: 'inherit',
		stderr: 'inherit',
		cwd,
	}).output();
	if (!result.success) {
		console.error(`command failed: ${cmd.join(' ')}`);
		Deno.exit(1);
	}
}

// Locate the wasm-bindgen binary. `cargo install` puts it in $CARGO_HOME/bin,
// which may differ from where the system `cargo` wrapper lives (e.g. /usr/bin).
// Probe the known roots in priority order and fall back to bare name (PATH).
async function findWbg(): Promise<string> {
	const home = Deno.env.get('HOME')!;
	const xdgState = Deno.env.get('XDG_STATE_HOME') ?? `${home}/.local/state`;
	const candidates = [
		Deno.env.get('CARGO_HOME'),
		`${home}/.cargo`,
		`${xdgState}/cargo`,
	].filter((x): x is string => Boolean(x)).map((h) =>
		`${h}/bin/wasm-bindgen`
	);

	for (const p of candidates) {
		try {
			await Deno.stat(p);
			return p;
		} catch { /* try next */ }
	}
	return 'wasm-bindgen'; // last resort: rely on PATH
}

// Read the wasm-bindgen version that Cargo resolved so we can install a
// matching wasm-bindgen-cli. The Cargo.lock line looks like:
//   name = "wasm-bindgen"
//   version = "0.2.xxx"
const lockText = await Deno.readTextFile(`${dir}/Cargo.lock`);
const versionMatch = lockText.match(
	/name = "wasm-bindgen"\nversion = "([^"]+)"/,
);
if (!versionMatch) {
	console.error('Could not find wasm-bindgen version in Cargo.lock');
	Deno.exit(1);
}
const wbgVersion = versionMatch[1];

// Check if installed wasm-bindgen-cli matches; install if not.
let installed: string | null = null;
try {
	const candidate = await findWbg();
	const out = await new Deno.Command(candidate, { args: ['--version'] })
		.output();
	if (out.success) {
		installed = new TextDecoder().decode(out.stdout).trim().split(' ')[1];
	}
} catch { /* not installed */ }

if (installed !== wbgVersion) {
	console.log(
		`Installing wasm-bindgen-cli ${wbgVersion} (have: ${
			installed ?? 'none'
		})`,
	);
	await run(
		[
			'cargo',
			'install',
			'wasm-bindgen-cli',
			'--version',
			wbgVersion,
			'--locked',
		],
		dir,
	);
}

const wbgBin = await findWbg();

// Build the WASM binary.
const profile = Deno.args.includes('--debug') ? 'debug' : 'release';
const cargoArgs = ['build', '--target', 'wasm32-unknown-unknown'];
if (profile === 'release') cargoArgs.push('--release');
await run(['cargo', ...cargoArgs], dir);

// Generate JS/TS bindings.
const wasmPath =
	`${dir}/target/wasm32-unknown-unknown/${profile}/hermes_bytecode_parser.wasm`;
await run([wbgBin, wasmPath, '--target', 'bundler', '--out-dir', 'wasm'], dir);

// Write the thin Deno adapter.  wasm-bindgen --target bundler produces
// hermes_bytecode_parser_bg.{js,wasm} plus hermes_bytecode_parser.d.ts.
// This adapter lets Deno import the .wasm as an ES module (static import) so
// no async init() call is needed at the use site.
const adapter = `\
// @generated — do not edit; run \`deno task build:wasm\` to regenerate
// @ts-self-types="./hermes_bytecode_parser.d.ts"
import * as wasm from "./hermes_bytecode_parser_bg.wasm";
export * from "./hermes_bytecode_parser_bg.js";
import { __wbg_set_wasm } from "./hermes_bytecode_parser_bg.js";
__wbg_set_wasm(wasm);
`;
await Deno.writeTextFile(`${dir}/wasm/hermes_bytecode_parser.js`, adapter);

console.log(`Build (${profile}) complete.`);
