let DEBUG = false;
let DEBUG_MODEL = false;
let DEBUG_DUP_SSA = false;
let DEBUG_RECOVERED_CFG = false;
try {
	DEBUG = Deno.env.get('ARES_DEBUG_LOWERED_GENERATOR') === '1';
	DEBUG_MODEL = Deno.env.get('ARES_DEBUG_LOWERED_GENERATOR_MODEL') === '1';
	DEBUG_DUP_SSA = Deno.env.get('ARES_DEBUG_DUP_SSA') === '1';
	DEBUG_RECOVERED_CFG =
		Deno.env.get('ARES_DEBUG_RECOVERED_GENERATOR_CFG') === '1';
} catch {
	DEBUG = false;
	DEBUG_MODEL = false;
	DEBUG_DUP_SSA = false;
	DEBUG_RECOVERED_CFG = false;
}

export function debug(...args: unknown[]) {
	if (DEBUG) console.error('[lowered-generator]', ...args);
}

export function debugModel(...args: unknown[]) {
	if (DEBUG_MODEL) console.error('[lowered-generator-model]', ...args);
}

export function debugDupSSA(...args: unknown[]) {
	if (DEBUG_DUP_SSA) console.error('[dup-ssa]', ...args);
}

export function duplicateSSADebugEnabled() {
	return DEBUG_DUP_SSA;
}

export function recoveredGeneratorCFGDebugEnabled() {
	return DEBUG_RECOVERED_CFG;
}
