export type CFGReducerMode = 'recursive';
export type CFGMigrationAuditMode = 'observe' | 'strict';

export interface CFGReducerOptions {
	mode?: CFGReducerMode;
	strict?: boolean;
	debug?: boolean;
	materialize?: boolean;
	/**
	 * Opt-in migration telemetry. This deliberately enables expensive Region
	 * probes and compatibility-path accounting, so it must never be enabled
	 * implicitly.
	 */
	migrationAudit?: CFGMigrationAuditMode;
	/**
	 * Keep heavyweight recursive-CFG emission artifacts on summaries.
	 *
	 * Plain decompile only needs those artifacts long enough to materialize a
	 * candidate; persisting them in cold snapshots makes summary heads carry full
	 * Babel programs and generated code for every function.
	 */
	retainArtifacts?: boolean;
}

export function envFlag(name: string): boolean {
	try {
		return Deno.env.get(name) === '1';
	} catch {
		return false;
	}
}

export function envCFGReducerOptions(): CFGReducerOptions {
	return {
		mode: 'recursive',
		strict: envFlag('ARES_RECURSIVE_CFG_STRICT'),
		debug: envFlag('ARES_RECURSIVE_CFG_DEBUG'),
	};
}
