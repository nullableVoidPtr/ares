/**
 * Opening a cold store for one run: where it lives, whether it can be reused,
 * and getting the bytes-derived phases into it.
 */
import * as path from 'node:path';
import * as fs from 'node:fs';
import type { HBCFile } from '../parser/file.ts';
import {
	type ColdStore,
	COLDSTORE_SCHEMA_VERSION,
	type ColdStoreFingerprint,
	fingerprintsMatch,
	hashBytes,
	hashOptions,
	markPhaseComplete,
	openColdStore,
	phaseComplete,
	readFingerprint,
	writeFingerprint,
} from './mod.ts';
import { writeColdFile } from './file.ts';
import { buildBytecodeDerivedPlan, writeColdPlan } from './plan.ts';

export interface ColdSessionOptions {
	/** Where stores are kept. Defaults to the user cache directory. */
	dir?: string;
	/**
	 * Reuse a store whose fingerprint matches, and keep it afterwards.
	 *
	 * Off by default. A store that is wrongly reused produces yesterday's
	 * output silently, which is a far worse failure than redoing the work, so
	 * this is opt-in even though the fingerprint covers the bundle bytes, the
	 * lifting options and the schema version.
	 */
	reuse?: boolean;
	/** Keep the store on disk after the run even when not reusing. */
	keep?: boolean;
}

export interface ColdSession {
	store: ColdStore;
	path: string;
	/** True when the bytes-derived phases were already present and valid. */
	reusedFile: boolean;
	/** True when every lifted snapshot was already present and valid. */
	reusedSnapshots: boolean;
	release(): Promise<void>;
}

function defaultSpillRoot(): string {
	const xdg = Deno.env.get('XDG_CACHE_HOME');
	if (xdg) return path.join(xdg, 'ares', 'spill');
	const home = Deno.env.get('HOME') ?? '.';
	return path.join(home, '.cache', 'ares', 'spill');
}

/**
 * Prepare a store for this bundle, writing the phases derived from its bytes.
 *
 * The caller still has to have parsed the file once -- something has to, and
 * this is the only place that does. What it buys is that no worker has to,
 * which is fifteen of the sixteen copies.
 */
export async function openColdSession(
	file: HBCFile,
	liftOptions: unknown,
	options: ColdSessionOptions = {},
	onProgress?: (message: string) => void,
): Promise<ColdSession> {
	const fingerprint: ColdStoreFingerprint = {
		schema: COLDSTORE_SCHEMA_VERSION,
		bundleHash: await hashBytes(file.data),
		bundleLength: file.data.byteLength,
		hermesVersion: file.version,
		optionsHash: hashOptions(liftOptions),
	};

	const root = options.dir ?? defaultSpillRoot();
	// Named by fingerprint so two runs with different options never collide.
	const storePath = path.join(
		root,
		`${fingerprint.bundleHash.slice(0, 16)}-${fingerprint.optionsHash}`,
	);
	fs.mkdirSync(root, { recursive: true });

	if (!options.reuse && fs.existsSync(storePath)) {
		fs.rmSync(storePath, { recursive: true, force: true });
	}

	let store = await openColdStore(storePath);
	let existing = readFingerprint(store);

	if (existing && !fingerprintsMatch(existing, fingerprint)) {
		// Rebuilt, never migrated: the contents are a cache of work that can
		// always be redone, so a migration path would be pure liability.
		onProgress?.('cold store fingerprint mismatch; rebuilding');
		await store.close();
		fs.rmSync(storePath, { recursive: true, force: true });
		store = await openColdStore(storePath);
		existing = undefined;
	}

	const reusedFile = existing != null &&
		phaseComplete(store, 'fn') &&
		phaseComplete(store, 'plan');
	const reusedSnapshots = reusedFile && phaseComplete(store, 'snap');

	if (!reusedFile) {
		await writeFingerprint(store, fingerprint);
		onProgress?.('writing bundle to cold store');
		await writeColdFile(store, file);
		await markPhaseComplete(store, 'fn');
		onProgress?.('writing bytecode plan to cold store');
		await writeColdPlan(store, buildBytecodeDerivedPlan(file));
		await markPhaseComplete(store, 'plan');
	}

	const keep = options.keep || options.reuse;
	return {
		store,
		path: storePath,
		reusedFile,
		reusedSnapshots,
		release: async () => {
			await store.close();
			if (!keep) {
				fs.rmSync(storePath, { recursive: true, force: true });
			}
		},
	};
}

/** Mark lifting complete, so a later run with `reuse` can skip it. */
export async function markSnapshotsComplete(
	session: ColdSession,
): Promise<void> {
	await markPhaseComplete(session.store, 'snap');
}
