/**
 * Progress reporting, silenced at its source.
 *
 * `--no-progress` used to replace `console.error` with a no-op for the whole
 * run. That reached far past progress: diagnostics went out the same way, so
 * three separate reports had to be rerouted through a raw file-descriptor
 * write to escape it (see `writeDiagnostic`), and every `--debug` feature
 * produced nothing at all when combined with the flag.
 *
 * Progress goes through here instead. Suppressing it now stops exactly one
 * kind of message and cannot reach anything else. The default sink is still
 * `console.error`, so a caller that wraps that stream -- the progress bar in
 * `src/ares.ts` reads these lines to drive itself -- keeps seeing them.
 */
let enabled = true;

/** Whether progress messages are currently emitted. */
export function progressEnabled(): boolean {
	return enabled;
}

/** Turn progress reporting on or off. Returns the previous setting. */
export function setProgressEnabled(next: boolean): boolean {
	const previous = enabled;
	enabled = next;
	return previous;
}

/** Emit a progress message, unless progress reporting is off. */
export function reportProgress(message: string): void {
	if (enabled) console.error(message);
}
