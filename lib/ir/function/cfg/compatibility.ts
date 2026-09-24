import type { BlockAddr } from '../../../hbc/disassembly/function.ts';

export type CFGCompatibilityPath =
	| 'whole-cfg-continuation-forest'
	| 'single-top-level-loop'
	| 'local-fallback-region';

interface MutableCFGCompatibilityEvent {
	attempts: number;
	selections: number;
	entries: Set<BlockAddr>;
	reasons: Set<string>;
}

export interface CFGCompatibilityEvent {
	path: CFGCompatibilityPath;
	attempts: number;
	selections: number;
	entries: BlockAddr[];
	reasons: string[];
}

export interface CFGCompatibilityTelemetry {
	events: Map<CFGCompatibilityPath, MutableCFGCompatibilityEvent>;
}

export function createCFGCompatibilityTelemetry(): CFGCompatibilityTelemetry {
	return { events: new Map() };
}

function eventFor(
	telemetry: CFGCompatibilityTelemetry | undefined,
	path: CFGCompatibilityPath,
): MutableCFGCompatibilityEvent | undefined {
	if (!telemetry) return;
	let event = telemetry.events.get(path);
	if (!event) {
		event = {
			attempts: 0,
			selections: 0,
			entries: new Set(),
			reasons: new Set(),
		};
		telemetry.events.set(path, event);
	}
	return event;
}

export function recordCFGCompatibilityAttempt(
	telemetry: CFGCompatibilityTelemetry | undefined,
	path: CFGCompatibilityPath,
	entry: BlockAddr,
	reason: string,
): void {
	const event = eventFor(telemetry, path);
	if (!event) return;
	event.attempts++;
	event.entries.add(entry);
	event.reasons.add(reason);
}

export function recordCFGCompatibilitySelection(
	telemetry: CFGCompatibilityTelemetry | undefined,
	path: CFGCompatibilityPath,
	entry: BlockAddr,
	reason: string,
): void {
	const event = eventFor(telemetry, path);
	if (!event) return;
	event.selections++;
	event.entries.add(entry);
	event.reasons.add(reason);
}

export function summarizeCFGCompatibilityTelemetry(
	telemetry: CFGCompatibilityTelemetry | undefined,
): CFGCompatibilityEvent[] {
	if (!telemetry) return [];
	return [...telemetry.events].map(([path, event]) => ({
		path,
		attempts: event.attempts,
		selections: event.selections,
		entries: [...event.entries].toSorted((left, right) => left - right),
		reasons: [...event.reasons].toSorted(),
	})).toSorted((left, right) => left.path.localeCompare(right.path));
}
