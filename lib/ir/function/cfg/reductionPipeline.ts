export type ReductionPassResult = boolean | 'restart';

export interface ReductionPass<Context> {
	name: string;
	run(context: Context): ReductionPassResult;
}

export interface FixpointOptions<Context> {
	/** Passes attempted only after the ordinary pass list stalls. */
	onStall?: ReductionPass<Context>[];
	/** Cleanup performed after an iteration makes progress. */
	cleanup?: (context: Context) => void;
}

/** Run an ordered pass list until neither it nor its stall passes progress. */
export function runFixpoint<Context>(
	context: Context,
	passes: readonly ReductionPass<Context>[],
	options: FixpointOptions<Context> = {},
): boolean {
	let changedAtAll = false;
	while (true) {
		let changed = false;
		let restart = false;
		for (const pass of passes) {
			const result = pass.run(context);
			if (!result) continue;
			changed = true;
			if (result === 'restart') {
				restart = true;
				break;
			}
		}
		if (!changed && options.onStall) {
			for (const pass of options.onStall) {
				const result = pass.run(context);
				if (!result) continue;
				changed = true;
				restart = result === 'restart';
				break;
			}
		}
		if (!changed) return changedAtAll;
		changedAtAll = true;
		options.cleanup?.(context);
		if (restart) continue;
	}
}
