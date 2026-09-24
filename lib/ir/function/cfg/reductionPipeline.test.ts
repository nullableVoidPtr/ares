import { strict as assert } from 'node:assert';
import { type ReductionPass, runFixpoint } from './reductionPipeline.ts';

Deno.test('reduction pipeline repeats ordered passes to a fixpoint', () => {
	const context = { value: 0, cleanupCount: 0 };
	const passes: ReductionPass<typeof context>[] = [{
		name: 'increment',
		run(state) {
			if (state.value === 3) return false;
			state.value++;
			return true;
		},
	}];

	assert.equal(
		runFixpoint(context, passes, {
			cleanup: (state) => state.cleanupCount++,
		}),
		true,
	);
	assert.equal(context.value, 3);
	assert.equal(context.cleanupCount, 3);
});

Deno.test('reduction pipeline restart skips later passes for the iteration', () => {
	const visits: string[] = [];
	const context = { restart: true };
	const passes: ReductionPass<typeof context>[] = [
		{
			name: 'restart',
			run(state) {
				visits.push('restart');
				if (!state.restart) return false;
				state.restart = false;
				return 'restart';
			},
		},
		{
			name: 'later',
			run() {
				visits.push('later');
				return false;
			},
		},
	];

	runFixpoint(context, passes);
	assert.deepEqual(visits, ['restart', 'restart', 'later']);
});

Deno.test('reduction pipeline runs stall passes only after ordinary passes stall', () => {
	const context = { ordinary: true, stalled: true };
	const visits: string[] = [];
	runFixpoint(context, [{
		name: 'ordinary',
		run(state) {
			visits.push('ordinary');
			if (!state.ordinary) return false;
			state.ordinary = false;
			return true;
		},
	}], {
		onStall: [{
			name: 'stalled',
			run(state) {
				visits.push('stalled');
				if (!state.stalled) return false;
				state.stalled = false;
				return true;
			},
		}],
	});
	assert.deepEqual(visits, [
		'ordinary',
		'ordinary',
		'stalled',
		'ordinary',
		'stalled',
	]);
});
