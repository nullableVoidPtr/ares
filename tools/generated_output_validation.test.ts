import { strict as assert } from 'node:assert';
import {
	type GeneratedOutputIssueKind,
	validateGeneratedOutput,
} from './generated_output_validation.ts';

function issueKinds(code: string): GeneratedOutputIssueKind[] {
	return validateGeneratedOutput(code).map((issue) => issue.kind);
}

Deno.test('generated output validation accepts bound registers and nested returns', () => {
	assert.deepEqual(
		validateGeneratedOutput(`
			function lifted(r1_1) {
				const r2_1 = r1_1;
				return r2_1;
			}
		`),
		[],
	);
});

Deno.test('generated output validation rejects returns outside functions', () => {
	assert.deepEqual(issueKinds('return 0;'), ['top-level-return']);
});

Deno.test('generated output validation rejects duplicate declarations', () => {
	assert.deepEqual(
		issueKinds('let r2_5; let r2_5;'),
		['duplicate-declaration'],
	);
});

Deno.test('generated output validation reports unrecoverable syntax errors', () => {
	assert.deepEqual(issueKinds('const = ;'), ['parse-error']);
});

Deno.test('generated output validation reports unbound generated registers', () => {
	assert.deepEqual(
		issueKinds('console.log(r8_1);'),
		['unbound-register'],
	);
	assert.deepEqual(
		issueKinds('const object = {}; object.r8_1;'),
		[],
	);
});

Deno.test('generated output validation rejects lifting-failure intrinsics', () => {
	const issues = validateGeneratedOutput(`
		%Phi(r1);
		%expectEnvironment(r2);
		%getFunctionById(1);
		%CreateGenerator();
		%DelegateYield(value);
	`);
	assert.deepEqual(
		issues.map((issue) => issue.kind),
		[
			'lifting-intrinsic',
			'lifting-intrinsic',
			'lifting-intrinsic',
			'lifting-intrinsic',
			'lifting-intrinsic',
		],
	);
});

Deno.test('generated output validation allows source Hermes rejection tracking', () => {
	assert.deepEqual(
		validateGeneratedOutput(
			'HermesInternal.enablePromiseRejectionTracker({});',
		),
		[],
	);
});

Deno.test('generated output validation rejects lowered Hermes protocols', () => {
	assert.deepEqual(
		issueKinds('HermesInternal.makeAsyncIterator(source);'),
		['hermes-internal'],
	);
});
