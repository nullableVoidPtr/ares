import { parse } from '@babel/parser';
import traverse from '@babel/traverse';
import * as t from '@babel/types';
import { readFileSync } from 'node:fs';

export type GeneratedOutputIssueKind =
	| 'parse-error'
	| 'duplicate-declaration'
	| 'top-level-return'
	| 'unbound-register'
	| 'lifting-intrinsic'
	| 'hermes-internal';

export interface GeneratedOutputIssue {
	kind: GeneratedOutputIssueKind;
	message: string;
	line: number | null;
	column: number | null;
}

const GENERATED_REGISTER = /^r\d+_\d+$/;

interface ParserError extends Error {
	reasonCode?: string;
	loc?: {
		line: number;
		column: number;
	};
}

const SOURCE_HERMES_INTERNAL_MEMBERS = new Set([
	'enablePromiseRejectionTracker',
]);
type ParsedFile = t.File & { errors: unknown[] };

export function validateGeneratedOutput(
	code: string,
): GeneratedOutputIssue[] {
	let ast: ParsedFile;
	try {
		ast = parse(code, {
			sourceType: 'unambiguous',
			allowReturnOutsideFunction: true,
			errorRecovery: true,
			plugins: ['v8intrinsic'],
		}) as ParsedFile;
	} catch (error) {
		return [parserIssue(asParserError(error))];
	}

	try {
		const issues = ast.errors.map((error) =>
			parserIssue(asParserError(error))
		);

		traverse(ast, {
			noScope: true,
			ReturnStatement(path) {
				if (path.findParent((parent) => parent.isFunction())) return;
				issues.push(nodeIssue(
					'top-level-return',
					'return statement is outside a function',
					path.node,
				));
			},
			V8IntrinsicIdentifier(path) {
				issues.push(nodeIssue(
					'lifting-intrinsic',
					`unresolved lifting intrinsic "%${path.node.name}"`,
					path.node,
				));
			},
			MemberExpression(path) {
				if (
					!path.get('object').isIdentifier({ name: 'HermesInternal' })
				) {
					return;
				}
				if (
					!path.node.computed &&
					t.isIdentifier(path.node.property) &&
					SOURCE_HERMES_INTERNAL_MEMBERS.has(path.node.property.name)
				) return;
				issues.push(nodeIssue(
					'hermes-internal',
					`unresolved hermes-internal "${path.toString()}"`,
					path.node,
				));
			},
		});

		// Babel cannot reliably construct scopes for a recovered invalid AST. The
		// parser issues are already sufficient in that case.
		if (ast.errors.length === 0) {
			try {
				traverse(ast, {
					Identifier(path) {
						const name = path.node.name;
						if (
							!GENERATED_REGISTER.test(name) ||
							!path.isReferencedIdentifier() ||
							path.scope.hasBinding(name)
						) return;
						issues.push(nodeIssue(
							'unbound-register',
							`generated register "${name}" has no lexical binding`,
							path.node,
						));
					},
				});
			} catch (error) {
				const parserError = asParserError(error);
				if (!isDuplicateDeclaration(parserError)) throw error;
				issues.push(parserIssue(parserError));
			}
		}

		return deduplicateIssues(issues).toSorted(compareIssues);
	} finally {
		// Babel's global path/scope cache retains the entire parsed program. The
		// coverage harness validates many generated bundles in one process, so
		// leaving those entries alive makes each sample accumulate every prior AST.
		traverse.cache.clear();
	}
}

export function formatGeneratedOutputIssue(
	issue: GeneratedOutputIssue,
): string {
	const location = issue.line == null
		? ''
		: ` at ${issue.line}:${issue.column ?? 1}`;
	return `${issue.kind}${location}: ${issue.message}`;
}

function parserIssue(error: ParserError): GeneratedOutputIssue {
	return {
		kind: isDuplicateDeclaration(error)
			? 'duplicate-declaration'
			: 'parse-error',
		message: error.message.replace(/\s+\(\d+:\d+\)$/, ''),
		line: error.loc?.line ?? null,
		column: error.loc == null ? null : error.loc.column + 1,
	};
}

function nodeIssue(
	kind: GeneratedOutputIssueKind,
	message: string,
	node: t.Node,
): GeneratedOutputIssue {
	return {
		kind,
		message,
		line: node.loc?.start.line ?? null,
		column: node.loc == null ? null : node.loc.start.column + 1,
	};
}

function asParserError(error: unknown): ParserError {
	if (error instanceof Error) return error as ParserError;
	return new Error(String(error));
}

function isDuplicateDeclaration(error: ParserError): boolean {
	return error.reasonCode === 'VarRedeclaration' ||
		error.reasonCode === 'ParamDupe' ||
		/already been declared|duplicate (?:declaration|parameter)/i.test(
			error.message,
		);
}

function deduplicateIssues(
	issues: GeneratedOutputIssue[],
): GeneratedOutputIssue[] {
	const unique = new Map<string, GeneratedOutputIssue>();
	for (const issue of issues) {
		const key = [
			issue.kind,
			issue.line ?? '',
			issue.column ?? '',
			issue.message,
		].join(':');
		unique.set(key, issue);
	}
	return [...unique.values()];
}

function compareIssues(
	left: GeneratedOutputIssue,
	right: GeneratedOutputIssue,
): number {
	return (left.line ?? Number.MAX_SAFE_INTEGER) -
			(right.line ?? Number.MAX_SAFE_INTEGER) ||
		(left.column ?? Number.MAX_SAFE_INTEGER) -
			(right.column ?? Number.MAX_SAFE_INTEGER) ||
		left.kind.localeCompare(right.kind) ||
		left.message.localeCompare(right.message);
}

if (import.meta.main) {
	const path = process.argv[2];
	const issues = validateGeneratedOutput(readFileSync(path, 'utf-8'));
	if (issues.length > 0) {
		console.log(
			`generated output validation failed for ${path}:\n` +
				issues.map((issue) => `  ${formatGeneratedOutputIssue(issue)}`)
					.join('\n'),
		);
	}
}
