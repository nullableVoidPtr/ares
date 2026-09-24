import path from 'node:path';
import * as t from '@babel/types';
import generate from '@babel/generator';
import traverse, { Binding, NodePath } from '@babel/traverse';
import { callArgsFromArrayExpression } from '../../function/utils.ts';

export interface MetroModuleExtractionOptions {
	outputDir: string;
	manifestFile?: string | false;
	replaceWithImports?: boolean;
	importPrefix?: string;
	keepModuleCalls?: boolean;
	moduleFormat?: 'factory' | 'metro';
}

export interface ExtractedMetroModule {
	id: string;
	name?: string;
	dependencies?: unknown[];
	path: string;
}

export type MetroDefineStatement = t.ExpressionStatement & {
	expression: t.CallExpression;
};

/**
 * A single module ready to be transformed and written out. Produced on the main
 * thread by {@link planMetroModuleExtraction}; the `stmt` AST node is structured-
 * cloneable, so a task can be posted to a worker as-is (the lifted `.extra`
 * markers and comments survive the clone).
 */
export interface MetroModuleTask {
	moduleId: string;
	moduleName?: string;
	dependencies?: unknown[];
	path: string;
	stmt: MetroDefineStatement;
}

export interface IncrementalMetroExtractionResult {
	extracted: boolean;
	replacement: t.Statement;
}

export interface IncrementalMetroExtractor {
	extractStatement(
		stmt: MetroDefineStatement,
	): IncrementalMetroExtractionResult;
	extractProgram(program: t.Program): void;
	finish(): void;
}

function metroModuleId(arg: t.Node | undefined) {
	if (t.isNumericLiteral(arg) || t.isStringLiteral(arg)) {
		return String(arg.value);
	}
}

function literalArrayValue(node: t.Node | undefined): unknown[] | undefined {
	if (!t.isArrayExpression(node)) return;
	const values: unknown[] = [];
	for (const element of node.elements) {
		if (element == null) {
			values.push(null);
		} else if (t.isNumericLiteral(element) || t.isStringLiteral(element)) {
			values.push(element.value);
		} else {
			return;
		}
	}
	return values;
}

function uniqueModuleFileName(
	moduleId: string,
	moduleName: string | undefined,
	used: Set<string>,
) {
	const base = moduleName ?? `module_${moduleId}`;
	if (!used.has(base)) {
		used.add(base);
		return base;
	}

	let candidate = `${base}.js`;
	for (let i = 0; used.has(candidate); i++) {
		candidate = `${base}_${i}.js`;
	}

	used.add(candidate);
	return candidate;
}

export function isMetroDefineStatement(
	stmt: t.Statement,
): stmt is MetroDefineStatement {
	if (!t.isExpressionStatement(stmt)) return false;
	const expr = stmt.expression;
	if (!t.isCallExpression(expr)) return false;
	return t.isIdentifier(expr.callee, { name: '__d' });
}

function constAliasFromRef(
	ref: NodePath<t.Identifier>,
): Binding | undefined {
	const declarator = ref.parentPath;
	if (!declarator?.isVariableDeclarator()) return;

	if (declarator.get('init') !== ref) return;

	const id = declarator.get('id');
	if (!id.isIdentifier()) return;

	const declaration = declarator.parentPath;
	if (!declaration?.isVariableDeclaration({ kind: 'const' })) return;

	const alias = declarator.scope.getBinding(id.node.name);
	if (alias?.identifier !== id.node) return;
	if (!alias.constant) return;

	return alias;
}

export function constAliasesOf(binding: Binding): Binding[] {
	const out: Binding[] = [];
	const seen = new Set<Binding>([binding]);
	const queue: Binding[] = [binding];

	for (let i = 0; i < queue.length; i++) {
		const current = queue[i];

		for (const ref of current.referencePaths) {
			if (!ref.isIdentifier()) continue;

			const alias = constAliasFromRef(ref);
			if (!alias || seen.has(alias)) continue;

			seen.add(alias);
			out.push(alias);
			queue.push(alias);
		}
	}

	return out;
}

const metroFactoryParameterNames = [
	'global',
	'_$$_REQUIRE',
	'_$$_IMPORT_DEFAULT',
	'_$$_IMPORT_ALL',
	'module',
	'exports',
	'_dependencyMap',
] as const;

function liftFactory(factory: t.FunctionExpression): t.Program {
	const wrapped = t.file(t.program([t.exportDefaultDeclaration(factory)]));

	const state = {
		paramsRenamed: false,
		deadFactoryParams: false,
	};
	traverse(
		wrapped,
		{
			FunctionExpression(func) {
				if (func.node !== factory) return;

				const params = func.get(`params`);
				if (params.length !== metroFactoryParameterNames.length) {
					func.skip();
					return;
				}

				this.paramsRenamed = true;
				for (let i = 0; i < metroFactoryParameterNames.length; i++) {
					const param = params[i];
					const newName = metroFactoryParameterNames[i];
					if (!param.isIdentifier()) {
						this.paramsRenamed = false;
						continue;
					}
					if (newName === 'global') {
						const binding = param.scope.getBinding(param.node.name);
						if (!binding) {
							this.paramsRenamed = false;
							continue;
						}
						param.node.name = newName;
						for (const ref of binding.referencePaths) {
							ref.replaceWith(t.identifier('global'));
						}

						continue;
					}

					const binding = param.scope.getBinding(param.node.name);
					if (binding?.constant) {
						const aliases = constAliasesOf(binding);

						for (const alias of aliases) {
							for (const ref of alias.referencePaths) {
								binding.referencePaths.push(
									ref.replaceWith(
										t.identifier(param.node.name),
									)[0],
								);
							}

							alias.path.remove();
						}
					}

					try {
						func.scope.rename(param.node.name, newName);
					} catch {
						this.paramsRenamed = false;
					}
				}

				func.traverse({
					CallExpression(call) {
						if (
							!call.get('callee').isIdentifier({
								name: '_$$_REQUIRE',
							})
						) return;
						const args = call.get('arguments');
						if (args.length !== 2) return;
						if (
							!args[0].isMemberExpression() ||
							!args[0].get('object').isIdentifier({
								name: '_dependencyMap',
							})
						) return;
						const indexPath = args[0].get('property');
						if (!indexPath.isNumericLiteral()) return;
						const index = indexPath.node.value;

						let source: t.StringLiteral;
						if (args[1].isStringLiteral()) {
							source = t.cloneNode(args[1].node);
						} else {
							// TODO fetch fallback from dependencymap
							return;
						}

						// TODO: insert comment declaring which module ID
						// source = t.addComment(source, 'inner', 'module ID', false);
						const requireCall = t.callExpression(
							t.identifier('require'),
							[source],
						);
						requireCall.extra = {
							liftedFromRequireIndex: index,
						};
						call.replaceWith(requireCall);
					},
				}, this);

				func.scope.crawl();
				this.deadFactoryParams = this.paramsRenamed &&
					func.get('params').every((p) => {
						if (!p.isIdentifier()) return false;
						if (
							['global', 'module', 'exports'].includes(
								p.node.name,
							)
						) return true;

						const binding = p.scope.getBinding(p.node.name);
						if (!binding) return false;

						return !binding.referenced;
					});
				func.skip();
			},
			ExportDefaultDeclaration: {
				exit(exp) {
					const decl = exp.get('declaration');
					if (decl.node !== factory) return;
					if (!this.paramsRenamed || !this.deadFactoryParams) return;

					exp.replaceWithMultiple([
						...factory.body.body,
					]);
					exp.stop();
				},
			},
		},
		null,
		state,
	);

	traverse.cache.clear();

	return wrapped.program;
}

function metroModuleProgram(stmt: t.ExpressionStatement) {
	const expr = stmt.expression;
	if (!t.isCallExpression(expr)) return t.program([t.cloneNode(stmt, true)]);
	const factory = expr.arguments[0];
	if (!t.isFunctionExpression(factory)) {
		return t.program([t.cloneNode(stmt, true)]);
	}

	const func = t.cloneNode(factory, true);
	return liftFactory(func);
}

function metroReplacementStatement(
	moduleId: string,
	filePath: string,
	options: MetroModuleExtractionOptions,
) {
	if (options.replaceWithImports) {
		const prefix = options.importPrefix ?? './';
		const source = prefix.endsWith('/')
			? `${prefix}${filePath}`
			: `${prefix}/${filePath}`;
		return t.importDeclaration([], t.stringLiteral(source));
	}

	const marker = t.emptyStatement();
	t.addComment(
		marker,
		'leading',
		` Metro module ${moduleId} extracted to ${filePath} `,
	);
	return marker;
}

/**
 * Transform a single extracted module's factory into its standalone output and
 * generate code for it. This is the per-module transformation seam: heavier,
 * module-local passes belong here so they parallelise across workers.
 */
export function buildMetroModuleCode(
	stmt: MetroDefineStatement,
	options: MetroModuleExtractionOptions,
): string {
	const moduleProgram = options.moduleFormat === 'metro'
		? t.program([t.cloneNode(stmt, true)])
		: metroModuleProgram(stmt);
	return generate(moduleProgram).code + '\n';
}

function toManifestEntry(task: MetroModuleTask): ExtractedMetroModule {
	return {
		id: task.moduleId,
		name: task.moduleName,
		dependencies: task.dependencies,
		path: task.path,
	};
}

/**
 * Main-thread pass: rewrite `program.body`, replacing each extractable `__d`
 * module with its marker/import, and return the ordered list of modules to
 * transform and write. Filename assignment is order-dependent so it must happen
 * here, sequentially, before any parallel dispatch.
 */
function planMetroModuleExtraction(
	program: t.Program,
	options: MetroModuleExtractionOptions,
): MetroModuleTask[] {
	Deno.mkdirSync(options.outputDir, { recursive: true });

	const tasks: MetroModuleTask[] = [];
	const usedFileNames = new Set<string>();
	const replacementBody: t.Statement[] = [];

	for (const stmt of program.body) {
		if (!isMetroDefineStatement(stmt)) {
			replacementBody.push(stmt);
			continue;
		}

		const args = stmt.expression.arguments;
		const moduleId = metroModuleId(args[1]);
		if (moduleId == null) {
			replacementBody.push(stmt);
			continue;
		}

		const moduleName = t.isStringLiteral(args[3])
			? args[3].value
			: undefined;
		const filePath = path.join(
			options.outputDir,
			uniqueModuleFileName(
				moduleId,
				moduleName,
				usedFileNames,
			),
		);
		tasks.push({
			moduleId,
			moduleName,
			dependencies: literalArrayValue(args[2]),
			path: filePath,
			stmt,
		});

		if (options.keepModuleCalls) {
			replacementBody.push(stmt);
		} else {
			replacementBody.push(
				metroReplacementStatement(moduleId, filePath, options),
			);
		}
	}

	program.body = replacementBody;
	return tasks;
}

function writeMetroManifest(
	options: MetroModuleExtractionOptions,
	extracted: ExtractedMetroModule[],
) {
	const manifestFile = options.manifestFile === undefined
		? 'manifest.json'
		: options.manifestFile;
	if (manifestFile === false) return;
	Deno.writeTextFileSync(
		path.join(options.outputDir, manifestFile),
		`${JSON.stringify({ modules: extracted }, null, 2)}\n`,
	);
}

/**
 * Write Metro modules as soon as their factories have been composed. Keeping
 * filename and manifest state in this small session lets callers release each
 * module AST before composing the next one.
 */
export function createIncrementalMetroExtractor(
	options: MetroModuleExtractionOptions,
): IncrementalMetroExtractor {
	Deno.mkdirSync(options.outputDir, { recursive: true });
	const usedFileNames = new Set<string>();
	const extracted: ExtractedMetroModule[] = [];

	const extractStatement = (
		stmt: MetroDefineStatement,
	): IncrementalMetroExtractionResult => {
		const args = stmt.expression.arguments;
		const moduleId = metroModuleId(args[1]);
		if (moduleId == null) {
			return { extracted: false, replacement: stmt };
		}

		const moduleName = t.isStringLiteral(args[3])
			? args[3].value
			: undefined;
		const filePath = path.join(
			options.outputDir,
			uniqueModuleFileName(
				moduleId,
				moduleName,
				usedFileNames,
			),
		);
		Deno.mkdirSync(path.dirname(filePath), { recursive: true });
		Deno.writeTextFileSync(
			filePath,
			buildMetroModuleCode(stmt, options),
		);
		extracted.push({
			id: moduleId,
			name: moduleName,
			dependencies: literalArrayValue(args[2]),
			path: filePath,
		});

		return {
			extracted: true,
			replacement: options.keepModuleCalls
				? stmt
				: metroReplacementStatement(moduleId, filePath, options),
		};
	};

	return {
		extractStatement,
		extractProgram(program) {
			const replacementBody: t.Statement[] = [];
			for (const stmt of program.body) {
				if (
					!isMetroDefineStatement(stmt) ||
					stmt.expression.extra?.incrementalMetroExtracted
				) {
					replacementBody.push(stmt);
					continue;
				}
				replacementBody.push(extractStatement(stmt).replacement);
			}
			program.body = replacementBody;
		},
		finish() {
			writeMetroManifest(options, extracted);
		},
	};
}

/**
 * Extract Metro `__d` modules into individual files, transforming and writing
 * each one in-thread. The original (synchronous) extraction path.
 */
export function extractMetroModules(
	program: t.Program,
	options: MetroModuleExtractionOptions | undefined,
) {
	if (!options) return;
	const extractor = createIncrementalMetroExtractor(options);
	extractor.extractProgram(program);
	extractor.finish();
}

function defaultModuleWorkerCount() {
	return Math.max(1, (navigator.hardwareConcurrency ?? 2) - 1);
}

function chunkTasks(
	tasks: MetroModuleTask[],
	count: number,
): MetroModuleTask[][] {
	const chunks = Array.from({ length: count }, () => [] as MetroModuleTask[]);
	for (let i = 0; i < tasks.length; i++) {
		chunks[i % count].push(tasks[i]);
	}
	return chunks.filter((chunk) => chunk.length > 0);
}

export interface MetroModuleWorkerRequest {
	tasks: MetroModuleTask[];
	options: MetroModuleExtractionOptions;
}

export type MetroModuleWorkerMessage =
	| { type: 'progress'; moduleId: string }
	| { type: 'result' }
	| { type: 'error'; moduleId?: string; message: string; stack?: string };

function runMetroModuleWorker(
	tasks: MetroModuleTask[],
	options: MetroModuleExtractionOptions,
): Promise<void> {
	return new Promise((resolve, reject) => {
		const worker = new Worker(
			new URL('./metro_worker.ts', import.meta.url).href,
			{ type: 'module' },
		);
		worker.onmessage = (event: MessageEvent<MetroModuleWorkerMessage>) => {
			const message = event.data;
			if (message.type === 'progress') return;
			if (message.type === 'result') {
				worker.terminate();
				resolve();
				return;
			}
			worker.terminate();
			const prefix = message.moduleId == null
				? 'Metro module worker failed'
				: `Metro module worker failed while extracting module ${message.moduleId}`;
			const error = new Error(`${prefix}: ${message.message}`);
			if (message.stack) error.stack = message.stack;
			reject(error);
		};
		worker.onerror = (event) => {
			worker.terminate();
			reject(event.error ?? new Error(event.message));
		};
		worker.postMessage(
			{ tasks, options } satisfies MetroModuleWorkerRequest,
		);
	});
}

/**
 * Extract Metro `__d` modules into individual files, transforming and writing
 * each module across a pool of workers. The `program.body` rewrite and filename
 * assignment stay on the main thread; only the per-module transform, codegen
 * and file write are parallelised.
 */
export async function extractMetroModulesParallel(
	program: t.Program,
	options: MetroModuleExtractionOptions | undefined,
	workers?: number,
) {
	if (!options) return;
	const tasks = planMetroModuleExtraction(program, options);
	if (tasks.length === 0) {
		writeMetroManifest(options, []);
		return;
	}

	const requested = workers ?? defaultModuleWorkerCount();
	const count = Math.max(
		1,
		Math.min(tasks.length, Math.floor(requested) || 1),
	);
	const chunks = chunkTasks(tasks, count);
	await Promise.all(
		chunks.map((chunk) => runMetroModuleWorker(chunk, options)),
	);

	writeMetroManifest(options, tasks.map(toManifestEntry));
}
