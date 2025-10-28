import * as t from '@babel/types';
import { SSAFunction, SSARegister, ssaRegisterEquals } from '../../ssa.ts';
import { StringRef } from '../../disassembly/instruction.ts';
// @ts-types="npm:@types/babel__generator"
import { default as _generate } from '@babel/generator';
// @ts-types="npm:@types/babel__traverse"
import { default as _traverse, NodePath } from '@babel/traverse';
import { HBCFile } from '../../parser/file.ts';
import { BlockAddr, FunctionExceptionHandler } from '../../disassembly/function.ts';
import { reduceSequence, reduceSimpleIf, reduceTryCatch } from './cfg.ts';
import { LiftedAST, IRBlock, liftSSABlocktoIR, extractFunctionRef } from '../ast.ts';
import { LiftError } from './../error.ts';
import mapEachBlocks from '../../utils/mapEachBlock.ts';

const traverse = _traverse.default;

function extractRegisterAssign(decn: NodePath<t.VariableDeclaration>) {
	if (decn.node.kind !== 'const') return;
	if (decn.node.declarations.length !== 1) return;
	const decl = decn.get('declarations.0');

	const id = decl.get('id');
	if (!id.isIdentifier()) return;
	const init = decl.get('init');
	if (!init.hasNode()) return;

	return {
		id,
		init,
	}

}

export class IRFunction {
	file: HBCFile
	ssa: SSAFunction;
	id: number;

	exceptionHandlers: FunctionExceptionHandler[];

	mergedBlocks: Map<BlockAddr, Set<BlockAddr>>;

	isGenerator = false;
	yieldingBlocks = new Map<BlockAddr, SSARegister>();
	yieldEndBlocks = new Map<BlockAddr, { destination: SSARegister; continuation: BlockAddr; return: BlockAddr; }>();
	// will be used later to structure any finally clauses
	returnBlocks = new Map<BlockAddr, SSARegister>();

	blocks = new Map<BlockAddr, IRBlock>();

	referencedFunctionIds = new Map<number, number>();

	constructor(file: HBCFile, ssa: SSAFunction) {
		this.file = file;
		this.ssa = ssa;
		this.id = this.ssa.id;

		this.exceptionHandlers = this.ssa.exceptionHandlers.map((exc) => ({...exc}));

		const { basicBlocks } = this.ssa;
		this.mergedBlocks = mapEachBlocks(basicBlocks, () => new Set());

		const startBlock = basicBlocks.get(0)!;
		if (startBlock.instructions[0].instruction === 'StartGenerator') {
			this.isGenerator = true;
		}

		if (this.isGenerator) {
			for (const [addr, block] of basicBlocks) {
				if (block.ssaInstructions[0].instruction == 'ResumeGenerator') {
					const destination = block.ssaInstructions[0].defs.destination;
					const jmp = block.ssaInstructions[1];
					if (jmp?.instruction != 'JmpTrue') throw new Error();

					const returnAddress = block.consequentAddresses[1];
					this.yieldEndBlocks.set(addr, {
						destination,
						continuation: block.consequentAddresses[0],
						return: returnAddress,
					});

					this.returnBlocks.set(returnAddress, destination);
				} else {
					const savePoints = block.ssaInstructions.reduce((acc, { instruction }, i) => {
						if (instruction == 'SaveGenerator') acc.push(i);
						return acc;
					}, new Array<number>());
					if (savePoints.length === 0) continue;
					if (savePoints.length > 1) throw new Error();
					
					const retInst = block.ssaInstructions[savePoints[0] + 1]
					if (retInst?.instruction != 'Ret') throw new Error();
					this.yieldingBlocks.set(addr, retInst.uses.argument);
				}
			}
		}

		for (const [addr, block] of basicBlocks) {
			if (this.yieldEndBlocks.has(addr) || this.returnBlocks.has(addr)) continue;

			this.blocks.set(addr, liftSSABlocktoIR(this, block));
		}

		if (this.isGenerator) {
			for (const addr of [0, ...this.yieldingBlocks.keys()]) {
				const block = this.blocks.get(addr);
				if (block?.consequentAddresses?.length !== 1) throw new LiftError('bruh');

				const endInfo = this.yieldEndBlocks.get(block.consequentAddresses[0]);
				if (!endInfo) throw new LiftError('Uncorresponding end error');

				const returnBlock = basicBlocks.get(endInfo.return);
				if (!returnBlock) throw new LiftError('Missing .return handler');
				
				if (returnBlock?.ssaInstructions.length === 2) {
					const [compGen, ret] = returnBlock?.ssaInstructions;
					if (compGen.instruction !== 'CompleteGenerator') throw new LiftError('');
					if (ret.instruction !== 'Ret' || !ssaRegisterEquals(endInfo.destination, ret.uses.argument)) throw new LiftError('');

					block.consequentAddresses = [endInfo.continuation];
					continue;
				}

				throw new LiftError('');
			}
		}

		let changed;
		do {
			changed = false;
			changed = reduceSequence(this) || changed;
			changed = reduceSimpleIf(this) || changed;
			changed = reduceTryCatch(this) || changed;
		} while (changed);
	
		const wrappedEntry = t.file(t.program(<t.Statement[]>this.blocks.get(0)!.body)); 
		
		if (this.blocks.size === 1) {
			// TODO: even on improperly structure ones, traverse on each block and use live-out analysis to avoid changing semantics
			let changed = false;
			do {
				changed = false;
				traverse(wrappedEntry, {
					VariableDeclaration: {
						exit(decn) {
							const assign = extractRegisterAssign(decn);
							if (!assign) return;

							const { id, init } = assign;
							const binding = decn.scope.getBinding(id.node.name);
							if (!binding?.constant) return;
							if (!(init.isPure() || init.node.extra?.isConst)) {
								if (binding.referencePaths.length === 0) {
									decn.replaceWith(init);
									changed = true;
									return;
								}
								if (binding.references !== 1) return;
							}

							for (const ref of binding.referencePaths) {
								ref.replaceWith(t.cloneNode(init.node, true));
							}

							decn.remove();
							changed = true;
						},
					},
					CallExpression: {
						enter(call) {
							const callee = call.get('callee');
							if (callee.isV8IntrinsicIdentifier({ name: 'TryGetById' }))  {
								const args = call.node.arguments;
								if (args.length !== 2) return;

								const [g, id] = args;
								if (!t.isIdentifier(g, { name: 'global' })) return;
								if (!t.isStringLiteral(id)) return;
								
								call.replaceWith(t.identifier(id.value));
								call.node.extra = { isReferencedGlobal: true };
								changed = true;
							} else if (callee.isV8IntrinsicIdentifier({ name: 'ReifyArguments' })) {
								if (!t.isIdentifier(call.node.arguments[0], { name: 'undefined' })) return;
								call.replaceWith(t.identifier('arguments'));
							}
						},
						exit(call) {
							const callee = call.get('callee');
							if (callee.isMemberExpression({ computed: false }) && callee.get('property').isIdentifier({ name: 'call' })) {
								const func = callee.get('object');
								const args = call.node.arguments;

								if (func.node.extra?.isReferencedGlobal || func.node.extra?.isBuiltin || (func.isMemberExpression() && t.isIdentifier(func.node.object, { name: 'global' }))) {
									if (args.length > 1 && !t.isIdentifier(args[0], { name: 'undefined' })) return;

									call.replaceWith(t.callExpression(
										func.node,
										args.slice(1),
									))[0].skip();
									changed = true;
								} else if (func.isMemberExpression()) {
									const object = func.get('object');
									if (!object.isIdentifier()) return;
									if (args.length > 1 && !t.isIdentifier(args[0], { name: object.node.name })) return;

									call.replaceWith(t.callExpression(
										func.node,
										args.slice(1),
									))[0].skip();
									changed = true;
								}
							}
						},
					},
					ReturnStatement(ret) {
						if (t.isIdentifier(ret.node.argument, { name: 'undefined' })) {
							ret.node.argument = undefined;
							changed = true;
						}
					}
				});
				traverse.cache.clearScope();
			} while (changed);

			traverse(wrappedEntry, {
				CallExpression(call) {
					if (!t.isV8IntrinsicIdentifier(call.node.callee, { name: 'getFunctionById' })) return;

					const index = call.node.arguments[0];
					if (!t.isNumericLiteral(index)) throw new LiftError('Unexpected call to %getFunctionById', { functionId: this.id });

					this.referencedFunctionIds.set(
						index.value,
						(this.referencedFunctionIds.get(index.value) ?? 0) + 1
					);
				},
			}, undefined, this);

			const last = <t.Statement>this.blocks.get(0)!.body.at(-1);
			if (t.isReturnStatement(last) && !last.argument) {
				this.blocks.get(0)!.body.pop();
			}
		}
	}

	get name() { return this.ssa.name; }
	get paramCount() { return this.ssa.paramCount; }

	predecessorsOf(target: BlockAddr) {
		const predecessors = new Set<BlockAddr>();
		for (const [addr, block] of this.blocks) {
			if (block.consequentAddresses.includes(target)) {
				predecessors.add(addr);
			}
		}
		for (const { tryStart, catchOffset } of this.exceptionHandlers) {
			if (catchOffset === target) {
				predecessors.add(tryStart);
			}
		}

		return predecessors;
	}

	markMergedBlocks(parentAddr: BlockAddr, childAddr: BlockAddr) {
		this.blocks.delete(childAddr);
		this.mergedBlocks.set(parentAddr,
			this.mergedBlocks.get(parentAddr)!.union(
				this.mergedBlocks.get(childAddr) ?? new Set(),
			)
		);
		this.mergedBlocks.delete(childAddr);
	}

	fromIdentifierRef(ref: StringRef) {
		const id: LiftedAST<t.Identifier> = t.identifier(this.file.getIdentifier(ref.stringTableIndex));
		id.extra = { ref };
		
		return id;
	}

	fromStringRef(ref: StringRef) {
		const id: LiftedAST<t.StringLiteral> = t.stringLiteral(this.file.getString(ref.stringTableIndex));
		id.extra = { ref };
		
		return id;
	}

	getBuiltin(builtinNo: number) {
		const builtin = t.cloneNode(this.file.versionInfo.builtins[builtinNo], true);
		builtin.extra = { isBuiltin: true };

		return builtin;
	}

	getParam(paramIndex: number) {
		return t.identifier(`_param_${this.id}_${paramIndex}_`);
	}

	getFunctionExpr() {
		if (this.blocks.size > 1) throw new LiftError('Body is not structured');
		const params: t.Identifier[] = [];
		for (let i = 0; i < this.paramCount; i++) {
			params.push(this.getParam(i));
		}

		const body = <t.Statement[]>this.blocks.get(0)!.body.slice();

		const envDecls: t.VariableDeclarator[] = [];
		for (let i = 0; i < this.ssa.envSize; i++) {
			envDecls.push(t.variableDeclarator(
				t.identifier(`_env_${this.id}_${i}`),
			));
		}

		if (envDecls.length) {
			body.unshift(
				t.variableDeclaration('var', envDecls)
			);
		}

		return t.functionExpression(
			this.name ? t.identifier(this.name) : null,
			params,
			t.blockStatement(body),
			this.isGenerator,
		)
	}

	analyseGeneratorClosure() {
		if (this.blocks.size > 1) return;

		const body = <t.Statement[]>this.blocks.get(0)!.body;
		if (body.length !== 1) return;

		const ret = body[0];
		if (!t.isReturnStatement(ret)) return;

		const arg = ret.argument;
		if (!t.isCallExpression(arg) || !t.isV8IntrinsicIdentifier(arg.callee, { name: 'CreateGenerator' })) return;

		if (arg.arguments.length !== 2) return;
		const [env, funcRefArg] = arg.arguments;
		if (!t.isCallExpression(env) || !t.isV8IntrinsicIdentifier(env.callee, { name: 'CreateEnvironment' })) return;

		return extractFunctionRef(funcRefArg);
	}

	analyseAsyncClosure() {
		if (this.blocks.size > 1) return;

		const body = <t.Statement[]>this.blocks.get(0)!.body;
		if (body.length !== 2) return;

		const [env, ret] = body;
		if (!t.isExpressionStatement(env) || !t.isCallExpression(env.expression)) return;
		if (!t.isV8IntrinsicIdentifier(env.expression.callee, { name: 'CreateEnvironment' })) return;
		if (!t.isReturnStatement(ret)) return;

		const arg = ret.argument;
		if (!t.isCallExpression(arg) || !arg.callee.extra?.isBuiltin || !t.matchesPattern(arg.callee, ['HermesInternal', 'spawnAsync'])) return;

		if (arg.arguments.length !== 3) return;
		const [genClosureRef, thisRef, argumentsRef] = arg.arguments;
		if (!t.isThisExpression(thisRef)) return;
		if (!t.isIdentifier(argumentsRef, { name: 'arguments' })) return;

		if (!t.isCallExpression(genClosureRef) || !t.isV8IntrinsicIdentifier(genClosureRef.callee, { name: 'CreateGeneratorClosure' })) return;

		return extractFunctionRef(genClosureRef.arguments[0]);
	}
}
