import { assert } from 'node:console';
import * as t from '@babel/types';
// @ts-types="npm:@types/babel__generator"
import { default as _generate } from '@babel/generator';
import { BigIntRef, FunctionId, FunctionRef, HermesEmpty, isStringRef, StringRef } from '../disassembly/instruction.ts';
import { SSABasicBlock, SSAInstruction, SSARegister } from '../ssa.ts';
import { IRFunction } from './function/mod.ts';
import { BlockAddr } from '../disassembly/function.ts';
import { LiftError } from './error.ts';

const generate = _generate.default;

export type LiftedExtra = Partial<{
	parentFunctionId: number;
	bytecodeAddress: number;

	isBuiltin: boolean;
	isConst: boolean;
	isDeclaredGlobal: boolean;
	isReferencedGlobal: boolean;

	ref: StringRef | FunctionRef | BigIntRef;
}>;
export type LiftedAST<T extends t.Node> = Pick<T, Exclude<keyof T, 'extra'>> & {
	extra?: LiftedExtra;
};

export interface IRBlock {
	address: BlockAddr;
	body: LiftedAST<t.Statement>[];
	branch?: LiftedAST<t.Expression>;
	consequentAddresses: BlockAddr[];
}


function registerAsIdentifier(register: SSARegister | undefined, extra?: LiftedExtra) {
	if (!register) throw new Error();

	const id: LiftedAST<t.Identifier> = t.identifier(`r${register.index}_${register.version}`);
	id.extra = extra;

	return id;
}

function declareConst(id: t.Identifier, init: t.Expression, extra?: LiftedExtra) {
	const decl: LiftedAST<t.VariableDeclaration> = t.variableDeclaration('const', [
		t.variableDeclarator(
			id,
			init,
		)
	]);
	decl.extra = extra;

	return decl;
}

function assignRegister(destination: SSARegister, expr: t.Expression, extra?: LiftedExtra) {
	const decl = declareConst(
		registerAsIdentifier(destination),
		expr,
	);
	decl.extra = extra;

	return decl;
}

function asAssigningIntrinsic(instruction: string, destination: SSARegister, args: t.Expression[], extra?: LiftedExtra) {
	const call = t.callExpression(t.v8IntrinsicIdentifier(instruction), args);
	call.extra = extra;
	const assign = declareConst(
		registerAsIdentifier(destination),
		call,
	);
	assign.extra = extra;

	return assign;
}

function getFunctionRef(ref: FunctionRef, extra?: LiftedExtra) {
	const call = t.callExpression(
		t.v8IntrinsicIdentifier('getFunctionById'),
		[t.valueToNode(ref.functionId)],
	);
	call.extra = <LiftedExtra>{ ...extra, ref };

	return call
}

export function extractFunctionRef(funcRef: t.Node): FunctionId | undefined {
	if (!t.isCallExpression(funcRef)) return;
	if (!t.isV8IntrinsicIdentifier(funcRef.callee, { name: 'getFunctionById' })) return;

	const index = funcRef.arguments[0];
	if (!t.isNumericLiteral(index)) return;

	return index.value;
}

function memberById(func: IRFunction, instr: SSAInstruction & { uses: { object?: SSARegister; }, property: StringRef; }, extra?: LiftedExtra) {
	const memberExpr = t.memberExpression(
		registerAsIdentifier(instr.uses.object),
		func.fromIdentifierRef(instr.property),
	);
	memberExpr.extra = extra;

	return memberExpr;
}

export function liftSSABlocktoIR(func: IRFunction, block: SSABasicBlock): IRBlock {
	const body: LiftedAST<t.Statement>[] = []; 

	let branchStmt: t.Statement | undefined = undefined;
	for (let i = 0; i < block.ssaInstructions.length; i++) {
		const instr = block.ssaInstructions[i];
		if (instr.instruction == 'Phi') {
			body.push(asAssigningIntrinsic(instr.instruction, instr.destination, [...instr.sources.values()].map(r => registerAsIdentifier(r))))
			continue;
		}

		const extra: LiftedExtra = { parentFunctionId: func.id, bytecodeAddress: instr.functionLocalOffset };
		switch (instr.instruction) {
			case 'GetGlobalObject': {
				const g = t.identifier('global');
				g.extra = { isConst: true };
				body.push(assignRegister(instr.defs.destination, g, extra));
				break;
			}
			case 'DeclareGlobalVar': {
				const decl = t.variableDeclarator(func.fromIdentifierRef(instr.identifier))
				decl.extra = { ...extra, isDeclaredGlobal: true };
				const decn = t.variableDeclaration('var', [decl]);
				decn.extra = extra;

				body.push(decn);
				break;
			}
			case 'GetById': {
				body.push(assignRegister(instr.defs.destination, memberById(func, instr), extra));
				break;
			}
			case 'GetByVal': {
				body.push(assignRegister(instr.defs.destination, t.memberExpression(
					registerAsIdentifier(instr.uses.object),
					registerAsIdentifier(instr.uses.property),
				), extra));
				break;
			}
			case 'TryGetById': {
				body.push(asAssigningIntrinsic(instr.instruction, instr.defs.destination, [
					registerAsIdentifier(instr.uses.object),
					t.valueToNode(func.file.getIdentifier(instr.property.stringTableIndex))
				], extra))
				break;
			}

			case 'PutById': {
				const assign = t.expressionStatement(t.assignmentExpression('=',
					memberById(func, instr),
					registerAsIdentifier(instr.uses.value),
				));
				assign.extra = extra;

				body.push(assign);
				break;
			}

			case 'PutOwnByIndex': {
				const assign = t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier(instr.instruction),
					[
						registerAsIdentifier(instr.uses.object),
						t.valueToNode(instr.property),
						registerAsIdentifier(instr.uses.value),
					],
				));
				assign.extra = extra;

				body.push(assign);
				break;
			}

			case 'CreateEnvironment': {
				body.push(asAssigningIntrinsic(instr.instruction, instr.defs.destination, [], extra))
				break;
			}

			case 'GetEnvironment': {
				body.push(asAssigningIntrinsic(instr.instruction, instr.defs.destination, [t.valueToNode(instr.levelIndex)], { ...extra, isConst: true }))
				break;
			}

			case 'GetBuiltinClosure': {
				extra.isBuiltin = true;
				body.push(assignRegister(instr.defs.destination, func.getBuiltin(instr.builtinNo), extra))
				break;
			}

			case 'CreateThis': {
				body.push(asAssigningIntrinsic(instr.instruction, instr.defs.destination, [
					registerAsIdentifier(instr.uses.prototype),
					registerAsIdentifier(instr.uses.constructorRef),
				], extra))
				break;
			}
			case 'SelectObject': {
				body.push(asAssigningIntrinsic(instr.instruction, instr.defs.destination, [
					registerAsIdentifier(instr.uses.thisObject),
					registerAsIdentifier(instr.uses.constructorReturnValue),
				], extra))
				break;
			}

			case 'LoadThisNS': {
				body.push(assignRegister(instr.defs.destination, t.thisExpression(), extra))
				break;
			}

			case 'CreateClosure':
			case 'CreateGeneratorClosure':
			case 'CreateAsyncClosure': {
				body.push(asAssigningIntrinsic(instr.instruction, instr.defs.destination, [getFunctionRef(instr.function)], extra))
				break;
			}

			case 'Mov': {
				body.push(assignRegister(instr.defs.destination, registerAsIdentifier(instr.uses.source), extra))
				break;
			}

			case 'LoadConst': {
				const { value } = instr;
				let valueNode: t.Expression;
				if (isStringRef(value)) {
					valueNode = func.fromStringRef(value);
				} else if (value === HermesEmpty) {
					valueNode = t.identifier('__hermes_empty__');
				} else {
					valueNode = t.valueToNode(value);
				}
				valueNode.extra = { isConst: true };
				body.push(assignRegister(instr.defs.destination, valueNode, extra))

				break;
			}

			case 'NewArray': {
				body.push(assignRegister(instr.defs.destination, t.newExpression(
					t.identifier('Array'),
					[t.valueToNode(instr.size)],
				), extra));
				break;
			}

			case 'CreateRegExp': {
				body.push(assignRegister(instr.defs.destination, t.regExpLiteral(
					func.file.getString(instr.pattern.stringTableIndex),
					func.file.getString(instr.flags.stringTableIndex),
				), extra))
				break;
			}

			case 'LoadFromEnvironment': {
				body.push(asAssigningIntrinsic(instr.instruction, instr.defs.destination, [registerAsIdentifier(instr.uses.environment), t.valueToNode(instr.slotIndex)], extra))
				break;
			}

			case 'StoreNPToEnvironment':
			case 'StoreToEnvironment': {
				const stmt = t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier(instr.instruction),
					[registerAsIdentifier(instr.uses.environment!), t.valueToNode(instr.slotIndex), registerAsIdentifier(instr.uses.value)]
				));
				stmt.extra = extra;

				body.push(stmt);
				break;
			}

			case 'Call':
			case 'Construct': {
				body.push(assignRegister(instr.defs.destination, t.callExpression(
					t.memberExpression(
						registerAsIdentifier(instr.uses.closure),
						t.identifier('call'),
					),
					instr.uses.arguments.map(a => registerAsIdentifier(a)),
				), extra))
				break;
			}

			case 'CreateGenerator': {
				body.push(asAssigningIntrinsic(instr.instruction, instr.defs.destination, [registerAsIdentifier(instr.uses.environment), getFunctionRef(instr.function)], extra));
				break;
			}

			case 'LoadParam': {
				const param = instr.parameterIndex >= func.paramCount ? 
					t.memberExpression(
						t.identifier('arguments'),
						t.valueToNode(instr.parameterIndex),
						true,
					) : func.getParam(instr.parameterIndex)
				body.push(assignRegister(instr.defs.destination,
					param,
					extra,
				))
				break;
			}

			case 'Ret': {
				const stmt = t.returnStatement(registerAsIdentifier(instr.uses.argument));
				stmt.extra = extra;

				body.push(stmt);
				break;
			}


			case 'Not': {
				body.push(assignRegister(instr.defs.destination!, t.unaryExpression('!',
					registerAsIdentifier(instr.uses.argument),
					true,
				), extra))
				break;
			}

			case 'Negate': {
				body.push(assignRegister(instr.defs.destination, t.unaryExpression('-',
					registerAsIdentifier(instr.uses.argument),
					true,
				), extra))
				break;
			}

			case 'Add': {
				body.push(assignRegister(instr.defs.destination, t.binaryExpression('+',
					registerAsIdentifier(instr.uses.left),
					registerAsIdentifier(instr.uses.right),
				), extra))
				break;
			}

			case 'Sub': {
				body.push(assignRegister(instr.defs.destination, t.binaryExpression('-',
					registerAsIdentifier(instr.uses.left),
					registerAsIdentifier(instr.uses.right),
				), extra))
				break;
			}

			case 'Mul': {
				body.push(assignRegister(instr.defs.destination, t.binaryExpression('*',
					registerAsIdentifier(instr.uses.left),
					registerAsIdentifier(instr.uses.right),
				), extra))
				break;
			}

			case 'Div': {
				body.push(assignRegister(instr.defs.destination, t.binaryExpression('/',
					registerAsIdentifier(instr.uses.left),
					registerAsIdentifier(instr.uses.right),
				), extra))
				break;
			}

			case 'Eq': {
				body.push(assignRegister(instr.defs.destination, t.binaryExpression('==',
					registerAsIdentifier(instr.uses.left),
					registerAsIdentifier(instr.uses.right),
				), extra))
				break;
			}

			case 'StrictEq': {
				body.push(assignRegister(instr.defs.destination, t.binaryExpression('===',
					registerAsIdentifier(instr.uses.left),
					registerAsIdentifier(instr.uses.right),
				), extra))
				break;
			}

			case 'Jmp':
				break;

			case 'JmpFalse':
			case 'JmpTrue':
			case 'JmpUndefined': {
				if (branchStmt != null) throw new LiftError('Non-terminating jmp');

				let predicate: t.Expression = registerAsIdentifier(instr.uses.predicate);
				if (instr.instruction == 'JmpFalse') {
					predicate = t.unaryExpression('!', predicate, true);
				} else if (instr.instruction == 'JmpUndefined') {
					predicate = t.binaryExpression('===', predicate, t.identifier('undefined'));
				}

				body.push(branchStmt = t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('JmpIf'),
					[
						predicate,
						t.valueToNode(block.consequentAddresses[1]), 
					],
				)));
				branchStmt.extra = extra;
				break;
			}

			case 'JLess':
			case 'JNotLess':
			case 'JLessEqual':
			case 'JNotLessEqual':
			case 'JGreater':
			case 'JNotGreater':
			case 'JGreaterEqual':
			case 'JNotGreaterEqual':
			case 'JEqual':
			case 'JNotEqual':
			case 'JStrictEqual':
			case 'JStrictNotEqual': {
				if (branchStmt != null) throw new LiftError('Non-terminating jmp');

				let predicate: t.Expression = t.binaryExpression(
					({
						'JLess': '<',
						'JNotLess': '<',
						'JLessEqual': '<=',
						'JNotLessEqual': '<=',
						'JGreater': '>',
						'JNotGreater': '>',
						'JGreaterEqual': '>=',
						'JNotGreaterEqual': '>=',
						'JEqual': '==',
						'JNotEqual': '==',
						'JStrictEqual': '===',
						'JStrictNotEqual': '===',
					} as const)[instr.instruction],
					registerAsIdentifier(instr.uses.left),
					registerAsIdentifier(instr.uses.right),
				);

				if ([
					'JNotLess',
					'JNotLessEqual',
					'JNotGreater',
					'JNotGreaterEqual',
					'JNotEqual',
					'JStrictNotEqual',
				].includes(instr.instruction)) {
					predicate = t.unaryExpression('!', predicate, true);
				}

				body.push(branchStmt = t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('JmpIf'),
					[
						predicate,
						t.valueToNode(block.consequentAddresses[1]), 
					],
				)));
				break;
			}

			case 'SaveGenerator': {
				const source = func.yieldingBlocks.get(block.address);
				if (!source) throw new Error();
				assert(block.ssaInstructions[++i].instruction == 'Ret');

				const { destination } = func.yieldEndBlocks.get(block.consequentAddresses[0])!;
				body.push(assignRegister(destination, t.yieldExpression(registerAsIdentifier(source)), extra))
				break;
			}

			case 'ReifyArguments': {
				body.push(asAssigningIntrinsic(instr.instruction, instr.defs.lazyLoad, [registerAsIdentifier(instr.uses.lazyLoad)], extra));
				break;
			}

			case 'Throw': {
				// exception binding to be handled later
				const throwStmt = t.throwStatement(
					registerAsIdentifier(instr.uses.exception),
				);
				throwStmt.extra = extra;
				body.push(throwStmt);
				break;
			}

			case 'Catch':
				// exception binding to be handled later
				body.push(asAssigningIntrinsic(instr.instruction, instr.defs.destination, [], extra));
				break;

			case 'StartGenerator':
			case 'CompleteGenerator':
				break;

			default:
				console.log(
					generate(
						t.blockStatement(
							body as t.Statement[]
						)
					).code
				)
				throw new Error(instr.instruction + ' ' + block.address);
		}
	}

	if (branchStmt) assert(body[body.length - 1] == branchStmt);

	let branch: t.Expression | undefined;
	if (branchStmt != null) {
		assert(body.pop() == branchStmt);
		t.assertCallExpression(branchStmt.expression);
		t.assertV8IntrinsicIdentifier(branchStmt.expression.callee, { name: 'JmpIf' });
		assert(branchStmt.expression.arguments.length === 2);

		t.assertExpression(branchStmt.expression.arguments[0]);
		branch = branchStmt.expression.arguments[0];
	};

	return {
		address: block.address,

		body,
		branch,
		consequentAddresses: block.consequentAddresses,
	};
}

