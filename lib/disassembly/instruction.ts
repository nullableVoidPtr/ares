import { getStackOffset, NamedStackVariables } from '../hbcConsts/stackFrameLayout.ts';
import { Reg8, Reg32, UInt8, UInt16, UInt32, UInt32 as Imm32, Double, Int8 as Addr8, Int32 as Addr32, StringRef8, StringRef16, StringRef32, FunctionRef16, FunctionRef32, BigIntRef16, BigIntRef32 } from '../utils/DataViewStream.ts';

function isType<T extends string>(o: unknown, type: T): o is { type: T } {
	if (typeof o != 'object' || o === null) return false;
	if (!('type' in o) || o.type != type) return false;

	return true;
}

export type RegisterIndex = number;
export interface Register {
	type: 'register';
	index: RegisterIndex;
};

export function asRegister(index: number): Register {
	return {
		type: 'register',
		index,
	}
}

export function isRegister(o: unknown): o is Register {
	if (!isType(o, 'register')) return false;
	if (!('index' in o) || typeof o.index != 'number') return false;

	return true;
}

export function checkRegister(o: unknown): Register {
	if (!isRegister(o)) throw Error();

	return o;
}

export type FunctionId = number;
export type FunctionRef = {
	type: 'function';
	functionId: FunctionId;
}

export function asFunctionRef(functionId: number): FunctionRef {
	return {
		type: 'function',
		functionId,
	};
}

export function isFunctionRef(o: unknown): o is FunctionRef {
	if (!isType(o, 'function')) return false;
	if (!('functionId' in o) || typeof o.functionId != 'number') return false;

	return true;
}

export function checkFunctionRef(o: unknown): FunctionRef {
	if (!isFunctionRef(o)) throw Error();

	return o;
}


export type StringRef = {
	type: 'string';
	stringTableIndex: number;
}

export function asStringRef(stringTableIndex: number): StringRef {
	return {
		type: 'string',
		stringTableIndex,
	};
}

export function isStringRef(o: unknown): o is StringRef {
	if (!isType(o, 'string')) return false;
	if (!('stringTableIndex' in o) || typeof o.stringTableIndex != 'number') return false;

	return true;
}

export function checkStringRef(o: unknown): StringRef {
	if (!isStringRef(o)) throw Error();

	return o;
}

export function checkImmediate(o: unknown): number {
	if (typeof o !== 'number') throw new Error();
	return o
}

export type BigIntRef = {
	type: 'bigint';
	bigintTableIndex: number;
}

export function asBigIntRef(bigintTableIndex: number): BigIntRef {
	return {
		type: 'bigint',
		bigintTableIndex,
	};
}

export function isBigIntRef(o: unknown): o is BigIntRef {
	if (!isType(o, 'bigint')) return false;
	if (!('stringTableIndex' in o) || typeof o.stringTableIndex != 'number') return false;

	return true;
}

export function checkBigIntRef(o: unknown): BigIntRef {
	if (!isBigIntRef(o)) throw Error();

	return o;
}


export const HermesEmpty: unique symbol = Symbol('Empty')

export type Operand = Register | StringRef | BigIntRef | FunctionRef | number | typeof HermesEmpty | void | null | boolean;

export enum InstructionLength {
	SHORT,
	NORMAL,
	LONG,
}

export enum InstructionType {
	NORMAL,
	NUMERIC,
}

export interface BaseInstruction {
	functionLocalOffset: number;
	length: InstructionLength;
	type: InstructionType;
}
export interface AssigningInstruction extends BaseInstruction {
	destination: Register;
}

export interface UnaryOperationInst extends AssigningInstruction {
	argument: Register;
}

export interface BinaryOperationInst extends AssigningInstruction {
	left: Register;
	right: Register;
}

export interface BranchInstruction extends BaseInstruction {
	relativeTarget: number;
}

export interface BranchingBinaryInstruction extends BranchInstruction {
	left: Register;
	right: Register;
}

export interface WASMSpecificInstruction extends BaseInstruction {
	isWASM: true;
}

export interface UnreachableInst extends BaseInstruction {
	instruction: 'Unreachable'
}

export interface NewObjectWithBufferInst extends AssigningInstruction {
	instruction: 'NewObjectWithBuffer';
 	sizeHint: number;
	noOfStaticElements: number;
	objectKeyBufferIndex: number;
	objectValueBufferIndex: number;
}

export interface NewObjectInst extends AssigningInstruction { instruction: 'NewObject' }

export interface NewObjectWithParentInst extends AssigningInstruction {
	instruction: 'NewObjectWithParent';
 	parent: Register;
}

export interface NewArrayWithBufferInst extends AssigningInstruction {
	instruction: 'NewArrayWithBuffer';
 	sizeHint: number;
	noOfStaticElements: number;
	arrayBufferIndex: number;
}

export interface NewArrayInst extends AssigningInstruction {
	instruction: 'NewArray';
 	size: number;
}

export interface MovInst extends AssigningInstruction {
	instruction: 'Mov';
 	source: Register;
}

export interface IncInst extends UnaryOperationInst { instruction: 'Inc'}
export interface DecInst extends UnaryOperationInst { instruction: 'Dec'}
export interface NegateInst extends UnaryOperationInst { instruction: 'Negate' }
export interface NotInst extends UnaryOperationInst { instruction: 'Not' }
export interface BitNotInst extends UnaryOperationInst { instruction: 'BitNot' }
export interface TypeOfInst extends UnaryOperationInst { instruction: 'TypeOf' }
export interface EqInst extends BinaryOperationInst { instruction: 'Eq' }
export interface StrictEqInst extends BinaryOperationInst { instruction: 'StrictEq' }
export interface NeqInst extends BinaryOperationInst { instruction: 'Neq' }
export interface StrictNeqInst extends BinaryOperationInst { instruction: 'StrictNeq' }
export interface LessInst extends BinaryOperationInst { instruction: 'Less' }
export interface LessEqInst extends BinaryOperationInst { instruction: 'LessEq' }
export interface GreaterInst extends BinaryOperationInst { instruction: 'Greater' }
export interface GreaterEqInst extends BinaryOperationInst { instruction: 'GreaterEq' }
export interface AddInst extends BinaryOperationInst { instruction: 'Add' }
export interface MulInst extends BinaryOperationInst { instruction: 'Mul' }
export interface DivInst extends BinaryOperationInst { instruction: 'Div' }
export interface ModInst extends BinaryOperationInst { instruction: 'Mod' }
export interface SubInst extends BinaryOperationInst { instruction: 'Sub' }
export interface LShiftInst extends BinaryOperationInst { instruction: 'LShift' }
export interface RShiftInst extends BinaryOperationInst { instruction: 'RShift' }
export interface URShiftInst extends BinaryOperationInst { instruction: 'URShift' }
export interface BitAndInst extends BinaryOperationInst { instruction: 'BitAnd' }
export interface BitXorInst extends BinaryOperationInst { instruction: 'BitXor' }
export interface BitOrInst extends BinaryOperationInst { instruction: 'BitOr' }
export interface InstanceOfInst extends BinaryOperationInst { instruction: 'InstanceOf' }
export interface IsInInst extends BinaryOperationInst { instruction: 'IsIn' }

export interface GetEnvironmentInst extends AssigningInstruction {
	instruction: 'GetEnvironment';
 	levelIndex: number;
}

export interface StoreToEnvironmentInst extends BaseInstruction {
	instruction: 'StoreToEnvironment';
 	environment: Register;
	slotIndex: number;
	value: Register;
}

export interface StoreNPToEnvironmentInst extends BaseInstruction {
	instruction: 'StoreNPToEnvironment';
 	environment: Register;
	slotIndex: number;
	value: Register;
}

export interface LoadFromEnvironmentInst extends AssigningInstruction {
	instruction: 'LoadFromEnvironment';
 	environment: Register;
	slotIndex: number;
}

export interface GetGlobalObjectInst extends AssigningInstruction { instruction: 'GetGlobalObject' }

export interface GetNewTargetInst extends AssigningInstruction { instruction: 'GetNewTarget' }

export interface CreateEnvironmentInst extends AssigningInstruction { instruction: 'CreateEnvironment' }
export interface CreateInnerEnvironmentInst extends AssigningInstruction { instruction: 'CreateInnerEnvironment' }

export interface DeclareGlobalVarInst extends BaseInstruction {
	instruction: 'DeclareGlobalVar';
 	identifier: StringRef;
}

export interface GetByIdInst extends AssigningInstruction {
	instruction: 'GetById';
 	object: Register;
	cacheIndex: number;
	property: StringRef;
}

export interface TryGetByIdInst extends AssigningInstruction {
	instruction: 'TryGetById';
 	object: Register;
	cacheIndex: number;
	property: StringRef;
}

export interface PutByIdInst extends BaseInstruction {
	instruction: 'PutById';
 	object: Register;
	value: Register;
	cacheIndex: number;
	property: StringRef;
}

export interface TryPutByIdInst extends BaseInstruction {
	instruction: 'TryPutById';
 	object: Register;
	value: Register;
	cacheIndex: number;
	property: StringRef;
}

export interface PutNewOwnByIdInst extends BaseInstruction {
	instruction: 'PutNewOwnById';
 	object: Register;
	value: Register;
	property: StringRef;
}

export interface PutNewOwnNEByIdInst extends BaseInstruction {
	instruction: 'PutNewOwnNEById';
 	object: Register;
	value: Register;
	property: StringRef;
}

export interface PutOwnByIndexInst extends BaseInstruction {
	instruction: 'PutOwnByIndex';
 	object: Register;
	value: Register;
	property: number;
}

export interface PutOwnByValInst extends BaseInstruction {
	instruction: 'PutOwnByVal';
 	object: Register;
	value: Register;
	property: Register;
	enumerable: boolean;
}

export interface DelByIdInst extends AssigningInstruction {
	instruction: 'DelById';
 	object: Register;
	property: StringRef;
}

export interface GetByValInst extends AssigningInstruction {
	instruction: 'GetByVal';
 	object: Register;
	property: Register;
}

export interface PutByValInst extends BaseInstruction {
	instruction: 'PutByVal';
 	object: Register;
	property: Register;
	value: Register;
}

export interface DelByValInst extends AssigningInstruction {
	instruction: 'DelByVal';
 	object: Register;
	property: Register;
}

export interface PutOwnGetterSetterByValInst extends BaseInstruction {
	instruction: 'PutOwnGetterSetterByVal';
 	object: Register;
	property: Register;
	getter: Register;
	setter: Register;
	enumerable: boolean;
}

export interface GetPNameListInst extends AssigningInstruction {
	instruction: 'GetPNameList';
 	object: Register;
	index: Register;
	propertyListSize: Register;
}

export interface GetNextPNameInst extends AssigningInstruction {
	instruction: 'GetNextPName';
 	object: Register;
	index: Register;
	propertyListSize: Register;
}

export interface CallInst extends AssigningInstruction {
	instruction: 'Call';
 	closure: Register;
	argumentCount?: number;

	arguments: Register[];
}

export interface ConstructInst extends AssigningInstruction {
	instruction: 'Construct';
 	closure: Register;
	argumentCount: number;

	arguments: Register[];
}

export interface CallDirectInst extends AssigningInstruction {
	instruction: 'CallDirect';
 	argumentCount: number;
	function: FunctionRef;
}

export interface CallBuiltinInst extends AssigningInstruction {
	instruction: 'CallBuiltin';
 	builtinNo: Register;
	argumentCount: number;
}

export interface GetBuiltinClosureInst extends AssigningInstruction {
	instruction: 'GetBuiltinClosure';
 	builtinNo: number;
}

export interface RetInst extends BaseInstruction {
	instruction: 'Ret';
 	argument: Register;
}

export interface CatchInst extends AssigningInstruction { instruction: 'Catch'; }

export interface DirectEvalInst extends AssigningInstruction {
	instruction: 'DirectEval';
 	code: Register;
	isStrict: boolean;
}

export interface ThrowInst extends BaseInstruction {
	instruction: 'Throw';
 	exception: Register;
}

export interface ThrowIfEmptyInst extends AssigningInstruction {
	instruction: 'ThrowIfEmpty';
 	source: Register;
}

export interface ThrowIfUndefinedInst extends AssigningInstruction {
	instruction: 'ThrowIfUndefined';
 	source: Register;
}

export interface ThrowIfHasRestrictedGlobalPropertyInst extends AssigningInstruction {
	instruction: 'ThrowIfHasRestrictedGlobalProperty';
 	property: StringRef;
}

export interface DebuggerInst extends BaseInstruction { instruction: 'Debugger' }
export interface DebuggerCheckBreakInst extends BaseInstruction { instruction: 'DebuggerCheckBreak' }

export interface AsyncBreakCheckInst extends BaseInstruction { instruction: 'AsyncBreakCheck' }

export interface ProfilePointInst extends BaseInstruction {
	instruction: 'ProfilePoint';
 	profilePoint: number;
}

export interface CreateClosureInst extends AssigningInstruction {
	instruction: 'CreateClosure';
 	environment: Register;
	function: FunctionRef;
}

export interface CreateGeneratorClosureInst extends AssigningInstruction {
	instruction: 'CreateGeneratorClosure';
 	environment: Register;
	function: FunctionRef;
}

export interface CreateAsyncClosureInst extends AssigningInstruction {
	instruction: 'CreateAsyncClosure';
 	environment: Register;
	function: FunctionRef;
}

export interface CreateThisInst extends AssigningInstruction {
	instruction: 'CreateThis';
 	prototype: Register;
	constructorRef: Register;
}

export interface SelectObjectInst extends AssigningInstruction {
	instruction: 'SelectObject';
 	thisObject: Register;
	constructorReturnValue: Register;
}

export interface LoadParamInst extends AssigningInstruction {
	instruction: 'LoadParam';
 	parameterIndex: number;
}

export interface LoadConstInst extends AssigningInstruction {
	instruction: 'LoadConst';
 	value: number | StringRef | BigIntRef | typeof HermesEmpty | void | null | boolean;
}

export interface CoerceThisNSInst extends UnaryOperationInst { instruction: 'CoerceThisNS'; }

export interface LoadThisNSInst extends AssigningInstruction { instruction: 'LoadThisNS' }

export interface ToNumberInst extends UnaryOperationInst { instruction: 'ToNumber'; }

export interface ToNumericInst extends AssigningInstruction { instruction: 'ToNumeric'; }


export interface ToInt32Inst extends AssigningInstruction { instruction: 'ToInt32'; }

export interface AddEmptyStringInst extends AssigningInstruction { instruction: 'AddEmptyString'; }

export interface GetArgumentsByPropValInst extends AssigningInstruction {
	instruction: 'GetArgumentsByPropVal';
 	argumentsIndex: Register;
	lazyLoad: Register;
}

export interface GetArgumentsLengthInst extends AssigningInstruction {
	instruction: 'GetArgumentsLength';
 	lazyLoad: Register;
}

export interface ReifyArgumentsInst extends BaseInstruction {
	instruction: 'ReifyArguments';
 	lazyLoad: Register;
}

export interface CreateRegExpInst extends AssigningInstruction {
	instruction: 'CreateRegExp';
 	pattern: StringRef;
	flags: StringRef;
	regExpBytecodeIndex: number;
}

export interface SwitchImmInst extends BaseInstruction {
	instruction: 'SwitchImm';
 	discriminant: Register;
	jumpTableOffset: number;
	defaultJumpOffset: number;
	minValue: number;
	maxValue: number;
}

export interface StartGeneratorInst extends BaseInstruction { instruction: 'StartGenerator'; }

export interface ResumeGeneratorInst extends AssigningInstruction{
	instruction: 'ResumeGenerator';
	isReturn: Register;
}

export interface CompleteGeneratorInst extends BaseInstruction { instruction: 'CompleteGenerator'; }

export interface CreateGeneratorInst extends AssigningInstruction {
	instruction: 'CreateGenerator';
 	environment: Register;
	function: FunctionRef;
}

export interface IteratorBeginInst extends AssigningInstruction {
	instruction: 'IteratorBegin';
 	source: Register;
}

export interface IteratorNextInst extends AssigningInstruction {
	instruction: 'IteratorNext';
 	iterator: Register;
	sourceOrNext: Register;
}

export interface IteratorCloseInst extends BaseInstruction {
	instruction: 'IteratorClose';
 	iterator: Register;
	ignoreException: Register;
}

export interface JmpInst extends BranchInstruction { instruction: 'Jmp' }

export interface JmpTrueInst extends BranchInstruction {
	instruction: 'JmpTrue';
 	predicate: Register;
}

export interface JmpFalseInst extends BranchInstruction {
	instruction: 'JmpFalse';
 	predicate: Register;
}

export interface JmpUndefinedInst extends BranchInstruction {
	instruction: 'JmpUndefined';
 	predicate: Register;
}

export interface SaveGeneratorInst extends BranchInstruction { instruction: 'SaveGenerator' }

export interface JLessInst extends BranchingBinaryInstruction { instruction: 'JLess' }
export interface JNotLessInst extends BranchingBinaryInstruction { instruction: 'JNotLess' }
export interface JLessEqualInst extends BranchingBinaryInstruction { instruction: 'JLessEqual' }
export interface JNotLessEqualInst extends BranchingBinaryInstruction { instruction: 'JNotLessEqual' }
export interface JGreaterInst extends BranchingBinaryInstruction { instruction: 'JGreater' }
export interface JNotGreaterInst extends BranchingBinaryInstruction { instruction: 'JNotGreater' }
export interface JGreaterEqualInst extends BranchingBinaryInstruction { instruction: 'JGreaterEqual' }
export interface JNotGreaterEqualInst extends BranchingBinaryInstruction { instruction: 'JNotGreaterEqual' }
export interface JEqualInst extends BranchingBinaryInstruction { instruction: 'JEqual' }
export interface JNotEqualInst extends BranchingBinaryInstruction { instruction: 'JNotEqual' }
export interface JStrictEqualInst extends BranchingBinaryInstruction { instruction: 'JStrictEqual' }
export interface JStrictNotEqualInst extends BranchingBinaryInstruction { instruction: 'JStrictNotEqual' }

export interface Add32Inst extends WASMSpecificInstruction, BinaryOperationInst { instruction: 'Add32' }

export interface Sub32Inst extends WASMSpecificInstruction, BinaryOperationInst { instruction: 'Sub32' }

export interface Mul32Inst extends WASMSpecificInstruction, BinaryOperationInst { instruction: 'Mul32' }

export interface Divi32Inst extends WASMSpecificInstruction, BinaryOperationInst { instruction: 'Divi32' }

export interface Divu32Inst extends WASMSpecificInstruction, BinaryOperationInst { instruction: 'Divu32' }

export interface Loadi8Inst extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadi8';
	heap: Register;
	offset: Register;
}

export interface Loadu8Inst extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadu8';
	heap: Register;
	offset: Register;
}

export interface Loadi16Inst extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadi16';
	heap: Register;
	offset: Register;
}

export interface Loadu16Inst extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadu16';
	heap: Register;
	offset: Register;
}

export interface Loadi32Inst extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadi32';
	heap: Register;
	offset: Register;
}

export interface Loadu32Inst extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadu32';
	heap: Register;
	offset: Register;
}

export interface Store8Inst extends WASMSpecificInstruction {
	instruction: 'Store8';
	heap: Register;
	offset: Register;
	value: Register;
}

export interface Store16Inst extends WASMSpecificInstruction {
	instruction: 'Store16';
	heap: Register;
	offset: Register;
	value: Register;
}

export interface Store32Inst extends WASMSpecificInstruction {
	instruction: 'Store32';
	heap: Register;
	offset: Register;
	value: Register;
}

export type Instructions = {
	'Unreachable': UnreachableInst,
	'NewObjectWithBuffer': NewObjectWithBufferInst,
	'NewObject': NewObjectInst,
	'NewObjectWithParent': NewObjectWithParentInst,
	'NewArrayWithBuffer': NewArrayWithBufferInst,
	'NewArray': NewArrayInst,
	'Mov': MovInst,
	'Inc': IncInst,
	'Dec': DecInst,
	'Negate': NegateInst,
	'Not': NotInst,
	'BitNot': BitNotInst,
	'TypeOf': TypeOfInst,
	'Eq': EqInst,
	'StrictEq': StrictEqInst,
	'Neq': NeqInst,
	'StrictNeq': StrictNeqInst,
	'Less': LessInst,
	'LessEq': LessEqInst,
	'Greater': GreaterInst,
	'GreaterEq': GreaterEqInst,
	'Add': AddInst,
	'Mul': MulInst,
	'Div': DivInst,
	'Mod': ModInst,
	'Sub': SubInst,
	'LShift': LShiftInst,
	'RShift': RShiftInst,
	'URShift': URShiftInst,
	'BitAnd': BitAndInst,
	'BitXor': BitXorInst,
	'BitOr': BitOrInst,
	'InstanceOf': InstanceOfInst,
	'IsIn': IsInInst,
	'GetEnvironment': GetEnvironmentInst,
	'StoreToEnvironment': StoreToEnvironmentInst,
	'StoreNPToEnvironment': StoreNPToEnvironmentInst,
	'LoadFromEnvironment': LoadFromEnvironmentInst,
	'GetGlobalObject': GetGlobalObjectInst,
	'GetNewTarget': GetNewTargetInst,
	'CreateEnvironment': CreateEnvironmentInst,
	'CreateInnerEnvironment': CreateInnerEnvironmentInst,
	'DeclareGlobalVar': DeclareGlobalVarInst,
	'GetById': GetByIdInst,
	'TryGetById': TryGetByIdInst,
	'PutById': PutByIdInst,
	'TryPutById': TryPutByIdInst,
	'PutNewOwnById': PutNewOwnByIdInst,
	'PutNewOwnNEById': PutNewOwnNEByIdInst,
	'PutOwnByIndex': PutOwnByIndexInst,
	'PutOwnByVal': PutOwnByValInst,
	'DelById': DelByIdInst,
	'GetByVal': GetByValInst,
	'PutByVal': PutByValInst,
	'DelByVal': DelByValInst,
	'PutOwnGetterSetterByVal': PutOwnGetterSetterByValInst,
	'GetPNameList': GetPNameListInst,
	'GetNextPName': GetNextPNameInst,
	'Call': CallInst,
	'Construct': ConstructInst,
	'CallDirect': CallDirectInst,
	'CallBuiltin': CallBuiltinInst,
	'GetBuiltinClosure': GetBuiltinClosureInst,
	'Ret': RetInst,
	'Catch': CatchInst,
	'DirectEval': DirectEvalInst,
	'Throw': ThrowInst,
	'ThrowIfEmpty': ThrowIfEmptyInst,
	'ThrowIfUndefined': ThrowIfUndefinedInst,
	'ThrowIfHasRestrictedGlobalProperty': ThrowIfHasRestrictedGlobalPropertyInst,
	'Debugger': DebuggerInst,
	'DebuggerCheckBreak': DebuggerCheckBreakInst,
	'AsyncBreakCheck': AsyncBreakCheckInst,
	'ProfilePoint': ProfilePointInst,
	'CreateClosure': CreateClosureInst,
	'CreateGeneratorClosure': CreateGeneratorClosureInst,
	'CreateAsyncClosure': CreateAsyncClosureInst,
	'CreateThis': CreateThisInst,
	'SelectObject': SelectObjectInst,
	'LoadParam': LoadParamInst,
	'LoadConst': LoadConstInst,
	'CoerceThisNS': CoerceThisNSInst,
	'LoadThisNS': LoadThisNSInst,
	'ToNumber': ToNumberInst,
	'ToNumeric': ToNumericInst,
	'ToInt32': ToInt32Inst,
	'AddEmptyString': AddEmptyStringInst,
	'GetArgumentsByPropVal': GetArgumentsByPropValInst,
	'GetArgumentsLength': GetArgumentsLengthInst,
	'ReifyArguments': ReifyArgumentsInst,
	'CreateRegExp': CreateRegExpInst,
	'SwitchImm': SwitchImmInst,
	'StartGenerator': StartGeneratorInst,
	'ResumeGenerator': ResumeGeneratorInst,
	'CompleteGenerator': CompleteGeneratorInst,
	'CreateGenerator': CreateGeneratorInst,
	'IteratorBegin': IteratorBeginInst,
	'IteratorNext': IteratorNextInst,
	'IteratorClose': IteratorCloseInst,
	'Jmp': JmpInst,
	'JmpTrue': JmpTrueInst,
	'JmpFalse': JmpFalseInst,
	'JmpUndefined': JmpUndefinedInst,
	'SaveGenerator': SaveGeneratorInst,
	'JLess': JLessInst,
	'JNotLess': JNotLessInst,
	'JLessEqual': JLessEqualInst,
	'JNotLessEqual': JNotLessEqualInst,
	'JGreater': JGreaterInst,
	'JNotGreater': JNotGreaterInst,
	'JGreaterEqual': JGreaterEqualInst,
	'JNotGreaterEqual': JNotGreaterEqualInst,
	'JEqual': JEqualInst,
	'JNotEqual': JNotEqualInst,
	'JStrictEqual': JStrictEqualInst,
	'JStrictNotEqual': JStrictNotEqualInst,
	'Add32': Add32Inst,
	'Sub32': Sub32Inst,
	'Mul32': Mul32Inst,
	'Divi32': Divi32Inst,
	'Divu32': Divu32Inst,
	'Loadi8': Loadi8Inst,
	'Loadu8': Loadu8Inst,
	'Loadi16': Loadi16Inst,
	'Loadu16': Loadu16Inst,
	'Loadi32': Loadi32Inst,
	'Loadu32': Loadu32Inst,
	'Store8': Store8Inst,
	'Store16': Store16Inst,
	'Store32': Store32Inst,
};

export const RAW_OPERANDS = {
	"Add": [Reg8, Reg8, Reg8],
	"Add32": [Reg8, Reg8, Reg8],
	"AddEmptyString": [Reg8, Reg8],
	"AddN": [Reg8, Reg8, Reg8],
	"AsyncBreakCheck": [],
	"BitAnd": [Reg8, Reg8, Reg8],
	"BitNot": [Reg8, Reg8],
	"BitOr": [Reg8, Reg8, Reg8],
	"BitXor": [Reg8, Reg8, Reg8],
	"Call": [Reg8, Reg8, UInt8],
	"Call1": [Reg8, Reg8, Reg8],
	"Call2": [Reg8, Reg8, Reg8, Reg8],
	"Call3": [Reg8, Reg8, Reg8, Reg8, Reg8],
	"Call4": [Reg8, Reg8, Reg8, Reg8, Reg8, Reg8],
	"CallBuiltin": [Reg8, UInt8, UInt8],
	"CallBuiltinLong": [Reg8, UInt8, UInt32],
	"CallDirect": [Reg8, UInt8, FunctionRef16],
	"CallDirectLongIndex": [Reg8, UInt8, FunctionRef32],
	"CallLong": [Reg8, Reg8, UInt32],
	"Catch": [Reg8],
	"CoerceThisNS": [Reg8, Reg8],
	"CompleteGenerator": [],
	"Construct": [Reg8, Reg8, UInt8],
	"ConstructLong": [Reg8, Reg8, UInt32],
	"CreateAsyncClosure": [Reg8, Reg8, FunctionRef16],
	"CreateAsyncClosureLongIndex": [Reg8, Reg8, FunctionRef32],
	"CreateClosure": [Reg8, Reg8, FunctionRef16],
	"CreateClosureLongIndex": [Reg8, Reg8, FunctionRef32],
	"CreateEnvironment": [Reg8],
	"CreateInnerEnvironment": [Reg8],
	"CreateGenerator": [Reg8, Reg8, FunctionRef16],
	"CreateGeneratorClosure": [Reg8, Reg8, FunctionRef16],
	"CreateGeneratorClosureLongIndex": [Reg8, Reg8, FunctionRef32],
	"CreateGeneratorLongIndex": [Reg8, Reg8, FunctionRef32],
	"CreateRegExp": [Reg8, StringRef32, StringRef32, UInt32],
	"CreateThis": [Reg8, Reg8, Reg8],
	"Debugger": [],
	"DebuggerCheckBreak": [],
	"Dec": [Reg8, Reg8],
	"DeclareGlobalVar": [StringRef32],
	"DelById": [Reg8, Reg8, StringRef16],
	"DelByIdLong": [Reg8, Reg8, StringRef32],
	"DelByVal": [Reg8, Reg8, Reg8],
	"DirectEval": [Reg8, Reg8, UInt8],
	"Div": [Reg8, Reg8, Reg8],
	"DivN": [Reg8, Reg8, Reg8],
	"Divi32": [Reg8, Reg8, Reg8],
	"Divu32": [Reg8, Reg8, Reg8],
	"Eq": [Reg8, Reg8, Reg8],
	"GetArgumentsLength": [Reg8, Reg8],
	"GetArgumentsPropByVal": [Reg8, Reg8, Reg8],
	"GetBuiltinClosure": [Reg8, UInt8],
	"GetById": [Reg8, Reg8, UInt8, StringRef16],
	"GetByIdLong": [Reg8, Reg8, UInt8, StringRef32],
	"GetByIdShort": [Reg8, Reg8, UInt8, StringRef8],
	"GetByVal": [Reg8, Reg8, Reg8],
	"GetEnvironment": [Reg8, UInt8],
	"GetGlobalObject": [Reg8],
	"GetNewTarget": [Reg8],
	"GetNextPName": [Reg8, Reg8, Reg8, Reg8, Reg8],
	"GetPNameList": [Reg8, Reg8, Reg8, Reg8],
	"Greater": [Reg8, Reg8, Reg8],
	"GreaterEq": [Reg8, Reg8, Reg8],
	"Inc": [Reg8, Reg8],
	"InstanceOf": [Reg8, Reg8, Reg8],
	"IsIn": [Reg8, Reg8, Reg8],
	"IteratorBegin": [Reg8, Reg8],
	"IteratorClose": [Reg8, UInt8],
	"IteratorNext": [Reg8, Reg8, Reg8],
	"JEqual": [Addr8, Reg8, Reg8],
	"JEqualLong": [Addr32, Reg8, Reg8],
	"JGreater": [Addr8, Reg8, Reg8],
	"JGreaterEqual": [Addr8, Reg8, Reg8],
	"JGreaterEqualLong": [Addr32, Reg8, Reg8],
	"JGreaterEqualN": [Addr8, Reg8, Reg8],
	"JGreaterEqualNLong": [Addr32, Reg8, Reg8],
	"JGreaterLong": [Addr32, Reg8, Reg8],
	"JGreaterN": [Addr8, Reg8, Reg8],
	"JGreaterNLong": [Addr32, Reg8, Reg8],
	"JLess": [Addr8, Reg8, Reg8],
	"JLessEqual": [Addr8, Reg8, Reg8],
	"JLessEqualLong": [Addr32, Reg8, Reg8],
	"JLessEqualN": [Addr8, Reg8, Reg8],
	"JLessEqualNLong": [Addr32, Reg8, Reg8],
	"JLessLong": [Addr32, Reg8, Reg8],
	"JLessN": [Addr8, Reg8, Reg8],
	"JLessNLong": [Addr32, Reg8, Reg8],
	"JNotEqual": [Addr8, Reg8, Reg8],
	"JNotEqualLong": [Addr32, Reg8, Reg8],
	"JNotGreater": [Addr8, Reg8, Reg8],
	"JNotGreaterEqual": [Addr8, Reg8, Reg8],
	"JNotGreaterEqualLong": [Addr32, Reg8, Reg8],
	"JNotGreaterEqualN": [Addr8, Reg8, Reg8],
	"JNotGreaterEqualNLong": [Addr32, Reg8, Reg8],
	"JNotGreaterLong": [Addr32, Reg8, Reg8],
	"JNotGreaterN": [Addr8, Reg8, Reg8],
	"JNotGreaterNLong": [Addr32, Reg8, Reg8],
	"JNotLess": [Addr8, Reg8, Reg8],
	"JNotLessEqual": [Addr8, Reg8, Reg8],
	"JNotLessEqualLong": [Addr32, Reg8, Reg8],
	"JNotLessEqualN": [Addr8, Reg8, Reg8],
	"JNotLessEqualNLong": [Addr32, Reg8, Reg8],
	"JNotLessLong": [Addr32, Reg8, Reg8],
	"JNotLessN": [Addr8, Reg8, Reg8],
	"JNotLessNLong": [Addr32, Reg8, Reg8],
	"JStrictEqual": [Addr8, Reg8, Reg8],
	"JStrictEqualLong": [Addr32, Reg8, Reg8],
	"JStrictNotEqual": [Addr8, Reg8, Reg8],
	"JStrictNotEqualLong": [Addr32, Reg8, Reg8],
	"Jmp": [Addr8],
	"JmpFalse": [Addr8, Reg8],
	"JmpFalseLong": [Addr32, Reg8],
	"JmpLong": [Addr32],
	"JmpTrue": [Addr8, Reg8],
	"JmpTrueLong": [Addr32, Reg8],
	"JmpUndefined": [Addr8, Reg8],
	"JmpUndefinedLong": [Addr32, Reg8],
	"LShift": [Reg8, Reg8, Reg8],
	"Less": [Reg8, Reg8, Reg8],
	"LessEq": [Reg8, Reg8, Reg8],
	"LoadConstBigInt": [Reg8, BigIntRef16],
	"LoadConstBigIntLongIndex": [Reg8, BigIntRef32],
	"LoadConstDouble": [Reg8, Double],
	"LoadConstEmpty": [Reg8],
	"LoadConstFalse": [Reg8],
	"LoadConstInt": [Reg8, Imm32],
	"LoadConstNull": [Reg8],
	"LoadConstString": [Reg8, StringRef16],
	"LoadConstStringLongIndex": [Reg8, StringRef32],
	"LoadConstTrue": [Reg8],
	"LoadConstUInt8": [Reg8, UInt8],
	"LoadConstUndefined": [Reg8],
	"LoadConstZero": [Reg8],
	"LoadFromEnvironment": [Reg8, Reg8, UInt8],
	"LoadFromEnvironmentL": [Reg8, Reg8, UInt16],
	"LoadParam": [Reg8, UInt8],
	"LoadParamLong": [Reg8, UInt32],
	"LoadThisNS": [Reg8],
	"Loadi16": [Reg8, Reg8, Reg8],
	"Loadi32": [Reg8, Reg8, Reg8],
	"Loadi8": [Reg8, Reg8, Reg8],
	"Loadu16": [Reg8, Reg8, Reg8],
	"Loadu32": [Reg8, Reg8, Reg8],
	"Loadu8": [Reg8, Reg8, Reg8],
	"Mod": [Reg8, Reg8, Reg8],
	"Mov": [Reg8, Reg8],
	"MovLong": [Reg32, Reg32],
	"Mul": [Reg8, Reg8, Reg8],
	"Mul32": [Reg8, Reg8, Reg8],
	"MulN": [Reg8, Reg8, Reg8],
	"Negate": [Reg8, Reg8],
	"Neq": [Reg8, Reg8, Reg8],
	"NewArray": [Reg8, UInt16],
	"NewArrayWithBuffer": [Reg8, UInt16, UInt16, UInt16],
	"NewArrayWithBufferLong": [Reg8, UInt16, UInt16, UInt32],
	"NewObject": [Reg8],
	"NewObjectWithBuffer": [Reg8, UInt16, UInt16, UInt16, UInt16],
	"NewObjectWithBufferLong": [Reg8, UInt16, UInt16, UInt32, UInt32],
	"NewObjectWithParent": [Reg8, Reg8],
	"Not": [Reg8, Reg8],
	"ProfilePoint": [UInt16],
	"PutById": [Reg8, Reg8, UInt8, StringRef16],
	"PutByIdLong": [Reg8, Reg8, UInt8, StringRef32],
	"PutByVal": [Reg8, Reg8, Reg8],
	"PutNewOwnById": [Reg8, Reg8, StringRef16],
	"PutNewOwnByIdLong": [Reg8, Reg8, StringRef32],
	"PutNewOwnByIdShort": [Reg8, Reg8, StringRef8],
	"PutNewOwnNEById": [Reg8, Reg8, StringRef16],
	"PutNewOwnNEByIdLong": [Reg8, Reg8, StringRef32],
	"PutOwnByIndex": [Reg8, Reg8, UInt8],
	"PutOwnByIndexL": [Reg8, Reg8, UInt32],
	"PutOwnByVal": [Reg8, Reg8, Reg8, UInt8],
	"PutOwnGetterSetterByVal": [Reg8, Reg8, Reg8, Reg8, UInt8],
	"RShift": [Reg8, Reg8, Reg8],
	"ReifyArguments": [Reg8],
	"ResumeGenerator": [Reg8, Reg8],
	"Ret": [Reg8],
	"SaveGenerator": [Addr8],
	"SaveGeneratorLong": [Addr32],
	"SelectObject": [Reg8, Reg8, Reg8],
	"StartGenerator": [],
	"Store16": [Reg8, Reg8, Reg8],
	"Store32": [Reg8, Reg8, Reg8],
	"Store8": [Reg8, Reg8, Reg8],
	"StoreNPToEnvironment": [Reg8, UInt8, Reg8],
	"StoreNPToEnvironmentL": [Reg8, UInt16, Reg8],
	"StoreToEnvironment": [Reg8, UInt8, Reg8],
	"StoreToEnvironmentL": [Reg8, UInt16, Reg8],
	"StrictEq": [Reg8, Reg8, Reg8],
	"StrictNeq": [Reg8, Reg8, Reg8],
	"Sub": [Reg8, Reg8, Reg8],
	"Sub32": [Reg8, Reg8, Reg8],
	"SubN": [Reg8, Reg8, Reg8],
	"SwitchImm": [Reg8, UInt32, Addr32, UInt32, UInt32],
	"Throw": [Reg8],
	"ThrowIfEmpty": [Reg8, Reg8],
	"ThrowIfUndefined": [Reg8],
	"ThrowIfHasRestrictedGlobalProperty": [StringRef32],
	"ToInt32": [Reg8, Reg8],
	"ToNumber": [Reg8, Reg8],
	"ToNumeric": [Reg8, Reg8],
	"TryGetByIdShort": [Reg8, Reg8, UInt8, StringRef8],
	"TryGetById": [Reg8, Reg8, UInt8, StringRef16],
	"TryGetByIdLong": [Reg8, Reg8, UInt8, StringRef32],
	"TryPutByIdShort": [Reg8, Reg8, UInt8, StringRef8],
	"TryPutById": [Reg8, Reg8, UInt8, StringRef16],
	"TryPutByIdLong": [Reg8, Reg8, UInt8, StringRef32],
	"TypeOf": [Reg8, Reg8],
	"URShift": [Reg8, Reg8, Reg8],
	"Unreachable": [],
} as const;

export type RawMnemonic = keyof typeof RAW_OPERANDS;

export const InstructionNormalisationMap = {
	'AddN': {
		instruction: 'Add',
		length: InstructionLength.NORMAL,
		type: InstructionType.NUMERIC,
	},
	'MulN': {
		instruction: 'Mul',
		length: InstructionLength.NORMAL,
		type: InstructionType.NUMERIC,
	},
	'DivN': {
		instruction: 'Div',
		length: InstructionLength.NORMAL,
		type: InstructionType.NUMERIC,
	},
	'SubN': {
		instruction: 'Div',
		length: InstructionLength.NORMAL,
		type: InstructionType.NUMERIC,
	},
	'GetByIdShort': {
		instruction: 'GetById',
		length: InstructionLength.SHORT,
		type: InstructionType.NORMAL,
	},
	'GetByIdLong': {
		instruction: 'GetById',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
	'TryGetByIdShort': {
		instruction: 'TryGetById',
		length: InstructionLength.SHORT,
		type: InstructionType.NORMAL,
	},
	'TryGetByIdLong': {
		instruction: 'TryGetById',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
	'PutByIdShort': {
		instruction: 'PutById',
		length: InstructionLength.SHORT,
		type: InstructionType.NORMAL,
	},
	'PutByIdLong': {
		instruction: 'PutById',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
	'TryPutByIdShort': {
		instruction: 'TryPutById',
		length: InstructionLength.SHORT,
		type: InstructionType.NORMAL,
	},
	'TryPutByIdLong': {
		instruction: 'TryPutById',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
	'StoreToEnvironmentL': {
		instruction: 'StoreToEnvironment',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
	'StoreNPToEnvironmentL': {
		instruction: 'StoreToEnvironment',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
	'JmpLong': {
		instruction: 'Jmp',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
	'JmpTrueLong': {
		instruction: 'JmpTrue',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
	'JmpFalseLong': {
		instruction: 'JmpFalse',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
	'JmpUndefinedLong': {
		instruction: 'JmpUndefined',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
	'PutNewOwnByIdShort': {
		instruction: 'PutNewOwnById',
		length: InstructionLength.SHORT,
		type: InstructionType.NORMAL,
	},
	'PutNewOwnByIdLong': {
		instruction: 'PutNewOwnById',
		length: InstructionLength.LONG,
		type: InstructionType.NORMAL,
	},
} satisfies {
	[mnemonic: string]: {
		instruction: keyof Instructions;
		length: InstructionLength;
		type: InstructionType;
	}
};

export type Instruction = Instructions[keyof Instructions];

export function createInstruction(mnemonic: string, operands: Operand[], functionLocalOffset: number, bytecodeVersion?: number, frameSize?: number): Instruction {
	type ExpectedInstruction<T extends string> = Instructions[
		T extends keyof typeof InstructionNormalisationMap ? typeof InstructionNormalisationMap[T]['instruction']
		: T extends keyof Instructions ? T 
		: never
	];

	let instruction = mnemonic;
	let length = InstructionLength.NORMAL;
	let type = InstructionType.NORMAL;
	if (mnemonic in InstructionNormalisationMap) {
		({ instruction, length, type } = InstructionNormalisationMap[mnemonic as keyof typeof InstructionNormalisationMap]);
	}

	const callArgs = [];

	switch (mnemonic) {
		case 'Unreachable':
		case 'Debugger':
		case 'DebuggerCheckBreak':
		case 'StartGenerator':
		case 'CompleteGenerator':
		case 'AsyncBreakCheck': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'DeclareGlobalVar': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				identifier: checkStringRef(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'GetGlobalObject':
		case 'CreateEnvironment':
		case 'NewObject':
		case 'LoadThisNS':
		case 'Catch': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		
		case 'GetEnvironment': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				levelIndex: checkImmediate(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'LoadFromEnvironment': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				environment: checkRegister(operands[1]),
				slotIndex: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'Ret': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				argument: checkRegister(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'Throw': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				exception: checkRegister(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'ThrowIfEmpty': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				source: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'LoadParam': {
		// TODO: LoadParamLong
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				parameterIndex: checkImmediate(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'Mov': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				source: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'CreateThis': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				prototype: checkRegister(operands[1]),
				constructorRef: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'SelectObject': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				thisObject: checkRegister(operands[1]),
				constructorReturnValue: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'Call4':
			callArgs.unshift(checkRegister(operands[5]));
			/* falls through */
		case 'Call3':
			callArgs.unshift(checkRegister(operands[4]));
			/* falls through */
		case 'Call2':
			callArgs.unshift(checkRegister(operands[3]));
			/* falls through */
		case 'Call1': {
			callArgs.unshift(checkRegister(operands[2]));
			return {
				instruction: 'Call',
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				closure: checkRegister(operands[1]),
				arguments: callArgs,
			}
		}

		case 'Call':
		case 'Construct': {
			if (typeof bytecodeVersion == 'undefined' || typeof frameSize == 'undefined') {
				throw new Error();
			}

			const argumentCount = checkImmediate(operands[2]);
			const args: Register[] = [];
			const lastArg = frameSize + getStackOffset(bytecodeVersion, NamedStackVariables.ThisArg);
			for (let i = lastArg; i > lastArg - argumentCount; i--) {
				args.push({ type: 'register', index: i });
			}

			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				closure: checkRegister(operands[1]),
				argumentCount,
				arguments: args,
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'Inc':
		case 'Dec':
		case 'Negate':
		case 'Not':
		case 'BitNot':
		case 'TypeOf':
		case 'ToNumber':
		case 'ToNumeric':
		case 'ToInt32':
		case 'CoerceThisNS': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				argument: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'NewArray': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				size: checkImmediate(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'NewArrayWithBuffer': {
			return {
				instruction,
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				sizeHint: checkImmediate(operands[1]),
				noOfStaticElements: checkImmediate(operands[2]),
				arrayBufferIndex: checkImmediate(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'Eq':
		case 'StrictEq':
		case 'Neq':
		case 'StrictNeq':
		case 'Less':
		case 'LessEq':
		case 'Greater':
		case 'GreaterEq':
		case 'Add':
		case 'AddN':
		case 'Mul':
		case 'MulN':
		case 'Div':
		case 'DivN':
		case 'Mod':
		case 'Sub':
		case 'SubN':
		case 'LShift':
		case 'RShift':
		case 'URShift':
		case 'BitAnd':
		case 'BitXor':
		case 'BitOr':
		case 'InstanceOf':
		case 'IsIn': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				destination: checkRegister(operands[0]),
				left: checkRegister(operands[1]),
				right: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'PutByIdShort':
		case 'PutById':
		case 'PutByIdLong':
		case 'TryPutByIdShort':
		case 'TryPutById':
		case 'TryPutByIdLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
				cacheIndex: checkImmediate(operands[2]),
				property: checkStringRef(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PutNewOwnByIdShort':
		case 'PutNewOwnById':
		case 'PutNewOwnByIdLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
				property: checkStringRef(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PutOwnByIndex': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
				property: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PutByVal': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				object: checkRegister(operands[0]),
				property: checkRegister(operands[1]),
				value: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'GetByIdShort':
		case 'GetById':
		case 'GetByIdLong':
		case 'TryGetByIdShort':
		case 'TryGetById':
		case 'TryGetByIdLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				cacheIndex: checkImmediate(operands[2]),
				property: checkStringRef(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'GetByVal': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type: InstructionType.NUMERIC,

				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				property: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'StoreToEnvironment':
		case 'StoreToEnvironmentL':
		case 'StoreNPToEnvironment':
		case 'StoreNPToEnvironmentL': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				environment: checkRegister(operands[0]),
				slotIndex: checkImmediate(operands[1]),
				value: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'CreateClosure':
		case 'CreateGeneratorClosure': 
		case 'CreateAsyncClosure': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				destination: checkRegister(operands[0]),
				environment: checkRegister(operands[1]),
				function: checkFunctionRef(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'CreateGenerator': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				destination: checkRegister(operands[0]),
				environment: checkRegister(operands[1]),
				function: checkFunctionRef(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'ResumeGenerator': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				destination: checkRegister(operands[0]),
				isReturn: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'CreateRegExp': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				destination: checkRegister(operands[0]),
				pattern: checkStringRef(operands[1]),
				flags: checkStringRef(operands[2]),
				regExpBytecodeIndex: checkImmediate(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'GetBuiltinClosure': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				destination: checkRegister(operands[0]),
				builtinNo: checkImmediate(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'ReifyArguments': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				lazyLoad: checkRegister(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'LoadConstUInt8':
		case 'LoadConstInt':
		case 'LoadConstDouble':
		case 'LoadConstBigInt':
		case 'LoadConstBigIntLongIndex':
		case 'LoadConstString':
		case 'LoadConstStringLongIndex':
		case 'LoadConstEmpty':
		case 'LoadConstUndefined':
		case 'LoadConstNull':
		case 'LoadConstTrue':
		case 'LoadConstFalse':
		case 'LoadConstZero': {
			let value: Instructions['LoadConst']['value'];
			switch (mnemonic) {
				case 'LoadConstUInt8':
				case 'LoadConstInt':
				case 'LoadConstDouble':
					value = checkImmediate(operands[1]);
					break;
				case 'LoadConstBigInt':
				case 'LoadConstBigIntLongIndex':
					value = checkBigIntRef(operands[1]);
					break;
				case 'LoadConstString':
				case 'LoadConstStringLongIndex':
					value = checkStringRef(operands[1]);
					break;
				case 'LoadConstEmpty':
					value = HermesEmpty;
					break;
				case 'LoadConstUndefined':
					value = undefined;
					break;
				case 'LoadConstNull':
					value = null;
					break;
				case 'LoadConstTrue':
					value = true;
					break;
				case 'LoadConstFalse':
					value = false;
					break;
				case 'LoadConstZero':
					value = 0;
					break;
			}
			return {
				instruction: 'LoadConst',
				functionLocalOffset,
				length,
				type,

				destination: checkRegister(operands[0]),
				value,
			} as ExpectedInstruction<'LoadConst'>;
		}

		case 'Jmp':
		case 'JmpLong':
		case 'SaveGenerator':
		case 'SaveGeneratorLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				relativeTarget: checkImmediate(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		
		case 'JmpTrue':
		case 'JmpTrueLong':
		case 'JmpFalse':
		case 'JmpFalseLong':
		case 'JmpUndefined':
		case 'JmpUndefinedLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,

				relativeTarget: checkImmediate(operands[0]),
				predicate: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		default:
			throw new Error('Unimplemented mnemonic: ' + mnemonic)
	}
}