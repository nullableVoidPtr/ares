import {
	getStackOffset,
	NamedStackVariables,
} from '../data/stackFrameLayout.ts';
import type { VersionInfo } from '../data/VersionInfo.ts';
import { Double, UInt16, UInt32, UInt8 } from '../../utils/DataReader.ts';
import {
	Addr32,
	Addr8,
	BigIntRef16,
	BigIntRef32,
	FunctionRef16,
	FunctionRef32,
	Imm32,
	Reg32,
	Reg8,
	StringRef16,
	StringRef32,
	StringRef8,
} from '../reader.ts';

function isType<T extends string>(o: unknown, type: T): o is { type: T } {
	if (typeof o != 'object' || o === null) return false;
	if (!('type' in o) || o.type != type) return false;

	return true;
}

export type RegisterIndex = number;
export interface Register {
	type: 'register';
	index: RegisterIndex;
}

export function asRegister(index: number): Register {
	return {
		type: 'register',
		index,
	};
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
};

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
};

export function asStringRef(stringTableIndex: number): StringRef {
	return {
		type: 'string',
		stringTableIndex,
	};
}

export function isStringRef(o: unknown): o is StringRef {
	if (!isType(o, 'string')) return false;
	if (!('stringTableIndex' in o) || typeof o.stringTableIndex != 'number') {
		return false;
	}

	return true;
}

export function checkStringRef(o: unknown): StringRef {
	if (!isStringRef(o)) throw Error();

	return o;
}

export function checkImmediate(o: unknown): number {
	if (typeof o !== 'number') throw new Error();
	return o;
}

export type BigIntRef = {
	type: 'bigint';
	bigintTableIndex: number;
};

export function asBigIntRef(bigintTableIndex: number): BigIntRef {
	return {
		type: 'bigint',
		bigintTableIndex,
	};
}

export function isBigIntRef(o: unknown): o is BigIntRef {
	if (!isType(o, 'bigint')) return false;
	if (!('bigintTableIndex' in o) || typeof o.bigintTableIndex != 'number') {
		return false;
	}

	return true;
}

export function checkBigIntRef(o: unknown): BigIntRef {
	if (!isBigIntRef(o)) throw Error();

	return o;
}

export const HermesEmpty: unique symbol = Symbol('Empty');

export type Operand =
	| Register
	| StringRef
	| BigIntRef
	| FunctionRef
	| number
	| typeof HermesEmpty
	| void
	| null
	| boolean;

export const TYPEOF_IS_TYPES = [
	'Undefined',
	'Object',
	'String',
	'Symbol',
	'Boolean',
	'Number',
	'Bigint',
	'Function',
	'Null',
] as const;

export type TypeOfIsType = typeof TYPEOF_IS_TYPES[number];

export const TYPEOF_IS_TYPE_MASKS = Object.fromEntries(
	TYPEOF_IS_TYPES.map((type, index) => [type, 1 << index]),
) as Record<TypeOfIsType, number>;

export const TYPEOF_IS_ALL_MASK = TYPEOF_IS_TYPES.reduce(
	(mask, type) => mask | TYPEOF_IS_TYPE_MASKS[type],
	0,
);

export function validateTypeOfIsMask(mask: number) {
	if (
		!Number.isInteger(mask) || mask < 0 || (mask & ~TYPEOF_IS_ALL_MASK) != 0
	) {
		throw new Error(`invalid TypeOfIsTypes mask: ${mask}`);
	}
}

export function typeOfIsTypes(mask: number): TypeOfIsType[] {
	validateTypeOfIsMask(mask);
	return TYPEOF_IS_TYPES.filter((type) =>
		(mask & TYPEOF_IS_TYPE_MASKS[type]) != 0
	);
}

export function hasTypeOfIsType(mask: number, type: TypeOfIsType) {
	validateTypeOfIsMask(mask);
	return (mask & TYPEOF_IS_TYPE_MASKS[type]) != 0;
}

export function invertTypeOfIsMask(mask: number) {
	validateTypeOfIsMask(mask);
	return (~mask) & TYPEOF_IS_ALL_MASK;
}

export enum InstructionLength {
	SHORT,
	NORMAL,
	LONG,
}

export enum InstructionType {
	NORMAL,
	NUMERIC,
}

export enum InstructionStrictness {
	NORMAL,
	LOOSE,
	STRICT,
}

export interface BaseInstruction {
	functionLocalOffset: number;
	length: InstructionLength;
	type: InstructionType;
	strict: InstructionStrictness;
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
	instruction: 'Unreachable';
}

export interface NewObjectWithBufferInst extends AssigningInstruction {
	instruction: 'NewObjectWithBuffer';
	sizeHint?: number;
	noOfStaticElements?: number;
	objectKeyBufferIndex?: number;

	shapeTableIndex?: number;
	objectValueBufferIndex: number;
}

export interface NewObjectWithBufferAndParentInst extends AssigningInstruction {
	instruction: 'NewObjectWithBufferAndParent';
	parent: Register;
	shapeTableIndex: number;
	objectValueBufferIndex: number;
}

export interface NewObjectInst extends AssigningInstruction {
	instruction: 'NewObject';
}

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

export interface NewFastArrayInst extends AssigningInstruction {
	instruction: 'NewFastArray';
	prototype: Register;
	size: number;
}

export interface FastArrayLengthInst extends UnaryOperationInst {
	instruction: 'FastArrayLength';
}

export interface FastArrayLoadInst extends AssigningInstruction {
	instruction: 'FastArrayLoad';
	object: Register;
	property: Register;
}

export interface FastArrayStoreInst extends BaseInstruction {
	instruction: 'FastArrayStore';
	object: Register;
	property: Register;
	value: Register;
}

export interface FastArrayPushInst extends BaseInstruction {
	instruction: 'FastArrayPush';
	object: Register;
	value: Register;
}

export interface FastArrayAppendInst extends BaseInstruction {
	instruction: 'FastArrayAppend';
	object: Register;
	value: Register;
}

export interface MovInst extends AssigningInstruction {
	instruction: 'Mov';
	source: Register;
}

export interface IncInst extends UnaryOperationInst {
	instruction: 'Inc';
}
export interface DecInst extends UnaryOperationInst {
	instruction: 'Dec';
}
export interface NegateInst extends UnaryOperationInst {
	instruction: 'Negate';
}
export interface NotInst extends UnaryOperationInst {
	instruction: 'Not';
}
export interface BitNotInst extends UnaryOperationInst {
	instruction: 'BitNot';
}
export interface TypeOfInst extends UnaryOperationInst {
	instruction: 'TypeOf';
}
export interface EqInst extends BinaryOperationInst {
	instruction: 'Eq';
}
export interface StrictEqInst extends BinaryOperationInst {
	instruction: 'StrictEq';
}
export interface NeqInst extends BinaryOperationInst {
	instruction: 'Neq';
}
export interface StrictNeqInst extends BinaryOperationInst {
	instruction: 'StrictNeq';
}
export interface LessInst extends BinaryOperationInst {
	instruction: 'Less';
}
export interface LessEqInst extends BinaryOperationInst {
	instruction: 'LessEq';
}
export interface GreaterInst extends BinaryOperationInst {
	instruction: 'Greater';
}
export interface GreaterEqInst extends BinaryOperationInst {
	instruction: 'GreaterEq';
}
export interface AddInst extends BinaryOperationInst {
	instruction: 'Add';
}
export interface AddSInst extends BinaryOperationInst {
	instruction: 'AddS';
}
export interface MulInst extends BinaryOperationInst {
	instruction: 'Mul';
}
export interface DivInst extends BinaryOperationInst {
	instruction: 'Div';
}
export interface ModInst extends BinaryOperationInst {
	instruction: 'Mod';
}
export interface SubInst extends BinaryOperationInst {
	instruction: 'Sub';
}
export interface LShiftInst extends BinaryOperationInst {
	instruction: 'LShift';
}
export interface RShiftInst extends BinaryOperationInst {
	instruction: 'RShift';
}
export interface URShiftInst extends BinaryOperationInst {
	instruction: 'URShift';
}
export interface BitAndInst extends BinaryOperationInst {
	instruction: 'BitAnd';
}
export interface BitXorInst extends BinaryOperationInst {
	instruction: 'BitXor';
}
export interface BitOrInst extends BinaryOperationInst {
	instruction: 'BitOr';
}
export interface InstanceOfInst extends BinaryOperationInst {
	instruction: 'InstanceOf';
}
export interface IsInInst extends BinaryOperationInst {
	instruction: 'IsIn';
}

export interface GetEnvironmentInst extends AssigningInstruction {
	instruction: 'GetEnvironment';
	parentEnv: Register;
	levelIndex: number;
}
export interface GetParentEnvironmentInst extends AssigningInstruction {
	instruction: 'GetParentEnvironment';
	levelIndex: number;
}
export interface GetClosureEnvironmentInst extends AssigningInstruction {
	instruction: 'GetClosureEnvironment';
	closure: Register;
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

export interface GetGlobalObjectInst extends AssigningInstruction {
	instruction: 'GetGlobalObject';
}

export interface GetNewTargetInst extends AssigningInstruction {
	instruction: 'GetNewTarget';
}

export interface CreateEnvironmentInst extends AssigningInstruction {
	instruction: 'CreateEnvironment';
	parent: Register;
	envSize: number;
}
export interface CreateInnerEnvironmentInst extends AssigningInstruction {
	instruction: 'CreateInnerEnvironment';
}
export interface CreateFunctionEnvironmentInst extends AssigningInstruction {
	instruction: 'CreateFunctionEnvironment';
	envSize?: number;
}
export interface CreateTopLevelEnvironmentInst extends AssigningInstruction {
	instruction: 'CreateTopLevelEnvironment';
	envSize: number;
}

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

export interface GetByIdWithReceiverInst extends AssigningInstruction {
	instruction: 'GetByIdWithReceiver';
	object: Register;
	cacheIndex: number;
	receiver: Register;
	property: StringRef;
}

export interface TryGetByIdInst extends AssigningInstruction {
	instruction: 'TryGetById';
	object: Register;
	cacheIndex: number;
	property: StringRef;
}

export interface GetBySlotIdxInst extends AssigningInstruction {
	instruction: 'GetBySlotIdx';
	object: Register;
	slotIndex: number;
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

export interface DefineOwnByIdInst extends BaseInstruction {
	instruction: 'DefineOwnById';
	object: Register;
	value: Register;
	cacheIndex: number;
	property: StringRef;
}

export interface PutOwnBySlotIdxInst extends BaseInstruction {
	instruction: 'PutOwnBySlotIdx';
	object: Register;
	value: Register;
	slotIndex: number;
}

export interface DefineOwnByIndexInst extends BaseInstruction {
	instruction: 'DefineOwnByIndex';
	object: Register;
	value: Register;
	property: number;
}

export interface DefineOwnByValInst extends BaseInstruction {
	instruction: 'DefineOwnByVal';
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

export interface GetByIndexInst extends AssigningInstruction {
	instruction: 'GetByIndex';
	object: Register;
	index: number;
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
	flags: number;
}

export interface DefineOwnGetterSetterByValInst extends BaseInstruction {
	instruction: 'DefineOwnGetterSetterByVal';
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
	newTarget?: Register;
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
	builtinNo: number;
	argumentCount: number;
	arguments: Register[];
}

export interface GetBuiltinClosureInst extends AssigningInstruction {
	instruction: 'GetBuiltinClosure';
	builtinNo: number;
}

export interface RetInst extends BaseInstruction {
	instruction: 'Ret';
	argument: Register;
}

export interface CatchInst extends AssigningInstruction {
	instruction: 'Catch';
}

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

export interface ThrowIfHasRestrictedGlobalPropertyInst
	extends BaseInstruction {
	instruction: 'ThrowIfHasRestrictedGlobalProperty';
	property: StringRef;
}

export interface ThrowIfThisInitializedInst extends BaseInstruction {
	instruction: 'ThrowIfThisInitialized';
	thisObject: Register;
}

export interface DebuggerInst extends BaseInstruction {
	instruction: 'Debugger';
}
export interface DebuggerCheckBreakInst extends BaseInstruction {
	instruction: 'DebuggerCheckBreak';
}

export interface AsyncBreakCheckInst extends BaseInstruction {
	instruction: 'AsyncBreakCheck';
}

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

export interface CreateBaseClassInst extends BaseInstruction {
	instruction: 'CreateBaseClass';
	classOut: Register;
	homeObject: Register;
	environment: Register;
	function: FunctionRef;
}

export interface CreateDerivedClassInst extends BaseInstruction {
	instruction: 'CreateDerivedClass';
	classOut: Register;
	homeObject: Register;
	environment: Register;
	superClass: Register;
	function: FunctionRef;
}

export interface CreateThisInst extends AssigningInstruction {
	instruction: 'CreateThis';
	prototype: Register;
	constructorRef: Register;
}

export interface CreateThisForNewInst extends AssigningInstruction {
	instruction: 'CreateThisForNew';
	closure: Register;
	prototypeCacheIndex: number;
}

export interface CreateThisForSuperInst extends AssigningInstruction {
	instruction: 'CreateThisForSuper';
	closure: Register;
	newTarget: Register;
	prototypeCacheIndex: number;
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
	value:
		| number
		| StringRef
		| BigIntRef
		| typeof HermesEmpty
		| void
		| null
		| boolean;
}

export interface CoerceThisNSInst extends UnaryOperationInst {
	instruction: 'CoerceThisNS';
}

export interface LoadThisNSInst extends AssigningInstruction {
	instruction: 'LoadThisNS';
}

export interface ToNumberInst extends UnaryOperationInst {
	instruction: 'ToNumber';
}

export interface ToNumericInst extends UnaryOperationInst {
	instruction: 'ToNumeric';
}

export interface ToInt32Inst extends UnaryOperationInst {
	instruction: 'ToInt32';
}

export interface ToPropertyKeyInst extends UnaryOperationInst {
	instruction: 'ToPropertyKey';
}
export interface ToUint32Inst extends UnaryOperationInst {
	instruction: 'ToUint32';
}

export interface LoadParentNoTrapsInst extends UnaryOperationInst {
	instruction: 'LoadParentNoTraps';
}

export interface AddEmptyStringInst extends UnaryOperationInst {
	instruction: 'AddEmptyString';
}

export interface GetArgumentsPropByValInst extends AssigningInstruction {
	instruction: 'GetArgumentsPropByVal';
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

export interface UIntSwitchImmInst extends BaseInstruction {
	instruction: 'UIntSwitchImm';
	discriminant: Register;
	jumpTableOffset: number;
	defaultJumpOffset: number;
	minValue: number;
	maxValue: number;

	relativeTargets: number[];
}
export interface StringSwitchImmInst extends BaseInstruction {
	instruction: 'StringSwitchImm';
	discriminant: Register;
	globalIndex: number;
	jumpTableOffset: number;
	defaultJumpOffset: number;
	size: number;

	stringTableIndices: number[];
	relativeTargets: number[];
}

export interface StartGeneratorInst extends BaseInstruction {
	instruction: 'StartGenerator';
}

export interface ResumeGeneratorInst extends AssigningInstruction {
	instruction: 'ResumeGenerator';
	isReturn: Register;
}

export interface CompleteGeneratorInst extends BaseInstruction {
	instruction: 'CompleteGenerator';
}

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
	ignoreException: number;
}

export interface JmpInst extends BranchInstruction {
	instruction: 'Jmp';
}

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

export interface JmpBuiltinIsInst extends BranchInstruction {
	instruction: 'JmpBuiltinIs';
	builtinNo: number;
	predicate: Register;
}

export interface JmpBuiltinIsNotInst extends BranchInstruction {
	instruction: 'JmpBuiltinIsNot';
	builtinNo: number;
	predicate: Register;
}

export interface SaveGeneratorInst extends BranchInstruction {
	instruction: 'SaveGenerator';
}

export interface JLessInst extends BranchingBinaryInstruction {
	instruction: 'JLess';
}
export interface JNotLessInst extends BranchingBinaryInstruction {
	instruction: 'JNotLess';
}
export interface JLessEqualInst extends BranchingBinaryInstruction {
	instruction: 'JLessEqual';
}
export interface JNotLessEqualInst extends BranchingBinaryInstruction {
	instruction: 'JNotLessEqual';
}
export interface JGreaterInst extends BranchingBinaryInstruction {
	instruction: 'JGreater';
}
export interface JNotGreaterInst extends BranchingBinaryInstruction {
	instruction: 'JNotGreater';
}
export interface JGreaterEqualInst extends BranchingBinaryInstruction {
	instruction: 'JGreaterEqual';
}
export interface JNotGreaterEqualInst extends BranchingBinaryInstruction {
	instruction: 'JNotGreaterEqual';
}
export interface JEqualInst extends BranchingBinaryInstruction {
	instruction: 'JEqual';
}
export interface JNotEqualInst extends BranchingBinaryInstruction {
	instruction: 'JNotEqual';
}
export interface JStrictEqualInst extends BranchingBinaryInstruction {
	instruction: 'JStrictEqual';
}
export interface JStrictNotEqualInst extends BranchingBinaryInstruction {
	instruction: 'JStrictNotEqual';
}

export interface Add32Inst
	extends WASMSpecificInstruction, BinaryOperationInst {
	instruction: 'Add32';
}

export interface Sub32Inst
	extends WASMSpecificInstruction, BinaryOperationInst {
	instruction: 'Sub32';
}

export interface Mul32Inst
	extends WASMSpecificInstruction, BinaryOperationInst {
	instruction: 'Mul32';
}

export interface Divi32Inst
	extends WASMSpecificInstruction, BinaryOperationInst {
	instruction: 'Divi32';
}

export interface Divu32Inst
	extends WASMSpecificInstruction, BinaryOperationInst {
	instruction: 'Divu32';
}

export interface Loadi8Inst
	extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadi8';
	heap: Register;
	offset: Register;
}

export interface Loadu8Inst
	extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadu8';
	heap: Register;
	offset: Register;
}

export interface Loadi16Inst
	extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadi16';
	heap: Register;
	offset: Register;
}

export interface Loadu16Inst
	extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadu16';
	heap: Register;
	offset: Register;
}

export interface Loadi32Inst
	extends WASMSpecificInstruction, AssigningInstruction {
	instruction: 'Loadi32';
	heap: Register;
	offset: Register;
}

export interface Loadu32Inst
	extends WASMSpecificInstruction, AssigningInstruction {
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

export interface CacheNewObjectInst extends BaseInstruction {
	instruction: 'CacheNewObject';
	thisObject: Register;
	newTarget: Register;
	shapeId: number;
	cacheIndex: number;
}
export interface DefineOwnInDenseArrayInst extends BaseInstruction {
	instruction: 'DefineOwnInDenseArray';
	object: Register;
	value: Register;
	index: number;
}
export interface TypeOfIsInst extends AssigningInstruction {
	instruction: 'TypeOfIs';
	value: Register;
	typeIndex: number;
}
export interface PrivateIsInInst extends AssigningInstruction {
	instruction: 'PrivateIsIn';
	name: Register;
	object: Register;
	scope: Register;
}
export interface JmpTypeOfIsInst extends BranchInstruction {
	instruction: 'JmpTypeOfIs';
	value: Register;
	typeIndex: number;
}
export interface CreatePrivateNameInst extends AssigningInstruction {
	instruction: 'CreatePrivateName';
	name: StringRef;
}
export interface AddOwnPrivateBySymInst extends BaseInstruction {
	instruction: 'AddOwnPrivateBySym';
	object: Register;
	name: Register;
	value: Register;
}
export interface GetOwnPrivateBySymInst extends AssigningInstruction {
	instruction: 'GetOwnPrivateBySym';
	object: Register;
	cacheIndex: number;
	name: Register;
}
export interface PutOwnPrivateBySymInst extends BaseInstruction {
	instruction: 'PutOwnPrivateBySym';
	object: Register;
	cacheIndex: number;
	name: Register;
	value: Register;
}
export interface GetByValWithReceiverInst extends AssigningInstruction {
	instruction: 'GetByValWithReceiver';
	object: Register;
	property: Register;
	receiver: Register;
}
export interface PutByValWithReceiverInst extends BaseInstruction {
	instruction: 'PutByValWithReceiver';
	object: Register;
	property: Register;
	value: Register;
	receiver: Register;
	flags: number;
}
export interface CallRequireInst extends AssigningInstruction {
	instruction: 'CallRequire';
	callee: Register;
	moduleId: number;
}
export interface TypedLoadParentInst extends AssigningInstruction {
	instruction: 'TypedLoadParent';
	object: Register;
}

export type Instructions = {
	'Unreachable': UnreachableInst;
	'NewObjectWithBuffer': NewObjectWithBufferInst;
	'NewObjectWithBufferAndParent': NewObjectWithBufferAndParentInst;
	'NewObject': NewObjectInst;
	'NewObjectWithParent': NewObjectWithParentInst;
	'NewArrayWithBuffer': NewArrayWithBufferInst;
	'NewArray': NewArrayInst;
	'NewFastArray': NewFastArrayInst;
	'FastArrayLength': FastArrayLengthInst;
	'FastArrayLoad': FastArrayLoadInst;
	'FastArrayStore': FastArrayStoreInst;
	'FastArrayPush': FastArrayPushInst;
	'FastArrayAppend': FastArrayAppendInst;
	'Mov': MovInst;
	'Inc': IncInst;
	'Dec': DecInst;
	'Negate': NegateInst;
	'Not': NotInst;
	'BitNot': BitNotInst;
	'TypeOf': TypeOfInst;
	'Eq': EqInst;
	'StrictEq': StrictEqInst;
	'Neq': NeqInst;
	'StrictNeq': StrictNeqInst;
	'Less': LessInst;
	'LessEq': LessEqInst;
	'Greater': GreaterInst;
	'GreaterEq': GreaterEqInst;
	'Add': AddInst;
	'AddS': AddSInst;
	'Mul': MulInst;
	'Div': DivInst;
	'Mod': ModInst;
	'Sub': SubInst;
	'LShift': LShiftInst;
	'RShift': RShiftInst;
	'URShift': URShiftInst;
	'BitAnd': BitAndInst;
	'BitXor': BitXorInst;
	'BitOr': BitOrInst;
	'InstanceOf': InstanceOfInst;
	'IsIn': IsInInst;
	'GetEnvironment': GetEnvironmentInst;
	'GetParentEnvironment': GetParentEnvironmentInst;
	'GetClosureEnvironment': GetClosureEnvironmentInst;
	'StoreToEnvironment': StoreToEnvironmentInst;
	'StoreNPToEnvironment': StoreNPToEnvironmentInst;
	'LoadFromEnvironment': LoadFromEnvironmentInst;
	'GetGlobalObject': GetGlobalObjectInst;
	'GetNewTarget': GetNewTargetInst;
	'CreateEnvironment': CreateEnvironmentInst;
	'CreateFunctionEnvironment': CreateFunctionEnvironmentInst;
	'CreateTopLevelEnvironment': CreateTopLevelEnvironmentInst;
	'CreateInnerEnvironment': CreateInnerEnvironmentInst;
	'DeclareGlobalVar': DeclareGlobalVarInst;
	'GetById': GetByIdInst;
	'GetByIdWithReceiver': GetByIdWithReceiverInst;
	'TryGetById': TryGetByIdInst;
	'GetBySlotIdx': GetBySlotIdxInst;
	'PutById': PutByIdInst;
	'TryPutById': TryPutByIdInst;
	'PutNewOwnById': PutNewOwnByIdInst;
	'PutNewOwnNEById': PutNewOwnNEByIdInst;
	'DefineOwnById': DefineOwnByIdInst;
	'PutOwnBySlotIdx': PutOwnBySlotIdxInst;
	'DefineOwnByIndex': DefineOwnByIndexInst;
	'DefineOwnByVal': DefineOwnByValInst;
	'DelById': DelByIdInst;
	'GetByVal': GetByValInst;
	'GetByIndex': GetByIndexInst;
	'PutByVal': PutByValInst;
	'DelByVal': DelByValInst;
	'DefineOwnGetterSetterByVal': DefineOwnGetterSetterByValInst;
	'GetPNameList': GetPNameListInst;
	'GetNextPName': GetNextPNameInst;
	'Call': CallInst;
	'Construct': ConstructInst;
	'CallDirect': CallDirectInst;
	'CallBuiltin': CallBuiltinInst;
	'GetBuiltinClosure': GetBuiltinClosureInst;
	'Ret': RetInst;
	'Catch': CatchInst;
	'DirectEval': DirectEvalInst;
	'Throw': ThrowInst;
	'ThrowIfEmpty': ThrowIfEmptyInst;
	'ThrowIfUndefined': ThrowIfUndefinedInst;
	'ThrowIfHasRestrictedGlobalProperty':
		ThrowIfHasRestrictedGlobalPropertyInst;
	'ThrowIfThisInitialized': ThrowIfThisInitializedInst;
	'Debugger': DebuggerInst;
	'DebuggerCheckBreak': DebuggerCheckBreakInst;
	'AsyncBreakCheck': AsyncBreakCheckInst;
	'ProfilePoint': ProfilePointInst;
	'CreateClosure': CreateClosureInst;
	'CreateGeneratorClosure': CreateGeneratorClosureInst;
	'CreateAsyncClosure': CreateAsyncClosureInst;
	'CreateBaseClass': CreateBaseClassInst;
	'CreateDerivedClass': CreateDerivedClassInst;
	'CreateThis': CreateThisInst;
	'CreateThisForNew': CreateThisForNewInst;
	'CreateThisForSuper': CreateThisForSuperInst;
	'SelectObject': SelectObjectInst;
	'LoadParam': LoadParamInst;
	'LoadConst': LoadConstInst;
	'CoerceThisNS': CoerceThisNSInst;
	'LoadThisNS': LoadThisNSInst;
	'ToNumber': ToNumberInst;
	'ToNumeric': ToNumericInst;
	'ToInt32': ToInt32Inst;
	'ToPropertyKey': ToPropertyKeyInst;
	'ToUint32': ToUint32Inst;
	'LoadParentNoTraps': LoadParentNoTrapsInst;
	'AddEmptyString': AddEmptyStringInst;
	'GetArgumentsPropByVal': GetArgumentsPropByValInst;
	'GetArgumentsLength': GetArgumentsLengthInst;
	'ReifyArguments': ReifyArgumentsInst;
	'CreateRegExp': CreateRegExpInst;
	'UIntSwitchImm': UIntSwitchImmInst;
	'StringSwitchImm': StringSwitchImmInst;
	'StartGenerator': StartGeneratorInst;
	'ResumeGenerator': ResumeGeneratorInst;
	'CompleteGenerator': CompleteGeneratorInst;
	'CreateGenerator': CreateGeneratorInst;
	'IteratorBegin': IteratorBeginInst;
	'IteratorNext': IteratorNextInst;
	'IteratorClose': IteratorCloseInst;
	'Jmp': JmpInst;
	'JmpTrue': JmpTrueInst;
	'JmpBuiltinIs': JmpBuiltinIsInst;
	'JmpBuiltinIsNot': JmpBuiltinIsNotInst;
	'JmpFalse': JmpFalseInst;
	'JmpUndefined': JmpUndefinedInst;
	'SaveGenerator': SaveGeneratorInst;
	'JLess': JLessInst;
	'JNotLess': JNotLessInst;
	'JLessEqual': JLessEqualInst;
	'JNotLessEqual': JNotLessEqualInst;
	'JGreater': JGreaterInst;
	'JNotGreater': JNotGreaterInst;
	'JGreaterEqual': JGreaterEqualInst;
	'JNotGreaterEqual': JNotGreaterEqualInst;
	'JEqual': JEqualInst;
	'JNotEqual': JNotEqualInst;
	'JStrictEqual': JStrictEqualInst;
	'JStrictNotEqual': JStrictNotEqualInst;
	'Add32': Add32Inst;
	'Sub32': Sub32Inst;
	'Mul32': Mul32Inst;
	'Divi32': Divi32Inst;
	'Divu32': Divu32Inst;
	'Loadi8': Loadi8Inst;
	'Loadu8': Loadu8Inst;
	'Loadi16': Loadi16Inst;
	'Loadu16': Loadu16Inst;
	'Loadi32': Loadi32Inst;
	'Loadu32': Loadu32Inst;
	'Store8': Store8Inst;
	'Store16': Store16Inst;
	'Store32': Store32Inst;
	'CacheNewObject': CacheNewObjectInst;
	'DefineOwnInDenseArray': DefineOwnInDenseArrayInst;
	'TypeOfIs': TypeOfIsInst;
	'PrivateIsIn': PrivateIsInInst;
	'JmpTypeOfIs': JmpTypeOfIsInst;
	'CreatePrivateName': CreatePrivateNameInst;
	'AddOwnPrivateBySym': AddOwnPrivateBySymInst;
	'GetOwnPrivateBySym': GetOwnPrivateBySymInst;
	'PutOwnPrivateBySym': PutOwnPrivateBySymInst;
	'GetByValWithReceiver': GetByValWithReceiverInst;
	'PutByValWithReceiver': PutByValWithReceiverInst;
	'CallRequire': CallRequireInst;
	'TypedLoadParent': TypedLoadParentInst;
};

export const RAW_OPERANDS = {
	'Add': [Reg8, Reg8, Reg8],
	'Add32': [Reg8, Reg8, Reg8],
	'AddEmptyString': [Reg8, Reg8],
	'CreatePrivateName': [Reg8, StringRef32],
	'AddN': [Reg8, Reg8, Reg8],
	'AddS': [Reg8, Reg8, Reg8],
	'AddOwnPrivateBySym': [Reg8, Reg8, Reg8],
	'GetOwnPrivateBySym': [Reg8, Reg8, UInt8, Reg8],
	'PutOwnPrivateBySym': [Reg8, Reg8, UInt8, Reg8],
	'AsyncBreakCheck': [],
	'BitAnd': [Reg8, Reg8, Reg8],
	'BitNot': [Reg8, Reg8],
	'BitOr': [Reg8, Reg8, Reg8],
	'BitXor': [Reg8, Reg8, Reg8],
	'Call': [Reg8, Reg8, UInt8],
	'Call1': [Reg8, Reg8, Reg8],
	'Call2': [Reg8, Reg8, Reg8, Reg8],
	'Call3': [Reg8, Reg8, Reg8, Reg8, Reg8],
	'Call4': [Reg8, Reg8, Reg8, Reg8, Reg8, Reg8],
	'CallBuiltin': [Reg8, UInt8, UInt8],
	'CallBuiltinLong': [Reg8, UInt8, UInt32],
	'CacheNewObject': [Reg8, Reg8, UInt32, UInt8],
	'CallDirect': [Reg8, UInt8, FunctionRef16],
	'CallDirectLongIndex': [Reg8, UInt8, FunctionRef32],
	'CallLong': [Reg8, Reg8, UInt32],
	'CallRequire': [Reg8, Reg8, UInt32],
	'CallWithNewTarget': [Reg8, Reg8, Reg8, UInt8],
	'CallWithNewTargetLong': [Reg8, Reg8, Reg8, Reg8],
	'Catch': [Reg8],
	'CoerceThisNS': [Reg8, Reg8],
	'CompleteGenerator': [],
	'Construct': [Reg8, Reg8, UInt8],
	'ConstructLong': [Reg8, Reg8, UInt32],
	'CreateAsyncClosure': [Reg8, Reg8, FunctionRef16],
	'CreateAsyncClosureLongIndex': [Reg8, Reg8, FunctionRef32],
	'CreateBaseClass': [Reg8, Reg8, Reg8, FunctionRef16],
	'CreateBaseClassLongIndex': [Reg8, Reg8, Reg8, FunctionRef32],
	'CreateClosure': [Reg8, Reg8, FunctionRef16],
	'CreateClosureLongIndex': [Reg8, Reg8, FunctionRef32],
	'CreateDerivedClass': [Reg8, Reg8, Reg8, Reg8, FunctionRef16],
	'CreateDerivedClassLongIndex': [Reg8, Reg8, Reg8, Reg8, FunctionRef32],
	'CreateEnvironment': [Reg8, Reg8, UInt32],
	'CreateFunctionEnvironment': [Reg8, UInt8],
	'CreateTopLevelEnvironment': [Reg8, UInt32],
	'CreateInnerEnvironment': [Reg8],
	'CreateGenerator': [Reg8, Reg8, FunctionRef16],
	'CreateGeneratorClosure': [Reg8, Reg8, FunctionRef16],
	'CreateGeneratorClosureLongIndex': [Reg8, Reg8, FunctionRef32],
	'CreateGeneratorLongIndex': [Reg8, Reg8, FunctionRef32],
	'CreateRegExp': [Reg8, StringRef32, StringRef32, UInt32],
	'CreateThis': [Reg8, Reg8, Reg8],
	'CreateThisForNew': [Reg8, Reg8, UInt8],
	'CreateThisForSuper': [Reg8, Reg8, Reg8, UInt8],
	'TypedLoadParent': [Reg8, Reg8],
	'TypedStoreParent': [Reg8, Reg8],
	'Debugger': [],
	'DebuggerCheckBreak': [],
	'Dec': [Reg8, Reg8],
	'DeclareGlobalVar': [StringRef32],
	'DelById': [Reg8, Reg8, StringRef16],
	'DelByIdLoose': [Reg8, Reg8, StringRef16],
	'DelByIdStrict': [Reg8, Reg8, StringRef16],
	'DelByIdLong': [Reg8, Reg8, StringRef32],
	'DelByIdLooseLong': [Reg8, Reg8, StringRef32],
	'DelByIdStrictLong': [Reg8, Reg8, StringRef32],
	'DelByVal': [Reg8, Reg8, Reg8, UInt8],
	'DelByValLoose': [Reg8, Reg8, Reg8, UInt8],
	'DelByValStrict': [Reg8, Reg8, Reg8, UInt8],
	'DirectEval': [Reg8, Reg8, UInt8],
	'Div': [Reg8, Reg8, Reg8],
	'DivN': [Reg8, Reg8, Reg8],
	'Divi32': [Reg8, Reg8, Reg8],
	'Divu32': [Reg8, Reg8, Reg8],
	'Eq': [Reg8, Reg8, Reg8],
	'GetArgumentsLength': [Reg8, Reg8],
	'GetArgumentsPropByVal': [Reg8, Reg8, Reg8],
	'GetArgumentsPropByValLoose': [Reg8, Reg8, Reg8],
	'GetArgumentsPropByValStrict': [Reg8, Reg8, Reg8],
	'GetBuiltinClosure': [Reg8, UInt8],
	'GetById': [Reg8, Reg8, UInt8, StringRef16],
	'GetByIdLong': [Reg8, Reg8, UInt8, StringRef32],
	'GetByIdShort': [Reg8, Reg8, UInt8, StringRef8],
	'GetByIdWithReceiverLong': [Reg8, Reg8, UInt8, Reg8, StringRef32],
	'GetByVal': [Reg8, Reg8, Reg8],
	'GetByIndex': [Reg8, Reg8, UInt8],
	'GetByValWithReceiver': [Reg8, Reg8, Reg8, Reg8],
	'GetParentEnvironment': [Reg8, UInt8],
	'GetEnvironment': [Reg8, Reg8, UInt8],
	'GetClosureEnvironment': [Reg8, Reg8],
	'GetGlobalObject': [Reg8],
	'GetNewTarget': [Reg8],
	'LoadParentNoTraps': [Reg8, Reg8],
	'GetNextPName': [Reg8, Reg8, Reg8, Reg8, Reg8],
	'GetPNameList': [Reg8, Reg8, Reg8, Reg8],
	'Greater': [Reg8, Reg8, Reg8],
	'GreaterEq': [Reg8, Reg8, Reg8],
	'Inc': [Reg8, Reg8],
	'InstanceOf': [Reg8, Reg8, Reg8],
	'IsIn': [Reg8, Reg8, Reg8],
	'PrivateIsIn': [Reg8, Reg8, Reg8, Reg8],
	'TypeOfIs': [Reg8, Reg8, UInt16],
	'IteratorBegin': [Reg8, Reg8],
	'IteratorClose': [Reg8, UInt8],
	'IteratorNext': [Reg8, Reg8, Reg8],
	'JEqual': [Addr8, Reg8, Reg8],
	'JEqualLong': [Addr32, Reg8, Reg8],
	'JGreater': [Addr8, Reg8, Reg8],
	'JGreaterEqual': [Addr8, Reg8, Reg8],
	'JGreaterEqualLong': [Addr32, Reg8, Reg8],
	'JGreaterEqualN': [Addr8, Reg8, Reg8],
	'JGreaterEqualNLong': [Addr32, Reg8, Reg8],
	'JGreaterLong': [Addr32, Reg8, Reg8],
	'JGreaterN': [Addr8, Reg8, Reg8],
	'JGreaterNLong': [Addr32, Reg8, Reg8],
	'JLess': [Addr8, Reg8, Reg8],
	'JLessEqual': [Addr8, Reg8, Reg8],
	'JLessEqualLong': [Addr32, Reg8, Reg8],
	'JLessEqualN': [Addr8, Reg8, Reg8],
	'JLessEqualNLong': [Addr32, Reg8, Reg8],
	'JLessLong': [Addr32, Reg8, Reg8],
	'JLessN': [Addr8, Reg8, Reg8],
	'JLessNLong': [Addr32, Reg8, Reg8],
	'JNotEqual': [Addr8, Reg8, Reg8],
	'JNotEqualLong': [Addr32, Reg8, Reg8],
	'JNotGreater': [Addr8, Reg8, Reg8],
	'JNotGreaterEqual': [Addr8, Reg8, Reg8],
	'JNotGreaterEqualLong': [Addr32, Reg8, Reg8],
	'JNotGreaterEqualN': [Addr8, Reg8, Reg8],
	'JNotGreaterEqualNLong': [Addr32, Reg8, Reg8],
	'JNotGreaterLong': [Addr32, Reg8, Reg8],
	'JNotGreaterN': [Addr8, Reg8, Reg8],
	'JNotGreaterNLong': [Addr32, Reg8, Reg8],
	'JNotLess': [Addr8, Reg8, Reg8],
	'JNotLessEqual': [Addr8, Reg8, Reg8],
	'JNotLessEqualLong': [Addr32, Reg8, Reg8],
	'JNotLessEqualN': [Addr8, Reg8, Reg8],
	'JNotLessEqualNLong': [Addr32, Reg8, Reg8],
	'JNotLessLong': [Addr32, Reg8, Reg8],
	'JNotLessN': [Addr8, Reg8, Reg8],
	'JNotLessNLong': [Addr32, Reg8, Reg8],
	'JStrictEqual': [Addr8, Reg8, Reg8],
	'JStrictEqualLong': [Addr32, Reg8, Reg8],
	'JStrictNotEqual': [Addr8, Reg8, Reg8],
	'JStrictNotEqualLong': [Addr32, Reg8, Reg8],
	'Jmp': [Addr8],
	'JmpFalse': [Addr8, Reg8],
	'JmpFalseLong': [Addr32, Reg8],
	'JmpLong': [Addr32],
	'JmpTrue': [Addr8, Reg8],
	'JmpTrueLong': [Addr32, Reg8],
	'JmpUndefined': [Addr8, Reg8],
	'JmpUndefinedLong': [Addr32, Reg8],
	'JmpTypeOfIs': [Addr32, Reg8, UInt16],
	'JmpBuiltinIs': [Addr8, UInt8, Reg8],
	'JmpBuiltinIsLong': [Addr32, UInt8, Reg8],
	'JmpBuiltinIsNot': [Addr8, UInt8, Reg8],
	'JmpBuiltinIsNotLong': [Addr32, UInt8, Reg8],
	'LShift': [Reg8, Reg8, Reg8],
	'Less': [Reg8, Reg8, Reg8],
	'LessEq': [Reg8, Reg8, Reg8],
	'LoadConstBigInt': [Reg8, BigIntRef16],
	'LoadConstBigIntLongIndex': [Reg8, BigIntRef32],
	'LoadConstDouble': [Reg8, Double],
	'LoadConstEmpty': [Reg8],
	'LoadConstFalse': [Reg8],
	'LoadConstInt': [Reg8, Imm32],
	'LoadConstNull': [Reg8],
	'LoadConstString': [Reg8, StringRef16],
	'LoadConstStringLongIndex': [Reg8, StringRef32],
	'LoadConstTrue': [Reg8],
	'LoadConstUInt8': [Reg8, UInt8],
	'LoadConstUndefined': [Reg8],
	'LoadConstZero': [Reg8],
	'LoadFromEnvironment': [Reg8, Reg8, UInt8],
	'LoadFromEnvironmentL': [Reg8, Reg8, UInt16],
	'LoadParam': [Reg8, UInt8],
	'LoadParamLong': [Reg8, UInt32],
	'LoadThisNS': [Reg8],
	'Loadi16': [Reg8, Reg8, Reg8],
	'Loadi32': [Reg8, Reg8, Reg8],
	'Loadi8': [Reg8, Reg8, Reg8],
	'Loadu16': [Reg8, Reg8, Reg8],
	'Loadu32': [Reg8, Reg8, Reg8],
	'Loadu8': [Reg8, Reg8, Reg8],
	'Mod': [Reg8, Reg8, Reg8],
	'Mov': [Reg8, Reg8],
	'MovLong': [Reg32, Reg32],
	'Mul': [Reg8, Reg8, Reg8],
	'Mul32': [Reg8, Reg8, Reg8],
	'MulN': [Reg8, Reg8, Reg8],
	'Negate': [Reg8, Reg8],
	'Neq': [Reg8, Reg8, Reg8],
	'NewArray': [Reg8, UInt16],
	'NewFastArray': [Reg8, Reg8, UInt16],
	'FastArrayLength': [Reg8, Reg8],
	'FastArrayLoad': [Reg8, Reg8, Reg8],
	'FastArrayStore': [Reg8, Reg8, Reg8],
	'FastArrayPush': [Reg8, Reg8],
	'FastArrayAppend': [Reg8, Reg8],
	'NewArrayWithBuffer': [Reg8, UInt16, UInt16, UInt16],
	'NewArrayWithBufferLong': [Reg8, UInt16, UInt16, UInt32],
	'NewObject': [Reg8],
	'NewObjectWithBuffer': [Reg8, UInt16, UInt16],
	'NewObjectWithBufferLong': [Reg8, UInt32, UInt32],
	'NewObjectWithBufferAndParent': [Reg8, Reg8, UInt32, UInt32],
	'NewTypedObjectWithBuffer': [Reg8, Reg8, UInt32, UInt32, UInt8],
	'NewObjectWithParent': [Reg8, Reg8],
	'Not': [Reg8, Reg8],
	'ProfilePoint': [UInt16],
	'PutById': [Reg8, Reg8, UInt8, StringRef16],
	'PutByIdLoose': [Reg8, Reg8, UInt8, StringRef16],
	'PutByIdStrict': [Reg8, Reg8, UInt8, StringRef16],
	'PutByIdLong': [Reg8, Reg8, UInt8, StringRef32],
	'PutByIdLooseLong': [Reg8, Reg8, UInt8, StringRef32],
	'PutByIdStrictLong': [Reg8, Reg8, UInt8, StringRef32],
	'PutByVal': [Reg8, Reg8, Reg8],
	'PutByValLoose': [Reg8, Reg8, Reg8],
	'PutByValStrict': [Reg8, Reg8, Reg8],
	'PutByValWithReceiver': [Reg8, Reg8, Reg8, Reg8, UInt8],
	'PutNewOwnById': [Reg8, Reg8, StringRef16],
	'PutNewOwnByIdLong': [Reg8, Reg8, StringRef32],
	'DefineOwnById': [Reg8, Reg8, UInt8, StringRef16],
	'DefineOwnByIdLong': [Reg8, Reg8, UInt8, StringRef32],
	'PutNewOwnByIdShort': [Reg8, Reg8, StringRef8],
	'PutNewOwnNEById': [Reg8, Reg8, StringRef16],
	'PutNewOwnNEByIdLong': [Reg8, Reg8, StringRef32],
	'PutOwnByIndex': [Reg8, Reg8, UInt8],
	'PutOwnByIndexL': [Reg8, Reg8, UInt32],
	'DefineOwnByIndex': [Reg8, Reg8, UInt8],
	'DefineOwnByIndexL': [Reg8, Reg8, UInt32],
	'DefineOwnInDenseArray': [Reg8, Reg8, UInt8],
	'DefineOwnInDenseArrayL': [Reg8, Reg8, UInt16],
	'PutOwnByVal': [Reg8, Reg8, Reg8, UInt8],
	'PutOwnBySlotIdx': [Reg8, Reg8, UInt8],
	'PutOwnBySlotIdxLong': [Reg8, Reg8, UInt32],
	'GetOwnBySlotIdx': [Reg8, Reg8, UInt8],
	'GetOwnBySlotIdxLong': [Reg8, Reg8, UInt32],
	'DefineOwnByVal': [Reg8, Reg8, Reg8, UInt8],
	'PutOwnGetterSetterByVal': [Reg8, Reg8, Reg8, Reg8, UInt8],
	'DefineOwnGetterSetterByVal': [Reg8, Reg8, Reg8, Reg8, UInt8],
	'RShift': [Reg8, Reg8, Reg8],
	'ReifyArguments': [Reg8],
	'ReifyArgumentsLoose': [Reg8],
	'ReifyArgumentsStrict': [Reg8],
	'ToPropertyKey': [Reg8, Reg8],
	'ResumeGenerator': [Reg8, Reg8],
	'Ret': [Reg8],
	'SaveGenerator': [Addr8],
	'SaveGeneratorLong': [Addr32],
	'SelectObject': [Reg8, Reg8, Reg8],
	'StartGenerator': [],
	'Store16': [Reg8, Reg8, Reg8],
	'Store32': [Reg8, Reg8, Reg8],
	'Store8': [Reg8, Reg8, Reg8],
	'StoreNPToEnvironment': [Reg8, UInt8, Reg8],
	'StoreNPToEnvironmentL': [Reg8, UInt16, Reg8],
	'StoreToEnvironment': [Reg8, UInt8, Reg8],
	'StoreToEnvironmentL': [Reg8, UInt16, Reg8],
	'StrictEq': [Reg8, Reg8, Reg8],
	'StrictNeq': [Reg8, Reg8, Reg8],
	'Sub': [Reg8, Reg8, Reg8],
	'Sub32': [Reg8, Reg8, Reg8],
	'SubN': [Reg8, Reg8, Reg8],
	'SwitchImm': [Reg8, UInt32, Addr32, UInt32, UInt32],
	'UIntSwitchImm': [Reg8, UInt32, Addr32, UInt32, UInt32],
	'StringSwitchImm': [Reg8, UInt32, Addr32, UInt32, UInt32],
	'Throw': [Reg8],
	'ThrowIfEmpty': [Reg8, Reg8],
	'ThrowIfUndefined': [Reg8],
	'ThrowIfHasRestrictedGlobalProperty': [StringRef32],
	'ThrowIfThisInitialized': [Reg8],
	'ToInt32': [Reg8, Reg8],
	'ToUint32': [Reg8, Reg8],
	'ToNumber': [Reg8, Reg8],
	'ToNumeric': [Reg8, Reg8],
	'TryGetById': [Reg8, Reg8, UInt8, StringRef16],
	'TryGetByIdLong': [Reg8, Reg8, UInt8, StringRef32],
	'TryPutById': [Reg8, Reg8, UInt8, StringRef16],
	'TryPutByIdLoose': [Reg8, Reg8, UInt8, StringRef16],
	'TryPutByIdStrict': [Reg8, Reg8, UInt8, StringRef16],
	'TryPutByIdLong': [Reg8, Reg8, UInt8, StringRef32],
	'TryPutByIdLooseLong': [Reg8, Reg8, UInt8, StringRef32],
	'TryPutByIdStrictLong': [Reg8, Reg8, UInt8, StringRef32],
	'TypeOf': [Reg8, Reg8],
	'URShift': [Reg8, Reg8, Reg8],
	'Unreachable': [],
} as const;

export type RawMnemonic = keyof typeof RAW_OPERANDS;

export const InstructionNormalisationMap = {
	'AddN': {
		instruction: 'Add',
		type: InstructionType.NUMERIC,
	},
	'MulN': {
		instruction: 'Mul',
		type: InstructionType.NUMERIC,
	},
	'DivN': {
		instruction: 'Div',
		type: InstructionType.NUMERIC,
	},
	'SubN': {
		instruction: 'Sub',
		type: InstructionType.NUMERIC,
	},
	'CallLong': {
		instruction: 'Call',
		length: InstructionLength.LONG,
	},
	'ConstructLong': {
		instruction: 'Construct',
		length: InstructionLength.LONG,
	},
	'MovLong': {
		instruction: 'Mov',
		length: InstructionLength.LONG,
	},
	'LoadParamLong': {
		instruction: 'LoadParam',
		length: InstructionLength.LONG,
	},
	'LoadFromEnvironmentL': {
		instruction: 'LoadFromEnvironment',
		length: InstructionLength.LONG,
	},
	'CreateClosureLongIndex': {
		instruction: 'CreateClosure',
		length: InstructionLength.LONG,
	},
	'CreateAsyncClosureLongIndex': {
		instruction: 'CreateAsyncClosure',
		length: InstructionLength.LONG,
	},
	'CreateGeneratorClosureLongIndex': {
		instruction: 'CreateGeneratorClosure',
		length: InstructionLength.LONG,
	},
	'CreateGeneratorLongIndex': {
		instruction: 'CreateGenerator',
		length: InstructionLength.LONG,
	},
	'CreateBaseClassLongIndex': {
		instruction: 'CreateBaseClass',
		length: InstructionLength.LONG,
	},
	'CreateDerivedClassLongIndex': {
		instruction: 'CreateDerivedClass',
		length: InstructionLength.LONG,
	},
	'PutOwnByIndexL': {
		instruction: 'DefineOwnByIndex',
		length: InstructionLength.LONG,
	},
	'PutOwnByIndex': {
		instruction: 'DefineOwnByIndex',
	},
	'DefineOwnByIndexL': {
		instruction: 'DefineOwnByIndex',
		length: InstructionLength.LONG,
	},
	'PutOwnByVal': {
		instruction: 'DefineOwnByVal',
	},
	'PutOwnBySlotIdxLong': {
		instruction: 'PutOwnBySlotIdx',
		length: InstructionLength.LONG,
	},
	'GetOwnBySlotIdx': {
		instruction: 'GetBySlotIdx',
	},
	'GetOwnBySlotIdxLong': {
		instruction: 'GetBySlotIdx',
		length: InstructionLength.LONG,
	},
	'PutOwnGetterSetterByVal': {
		instruction: 'DefineOwnGetterSetterByVal',
	},
	'GetByIdShort': {
		instruction: 'GetById',
		length: InstructionLength.SHORT,
	},
	'GetByIdLong': {
		instruction: 'GetById',
		length: InstructionLength.LONG,
	},
	'GetByIdWithReceiverLong': {
		instruction: 'GetByIdWithReceiver',
		length: InstructionLength.LONG,
	},
	'TryGetByIdLong': {
		instruction: 'TryGetById',
		length: InstructionLength.LONG,
	},
	'DelByIdLong': {
		instruction: 'DelById',
		length: InstructionLength.LONG,
	},
	'DelByIdLoose': {
		instruction: 'DelById',
		strict: InstructionStrictness.LOOSE,
	},
	'DelByIdStrict': {
		instruction: 'DelById',
		strict: InstructionStrictness.STRICT,
	},
	'DelByIdLooseLong': {
		instruction: 'DelById',
		length: InstructionLength.LONG,
		strict: InstructionStrictness.LOOSE,
	},
	'DelByIdStrictLong': {
		instruction: 'DelById',
		length: InstructionLength.LONG,
		strict: InstructionStrictness.STRICT,
	},
	'DelByValLoose': {
		instruction: 'DelByVal',
		strict: InstructionStrictness.LOOSE,
	},
	'DelByValStrict': {
		instruction: 'DelByVal',
		strict: InstructionStrictness.STRICT,
	},
	'PutByIdLong': {
		instruction: 'PutById',
		length: InstructionLength.LONG,
	},
	'PutByIdLoose': {
		instruction: 'PutById',
		strict: InstructionStrictness.LOOSE,
	},
	'PutByIdStrict': {
		instruction: 'PutById',
		strict: InstructionStrictness.STRICT,
	},
	'PutByIdLooseLong': {
		instruction: 'PutById',
		length: InstructionLength.LONG,
		strict: InstructionStrictness.LOOSE,
	},
	'PutByIdStrictLong': {
		instruction: 'PutById',
		length: InstructionLength.LONG,
		strict: InstructionStrictness.STRICT,
	},
	'TryPutByIdLong': {
		instruction: 'TryPutById',
		length: InstructionLength.LONG,
	},
	'TryPutByIdLoose': {
		instruction: 'TryPutById',
		strict: InstructionStrictness.LOOSE,
	},
	'TryPutByIdStrict': {
		instruction: 'TryPutById',
		strict: InstructionStrictness.STRICT,
	},
	'TryPutByIdLooseLong': {
		instruction: 'TryPutById',
		length: InstructionLength.LONG,
		strict: InstructionStrictness.LOOSE,
	},
	'TryPutByIdStrictLong': {
		instruction: 'TryPutById',
		length: InstructionLength.LONG,
		strict: InstructionStrictness.STRICT,
	},
	'PutByValLoose': {
		instruction: 'PutByVal',
		strict: InstructionStrictness.LOOSE,
	},
	'PutByValStrict': {
		instruction: 'PutByVal',
		strict: InstructionStrictness.STRICT,
	},
	'StoreToEnvironmentL': {
		instruction: 'StoreToEnvironment',
		length: InstructionLength.LONG,
	},
	'StoreNPToEnvironmentL': {
		instruction: 'StoreNPToEnvironment',
		length: InstructionLength.LONG,
	},
	'JmpLong': {
		instruction: 'Jmp',
		length: InstructionLength.LONG,
	},
	'JmpTrueLong': {
		instruction: 'JmpTrue',
		length: InstructionLength.LONG,
	},
	'JmpFalseLong': {
		instruction: 'JmpFalse',
		length: InstructionLength.LONG,
	},
	'JmpUndefinedLong': {
		instruction: 'JmpUndefined',
		length: InstructionLength.LONG,
	},
	'JmpBuiltinIsLong': {
		instruction: 'JmpBuiltinIs',
		length: InstructionLength.LONG,
	},
	'JmpBuiltinIsNotLong': {
		instruction: 'JmpBuiltinIsNot',
		length: InstructionLength.LONG,
	},
	'JLessLong': {
		instruction: 'JLess',
		length: InstructionLength.LONG,
	},
	'JLessN': {
		instruction: 'JLess',
		type: InstructionType.NUMERIC,
	},
	'JLessNLong': {
		instruction: 'JLess',
		length: InstructionLength.LONG,
		type: InstructionType.NUMERIC,
	},
	'JNotLessLong': {
		instruction: 'JNotLess',
		length: InstructionLength.LONG,
	},
	'JNotLessN': {
		instruction: 'JNotLess',
		type: InstructionType.NUMERIC,
	},
	'JNotLessNLong': {
		instruction: 'JNotLess',
		length: InstructionLength.LONG,
		type: InstructionType.NUMERIC,
	},
	'JLessEqualLong': {
		instruction: 'JLessEqual',
		length: InstructionLength.LONG,
	},
	'JLessEqualN': {
		instruction: 'JLessEqual',
		type: InstructionType.NUMERIC,
	},
	'JLessEqualNLong': {
		instruction: 'JLessEqual',
		length: InstructionLength.LONG,
		type: InstructionType.NUMERIC,
	},
	'JNotLessEqualLong': {
		instruction: 'JNotLessEqual',
		length: InstructionLength.LONG,
	},
	'JNotLessEqualN': {
		instruction: 'JNotLessEqual',
		type: InstructionType.NUMERIC,
	},
	'JNotLessEqualNLong': {
		instruction: 'JNotLessEqual',
		length: InstructionLength.LONG,
		type: InstructionType.NUMERIC,
	},
	'JGreaterLong': {
		instruction: 'JGreater',
		length: InstructionLength.LONG,
	},
	'JGreaterN': {
		instruction: 'JGreater',
		type: InstructionType.NUMERIC,
	},
	'JGreaterNLong': {
		instruction: 'JGreater',
		length: InstructionLength.LONG,
		type: InstructionType.NUMERIC,
	},
	'JNotGreaterLong': {
		instruction: 'JNotGreater',
		length: InstructionLength.LONG,
	},
	'JNotGreaterN': {
		instruction: 'JNotGreater',
		type: InstructionType.NUMERIC,
	},
	'JNotGreaterNLong': {
		instruction: 'JNotGreater',
		length: InstructionLength.LONG,
		type: InstructionType.NUMERIC,
	},
	'JGreaterEqualLong': {
		instruction: 'JGreaterEqual',
		length: InstructionLength.LONG,
	},
	'JGreaterEqualN': {
		instruction: 'JGreaterEqual',
		type: InstructionType.NUMERIC,
	},
	'JGreaterEqualNLong': {
		instruction: 'JGreaterEqual',
		length: InstructionLength.LONG,
		type: InstructionType.NUMERIC,
	},
	'JNotGreaterEqualLong': {
		instruction: 'JNotGreaterEqual',
		length: InstructionLength.LONG,
	},
	'JNotGreaterEqualN': {
		instruction: 'JNotGreaterEqual',
		type: InstructionType.NUMERIC,
	},
	'JNotGreaterEqualNLong': {
		instruction: 'JNotGreaterEqual',
		length: InstructionLength.LONG,
		type: InstructionType.NUMERIC,
	},
	'JEqualLong': {
		instruction: 'JEqual',
		length: InstructionLength.LONG,
	},
	'JNotEqualLong': {
		instruction: 'JNotEqual',
		length: InstructionLength.LONG,
	},
	'JStrictEqualLong': {
		instruction: 'JStrictEqual',
		length: InstructionLength.LONG,
	},
	'JStrictNotEqualLong': {
		instruction: 'JStrictNotEqual',
		length: InstructionLength.LONG,
	},
	'PutNewOwnByIdShort': {
		instruction: 'PutNewOwnById',
		length: InstructionLength.SHORT,
	},
	'PutNewOwnByIdLong': {
		instruction: 'PutNewOwnById',
		length: InstructionLength.LONG,
	},
	'DefineOwnByIdLong': {
		instruction: 'DefineOwnById',
		length: InstructionLength.LONG,
	},
	'NewObjectWithBufferLong': {
		instruction: 'NewObjectWithBuffer',
		length: InstructionLength.LONG,
	},
	'NewArrayWithBufferLong': {
		instruction: 'NewArrayWithBuffer',
		length: InstructionLength.LONG,
	},
	'ReifyArgumentsLoose': {
		instruction: 'ReifyArguments',
		strict: InstructionStrictness.LOOSE,
	},
	'ReifyArgumentsStrict': {
		instruction: 'ReifyArguments',
		strict: InstructionStrictness.STRICT,
	},
	'CallWithNewTarget': {
		instruction: 'Call',
	},
	'CallWithNewTargetLong': {
		instruction: 'Call',
		length: InstructionLength.LONG,
	},
	'SaveGeneratorLong': {
		instruction: 'SaveGenerator',
		length: InstructionLength.LONG,
	},
	// v99 renames
	'SwitchImm': {
		instruction: 'UIntSwitchImm',
	},
} as const satisfies Partial<
	Record<
		RawMnemonic,
		Partial<{
			instruction: keyof Instructions;
			length: InstructionLength;
			type: InstructionType;
			strict: InstructionStrictness;
		}>
	>
>;

export type Instruction = Instructions[keyof Instructions];

export function createInstruction(
	mnemonic: string,
	operands: Operand[],
	functionLocalOffset: number,
	version?: VersionInfo,
	frameSize?: number,
): Instruction {
	type ExpectedInstruction<T extends string> = Instructions[
		T extends keyof typeof InstructionNormalisationMap
			? typeof InstructionNormalisationMap[T]['instruction']
			: T extends keyof Instructions ? T
			: never
	];

	let instruction = mnemonic;
	let length = InstructionLength.NORMAL;
	let type = InstructionType.NORMAL;
	let strict = InstructionStrictness.NORMAL;
	if (mnemonic in InstructionNormalisationMap) {
		({ instruction, length, type, strict } = {
			length,
			type,
			strict,
			...InstructionNormalisationMap[
				mnemonic as keyof typeof InstructionNormalisationMap
			],
		});
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
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'DeclareGlobalVar': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				identifier: checkStringRef(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'GetGlobalObject':
		case 'NewObject':
		case 'LoadThisNS':
		case 'Catch': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'NewObjectWithParent': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				parent: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'CreateEnvironment': {
			if (version && version.bytecodeVersion >= 97) {
				return {
					functionLocalOffset,
					instruction,
					length,
					type,
					strict,
					destination: checkRegister(operands[0]),
					parent: checkRegister(operands[1]),
					envSize: checkImmediate(operands[2]),
				} as ExpectedInstruction<typeof mnemonic>;
			}
		}
		/* falls through */
		case 'CreateFunctionEnvironment': {
			let envSize: number | undefined;
			if (version && version.bytecodeVersion >= 97) {
				envSize = checkImmediate(operands[1]);
			}
			return {
				functionLocalOffset,
				instruction: 'CreateFunctionEnvironment',
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				envSize,
			} as ExpectedInstruction<'CreateFunctionEnvironment'>;
		}

		case 'CreateTopLevelEnvironment': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				envSize: checkImmediate(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'GetEnvironment': {
			if (version && version.bytecodeVersion >= 97) {
				return {
					functionLocalOffset,
					instruction,
					length,
					type,
					strict,
					destination: checkRegister(operands[0]),
					parentEnv: checkRegister(operands[1]),
					levelIndex: checkImmediate(operands[2]),
				} as ExpectedInstruction<typeof mnemonic>;
			}
		}
		/* falls through */
		case 'GetParentEnvironment': {
			return {
				functionLocalOffset,
				instruction: 'GetParentEnvironment',
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				levelIndex: checkImmediate(operands[1]),
			} as ExpectedInstruction<'GetParentEnvironment'>;
		}

		case 'GetClosureEnvironment': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				closure: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'LoadFromEnvironment':
		case 'LoadFromEnvironmentL': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				environment: checkRegister(operands[1]),
				slotIndex: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'Ret': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				argument: checkRegister(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'DirectEval': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				code: checkRegister(operands[1]),
				// v95 added the `strictCaller` operand; reading it
				// unconditionally threw on every older bundle. The legacy
				// 2-operand form ran the text in a dummy scope chain — "as per
				// the spec for strict callers, which is the only thing we
				// support" — so a strict caller is the faithful legacy value.
				isStrict: operands.length > 2
					? checkImmediate(operands[2]) != 0
					: true,
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'Throw': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				exception: checkRegister(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'ThrowIfEmpty': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				source: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'ThrowIfUndefined': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				source: checkRegister(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'ThrowIfThisInitialized': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				thisObject: checkRegister(operands[0]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'LoadParam':
		case 'LoadParamLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				parameterIndex: checkImmediate(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'Mov':
		case 'MovLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				source: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'CreateThis': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				prototype: checkRegister(operands[1]),
				constructorRef: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'CreateThisForNew': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				closure: checkRegister(operands[1]),
				prototypeCacheIndex: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'CreateThisForSuper': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				closure: checkRegister(operands[1]),
				newTarget: checkRegister(operands[2]),
				prototypeCacheIndex: checkImmediate(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'SelectObject': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

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
				strict,

				destination: checkRegister(operands[0]),
				closure: checkRegister(operands[1]),
				arguments: callArgs,
			};
		}

		case 'Call':
		case 'CallLong':
		case 'Construct':
		case 'ConstructLong': {
			if (
				typeof version == 'undefined' || typeof frameSize == 'undefined'
			) {
				throw new Error();
			}

			const argumentCount = checkImmediate(operands[2]);
			const args: Register[] = [];
			const lastArg = frameSize +
				getStackOffset(version, NamedStackVariables.ThisArg);
			for (let i = lastArg; i > lastArg - argumentCount; i--) {
				args.push({ type: 'register', index: i });
			}

			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				closure: checkRegister(operands[1]),
				argumentCount,
				arguments: args,
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'CallWithNewTarget':
		case 'CallWithNewTargetLong': {
			if (
				typeof version == 'undefined' || typeof frameSize == 'undefined'
			) {
				throw new Error();
			}

			const rawArgumentCount = operands[3];
			const argumentCount = typeof rawArgumentCount === 'number'
				? rawArgumentCount
				: checkRegister(rawArgumentCount).index;
			const args: Register[] = [];
			const lastArg = frameSize +
				getStackOffset(version, NamedStackVariables.ThisArg);
			for (let i = lastArg; i > lastArg - argumentCount; i--) {
				args.push({ type: 'register', index: i });
			}

			return {
				functionLocalOffset,
				instruction: 'Call',
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				closure: checkRegister(operands[1]),
				newTarget: checkRegister(operands[2]),
				argumentCount,
				arguments: args,
			} as ExpectedInstruction<'Call'>;
		}

		case 'CallDirect':
		case 'CallDirectLongIndex': {
			if (
				typeof version == 'undefined' || typeof frameSize == 'undefined'
			) {
				throw new Error();
			}

			const argumentCount = checkImmediate(operands[2]);
			const args: Register[] = [];
			const lastArg = frameSize +
				getStackOffset(version, NamedStackVariables.ThisArg);
			for (let i = lastArg; i > lastArg - argumentCount; i--) {
				args.push({ type: 'register', index: i });
			}

			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				function: checkFunctionRef(operands[1]),
				argumentCount,
				arguments: args,
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'CallBuiltin':
		case 'CallBuiltinLong': {
			if (
				typeof version == 'undefined' || typeof frameSize == 'undefined'
			) {
				throw new Error();
			}

			const argumentCount = checkImmediate(operands[2]);
			const args: Register[] = [];
			const lastArg = frameSize +
				getStackOffset(version, NamedStackVariables.FirstArg);
			for (let i = lastArg; i > lastArg - (argumentCount - 1); i--) {
				args.push({ type: 'register', index: i });
			}

			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				builtinNo: checkImmediate(operands[1]),
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
		case 'AddEmptyString':
		case 'ToNumber':
		case 'ToNumeric':
		case 'ToInt32':
		case 'ToPropertyKey':
		case 'ToUint32':
		case 'LoadParentNoTraps':
		case 'CoerceThisNS': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				argument: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'NewArray': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				size: checkImmediate(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'NewArrayWithBuffer':
		case 'NewArrayWithBufferLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				sizeHint: checkImmediate(operands[1]),
				noOfStaticElements: checkImmediate(operands[2]),
				arrayBufferIndex: checkImmediate(operands[3]),
			} as ExpectedInstruction<'NewArrayWithBuffer'>;
		}

		case 'NewObjectWithBuffer':
		case 'NewObjectWithBufferLong': {
			if (operands.length === 3) {
				return {
					functionLocalOffset,
					instruction,
					length,
					type,
					strict,

					destination: checkRegister(operands[0]),
					shapeTableIndex: checkImmediate(operands[1]),
					objectValueBufferIndex: checkImmediate(operands[2]),
				} as ExpectedInstruction<'NewObjectWithBuffer'>;
			} else {
				return {
					functionLocalOffset,
					instruction,
					length,
					type,
					strict,

					destination: checkRegister(operands[0]),
					sizeHint: checkImmediate(operands[1]),
					noOfStaticElements: checkImmediate(operands[2]),
					objectKeyBufferIndex: checkImmediate(operands[3]),
					objectValueBufferIndex: checkImmediate(operands[4]),
				} as ExpectedInstruction<'NewObjectWithBuffer'>;
			}
		}

		case 'NewObjectWithBufferAndParent': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				parent: checkRegister(operands[1]),
				shapeTableIndex: checkImmediate(operands[2]),
				objectValueBufferIndex: checkImmediate(operands[3]),
			} as ExpectedInstruction<'NewObjectWithBufferAndParent'>;
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
		case 'AddS':
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
				strict,
				destination: checkRegister(operands[0]),
				left: checkRegister(operands[1]),
				right: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'PutById':
		case 'PutByIdLoose':
		case 'PutByIdStrict':
		case 'PutByIdLong':
		case 'PutByIdLooseLong':
		case 'PutByIdStrictLong':
		case 'TryPutById':
		case 'TryPutByIdLoose':
		case 'TryPutByIdStrict':
		case 'TryPutByIdLooseLong':
		case 'TryPutByIdStrictLong':
		case 'TryPutByIdLong':
		case 'DefineOwnById':
		case 'DefineOwnByIdLong': {
			return {
				functionLocalOffset,
				instruction: mnemonic.startsWith('DefineOwnById')
					? 'DefineOwnById'
					: instruction,
				length,
				type,
				strict,

				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
				cacheIndex: checkImmediate(operands[2]),
				property: checkStringRef(operands[3]),
			} as ExpectedInstruction<
				'PutById' | 'TryPutById' | 'DefineOwnById'
			>;
		}
		case 'PutNewOwnByIdShort':
		case 'PutNewOwnById':
		case 'PutNewOwnByIdLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
				property: checkStringRef(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PutOwnByIndex':
		case 'DefineOwnByIndex':
		case 'DefineOwnByIndexL':
		case 'PutOwnByIndexL': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
				property: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PutByVal':
		case 'PutByValLoose':
		case 'PutByValStrict': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				object: checkRegister(operands[0]),
				property: checkRegister(operands[1]),
				value: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PutOwnByVal':
		case 'DefineOwnByVal': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				object: checkRegister(operands[0]),
				property: checkRegister(operands[2]),
				value: checkRegister(operands[1]),
				enumerable: checkImmediate(operands[3]) !== 0,
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PutOwnBySlotIdx':
		case 'PutOwnBySlotIdxLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
				slotIndex: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PutOwnGetterSetterByVal':
		case 'DefineOwnGetterSetterByVal': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				object: checkRegister(operands[0]),
				property: checkRegister(operands[1]),
				getter: checkRegister(operands[2]),
				setter: checkRegister(operands[3]),
				enumerable: checkImmediate(operands[4]) !== 0,
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
				strict,

				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				cacheIndex: checkImmediate(operands[2]),
				property: checkStringRef(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'GetByIdWithReceiverLong': {
			return {
				functionLocalOffset,
				instruction: 'GetByIdWithReceiver',
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				cacheIndex: checkImmediate(operands[2]),
				receiver: checkRegister(operands[3]),
				property: checkStringRef(operands[4]),
			} as ExpectedInstruction<'GetByIdWithReceiver'>;
		}
		case 'GetOwnBySlotIdx':
		case 'GetOwnBySlotIdxLong':
		case 'GetBySlotIdx':
		case 'GetBySlotIdxLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				slotIndex: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'GetByIndex': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				index: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'GetByVal': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				property: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'DelById':
		case 'DelByIdLong':
		case 'DelByIdLoose':
		case 'DelByIdStrict':
		case 'DelByIdLooseLong':
		case 'DelByIdStrictLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				property: checkStringRef(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'DelByVal': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				property: checkRegister(operands[2]),
				flags: operands.length > 3 ? checkImmediate(operands[3]) : 0,
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
				strict,
				environment: checkRegister(operands[0]),
				slotIndex: checkImmediate(operands[1]),
				value: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'CreateClosure':
		case 'CreateClosureLongIndex':
		case 'CreateGeneratorClosure':
		case 'CreateGeneratorClosureLongIndex':
		case 'CreateAsyncClosure':
		case 'CreateAsyncClosureLongIndex': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				environment: checkRegister(operands[1]),
				function: checkFunctionRef(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'CreateGenerator':
		case 'CreateGeneratorLongIndex': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				environment: checkRegister(operands[1]),
				function: checkFunctionRef(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'CreateBaseClass':
		case 'CreateBaseClassLongIndex': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				classOut: checkRegister(operands[0]),
				homeObject: checkRegister(operands[1]),
				environment: checkRegister(operands[2]),
				function: checkFunctionRef(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'CreateDerivedClass':
		case 'CreateDerivedClassLongIndex': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				classOut: checkRegister(operands[0]),
				homeObject: checkRegister(operands[1]),
				environment: checkRegister(operands[2]),
				superClass: checkRegister(operands[3]),
				function: checkFunctionRef(operands[4]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'ResumeGenerator': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
				isReturn: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'GetPNameList': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				index: checkRegister(operands[2]),
				propertyListSize: checkRegister(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'GetNextPName': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				index: checkRegister(operands[2]),
				propertyListSize: checkRegister(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'IteratorBegin': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				source: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'IteratorNext': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				iterator: checkRegister(operands[1]),
				sourceOrNext: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'IteratorClose': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				iterator: checkRegister(operands[0]),
				ignoreException: checkImmediate(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'CreateRegExp': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

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
				strict,

				destination: checkRegister(operands[0]),
				builtinNo: checkImmediate(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'SwitchImm':
		case 'UIntSwitchImm': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				discriminant: checkRegister(operands[0]),
				jumpTableOffset: checkImmediate(operands[1]),
				defaultJumpOffset: checkImmediate(operands[2]),
				minValue: checkImmediate(operands[3]),
				maxValue: checkImmediate(operands[4]),
			} as ExpectedInstruction<'UIntSwitchImm'>;
		}

		case 'ReifyArguments':
		case 'ReifyArgumentsLoose':
		case 'ReifyArgumentsStrict': {
			return {
				functionLocalOffset,
				instruction: 'ReifyArguments',
				length,
				type,
				strict,

				lazyLoad: checkRegister(operands[0]),
			} as ExpectedInstruction<'ReifyArguments'>;
		}

		case 'GetArgumentsLength': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				lazyLoad: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'GetArgumentsPropByVal':
		case 'GetArgumentsPropByValLoose':
		case 'GetArgumentsPropByValStrict': {
			return {
				functionLocalOffset,
				instruction: 'GetArgumentsPropByVal',
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				argumentsIndex: checkRegister(operands[1]),
				lazyLoad: checkRegister(operands[2]),
			} as ExpectedInstruction<'GetArgumentsPropByVal'>;
		}

		case 'GetNewTarget': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				destination: checkRegister(operands[0]),
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
				strict,

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
				strict,

				relativeTarget: checkImmediate(operands[0]),
				predicate: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'JmpBuiltinIs':
		case 'JmpBuiltinIsLong':
		case 'JmpBuiltinIsNot':
		case 'JmpBuiltinIsNotLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				relativeTarget: checkImmediate(operands[0]),
				builtinNo: checkImmediate(operands[1]),
				predicate: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'JLess':
		case 'JLessLong':
		case 'JLessN':
		case 'JLessNLong':
		case 'JNotLess':
		case 'JNotLessLong':
		case 'JNotLessN':
		case 'JNotLessNLong':
		case 'JLessEqual':
		case 'JLessEqualLong':
		case 'JLessEqualN':
		case 'JLessEqualNLong':
		case 'JNotLessEqual':
		case 'JNotLessEqualLong':
		case 'JNotLessEqualN':
		case 'JNotLessEqualNLong':
		case 'JGreater':
		case 'JGreaterLong':
		case 'JGreaterN':
		case 'JGreaterNLong':
		case 'JNotGreater':
		case 'JNotGreaterLong':
		case 'JNotGreaterN':
		case 'JNotGreaterNLong':
		case 'JGreaterEqual':
		case 'JGreaterEqualLong':
		case 'JGreaterEqualN':
		case 'JGreaterEqualNLong':
		case 'JNotGreaterEqual':
		case 'JNotGreaterEqualLong':
		case 'JNotGreaterEqualN':
		case 'JNotGreaterEqualNLong':
		case 'JEqual':
		case 'JEqualLong':
		case 'JEqualN':
		case 'JEqualNLong':
		case 'JNotEqual':
		case 'JNotEqualLong':
		case 'JNotEqualN':
		case 'JNotEqualNLong':
		case 'JStrictEqual':
		case 'JStrictEqualLong':
		case 'JStrictEqualN':
		case 'JStrictEqualNLong':
		case 'JStrictNotEqual':
		case 'JStrictNotEqualLong':
		case 'JStrictNotEqualN':
		case 'JStrictNotEqualNLong': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,

				relativeTarget: checkImmediate(operands[0]),
				left: checkRegister(operands[1]),
				right: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		case 'NewFastArray': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				prototype: checkRegister(operands[1]),
				size: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'FastArrayLength': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				argument: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'FastArrayLoad': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				property: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'FastArrayStore': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				object: checkRegister(operands[0]),
				property: checkRegister(operands[1]),
				value: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'FastArrayPush': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'FastArrayAppend': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'StringSwitchImm': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				discriminant: checkRegister(operands[0]),
				globalIndex: checkImmediate(operands[1]),
				jumpTableOffset: checkImmediate(operands[2]),
				defaultJumpOffset: checkImmediate(operands[3]),
				size: checkImmediate(operands[4]),
				stringTableIndices: [],
				relativeTargets: [],
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'CacheNewObject': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				thisObject: checkRegister(operands[0]),
				newTarget: checkRegister(operands[1]),
				shapeId: checkImmediate(operands[2]),
				cacheIndex: checkImmediate(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'DefineOwnInDenseArray':
		case 'DefineOwnInDenseArrayL': {
			return {
				functionLocalOffset,
				instruction: 'DefineOwnInDenseArray',
				length,
				type,
				strict,
				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
				index: checkImmediate(operands[2]),
			} as ExpectedInstruction<'DefineOwnInDenseArray'>;
		}
		case 'TypeOfIs': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
				typeIndex: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PrivateIsIn': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				name: checkRegister(operands[1]),
				object: checkRegister(operands[2]),
				scope: checkRegister(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'JmpTypeOfIs': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				relativeTarget: checkImmediate(operands[0]),
				value: checkRegister(operands[1]),
				typeIndex: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'CreatePrivateName': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				name: checkStringRef(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'AddOwnPrivateBySym': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				object: checkRegister(operands[0]),
				name: checkRegister(operands[1]),
				value: checkRegister(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'GetOwnPrivateBySym': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				cacheIndex: checkImmediate(operands[2]),
				name: checkRegister(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PutOwnPrivateBySym': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				object: checkRegister(operands[0]),
				value: checkRegister(operands[1]),
				cacheIndex: checkImmediate(operands[2]),
				name: checkRegister(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'GetByValWithReceiver': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
				property: checkRegister(operands[2]),
				receiver: checkRegister(operands[3]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'PutByValWithReceiver': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				object: checkRegister(operands[0]),
				property: checkRegister(operands[1]),
				value: checkRegister(operands[2]),
				receiver: checkRegister(operands[3]),
				flags: checkImmediate(operands[4]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'CallRequire': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				callee: checkRegister(operands[1]),
				moduleId: checkImmediate(operands[2]),
			} as ExpectedInstruction<typeof mnemonic>;
		}
		case 'TypedLoadParent': {
			return {
				functionLocalOffset,
				instruction,
				length,
				type,
				strict,
				destination: checkRegister(operands[0]),
				object: checkRegister(operands[1]),
			} as ExpectedInstruction<typeof mnemonic>;
		}

		default:
			throw new Error('Unimplemented mnemonic: ' + mnemonic);
	}
}
