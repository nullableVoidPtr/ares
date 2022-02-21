// deno-lint-ignore-file no-empty-interface

export type RegisterIndex = number;

export interface VMInstruction {}

export interface UnreachableOp extends VMInstruction {}

export interface NewObjectWithBufferInst extends VMInstruction {
	destination: RegisterIndex;
	sizeHint: number;
	noOfStaticElements: number;
	objectKeyBufferIndex: number;
	objectValueBufferIndex: number;
}

export interface NewObjectInst extends VMInstruction {
	destination: RegisterIndex;
}

export interface NewObjectWithParentInst extends VMInstruction {
	destination: RegisterIndex;
	parent: RegisterIndex;
}

export interface NewArrayWithBufferInst extends VMInstruction {
	destination: RegisterIndex;
	sizeHint: number;
	noOfStaticElements: number;
	arrayBufferIndex: number;
}

export interface NewArrayInst extends VMInstruction {
	destination: RegisterIndex;
	size: number;
}

export interface MovInst extends VMInstruction {
	destination: RegisterIndex;
	source: RegisterIndex;
}

export interface UnaryOperationInst extends VMInstruction {
	destination: RegisterIndex;
	operand: RegisterIndex;
}

export interface BinaryOperationInst extends VMInstruction {
	destination: RegisterIndex;
	left: RegisterIndex;
	right: RegisterIndex;
}

export interface NegateInst extends UnaryOperationInst {}
export interface NotInst extends UnaryOperationInst {}
export interface BitNotInst extends UnaryOperationInst {}
export interface TypeOfInst extends UnaryOperationInst {}
export interface EqInst extends BinaryOperationInst {}
export interface StrictEqInst extends BinaryOperationInst {}
export interface NeqInst extends BinaryOperationInst {}
export interface StrictNeqInst extends BinaryOperationInst {}
export interface LessInst extends BinaryOperationInst {}
export interface LessEqInst extends BinaryOperationInst {}
export interface GreaterInst extends BinaryOperationInst {}
export interface GreaterEqInst extends BinaryOperationInst {}
export interface AddInst extends BinaryOperationInst {}
export interface AddNInst extends BinaryOperationInst {}
export interface MulInst extends BinaryOperationInst {}
export interface MulNInst extends BinaryOperationInst {}
export interface DivInst extends BinaryOperationInst {}
export interface DivNInst extends BinaryOperationInst {}
export interface ModInst extends BinaryOperationInst {}
export interface SubInst extends BinaryOperationInst {}
export interface SubNInst extends BinaryOperationInst {}
export interface LShiftInst extends BinaryOperationInst {}
export interface RShiftInst extends BinaryOperationInst {}
export interface URShiftInst extends BinaryOperationInst {}
export interface BitAndInst extends BinaryOperationInst {}
export interface BitXorInst extends BinaryOperationInst {}
export interface BitOrInst extends BinaryOperationInst {}
export interface InstanceOfInst extends BinaryOperationInst {}
export interface IsInInst extends BinaryOperationInst {}

export interface GetEnvironmentInst extends VMInstruction {
	destination: RegisterIndex;
	levelIndex: number;
}

export interface StoreToEnvironmentInst extends VMInstruction {
	environment: RegisterIndex;
	slotIndex: number;
	value: RegisterIndex;
}

export interface StoreNPToEnvironmentInst extends VMInstruction {
	environment: RegisterIndex;
	slotIndex: number;
	value: RegisterIndex;
}

export interface LoadFromEnvironmentInst extends VMInstruction {
	destination: RegisterIndex;
	environment: RegisterIndex;
	slotIndex: number;
}

export interface GetGlobalObjectInst extends VMInstruction {
	destination: RegisterIndex;
}

export interface GetNewTargetInst extends VMInstruction {
	destination: RegisterIndex;
}

export interface CreateEnvironmentInst extends VMInstruction {
	destination: RegisterIndex;
}

export interface DeclareGlobalVarInst extends VMInstruction {
	identifier: string;
}

export interface GetByIdInst extends VMInstruction {
	destination: RegisterIndex;
	object: RegisterIndex;
	cacheIndex: number;
	property: string;
}

export interface TryGetByIdInst extends VMInstruction {
	destination: RegisterIndex;
	object: RegisterIndex;
	cacheIndex: number;
	property: string;
}

export interface PutByIdInst extends VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	cacheIndex: number;
	property: string;
}

export interface TryPutByIdInst extends VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	cacheIndex: number;
	property: string;
}

export interface PutNewOwnByIdInst extends VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	property: string;
}

export interface PutNewOwnNEByIdInst extends VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	property: string;
}

export interface PutOwnByIndexInst extends VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	property: RegisterIndex;
}

export interface PutOwnByValInst extends VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	property: RegisterIndex;
	enumerable: boolean;
}

export interface DelByIdInst extends VMInstruction {
	destination: RegisterIndex;
	object: RegisterIndex;
	property: string;
}

export interface GetByValInst extends VMInstruction {
	destination: RegisterIndex;
	object: RegisterIndex;
	property: RegisterIndex;
}

export interface PutByValInst extends VMInstruction {
	object: RegisterIndex;
	property: RegisterIndex;
	value: RegisterIndex;
}

export interface DelByValInst extends VMInstruction {
	destination: RegisterIndex;
	object: RegisterIndex;
	property: RegisterIndex;
}

export interface PutOwnGetterSetterByValInst extends VMInstruction {
	object: RegisterIndex;
	property: RegisterIndex;
	getter: RegisterIndex;
	setter: RegisterIndex;
	enumerable: booleano;
}

export interface GetPNameListInst extends VMInstruction {
	destination: RegisterIndex;
	object: RegisterIndex;
	index: RegisterIndex;
	propertyListSize: RegisterIndex;
}

export interface GetNextPNameInst extends VMInstruction {
	destination: RegisterIndex;
	object: RegisterIndex;
	index: RegisterIndex;
	propertyListSize: RegisterIndex;
}

export interface CallInst extends VMInstruction {
	destination: RegisterIndex;
	closure: RegisterIndex;
	argumentCount: number;
}

export interface ConstructInst extends VMInstruction {
	destination: RegisterIndex;
	closure: RegisterIndex;
	argumentCount: number;
}

export interface CallNInst extends VMInstruction {
	destination: RegisterIndex;
	closure: RegisterIndex;
	arguments: RegisterIndex[];
}

export interface CallDirectInst extends VMInstruction {
	destination: RegisterIndex;
	argumentCount: number;
	functionIndex: RegisterIndex;
}

export interface CallBuiltinInst extends VMInstruction {
	destination: RegisterIndex;
	builtinNo: RegisterIndex;
	argumentCount: number;
}

export interface CallBuiltinClosureInst extends VMInstruction {
	destination: RegisterIndex;
	builtinNo: RegisterIndex;
}

export interface RetInst extends VMInstruction {
	argument: RegisterIndex;
}

export interface CatchInst extends VMInstruction {
	exception: RegisterIndex;
}

export interface DirectEvalInst extends VMInstruction {
	destination: RegisterIndex;
	code: RegisterIndex;
}

export interface ThrowInst extends VMInstruction {
	exception: RegisterIndex;
}

export interface ThrowIfEmptyInst extends VMInstruction {
	destination: RegisterIndex;
	source: RegisterIndex;
}

export interface DebuggerInst extends VMInstruction {}

export interface AsyncBreakCheckInst extends VMInstruction {}

export interface ProfilePointInst extends VMInstruction {
	profilePoint: number;
}

export interface CreateClosureInst extends VMInstruction {
	destination: RegisterIndex;
	environment: RegisterIndex;
	functionIndex: number;
}

export interface CreateGeneratorClosureInst extends VMInstruction {
	destination: RegisterIndex;
	environment: RegisterIndex;
	functionIndex: number;
}

export interface CreateAsyncClosureInst extends VMInstruction {
	destination: RegisterIndex;
	environment: RegisterIndex;
	functionIndex: number;
}

export interface CreateThisInst extends VMInstruction {
	destination: RegisterIndex;
	prototype: RegisterIndex;
	constructor: RegisterIndex;
}

export interface SelectObjectInst extends VMInstruction {
	destination: RegisterIndex;
	thisObject: RegisterIndex;
	constructorReturnValue: RegisterIndex;
}

export interface LoadParamInst extends VMInstruction {
	destination: RegisterIndex;
	parameterIndex: RegisterIndex;
}

export interface LoadParamInst extends VMInstruction {
	destination: RegisterIndex;
	parameterIndex: RegisterIndex;
}

export interface HermesEmpty {}

export interface LoadConstInst extends VMInstruction {
	destination: RegisterIndex;
	value: number | string | HermesEmpty | void | null | boolean;
}

export interface CoerceThisNSInst extends VMInstruction {
	destination: RegisterIndex;
	argument: RegisterIndex;
}

export interface LoadThisNSInst extends VMInstruction {
	destination: RegisterIndex;
}

export interface ToNumberInst extends VMInstruction {
	destination: RegisterIndex;
	argument: RegisterIndex;
}

export interface ToInt32Inst extends VMInstruction {
	destination: RegisterIndex;
	argument: RegisterIndex;
}

export interface AddEmptyStringInst extends VMInstruction {
	destination: RegisterIndex;
	argument: RegisterIndex;
}

export interface GetArgumentsByPropValInst extends VMInstruction {
	destination: RegisterIndex;
	argumentsIndex: RegisterIndex;
	lazyLoad: RegisterIndex;
}

export interface GetArgumentsLengthInst extends VMInstruction {
	destination: RegisterIndex;
	lazyLoad: RegisterIndex;
}

export interface ReifyArgumentsInst extends VMInstruction {
	lazyLoad: RegisterIndex;
}

export interface CreateRegExpInst extends VMInstruction {
	destination: RegisterIndex;
	pattern: string;
	flags: string;
	regExpBytecodeIndex: number;
}

export interface SwitchImmInst extends VMInstruction {
	discriminant: RegisterIndex;
	jumpTableOffset: number;
	defaultJumpOffset: number;
	minValue: number;
	maxValue: number;
}

export interface StartGeneratorInst extends VMInstruction {}

export interface ResumeGeneratorInst extends VMInstruction {
	value: RegisterIndex;
	isReturn: RegisterIndex;
}

export interface CompleteGeneratorInst extends VMInstruction {}

export interface CreateGeneratorInst extends VMInstruction {
	destination: RegisterIndex;
	environment: RegisterIndex;
	functionIndex: number;
}

export interface IteratorBeginInst extends VMInstruction {
	destination: RegisterIndex;
	source: RegisterIndex;
}

export interface IteratorNextInst extends VMInstruction {
	destination: RegisterIndex;
	iterator: RegisterIndex;
	sourceOrNext: RegisterIndex;
}

export interface IteratorCloseInst extends VMInstruction {
	iterator: RegisterIndex;
	ignoreException: RegisterIndex;
}

export interface IteratorCloseInst extends VMInstruction {
	iterator: RegisterIndex;
	ignoreException: RegisterIndex;
}

export interface JumpingInstruction extends VMInstruction {
	target: number;
}

export interface JmpInst extends VMInstruction {}

export interface JmpTrueInst extends VMInstruction {
	predicate: RegisterIndex;
}

export interface JmpFalseInst extends VMInstruction {
	predicate: RegisterIndex;
}

export interface JmpUndefinedInst extends VMInstruction {
	predicate: RegisterIndex;
}

export interface SaveGenerator extends VMInstruction {}

export interface JumpingBinaryInstruction extends JumpingInstruction {
	left: RegisterIndex;
	right: RegisterIndex;
}

export interface JLess extends JumpingBinaryInstruction {}
export interface JNotLess extends JumpingBinaryInstruction {}
export interface JLessN extends JumpingBinaryInstruction {}
export interface JNotLessN extends JumpingBinaryInstruction {}
export interface JLessEqual extends JumpingBinaryInstruction {}
export interface JNotLessEqual extends JumpingBinaryInstruction {}
export interface JLessEqualN extends JumpingBinaryInstruction {}
export interface JNotLessEqualN extends JumpingBinaryInstruction {}
export interface JGreater extends JumpingBinaryInstruction {}
export interface JNotGreater extends JumpingBinaryInstruction {}
export interface JGreaterN extends JumpingBinaryInstruction {}
export interface JNotGreaterN extends JumpingBinaryInstruction {}
export interface JGreaterEqual extends JumpingBinaryInstruction {}
export interface JNotGreaterEqual extends JumpingBinaryInstruction {}
export interface JGreaterEqualN extends JumpingBinaryInstruction {}
export interface JNotGreaterEqualN extends JumpingBinaryInstruction {}
export interface JEqual extends JumpingBinaryInstruction {}
export interface JNotEqual extends JumpingBinaryInstruction {}
export interface JEqualN extends JumpingBinaryInstruction {}
export interface JNotEqualN extends JumpingBinaryInstruction {}
export interface JStrictEqual extends JumpingBinaryInstruction {}
export interface JStrictNotEqual extends JumpingBinaryInstruction {}

export interface WASMSpecificInstruction extends VMInstruction {}

export interface Add32Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	left: RegisterIndex;
	right: RegisterIndex;
}

export interface Sub32Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	left: RegisterIndex;
	right: RegisterIndex;
}

export interface Mul32Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	left: RegisterIndex;
	right: RegisterIndex;
}

export interface Divi32Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	left: RegisterIndex;
	right: RegisterIndex;
}

export interface Divu32Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	left: RegisterIndex;
	right: RegisterIndex;
}

export interface Loadi8Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	heap: RegisterIndex;
	offset: RegisterIndex;
}

export interface Loadu8Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	heap: RegisterIndex;
	offset: RegisterIndex;
}

export interface Loadi16Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	heap: RegisterIndex;
	offset: RegisterIndex;
}

export interface Loadu16Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	heap: RegisterIndex;
	offset: RegisterIndex;
}

export interface Loadi32Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	heap: RegisterIndex;
	offset: RegisterIndex;
}

export interface Loadu32Inst extends WASMSpecificInstruction {
	destination: RegisterIndex;
	heap: RegisterIndex;
	offset: RegisterIndex;
}

export interface Store8Inst extends WASMSpecificInstruction {
	heap: RegisterIndex;
	offset: RegisterIndex;
	value: RegisterIndex;
}

export interface Store16Inst extends WASMSpecificInstruction {
	heap: RegisterIndex;
	offset: RegisterIndex;
	value: RegisterIndex;
}

export interface Store32Inst extends WASMSpecificInstruction {
	heap: RegisterIndex;
	offset: RegisterIndex;
	value: RegisterIndex;
}
