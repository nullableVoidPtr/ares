export type RegisterIndex = number;

export type HermesString = string & {
	stringTableIndex: number;
}

export interface VMInstruction {
	functionLocalOffset: number;
	isLongVariant: boolean;
}

export interface AssigningInstruction extends VMInstruction {
	destination: RegisterIndex;
}

export interface UnaryOperationInst extends AssigningInstruction {
	operand: RegisterIndex;
}

export interface BinaryOperationInst extends AssigningInstruction {
	left: RegisterIndex;
	right: RegisterIndex;
}

export interface BranchInstruction extends VMInstruction {
	target: number;
}

export interface BranchingBinaryInstuction extends BranchInstruction {
	left: RegisterIndex;
	right: RegisterIndex;
}

export interface WASMSpecificInstruction extends VMInstruction {
	isWASM: true;
}

export class UnreachableOp implements VMInstruction {}

export class NewObjectWithBufferInst implements AssigningInstruction {
	sizeHint: number;
	noOfStaticElements: number;
	objectKeyBufferIndex: number;
	objectValueBufferIndex: number;
}

export class NewObjectInst implements AssigningInstruction {}

export class NewObjectWithParentInst implements AssigningInstruction {
	parent: RegisterIndex;
}

export class NewArrayWithBufferInst implements AssigningInstruction {
	sizeHint: number;
	noOfStaticElements: number;
	arrayBufferIndex: number;
}

export class NewArrayInst implements AssigningInstruction {
	size: number;
}

export class MovInst implements AssigningInstruction {
	source: RegisterIndex;
}

export class NegateInst implements UnaryOperationInst {}
export class NotInst implements UnaryOperationInst {}
export class BitNotInst implements UnaryOperationInst {}
export class TypeOfInst implements UnaryOperationInst {}
export class EqInst implements BinaryOperationInst {}
export class StrictEqInst implements BinaryOperationInst {}
export class NeqInst implements BinaryOperationInst {}
export class StrictNeqInst implements BinaryOperationInst {}
export class LessInst implements BinaryOperationInst {}
export class LessEqInst implements BinaryOperationInst {}
export class GreaterInst implements BinaryOperationInst {}
export class GreaterEqInst implements BinaryOperationInst {}
export class AddInst implements BinaryOperationInst {}
export class AddNInst implements BinaryOperationInst {}
export class MulInst implements BinaryOperationInst {}
export class MulNInst implements BinaryOperationInst {}
export class DivInst implements BinaryOperationInst {}
export class DivNInst implements BinaryOperationInst {}
export class ModInst implements BinaryOperationInst {}
export class SubInst implements BinaryOperationInst {}
export class SubNInst implements BinaryOperationInst {}
export class LShiftInst implements BinaryOperationInst {}
export class RShiftInst implements BinaryOperationInst {}
export class URShiftInst implements BinaryOperationInst {}
export class BitAndInst implements BinaryOperationInst {}
export class BitXorInst implements BinaryOperationInst {}
export class BitOrInst implements BinaryOperationInst {}
export class InstanceOfInst implements BinaryOperationInst {}
export class IsInInst implements BinaryOperationInst {}

export class GetEnvironmentInst implements AssigningInstruction {
	levelIndex: number;
}

export class StoreToEnvironmentInst implements VMInstruction {
	environment: RegisterIndex;
	slotIndex: number;
	value: RegisterIndex;
}

export class StoreNPToEnvironmentInst implements VMInstruction {
	environment: RegisterIndex;
	slotIndex: number;
	value: RegisterIndex;
}

export class LoadFromEnvironmentInst implements AssigningInstruction {
	environment: RegisterIndex;
	slotIndex: number;
}

export class GetGlobalObjectInst implements AssigningInstruction {}

export class GetNewTargetInst implements AssigningInstruction {}

export class CreateEnvironmentInst implements AssigningInstruction {}

export class DeclareGlobalVarInst implements VMInstruction {
	identifier: HermesString;
}

export class GetByIdInst implements AssigningInstruction {
	object: RegisterIndex;
	cacheIndex: number;
	property: HermesString;
}

export class TryGetByIdInst implements AssigningInstruction {
	object: RegisterIndex;
	cacheIndex: number;
	property: HermesString;
}

export class PutByIdInst implements VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	cacheIndex: number;
	property: HermesString;
}

export class TryPutByIdInst implements VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	cacheIndex: number;
	property: HermesString;
}

export class PutNewOwnByIdInst implements VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	property: HermesString;
}

export class PutNewOwnNEByIdInst implements VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	property: HermesString;
}

export class PutOwnByIndexInst implements VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	property: RegisterIndex;
}

export class PutOwnByValInst implements VMInstruction {
	object: RegisterIndex;
	value: RegisterIndex;
	property: RegisterIndex;
	enumerable: boolean;
}

export class DelByIdInst implements AssigningInstruction {
	object: RegisterIndex;
	property: HermesString;
}

export class GetByValInst implements AssigningInstruction {
	object: RegisterIndex;
	property: RegisterIndex;
}

export class PutByValInst implements VMInstruction {
	object: RegisterIndex;
	property: RegisterIndex;
	value: RegisterIndex;
}

export class DelByValInst implements AssigningInstruction {
	object: RegisterIndex;
	property: RegisterIndex;
}

export class PutOwnGetterSetterByValInst implements VMInstruction {
	object: RegisterIndex;
	property: RegisterIndex;
	getter: RegisterIndex;
	setter: RegisterIndex;
	enumerable: booleano;
}

export class GetPNameListInst implements AssigningInstruction {
	object: RegisterIndex;
	index: RegisterIndex;
	propertyListSize: RegisterIndex;
}

export class GetNextPNameInst implements AssigningInstruction {
	object: RegisterIndex;
	index: RegisterIndex;
	propertyListSize: RegisterIndex;
}

export class CallInst implements AssigningInstruction {
	closure: RegisterIndex;
	argumentCount: number;
}

export class ConstructInst implements AssigningInstruction {
	closure: RegisterIndex;
	argumentCount: number;
}

export class CallNInst implements AssigningInstruction {
	closure: RegisterIndex;
	arguments: RegisterIndex[];
}

export class CallDirectInst implements AssigningInstruction {
	argumentCount: number;
	functionIndex: RegisterIndex;
}

export class CallBuiltinInst implements AssigningInstruction {
	builtinNo: RegisterIndex;
	argumentCount: number;
}

export class CallBuiltinClosureInst implements AssigningInstruction {
	builtinNo: RegisterIndex;
}

export class RetInst implements VMInstruction {
	argument: RegisterIndex;
}

export class CatchInst implements VMInstruction {
	exception: RegisterIndex;
}

export class DirectEvalInst implements AssigningInstruction {
	code: RegisterIndex;
}

export class ThrowInst implements VMInstruction {
	exception: RegisterIndex;
}

export class ThrowIfEmptyInst implements AssigningInstruction {
	source: RegisterIndex;
}

export class DebuggerInst implements VMInstruction {}

export class AsyncBreakCheckInst implements VMInstruction {}

export class ProfilePointInst implements VMInstruction {
	profilePoint: number;
}

export class CreateClosureInst implements AssigningInstruction {
	environment: RegisterIndex;
	functionIndex: number;
}

export class CreateGeneratorClosureInst implements AssigningInstruction {
	environment: RegisterIndex;
	functionIndex: number;
}

export class CreateAsyncClosureInst implements AssigningInstruction {
	environment: RegisterIndex;
	functionIndex: number;
}

export class CreateThisInst implements AssigningInstruction {
	prototype: RegisterIndex;
	constructorRef: RegisterIndex;
}

export class SelectObjectInst implements AssigningInstruction {
	thisObject: RegisterIndex;
	constructorReturnValue: RegisterIndex;
}

export class LoadParamInst implements AssigningInstruction {
	parameterIndex: RegisterIndex;
}

export class HermesEmpty {}

export class LoadConstInst implements AssigningInstruction {
	value: number | HermesString | HermesEmpty | void | null | boolean;
}

export class CoerceThisNSInst implements AssigningInstruction {
	argument: RegisterIndex;
}

export class LoadThisNSInst implements AssigningInstruction {}

export class ToNumberInst implements AssigningInstruction {
	argument: RegisterIndex;
}

export class ToInt32Inst implements AssigningInstruction {
	argument: RegisterIndex;
}

export class AddEmptyStringInst implements AssigningInstruction {
	argument: RegisterIndex;
}

export class GetArgumentsByPropValInst implements AssigningInstruction {
	argumentsIndex: RegisterIndex;
	lazyLoad: RegisterIndex;
}

export class GetArgumentsLengthInst implements AssigningInstruction {
	lazyLoad: RegisterIndex;
}

export class ReifyArgumentsInst implements VMInstruction {
	lazyLoad: RegisterIndex;
}

export class CreateRegExpInst implements AssigningInstruction {
	pattern: HermesString;
	flags: HermesString;
	regExpBytecodeIndex: number;
}

export class SwitchImmInst implements VMInstruction {
	discriminant: RegisterIndex;
	jumpTableOffset: number;
	defaultJumpOffset: number;
	minValue: number;
	maxValue: number;
}

export class StartGeneratorInst implements VMInstruction {}

export class ResumeGeneratorInst implements VMInstruction {
	value: RegisterIndex;
	isReturn: RegisterIndex;
}

export class CompleteGeneratorInst implements VMInstruction {}

export class CreateGeneratorInst implements AssigningInstruction {
	environment: RegisterIndex;
	functionIndex: number;
}

export class IteratorBeginInst implements AssigningInstruction {
	source: RegisterIndex;
}

export class IteratorNextInst implements AssigningInstruction {
	iterator: RegisterIndex;
	sourceOrNext: RegisterIndex;
}

export class IteratorCloseInst implements VMInstruction {
	iterator: RegisterIndex;
	ignoreException: RegisterIndex;
}

export class JmpInst implements BranchInstruction {}

export class JmpTrueInst implements BranchInstruction {
	predicate: RegisterIndex;
}

export class JmpFalseInst implements BranchInstruction {
	predicate: RegisterIndex;
}

export class JmpUndefinedInst implements BranchInstruction {
	predicate: RegisterIndex;
}

export class SaveGenerator implements BranchInstruction {}

export class JLess implements BranchBinaryInstruction {}
export class JNotLess implements BranchBinaryInstruction {}
export class JLessN implements BranchBinaryInstruction {}
export class JNotLessN implements BranchBinaryInstruction {}
export class JLessEqual implements BranchBinaryInstruction {}
export class JNotLessEqual implements BranchBinaryInstruction {}
export class JLessEqualN implements BranchBinaryInstruction {}
export class JNotLessEqualN implements BranchBinaryInstruction {}
export class JGreater implements BranchBinaryInstruction {}
export class JNotGreater implements BranchBinaryInstruction {}
export class JGreaterN implements BranchBinaryInstruction {}
export class JNotGreaterN implements BranchBinaryInstruction {}
export class JGreaterEqual implements BranchBinaryInstruction {}
export class JNotGreaterEqual implements BranchBinaryInstruction {}
export class JGreaterEqualN implements BranchBinaryInstruction {}
export class JNotGreaterEqualN implements BranchBinaryInstruction {}
export class JEqual implements BranchBinaryInstruction {}
export class JNotEqual implements BranchBinaryInstruction {}
export class JEqualN implements BranchBinaryInstruction {}
export class JNotEqualN implements BranchBinaryInstruction {}
export class JStrictEqual implements BranchBinaryInstruction {}
export class JStrictNotEqual implements BranchBinaryInstruction {}

export class Add32Inst implements WASMSpecificInstruction, BinaryOperationInst {}

export class Sub32Inst implements WASMSpecificInstruction, BinaryOperationInst {}

export class Mul32Inst implements WASMSpecificInstruction, BinaryOperationInst {}

export class Divi32Inst implements WASMSpecificInstruction, BinaryOperationInst {}

export class Divu32Inst implements WASMSpecificInstruction, BinaryOperationInst {}

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
