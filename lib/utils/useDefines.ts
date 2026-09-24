import { Instruction, Register } from '../hbc/disassembly/instruction.ts';

export interface InstructionUseDefines {
	defs: Record<string, Register>;
	uses: Record<string, Register | Register[]>;
}

/** Classify the register operands read and written by one instruction. */
export function analyseUseDefines<T extends Instruction>(
	instr: T,
): InstructionUseDefines {
	const defs: Record<string, Register> = {};
	const uses: Record<string, Register | Register[]> = {};

	if ('destination' in instr) defs.destination = instr.destination;
	if ('argument' in instr) uses.argument = instr.argument;
	if ('left' in instr) uses.left = instr.left;
	if ('right' in instr) uses.right = instr.right;
	if ('predicate' in instr) uses.predicate = instr.predicate;

	switch (instr.instruction) {
		case 'NewObjectWithParent':
		case 'NewObjectWithBufferAndParent':
			uses.parent = instr.parent;
			break;

		case 'Mov':
			uses.source = instr.source;
			break;

		case 'ThrowIfEmpty':
		case 'IteratorBegin':
			defs.source = instr.source;
			uses.source = instr.source;
			break;

		case 'TypeOfIs':
		case 'JmpTypeOfIs':
			uses.value = instr.value;
			break;

		case 'CreateEnvironment':
			uses.parent = instr.parent;
			break;

		case 'GetEnvironment':
			uses.parentEnv = instr.parentEnv;
			break;

		case 'StoreToEnvironment':
		case 'StoreNPToEnvironment':
			uses.value = instr.value;
		/* falls through */
		case 'LoadFromEnvironment':
		case 'CreateClosure':
		case 'CreateGeneratorClosure':
		case 'CreateAsyncClosure':
		case 'CreateGenerator':
			uses.environment = instr.environment;
			break;

		case 'GetClosureEnvironment':
			uses.closure = instr.closure;
			break;

		case 'CreateBaseClass':
			defs.classOut = instr.classOut;
			if (instr.homeObject.index !== instr.classOut.index) {
				defs.homeObject = instr.homeObject;
			}
			uses.environment = instr.environment;
			break;

		case 'CreateDerivedClass':
			defs.classOut = instr.classOut;
			if (instr.homeObject.index !== instr.classOut.index) {
				defs.homeObject = instr.homeObject;
			}
			uses.environment = instr.environment;
			uses.superClass = instr.superClass;
			break;

		case 'PutByVal':
		case 'DefineOwnByVal':
			uses.property = instr.property;
		/* falls through */
		case 'PutOwnBySlotIdx':
		case 'PutById':
		case 'TryPutById':
		case 'DefineOwnById':
		case 'PutNewOwnById':
		case 'PutNewOwnNEById':
		case 'DefineOwnInDenseArray':
		case 'DefineOwnByIndex':
			uses.value = instr.value;
		/* falls through */
		case 'GetBySlotIdx':
		case 'TryGetById':
		case 'GetById':
		case 'DelById':
			uses.object = instr.object;
			break;

		case 'GetByIdWithReceiver':
			uses.object = instr.object;
			uses.receiver = instr.receiver;
			break;

		case 'DefineOwnGetterSetterByVal':
			uses.getter = instr.getter;
			uses.setter = instr.setter;
		/* falls through */
		case 'DelByVal':
		case 'GetByVal':
			uses.object = instr.object;
			uses.property = instr.property;
			break;

		case 'GetByIndex':
			uses.object = instr.object;
			break;

		case 'GetPNameList':
			defs.index = instr.index;
			defs.propertyListSize = instr.propertyListSize;
			uses.object = instr.object;
			break;

		case 'GetNextPName':
			defs.index = instr.index;
			uses.index = instr.index;
			uses.object = instr.object;
			uses.propertyListSize = instr.propertyListSize;
			break;

		case 'Call':
		case 'CallBuiltin':
		case 'Construct': {
			if ('closure' in instr) uses.closure = instr.closure;
			if ('newTarget' in instr && instr.newTarget) {
				uses.newTarget = instr.newTarget;
			}
			uses.arguments = instr.arguments.slice();
			break;
		}

		case 'Ret':
			uses.argument = instr.argument;
			break;

		case 'DirectEval':
			uses.code = instr.code;
			break;

		case 'Throw':
			uses.exception = instr.exception;
			break;

		case 'ThrowIfThisInitialized':
			uses.thisObject = instr.thisObject;
			break;

		case 'CreateThis':
			uses.prototype = instr.prototype;
			uses.constructorRef = instr.constructorRef;
			break;

		case 'CacheNewObject':
			uses.thisObject = instr.thisObject;
			uses.newTarget = instr.newTarget;
			break;

		case 'CreateThisForNew':
			uses.closure = instr.closure;
			break;

		case 'CreateThisForSuper':
			uses.closure = instr.closure;
			uses.newTarget = instr.newTarget;
			break;

		case 'SelectObject':
			uses.thisObject = instr.thisObject;
			uses.constructorReturnValue = instr.constructorReturnValue;
			break;

		case 'GetArgumentsPropByVal':
			uses.argumentsIndex = instr.argumentsIndex;
			break;

		case 'GetArgumentsLength':
			break;

		case 'ReifyArguments':
			defs.lazyLoad = instr.lazyLoad;
			break;

		case 'UIntSwitchImm':
		case 'StringSwitchImm':
			uses.discriminant = instr.discriminant;
			break;

		case 'ResumeGenerator':
			uses.isReturn = instr.isReturn;
			break;

		case 'IteratorNext':
			defs.iterator = instr.iterator;
			uses.iterator = instr.iterator;
			uses.sourceOrNext = instr.sourceOrNext;
			break;

		case 'IteratorClose':
			uses.iterator = instr.iterator;
			break;

		case 'Store8':
		case 'Store16':
		case 'Store32':
			uses.value = instr.value;
		/* falls through */
		case 'Loadi8':
		case 'Loadu8':
		case 'Loadi16':
		case 'Loadu16':
		case 'Loadi32':
		case 'Loadu32':
			uses.heap = instr.heap;
			uses.offset = instr.offset;
			break;
	}
	return { defs, uses };
}
