import { Instruction, Register } from './instruction.ts';

export interface FunctionExceptionHandler {
	tryStart: number;
	tryEnd: number;
	catchOffset: number;
}

export type BlockAddr = number;
export interface BasicBlock {
	address: BlockAddr;
	instructions: Instruction[];

	predicate: {
		not: boolean;
		predicate: Register;
	} | {
		not: boolean;

		left: Register;

		operation: '<' | '<=' | '>' | '>=' | '==' | '===';

		right: Register | undefined;
	} | {
		not: boolean;
		value: Register;
		operation: 'typeof-is';
		typeIndex: number;
	} | {
		discriminant: Register;
		minValue: number;
		maxValue: number;
	} | null;
	// length:
	// == 1 if unconditional,
	// == 2 if conditional branch, [false, true]
	// otherwise if switch case, [default, case 1...]
	consequentAddresses: BlockAddr[];
}

enum ProhibitInvoke {
	ProhibitCall = 0,
	ProhibitConstruct = 1,
	ProhibitNone = 2,
}

export enum FunctionKind {
	NormalFunction = 0,
	GeneratorFunction = 1,
	AsyncFunction = 2,
}

export interface Function {
	id: number;
	offset: number;
	/** Encoded bytecode bytes; used as a scheduling/memory weight. */
	bytecodeLength?: number;
	name?: string;
	paramCount: number;
	frameSize: number;
	envSize: number;
	loopDepth: number;
	numberRegCount: number;
	nonPtrRegCount: number;
	highestReadCacheIndex: number;
	highestWriteCacheIndex: number;
	readCacheSize: number;
	writeCacheSize: number;
	privateNameCacheSize: number;
	strict: boolean;
	prohibitInvoke: ProhibitInvoke;
	functionKind: FunctionKind;

	exceptionHandlers: FunctionExceptionHandler[];

	// debugInfo: number;

	basicBlocks: Map<BlockAddr, BasicBlock>;
	trampolines: Map<BlockAddr, BlockAddr>;
}
