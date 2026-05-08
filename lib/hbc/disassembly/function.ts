import { Register, Instruction } from "./instruction.js";

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

		operation: (
			'<' | '<=' |
			'>' | '>=' |
			'==' |
			'==='
		);

		right: Register | undefined;
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

export interface Function {
	id: number;
	offset: number;
	name?: string;
	paramCount: number;
	frameSize: number;
	envSize: number;
	highestReadCacheIndex: number;
	highestWriteCacheIndex: number;
	strict: boolean;
	prohibitInvoke: ProhibitInvoke;

	exceptionHandlers: FunctionExceptionHandler[];

	// debugInfo: number;

	basicBlocks: Map<BlockAddr, BasicBlock>;
	trampolines: Map<BlockAddr, BlockAddr>;
}
