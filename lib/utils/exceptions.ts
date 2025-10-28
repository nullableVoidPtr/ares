import { BlockAddr, Function, FunctionExceptionHandler } from '../disassembly/function.ts';

export function exceptionHandlersByAddress(address: BlockAddr, exceptionHandlers: FunctionExceptionHandler[]): FunctionExceptionHandler[] {
	return exceptionHandlers.filter(
		({tryStart, tryEnd}) => tryStart <= address && tryEnd > address
	);
}

export function areExceptionHandlersParent(parent: number | FunctionExceptionHandler[], child: number | FunctionExceptionHandler[], exceptionHandlers?: Function['exceptionHandlers']) {
	if (!Array.isArray(parent)) {
		if (!exceptionHandlers) throw new Error('Expected exception handlers with address specified');
		parent = exceptionHandlersByAddress(parent, exceptionHandlers);
	}
	if (!Array.isArray(child)) {
		if (!exceptionHandlers) throw new Error('Expected exception handlers with address specified');
		child = exceptionHandlersByAddress(child, exceptionHandlers);
	}

	return child.every(e => parent.findIndex(
		({tryStart, tryEnd, catchOffset}) => tryStart === e.tryStart && tryEnd === e.tryEnd && catchOffset === e.catchOffset
	) !== -1);
}

export function areExceptionHandlersEqual(left: number | FunctionExceptionHandler[], right: number | FunctionExceptionHandler[], exceptionHandlers?: Function['exceptionHandlers']) {
	if (!Array.isArray(left)) {
		if (!exceptionHandlers) throw new Error('Expected exception handlers with address specified');
		left = exceptionHandlersByAddress(left, exceptionHandlers);
	}
	if (!Array.isArray(right)) {
		if (!exceptionHandlers) throw new Error('Expected exception handlers with address specified');
		right = exceptionHandlersByAddress(right, exceptionHandlers);
	}

	if (!areExceptionHandlersParent(left, right, exceptionHandlers)) return false;
	if (left.length !== right.length) return false;

	return true;
}
