import type { FunctionId } from '../../hbc/disassembly/instruction.ts';
import type { IRFunction } from './mod.ts';

/**
 * How composition reaches the lifted functions it consumes.
 *
 * Declared apart from `lib/ir/lift.ts` so implementations can live outside it:
 * `lib/coldstore/store.ts` backs one with LMDB, and lift.ts already imports the
 * cold store's plan builder, so keeping the interface there would make the two
 * modules mutually dependent.
 */
export interface IRFunctionStore {
	has(functionId: FunctionId): boolean;
	get(functionId: FunctionId): IRFunction | undefined;
	delete(functionId: FunctionId): boolean;
	set(functionId: FunctionId, func: IRFunction): void;
	/**
	 * Rebuild a function this store has already handed out and consumed.
	 *
	 * Consumption is irreversible, so no store can answer `get` for a function
	 * that has been inlined somewhere; lifting is deterministic, so a rebuild
	 * reproduces the copy that was consumed. Only consumed ids may be rebuilt:
	 * generator and async lowering consume the functions they absorb, and those
	 * must not be materialized a second time.
	 */
	relift(functionId: FunctionId): IRFunction | undefined;
}
