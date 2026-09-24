import {
	BlockAddr,
	FunctionExceptionHandler,
} from '../../../hbc/disassembly/function.ts';
import { RegisterIndex } from '../../../hbc/disassembly/instruction.ts';
import { RegisterVersion, SSAInstruction, SSARegister } from '../../../ssa.ts';
import { AddressSet, setEquals } from '../../../utils/set.ts';
import type { IRFunction } from '../mod.ts';
import { exceptionHandlersByAddress } from '../../../hbc/utils/exceptions.ts';
import { AddressMap, MapWithDefault } from '../../../utils/map.ts';
import { AddressGraph } from '../../../utils/graph.ts';
import * as t from '@babel/types';
import { statementsMaySuspend } from '../../ast/effects.ts';
import {
	kmpSearch,
	statementFingerprint,
	type TraceBlock,
	traceFingerprints,
	traceMatchesPrefix,
	tracePrefixLength,
} from '../cfg/descriptors/subgraphMatch.ts';

class SSARegisterMap<V> {
	#map = new MapWithDefault<RegisterIndex, Map<RegisterVersion, V>>();

	set(key: SSARegister, value: V) {
		this.#map.getWithDefault(
			key.index,
			() => new Map(),
		).set(
			key.version,
			value,
		);
	}

	get(key: SSARegister): V | undefined {
		return this.#map.get(key.index)?.get(key.version);
	}
}

function comparableInstructionKeys(instr: SSAInstruction) {
	return Object.keys(instr).filter((key) =>
		![
			'instruction',
			'defs',
			'uses',
			'functionLocalOffset',
			'type',
			'length',
		].includes(key)
	).toSorted();
}

function comparableValue(value: unknown): unknown {
	if (Array.isArray(value)) return value.map(comparableValue);
	if (value && typeof value === 'object') {
		const result: Record<string, unknown> = {};
		for (const key of Object.keys(value).toSorted()) {
			result[key] = comparableValue(
				(value as Record<string, unknown>)[key],
			);
		}
		return result;
	}
	return value;
}

function compareFinallyCopies(
	func: IRFunction,
	canonicalStart: BlockAddr,
	copyStart: BlockAddr,
	ignoreUnconditionalJumps = false,
) {
	if (canonicalStart === copyStart) return true;
	if (
		!func.ssa.basicBlocks.has(canonicalStart) ||
		!func.ssa.basicBlocks.has(copyStart)
	) return false;

	const canonicalToCopy = new SSARegisterMap<SSARegister>();
	const copyToCanonical = new SSARegisterMap<SSARegister>();
	const visited = new Set<string>();

	const registersEqual = (
		canonical: SSARegister,
		copy: SSARegister,
	): boolean => {
		const mapped = canonicalToCopy.get(canonical);
		const reverse = copyToCanonical.get(copy);
		if (
			mapped &&
			(mapped.index !== copy.index || mapped.version !== copy.version)
		) return false;
		if (
			reverse &&
			(reverse.index !== canonical.index ||
				reverse.version !== canonical.version)
		) return false;

		if (!mapped) {
			if (reverse) throw new Error();
			canonicalToCopy.set(canonical, copy);
			copyToCanonical.set(copy, canonical);
		}

		return true;
	};

	const regsEqual = (
		canonical: SSARegister | SSARegister[],
		copy: SSARegister | SSARegister[],
	) => {
		if (Array.isArray(canonical) || Array.isArray(copy)) {
			if (!Array.isArray(canonical) || !Array.isArray(copy)) return false;
			if (canonical.length !== copy.length) return false;
			return canonical.every((reg, i) => registersEqual(reg, copy[i]));
		}

		return registersEqual(canonical, copy);
	};

	const instrsEqual = (
		canonical: SSAInstruction,
		copy: SSAInstruction,
	): boolean => {
		if (canonical.instruction !== copy.instruction) return false;

		if (canonical.instruction === 'Phi' || copy.instruction === 'Phi') {
			if (canonical.instruction !== 'Phi' || copy.instruction !== 'Phi') {
				return false;
			}
			return registersEqual(canonical.destination, copy.destination);
		}

		if (
			!setEquals(
				new Set(Object.keys(canonical.defs)),
				new Set(Object.keys(copy.defs)),
			)
		) return false;
		if (
			!setEquals(
				new Set(Object.keys(canonical.uses)),
				new Set(Object.keys(copy.uses)),
			)
		) return false;
		if (
			!setEquals(
				new Set(comparableInstructionKeys(canonical)),
				new Set(comparableInstructionKeys(copy)),
			)
		) return false;

		for (const key of comparableInstructionKeys(canonical)) {
			if (
				JSON.stringify(comparableValue((canonical as any)[key])) !==
					JSON.stringify(comparableValue((copy as any)[key]))
			) {
				return false;
			}
		}

		for (const key of Object.keys(canonical.uses)) {
			if (
				!regsEqual(
					(canonical.uses as Record<
						string,
						SSARegister | SSARegister[]
					>)[key],
					(copy.uses as Record<string, SSARegister | SSARegister[]>)[
						key
					],
				)
			) return false;
		}
		for (const key of Object.keys(canonical.defs)) {
			if (
				!registersEqual(
					(canonical.defs as Record<string, SSARegister>)[key],
					(copy.defs as Record<string, SSARegister>)[key],
				)
			) return false;
		}

		return true;
	};

	const blocksEqual = (
		canonicalAddr: BlockAddr,
		copyAddr: BlockAddr,
	): boolean => {
		const visitKey = `${canonicalAddr}:${copyAddr}`;
		if (visited.has(visitKey)) return true;
		visited.add(visitKey);

		const canonical = func.ssa.basicBlocks.get(canonicalAddr);
		const copy = func.ssa.basicBlocks.get(copyAddr);
		if (!canonical || !copy) return false;

		const canonicalInstrs = canonical.ssaInstructions.filter((instr) =>
			instr.instruction !== 'Phi' &&
			instr.instruction !== 'Catch' &&
			(
				!ignoreUnconditionalJumps ||
				instr.instruction !== 'Jmp'
			)
		);
		const copyInstrs = copy.ssaInstructions.filter((instr) =>
			instr.instruction !== 'Phi' &&
			instr.instruction !== 'Catch' &&
			(
				!ignoreUnconditionalJumps ||
				instr.instruction !== 'Jmp'
			)
		);
		if (canonicalInstrs.length !== copyInstrs.length) return false;

		for (let i = 0; i < canonicalInstrs.length; i++) {
			if (!instrsEqual(canonicalInstrs[i], copyInstrs[i])) return false;
		}

		if (
			canonical.consequentAddresses.length !==
				copy.consequentAddresses.length
		) return false;
		for (let i = 0; i < canonical.consequentAddresses.length; i++) {
			if (
				!blocksEqual(
					canonical.consequentAddresses[i],
					copy.consequentAddresses[i],
				)
			) return false;
		}

		return true;
	};

	return blocksEqual(canonicalStart, copyStart);
}

function equivalentPureCatchCompletion(
	func: IRFunction,
	canonicalHandler: BlockAddr,
	copyHandler: BlockAddr,
): boolean {
	const canonicalStart = skipCatchOnlyPrelude(func, canonicalHandler);
	const copyStart = skipCatchOnlyPrelude(func, copyHandler);
	if (!pureCatchCompletionPathsConverge(func, canonicalStart, copyStart)) {
		return false;
	}
	return compareFinallyCopies(func, canonicalStart, copyStart, true);
}

function skipCatchOnlyPrelude(
	func: IRFunction,
	handler: BlockAddr,
): BlockAddr {
	let current = handler;
	const visited = new AddressSet<BlockAddr>();
	while (!visited.has(current)) {
		visited.add(current);
		const block = func.ssa.basicBlocks.get(current);
		if (!block || block.consequentAddresses.length !== 1) break;
		if (
			block.ssaInstructions.some((instruction) =>
				instruction.instruction !== 'Catch' &&
				instruction.instruction !== 'Phi'
			)
		) break;
		current = block.consequentAddresses[0];
	}
	return current;
}

/**
 * A compiler catch copy may be folded into its enclosing catch only when the
 * two handler prefixes perform value-only completion work before reaching the
 * same continuation. Calls, stores, throws, and conditional branches remain
 * distinct: a genuine nested catch can observe those effects or catch an error
 * they throw.
 */
function pureCatchCompletionPathsConverge(
	func: IRFunction,
	canonicalStart: BlockAddr,
	copyStart: BlockAddr,
): boolean {
	let canonical = canonicalStart;
	let copy = copyStart;
	const visited = new Set<string>();
	while (canonical !== copy) {
		const key = `${canonical}:${copy}`;
		if (visited.has(key)) return false;
		visited.add(key);
		const canonicalBlock = func.ssa.basicBlocks.get(canonical);
		const copyBlock = func.ssa.basicBlocks.get(copy);
		if (!canonicalBlock || !copyBlock) return false;
		if (
			!canonicalBlock.ssaInstructions.every(
				isPureCatchCompletionInstruction,
			) ||
			!copyBlock.ssaInstructions.every(
				isPureCatchCompletionInstruction,
			) ||
			canonicalBlock.consequentAddresses.length !== 1 ||
			copyBlock.consequentAddresses.length !== 1
		) return false;
		canonical = canonicalBlock.consequentAddresses[0];
		copy = copyBlock.consequentAddresses[0];
	}
	return true;
}

function isPureCatchCompletionInstruction(
	instruction: SSAInstruction,
): boolean {
	return instruction.instruction === 'Catch' ||
		instruction.instruction === 'Phi' ||
		instruction.instruction === 'LoadConst' ||
		instruction.instruction.startsWith('Mov') ||
		instruction.instruction === 'Jmp';
}

function instructionFingerprint(instr: SSAInstruction): string {
	const comparable: Record<string, unknown> = {
		instruction: instr.instruction,
	};
	for (const key of comparableInstructionKeys(instr)) {
		comparable[key] = comparableValue(
			(instr as unknown as Record<string, unknown>)[key],
		);
	}
	return JSON.stringify(comparable);
}

/**
 * Observable instruction skeleton for a finalizer body.
 *
 * Canonical exceptional copies often reload globals/arguments which the normal
 * copy already has live. Register operands are compared by SSA elsewhere and
 * are omitted here; semantic immediates such as property and string-table
 * indices remain. IteratorClose is excluded: its path-specific close protocol
 * is classified separately and its exits remain owned by iterator structuring,
 * not generic finalizer-copy emission.
 */
function finalizerEffectFingerprint(
	instruction: SSAInstruction,
): string | null {
	const name = instruction.instruction;
	if (
		name === 'Phi' ||
		name === 'Catch' ||
		name === 'Throw' ||
		name === 'Ret' ||
		name === 'GetGlobalObject' ||
		name === 'CompleteGenerator' ||
		name === 'SaveGenerator' ||
		name === 'ResumeGenerator' ||
		name === 'IteratorClose' ||
		name.startsWith('Mov') ||
		name.startsWith('Load') ||
		name.startsWith('Jmp')
	) return null;

	const operands = new Set<string>([
		...Object.keys(instruction.defs),
		...Object.keys(instruction.uses),
	]);
	const comparable: Record<string, unknown> = { instruction: name };
	for (const key of comparableInstructionKeys(instruction)) {
		if (operands.has(key)) continue;
		if (/cache/i.test(key)) continue;
		comparable[key] = comparableValue(
			(instruction as unknown as Record<string, unknown>)[key],
		);
	}
	return JSON.stringify(comparable);
}

/**
 * Constants are setup too, but their values distinguish otherwise identical
 * effects (`dispatch("success")` versus `dispatch("failure")`). Attach each
 * constant to the next observable instruction and discard trailing constants
 * used only by completion protocol.
 */
function finalizerEffectFingerprints(
	instructions: readonly SSAInstruction[],
): string[] {
	const effects: string[] = [];
	const pendingConstants: string[] = [];
	for (const instruction of instructions) {
		if (instruction.instruction === 'LoadConst') {
			const value =
				(instruction as unknown as Record<string, unknown>).value;
			if (value !== undefined) {
				pendingConstants.push(JSON.stringify({
					instruction: 'LoadConst',
					value: comparableValue(value),
				}));
			}
			continue;
		}
		const effect = finalizerEffectFingerprint(instruction);
		if (effect == null) continue;
		effects.push(...pendingConstants, effect);
		pendingConstants.length = 0;
	}
	return effects;
}

function compareFinallyEffectBlocks(
	func: IRFunction,
	canonicalStart: BlockAddr,
	copyStart: BlockAddr,
): boolean {
	const canonical = func.ssa.basicBlocks.get(canonicalStart);
	const copy = func.ssa.basicBlocks.get(copyStart);
	if (!canonical || !copy) return false;
	const canonicalEffects = finalizerEffectFingerprints(
		canonical.ssaInstructions,
	);
	if (canonicalEffects.length === 0) return false;
	const copyEffects = finalizerEffectFingerprints(copy.ssaInstructions);
	return canonicalEffects.length === copyEffects.length &&
		canonicalEffects.every((fingerprint, index) =>
			fingerprint === copyEffects[index]
		);
}

function compareFinallyCopyPrefix(
	func: IRFunction,
	canonicalStart: BlockAddr,
	copyStart: BlockAddr,
): boolean {
	const canonical = func.ssa.basicBlocks.get(canonicalStart);
	const copy = func.ssa.basicBlocks.get(copyStart);
	if (!canonical || !copy) return false;

	const canonicalInstructions = canonical.ssaInstructions.filter((instr) =>
		instr.instruction !== 'Phi'
	);
	while (
		canonicalInstructions.length > 0 &&
		canonicalInstructions[0].instruction === 'Catch'
	) {
		canonicalInstructions.shift();
	}
	const last = canonicalInstructions.at(-1);
	if (last?.instruction === 'Throw') canonicalInstructions.pop();
	if (canonicalInstructions.length === 0) return false;

	const copyInstructions = copy.ssaInstructions.filter((instr) =>
		instr.instruction !== 'Phi'
	);
	if (copyInstructions.length < canonicalInstructions.length) return false;

	const canonicalFingerprints = canonicalInstructions.map(
		instructionFingerprint,
	);
	const copyFingerprints = copyInstructions.slice(
		0,
		canonicalFingerprints.length,
	).map(instructionFingerprint);
	return canonicalFingerprints.every((fingerprint, index) =>
		copyFingerprints[index] === fingerprint
	);
}

function compareFinallyCopySuffixPrefix(
	func: IRFunction,
	canonicalStart: BlockAddr,
	copyStart: BlockAddr,
): boolean {
	const canonical = func.ssa.basicBlocks.get(canonicalStart);
	const copy = func.ssa.basicBlocks.get(copyStart);
	if (!canonical || !copy) return false;

	const canonicalInstructions = canonical.ssaInstructions.filter((instr) =>
		instr.instruction !== 'Phi'
	);
	while (
		canonicalInstructions.length > 0 &&
		canonicalInstructions[0].instruction === 'Catch'
	) {
		canonicalInstructions.shift();
	}
	const last = canonicalInstructions.at(-1);
	if (last?.instruction === 'Throw') canonicalInstructions.pop();

	const copyInstructions = copy.ssaInstructions.filter((instr) =>
		instr.instruction !== 'Phi' && instr.instruction !== 'Catch'
	);
	if (canonicalInstructions.length < 2 || copyInstructions.length < 2) {
		return false;
	}

	const canonicalFingerprints = canonicalInstructions.map(
		instructionFingerprint,
	);
	const copyFingerprints = copyInstructions.map(instructionFingerprint);
	const maxOffset = canonicalFingerprints.length - 2;
	for (let offset = 1; offset <= maxOffset; offset++) {
		const suffix = canonicalFingerprints.slice(offset);
		if (suffix.length < 2 || copyFingerprints.length < suffix.length) {
			continue;
		}
		if (
			suffix.every((fingerprint, index) =>
				copyFingerprints[index] === fingerprint
			)
		) return true;
	}
	return false;
}

function minAddress(blocks: Iterable<BlockAddr>): BlockAddr | null {
	let result: BlockAddr | null = null;
	for (const block of blocks) {
		if (result == null || block < result) result = block;
	}
	return result;
}

/** A register version, as a comparable key. */
type RegisterKey = string;

function registerKey(register: SSARegister): RegisterKey {
	return `r${register.index}_${register.version}`;
}

/**
 * Every register an instruction writes. Phi carries its destination directly;
 * every other instruction exposes the SSA `defs` record the lifter built.
 */
function instructionDefines(instruction: SSAInstruction): SSARegister[] {
	if (instruction.instruction === 'Phi') return [instruction.destination];
	return Object.values(
		instruction.defs as Record<string, SSARegister>,
	);
}

/**
 * The registers a value-preserving instruction copies from, or `null` when the
 * instruction computes a new value. Only a register move and a Phi preserve
 * identity, which is what a rethrow of the caught value travels through.
 */
function instructionCopySources(
	instruction: SSAInstruction,
): SSARegister[] | null {
	if (instruction.instruction === 'Phi') {
		return [...instruction.sources.values()];
	}
	if (!instruction.instruction.startsWith('Mov')) return null;
	const uses = instruction.uses as Record<
		string,
		SSARegister | SSARegister[]
	>;
	return Object.values(uses).flat();
}

function terminalSuffixFingerprints(body: t.Statement[]): string[][] {
	const result: string[][] = [];
	const addTail = (statements: t.Statement[]) => {
		if (statements.length === 0) return;
		const last = statements.at(-1)!;
		const tail = statements.slice(Math.max(0, statements.length - 2));
		if (t.isReturnStatement(last) || t.isThrowStatement(last)) {
			result.push(tail.map(statementFingerprint));
		}
		collectFromStatement(last);
	};
	const collectFromStatement = (statement: t.Statement) => {
		if (t.isBlockStatement(statement)) {
			addTail(statement.body);
			return;
		}
		if (t.isTryStatement(statement)) {
			addTail(statement.block.body);
			if (statement.handler) addTail(statement.handler.body.body);
			if (statement.finalizer) addTail(statement.finalizer.body);
			return;
		}
		if (t.isIfStatement(statement)) {
			collectFromStatement(statement.consequent);
			if (statement.alternate) collectFromStatement(statement.alternate);
			return;
		}
		if (t.isLabeledStatement(statement)) {
			collectFromStatement(statement.body);
		}
	};
	addTail(body);
	return result.filter((suffix) => suffix.length > 0);
}

function isCatchPreludeStatement(statement: t.Statement): boolean {
	if (
		t.isExpressionStatement(statement) &&
		t.isCallExpression(statement.expression) &&
		t.isV8IntrinsicIdentifier(statement.expression.callee, {
			name: 'Catch',
		})
	) return true;
	return t.isVariableDeclaration(statement) &&
		statement.declarations.some((declaration) =>
			t.isCallExpression(declaration.init) &&
			t.isV8IntrinsicIdentifier(declaration.init.callee, {
				name: 'Catch',
			})
		);
}

/*
There are several instances of where a finally block is duplicated
- "Canonical": the "original" copy, a exception handler for a JS catch block
	- for when an error is raised in the catch block
- "TryTrailer": a copy after a try block
	- has the corresponding FunctionExceptionHandler end just as this finally code starts
	- end of Try blocks may just jump to "CatchTrailer"
- "ControlFlowPrologue": a copy before a Ret, Jmp (break, continue) instruction
	- has the corresponding FunctionExceptionHandler end just as this finally code starts
	- may split the exception range for a try block
	- may not be an exact match with "Canonical" due to header code deduplication if one consequent address is a terminal block
- "CatchTrailer": a copy after a catch block
	- has the FunctionExceptionHandler "caught" by the "canonical" block end just as this finally code starts
*/

/*
Finally termination types
- "Rethrow"
- "Return"
- "ReturnOverride"
*/

export class ExceptionRange {
	index: number;

	start: BlockAddr;
	end: BlockAddr;

	protectedBlocks = new AddressSet(); // "directly" protected blocks

	constructor(index: number, info: FunctionExceptionHandler) {
		this.index = index;
		this.start = info.tryStart;
		this.end = info.tryEnd;
	}
}

export interface ExceptionRangeSnapshot {
	index: number;
	start: BlockAddr;
	end: BlockAddr;
	protectedBlocks: BlockAddr[];
}

export type HandlerId = BlockAddr;
export class HandlerRecord {
	catchAddress: BlockAddr; // Also handlerId
	innerTryRecords = new AddressSet<HandlerId>();
	ranges: ExceptionRange[] = [];
	directProtectedBlocks: AddressSet | null = null;

	catchBody: AddressSet | null = null; // "directly" protected blocks within the catch body, usually catch blocks of inner trys
	canonicalFinallyAddress: FinallyId | null = null;

	constructor(catchAddress: number) {
		this.catchAddress = catchAddress;
	}

	isProtectingBlock(address: BlockAddr) {
		if (this.directProtectedBlocks != null) {
			return this.directProtectedBlocks.has(address);
		}
		return this.ranges.some(({ start, end }) =>
			address >= start && address < end
		);
	}

	get protectedBlocks() {
		if (this.directProtectedBlocks != null) {
			return new AddressSet(this.directProtectedBlocks);
		}
		return this.ranges.reduce(
			(a, { protectedBlocks }) => a.union(protectedBlocks),
			new AddressSet(),
		);
	}

	toString() {
		return `TryRecord @ ${
			this.catchAddress.toString(16)
		} { protectedBlocks: {${
			[...this.protectedBlocks].map((n) => n.toString(16)).join(', ')
		}}, innerTryRecords: {${
			[...this.innerTryRecords].map((n) => n.toString(16)).join(', ')
		}} }`;
	}
}

export interface HandlerRecordSnapshot {
	catchAddress: BlockAddr;
	innerTryRecords: HandlerId[];
	ranges: ExceptionRangeSnapshot[];
	directProtectedBlocks: BlockAddr[] | null;
	catchBody: BlockAddr[] | null;
	canonicalFinallyAddress: FinallyId | null;
}

export interface HandlerGraphFinallyOwnershipProof {
	finallyAddress: FinallyId;
	protectsCatch: boolean;
	missingProtectedBlocks: AddressSet<BlockAddr>;
	valid: boolean;
}

export interface HandlerGraphFinallyOwnershipDiagnostic {
	catchAddress: HandlerId;
	finallyAddress: FinallyId;
	protectsCatch: boolean;
	missingProtectedBlocks: AddressSet<BlockAddr>;
	message: string;
}

export class HandlerGraph {
	#func: IRFunction;
	#records = new AddressMap<HandlerRecord, number>();
	#rangeToHandlers = new AddressMap<AddressGraph>();
	#protectedEntries = new AddressSet<BlockAddr>();

	#strictDominatorMap = new AddressGraph<HandlerId, HandlerId>();
	#strictDominanceMap = new AddressGraph<HandlerId, HandlerId>();
	#dominatorTree = new AddressGraph<HandlerId, HandlerId>();
	#finallyRecords = new AddressMap<FinallyRecord>();

	constructor(
		func: IRFunction,
	) {
		this.#func = func;
		if (func._exceptionHandlers.length === 0) return;

		const graphBlockAddresses = () =>
			func.blocks.size > 0
				? func.blocks.keys()
				: func.ssa.basicBlocks.keys();
		const graphSuccessors = (addr: BlockAddr) =>
			func.blocks.get(addr)?.consequentAddresses ??
				func.ssa.basicBlocks.get(addr)?.consequentAddresses ?? [];
		const graphPredecessors = new AddressGraph<BlockAddr, BlockAddr>();
		for (const addr of graphBlockAddresses()) {
			for (const successor of graphSuccessors(addr)) {
				graphPredecessors.addEdge(successor, addr);
			}
		}
		const graphTerminalKind = (addr: BlockAddr): 'Throw' | 'Ret' | null => {
			const ssaLast = func.ssa.basicBlocks.get(addr)?.ssaInstructions.at(
				-1,
			);
			if (ssaLast?.instruction === 'Throw') return 'Throw';
			if (ssaLast?.instruction === 'Ret') return 'Ret';

			const astLast = func.blocks.get(addr)?.body.at(-1) as
				| t.Statement
				| undefined;
			if (t.isThrowStatement(astLast)) return 'Throw';
			if (t.isReturnStatement(astLast)) return 'Ret';
			return null;
		};

		const handlerToRange = new Map<
			FunctionExceptionHandler,
			ExceptionRange
		>();
		for (let i = 0; i < func._exceptionHandlers.length; i++) {
			const handler = func._exceptionHandlers[i];
			const range = new ExceptionRange(i, handler);
			handlerToRange.set(handler, range);

			this.#records.getWithDefault(
				handler.catchOffset,
				() => new HandlerRecord(handler.catchOffset),
			).ranges.push(range);

			this.#rangeToHandlers.getWithDefault(
				handler.tryStart,
				() => new AddressGraph(),
			).addEdge(handler.tryEnd, handler.catchOffset);
		}

		for (const addr of graphBlockAddresses()) {
			for (
				const handler of exceptionHandlersByAddress(
					addr,
					func._exceptionHandlers,
				)
			) {
				handlerToRange.get(handler)!.protectedBlocks.add(addr);
			}
		}

		// TODO: first construct finallyrecords from records where ranges.length == 1 and

		// For each handler, find which other handler "dominates" it
		// (i.e., protects it most directly)

		for (const [catchAddress, record] of this.#records) {
			const dominators = new AddressSet(
				this.#records.values().filter(
					(r) => HandlerGraph.#isStrictDominator(r, record),
				).map((r) => r.catchAddress),
			);

			this.#strictDominatorMap.set(catchAddress, dominators);

			// TODO: consider selecting record with smallest protection size?
		}

		/*
		let changed = false;
		do {
			changed = false;

			for (const [child, dominators] of this.#strictlyDominatedBy) {
				if (this.#immediatelyDominatedBy.has(child)) continue;

				const parents = new AddressSet();
				const filteredDominators = new AddressSet(dominators);
				for (const parent of dominators) {
					const grandparent = this.#immediatelyDominatedBy.get(parent);
					if (grandparent == null) continue;
					if (!filteredDominators.has(parent) || !filteredDominators.has(grandparent)) continue;

					filteredDominators.delete(parent);
					filteredDominators.delete(grandparent);

					parents.add(parent);
				}

				if (parents.size > 1) console.log(parents);
				let knownParent = null;
				if (parents.size === 1) {
					knownParent = [...parents][0];
				}

				if (filteredDominators.size === 0) {
					if (parents.size > 1) {
						throw new LiftError('Unresolved exception parent');
					}
					this.#immediatelyDominatedBy.set(child, knownParent);
					changed = true;
					continue;
				} else if (filteredDominators.size === 1) {
					const dominator = [...dominators][0];
					if (this.#immediatelyDominatedBy.get(dominator) === null) {
						this.#immediatelyDominatedBy.set(child, dominator);
						changed = true;
					}

					continue;
				}
			}
		} while (changed);
		*/

		for (const [key, value] of this.#strictDominatorMap) {
			for (const v of value) {
				this.#strictDominanceMap.addEdge(v, key);
			}
		}

		this.#rebuildDominatorTree();

		// Returns true if all CFG-terminal blocks reachable from addr end with Throw (rethrow).
		// This is the unambiguous case: a regular catch block falls through to the CatchTrailer
		// which ends with Ret, not Throw.
		const isFinallyCanonical = (addr: HandlerId): boolean => {
			const visited = new AddressSet();
			const stack: BlockAddr[] = [addr];
			while (stack.length > 0) {
				const current = stack.pop()!;
				if (visited.has(current)) continue;
				visited.add(current);

				if (
					!func.ssa.basicBlocks.has(current) &&
					!func.blocks.has(current)
				) return false;

				const successors = graphSuccessors(current);
				if (successors.length === 0) {
					if (graphTerminalKind(current) !== 'Throw') return false;
				} else {
					for (const succ of successors) {
						stack.push(succ);
					}
				}
			}
			return visited.size > 0;
		};

		// Returns true if all CFG-terminal blocks reachable from addr end with Throw OR Ret.
		// Used for return-override finally canonicals (finally block has explicit `return`).
		// Ret-terminal cases require an additional shared-range-starts check in the attribution
		// loop to avoid false positives from regular catch blocks that fall through to CatchTrailers.
		const isAllTerminalFinally = (addr: HandlerId): boolean => {
			const visited = new AddressSet();
			const stack: BlockAddr[] = [addr];
			while (stack.length > 0) {
				const current = stack.pop()!;
				if (visited.has(current)) continue;
				visited.add(current);

				if (
					!func.ssa.basicBlocks.has(current) &&
					!func.blocks.has(current)
				) return false;

				const successors = graphSuccessors(current);
				if (successors.length === 0) {
					const terminal = graphTerminalKind(current);
					if (terminal !== 'Throw' && terminal !== 'Ret') {
						return false;
					}
				} else {
					for (const succ of successors) {
						stack.push(succ);
					}
				}
			}
			return visited.size > 0;
		};

		const hasThrowTerminal = (addr: HandlerId): boolean => {
			const visited = new AddressSet();
			const stack: BlockAddr[] = [addr];
			while (stack.length > 0) {
				const current = stack.pop()!;
				if (visited.has(current)) continue;
				visited.add(current);

				if (
					!func.ssa.basicBlocks.has(current) &&
					!func.blocks.has(current)
				) continue;

				const successors = graphSuccessors(current);
				if (successors.length === 0) {
					if (graphTerminalKind(current) === 'Throw') return true;
				} else {
					for (const succ of successors) {
						stack.push(succ);
					}
				}
			}
			return false;
		};

		/**
		 * A finalizer re-raises the value it caught; a handler that throws a
		 * value it built itself is a source-level `catch` however its terminals
		 * look — `catch { throw new Error(...) }` reaches nothing but `Throw`.
		 *
		 * Only a provably fresh thrown value disqualifies a candidate. A thrown
		 * register this walk cannot resolve is treated as a rethrow, so shapes
		 * outside the copy/Phi model keep the classification they had.
		 */
		const rethrowsCaughtValue = (addr: HandlerId): boolean => {
			const reachable: BlockAddr[] = [];
			const visited = new AddressSet<BlockAddr>();
			const stack: BlockAddr[] = [addr];
			while (stack.length > 0) {
				const current = stack.pop()!;
				if (visited.has(current)) continue;
				visited.add(current);
				if (!func.ssa.basicBlocks.has(current)) continue;
				reachable.push(current);
				for (const successor of graphSuccessors(current)) {
					stack.push(successor);
				}
			}
			const caught = new Set<RegisterKey>();
			const definitions = new Map<RegisterKey, SSAInstruction>();
			for (const address of reachable) {
				for (
					const instruction of func.ssa.basicBlocks.get(address)
						?.ssaInstructions ?? []
				) {
					for (const register of instructionDefines(instruction)) {
						definitions.set(registerKey(register), instruction);
					}
					if (instruction.instruction !== 'Catch') continue;
					caught.add(registerKey(instruction.defs.destination));
				}
			}
			if (caught.size === 0) return true;
			// The caught value reaches its rethrow through register copies and
			// through Phis that merge nothing but copies of it.
			for (let changed = true; changed;) {
				changed = false;
				for (const [key, instruction] of definitions) {
					if (caught.has(key)) continue;
					const sources = instructionCopySources(instruction);
					if (
						sources == null || sources.length === 0 ||
						!sources.every((source) =>
							caught.has(registerKey(source))
						)
					) continue;
					caught.add(key);
					changed = true;
				}
			}
			for (const address of reachable) {
				const last = func.ssa.basicBlocks.get(address)?.ssaInstructions
					.at(-1);
				if (last?.instruction !== 'Throw') continue;
				const key = registerKey(last.uses.exception);
				if (caught.has(key) || !definitions.has(key)) continue;
				return false;
			}
			return true;
		};

		/**
		 * IteratorClose's exceptional form is an implicit finalization protocol:
		 * it closes the iterator and rethrows the same exception. Normal loop
		 * exhaustion deliberately has no matching close copy, so the opcode
		 * itself is the ownership proof.
		 */
		const isIteratorCloseFinalizer = (addr: HandlerId): boolean => {
			const block = func.ssa.basicBlocks.get(addr);
			if (!block) return false;
			const core = block.ssaInstructions.filter((instruction) =>
				instruction.instruction !== 'Phi' &&
				instruction.instruction !== 'Catch' &&
				instruction.instruction !== 'Throw'
			);
			return core.length === 1 &&
				core[0].instruction === 'IteratorClose';
		};

		/**
		 * A catch landing pad can be only a short state-staging prefix before it
		 * rejoins the protected block's ordinary completion dispatcher. Following
		 * that dispatcher to its Ret/Throw leaves makes it look like a mixed
		 * return-override finalizer even though the handler owns none of that code.
		 *
		 * Reaching a block that also has a normal predecessor in this handler's
		 * protected range is direct CFG proof that this is a catch completion
		 * join, not a standalone finally canonical. The walk follows the whole
		 * handler, not a linear prefix: a handler that inspects the caught value
		 * before deciding to rethrow branches immediately, and the join it
		 * resumes at lies past that diamond.
		 *
		 * Another handler's block ends the walk. Its code belongs to that
		 * record, so whatever it joins says nothing about this one.
		 */
		const joinsProtectedCompletion = (
			handler: HandlerId,
			record: HandlerRecord,
		): boolean => {
			const visited = new AddressSet<BlockAddr>();
			const stack: BlockAddr[] = [handler];
			while (stack.length > 0) {
				const cursor = stack.pop()!;
				if (visited.has(cursor)) continue;
				visited.add(cursor);
				// A suspend ends the handler's control flow. The edge out of it
				// is a generator resume, and the block it resumes at belongs to
				// the machine both arms share -- not to a catch completion.
				if (cursor !== handler && graphTerminalKind(cursor) === 'Ret') {
					continue;
				}
				for (const next of graphSuccessors(cursor)) {
					if (
						[...(graphPredecessors.get(next) ?? [])].some(
							(predecessor) =>
								record.protectedBlocks.has(predecessor),
						)
					) return true;
					if (this.#records.has(next)) continue;
					stack.push(next);
				}
			}
			return false;
		};
		const joinsSharedHandlerCompletion = (handler: HandlerId): boolean => {
			const visited = new AddressSet<BlockAddr>();
			let cursor = handler;
			while (!visited.has(cursor)) {
				visited.add(cursor);
				const successors = graphSuccessors(cursor);
				if (successors.length !== 1) return false;
				const next = successors[0];
				const handlerPredecessors = [
					...(graphPredecessors.get(next) ?? []),
				].filter((predecessor) => this.#records.has(predecessor));
				if (handlerPredecessors.length > 1) return true;
				if (this.#records.has(next)) return false;
				cursor = next;
			}
			return false;
		};

		const returnRegisterValue = (reg: SSARegister): unknown => {
			for (const block of func.ssa.basicBlocks.values()) {
				for (const instr of block.ssaInstructions) {
					if (instr.instruction !== 'LoadConst') continue;
					const destination = instr.defs.destination;
					if (
						destination.index === reg.index &&
						destination.version === reg.version
					) {
						return instr.value;
					}
				}
			}
			return Symbol.for('unknown-return-value');
		};

		const hasExplicitReturnTerminal = (addr: HandlerId): boolean => {
			const visited = new AddressSet();
			const stack: BlockAddr[] = [addr];
			while (stack.length > 0) {
				const current = stack.pop()!;
				if (visited.has(current)) continue;
				visited.add(current);

				if (
					!func.ssa.basicBlocks.has(current) &&
					!func.blocks.has(current)
				) continue;

				const successors = graphSuccessors(current);
				if (successors.length === 0) {
					const last = func.ssa.basicBlocks.get(current)
						?.ssaInstructions.at(-1);
					if (
						(last?.instruction === 'Ret' &&
							returnRegisterValue(last.uses.argument) !==
								undefined) ||
						t.isReturnStatement(
							func.blocks.get(current)?.body.at(-1) as
								| t.Statement
								| undefined,
						)
					) {
						return true;
					}
				} else {
					for (const succ of successors) {
						stack.push(succ);
					}
				}
			}
			return false;
		};

		const normallyReaches = (
			start: BlockAddr,
			target: BlockAddr,
		): boolean => {
			const visited = new AddressSet();
			const stack: BlockAddr[] = [start];
			while (stack.length > 0) {
				const current = stack.pop()!;
				if (current === target) return true;
				if (visited.has(current)) continue;
				visited.add(current);

				const blk = func.ssa.basicBlocks.get(current);
				if (!blk && !func.blocks.has(current)) continue;
				if (
					blk?.ssaInstructions[0]?.instruction === 'ResumeGenerator'
				) {
					const [resumeContinuation] = graphSuccessors(current);
					if (resumeContinuation !== undefined) {
						stack.push(resumeContinuation);
					}
					continue;
				}
				for (const succ of graphSuccessors(current)) {
					stack.push(succ);
				}
			}
			return false;
		};

		const hasEquivalentReturnOverrideCopy = (
			finallyAddr: HandlerId,
		): boolean => {
			for (const other of this.#records.keys()) {
				if (other === finallyAddr) continue;
				if (!isAllTerminalFinally(other) || hasThrowTerminal(other)) {
					continue;
				}
				if (!hasExplicitReturnTerminal(other)) continue;
				if (compareFinallyCopies(func, other, finallyAddr)) return true;
			}
			return false;
		};

		const hasRecognizedFinallyOwner = (finallyAddr: HandlerId): boolean => {
			const record = this.#records.get(finallyAddr);
			if (!record) return false;

			for (const owner of this.#finallyRecords.keys()) {
				if (owner === finallyAddr) continue;
				if (
					record.ranges.some((range) =>
						normallyReaches(owner, range.start)
					)
				) {
					return true;
				}
			}
			return false;
		};

		const canonicalFinallyCoreFingerprints = (
			finallyAddr: HandlerId,
		): string[] => {
			const block = func.blocks.get(finallyAddr);
			if (!block) return [];
			const body = (block.body as t.Statement[]).slice();
			while (body.length > 0 && isCatchPreludeStatement(body[0])) {
				body.shift();
			}
			const last = body.at(-1);
			if (last && t.isThrowStatement(last)) body.pop();
			return body.map(statementFingerprint);
		};

		const blockStartsWithFingerprints = (
			addr: BlockAddr,
			pattern: string[],
		): boolean => {
			if (pattern.length === 0) return false;
			const block = func.blocks.get(addr);
			if (!block) return false;
			const candidate = (block.body as t.Statement[]).map(
				statementFingerprint,
			);
			if (candidate.length < pattern.length) return false;
			return pattern.every((fingerprint, index) =>
				candidate[index] === fingerprint
			);
		};

		const matchesFinallyCopyRoot = (
			finallyAddr: HandlerId,
			copyRoot: BlockAddr,
		): boolean => {
			return compareFinallyCopies(func, finallyAddr, copyRoot) ||
				compareFinallyCopyPrefix(func, finallyAddr, copyRoot) ||
				compareFinallyCopySuffixPrefix(
					func,
					finallyAddr,
					copyRoot,
				) ||
				compareFinallyEffectBlocks(
					func,
					finallyAddr,
					copyRoot,
				) ||
				blockStartsWithFingerprints(
					copyRoot,
					canonicalFinallyCoreFingerprints(finallyAddr),
				);
		};

		const recordEntryBlocks = (
			record: HandlerRecord,
		): AddressSet<BlockAddr> => {
			const protectedBlocks = record.protectedBlocks;
			let entries = new AddressSet(
				[...this.#protectedEntries].filter((entry) =>
					protectedBlocks.has(entry)
				),
			);
			if (entries.size === 0) {
				entries = new AddressSet(
					record.ranges.map((range) => range.start),
				);
			}
			if (
				entries.size === 0 &&
				record.directProtectedBlocks != null
			) {
				const entry = minAddress(record.directProtectedBlocks);
				if (entry != null) entries.add(entry);
			}
			return entries;
		};

		const extendCatchBodyContinuations = (
			catchRecord: HandlerRecord,
			catchTrailerStart?: BlockAddr,
		) => {
			if (catchRecord.catchBody == null) {
				catchRecord.catchBody = new AddressSet([
					catchRecord.catchAddress,
				]);
			}
			if (catchTrailerStart != null) {
				catchRecord.catchBody.add(catchTrailerStart);
			}

			let changed = true;
			while (changed) {
				changed = false;
				for (const [handler, record] of this.#records) {
					if (handler === catchRecord.catchAddress) continue;
					if (record.protectedBlocks.size > 8) continue;
					const entries = recordEntryBlocks(record);
					if (
						catchTrailerStart != null &&
						[...entries].every((entry) =>
							entry >= catchTrailerStart
						)
					) {
						continue;
					}
					if (!entries.intersection(catchRecord.catchBody).size) {
						continue;
					}
					for (const block of record.protectedBlocks) {
						if (catchRecord.catchBody.has(block)) continue;
						catchRecord.catchBody.add(block);
						changed = true;
					}
					if (
						isFinallyCanonical(handler) ||
						this.#finallyRecords.has(handler)
					) {
						continue;
					}
					if (!catchRecord.catchBody.has(handler)) {
						catchRecord.catchBody.add(handler);
						changed = true;
					}
				}
			}
		};

		const finallyProtectsCatchAndProtectedBlocks = (
			finallyRecord: HandlerRecord,
			catchRecord: HandlerRecord,
			catchAddr: HandlerId,
		): boolean => {
			if (!finallyRecord.protectedBlocks.has(catchAddr)) return false;
			for (const block of catchRecord.protectedBlocks) {
				if (!finallyRecord.protectedBlocks.has(block)) return false;
			}
			return true;
		};

		let foundFinally;
		do {
			foundFinally = false;

			for (const [finallyAddr, domChildren] of this.#dominatorTree) {
				if (this.#finallyRecords.has(finallyAddr)) continue;
				if (
					this.#records.get(finallyAddr)?.canonicalFinallyAddress !=
						null
				) continue;

				// A candidate only rethrows if it re-raises what it caught: a
				// handler that throws a value of its own is a catch, and its
				// `Throw` leaves must not be read as the finalizer protocol.
				const rethrows = rethrowsCaughtValue(finallyAddr);
				const isThrowFinal = isFinallyCanonical(finallyAddr) &&
					rethrows;
				const hasRethrowExit = isThrowFinal ||
					(hasThrowTerminal(finallyAddr) && rethrows);
				if (!isThrowFinal && !isAllTerminalFinally(finallyAddr)) {
					continue;
				}
				if (
					!hasRethrowExit && !hasExplicitReturnTerminal(finallyAddr)
				) continue;
				const finallyHandlerRecord = this.#records.get(finallyAddr)!;
				if (
					joinsProtectedCompletion(
						finallyAddr,
						finallyHandlerRecord,
					)
				) continue;
				if (joinsSharedHandlerCompletion(finallyAddr)) continue;
				const finallyRangeStarts = new AddressSet(
					finallyHandlerRecord.ranges.map((r) => r.start),
				);
				const hasEquivalentCopy = !hasRethrowExit &&
					hasEquivalentReturnOverrideCopy(finallyAddr);
				// A rethrowing handler is observationally indistinguishable from
				// `catch (error) { ...; throw error; }` unless the bytecode also
				// contains a copy of its body on a protected normal/abrupt exit.
				// IteratorClose is the one exception: its exceptional-only
				// close-and-rethrow protocol is intrinsically finalizer-shaped.
				const matchingCopyRoots = new AddressSet<BlockAddr>();
				for (const range of finallyHandlerRecord.ranges) {
					if (
						range.end !== finallyAddr &&
						matchesFinallyCopyRoot(finallyAddr, range.end)
					) {
						matchingCopyRoots.add(range.end);
					}
				}
				const finallyProtectedBlocks =
					finallyHandlerRecord.protectedBlocks;
				for (const block of finallyProtectedBlocks) {
					for (const successor of graphSuccessors(block)) {
						if (
							successor === finallyAddr ||
							finallyProtectedBlocks.has(successor)
						) continue;
						// Boundary successors can be numerous. The single-block
						// effect proof is sufficient here; reserve recursive
						// copy comparison for explicit exception-range ends.
						if (
							compareFinallyEffectBlocks(
								func,
								finallyAddr,
								successor,
							)
						) matchingCopyRoots.add(successor);
					}
				}
				if (
					hasRethrowExit &&
					matchingCopyRoots.size === 0 &&
					!isIteratorCloseFinalizer(finallyAddr)
				) continue;

				const candidateCatches = new AddressSet<HandlerId>(
					[...domChildren].filter((c) => {
						if (isFinallyCanonical(c)) return false; // exclude Throw-terminal finally canonicals
						const candidateRecord = this.#records.get(c)!;
						if (
							!finallyProtectsCatchAndProtectedBlocks(
								finallyHandlerRecord,
								candidateRecord,
								c,
							)
						) return false;
						if (hasRethrowExit) {
							// Associating a finalizer with a nested catch also
							// makes this range end the catch trailer. Require that
							// specific exit to be an actual finalizer-body copy;
							// a generator suspension or unrelated protected exit
							// must not seed the catch body.
							const catchCoveringRange = finallyHandlerRecord
								.ranges
								.find((range) =>
									range.start <= c && c < range.end
								);
							if (
								catchCoveringRange == null ||
								!matchingCopyRoots.has(catchCoveringRange.end)
							) return false;
						}

						if (!hasRethrowExit) {
							// Ret-terminal (return-override) finally canonical: requires stricter checks.
							//
							// 1. Shared range starts: both protect the same try body start addresses.
							const catchRangeStarts = new AddressSet(
								candidateRecord.ranges.map((r) => r.start),
							);
							if (
								!finallyRangeStarts.intersection(
									catchRangeStarts,
								).size
							) return false;

							// 2. The finally canonical's range normally starts before the catch
							//    address. Cleanup ranges can start exactly at the catch address;
							//    accept those only when the handler is either unique or owned by
							//    an already-recognized enclosing finally body.
							const coversCatch = finallyHandlerRecord.ranges
								.some((r) => r.start < c && c < r.end);
							const coversCatchBodyCleanup = finallyHandlerRecord
								.ranges.some((r) => r.start === c && c < r.end);
							if (
								!coversCatch &&
								!(coversCatchBodyCleanup &&
									(!hasEquivalentCopy ||
										hasRecognizedFinallyOwner(finallyAddr)))
							) {
								return false;
							}
						}

						return true;
					}),
				);

				if (candidateCatches.size === 0) {
					// Simple try-finally with no nested handlers: the finally canonical
					// has no dominated children. Add it directly using itself as the key.
					if (hasRethrowExit) {
						const fr = new FinallyRecord(finallyAddr);
						fr.isReturnOverride = !hasRethrowExit;
						for (const copyRoot of matchingCopyRoots) {
							fr.copyRoots.add(copyRoot);
						}
						this.#finallyRecords.set(finallyAddr, fr);
						foundFinally = true;
					}
					continue;
				}

				// Pick the candidate with the largest protected region (most closely mirrors the finally's scope)
				let attributedCatch: HandlerId;
				if (candidateCatches.size === 1) {
					attributedCatch = [...candidateCatches][0];
				} else {
					let best: HandlerId | null = null;
					let bestSize = -1;
					for (const c of candidateCatches) {
						const size = this.#records.get(c)!.protectedBlocks.size;
						if (size > bestSize) {
							bestSize = size;
							best = c;
						}
					}
					if (best === null) continue;
					attributedCatch = best;
				}

				const catchHandlerRecord = this.#records.get(attributedCatch)!;
				catchHandlerRecord.canonicalFinallyAddress = finallyAddr;
				const existingCatchFinally = this.#finallyRecords.get(
					attributedCatch,
				);
				if (
					existingCatchFinally?.isReturnOverride &&
					this.#finallyRecords.delete(attributedCatch)
				) {
					foundFinally = true;
				}

				// CatchTrailer: tryEnd of the finally range that spans the catch body
				const catchCoveringRange = finallyHandlerRecord.ranges.find(
					(r) =>
						r.start <= attributedCatch && attributedCatch < r.end,
				);
				if (
					catchCoveringRange &&
					catchHandlerRecord.protectedBlocks.size <= 8
				) {
					catchHandlerRecord.catchBody = new AddressSet([
						...(catchHandlerRecord.catchBody ?? []),
						...[...catchCoveringRange.protectedBlocks].filter((
							block,
						) => block < catchCoveringRange.end),
						attributedCatch,
					]);
				}

				const fr = new FinallyRecord(finallyAddr);
				if (catchCoveringRange) {
					fr.catchTrailer = {
						start: catchCoveringRange.end,
						end: null,
					};
				}
				if (catchHandlerRecord.protectedBlocks.size <= 8) {
					extendCatchBodyContinuations(
						catchHandlerRecord,
						fr.catchTrailer?.start,
					);
				}
				// Return-override: the finally block has an explicit `return` — the canonical
				// ends with Ret instead of Throw.
				fr.isReturnOverride = !hasRethrowExit;

				const copyTemplate = fr.catchTrailer?.start;
				if (copyTemplate != null) {
					for (const candidate of matchingCopyRoots) {
						if (
							compareFinallyCopies(
								func,
								copyTemplate,
								candidate,
							) ||
							(copyTemplate != null &&
								blockStartsWithFingerprints(
									candidate,
									canonicalFinallyCoreFingerprints(
										copyTemplate,
									),
								))
						) {
							fr.copyRoots.add(candidate);
						}
					}
				}

				this.#finallyRecords.set(finallyAddr, fr);
				foundFinally = true;
			}
		} while (foundFinally);

		for (const [finallyAddr, record] of this.#records) {
			if (this.#finallyRecords.has(finallyAddr)) continue;
			if (record.canonicalFinallyAddress != null) continue;
			if (!isFinallyCanonical(finallyAddr)) continue;

			const domChildren = this.#dominatorTree.get(finallyAddr);
			if (domChildren && domChildren.size > 0) continue;
			if (record.ranges.some((range) => this.#records.has(range.start))) {
				continue;
			}
			if (
				record.ranges.some((range) =>
					range.end <= finallyAddr && finallyAddr - range.end <= 4
				)
			) continue;

			const copyRoots = new AddressSet<BlockAddr>();
			for (const range of record.ranges) {
				if (matchesFinallyCopyRoot(finallyAddr, range.end)) {
					copyRoots.add(range.end);
				}
			}
			if (copyRoots.size === 0) continue;

			const fr = new FinallyRecord(finallyAddr);
			for (const copyRoot of copyRoots) fr.copyRoots.add(copyRoot);
			this.#finallyRecords.set(finallyAddr, fr);
		}
	}

	get records() {
		return this.#records;
	}
	get finallyRecords() {
		return this.#finallyRecords;
	}

	isSuspendingReturnOverrideFinalizerCopy(
		finallyAddress: FinallyId,
		copyRoot: BlockAddr,
	): boolean {
		const record = this.#finallyRecords.get(finallyAddress);
		if (!record?.isReturnOverride) return false;
		if (
			record.catchTrailer?.start !== copyRoot &&
			!record.copyRoots.has(copyRoot)
		) return false;
		const block = this.#func.blocks.get(copyRoot);
		return block != null &&
			statementsMaySuspend(block.body as t.Statement[]);
	}

	finalizerCleanupPlan(): HandlerGraphFinalizerCleanupPlan {
		const removeRanges: HandlerGraphStatementRange[] = [];
		const replaceWithReturnRanges: HandlerGraphStatementRange[] = [];
		const embeddedCatchActions: HandlerGraphEmbeddedFinalizerAction[] = [];
		let enclosingEdgeActionCount = 0;
		for (const descriptor of this.structuredRegionDescriptors()) {
			if (descriptor.kind !== 'finally') continue;
			enclosingEdgeActionCount +=
				descriptor.enclosingFinallyCopyRoots.length;
			for (const copy of descriptor.finallyCopies) {
				if (copy.kind !== 'catchTrailer') continue;
				const block = this.#func.blocks.get(copy.copyRoot);
				if (!block) continue;
				if (!statementsMaySuspend(block.body as t.Statement[])) {
					continue;
				}
				embeddedCatchActions.push({
					owner: descriptor.handler,
					copyRoot: copy.copyRoot,
					kind: copy.kind,
					replacementFingerprints: (block.body as t.Statement[]).map(
						statementFingerprint,
					),
					terminalSuffixFingerprints: terminalSuffixFingerprints(
						block.body as t.Statement[],
					),
					maySuspend: true,
				});
			}
			for (const suffix of descriptor.finallyCopySuffixes) {
				for (const range of suffix.skipRanges ?? []) {
					if (suffix.kind === 'catchTrailer') {
						replaceWithReturnRanges.push({ ...range });
					} else {
						removeRanges.push({ ...range });
					}
				}
				if (suffix.kind === 'catchTrailer') {
					if (!statementsMaySuspend(suffix.statements)) continue;
					embeddedCatchActions.push({
						owner: descriptor.handler,
						copyRoot: suffix.copyRoot,
						kind: suffix.kind,
						replacementFingerprints: suffix.statements.map(
							statementFingerprint,
						),
						terminalSuffixFingerprints: terminalSuffixFingerprints(
							suffix.statements,
						),
						maySuspend: true,
					});
				}
			}
		}
		return {
			removeRanges,
			replaceWithReturnRanges,
			embeddedCatchActions,
			enclosingEdgeActionCount,
		};
	}

	structuredRegionForest(): HandlerGraphRegionForest {
		const descriptors = this.structuredRegionDescriptors();
		const nodes = descriptors.map((descriptor) => ({
			descriptor,
			children: [] as HandlerGraphRegionForestNode[],
		}));
		const nodeByHandler = new AddressMap<HandlerGraphRegionForestNode>();
		for (const node of nodes) {
			nodeByHandler.set(node.descriptor.handler, node);
		}
		const parentByHandler = new AddressMap<BlockAddr>();

		for (const child of nodes) {
			const parent = nodes.filter((candidate) =>
				candidate !== child &&
				descriptorContainsDescriptor(
					candidate.descriptor,
					child.descriptor,
				)
			).toSorted((left, right) =>
				left.descriptor.protectedBlocks.size -
					right.descriptor.protectedBlocks.size ||
				left.descriptor.handler - right.descriptor.handler
			)[0];
			if (!parent) continue;
			parent.children.push(child);
			parentByHandler.set(
				child.descriptor.handler,
				parent.descriptor.handler,
			);
		}

		const roots = nodes.filter((node) =>
			!parentByHandler.has(node.descriptor.handler)
		);
		sortForestNodes(roots);
		return { roots, nodeByHandler, parentByHandler };
	}

	/**
	 * Catch landing pads Hermes split while inlining a protected expression.
	 *
	 * The child handler must be nested by the exception table, converge with its
	 * parent through equivalent value-only completion instructions, and then
	 * share the entire continuation. The child can then be represented by the
	 * parent catch without losing an observable handler effect.
	 */
	equivalentCatchHandlerAliases(): AddressMap<BlockAddr> {
		const aliases = new AddressMap<BlockAddr>();
		const forest = this.structuredRegionForest();
		for (const [childHandler, parentHandler] of forest.parentByHandler) {
			const child = forest.nodeByHandler.get(childHandler)?.descriptor;
			const parent = forest.nodeByHandler.get(parentHandler)?.descriptor;
			if (child?.kind !== 'catch' || parent?.kind !== 'catch') continue;
			if (
				equivalentPureCatchCompletion(
					this.#func,
					parentHandler,
					childHandler,
				)
			) aliases.set(childHandler, parentHandler);
		}
		return aliases;
	}

	structuredRegionDescriptors(): HandlerGraphRegionDescriptor[] {
		const catchContinuationBodies = this.#catchContinuationBodies();
		return [...this.#records.values()].map((record) => {
			const finallyRecord = this.#finallyRecords.get(
				record.catchAddress,
			);
			const kind: HandlerGraphRegionDescriptor['kind'] = finallyRecord
				? 'finally'
				: 'catch';
			const protectedBlocks = new AddressSet(record.protectedBlocks);
			let protectedEntries = new AddressSet(
				[...this.#protectedEntries].filter((entry) =>
					protectedBlocks.has(entry)
				),
			);
			if (protectedEntries.size === 0) {
				protectedEntries = new AddressSet(
					record.ranges.map((range) => range.start),
				);
			}
			if (
				protectedEntries.size === 0 &&
				record.directProtectedBlocks != null
			) {
				const entry = minAddress(record.directProtectedBlocks);
				if (entry != null) protectedEntries.add(entry);
			}
			const catchBody = new AddressSet<BlockAddr>([
				...(record.catchBody ?? []),
				...(catchContinuationBodies.get(record.catchAddress) ?? []),
			]);
			const finallyOwnership = this.#finallyOwnershipProof(record);
			return {
				handler: record.catchAddress,
				kind,
				protectedBlocks,
				protectedEntries,
				catchBody: catchBody.size === 0 ? null : catchBody,
				canonicalFinallyAddress: record.canonicalFinallyAddress,
				canonicalFinallyOwnership: finallyOwnership,
				finallyCopyRoots: finallyRecord == null
					? new AddressSet()
					: new AddressSet(finallyRecord.copyRoots),
				finallyBodyBlocks: finallyRecord == null
					? null
					: this.#finallyBodyBlocks(record, finallyRecord),
				finallyCopies: finallyRecord == null
					? []
					: this.#finallyCopies(record, finallyRecord),
				finallyCopySuffixes: finallyRecord == null
					? []
					: this.#finallyCopySuffixes(record, finallyRecord),
				enclosingFinallyCopyRoots: finallyRecord == null
					? []
					: this.#enclosingFinallyCopyRoots(record, finallyRecord),
			};
		}).toSorted((left, right) => left.handler - right.handler);
	}

	finallyOwnershipDiagnostics(): HandlerGraphFinallyOwnershipDiagnostic[] {
		const diagnostics: HandlerGraphFinallyOwnershipDiagnostic[] = [];
		for (const record of this.#records.values()) {
			const proof = this.#finallyOwnershipProof(record);
			if (proof == null || proof.valid) continue;
			const missing = [...proof.missingProtectedBlocks].map((block) =>
				`0x${block.toString(16)}`
			).join(', ');
			diagnostics.push({
				catchAddress: record.catchAddress,
				finallyAddress: proof.finallyAddress,
				protectsCatch: proof.protectsCatch,
				missingProtectedBlocks: proof.missingProtectedBlocks,
				message: proof.protectsCatch
					? `finally 0x${
						proof.finallyAddress.toString(16)
					} does not protect catch 0x${
						record.catchAddress.toString(16)
					} protected blocks: ${missing}`
					: `finally 0x${
						proof.finallyAddress.toString(16)
					} does not protect catch handler 0x${
						record.catchAddress.toString(16)
					}`,
			});
		}
		return diagnostics;
	}

	/**
	 * Ordered ownership actions for canonical and copied finalizer paths. These
	 * are derived before CFG materialization so emitters do not need to infer
	 * ownership from generated AST text.
	 */
	finalizerEdgeActions(): HandlerGraphFinalizerEdgeAction[] {
		const descriptors = this.structuredRegionDescriptors();
		const descriptorByHandler = new AddressMap(
			descriptors.map((descriptor) => [descriptor.handler, descriptor]),
		);
		const forest = this.structuredRegionForest();
		const depth = new Map<BlockAddr, number>();
		const handlerDepth = (handler: BlockAddr): number => {
			const cached = depth.get(handler);
			if (cached != null) return cached;
			const parent = forest.parentByHandler.get(handler);
			const value = parent == null ? 0 : handlerDepth(parent) + 1;
			depth.set(handler, value);
			return value;
		};
		const actions: HandlerGraphFinalizerEdgeAction[] = [];
		for (const descriptor of descriptors) {
			if (descriptor.kind !== 'finally') continue;
			const add = (
				action: Omit<HandlerGraphFinalizerEdgeAction, 'depth'>,
			) => actions.push({
				...action,
				depth: handlerDepth(descriptor.handler),
			});
			for (const from of descriptor.protectedEntries) {
				add({
					handler: descriptor.handler,
					edge: { from, to: descriptor.handler, kind: 'exceptional' },
					canonical: descriptor.handler,
					copyRoot: descriptor.handler,
					ownerBlock: from,
					next: null,
					kind: 'canonical',
					completion: 'throw',
					statements: [],
					skipRanges: [],
				});
			}
			const suffixRoots = new Set(
				descriptor.finallyCopySuffixes.map((suffix) => suffix.copyRoot),
			);
			for (const suffix of descriptor.finallyCopySuffixes) {
				add({
					handler: descriptor.handler,
					edge: {
						from: suffix.ownerBlock,
						to: suffix.copyRoot,
						kind: 'normal',
					},
					canonical: suffix.canonical,
					copyRoot: suffix.copyRoot,
					ownerBlock: suffix.ownerBlock,
					next: suffix.next,
					kind: suffix.kind === 'catchTrailer'
						? 'catch-copy'
						: 'abrupt-copy',
					completion: finalizerCompletion(suffix.statements, true),
					statements: suffix.statements.map((statement) =>
						t.cloneNode(statement, true)
					),
					skipRanges:
						suffix.skipRanges?.map((range) => ({ ...range })) ??
							[],
				});
			}
			for (const copy of descriptor.finallyCopies) {
				if (copy.copyRoot === descriptor.handler) continue;
				if (suffixRoots.has(copy.copyRoot)) continue;
				const owners = [...this.#func.predecessorsOf(copy.copyRoot)]
					.filter((owner) => descriptor.protectedBlocks.has(owner));
				for (const ownerBlock of owners) {
					const block = this.#func.blocks.get(copy.copyRoot);
					add({
						handler: descriptor.handler,
						edge: {
							from: ownerBlock,
							to: copy.copyRoot,
							kind: 'normal',
						},
						canonical: copy.canonical,
						copyRoot: copy.copyRoot,
						ownerBlock,
						next: copy.next,
						kind: copy.kind === 'normalExit'
							? 'normal-copy'
							: copy.kind === 'catchTrailer'
							? 'catch-copy'
							: 'abrupt-copy',
						completion: finalizerCompletion(
							(block?.body as t.Statement[] | undefined) ?? [],
							copy.kind !== 'normalExit',
						),
						statements: [],
						skipRanges:
							copy.skipRanges?.map((range) => ({ ...range })) ??
								[],
					});
				}
			}
			for (const copy of descriptor.enclosingFinallyCopyRoots) {
				const ownerDescriptor = descriptorByHandler.get(copy.owner);
				if (ownerDescriptor?.kind !== 'finally') continue;
				const predecessors = [
					...this.#func.predecessorsOf(copy.tailRoot),
				];
				for (const ownerBlock of predecessors) {
					const block = this.#func.blocks.get(copy.tailRoot);
					actions.push({
						handler: copy.owner,
						edge: {
							from: ownerBlock,
							to: copy.tailRoot,
							kind: 'normal',
						},
						canonical: copy.owner,
						copyRoot: copy.tailRoot,
						ownerBlock,
						next: null,
						kind: 'enclosing-copy',
						completion: finalizerCompletion(
							(block?.body as t.Statement[] | undefined) ?? [],
							true,
						),
						statements: [],
						skipRanges: [],
						depth: handlerDepth(copy.owner),
					});
				}
			}
		}
		return uniqueFinalizerEdgeActions(actions).toSorted((left, right) =>
			left.edge.from - right.edge.from ||
			left.edge.to - right.edge.to ||
			right.depth - left.depth ||
			left.kind.localeCompare(right.kind)
		);
	}

	#finallyOwnershipProof(
		record: HandlerRecord,
	): HandlerGraphFinallyOwnershipProof | null {
		const finallyAddress = record.canonicalFinallyAddress;
		if (finallyAddress == null) return null;
		const finallyRecord = this.#records.get(finallyAddress);
		if (!finallyRecord) {
			return {
				finallyAddress,
				protectsCatch: false,
				missingProtectedBlocks: new AddressSet(record.protectedBlocks),
				valid: false,
			};
		}
		const missingProtectedBlocks = new AddressSet<BlockAddr>();
		const finallyProtectedBlocks = finallyRecord.protectedBlocks;
		const protectsCatch = finallyProtectedBlocks.has(record.catchAddress);
		for (const block of record.protectedBlocks) {
			if (!finallyProtectedBlocks.has(block)) {
				missingProtectedBlocks.add(block);
			}
		}
		return {
			finallyAddress,
			protectsCatch,
			missingProtectedBlocks,
			valid: protectsCatch && missingProtectedBlocks.size === 0,
		};
	}

	#catchContinuationBodies(): AddressMap<AddressSet<BlockAddr>> {
		const continuations = new AddressMap<AddressSet<BlockAddr>>();
		for (const [finallyAddr, finallyRecord] of this.#finallyRecords) {
			const start = finallyRecord.catchTrailer?.start;
			if (start == null) continue;
			for (const [catchAddr, record] of this.#records) {
				if (record.canonicalFinallyAddress !== finallyAddr) continue;
				if (record.protectedBlocks.size > 8) continue;
				const body = continuations.getWithDefault(
					catchAddr,
					() => new AddressSet<BlockAddr>(),
				);
				body.add(start);
				this.#extendCatchContinuationBody(body, catchAddr, start);
			}
		}
		return continuations;
	}

	#extendCatchContinuationBody(
		body: AddressSet<BlockAddr>,
		ownerCatch: HandlerId,
		catchTrailerStart: BlockAddr,
	) {
		let changed = true;
		while (changed) {
			changed = false;
			for (const [handler, record] of this.#records) {
				if (handler === ownerCatch) continue;
				if (record.protectedBlocks.size > 8) continue;
				const entries = this.#recordEntryBlocks(record);
				if ([...entries].every((entry) => entry >= catchTrailerStart)) {
					continue;
				}
				if (!entries.intersection(body).size) continue;
				for (const block of record.protectedBlocks) {
					if (body.has(block)) continue;
					body.add(block);
					changed = true;
				}
				if (this.#finallyRecords.has(handler)) continue;
				if (!body.has(handler)) {
					body.add(handler);
					changed = true;
				}
			}
		}
	}

	#recordEntryBlocks(record: HandlerRecord): AddressSet<BlockAddr> {
		const protectedBlocks = record.protectedBlocks;
		let entries = new AddressSet(
			[...this.#protectedEntries].filter((entry) =>
				protectedBlocks.has(entry)
			),
		);
		if (entries.size === 0) {
			entries = new AddressSet(record.ranges.map((range) => range.start));
		}
		if (
			entries.size === 0 &&
			record.directProtectedBlocks != null
		) {
			const entry = minAddress(record.directProtectedBlocks);
			if (entry != null) entries.add(entry);
		}
		return entries;
	}

	#finallyBodyBlocks(
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
	): BlockAddr[] | null {
		const preferred = this.#preferredFinallyBodyBlocks(
			record,
			finallyRecord,
		);
		if (preferred != null) return preferred;
		const canonicalBlocks = this.#matchedCanonicalFinalizerBlocks(
			record,
			finallyRecord,
		);
		if (canonicalBlocks != null) return canonicalBlocks;
		for (
			const entry of [
				...finallyRecord.copyRoots,
				finallyRecord.catchTrailer?.start,
				record.catchAddress,
			]
		) {
			if (entry == null) continue;
			const blocks = this.#linearFinalizerBlocks(
				entry,
				finallyRecord.isReturnOverride,
			);
			if (blocks != null) return blocks;
		}
		if (record.catchBody != null && record.catchBody.size > 0) {
			return [...record.catchBody].toSorted((left, right) =>
				left - right
			);
		}
		return null;
	}

	#preferredFinallyBodyBlocks(
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
	): BlockAddr[] | null {
		const recoveredBody = this.#recoveredFinalizerBodyBlocks(
			record.catchAddress,
		);
		if (finallyRecord.bodyBlocks != null) {
			return uniqueBlocks([
				...finallyRecord.bodyBlocks,
				...recoveredBody,
			]);
		}
		if (recoveredBody.length > 0) {
			return recoveredBody;
		}
		if (
			finallyRecord.catchTrailer?.start != null &&
			this.#isCatchRethrowBlock(record.catchAddress)
		) {
			const trailerBlocks = this.#linearFinalizerBlocks(
				finallyRecord.catchTrailer.start,
				finallyRecord.isReturnOverride,
			);
			if (trailerBlocks != null) return trailerBlocks;
		}
		return null;
	}

	#recoveredFinalizerBodyBlocks(owner: BlockAddr): BlockAddr[] {
		return [...this.#func.blocks.values()].filter((block) =>
			block.recoveredFinalizerOwner === owner &&
			(
				block.recoveredFinalizerRole === 'canonical' ||
				block.recoveredFinalizerRole === 'continuation'
			)
		).map((block) => block.address).toSorted((left, right) => left - right);
	}

	#isCatchRethrowBlock(addr: BlockAddr): boolean {
		const block = this.#func.blocks.get(addr);
		if (!block) return false;
		const statements = block.body as t.Statement[];
		if (!statements.some(isCatchPreludeStatement)) return false;
		return t.isThrowStatement(statements.at(-1));
	}

	#matchedCanonicalFinalizerBlocks(
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
	): BlockAddr[] | null {
		const canonicalBlocks =
			this.#preferredFinallyBodyBlocks(record, finallyRecord) ??
				this.#linearFinalizerBlocks(
					record.catchAddress,
					finallyRecord.isReturnOverride,
				);
		if (canonicalBlocks == null) return null;
		const canonicalTrace = this.#traceBlocks(canonicalBlocks);
		if (canonicalTrace == null) return null;

		for (
			const entry of [
				...finallyRecord.copyRoots,
				finallyRecord.catchTrailer?.start,
			]
		) {
			if (entry == null) continue;
			const copyBlocks = this.#linearFinalizerBlocks(
				entry,
				finallyRecord.isReturnOverride,
			);
			if (copyBlocks == null) continue;
			const copyTrace = this.#traceBlocks(copyBlocks);
			if (copyTrace == null) continue;
			if (traceMatchesPrefix(canonicalTrace, copyTrace)) {
				return canonicalBlocks;
			}
		}
		return canonicalBlocks;
	}

	#traceBlocks(blocks: BlockAddr[]) {
		const result = [];
		for (const address of blocks) {
			const block = this.#func.blocks.get(address);
			if (!block) return null;
			result.push({
				address,
				body: block.body as readonly t.Statement[],
			});
		}
		return result;
	}

	#linearFinalizerBlocks(
		entry: BlockAddr,
		isReturnOverride: boolean,
	): BlockAddr[] | null {
		const result: BlockAddr[] = [];
		const visited = new AddressSet<BlockAddr>();
		let cursor: BlockAddr | undefined = entry;
		while (cursor != null) {
			if (visited.has(cursor)) return null;
			visited.add(cursor);
			const block = this.#func.blocks.get(cursor);
			if (!block) return null;
			result.push(cursor);
			if (block.consequentAddresses.length === 0) break;
			if (block.consequentAddresses.length !== 1) break;
			const [next] = block.consequentAddresses;
			if (this.#records.has(next)) break;
			if (this.#func.predecessorsOf(next).size !== 1) break;
			cursor = next;
		}
		if (!isReturnOverride && result.length > 0) {
			const last = this.#func.blocks.get(result.at(-1)!);
			if (
				last?.consequentAddresses.length === 0 &&
				t.isReturnStatement(last.body.at(-1) as t.Statement | undefined)
			) {
				result.pop();
			}
		}
		return result.length === 0 ? null : result;
	}

	#finallyCopies(
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
	): HandlerGraphFinallyCopyDescriptor[] {
		const copies: HandlerGraphFinallyCopyDescriptor[] = [];
		for (
			const copyRoot of this.#finallyCopyRootsForDescriptor(
				record,
				finallyRecord,
			)
		) {
			const copyBlocks = this.#linearFinalizerBlocks(
				copyRoot,
				finallyRecord.isReturnOverride,
			);
			const kind = copyRoot === finallyRecord.catchTrailer?.start
				? 'catchTrailer'
				: this.#isNormalFinallyCopyRoot(record, copyRoot)
				? 'normalExit'
				: 'abruptExit';
			const skipRanges = kind === 'normalExit' && copyBlocks != null
				? this.#normalCopyPrefixSkipRanges(
					record,
					finallyRecord,
					copyBlocks,
				)
				: undefined;
			copies.push({
				canonical: record.catchAddress,
				copyRoot,
				next: copyBlocks == null
					? this.#singleSuccessor(copyRoot)
					: this.#copySuccessor(copyBlocks),
				kind,
				skipRanges,
			});
		}
		return copies;
	}

	#normalCopyPrefixSkipRanges(
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
		copyBlocks: BlockAddr[],
	): HandlerGraphStatementRange[] | undefined {
		const canonicalTrace = this.#canonicalFinallyTrace(
			record,
			finallyRecord,
		);
		const copyTrace = this.#traceBlocks(copyBlocks);
		if (canonicalTrace == null || copyTrace == null) return undefined;
		const prefixLength = tracePrefixLength(canonicalTrace, copyTrace);
		if (prefixLength === 0) return undefined;
		return copyPrefixSkipRanges(copyTrace, prefixLength);
	}

	#finallyCopyRootsForDescriptor(
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
	): AddressSet<BlockAddr> {
		const copyRoots = new AddressSet<BlockAddr>(finallyRecord.copyRoots);
		if (finallyRecord.catchTrailer?.start != null) {
			copyRoots.add(finallyRecord.catchTrailer.start);
		}

		const canonicalTrace = this.#canonicalFinallyTrace(
			record,
			finallyRecord,
		);
		const templates = [
			record.catchAddress,
			...finallyRecord.copyRoots,
			finallyRecord.catchTrailer?.start,
		].filter((addr): addr is BlockAddr => addr != null);
		for (const block of record.protectedBlocks) {
			for (
				const successor of this.#func.blocks.get(block)
					?.consequentAddresses ?? []
			) {
				if (record.protectedBlocks.has(successor)) continue;
				if (copyRoots.has(successor)) continue;
				if (!this.#func.blocks.has(successor)) continue;
				if (this.#records.has(successor)) continue;
				if (
					this.#matchesFinallyCopyRoot(
						successor,
						canonicalTrace,
						templates,
						finallyRecord.isReturnOverride,
					)
				) {
					copyRoots.add(successor);
				}
			}
		}
		return copyRoots;
	}

	#enclosingFinallyCopyRoots(
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
	): HandlerGraphEnclosingFinallyCopyDescriptor[] {
		const result: HandlerGraphEnclosingFinallyCopyDescriptor[] = [];
		const roots = this.#finallyCopyRootsForDescriptor(
			record,
			finallyRecord,
		);
		for (const [owner, ownerRecord] of this.#records) {
			if (owner === record.catchAddress) continue;
			const ownerFinally = this.#finallyRecords.get(owner);
			if (!ownerFinally) continue;
			if (!ownerRecord.protectedBlocks.has(record.catchAddress)) {
				continue;
			}
			for (const copyRoot of roots) {
				if (
					(
						ownerRecord.protectedBlocks.has(copyRoot) &&
						!record.protectedBlocks.has(copyRoot) &&
						!this.#copyRootMatchesFinallyBody(
							copyRoot,
							record,
							finallyRecord,
						)
					) ||
					this.#copyRootMatchesFinallyBody(
						copyRoot,
						ownerRecord,
						ownerFinally,
					)
				) {
					result.push({
						owner,
						copyRoot,
						tailRoot: this.#firstBlockOutsideProtection(
							copyRoot,
							ownerRecord.protectedBlocks,
						),
					});
				}
			}
		}
		return result.toSorted((left, right) =>
			left.owner - right.owner || left.copyRoot - right.copyRoot
		);
	}

	#firstBlockOutsideProtection(
		entry: BlockAddr,
		protectedBlocks: AddressSet<BlockAddr>,
	): BlockAddr {
		const seen = new AddressSet<BlockAddr>();
		let cursor = entry;
		while (protectedBlocks.has(cursor) && !seen.has(cursor)) {
			seen.add(cursor);
			const successors = this.#func.blocks.get(cursor)
				?.consequentAddresses;
			if (successors?.length !== 1) break;
			cursor = successors[0];
		}
		return cursor;
	}

	#copyRootMatchesFinallyBody(
		copyRoot: BlockAddr,
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
	): boolean {
		if (
			compareFinallyCopies(
				this.#func,
				record.catchAddress,
				copyRoot,
			) ||
			compareFinallyCopyPrefix(
				this.#func,
				record.catchAddress,
				copyRoot,
			) ||
			compareFinallyCopySuffixPrefix(
				this.#func,
				record.catchAddress,
				copyRoot,
			)
		) return true;
		const copyFingerprint = this.#firstEffectiveBlockFingerprint(copyRoot);
		if (copyFingerprint == null) return false;
		for (
			const entry of [
				...(finallyRecord.bodyBlocks ?? []),
				record.catchAddress,
				...finallyRecord.copyRoots,
				finallyRecord.catchTrailer?.start,
			]
		) {
			if (entry == null) continue;
			if (
				this.#firstEffectiveBlockFingerprint(entry) === copyFingerprint
			) {
				return true;
			}
		}
		return false;
	}

	#firstEffectiveBlockFingerprint(blockAddress: BlockAddr): string | null {
		const block = this.#func.blocks.get(blockAddress);
		if (!block) return null;
		for (const statement of block.body as t.Statement[]) {
			if (this.#isCatchIntrinsicDeclaration(statement)) continue;
			return statementFingerprint(statement);
		}
		return null;
	}

	#canonicalFinallyTrace(
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
	) {
		const canonicalBlocks = this.#canonicalFinallyBlocks(
			record,
			finallyRecord,
		);
		if (canonicalBlocks == null) return null;
		return this.#traceBlocks(canonicalBlocks);
	}

	#canonicalFinallyBlocks(
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
	): BlockAddr[] | null {
		const preferred = this.#preferredFinallyBodyBlocks(
			record,
			finallyRecord,
		);
		if (preferred != null && preferred.length > 0) return preferred;
		return this.#linearFinalizerBlocks(
			record.catchAddress,
			finallyRecord.isReturnOverride,
		);
	}

	#matchesFinallyCopyRoot(
		successor: BlockAddr,
		canonicalTrace: TraceBlock[] | null,
		templates: BlockAddr[],
		isReturnOverride: boolean,
	): boolean {
		const candidateBlocks = this.#linearFinalizerBlocks(
			successor,
			isReturnOverride,
		);
		const candidateTrace = candidateBlocks == null
			? null
			: this.#traceBlocks(candidateBlocks);
		if (canonicalTrace != null && candidateTrace != null) {
			const prefixLength = tracePrefixLength(
				canonicalTrace,
				candidateTrace,
			);
			if (prefixLength > 0) return true;
		}
		return templates.some((template) =>
			compareFinallyCopies(this.#func, template, successor) ||
			compareFinallyCopyPrefix(this.#func, template, successor) ||
			compareFinallyCopySuffixPrefix(this.#func, template, successor)
		);
	}

	#isCatchIntrinsicDeclaration(statement: t.Statement): boolean {
		if (
			t.isExpressionStatement(statement) &&
			t.isCallExpression(statement.expression) &&
			t.isV8IntrinsicIdentifier(statement.expression.callee, {
				name: 'Catch',
			})
		) return true;
		if (!t.isVariableDeclaration(statement)) return false;
		return statement.declarations.some((declaration) =>
			t.isCallExpression(declaration.init) &&
			t.isV8IntrinsicIdentifier(declaration.init.callee, {
				name: 'Catch',
			})
		);
	}

	#isNormalFinallyCopyRoot(
		record: HandlerRecord,
		copyRoot: BlockAddr,
	): boolean {
		const block = this.#func.blocks.get(copyRoot);
		if (!block || block.consequentAddresses.length !== 1) return false;
		const lastStatement = block.body.at(-1) as t.Statement | undefined;
		if (
			t.isReturnStatement(lastStatement) ||
			t.isThrowStatement(lastStatement)
		) {
			return false;
		}

		let protectedPredecessors = 0;
		for (const predecessor of this.#func.cfgPredecessorsOf(copyRoot)) {
			if (record.protectedBlocks.has(predecessor)) {
				protectedPredecessors++;
			}
		}
		return protectedPredecessors > 0;
	}

	#finallyCopySuffixes(
		record: HandlerRecord,
		finallyRecord: FinallyRecord,
	): HandlerGraphFinallyCopySuffixDescriptor[] {
		const canonicalBlocks = this.#linearFinalizerBlocks(
			record.catchAddress,
			finallyRecord.isReturnOverride,
		);
		if (canonicalBlocks == null) return [];
		const canonicalTrace = this.#traceBlocks(canonicalBlocks);
		if (canonicalTrace == null) return [];
		const ownerBlock = canonicalBlocks.at(-1);
		if (ownerBlock == null) return [];

		const suffixes: HandlerGraphFinallyCopySuffixDescriptor[] = [];
		for (
			const copyRoot of [
				...finallyRecord.copyRoots,
				finallyRecord.catchTrailer?.start,
			]
		) {
			if (copyRoot == null) continue;
			const copyBlocks = this.#linearFinalizerBlocks(
				copyRoot,
				finallyRecord.isReturnOverride,
			);
			if (copyBlocks == null) continue;
			const copyTrace = this.#traceBlocks(copyBlocks);
			if (copyTrace == null) continue;
			const prefixLength = tracePrefixLength(canonicalTrace, copyTrace);
			if (prefixLength === 0) continue;
			const flattened = copyTrace.flatMap((block) =>
				block.body.map((stmt) => ({
					block: block.address,
					statement: stmt,
				}))
			);
			const suffixStatements = flattened.slice(prefixLength).map((
				entry,
			) => t.cloneNode(entry.statement, true));
			if (suffixStatements.length === 0) continue;
			suffixes.push({
				canonical: record.catchAddress,
				copyRoot,
				ownerBlock,
				next: this.#copySuccessor(copyBlocks),
				kind: copyRoot === finallyRecord.catchTrailer?.start
					? 'catchTrailer'
					: 'abruptExitTrailer',
				statements: suffixStatements,
				skipRanges: copySuffixSkipRanges(copyTrace, prefixLength),
			});
		}
		for (
			const embedded of this.#embeddedFinalizerSuffixes(
				record,
				canonicalTrace,
			)
		) {
			suffixes.push(embedded);
		}
		return suffixes;
	}

	#embeddedFinalizerSuffixes(
		record: HandlerRecord,
		canonicalTrace: TraceBlock[],
	): HandlerGraphFinallyCopySuffixDescriptor[] {
		const canonicalFingerprints = traceFingerprints(canonicalTrace);
		const suffixes: HandlerGraphFinallyCopySuffixDescriptor[] = [];
		const seen = new Set<string>();
		const canonicalBlocks = new AddressSet(
			canonicalTrace.map((block) => block.address),
		);
		const maxSuffixLength = Math.min(8, canonicalFingerprints.length);
		for (let length = maxSuffixLength; length >= 2; length--) {
			const suffix = canonicalFingerprints.slice(
				canonicalFingerprints.length - length,
			);
			for (const block of this.#func.blocks.values()) {
				if (canonicalBlocks.has(block.address)) continue;
				if (block.body.length < length) continue;
				const blockFingerprints = (block.body as t.Statement[]).map(
					statementFingerprint,
				);
				const start = kmpSearch(
					blockFingerprints,
					suffix,
					(left, right) => left === right,
				);
				if (start < 0) continue;
				const end = start + length;
				const key = `${block.address}:${start}:${end}`;
				if (seen.has(key)) continue;
				seen.add(key);
				const expandedStart = expandSkipStartForDependencies(
					block.body as t.Statement[],
					start,
					end,
				);
				const statements = (block.body.slice(
					expandedStart,
					end,
				) as t.Statement[])
					.map((stmt) => t.cloneNode(stmt, true));
				suffixes.push({
					canonical: record.catchAddress,
					copyRoot: block.address,
					ownerBlock: canonicalTrace.at(-1)?.address ??
						record.catchAddress,
					next: this.#singleSuccessor(block.address),
					kind: 'abruptExitTrailer',
					statements,
					skipRanges: [{
						block: block.address,
						start: expandedStart,
						end,
					}],
				});
			}
		}
		return suffixes;
	}

	#singleSuccessor(block: BlockAddr): BlockAddr | null {
		const source = this.#func.blocks.get(block);
		if (!source || source.consequentAddresses.length !== 1) return null;
		return source.consequentAddresses[0];
	}

	#copySuccessor(blocks: BlockAddr[]): BlockAddr | null {
		const last = this.#func.blocks.get(blocks.at(-1)!);
		if (!last || last.consequentAddresses.length !== 1) return null;
		return last.consequentAddresses[0];
	}

	snapshot(): HandlerGraphSnapshot {
		return {
			records: [...this.#records].map(([addr, record]) => [
				addr,
				{
					catchAddress: record.catchAddress,
					innerTryRecords: [...record.innerTryRecords],
					ranges: record.ranges.map((range) => ({
						index: range.index,
						start: range.start,
						end: range.end,
						protectedBlocks: [...range.protectedBlocks],
					})),
					directProtectedBlocks: record.directProtectedBlocks == null
						? null
						: [...record.directProtectedBlocks],
					catchBody: record.catchBody == null
						? null
						: [...record.catchBody],
					canonicalFinallyAddress: record.canonicalFinallyAddress,
				},
			]),
			protectedEntries: [...this.#protectedEntries],
			finallyRecords: [...this.#finallyRecords].map(([addr, record]) => [
				addr,
				{
					canonicalFinallyAddress: record.canonicalFinallyAddress,
					catchTrailer: record.catchTrailer == null
						? null
						: { ...record.catchTrailer },
					copyRoots: [...record.copyRoots],
					bodyBlocks: record.bodyBlocks == null
						? null
						: [...record.bodyBlocks],
					bodyBlockStatementLimits: [
						...record.bodyBlockStatementLimits,
					],
					isReturnOverride: record.isReturnOverride,
				},
			]),
		};
	}

	static fromSnapshot(
		func: IRFunction,
		snapshot: HandlerGraphSnapshot,
	): HandlerGraph {
		const graph = new HandlerGraph(func);
		graph.#records = new AddressMap<HandlerRecord, number>();
		graph.#protectedEntries = new AddressSet(snapshot.protectedEntries);
		graph.#finallyRecords = new AddressMap<FinallyRecord>();

		for (const [addr, recordSnapshot] of snapshot.records) {
			const record = new HandlerRecord(recordSnapshot.catchAddress);
			record.innerTryRecords = new AddressSet(
				recordSnapshot.innerTryRecords,
			);
			record.ranges = recordSnapshot.ranges.map((rangeSnapshot) => {
				const range = new ExceptionRange(rangeSnapshot.index, {
					tryStart: rangeSnapshot.start,
					tryEnd: rangeSnapshot.end,
					catchOffset: recordSnapshot.catchAddress,
				});
				range.protectedBlocks = new AddressSet(
					rangeSnapshot.protectedBlocks,
				);
				return range;
			});
			record.directProtectedBlocks =
				recordSnapshot.directProtectedBlocks == null
					? null
					: new AddressSet(recordSnapshot.directProtectedBlocks);
			record.catchBody = recordSnapshot.catchBody == null
				? null
				: new AddressSet(recordSnapshot.catchBody);
			record.canonicalFinallyAddress =
				recordSnapshot.canonicalFinallyAddress;
			graph.#records.set(addr, record);
		}

		for (const [addr, finallySnapshot] of snapshot.finallyRecords) {
			const record = new FinallyRecord(
				finallySnapshot.canonicalFinallyAddress,
			);
			record.catchTrailer = finallySnapshot.catchTrailer == null
				? null
				: { ...finallySnapshot.catchTrailer };
			record.copyRoots = new AddressSet(finallySnapshot.copyRoots);
			record.bodyBlocks = finallySnapshot.bodyBlocks == null
				? null
				: [...finallySnapshot.bodyBlocks];
			record.bodyBlockStatementLimits = new Map(
				finallySnapshot.bodyBlockStatementLimits,
			);
			record.isReturnOverride = finallySnapshot.isReturnOverride;
			graph.#finallyRecords.set(addr, record);
		}

		graph.#rebuildRangeToHandlers();
		graph.#rebuildDominance();
		return graph;
	}

	isProtectedEntry(address: BlockAddr): boolean {
		return this.#protectedEntries.has(address);
	}

	addDirectRecord(
		catchAddress: BlockAddr,
		protectedBlocks: Iterable<BlockAddr>,
		entryBlocks?: Iterable<BlockAddr>,
	): HandlerRecord {
		let record = this.#records.get(catchAddress);
		const isNew = record == null;
		if (isNew) {
			record = new HandlerRecord(catchAddress);
			record.directProtectedBlocks = new AddressSet();
			this.#records.set(catchAddress, record);
		}
		const handlerRecord = record!;
		if (handlerRecord.directProtectedBlocks == null) {
			handlerRecord.directProtectedBlocks = new AddressSet();
		}
		for (const addr of protectedBlocks) {
			handlerRecord.directProtectedBlocks.add(addr);
		}
		if (entryBlocks) {
			for (const addr of entryBlocks) this.#protectedEntries.add(addr);
		}
		if (isNew) {
			const firstProtected =
				handlerRecord.directProtectedBlocks.values().next()
					.value ?? 0;
			this.#func._exceptionHandlers.push({
				tryStart: firstProtected,
				tryEnd: firstProtected + 1,
				catchOffset: catchAddress,
			});
		}
		this.#rebuildDominance();
		return handlerRecord;
	}

	notifyBlocksMerged(parentAddr: BlockAddr, childAddr: BlockAddr) {
		let changed = false;
		for (const handler of this.#func._exceptionHandlers) {
			if (handler.tryStart === childAddr) {
				handler.tryStart = parentAddr;
				handler.tryEnd = parentAddr + 1;
				changed = true;
			}
		}
		if (this.#protectedEntries.has(childAddr)) {
			this.#protectedEntries.delete(childAddr);
			this.#protectedEntries.add(parentAddr);
		}
		if (changed) this.#rebuildDominance();
	}

	liveHandlers(): AddressSet<HandlerId> {
		if (this.#func.blocks.size === 0) {
			return new AddressSet(this.#records.keys());
		}
		return new AddressSet(
			[...this.#records.keys()].filter((addr) =>
				this.#func.blocks.has(addr)
			),
		);
	}

	removeHandlers(handlers: Iterable<HandlerId>) {
		const removed = new AddressSet(handlers);
		if (removed.size === 0) return;
		for (const handler of removed) {
			this.#records.delete(handler);
			this.#finallyRecords.delete(handler);
		}
		for (const [, record] of this.#records) {
			if (
				record.canonicalFinallyAddress != null &&
				removed.has(record.canonicalFinallyAddress)
			) {
				record.canonicalFinallyAddress = null;
			}
		}
		this.#rebuildDominance();
		this.#func._exceptionHandlers = this.#func._exceptionHandlers.filter(
			({ catchOffset }) => !removed.has(catchOffset),
		);
	}

	removeStructuredCatchHandler(catchAddress: HandlerId) {
		this.removeHandlers([catchAddress]);
	}

	removeStructuredFinallyHandler(finallyAddress: FinallyId) {
		this.removeHandlers([finallyAddress]);
	}

	removeStructuredTryCatchFinallyHandlers(
		catchAddress: HandlerId,
		finallyAddress: FinallyId,
	) {
		this.removeHandlers([catchAddress, finallyAddress]);
	}

	isCatchTarget(address: BlockAddr): boolean {
		return this.#records.has(address);
	}

	activeHandlersAtBlock(
		address: BlockAddr,
		options: {
			exclude?: Iterable<HandlerId>;
			liveHandlers?: ReadonlySet<HandlerId>;
		} = {},
	): AddressSet<HandlerId> {
		const excluded = new AddressSet(options.exclude ?? []);
		const liveHandlers = options.liveHandlers ?? this.liveHandlers();
		const handlers = new AddressSet<HandlerId>();
		const merged = this.#func.mergedBlocks.get(address);
		const sourceAddresses = merged != null && merged.size > 0
			? merged
			: new AddressSet([address]);
		for (const [catchAddress, record] of this.#records) {
			if (excluded.has(catchAddress)) continue;
			if (!liveHandlers.has(catchAddress)) continue;
			for (const sourceAddress of sourceAddresses) {
				if (!record.isProtectingBlock(sourceAddress)) continue;
				handlers.add(catchAddress);
				break;
			}
		}
		return handlers;
	}

	activeHandlersEqual(
		left: BlockAddr,
		right: BlockAddr,
		options: {
			exclude?: Iterable<HandlerId>;
			liveHandlers?: ReadonlySet<HandlerId>;
		} = {},
	): boolean {
		return this.activeHandlersAtBlock(left, options).equals(
			this.activeHandlersAtBlock(right, options),
		);
	}

	activeHandlersParent(
		parent: BlockAddr | ReadonlySet<HandlerId>,
		child: BlockAddr,
		options: {
			exclude?: Iterable<HandlerId>;
			liveHandlers?: ReadonlySet<HandlerId>;
		} = {},
	): boolean {
		const parentHandlers = typeof parent === 'number'
			? this.activeHandlersAtBlock(parent, options)
			: parent;
		const childHandlers = this.activeHandlersAtBlock(child, options);
		return [...childHandlers].every((handler) =>
			parentHandlers.has(handler)
		);
	}

	catchMapForBlocks(
		addresses: Iterable<BlockAddr> = this.#func.blocks.keys(),
		options: {
			liveHandlers?: ReadonlySet<HandlerId>;
		} = {},
	): AddressGraph<HandlerId, BlockAddr> {
		const graph = new AddressGraph<HandlerId, BlockAddr>();
		const liveHandlers = options.liveHandlers ?? this.liveHandlers();
		for (const addr of addresses) {
			// Check the current address AND all original source addresses that have been
			// merged into this block. The current block can contain statements from
			// multiple protected source ranges, so mergedBlocks is the source of truth
			// for handler coverage after CFG reductions.
			const merged = this.#func.mergedBlocks.get(addr);
			const sourceAddresses = merged != null && merged.size > 0
				? merged
				: new AddressSet([addr]);
			const handlers = new AddressSet<HandlerId>();
			for (const srcAddr of sourceAddresses) {
				for (
					const catchAddress of this.activeHandlersAtBlock(srcAddr, {
						liveHandlers,
					})
				) {
					handlers.add(catchAddress);
				}
			}
			for (const catchAddress of handlers) {
				graph.addEdge(catchAddress, addr);
			}
		}
		return graph;
	}

	hasLiveOwningCatchForFinally(
		finallyAddress: FinallyId,
		liveHandlers: ReadonlySet<HandlerId>,
	): boolean {
		for (const [catchAddress, record] of this.#records) {
			if (!liveHandlers.has(catchAddress)) continue;
			if (record.canonicalFinallyAddress === finallyAddress) return true;
		}
		return false;
	}

	isNestedWithin(child: HandlerId, parent: HandlerId): boolean {
		return this.#strictDominatorMap.get(child)?.has(parent) === true;
	}

	liveNestedHandlersAtBlock(
		address: BlockAddr,
		parent: HandlerId,
		liveHandlers: ReadonlySet<HandlerId>,
	): AddressSet<HandlerId> {
		const nested = new AddressSet<HandlerId>();
		for (
			const catchAddress of this.activeHandlersAtBlock(address, {
				liveHandlers,
			})
		) {
			if (catchAddress === parent) continue;
			if (this.isNestedWithin(catchAddress, parent)) {
				nested.add(catchAddress);
			}
		}
		return nested;
	}

	static #isStrictDominator(
		dominator: HandlerRecord,
		dominated: HandlerRecord,
	) {
		if (dominator.catchAddress === dominated.catchAddress) return false;

		// For direct block-set records the protected set never includes catch block
		// addresses, so fall back to a pure subset check: A strictly dominates B iff
		// B's protected blocks are a non-equal subset of A's protected blocks.
		if (dominator.directProtectedBlocks != null) {
			const dominatedBlocks = dominated.protectedBlocks;
			const dominatorBlocks = dominator.protectedBlocks;
			return dominatedBlocks.size < dominatorBlocks.size &&
				dominatedBlocks.isSubsetOf(dominatorBlocks);
		}
		if (!dominator.isProtectingBlock(dominated.catchAddress)) return false;
		if (!dominated.protectedBlocks.isSubsetOf(dominator.protectedBlocks)) {
			return false;
		}
		return true;
	}

	#rebuildDominance() {
		this.#strictDominatorMap = new AddressGraph<HandlerId, HandlerId>();
		this.#strictDominanceMap = new AddressGraph<HandlerId, HandlerId>();

		for (const [catchAddress, record] of this.#records) {
			const dominators = new AddressSet(
				this.#records.values().filter((candidate) =>
					HandlerGraph.#isStrictDominator(candidate, record)
				).map((candidate) => candidate.catchAddress),
			);
			this.#strictDominatorMap.set(catchAddress, dominators);
		}

		for (const [key, value] of this.#strictDominatorMap) {
			for (const v of value) {
				this.#strictDominanceMap.addEdge(v, key);
			}
		}

		this.#rebuildDominatorTree();
	}

	#rebuildRangeToHandlers() {
		this.#rangeToHandlers = new AddressMap<AddressGraph>();
		for (const [catchAddress, record] of this.#records) {
			for (const range of record.ranges) {
				this.#rangeToHandlers.getWithDefault(
					range.start,
					() => new AddressGraph(),
				).addEdge(range.end, catchAddress);
			}
		}
	}

	#rebuildDominatorTree() {
		this.#dominatorTree = new AddressGraph<HandlerId, HandlerId>();
		for (const addr of this.#records.keys()) {
			this.#dominatorTree.set(addr, new AddressSet());
		}
		for (const [block, strictlyDominated] of this.#strictDominanceMap) {
			const indirectlyDominated = new AddressSet(
				Array.from(strictlyDominated).flatMap((child) => [
					...(this.#strictDominanceMap.get(child) ?? []),
				]),
			);
			this.#dominatorTree.set(
				block,
				strictlyDominated.difference(indirectlyDominated),
			);
		}
	}
}

function descriptorContainsDescriptor(
	parent: HandlerGraphRegionDescriptor,
	child: HandlerGraphRegionDescriptor,
): boolean {
	if (parent.handler === child.handler) return false;
	for (const block of child.protectedBlocks) {
		if (!parent.protectedBlocks.has(block)) return false;
	}
	if (parent.protectedBlocks.has(child.handler)) return true;
	if (child.kind === 'finally') {
		for (const block of child.finallyBodyBlocks ?? []) {
			if (parent.protectedBlocks.has(block)) return true;
		}
		for (const root of child.finallyCopyRoots) {
			if (parent.protectedBlocks.has(root)) return true;
		}
	}
	return false;
}

function sortForestNodes(nodes: HandlerGraphRegionForestNode[]) {
	nodes.sort((left, right) =>
		left.descriptor.protectedBlocks.size -
			right.descriptor.protectedBlocks.size ||
		left.descriptor.handler - right.descriptor.handler
	);
	for (const node of nodes) sortForestNodes(node.children);
}

function uniqueBlocks(blocks: Iterable<BlockAddr>): BlockAddr[] {
	return [...new Set(blocks)];
}

function copySuffixSkipRanges(
	trace: TraceBlock[],
	prefixLength: number,
): HandlerGraphStatementRange[] {
	const ranges: HandlerGraphStatementRange[] = [];
	let cursor = 0;
	for (const block of trace) {
		const start = Math.max(prefixLength - cursor, 0);
		const end = block.body.length;
		if (start < end) {
			ranges.push({ block: block.address, start, end });
		}
		cursor += block.body.length;
	}
	return ranges;
}

function copyPrefixSkipRanges(
	trace: TraceBlock[],
	prefixLength: number,
): HandlerGraphStatementRange[] {
	const ranges: HandlerGraphStatementRange[] = [];
	let cursor = 0;
	for (const block of trace) {
		const end = Math.min(prefixLength - cursor, block.body.length);
		if (end > 0) {
			ranges.push({ block: block.address, start: 0, end });
		}
		cursor += block.body.length;
		if (cursor >= prefixLength) break;
	}
	return ranges;
}

function expandSkipStartForDependencies(
	statements: t.Statement[],
	start: number,
	end: number = statements.length,
): number {
	const needed = referencedIdentifiers(statements.slice(start, end));
	let expanded = start;
	for (let index = start - 1; index >= 0; index--) {
		const declared = declarationIdentifier(statements[index]);
		if (!declared || !needed.has(declared)) continue;
		expanded = index;
		for (const name of referencedIdentifiers([statements[index]])) {
			if (name !== declared) needed.add(name);
		}
	}
	return expanded;
}

function declarationIdentifier(statement: t.Statement): string | null {
	if (!t.isVariableDeclaration(statement)) return null;
	if (statement.declarations.length !== 1) return null;
	const declaration = statement.declarations[0];
	return t.isIdentifier(declaration.id) ? declaration.id.name : null;
}

function referencedIdentifiers(statements: t.Statement[]): Set<string> {
	const names = new Set<string>();
	for (const statement of statements) {
		t.traverseFast(statement, (node) => {
			if (!t.isIdentifier(node)) return;
			names.add(node.name);
		});
	}
	for (const statement of statements) {
		const declared = declarationIdentifier(statement);
		if (declared) names.delete(declared);
	}
	return names;
}

export interface FinallyRange {
	start: BlockAddr;
	end: BlockAddr | null;
}

export type FinallyId = BlockAddr;
export class FinallyRecord {
	canonicalFinallyAddress: BlockAddr; // also finallyId

	catchTrailer: FinallyRange | null = null;
	copyRoots = new AddressSet();
	bodyBlocks: BlockAddr[] | null = null;
	bodyBlockStatementLimits = new Map<BlockAddr, number>();

	// True when the finally block has an explicit `return` (return-override termination).
	// The canonical finally block ends with Ret instead of Throw in this case.
	isReturnOverride = false;

	constructor(address: BlockAddr) {
		this.canonicalFinallyAddress = address;
	}
}

export interface FinallyRecordSnapshot {
	canonicalFinallyAddress: BlockAddr;
	catchTrailer: FinallyRange | null;
	copyRoots: BlockAddr[];
	bodyBlocks: BlockAddr[] | null;
	bodyBlockStatementLimits: [BlockAddr, number][];
	isReturnOverride: boolean;
}

export interface HandlerGraphRegionDescriptor {
	handler: BlockAddr;
	kind: 'catch' | 'finally';
	protectedBlocks: AddressSet<BlockAddr>;
	protectedEntries: AddressSet<BlockAddr>;
	catchBody: AddressSet<BlockAddr> | null;
	canonicalFinallyAddress: FinallyId | null;
	canonicalFinallyOwnership: HandlerGraphFinallyOwnershipProof | null;
	finallyCopyRoots: AddressSet<BlockAddr>;
	finallyBodyBlocks: BlockAddr[] | null;
	finallyCopies: HandlerGraphFinallyCopyDescriptor[];
	finallyCopySuffixes: HandlerGraphFinallyCopySuffixDescriptor[];
	enclosingFinallyCopyRoots: HandlerGraphEnclosingFinallyCopyDescriptor[];
}

export interface HandlerGraphRegionForest {
	roots: HandlerGraphRegionForestNode[];
	nodeByHandler: AddressMap<HandlerGraphRegionForestNode>;
	parentByHandler: AddressMap<BlockAddr>;
}

export interface HandlerGraphRegionForestNode {
	descriptor: HandlerGraphRegionDescriptor;
	children: HandlerGraphRegionForestNode[];
}

export interface HandlerGraphFinallyCopyDescriptor {
	canonical: BlockAddr;
	copyRoot: BlockAddr;
	next: BlockAddr | null;
	kind: 'normalExit' | 'abruptExit' | 'catchTrailer';
	skipRanges?: HandlerGraphStatementRange[];
}

export interface HandlerGraphEnclosingFinallyCopyDescriptor {
	owner: BlockAddr;
	copyRoot: BlockAddr;
	tailRoot: BlockAddr;
}

export interface HandlerGraphFinallyCopySuffixDescriptor {
	canonical: BlockAddr;
	copyRoot: BlockAddr;
	ownerBlock: BlockAddr;
	next: BlockAddr | null;
	kind: 'tryTrailer' | 'catchTrailer' | 'abruptExitTrailer' | 'canonical';
	statements: t.Statement[];
	skipRanges?: HandlerGraphStatementRange[];
}

export interface HandlerGraphStatementRange {
	block: BlockAddr;
	start: number;
	end: number;
}

export interface HandlerGraphEmbeddedFinalizerAction {
	owner: BlockAddr;
	copyRoot: BlockAddr;
	kind: 'catchTrailer';
	replacementFingerprints: string[];
	terminalSuffixFingerprints: string[][];
	maySuspend: boolean;
}

export interface HandlerGraphFinalizerCleanupPlan {
	removeRanges: HandlerGraphStatementRange[];
	replaceWithReturnRanges: HandlerGraphStatementRange[];
	embeddedCatchActions: HandlerGraphEmbeddedFinalizerAction[];
	enclosingEdgeActionCount: number;
}

export interface HandlerGraphFinalizerEdgeAction {
	handler: BlockAddr;
	edge: {
		from: BlockAddr;
		to: BlockAddr;
		kind: 'normal' | 'exceptional';
	};
	canonical: BlockAddr;
	copyRoot: BlockAddr;
	ownerBlock: BlockAddr;
	next: BlockAddr | null;
	kind:
		| 'canonical'
		| 'normal-copy'
		| 'catch-copy'
		| 'abrupt-copy'
		| 'enclosing-copy';
	completion: 'normal' | 'return' | 'throw' | 'break-or-continue';
	statements: t.Statement[];
	skipRanges: HandlerGraphStatementRange[];
	depth: number;
}

function finalizerCompletion(
	statements: readonly t.Statement[],
	abrupt: boolean,
): HandlerGraphFinalizerEdgeAction['completion'] {
	const terminal = statements.at(-1);
	if (t.isReturnStatement(terminal)) return 'return';
	if (t.isThrowStatement(terminal)) return 'throw';
	return abrupt ? 'break-or-continue' : 'normal';
}

function uniqueFinalizerEdgeActions(
	actions: HandlerGraphFinalizerEdgeAction[],
): HandlerGraphFinalizerEdgeAction[] {
	const unique = new Map<string, HandlerGraphFinalizerEdgeAction>();
	for (const action of actions) {
		const key = [
			action.handler,
			action.edge.kind,
			action.edge.from,
			action.edge.to,
			action.copyRoot,
			action.kind,
		].join(':');
		unique.set(key, action);
	}
	return [...unique.values()];
}

export interface HandlerGraphSnapshot {
	records: [HandlerId, HandlerRecordSnapshot][];
	protectedEntries: BlockAddr[];
	finallyRecords: [FinallyId, FinallyRecordSnapshot][];
}
