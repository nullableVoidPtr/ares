import * as t from '@babel/types';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import type { NewObjectWithBufferInst } from '../../../hbc/disassembly/instruction.ts';
import {
	type SSAInstruction,
	type SSARegister,
	ssaRegisterEquals,
} from '../../../ssa.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import type { IRFunction } from '../mod.ts';
import { debugModel } from './debug.ts';
import {
	blockConstantNumber,
	constantNumber,
	rawRegister,
	recognitionStateControlSlots,
	recognizeStateMachine,
} from './recognition.ts';
import type {
	CaseTerminal,
	EnvSlotKind,
	GeneratorCaseBlockModel,
	GeneratorCaseModel,
	RawInstructionLike,
	SSAGeneratorModel,
	StateDispatch,
	StateMachineRecognition,
	TerminalValue,
} from './types.ts';

function literalKeyName(func: IRFunction, value: unknown) {
	if (!value || typeof value !== 'object' || !('stringTableIndex' in value)) {
		return;
	}
	const index = (value as { stringTableIndex: unknown }).stringTableIndex;
	if (typeof index !== 'number') return;
	return func.file.getString(index);
}

export function ssaRegisterKey(register: SSARegister) {
	return `${register.index}:${register.version}`;
}

function ssaInstructionDefs(instr: SSAInstruction) {
	const defs: SSARegister[] = [];
	if (instr.instruction === 'Phi') {
		defs.push(instr.destination);
		return defs;
	}
	const values = Object.values(
		(instr as { defs?: Record<string, SSARegister> }).defs ?? {},
	);
	for (const value of values) {
		if (rawRegister(value)) defs.push(value);
	}
	return defs;
}

function ssaInstructionUses(instr: SSAInstruction) {
	const uses: SSARegister[] = [];
	if (instr.instruction === 'Phi') {
		uses.push(...instr.sources.values());
		return uses;
	}
	const values = Object.values(
		(instr as { uses?: Record<string, SSARegister | SSARegister[]> })
			.uses ??
			{},
	);
	for (const value of values) {
		if (Array.isArray(value)) {
			uses.push(
				...value.filter((item): item is SSARegister =>
					rawRegister(item) != null
				),
			);
		} else if (rawRegister(value)) {
			uses.push(value);
		}
	}
	return uses;
}

function collectRetainedUses(instructions: SSAInstruction[]) {
	const retained = new Set<string>();
	for (const instr of instructions) {
		for (const use of ssaInstructionUses(instr)) {
			retained.add(ssaRegisterKey(use));
		}
	}
	return retained;
}

function terminalValueSummary(func: IRFunction, value: TerminalValue) {
	if (value == null) return 'none';
	if (value.kind === 'register') {
		return `r${value.register.index}_${value.register.version}`;
	}
	const literal = value.value;
	if (
		literal && typeof literal === 'object' &&
		'stringTableIndex' in literal &&
		typeof literal.stringTableIndex === 'number'
	) {
		return JSON.stringify(func.file.getString(literal.stringTableIndex));
	}
	return JSON.stringify(literal);
}

function literalTerminalValue(value: unknown): TerminalValue {
	return { kind: 'literal', value };
}

/**
 * SSA counterparts of a block's raw instructions, keyed by bytecode offset.
 *
 * A join block's SSA form carries `Phi` pseudo-instructions that have no raw
 * counterpart, so the two instruction arrays are not index-parallel there.
 * Only `functionLocalOffset` pairs them reliably.
 */
function ssaInstructionsByOffset(
	ssaBlock: { ssaInstructions: SSAInstruction[] } | undefined,
) {
	const byOffset = new Map<number, SSAInstruction>();
	for (const instr of ssaBlock?.ssaInstructions ?? []) {
		if (instr.instruction === 'Phi') continue;
		byOffset.set(instr.functionLocalOffset, instr);
	}
	return byOffset;
}

function pairedSSAInstruction(
	byOffset: Map<number, SSAInstruction>,
	instr: RawInstructionLike,
) {
	if (instr.functionLocalOffset == null) return;
	return byOffset.get(instr.functionLocalOffset);
}

/**
 * The `{ value, done }` payload a state returns.
 *
 * `returned` is the register the block's `Ret` hands back. A yield block also
 * builds unrelated object literals -- the fetch options of a call being
 * yielded, for instance -- so the iterator result is identified by the
 * definition of the returned register, never by the first
 * `NewObjectWithBuffer` in the block.
 */
function iteratorResultValueSSA(
	func: IRFunction,
	block: { instructions: RawInstructionLike[] },
	ssaBlock?: { ssaInstructions: SSAInstruction[] },
	returned?: SSARegister,
): { value: TerminalValue; done: boolean } | undefined {
	const returnedDef = returned &&
		ssaDefinitionIndex(func).get(ssaRegisterKey(returned));
	const resultSSA = returnedDef?.instruction === 'NewObjectWithBuffer'
		? returnedDef
		: undefined;
	const objectInst: RawInstructionLike | undefined = resultSSA ??
		(returned
			? undefined
			: block.instructions.find((instr) =>
				instr.instruction === 'NewObjectWithBuffer'
			));
	if (!objectInst || typeof objectInst.shapeTableIndex !== 'number') return;
	const { keys, values } = func.file.getObjectBufferElements(
		objectInst as NewObjectWithBufferInst,
	);
	if (literalKeyName(func, keys[0]) !== 'value') return;
	if (literalKeyName(func, keys[1]) !== 'done') return;
	if (values[1] !== true && values[1] !== false) return;

	let value: TerminalValue = literalTerminalValue(values[0]);
	if (resultSSA && returned) {
		for (const instr of ssaBlock?.ssaInstructions ?? []) {
			if (instr.instruction !== 'PutOwnBySlotIdx') continue;
			if (instr.slotIndex !== 0) continue;
			if (!ssaRegisterEquals(instr.uses.object, returned)) continue;
			value = { kind: 'register', register: instr.uses.value };
		}
		return { value, done: values[1] };
	}

	const ssaByOffset = ssaInstructionsByOffset(ssaBlock);
	const objectSSA = pairedSSAInstruction(ssaByOffset, objectInst);
	const objectRegister = objectSSA?.instruction === 'NewObjectWithBuffer'
		? rawRegister(objectSSA.defs.destination)
		: rawRegister(objectInst.destination);
	if (objectRegister) {
		for (const instr of block.instructions) {
			if (instr.instruction !== 'PutOwnBySlotIdx') continue;
			if (instr.slotIndex !== 0) continue;
			const ssaInstr = pairedSSAInstruction(ssaByOffset, instr);
			const target = ssaInstr?.instruction === 'PutOwnBySlotIdx'
				? rawRegister(ssaInstr.uses.object)
				: rawRegister(instr.object);
			if (!target || target.index !== objectRegister.index) continue;
			const reg = ssaInstr?.instruction === 'PutOwnBySlotIdx'
				? rawRegister(ssaInstr.uses.value)
				: rawRegister(instr.value);
			if (reg) value = { kind: 'register', register: reg };
		}
	}

	return { value, done: values[1] };
}

/**
 * The name of builtin `index`, when it is one of the `HermesInternal` helpers.
 *
 * Resolved through the version's own builtin table rather than by number: the
 * private builtins sit after the public ones, so the index of any given helper
 * moves between bytecode versions.
 */
function hermesInternalBuiltinName(
	func: IRFunction,
	index: number,
): string | null {
	const builtin = func.file.versionInfo.builtins[index];
	if (!builtin || builtin.computed) return null;
	if (!t.isIdentifier(builtin.object, { name: 'HermesInternal' })) {
		return null;
	}
	if (!t.isIdentifier(builtin.property)) return null;

	return builtin.property.name;
}

/**
 * Whether a block returns the result object of a delegated iterator.
 *
 * `yield*` forwards the delegate's own `{ value, done }` object instead of
 * building one, so the state ends in `Ret` on a register the literal
 * recogniser above cannot see into, and the state would otherwise be filed as
 * an opaque `iteratorResult`. A generator whose every state ends that way is
 * refused as "not a lowered generator", which is what left every delegating
 * generator raw.
 *
 * Hermes marks the object twice on the way out. It validates it --
 * `HermesInternal.ensureObject(result, "iterator.next() did not return an
 * object")` -- and then reads `.done` from it to choose between forwarding the
 * result and resuming the body. Requiring both, and requiring the `.done` read
 * to be on the register actually returned, is what keeps an ordinary switch
 * over an environment slot from matching: `ensureObject` is only ever emitted
 * by the iterator protocol, and a plain function has no reason to interrogate
 * the value it is about to return.
 */
function returnsDelegateIteratorResult(
	func: IRFunction,
	address: BlockAddr,
	returned: SSARegister,
): boolean {
	// The two marks sit in the block that decides whether to forward: it ends
	// in the conditional jump on `.done`, so the `Ret` is already the next
	// block along. Scan the returning block together with whatever branches
	// into it.
	const blocks: { instructions: RawInstructionLike[] }[] = [];
	const seen = new AddressSet<BlockAddr>();
	let frontier: BlockAddr[] = [address];
	// Four levels reaches the deciding block through the store-and-fall-through
	// blocks Hermes leaves between it and the `Ret`, without wandering far
	// enough for a reused register number to mean something else.
	for (let depth = 0; depth < 4 && frontier.length > 0; depth++) {
		const next: BlockAddr[] = [];
		for (const at of frontier) {
			if (seen.has(at)) continue;
			seen.add(at);
			const entry = func.ssa._func.basicBlocks.get(at);
			if (entry) blocks.push(entry);
			for (const candidate of func.ssa._func.basicBlocks.values()) {
				if (candidate.consequentAddresses?.includes(at)) {
					next.push(candidate.address);
				}
			}
		}
		frontier = next;
	}

	let validated = false;
	let readsDone = false;

	for (const instr of blocks.flatMap((entry) => entry.instructions)) {
		if (
			instr.instruction === 'CallBuiltin' &&
			hermesInternalBuiltinName(
					func,
					(instr as unknown as { builtinNo: number }).builtinNo,
				) === 'ensureObject'
		) {
			validated = true;
			continue;
		}
		if (instr.instruction !== 'GetById') continue;
		const object = rawRegister(
			(instr as unknown as { object?: unknown }).object,
		);
		if (object?.index !== returned.index) continue;
		const property = (instr as unknown as {
			property?: { stringTableIndex?: number };
		}).property;
		if (property?.stringTableIndex == null) continue;
		if (func.file.getString(property.stringTableIndex) === 'done') {
			readsDone = true;
		}
	}

	return validated && readsDone;
}

function terminalFromSSA(
	func: IRFunction,
	address: BlockAddr,
): CaseTerminal | undefined {
	const block = func.ssa._func.basicBlocks.get(address);
	const ssaBlock = func.ssa.basicBlocks.get(address);
	if (!block) return;
	const terminal = block.instructions.at(-1);
	const ssaTerminal = ssaBlock?.ssaInstructions.at(-1);
	if (terminal?.instruction === 'Throw') {
		const reg = ssaTerminal?.instruction === 'Throw'
			? rawRegister(ssaTerminal.uses.exception)
			: rawRegister(terminal.exception);
		return {
			kind: 'throw',
			value: reg ? { kind: 'register', register: reg } : null,
		};
	}
	if (terminal?.instruction !== 'Ret') return;

	const returnedRegister = ssaTerminal?.instruction === 'Ret'
		? rawRegister(ssaTerminal.uses.argument)
		: undefined;
	const result = iteratorResultValueSSA(
		func,
		block,
		ssaBlock,
		returnedRegister ?? undefined,
	);
	if (!result) {
		const reg = ssaTerminal?.instruction === 'Ret'
			? rawRegister(ssaTerminal.uses.argument)
			: rawRegister((terminal as { argument?: unknown }).argument);
		if (!reg) return;
		// A forwarded delegate result is a yield of that delegate, not an
		// opaque return.
		if (returnsDelegateIteratorResult(func, address, reg)) {
			return {
				kind: 'yield',
				value: { kind: 'register', register: reg },
			};
		}
		return {
			kind: 'iteratorResult',
			value: { kind: 'register', register: reg },
		};
	}
	if (result.done === false) {
		return { kind: 'yield', value: result.value };
	}
	return { kind: 'return', value: result.value };
}

function isStateControlStore(
	instr: RawInstructionLike,
	recognition: StateMachineRecognition,
) {
	if (
		instr.instruction !== 'StoreNPToEnvironment' &&
		instr.instruction !== 'StoreToEnvironment'
	) return false;
	if (instr.environment?.index !== recognition.stateEnvRegisterIndex) {
		return false;
	}
	return instr.slotIndex != null &&
		recognitionStateControlSlots(recognition).has(instr.slotIndex);
}

function isStateControlLoad(
	instr: RawInstructionLike,
	recognition: StateMachineRecognition,
) {
	if (instr.instruction !== 'LoadFromEnvironment') return false;
	if (instr.environment?.index !== recognition.stateEnvRegisterIndex) {
		return false;
	}
	return instr.slotIndex != null &&
		recognitionStateControlSlots(recognition).has(instr.slotIndex);
}

function isLoweredGeneratorPathControl(instr: SSAInstruction) {
	switch (instr.instruction) {
		case 'Jmp':
		case 'UIntSwitchImm':
			return true;
		default:
			return false;
	}
}

function isActionRegisterBranch(
	instr: SSAInstruction,
	recognition: StateMachineRecognition,
) {
	if (
		instr.instruction !== 'JStrictEqual' &&
		instr.instruction !== 'JStrictNotEqual'
	) return false;
	return instr.uses.left.index === recognition.actionRegister ||
		instr.uses.right.index === recognition.actionRegister;
}

function filterCaseBlockInstructions(
	instructions: SSAInstruction[],
	recognition: StateMachineRecognition,
) {
	const structurallyRetained = instructions.filter((instr) =>
		!isStateControlStore(
			instr as unknown as RawInstructionLike,
			recognition,
		) &&
		!isLoweredGeneratorPathControl(instr) &&
		!isActionRegisterBranch(instr, recognition)
	);
	const retainedUses = collectRetainedUses(structurallyRetained);
	return structurallyRetained.filter((instr) => {
		if (
			!isStateControlLoad(
				instr as unknown as RawInstructionLike,
				recognition,
			)
		) return true;
		return ssaInstructionDefs(instr).some((def) =>
			retainedUses.has(ssaRegisterKey(def))
		);
	});
}

function reorderCasePhiSources(
	instructions: SSAInstruction[],
	incomingPredecessors: AddressSet<BlockAddr>,
) {
	return instructions.map((instr): SSAInstruction => {
		if (instr.instruction !== 'Phi') return instr;
		const ordered = new AddressMap<SSARegister>();
		for (const [addr, source] of instr.sources) {
			if (incomingPredecessors.has(addr)) ordered.set(addr, source);
		}
		for (const [addr, source] of instr.sources) {
			if (!ordered.has(addr)) ordered.set(addr, source);
		}
		return { ...instr, sources: ordered };
	});
}

const ssaDefinitionIndexes = new WeakMap<
	IRFunction,
	Map<string, SSAInstruction>
>();

/**
 * Every SSA register of a function indexed by `index:version`.
 *
 * `recognition.constants` is keyed by raw register *index*, so it answers with
 * whichever block wrote that index last. Hermes reuses low registers freely --
 * `r5` can be the state constant in one block and an iterator-result object in
 * another -- so state-transition values must be resolved from the versioned
 * definition instead.
 */
function ssaDefinitionIndex(func: IRFunction) {
	let index = ssaDefinitionIndexes.get(func);
	if (index) return index;
	index = new Map<string, SSAInstruction>();
	for (const block of func.ssa.basicBlocks.values()) {
		for (const instr of block.ssaInstructions) {
			for (const def of ssaInstructionDefs(instr)) {
				index.set(ssaRegisterKey(def), instr);
			}
		}
	}
	ssaDefinitionIndexes.set(func, index);
	return index;
}

/** The constant a versioned register holds, following `Mov` copies. */
function ssaConstantNumber(
	definitions: Map<string, SSAInstruction>,
	register: SSARegister | undefined,
	depth = 0,
): number | null {
	if (!register || depth > 8) return null;
	const def = definitions.get(ssaRegisterKey(register));
	if (!def) return null;
	if (def.instruction === 'LoadConst') {
		return typeof def.value === 'number' ? def.value : null;
	}
	if (def.instruction === 'Mov') {
		return ssaConstantNumber(definitions, def.uses.source, depth + 1);
	}
	return null;
}

function storedGeneratorNextState(
	instr: RawInstructionLike,
	rawBlock: { instructions: RawInstructionLike[] },
	recognition: StateMachineRecognition,
	ssaInstr: SSAInstruction | undefined,
	definitions: Map<string, SSAInstruction>,
): number | null | undefined {
	if (
		instr.instruction !== 'StoreNPToEnvironment' &&
		instr.instruction !== 'StoreToEnvironment'
	) return;
	if (instr.slotIndex !== recognition.switchSlot) return;

	const reg = rawRegister(instr.value);
	let ssaValue: SSARegister | undefined;
	if (
		ssaInstr?.instruction === 'StoreToEnvironment' ||
		ssaInstr?.instruction === 'StoreNPToEnvironment'
	) ssaValue = ssaInstr.uses.value;
	const rawNextState = ssaValue
		? ssaConstantNumber(definitions, ssaValue)
		: reg == null
		? null
		: blockConstantNumber(recognition.constants, rawBlock, reg.index);
	if (rawNextState == null) return null;
	if (recognition.dispatch.has(rawNextState)) return rawNextState;
	// Stored step value doesn't match any explicit dispatch case; it routes to
	// the default catch-all state, which has the highest key in the map.
	return Math.max(...recognition.dispatch.keys());
}

function collectSSACase(
	func: IRFunction,
	recognition: StateMachineRecognition,
	state: number,
	entry: BlockAddr,
): GeneratorCaseModel | undefined {
	let nextState: number | null = null;
	let activeHandlerIndex: number | null = null;
	let protectedHandlerIndex: number | null = null;
	let readsCaughtException = false;
	const dispatchEntries = new Set(recognition.dispatch.values());
	const path: BlockAddr[] = [];
	const blocks = new AddressMap<GeneratorCaseBlockModel>();
	const seen = new AddressSet<BlockAddr>();
	const stack: BlockAddr[] = [entry];
	while (stack.length > 0) {
		const blockAddress = stack.pop()!;
		if (seen.has(blockAddress)) continue;
		seen.add(blockAddress);
		if (seen.size > 128) return;

		const rawBlock = func.ssa._func.basicBlocks.get(blockAddress);
		const ssaBlock = func.ssa.basicBlocks.get(blockAddress);
		if (!rawBlock || !ssaBlock) return;
		path.push(blockAddress);
		let blockNextState: number | null | undefined;

		const ssaByOffset = ssaInstructionsByOffset(ssaBlock);
		const definitions = ssaDefinitionIndex(func);
		for (const instr of rawBlock.instructions) {
			const rawInstr = instr as unknown as RawInstructionLike;
			const storedNext = storedGeneratorNextState(
				rawInstr,
				rawBlock as unknown as { instructions: RawInstructionLike[] },
				recognition,
				pairedSSAInstruction(ssaByOffset, rawInstr),
				definitions,
			);
			if (storedNext !== undefined) {
				nextState = storedNext;
				blockNextState = storedNext;
			}
			if (
				recognition.exceptionHandlerSlot != null &&
				(instr.instruction === 'StoreNPToEnvironment' ||
					instr.instruction === 'StoreToEnvironment') &&
				instr.slotIndex === recognition.exceptionHandlerSlot
			) {
				const reg = rawRegister(instr.value);
				const handlerIndex = reg == null
					? null
					: constantNumber(recognition.constants, reg.index);
				activeHandlerIndex = handlerIndex;
				if (
					handlerIndex != null &&
					handlerIndex !== 0 &&
					protectedHandlerIndex == null
				) {
					protectedHandlerIndex = handlerIndex;
				}
			}
			if (
				recognition.caughtExceptionSlot != null &&
				instr.instruction === 'LoadFromEnvironment' &&
				instr.slotIndex === recognition.caughtExceptionSlot
			) {
				readsCaughtException = true;
			}
		}

		const terminal = terminalFromSSA(func, blockAddress) ?? null;
		const terminalBlock = rawBlock.consequentAddresses.length === 0 ||
			terminal != null;
		const terminalInstr = ssaBlock.ssaInstructions.at(-1);
		const actionGuard = terminalInstr &&
			isActionRegisterBranch(terminalInstr, recognition);
		const consequentAddresses = terminalBlock
			? []
			: actionGuard
			? (terminalInstr?.instruction === 'JStrictNotEqual'
				? [rawBlock.consequentAddresses[1]]
				: [rawBlock.consequentAddresses[0]])
			: rawBlock.consequentAddresses.filter((successor) =>
				successor === entry || !dispatchEntries.has(successor)
			);
		const incomingPredecessors = new AddressSet<BlockAddr>();
		for (const [predAddress, predBlock] of func.ssa._func.basicBlocks) {
			if (
				seen.has(predAddress) &&
				predBlock.consequentAddresses.includes(blockAddress)
			) {
				incomingPredecessors.add(predAddress);
			}
		}
		const instructions = reorderCasePhiSources(
			filterCaseBlockInstructions(
				ssaBlock.ssaInstructions,
				recognition,
			),
			incomingPredecessors,
		);
		blocks.set(blockAddress, {
			address: blockAddress,
			instructions,
			consequentAddresses,
			terminal,
			nextState: blockNextState,
		});
		for (const successor of consequentAddresses.toReversed()) {
			if (!seen.has(successor)) stack.push(successor);
		}
	}

	const terminalEntries = [...blocks.values()].filter((block) =>
		block.terminal != null
	);
	const inCasePredecessorCounts = new AddressMap<number>();
	for (const block of blocks.values()) {
		for (const successor of block.consequentAddresses) {
			inCasePredecessorCounts.set(
				successor,
				(inCasePredecessorCounts.get(successor) ?? 0) + 1,
			);
		}
	}
	for (const block of blocks.values()) {
		if (block.nextState === undefined) continue;
		if (block.consequentAddresses.length !== 1) continue;
		const successorAddress = block.consequentAddresses[0];
		if ((inCasePredecessorCounts.get(successorAddress) ?? 0) !== 1) {
			continue;
		}
		const successor = blocks.get(successorAddress);
		if (!successor || successor.nextState !== undefined) continue;
		if (!successor.terminal) continue;
		successor.nextState = block.nextState;
	}
	const terminal = terminalEntries[0]?.terminal;
	if (!terminal) return;
	const yieldEntries = terminalEntries.filter((block) =>
		block.terminal?.kind === 'yield'
	);
	const rawNextState = nextState;
	const defaultCatchAllState = Math.max(...recognition.dispatch.keys());
	const isSelfLoopOnDefaultState = nextState === state &&
		state === defaultCatchAllState;
	if (
		!isSelfLoopOnDefaultState &&
		recognition.sequentialStates &&
		yieldEntries.length > 0 &&
		(nextState == null || nextState === state)
	) {
		nextState = state + 1;
		for (const block of yieldEntries) {
			if (
				block.nextState == null ||
				block.nextState === state
			) block.nextState = state + 1;
		}
	}
	const instructions = path.flatMap((address) =>
		blocks.get(address)?.instructions ?? []
	);
	const effectiveActiveHandlerIndex = activeHandlerIndex == null ||
			activeHandlerIndex === 0
		? protectedHandlerIndex
		: activeHandlerIndex;
	const activeHandlerState = effectiveActiveHandlerIndex == null ||
			effectiveActiveHandlerIndex === 0
		? null
		: recognition.handlerIndexToState.get(effectiveActiveHandlerIndex) ??
			null;
	const pairedFinallyState = readsCaughtException ? activeHandlerState : null;
	return {
		state,
		entry,
		path,
		instructions,
		blocks,
		terminal,
		nextState,
		rawNextState,
		activeHandlerIndex: effectiveActiveHandlerIndex,
		activeHandlerState,
		readsCaughtException,
		pairedFinallyState,
	};
}

function classifyEnvSlotsSSA(
	func: IRFunction,
	recognition: StateMachineRecognition,
) {
	const stateControlSlots = recognitionStateControlSlots(recognition);
	const slots = new Map<number, {
		stores: { address: BlockAddr; value: unknown }[];
		loads: BlockAddr[];
	}>();
	const ensure = (slot: number) => {
		let info = slots.get(slot);
		if (!info) {
			info = { stores: [], loads: [] };
			slots.set(slot, info);
		}
		return info;
	};

	for (const block of func.ssa._func.basicBlocks.values()) {
		for (const instr of block.instructions) {
			if (
				(instr.instruction === 'StoreNPToEnvironment' ||
					instr.instruction === 'StoreToEnvironment') &&
				typeof instr.slotIndex === 'number'
			) {
				ensure(instr.slotIndex).stores.push({
					address: block.address,
					value: instr.value,
				});
			}
			if (
				instr.instruction === 'LoadFromEnvironment' &&
				typeof instr.slotIndex === 'number'
			) {
				ensure(instr.slotIndex).loads.push(block.address);
			}
		}
	}

	const kinds = new Map<number, EnvSlotKind>();
	for (const [slot, info] of slots) {
		if (stateControlSlots.has(slot)) {
			kinds.set(slot, { kind: 'stateControl' });
			continue;
		}
		const preludeStores = info.stores.filter((store) =>
			store.address < recognition.mainSwitchAddress
		);
		if (
			info.stores.length === 1 &&
			preludeStores.length === 1
		) {
			const reg = rawRegister(preludeStores[0].value);
			const value = reg == null
				? undefined
				: recognition.constants.get(reg.index);
			if (value !== undefined) {
				kinds.set(slot, { kind: 'constant', value });
				continue;
			}
		}
		if (slot >= 0 && slot < func.params.length) {
			kinds.set(slot, { kind: 'param', index: slot });
			continue;
		}
		kinds.set(slot, {
			kind: 'local',
			name: `_env_${func.id}_${slot}`,
			slot,
		});
	}
	return kinds;
}

function generatorCaseTerminals(info: GeneratorCaseModel) {
	const terminals = [...info.blocks.values()]
		.map((block) => block.terminal)
		.filter((terminal): terminal is CaseTerminal => terminal != null);
	return terminals.length > 0 ? terminals : [info.terminal];
}

function generatorCaseContinuationStates(info: GeneratorCaseModel) {
	const states = new Set<number>();
	for (const block of info.blocks.values()) {
		if (
			block.terminal?.kind === 'return' ||
			block.terminal?.kind === 'throw'
		) continue;
		const nextState = block.nextState === undefined
			? info.nextState
			: block.nextState;
		if (nextState != null) states.add(nextState);
	}
	return states;
}

function orderedModelStates(cases: Map<number, GeneratorCaseModel>) {
	const result: number[] = [];
	const seen = new Set<number>();
	const visit = (state: number) => {
		if (seen.has(state)) return;
		seen.add(state);
		const info = cases.get(state);
		if (!info) return;
		result.push(state);
		for (const nextState of generatorCaseContinuationStates(info)) {
			visit(nextState);
		}
		if (info.activeHandlerState != null) visit(info.activeHandlerState);
	};
	visit(0);
	for (const state of [...cases.keys()].toSorted((a, b) => a - b)) {
		visit(state);
	}
	return result;
}

export function buildSSAGeneratorModel(func: IRFunction) {
	const recognition = recognizeStateMachine(
		func,
		(dispatch) => chainedDispatchScore(func, dispatch),
		(candidate, entryAddress) => {
			const info = collectSSACase(func, candidate, 0, entryAddress);
			return info == null
				? false
				: generatorCaseTerminals(info).some((terminal) =>
					terminal.kind === 'return'
				);
		},
	);
	if (!recognition) return;

	const cases = new Map<number, GeneratorCaseModel>();
	for (const [state, entry] of recognition.dispatch) {
		const info = collectSSACase(func, recognition, state, entry);
		if (!info) {
			debugModel('failed to collect SSA generator state', {
				state,
				entry,
			});
			continue;
		}
		cases.set(state, info);
	}
	if (!cases.has(0)) return;

	// Post-process: detect genuine self-loops where the override incorrectly fired.
	// The override converts rawNextState=N → nextState=N+1 for state N. This is correct
	// for SSA artifact self-loops (where the global constants map returns stale value N)
	// but wrong for genuine loops (e.g. async-gen `for await...of`).
	// Heuristic: if another collected state M also targets state N (M.nextState === N),
	// then the self-loop is genuine and we reset nextState back to N.
	{
		const statesTargeted = new Set<number>();
		for (const [s, info] of cases) {
			for (const nextState of generatorCaseContinuationStates(info)) {
				if (nextState !== s) statesTargeted.add(nextState);
			}
		}
		for (const [s, info] of cases) {
			if (info.rawNextState === s && statesTargeted.has(s)) {
				info.nextState = s;
				for (const block of info.blocks.values()) {
					if (
						block.terminal?.kind === 'yield' &&
						block.nextState === s + 1
					) block.nextState = s;
				}
			}
		}
	}

	// A lowered generator implements the iterator protocol: at least one state
	// has to produce a recognized `{ value, done }` result. A dispatch whose
	// states only return an opaque register is an ordinary switch on an
	// environment slot, and recovering it would rewrite a plain function into a
	// generator that never had a `yield`.
	if (
		![...cases.values()].some((info) =>
			generatorCaseTerminals(info).some((terminal) =>
				terminal.kind === 'yield' || terminal.kind === 'return'
			)
		)
	) {
		debugModel('no iterator-result state; not a lowered generator', {
			functionId: func.id,
			terminals: [...cases.values()].map((info) =>
				generatorCaseTerminals(info).map((terminal) => terminal.kind)
			),
		});
		return;
	}

	const model: SSAGeneratorModel = {
		recognition,
		cases,
		envSlots: classifyEnvSlotsSSA(func, recognition),
		emissionOrder: orderedModelStates(cases),
	};
	debugModel(
		'SSA generator model',
		JSON.stringify({
			switchSlot: recognition.switchSlot,
			exceptionHandlerSlot: recognition.exceptionHandlerSlot,
			caughtExceptionSlot: recognition.caughtExceptionSlot,
			executionStatusSlot: recognition.executionStatusSlot,
			dispatchSize: recognition.dispatch.size,
			caseSize: cases.size,
			envSlots: [...model.envSlots],
			cases: [...cases.values()].map((info) => ({
				state: info.state,
				entry: info.entry,
				path: info.path,
				nextState: info.nextState,
				activeHandlerState: info.activeHandlerState,
				readsCaughtException: info.readsCaughtException,
				pairedFinallyState: info.pairedFinallyState,
				terminal: info.terminal.kind,
				terminalValue: terminalValueSummary(func, info.terminal.value),
				instructionCount: info.instructions.length,
			})),
			emissionOrder: model.emissionOrder,
		}),
	);
	return model;
}

function chainedDispatchScore(func: IRFunction, dispatch: StateDispatch) {
	let terminalCases = 0;
	let failedCases = 0;
	for (const address of dispatch.cases.values()) {
		if (reachableCaseTerminal(func, dispatch, address)) {
			terminalCases++;
		} else {
			failedCases++;
		}
	}
	return terminalCases - failedCases;
}

function reachableCaseTerminal(
	func: IRFunction,
	dispatch: StateDispatch,
	start: BlockAddr,
) {
	const dispatchEntries = new Set(dispatch.cases.values());
	const seen = new AddressSet<BlockAddr>();
	const stack: BlockAddr[] = [start];
	while (stack.length > 0) {
		const address = stack.pop()!;
		if (seen.has(address)) continue;
		seen.add(address);
		if (seen.size > 128) return false;
		const block = func.ssa._func.basicBlocks.get(address);
		if (!block) continue;
		if (terminalFromSSA(func, address)) return true;
		for (const successor of block.consequentAddresses) {
			if (successor !== start && dispatchEntries.has(successor)) {
				continue;
			}
			stack.push(successor);
		}
	}
	return false;
}
