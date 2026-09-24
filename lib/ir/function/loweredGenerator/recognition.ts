import { BlockAddr, FunctionKind } from '../../../hbc/disassembly/function.ts';
import { AddressSet } from '../../../utils/set.ts';
import type { SSARegister } from '../../../ssa.ts';
import type { IRFunction } from '../mod.ts';
import { debug } from './debug.ts';
import type {
	ChainedExceptionRouter,
	RawBlockLike,
	RawInstructionLike,
	StateDispatch,
	StateMachineRecognition,
	StateRoles,
} from './types.ts';

export type DispatchScore = (dispatch: StateDispatch) => number;
export type ImmediateCandidateValidator = (
	recognition: StateMachineRecognition,
	entryAddress: BlockAddr,
) => boolean;

export function rawRegister(value: unknown): SSARegister | null {
	if (
		value && typeof value === 'object' &&
		'index' in value && typeof value.index === 'number'
	) {
		const version = 'version' in value && typeof value.version === 'number'
			? value.version
			: 0;
		return { type: 'register', index: value.index, version };
	}
	return null;
}

export function rawRegisterIndex(value: unknown) {
	if (
		value && typeof value === 'object' &&
		'index' in value && typeof value.index === 'number'
	) return value.index;
}

export function rawFunctionId(value: unknown) {
	if (
		value && typeof value === 'object' &&
		'functionId' in value && typeof value.functionId === 'number'
	) return value.functionId;
}

export function constantNumber(
	constants: Map<number, unknown>,
	registerIndex: number,
) {
	const value = constants.get(registerIndex);
	return typeof value === 'number' ? value : null;
}

function inferSwitchDispatch(func: IRFunction): StateDispatch | undefined {
	if (func.ssa._func.functionKind !== FunctionKind.NormalFunction) return;

	const constants = new Map<number, unknown>();
	let actionRegister: number | null = null;
	for (const block of func.ssa._func.basicBlocks.values()) {
		for (const instr of block.instructions) {
			// These loops walk every instruction of every block, so they meet
			// whatever shape a restored function carries. The declared type
			// guarantees a destination here, but a function paged back in
			// through the cold store has produced one without it, and reading
			// `.index` off that cost the whole function rather than just this
			// recognition.
			if (instr.instruction === 'LoadConst') {
				const destination = rawRegisterIndex(instr.destination);
				if (destination != null) {
					constants.set(destination, instr.value);
				}
			}
			if (
				instr.instruction === 'LoadParam' && instr.parameterIndex === 1
			) {
				const destination = rawRegisterIndex(instr.destination);
				if (destination != null) actionRegister = destination;
			}
		}
	}
	if (actionRegister == null) return;

	const switchBlocks = [...func.ssa._func.basicBlocks.values()].filter(
		(block) =>
			block.instructions.some((instr) =>
				instr.instruction === 'UIntSwitchImm'
			),
	);
	if (switchBlocks.length === 0) return;

	const [mainSwitch, exceptionSwitch] = switchBlocks.toSorted((a, b) =>
		b.consequentAddresses.length - a.consequentAddresses.length
	);
	const mainSwitchInst = mainSwitch.instructions.find((instr) =>
		instr.instruction === 'UIntSwitchImm'
	);
	if (mainSwitchInst?.instruction !== 'UIntSwitchImm') return;

	const switchLoad = mainSwitch.instructions.find((instr) =>
		instr.instruction === 'LoadFromEnvironment' &&
		instr.destination.index === mainSwitchInst.discriminant.index
	);
	if (switchLoad?.instruction !== 'LoadFromEnvironment') return;

	const handlerIndexToState = new Map<number, number>();
	let exceptionHandlerSlot = -1;
	let caughtExceptionSlot = -1;
	const exceptionSwitchInst = exceptionSwitch?.instructions.find((instr) =>
		instr.instruction === 'UIntSwitchImm'
	);
	const exceptionLoad = exceptionSwitch && exceptionSwitchInst
		? exceptionSwitch.instructions.find((instr) =>
			instr.instruction === 'LoadFromEnvironment' &&
			instr.destination.index === exceptionSwitchInst.discriminant.index
		)
		: undefined;
	const catchInst = exceptionSwitch?.instructions.find((instr) =>
		instr.instruction === 'Catch'
	);
	const caughtExceptionStore = exceptionSwitch && catchInst
		? exceptionSwitch.instructions.find((instr) =>
			(instr.instruction === 'StoreToEnvironment' ||
				instr.instruction === 'StoreNPToEnvironment') &&
			instr.value.index === catchInst.destination.index
		)
		: undefined;

	if (
		exceptionSwitch &&
		exceptionSwitchInst?.instruction === 'UIntSwitchImm' &&
		exceptionLoad?.instruction === 'LoadFromEnvironment' &&
		catchInst?.instruction === 'Catch' &&
		(caughtExceptionStore?.instruction === 'StoreToEnvironment' ||
			caughtExceptionStore?.instruction === 'StoreNPToEnvironment')
	) {
		exceptionHandlerSlot = exceptionLoad.slotIndex;
		caughtExceptionSlot = caughtExceptionStore.slotIndex;
		const exceptionDefaultTarget = exceptionSwitch.consequentAddresses[0];
		if (exceptionDefaultTarget != null) {
			const block = func.ssa._func.basicBlocks.get(
				exceptionDefaultTarget,
			);
			if (block) {
				for (const instr of block.instructions) {
					if (
						instr.instruction !== 'StoreNPToEnvironment' &&
						instr.instruction !== 'StoreToEnvironment'
					) continue;
					if (instr.slotIndex !== switchLoad.slotIndex) continue;
					const state = constantNumber(constants, instr.value.index);
					if (state == null) continue;
					handlerIndexToState.set(
						exceptionSwitchInst.maxValue + 1,
						state,
					);
					break;
				}
			}
		}
		for (
			let i = 0;
			i <= exceptionSwitchInst.maxValue - exceptionSwitchInst.minValue;
			i++
		) {
			const target = exceptionSwitch.consequentAddresses[i + 1];
			const block = func.ssa._func.basicBlocks.get(target);
			if (!block) continue;
			for (const instr of block.instructions) {
				if (
					instr.instruction !== 'StoreNPToEnvironment' &&
					instr.instruction !== 'StoreToEnvironment'
				) continue;
				if (instr.slotIndex !== switchLoad.slotIndex) continue;
				const state = constantNumber(constants, instr.value.index);
				if (state == null) continue;
				handlerIndexToState.set(
					i + exceptionSwitchInst.minValue,
					state,
				);
				break;
			}
		}
	} else {
		const exceptionRouter = inferChainedExceptionRouter(
			func,
			constants,
			switchLoad.slotIndex,
			mainSwitch.address,
		);
		if (exceptionRouter) {
			exceptionHandlerSlot = exceptionRouter.exceptionHandlerSlot;
			caughtExceptionSlot = exceptionRouter.caughtExceptionSlot;
			for (
				const [handlerIndex, state] of exceptionRouter
					.handlerIndexToState
			) {
				handlerIndexToState.set(handlerIndex, state);
			}
		}
	}
	if (handlerIndexToState.size === 0) return;

	const cases = new Map<number, BlockAddr>();
	const inclusiveCaseCount = mainSwitchInst.maxValue -
		mainSwitchInst.minValue + 1;
	if (mainSwitch.consequentAddresses.length === inclusiveCaseCount + 1) {
		const defaultAddress = mainSwitch.consequentAddresses[0];
		if (defaultAddress != null) {
			cases.set(mainSwitchInst.maxValue + 1, defaultAddress);
		}
		for (
			let state = mainSwitchInst.minValue;
			state <= mainSwitchInst.maxValue;
			state++
		) {
			const address = mainSwitch.consequentAddresses[
				state - mainSwitchInst.minValue + 1
			];
			if (address != null) cases.set(state, address);
		}
	} else if (mainSwitch.consequentAddresses.length === inclusiveCaseCount) {
		const defaultAddress = mainSwitch.consequentAddresses[0];
		if (defaultAddress != null) {
			cases.set(mainSwitchInst.maxValue + 1, defaultAddress);
		}
		for (
			let state = mainSwitchInst.minValue;
			state < mainSwitchInst.maxValue;
			state++
		) {
			const address = mainSwitch.consequentAddresses[
				state - mainSwitchInst.minValue + 1
			];
			if (address != null) cases.set(state, address);
		}
	} else {
		return;
	}

	return {
		cases,
		roles: {
			actionRegister,
			switchSlot: switchLoad.slotIndex,
			stateEnvRegisterIndex: switchLoad.environment.index,
			exceptionHandlerSlot,
			caughtExceptionSlot,
			executionStatusSlot: inferExecutionStatusSlot(
				func,
				constants,
				switchLoad.slotIndex,
			),
			resumeValueSlot: inferResumeValueSlot(
				func,
				constants,
				actionRegister,
				switchLoad.environment.index,
			),
			mainSwitchAddress: mainSwitch.address,
			handlerIndexToState,
			constants,
		},
	};
}

export function blockConstantNumber(
	constants: Map<number, unknown>,
	block: { instructions: RawInstructionLike[] } | undefined,
	register: number,
) {
	const definition = block?.instructions.findLast((candidate) =>
		candidate.destination?.index === register
	);
	if (definition) {
		return definition.instruction === 'LoadConst' &&
				typeof definition.value === 'number'
			? definition.value
			: null;
	}
	return constantNumber(constants, register);
}

function comparedRegisterAndConstant(
	constants: Map<number, unknown>,
	terminal: RawInstructionLike | undefined,
	block?: { instructions: RawInstructionLike[] },
) {
	if (terminal?.instruction !== 'JStrictEqual') return;
	if (!terminal.left || !terminal.right) return;
	const left = terminal.left.index;
	const right = terminal.right.index;
	const leftConstant = blockConstantNumber(constants, block, left);
	const rightConstant = blockConstantNumber(constants, block, right);
	if (leftConstant != null && rightConstant == null) {
		return { register: right, constant: leftConstant };
	}
	if (rightConstant != null && leftConstant == null) {
		return { register: left, constant: rightConstant };
	}
}

function constantComparedWithRegister(
	constants: Map<number, unknown>,
	terminal: RawInstructionLike | undefined,
	register: number,
	block?: { instructions: RawInstructionLike[] },
) {
	if (terminal?.instruction !== 'JStrictEqual') return null;
	if (!terminal.left || !terminal.right) return null;
	if (terminal.left.index === register) {
		return blockConstantNumber(constants, block, terminal.right.index);
	}
	if (terminal.right.index === register) {
		return blockConstantNumber(constants, block, terminal.left.index);
	}
	return null;
}

function inferExecutionStatusSlot(
	func: IRFunction,
	constants: Map<number, unknown>,
	switchSlot: number,
) {
	for (const block of func.ssa._func.basicBlocks.values()) {
		const terminal = block.instructions.at(-1);
		if (
			terminal?.instruction !== 'JStrictEqual' ||
			!terminal.left ||
			!terminal.right
		) continue;
		for (
			const [loadedRegister, constantRegister] of [
				[terminal.left.index, terminal.right.index],
				[terminal.right.index, terminal.left.index],
			]
		) {
			if (
				blockConstantNumber(constants, block, constantRegister) !== 2
			) continue;
			const load = block.instructions.findLast((instr) =>
				'destination' in instr &&
				instr.destination.index === loadedRegister
			);
			if (
				load?.instruction === 'LoadFromEnvironment' &&
				load.slotIndex !== switchSlot
			) return load.slotIndex;
		}
	}
}

function inferResumeValueSlot(
	func: IRFunction,
	constants: Map<number, unknown>,
	actionRegister: number,
	stateEnvRegisterIndex: number,
) {
	const resumeRegisters = new Set<number>();
	for (const block of func.ssa._func.basicBlocks.values()) {
		for (const instr of block.instructions) {
			if (
				instr.instruction === 'LoadParam' &&
				instr.parameterIndex === 2
			) {
				resumeRegisters.add(instr.destination.index);
			}
		}
	}
	for (const block of func.ssa._func.basicBlocks.values()) {
		if (
			constantComparedWithRegister(
				constants,
				block.instructions.at(-1),
				actionRegister,
				block,
			) !== 2
		) continue;
		for (const instr of block.instructions) {
			if (
				(instr.instruction === 'StoreToEnvironment' ||
					instr.instruction === 'StoreNPToEnvironment') &&
				instr.environment.index === stateEnvRegisterIndex &&
				resumeRegisters.has(instr.value.index)
			) return instr.slotIndex;
		}
	}
}

function storedEnvironmentSlot(
	instr: RawInstructionLike,
	registerIndex: number,
) {
	if (
		instr.instruction !== 'StoreToEnvironment' &&
		instr.instruction !== 'StoreNPToEnvironment'
	) return null;
	if (instr.value == null || typeof instr.value !== 'object') return null;
	if (!('index' in instr.value) || instr.value.index !== registerIndex) {
		return null;
	}
	return instr.slotIndex ?? null;
}

function handlerRouteState(
	func: IRFunction,
	constants: Map<number, unknown>,
	address: BlockAddr,
	switchSlot: number,
	mainSwitchAddress: BlockAddr,
) {
	const block = func.ssa._func.basicBlocks.get(address) as
		| RawBlockLike
		| undefined;
	if (!block || !reachesDispatchEntry(func, block, mainSwitchAddress)) {
		return null;
	}

	for (const instr of block.instructions) {
		if (
			instr.instruction !== 'StoreToEnvironment' &&
			instr.instruction !== 'StoreNPToEnvironment'
		) continue;
		if (instr.slotIndex !== switchSlot) continue;
		if (instr.value == null || typeof instr.value !== 'object') continue;
		if (!('index' in instr.value)) continue;
		if (typeof instr.value.index !== 'number') continue;
		return blockConstantNumber(constants, block, instr.value.index);
	}
	return null;
}

function reachesDispatchEntry(
	func: IRFunction,
	start: RawBlockLike,
	mainSwitchAddress: BlockAddr,
) {
	let block: RawBlockLike | undefined = start;
	const seen = new AddressSet<BlockAddr>();
	for (let depth = 0; block && depth < 4; depth++) {
		if (block.address === mainSwitchAddress) return true;
		if (block.consequentAddresses.includes(mainSwitchAddress)) {
			return true;
		}
		if (block.consequentAddresses.length !== 1) return false;
		if (seen.has(block.address)) return false;
		seen.add(block.address);
		block = func.ssa._func.basicBlocks.get(
			block.consequentAddresses[0],
		) as RawBlockLike | undefined;
	}
	return false;
}

function inferChainedExceptionRouter(
	func: IRFunction,
	constants: Map<number, unknown>,
	switchSlot: number,
	mainSwitchAddress: BlockAddr,
): ChainedExceptionRouter | undefined {
	for (
		const block of func.ssa._func.basicBlocks.values() as Iterable<
			RawBlockLike
		>
	) {
		const catchInst = block.instructions.find((instr) =>
			instr.instruction === 'Catch' && instr.destination != null
		);
		if (!catchInst?.destination) continue;

		let caughtExceptionSlot: number | null = null;
		for (const instr of block.instructions) {
			const slot = storedEnvironmentSlot(
				instr,
				catchInst.destination.index,
			);
			if (slot != null) {
				caughtExceptionSlot = slot;
				break;
			}
		}
		if (caughtExceptionSlot == null) continue;

		const terminal = block.instructions.at(-1);
		const compared = comparedRegisterAndConstant(
			constants,
			terminal,
			block,
		);
		if (!compared || compared.constant !== 0) continue;

		const handlerLoad = block.instructions.find((instr) =>
			instr.instruction === 'LoadFromEnvironment' &&
			instr.destination?.index === compared.register
		);
		if (
			handlerLoad?.instruction !== 'LoadFromEnvironment' ||
			handlerLoad.slotIndex == null
		) continue;

		const handlerIndexToState = new Map<number, number>();
		let currentAddress: BlockAddr | undefined = block.address;
		let nextDefaultHandlerIndex = 0;
		const seen = new AddressSet<BlockAddr>();
		while (currentAddress != null) {
			if (seen.has(currentAddress)) break;
			seen.add(currentAddress);
			const current = func.ssa._func.basicBlocks.get(currentAddress) as
				| RawBlockLike
				| undefined;
			const currentTerminal = current?.instructions.at(-1);
			const handlerIndex = constantComparedWithRegister(
				constants,
				currentTerminal,
				compared.register,
				current,
			);
			if (
				!current ||
				current.consequentAddresses.length !== 2 ||
				handlerIndex == null
			) break;

			const falseTarget = current.consequentAddresses[0];
			const trueTarget = current.consequentAddresses[1];
			const state = handlerRouteState(
				func,
				constants,
				trueTarget,
				switchSlot,
				mainSwitchAddress,
			);
			if (state != null) handlerIndexToState.set(handlerIndex, state);
			nextDefaultHandlerIndex = Math.max(
				nextDefaultHandlerIndex,
				handlerIndex + 1,
			);
			currentAddress = falseTarget;
		}

		if (currentAddress != null) {
			const defaultState = handlerRouteState(
				func,
				constants,
				currentAddress,
				switchSlot,
				mainSwitchAddress,
			);
			if (defaultState != null) {
				handlerIndexToState.set(nextDefaultHandlerIndex, defaultState);
			}
		}
		if (handlerIndexToState.size === 0) continue;

		debug('chained exception router', {
			exceptionHandlerSlot: handlerLoad.slotIndex,
			caughtExceptionSlot,
			handlerIndexToState: [...handlerIndexToState],
		});
		return {
			exceptionHandlerSlot: handlerLoad.slotIndex,
			caughtExceptionSlot,
			handlerIndexToState,
		};
	}
}

function inferChainedDispatch(
	func: IRFunction,
	scoreDispatch: DispatchScore,
): StateDispatch | undefined {
	if (func.ssa._func.functionKind !== FunctionKind.NormalFunction) return;

	const constants = new Map<number, unknown>();
	let actionRegister: number | null = null;
	for (const block of func.ssa._func.basicBlocks.values()) {
		for (const instr of block.instructions) {
			// These loops walk every instruction of every block, so they meet
			// whatever shape a restored function carries. The declared type
			// guarantees a destination here, but a function paged back in
			// through the cold store has produced one without it, and reading
			// `.index` off that cost the whole function rather than just this
			// recognition.
			if (instr.instruction === 'LoadConst') {
				const destination = rawRegisterIndex(instr.destination);
				if (destination != null) {
					constants.set(destination, instr.value);
				}
			}
			if (
				instr.instruction === 'LoadParam' && instr.parameterIndex === 1
			) {
				const destination = rawRegisterIndex(instr.destination);
				if (destination != null) actionRegister = destination;
			}
		}
	}
	if (actionRegister == null) return;

	const candidates: StateDispatch[] = [];
	for (const block of func.ssa._func.basicBlocks.values()) {
		const terminal = block.instructions.at(-1);
		const firstCompared = comparedRegisterAndConstant(
			constants,
			terminal,
			block,
		) ??
			(() => {
				const compared = environmentLoadComparedToConstant(
					constants,
					block as RawBlockLike,
				);
				if (!compared) return;
				return {
					register: compared.load.register,
					constant: compared.constant,
				};
			})();
		if (!firstCompared || firstCompared.constant !== 0) continue;

		const switchLoad = block.instructions.find((instr) =>
			instr.instruction === 'LoadFromEnvironment' &&
			instr.destination.index === firstCompared.register
		);
		if (switchLoad?.instruction !== 'LoadFromEnvironment') continue;

		const cases = new Map<number, BlockAddr>();
		const dispatchPreludeAddresses: BlockAddr[] = [];
		let currentAddress: BlockAddr | undefined = block.address;
		let nextDefaultState = 0;
		const seen = new AddressSet<BlockAddr>();
		while (currentAddress != null) {
			if (seen.has(currentAddress)) break;
			seen.add(currentAddress);
			const current = func.ssa._func.basicBlocks.get(currentAddress);
			const currentTerminal = current?.instructions.at(-1);
			const state = constantComparedWithRegister(
				constants,
				currentTerminal,
				firstCompared.register,
				current,
			);
			if (
				!current ||
				current.consequentAddresses.length !== 2 ||
				state == null
			) break;
			if (state !== nextDefaultState || cases.has(state)) break;
			dispatchPreludeAddresses.push(currentAddress);
			const falseTarget = current.consequentAddresses[0];
			const trueTarget = current.consequentAddresses[1];
			cases.set(state, trueTarget);
			nextDefaultState = state + 1;
			currentAddress = falseTarget;
		}
		if (cases.size === 0 || currentAddress == null) continue;
		cases.set(nextDefaultState, currentAddress);

		const exceptionRouter = inferChainedExceptionRouter(
			func,
			constants,
			switchLoad.slotIndex,
			block.address,
		);

		candidates.push({
			cases,
			roles: {
				actionRegister,
				switchSlot: switchLoad.slotIndex,
				stateEnvRegisterIndex: switchLoad.environment.index,
				exceptionHandlerSlot: exceptionRouter?.exceptionHandlerSlot ??
					-1,
				executionStatusSlot: inferExecutionStatusSlot(
					func,
					constants,
					switchLoad.slotIndex,
				),
				resumeValueSlot: inferResumeValueSlot(
					func,
					constants,
					actionRegister,
					switchLoad.environment.index,
				),
				caughtExceptionSlot: exceptionRouter?.caughtExceptionSlot ??
					-1,
				mainSwitchAddress: block.address,
				handlerIndexToState: exceptionRouter?.handlerIndexToState ??
					new Map(),
				constants,
				sequentialStates: true,
				dispatchPreludeAddresses,
			},
		});
	}

	return candidates
		.map((candidate) => ({
			candidate,
			score: scoreDispatch(candidate),
		}))
		.filter(({ score }) => score > 0)
		.toSorted((a, b) => b.score - a.score)[0]?.candidate;
}

function blockStoresConstantToSlot(
	constants: Map<number, unknown>,
	block: RawBlockLike,
	environmentRegisterIndex: number,
	slotIndex: number,
	value: number,
) {
	return block.instructions.some((instr) => {
		if (
			instr.instruction !== 'StoreToEnvironment' &&
			instr.instruction !== 'StoreNPToEnvironment'
		) return false;
		if (instr.environment?.index !== environmentRegisterIndex) return false;
		if (instr.slotIndex !== slotIndex) return false;
		const reg = rawRegister(instr.value);
		if (!reg) return false;
		return blockConstantNumber(constants, block, reg.index) === value;
	});
}

function environmentLoadComparedToConstant(
	constants: Map<number, unknown>,
	block: RawBlockLike,
) {
	const terminal = block.instructions.at(-1);
	if (terminal?.instruction !== 'JStrictEqual') return;
	if (!terminal.left || !terminal.right) return;
	const loaded = block.instructions.find((instr) =>
		instr.instruction === 'LoadFromEnvironment' &&
		instr.destination != null &&
		(instr.destination.index === terminal.left!.index ||
			instr.destination.index === terminal.right!.index)
	);
	if (loaded?.instruction !== 'LoadFromEnvironment') return;
	if (
		loaded.destination == null ||
		loaded.slotIndex == null ||
		loaded.environment == null
	) return;
	const destinationIndex = loaded.destination.index;
	const slotIndex = loaded.slotIndex;
	const environmentIndex = loaded.environment.index;
	const constantRegister = terminal.left.index === destinationIndex
		? terminal.right.index
		: terminal.left.index;
	const constant = blockConstantNumber(constants, block, constantRegister);
	if (constant == null) return;
	return {
		load: {
			register: destinationIndex,
			environmentIndex,
			slotIndex,
		},
		constant,
	};
}

function inferImmediateCompletionDispatch(
	func: IRFunction,
	scoreDispatch: DispatchScore,
	acceptImmediateCandidate: ImmediateCandidateValidator,
): StateDispatch | undefined {
	if (func.ssa._func.functionKind !== FunctionKind.NormalFunction) return;

	// Hermes LowerGeneratorFunction still wraps no-yield bodies in the generator
	// protocol prologue: it checks Executing/Completed state and stores
	// Executing before returning a done:true iterator result. There is no
	// SuspendedStart dispatch state in that shape, so synthesize state 0 from
	// the initial Executing path and let the normal SSA case collector recover
	// the body.
	const constants = new Map<number, unknown>();
	let actionRegister: number | null = null;
	for (const block of func.ssa._func.basicBlocks.values()) {
		for (const instr of block.instructions) {
			// These loops walk every instruction of every block, so they meet
			// whatever shape a restored function carries. The declared type
			// guarantees a destination here, but a function paged back in
			// through the cold store has produced one without it, and reading
			// `.index` off that cost the whole function rather than just this
			// recognition.
			if (instr.instruction === 'LoadConst') {
				const destination = rawRegisterIndex(instr.destination);
				if (destination != null) {
					constants.set(destination, instr.value);
				}
			}
			if (
				instr.instruction === 'LoadParam' && instr.parameterIndex === 1
			) {
				const destination = rawRegisterIndex(instr.destination);
				if (destination != null) actionRegister = destination;
			}
		}
	}
	if (actionRegister == null) return;

	const candidates: StateDispatch[] = [];
	for (
		const guard of func.ssa._func.basicBlocks.values() as Iterable<
			RawBlockLike
		>
	) {
		const compared = environmentLoadComparedToConstant(constants, guard);
		if (!compared || compared.constant !== 2) continue;
		const stateLoad = compared.load;
		const stateEnvRegisterIndex = stateLoad.environmentIndex;
		const stateSlot = stateLoad.slotIndex;

		const entries = [...func.ssa._func.basicBlocks.values()].filter((
			block,
		) => blockStoresConstantToSlot(
			constants,
			block as RawBlockLike,
			stateEnvRegisterIndex,
			stateSlot,
			2,
		)) as RawBlockLike[];
		for (const entry of entries) {
			const dispatch: StateDispatch = {
				cases: new Map([[0, entry.address]]),
				roles: {
					actionRegister,
					switchSlot: stateSlot,
					stateEnvRegisterIndex,
					exceptionHandlerSlot: -1,
					executionStatusSlot: stateSlot,
					caughtExceptionSlot: -1,
					mainSwitchAddress: entry.address,
					handlerIndexToState: new Map(),
					constants,
					sequentialStates: false,
				},
			};
			const recognition: StateMachineRecognition = {
				switchSlot: dispatch.roles.switchSlot,
				stateEnvRegisterIndex: dispatch.roles.stateEnvRegisterIndex,
				exceptionHandlerSlot: null,
				caughtExceptionSlot: null,
				executionStatusSlot: dispatch.roles.executionStatusSlot ?? null,
				resumeValueSlot: null,
				actionRegister,
				mainSwitchAddress: entry.address,
				constants,
				dispatch: new Map(dispatch.cases),
				handlerIndexToState: new Map(),
				sequentialStates: false,
			};
			if (!acceptImmediateCandidate(recognition, entry.address)) continue;
			candidates.push(dispatch);
		}
	}

	return candidates
		.map((candidate) => ({
			candidate,
			score: scoreDispatch(candidate),
		}))
		.filter(({ score }) => score > 0)
		.toSorted((a, b) => b.score - a.score)[0]?.candidate;
}

function inferStateDispatch(
	func: IRFunction,
	scoreDispatch: DispatchScore,
	acceptImmediateCandidate: ImmediateCandidateValidator,
): StateDispatch | undefined {
	return inferSwitchDispatch(func) ??
		inferChainedDispatch(func, scoreDispatch) ??
		inferImmediateCompletionDispatch(
			func,
			scoreDispatch,
			acceptImmediateCandidate,
		);
}

function inferImmediateSubstateControlSlots(
	func: IRFunction,
	recognition: StateMachineRecognition,
) {
	if (
		recognition.dispatch.size !== 1 ||
		recognition.executionStatusSlot !== recognition.switchSlot
	) return new Set<number>();

	const primaryStateSlots = recognitionStateControlSlots(recognition);
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
				instr.instruction === 'StoreNPToEnvironment' ||
				instr.instruction === 'StoreToEnvironment'
			) {
				if (
					instr.environment?.index !==
						recognition.stateEnvRegisterIndex
				) {
					continue;
				}
				if (typeof instr.slotIndex === 'number') {
					ensure(instr.slotIndex).stores.push({
						address: block.address,
						value: instr.value,
					});
				}
			}
			if (instr.instruction === 'LoadFromEnvironment') {
				if (
					instr.environment?.index !==
						recognition.stateEnvRegisterIndex
				) {
					continue;
				}
				if (typeof instr.slotIndex === 'number') {
					ensure(instr.slotIndex).loads.push(block.address);
				}
			}
		}
	}

	const result = new Set<number>();
	for (const [slot, info] of slots) {
		if (primaryStateSlots.has(slot)) continue;
		if (info.stores.length === 0 || info.loads.length === 0) continue;

		const storesOnlyNumericStates = info.stores.every((store) => {
			const block = func.ssa._func.basicBlocks.get(store.address) as
				| RawBlockLike
				| undefined;
			const reg = rawRegister(store.value);
			return reg != null &&
				typeof blockConstantNumber(
						recognition.constants,
						block,
						reg.index,
					) === 'number';
		});
		if (!storesOnlyNumericStates) continue;

		const loadsFeedNumericStateTests = info.loads.every((address) => {
			const block = func.ssa._func.basicBlocks.get(address) as
				| RawBlockLike
				| undefined;
			if (!block) return false;
			const load = block.instructions.find((instr) =>
				instr.instruction === 'LoadFromEnvironment' &&
				instr.slotIndex === slot &&
				instr.destination != null
			);
			if (
				load?.instruction !== 'LoadFromEnvironment' ||
				load.destination == null
			) return false;
			return constantComparedWithRegister(
				recognition.constants,
				block.instructions.at(-1),
				load.destination.index,
				block,
			) != null;
		});
		if (!loadsFeedNumericStateTests) continue;
		result.add(slot);
	}
	return result;
}

export function recognizeStateMachine(
	func: IRFunction,
	scoreDispatch: DispatchScore,
	acceptImmediateCandidate: ImmediateCandidateValidator,
): StateMachineRecognition | undefined {
	const dispatch = inferStateDispatch(
		func,
		scoreDispatch,
		acceptImmediateCandidate,
	);
	if (!dispatch) return;
	const { roles } = dispatch;
	const recognition: StateMachineRecognition = {
		switchSlot: roles.switchSlot,
		stateEnvRegisterIndex: roles.stateEnvRegisterIndex,
		exceptionHandlerSlot: roles.exceptionHandlerSlot >= 0
			? roles.exceptionHandlerSlot
			: null,
		caughtExceptionSlot: roles.caughtExceptionSlot >= 0
			? roles.caughtExceptionSlot
			: null,
		executionStatusSlot: roles.executionStatusSlot ?? null,
		resumeValueSlot: roles.resumeValueSlot ?? null,
		actionRegister: roles.actionRegister,
		mainSwitchAddress: roles.mainSwitchAddress,
		constants: roles.constants,
		dispatch: new Map(dispatch.cases),
		handlerIndexToState: roles.handlerIndexToState,
		sequentialStates: roles.sequentialStates,
		dispatchPreludeAddresses: roles.dispatchPreludeAddresses,
	};
	const extraStateControlSlots = inferImmediateSubstateControlSlots(
		func,
		recognition,
	);
	if (extraStateControlSlots.size > 0) {
		recognition.extraStateControlSlots = extraStateControlSlots;
	}
	return recognition;
}

export function stateRolesFromRecognition(
	recognition: StateMachineRecognition,
): StateRoles {
	return {
		actionRegister: recognition.actionRegister,
		switchSlot: recognition.switchSlot,
		stateEnvRegisterIndex: recognition.stateEnvRegisterIndex,
		exceptionHandlerSlot: recognition.exceptionHandlerSlot ?? -1,
		executionStatusSlot: recognition.executionStatusSlot ?? undefined,
		resumeValueSlot: recognition.resumeValueSlot ?? undefined,
		caughtExceptionSlot: recognition.caughtExceptionSlot ?? -1,
		extraStateControlSlots: recognition.extraStateControlSlots,
		mainSwitchAddress: recognition.mainSwitchAddress,
		handlerIndexToState: recognition.handlerIndexToState,
		constants: recognition.constants,
		sequentialStates: recognition.sequentialStates,
		dispatchPreludeAddresses: recognition.dispatchPreludeAddresses,
	};
}

export function recognitionStateControlSlots(
	recognition: StateMachineRecognition,
) {
	return new Set(
		[
			recognition.switchSlot,
			recognition.exceptionHandlerSlot,
			recognition.executionStatusSlot,
			recognition.resumeValueSlot,
			...(recognition.extraStateControlSlots ?? []),
		].filter((slot): slot is number => slot != null),
	);
}

export function roleStateControlSlots(roles: StateRoles) {
	return new Set(
		[
			roles.switchSlot,
			roles.exceptionHandlerSlot,
			roles.caughtExceptionSlot,
			roles.executionStatusSlot,
			roles.resumeValueSlot,
			...(roles.extraStateControlSlots ?? []),
		].filter((slot): slot is number => slot != null && slot >= 0),
	);
}
