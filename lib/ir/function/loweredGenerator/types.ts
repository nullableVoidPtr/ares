import * as t from '@babel/types';
import { BlockAddr } from '../../../hbc/disassembly/function.ts';
import type { AddressGraph } from '../../../utils/graph.ts';
import { AddressMap } from '../../../utils/map.ts';
import { SSAInstruction, SSARegister } from '../../../ssa.ts';
import type { IRBlock } from '../../ast/mod.ts';
import type { EnvironmentSiteId } from '../../../coldstore/plan.ts';

export interface StateRoles {
	actionRegister: number;
	switchSlot: number;
	stateEnvRegisterIndex: number;
	exceptionHandlerSlot: number;
	executionStatusSlot?: number;
	resumeValueSlot?: number;
	caughtExceptionSlot: number;
	extraStateControlSlots?: Set<number>;
	mainSwitchAddress: number;
	handlerIndexToState: Map<number, number>;
	constants: Map<number, unknown>;
	sequentialStates?: boolean;
	dispatchPreludeAddresses?: BlockAddr[];
}

export interface StateDispatch {
	roles: StateRoles;
	cases: Map<number, BlockAddr>;
}

export interface LoweredGeneratorModel {
	roles: StateRoles;
	dispatch: StateDispatch;
	cases: Map<number, CaseInfo>;
	order: number[];
	remap: Map<number, BlockAddr>;
	embeddedFinallySplits: EmbeddedFinallySplit[];
	preludeBody: t.Statement[];
	finalizerCopies: FinalizerCopyAnalysis;
	parentParameterAliases: Map<string, t.Expression>;
	materializedEnvironmentNames: Set<string>;
}

export interface LoweredEnvironmentAliases {
	parentEnvNames: Set<string>;
	escapingEnvNames: Set<string>;
	spillEnvSlots: Map<number, string>;
	parentEnvSlots: Map<number, t.Expression>;
	envSlots: Map<string, Map<number, t.Expression>>;
	materializedEnvSlots: Map<string, Map<number, t.Identifier>>;
	environmentSites: Map<string, EnvironmentSiteId>;
	values: Map<string, t.Expression>;
}

export interface CaseInfo {
	state: number;
	address: number;
	path: number[];
	body: t.Statement[];
	blocks?: AddressMap<CaseBlockInfo>;
	nextState: number | null;
	activeHandlerIndex: number | null;
	terminal: t.Statement;
}

export interface CaseBlockInfo {
	address: BlockAddr;
	body: t.Statement[];
	branch?: t.Expression;
	consequentAddresses: BlockAddr[];
	terminal: t.Statement | null;
	nextState?: number | null;
}

export interface FinalizerAnalysisDecline {
	state: number;
	continuations: number[];
	reason: 'multiple-continuations';
}

export interface FinalizerCopyAnalysis {
	finalizerStates: Set<number>;
	suspendedFinalizerStates: Set<number>;
	bodyStatesByFinalizerState: Map<number, number[]>;
	bodyStateStatementLimitsByFinalizerState: Map<number, Map<number, number>>;
	copyRootsByFinalizerState: Map<number, Set<number>>;
	successorRedirects: Map<number, number>;
	declines: FinalizerAnalysisDecline[];
}

export interface ProtectedStateAnalysis {
	protectedStatesByCatchState: Map<number, Set<number>>;
	protectedStatesByFinallyState: Map<number, Set<number>>;
}

export interface EmbeddedFinallySplit {
	catchState: number;
	finallyState: number;
	catchCopyStart: number;
	prefixLength: number;
}

export interface EmbeddedSplitAddresses {
	finallyContinuation: BlockAddr;
	catchCopy: BlockAddr;
	catchRemainder: BlockAddr | null;
}

export interface LoweredGeneratorBuildPlan {
	embeddedSplitByFinallyState: Map<number, EmbeddedFinallySplit>;
	embeddedSplitAddresses: Map<EmbeddedFinallySplit, EmbeddedSplitAddresses>;
	recoveredAddressesByState: Map<number, AddressMap<BlockAddr>>;
	blocks: AddressMap<IRBlock>;
	mergedBlocks: AddressGraph;
	protectedStates: ProtectedStateAnalysis;
}

export interface StateMachineRecognition {
	switchSlot: number;
	stateEnvRegisterIndex: number;
	exceptionHandlerSlot: number | null;
	caughtExceptionSlot: number | null;
	executionStatusSlot: number | null;
	resumeValueSlot?: number | null;
	extraStateControlSlots?: Set<number>;
	actionRegister: number;
	mainSwitchAddress: BlockAddr;
	constants: Map<number, unknown>;
	dispatch: Map<number, BlockAddr>;
	handlerIndexToState: Map<number, number>;
	sequentialStates?: boolean;
	dispatchPreludeAddresses?: BlockAddr[];
}

export type EnvSlotKind =
	| { kind: 'stateControl' }
	| { kind: 'constant'; value: unknown }
	| { kind: 'param'; index: number }
	| { kind: 'local'; name: string; slot: number };

export type TerminalValue =
	| { kind: 'literal'; value: unknown }
	| { kind: 'register'; register: SSARegister }
	| null;

export type CaseTerminal =
	| { kind: 'yield'; value: TerminalValue }
	| { kind: 'return'; value: TerminalValue }
	| { kind: 'iteratorResult'; value: TerminalValue }
	| { kind: 'throw'; value: TerminalValue };

export interface GeneratorCaseModel {
	state: number;
	entry: BlockAddr;
	path: BlockAddr[];
	instructions: SSAInstruction[];
	blocks: AddressMap<GeneratorCaseBlockModel>;
	terminal: CaseTerminal;
	nextState: number | null;
	rawNextState: number | null;
	activeHandlerIndex: number | null;
	activeHandlerState: number | null;
	readsCaughtException: boolean;
	pairedFinallyState: number | null;
}

export interface GeneratorCaseBlockModel {
	address: BlockAddr;
	instructions: SSAInstruction[];
	consequentAddresses: BlockAddr[];
	terminal: CaseTerminal | null;
	nextState?: number | null;
}

export interface SSAGeneratorModel {
	recognition: StateMachineRecognition;
	cases: Map<number, GeneratorCaseModel>;
	envSlots: Map<number, EnvSlotKind>;
	emissionOrder: number[];
}

export type RawInstructionLike = {
	instruction: string;
	functionLocalOffset?: number;
	destination?: { index: number };
	environment?: { index: number };
	parentEnv?: { index: number };
	function?: unknown;
	left?: { index: number };
	right?: { index: number };
	value?: unknown;
	exception?: unknown;
	object?: unknown;
	objectValueBufferIndex?: number;
	shapeTableIndex?: number;
	noOfStaticElements?: number;
	objectKeyBufferIndex?: number;
	slotIndex?: number;
	levelIndex?: number;
	parameterIndex?: number;
};

export type RawBlockLike = {
	address: BlockAddr;
	instructions: RawInstructionLike[];
	consequentAddresses: BlockAddr[];
};

export interface ChainedExceptionRouter {
	exceptionHandlerSlot: number;
	caughtExceptionSlot: number;
	handlerIndexToState: Map<number, number>;
}

export type RawEnvironmentRef =
	| { kind: 'closure'; depth: number }
	| { kind: 'local' };
