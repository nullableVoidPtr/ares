import * as t from '@babel/types';
import {
	BigIntRef,
	FunctionRef,
	Instruction,
	StringRef,
} from '../../hbc/disassembly/instruction.ts';
import { BlockAddr } from '../../hbc/disassembly/function.ts';
import { SerializedLiteralValue } from '../../parser/file.ts';
import { AddressSet } from '../../utils/set.ts';
import type { Environment } from '../environment.ts';
import type { SSARegister } from '../../ssa.ts';
import type { StorageLocation } from './alias.ts';

export type LiftedExtra = Partial<{
	parentFunctionId: number;
	address: number;
	instruction: Instruction['instruction'];

	isBuiltin: boolean;
	isNonVolatile: boolean;
	isDeclaredGlobal: boolean;
	// Names a global the function reads. Composition collects these so
	// `global.x` can be unqualified back to `x`; the intrinsic-level global fold
	// sets it too, and a recovered `global.x++` must register the name the same
	// way or the member survives into the output.
	isReferencedGlobal: boolean;
	isHomeObject: boolean;
	isLocalEnvironment: boolean;
	localEnvironment: Environment;

	// Marks a Phi-derived value that an IR-level pass recognised as a contained
	// conditional-merge region (triangle/diamond). The actual fold into
	// ??/||/&&/?./ternary is deferred until the conditionally-computed RVal — which
	// may span several low-level IR statements — has collapsed to a single expression.
	// See markPotentialConditionalPhis (cfg) and foldConditionalValuesInBody (phi).
	isPotentialConditionalValue: boolean;
	// Keeps an SSA phi destination alive while its declaration and edge
	// assignments still reside in separate IR blocks.
	preserveAcrossBlocks: boolean;
	// Records the exact SSA names merged by a Phi that has already been lowered
	// to an accumulator. Later Phis over the same incoming values can reuse that
	// accumulator instead of referring to a pattern binding outside its scope.
	liftedPhiSources: string[];

	// The SSA register this value node was lifted from (set on register-use identifiers
	// by registerAsIdentifier). Lets passes test "same SSA value" by identity rather than
	// by the textual rN_M name — e.g. chaining consecutive stores of one register into a
	// single assignment chain. See chainSharedRegisterAssignmentsInBody.
	sourceRegister: SSARegister;
	// The function instance owning `sourceRegister`. Stored as one scalar rather
	// than repeating a full register StorageLocation object on every identifier;
	// `locationOf` combines the two fields on demand.
	bindingOwnerFunctionId: number;
	// Marks registers allocated by recovered environment mem2reg. Their incoming
	// values may be parameters or arbitrary expressions, so downstream cleanup
	// must use origin metadata rather than infer provenance from rN_M spelling.
	recoveredEnvironmentSSA: boolean;
	// Origin of a local introduced to carry one lowered-generator environment
	// slot across reconstructed state-machine cases.
	recoveredEnvironmentSlot: {
		environmentName: string;
		slot: number;
	};
	// Marks a residual non-escaping environment slot lowered to an ordinary
	// mutable local after generator CFG recovery.
	recoveredEnvironmentLocal: boolean;
	// Provenance for values supplied by LoadParam(2) when a lowered generator
	// resumes after a suspension.
	loweredGeneratorResumeValue: boolean;
	// Original iterator state bindings consumed by a recovered for-of loop.
	// Used only to prove that an enclosing IteratorClose/rethrow handler is the
	// protocol cleanup now represented by the structured loop.
	recoveredIteratorNames: string[];
	// Original async iterator binding consumed by a recovered for-await loop.
	recoveredAsyncIteratorNames: string[];

	// The storage location this node denotes, where lifting knew it. Set on
	// parameter expressions by IRFunction.getParam and on the `arguments[k]`
	// form by the LoadParam case, so `this`, `_param_<fn>_<i>_` and
	// `arguments[k]` all answer as the parameters they are rather than only the
	// spelling that happens to match /^_param_\d+_\d+_$/. Plain data, so it
	// survives cloneNode's shallow extra copy and the cold store's msgpackr
	// encoding. See lib/ir/ast/alias.ts.
	storageLocation: StorageLocation;

	// Original SSA destination for a lifted member read. Stored on the member key
	// as well as the expression so rewritten side-effect-only reads can still use
	// the real temp binding when folded into object destructuring.
	memberReadDestination: SSARegister;

	objectShapeKeys: SerializedLiteralValue[];
	// Marks `{ ...source }` produced from the zero-exclusion form of
	// HermesInternal.copyDataProperties. Empty/rest-only object destructuring
	// needs this provenance after construction inlining has erased the builtin.
	copyDataPropertiesSpread: boolean;

	ref: StringRef | FunctionRef | BigIntRef;

	consumed: boolean;
}>;
export type LiftedAST<T extends t.Node> = Pick<T, Exclude<keyof T, 'extra'>> & {
	extra?: LiftedExtra;
};

export interface IRBlock {
	address: BlockAddr;
	body: LiftedAST<t.Statement>[];
	branch?: LiftedAST<t.Expression>;
	consequentAddresses: BlockAddr[];
	kind?: 'normal' | 'synthetic' | 'catch' | 'finally' | 'generatorCase';
	sourceAddresses?: AddressSet;
	terminalKind?: 'fallthrough' | 'return' | 'throw' | 'break' | 'continue';
	protectedBy?: BlockAddr;
	handlerFor?: AddressSet;
	syntheticReason?: string;
	generatorState?: number;
	activeHandlerState?: number | null;
	pairedFinallyState?: number | null;
	recoveredFinalizerOwner?: BlockAddr;
	recoveredFinalizerRole?:
		| 'canonical'
		| 'continuation'
		| 'catchCopy'
		| 'catchRemainder';
}

export function getIRInstruction(
	node: LiftedAST<t.Node>,
): Instruction['instruction'] | null {
	return node.extra?.instruction ?? null;
}

export function isFromIRCall(node: LiftedAST<t.Node>): boolean {
	const instruction = getIRInstruction(node);
	if (!instruction) return false;

	return [
		'Call',
		'Construct',
		'CallBuiltin',
	].includes(instruction);
}

export function isFromIRCreateClass(node: LiftedAST<t.Node>): boolean {
	if (node.extra?.isHomeObject) return true;

	const instruction = getIRInstruction(node);
	if (!instruction) return false;

	return [
		'CreateBaseClass',
		'CreateDerivedClass',
	].includes(instruction);
}
