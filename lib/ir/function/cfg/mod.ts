export {
	capturePlainObjectProjectionSources,
	objectRestProtocolBindingNames,
	recordResidualObjectRestTelemetry,
	recoverGuardedObjectDestructuring,
	reduceIteratorDestructuringDefaults,
	reduceIteratorDestructuringSequence,
	reduceNestedRecoveredDestructuring,
	reduceProtectedArrayDestructuring,
	reduceSequentialArrayDestructuring,
	reduceSequentialObjectDestructuring,
} from './destructuring.ts';
export { reduceDirectEvalDiamonds } from './directEval.ts';
export { reduceSequence, reduceSharedSequenceEdge } from './linear.ts';
export { reduceNaturalLoop } from './loops.ts';
export {
	reduceGuardedBooleanPhiPredicate,
	reduceOrChain,
	reducePredicateGuardChains,
	reduceSimpleIf,
} from './predicates.ts';
export { reduceSwitch } from './switch.ts';
export {
	reduceDanglingGuardTail,
	reduceInlineTerminal,
	reduceMergedGuardPhiTerminal,
	reduceNullishDefaultReturnPhi,
	reduceSharedAlternateGuard,
	reduceSharedGuardedPrelude,
	reduceSharedLeadingPhi,
	reduceSharedTerminalPhi,
} from './terminals.ts';
export { reduceTryCatch } from './tryCatch.ts';
export { reduceArgumentsCopyRest } from './restParameters.ts';
export { reduceSideEffectOnlyOverflowDefault } from './sideEffectParameters.ts';
