import type { ImmutableCFG } from '../immutableCFG.ts';
import type { CFGAnalyses } from '../algorithms/mod.ts';
import { AddressMap } from '../../../../utils/map.ts';
import type { IRFunction } from '../../mod.ts';
import {
	type DelegateYieldDescriptorInfo,
	recoverDelegateYieldDescriptors,
} from './delegateYield.ts';
import { type PhiDescriptorInfo, recoverPhiDescriptors } from './phis.ts';
import {
	recoverSwitchDescriptors,
	type SwitchDescriptorInfo,
} from './switches.ts';
import {
	type ExceptionDescriptorInfo,
	recoverExceptionDescriptors,
} from './exceptions.ts';
import {
	type DestructuringDescriptorInfo,
	recoverDestructuringDescriptors,
} from './destructuring.ts';
import {
	type CFGCompatibilityTelemetry,
	createCFGCompatibilityTelemetry,
} from '../compatibility.ts';
export interface CFGDescriptors {
	phis: PhiDescriptorInfo;
	switches: SwitchDescriptorInfo;
	exceptions: ExceptionDescriptorInfo;
	delegateYields: DelegateYieldDescriptorInfo;
	destructuring: DestructuringDescriptorInfo;
	/** Opt-in-by-consumer counters; never consulted for structuring decisions. */
	compatibility?: CFGCompatibilityTelemetry;
}

export function recoverDescriptors(
	cfg: ImmutableCFG,
	func?: IRFunction,
	analyses?: CFGAnalyses,
): CFGDescriptors {
	return {
		phis: recoverPhiDescriptors(cfg),
		switches: recoverSwitchDescriptors(cfg),
		exceptions: recoverExceptionDescriptors(cfg, func),
		delegateYields: analyses
			? recoverDelegateYieldDescriptors(cfg, analyses)
			: {
				delegates: [],
				delegateByPrelude: new AddressMap(),
				delegateByHeader: new AddressMap(),
			},
		destructuring: recoverDestructuringDescriptors(cfg),
		compatibility: createCFGCompatibilityTelemetry(),
	};
}

export * from './delegateYield.ts';
export * from './exceptions.ts';
export * from './phis.ts';
export * from './switches.ts';
export * from './destructuring.ts';
