import { assert } from 'node:console';
import { BlockAddr } from '../../../disassembly/function.ts';
import { AddressGraph } from '../../../utils/graph.ts';
import { AddressMap } from '../../../utils/map.ts';
import { AddressSet } from '../../../utils/set.ts';
import { LiftError } from '../../error.ts';
import { IRFunction } from '../mod.ts';
import { FinallyId, HandlerId } from './mod.ts';

export function structureTry(func: IRFunction) {
	if (func._exceptionHandlers.length === 0) return;


	// TODO: first construct finallyrecords from records where ranges.length == 1 and
	const protectedCatches = new AddressGraph();
	for (const { catchAddress } of func.exceptions.values()) {
		const potentialOuterRecords = new AddressSet(
			func.exceptions.values().filter(
				r => r.catchAddress !== catchAddress && r.protectedBlocks.has(catchAddress)
			).map(r => r.catchAddress)
		);
		if (potentialOuterRecords.size == 0) continue;

		protectedCatches.set(catchAddress, potentialOuterRecords);
	}

	const unprotectedCatches = new AddressSet(func.exceptions.keys()).difference(protectedCatches);
	console.log("protected", protectedCatches);
	console.log("unprotected", unprotectedCatches);

	const surroundingFinallies = new AddressGraph<HandlerId, FinallyId>();
	const potentialCatchFinallies = new AddressMap<FinallyId>();
	const finallyToChildren = new AddressGraph<FinallyId, FinallyId>();
	let changed = false;
	do {
		changed = false;
		const toRemove = new AddressSet();
		for (const [protectedCatch, targets] of protectedCatches) {
			if (targets.size !== 1) continue;

			for (const potentialFinally of targets) {
				for (const [innerHandler, innerTargets] of protectedCatches) {
					if (!innerTargets.has(protectedCatch)) continue;
					if (!innerTargets.has(potentialFinally)) continue;

					innerTargets.delete(protectedCatch);
					innerTargets.delete(potentialFinally);

					changed = true;

					surroundingFinallies.addEdge(innerHandler, potentialFinally);
					if (innerTargets.size === 0) toRemove.add(innerHandler);
				}

				potentialCatchFinallies.set(protectedCatch, potentialFinally);

				const surroundingFinally = (surroundingFinallies.get(
					protectedCatch,
				) ?? new AddressSet()).intersection(
					surroundingFinallies.get(
						potentialFinally,
					) ?? new AddressSet()
				);

				if (surroundingFinally.size === 1) {
					finallyToChildren.addEdge([...surroundingFinally][0], potentialFinally)
				}
			}

			toRemove.add(protectedCatch);
		}

		for (const addr of toRemove) {
			protectedCatches.delete(addr);
		}
	} while (changed);

	console.log("protected", protectedCatches);
	console.log(finallyToChildren);
	/*
	60a => { 385 }
	385 => { 139 }
	BUT NOT 2c => { 151 }
	ee 241 33a 481 536 5d7
	*/


	// TODO: construct finally-catch tree from protectedCatches
		/*
		const finallyRanges = rangeToHandlers.get(recordForCatch.catchAddress);
		if (!finallyRanges) continue;

		// TODO: change to iterating through potentialOuterRecords
		for (const [catchTrailer, canonicalFinallies] of finallyRanges) {
			if (canonicalFinallies.size > 1) {
				// TODO: do we need to handle this?
				continue;
			}

			const canonical = [...canonicalFinallies][0];

			type PreRecord = {
				ends: AddressSet;
				innerTargets: AddressSet;
			};
			let potentialTryStarts = new Map<BlockAddr, PreRecord>();
			console.log(recordForCatch.catchAddress.toString(16), new Set(recordForCatch.ranges.map(r => r.start)).size);
			
			const starts = new Set(recordForCatch.ranges.map(r => r.start));
			for (const start of starts) {
				const ends = new AddressSet();
				let allTargets = new AddressSet();
				for (const [end, targets] of rangeToHandlers.get(start)!) {
					ends.add(end);
					allTargets = new AddressSet(allTargets.union(targets));
				}

				if (!allTargets.has(recordForCatch.catchAddress)) continue;
				if (!allTargets.has(canonical)) continue;

				allTargets.delete(recordForCatch.catchAddress);
				allTargets.delete(canonical);

				potentialTryStarts.set(start, {
					ends,
					innerTargets: allTargets,
				});
			}

			if (potentialTryStarts.size == 0) debugger;
			console.log("\t", canonical.toString(16));
			for (const [start, values] of potentialTryStarts) {
				console.log("\t\t", start, values);
			}
		}
	}

	// Identify finallies first
	// simplyTryFinally
	// [start=0x71, end=0x7a, target=0x93] target: catch
	// [start=0x71, end=0x7a, target=0xc5] target: finally
	// [start=0x93, end=0xab, target=0xc5] target: finally
	// tryCatch.test
	// [start=0x199, end=0x1ad, target=0x1f3c]
	// [start=0x199, end=0x1ad, target=0x22c0]
	// [start=0x1f3c, end=0x1f88, target=0x22c0]
	// [start=0x4f, end=0x70, target=0x447]
	// [start=0x4f, end=0x75, target=0x19bf]
	// [start=0x447, end=0x4a1, target=0x19bf]

	// nestedTry
	// inner = new Set(records.get(107).protectedBlocks)
	// inner.add(107)
	// outer = records.get(133)
	// isSubset(outer, inner) === true

	// TODO: for any catches without a finally - check for simple try-finally
	/*
	const plainCatches = new Set<BlockAddr>();
	const canonicalFinallies = new Map<BlockAddr, BlockAddr>();
	let changed = false;
	do {
		changed = false;

		for (const catchAddr of records.keys()) {
			if (plainCatches.has(catchAddr)) continue;
			if (canonicalFinallies.has(catchAddr)) continue;

			let finallyAddrs: BlockAddr[] = [];
			for (const [finallyAddr, {protectedBlocks}] of records) {
				if (finallyAddr === catchAddr) continue;
				if (!protectedBlocks.has(catchAddr)) continue;

				finallyAddrs.push(finallyAddr);
			}

			if (finallyAddrs.length > 1) {
				const knownFinallies = new Set(canonicalFinallies.values());
				finallyAddrs = finallyAddrs.filter(addr => !knownFinallies.has(addr));
			}

			if (finallyAddrs.length === 0) {
				plainCatches.add(catchAddr);
			} else if (finallyAddrs.length == 1) {
				canonicalFinallies.set(catchAddr, finallyAddrs[0]);
				changed = true;
			}
		}
	} while (changed);

	for (const [catchAddr, finallyAddr] of canonicalFinallies) {
		const uncommonProtected = records.get(finallyAddr)!.protectedBlocks.symmetricDifference(records.get(catchAddr)!.protectedBlocks);
		uncommonProtected.delete(catchAddr);
		if (uncommonProtected.size === 1) {
			const potentialTermination = uncommonProtected.values().next().value!;
			if (func.ssa.basicBlocks.get(potentialTermination!)?.consequentAddresses?.length === 0) continue;
		}

		console.log(records.get(catchAddr)!.toString(), records.get(finallyAddr)!.toString());
	}
	console.log(canonicalFinallies.size);

	/*
	const potentialTrys = new Set<BlockAddr>();
	const potentialFinallies = new Set<BlockAddr>();

	const allCatchAddrs = new Set(records.keys());

	for (const { protectedRanges } of records.values()) {
		if (new Set(protectedRanges.keys()).intersection(allCatchAddrs).size === 0) {
			//TODO
			continue;
		}
	}
	*/

	// TODO:
	// check: finally blocks have a TryRecord protecting only the body and catch blocks of the actual TryRecord
	debugger;
}

export function findFinallyBlocks(func: IRFunction) {
	if (func.exceptionHandlers.length === 0) return;

	// TODO: Catch deduplication here
	// Gather every block which may have a catch
	const regionHandlers = new AddressMap<Map<BlockAddr, AddressSet>>();
	const catchFlows = new AddressMap<{ tryStart: BlockAddr, tryEnd: BlockAddr }[]>();
	for (const { tryStart, tryEnd, catchOffset } of func.ssa.exceptionHandlers) {
		let startMap = regionHandlers.get(tryStart);
		if (!startMap) {
			regionHandlers.set(tryStart, startMap = new Map());
		}

		let handlers = startMap.get(tryEnd);
		if (!handlers) {
			startMap.set(tryEnd, handlers = new AddressSet());
		}

		handlers.add(catchOffset);

		let incomingRegions = catchFlows.get(catchOffset);
		if (!incomingRegions) {
			catchFlows.set(catchOffset, incomingRegions = []);
		}

		incomingRegions.push({ tryStart, tryEnd });
	}

	// K: Canonical catch block V: { [Child catch address]: Finally trailer start }
	const finallyBlocks = new AddressMap<Map<BlockAddr, BlockAddr>>();
	const yieldRetToFinally = new AddressMap<Set<BlockAddr>>();
	for (const innerCatchAddr of catchFlows.keys()) {
		const catchEnds = regionHandlers.get(innerCatchAddr);
		if (!catchEnds) continue;

		for (const [innerCatchEnd, parentCatches] of catchEnds) {
			for (const parentCatchAddr of parentCatches) {
				let catchAddr = innerCatchAddr;
				let catchTrailerAddr = innerCatchEnd;
				let finallyCatchAddr = parentCatchAddr;

				if (parentCatches.size > 1 && regionHandlers.has(parentCatchAddr)) {
					const surroundingCatch = parentCatchAddr;
					const surroundingCatchEnds = regionHandlers.get(surroundingCatch);
					if (surroundingCatchEnds?.size !== 1) {
						throw new LiftError('Expected a catch block');
					}

					const [surroundingCatchTrailer, grandparentCatches] = surroundingCatchEnds.entries().next().value!;
					if (grandparentCatches.size !== 1) {
						throw new LiftError('Expected a finally block to handle catch');
					}

					const outerCatchAddr = grandparentCatches.values().next().value!;

					catchAddr = surroundingCatch;
					catchTrailerAddr = surroundingCatchTrailer;
					finallyCatchAddr = outerCatchAddr;
				}

				let finallyCopies = finallyBlocks.get(finallyCatchAddr);
				if (!finallyCopies) finallyBlocks.set(finallyCatchAddr, finallyCopies = new Map());
				if (finallyCopies.has(catchAddr)) {
					assert(finallyCopies.get(catchAddr) === catchTrailerAddr, `${finallyCopies.get(catchAddr)} === ${catchTrailerAddr}`);
				} else {
					finallyCopies.set(catchAddr, catchTrailerAddr);
				}

				if (func.returnBlocks.has(catchTrailerAddr)) {
					let yieldRetSet = yieldRetToFinally.get(catchTrailerAddr);
					if (!yieldRetSet) yieldRetToFinally.set(catchTrailerAddr, yieldRetSet = new Set());
					yieldRetSet.add(finallyCatchAddr)
				}
			}
		}
	}

	// expect
	// c5 (canonical)
	//	93, ab (catch trailer)
	//	41?, 58
	//  71?, 7a
	for (const [k, v] of finallyBlocks) {
		console.log(k.toString(16));
		for (const [kk, vv] of v) {
			console.log("\t" + kk.toString(16) + ", " + vv.toString(16));
		}
	}

	debugger;

	// const tryInfo: { tryStart: BlockAddr; catchStart: BlockAddr; finallyStart?: BlockAddr}[] = [];

	/*
	if (this.isGenerator) {
		console.log(this.yieldEndBlocks)
		for (const [tryStart, ends] of regionHandlers) {
			try {
				if (ends.size !== 2) continue;
			
				console.log(tryStart, ends);

				const regionCatches = new Map([...ends].map(([tryEnd, catches]) => {
					if (catches.size !== 1) throw new LiftError('bruh');
					return [tryEnd, catches.values().next().value!];
				}));

				console.log(regionCatches);
			} catch {
				continue;
			}
		}
		debugger;
	}
	*/
}