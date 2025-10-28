import { BlockAddr, FunctionExceptionHandler } from '../disassembly/function.ts';
import { exceptionHandlersByAddress } from './exceptions.ts';
import mapEachBlocks from './mapEachBlock.ts';
import { setEquals } from './set.ts';

type Dominator = BlockAddr;
export default class DominanceGraph<T extends { basicBlocks: Map<BlockAddr, { consequentAddresses: BlockAddr[]; }>; exceptionHandlers: FunctionExceptionHandler[]; }> {
	predecessorMap!: Map<BlockAddr, Set<BlockAddr>>;
	successorMap!: Map<BlockAddr, Set<BlockAddr>>;
	
	mapEdges(func: T) {
		this.predecessorMap = mapEachBlocks(func.basicBlocks, () => new Set<BlockAddr>());
		this.successorMap = mapEachBlocks(func.basicBlocks, () => new Set<BlockAddr>());

		for (const [addr, block] of func.basicBlocks) {
			const blockSuccs = new Set([
				...block.consequentAddresses,
				...exceptionHandlersByAddress(addr, func.exceptionHandlers).map(({ catchOffset }) => catchOffset)
			]);

			this.successorMap.set(addr, blockSuccs);
			for (const s of blockSuccs) {
				this.predecessorMap.get(s)!.add(addr);
			}
		}
	}

	predecessorsOf(addr: BlockAddr) {
		return this.predecessorMap.get(addr)!;
	}

	successorsOf(addr: BlockAddr) {
		return this.successorMap.get(addr)!;
	}

	dominatorMap!: Map<BlockAddr, Set<Dominator>>;
	dominanceMap!: Map<Dominator, Set<BlockAddr>>;
	dominanceFrontierMap!: Map<BlockAddr, Set<BlockAddr>>;

	analyseDominators(basicBlocks: T['basicBlocks'], entryAddr: BlockAddr = 0) {
		this.dominatorMap = mapEachBlocks(basicBlocks, () => new Set<BlockAddr>(basicBlocks.keys()));
		this.dominatorMap.set(entryAddr, new Set([entryAddr]));

		let changed = true;
		while (changed) {
			changed = false;
			for (const [addr, predecessors] of this.predecessorMap) {
				if (addr === entryAddr) continue;
				if (predecessors.size === 0) continue;

				let newDominators = new Set(basicBlocks.keys());
				for (const p of predecessors) {
					newDominators = newDominators.intersection(this.dominatorMap.get(p)!);
				}
				newDominators.add(addr);

				const old = this.dominatorMap.get(addr)!;
				if (!setEquals(old, newDominators)) {
					this.dominatorMap.set(addr, new Set(newDominators));
					changed = true;
				}
			}
		}

		this.dominanceMap = mapEachBlocks(basicBlocks, () => { return new Set<BlockAddr>() });
		for (const [key, value] of this.dominatorMap) {
			for (const v of value) {
				this.dominanceMap.get(v)!.add(key);
			}
		}

		this.dominanceFrontierMap = mapEachBlocks(basicBlocks, () => new Set<BlockAddr>());
		for (const block of this.dominatorMap.keys()) {
			const dominatedSuccessors = new Set<BlockAddr>(
				[...this.dominatedBy(block)].flatMap(domi => [...this.successorsOf(domi)])
			).difference(this.strictlyDominatedBy(block));
			dominatedSuccessors.delete(block);
			this.dominanceFrontierMap.set(block, dominatedSuccessors,);
		}
		this.makeDominatorTree();
	}

	dominatorTree!: Map<BlockAddr, Set<BlockAddr>>;

	makeDominatorTree() {
		this.dominatorTree = new Map<BlockAddr, Set<BlockAddr>>();

		const strictDominanceMap = new Map<BlockAddr, Set<BlockAddr>>(
			[...this.dominanceMap.keys()].map(block => [block, this.strictlyDominatedBy(block)])
		);
		for (const [block, strictlyDominated] of strictDominanceMap) {
			this.dominatorTree.set(block, strictlyDominated.difference(new Set(
				Array.from(strictlyDominated).flatMap((child) => [...strictDominanceMap.get(child)!])
			)));
		}
	}

	dominatorsOf(addr: BlockAddr) {
		return new Set(this.dominatorMap.get(addr));
	}

	dominatedBy(addr: BlockAddr) {
		return new Set(this.dominanceMap.get(addr));
	}

	strictlyDominatedBy(addr: BlockAddr) {
		const set = new Set(this.dominanceMap.get(addr));
		set.delete(addr);
		return set;
	}
	
	dominanceFrontierOf(addr: BlockAddr) {
		return new Set(this.dominanceFrontierMap.get(addr));
	}
	
	immediatelyDominatedBy(addr: BlockAddr) {
		return new Set(this.dominatorTree.get(addr));
	}

	constructor(func: T) {
		this.mapEdges(func);
		this.analyseDominators(func.basicBlocks);
	}
}
