import { BlockAddr, FunctionExceptionHandler } from '../hbc/disassembly/function.ts';
import { exceptionHandlersByAddress } from '../hbc/utils/exceptions.ts';
import { AddressGraph } from './graph.ts';
import { AddressSet } from './set.ts';

type Dominator = BlockAddr;
export default class DominanceGraph<T extends { basicBlocks: Map<BlockAddr, { consequentAddresses: BlockAddr[]; }>; exceptionHandlers: FunctionExceptionHandler[]; }> {
	predecessorMap!: AddressGraph;
	successorMap!: AddressGraph;
	
	mapEdges(func: T) {
		this.predecessorMap = AddressGraph.fromBasicBlocks(func.basicBlocks);
		this.successorMap = AddressGraph.fromBasicBlocks(func.basicBlocks);

		for (const [addr, block] of func.basicBlocks) {
			const blockSuccs = new AddressSet([
				...block.consequentAddresses,
				...exceptionHandlersByAddress(addr, func.exceptionHandlers).map(({ catchOffset }) => catchOffset)
			]);

			this.successorMap.set(addr, blockSuccs);
			for (const s of blockSuccs) {
				this.predecessorMap.addEdge(s, addr);
			}
		}
	}

	predecessorsOf(addr: BlockAddr) {
		return this.predecessorMap.get(addr)!;
	}

	successorsOf(addr: BlockAddr) {
		return this.successorMap.get(addr)!;
	}

	dominatorMap!: AddressGraph<BlockAddr, Dominator>;
	dominanceMap!: AddressGraph<Dominator, BlockAddr>;
	dominanceFrontierMap!: AddressGraph;

	analyseDominators(basicBlocks: T['basicBlocks'], entryAddr: BlockAddr = 0) {
		this.dominatorMap = <AddressGraph>AddressGraph.mapEachBlock(basicBlocks, () => new AddressSet<BlockAddr>(basicBlocks.keys()));
		this.dominatorMap.set(entryAddr, new AddressSet([entryAddr]));

		let changed = true;
		while (changed) {
			changed = false;
			for (const [addr, predecessors] of this.predecessorMap) {
				if (addr === entryAddr) continue;
				if (predecessors.size === 0) continue;

				let newDominators = new AddressSet(basicBlocks.keys());
				for (const p of predecessors) {
					newDominators = newDominators.intersection(this.dominatorMap.get(p)!);
				}
				newDominators.add(addr);

				const old = this.dominatorMap.get(addr)!;
				if (!old.equals(newDominators)) {
					this.dominatorMap.set(addr, newDominators);
					changed = true;
				}
			}
		}

		this.dominanceMap = AddressGraph.fromBasicBlocks(basicBlocks);
		for (const [key, value] of this.dominatorMap) {
			for (const v of value) {
				this.dominanceMap.get(v)!.add(key);
			}
		}

		this.dominanceFrontierMap = AddressGraph.fromBasicBlocks(basicBlocks);
		for (const block of this.dominatorMap.keys()) {
			const dominatedSuccessors = new AddressSet(
				[...this.dominatedBy(block)].flatMap(domi => [...this.successorsOf(domi)])
			).difference(this.strictlyDominatedBy(block));
			dominatedSuccessors.delete(block);
			this.dominanceFrontierMap.set(block, dominatedSuccessors,);
		}
		this.makeDominatorTree();
	}

	dominatorTree!: AddressGraph;

	makeDominatorTree() {
		this.dominatorTree = new AddressGraph();

		const strictDominanceMap = new AddressGraph(
			[...this.dominanceMap.keys()].map(block => [block, this.strictlyDominatedBy(block)])
		);
		for (const [block, strictlyDominated] of strictDominanceMap) {
			this.dominatorTree.set(block, strictlyDominated.difference(new AddressSet(
				Array.from(strictlyDominated).flatMap((child) => [...strictDominanceMap.get(child)!])
			)));
		}
	}

	dominatorsOf(addr: BlockAddr) {
		return new AddressSet(this.dominatorMap.get(addr));
	}

	dominatedBy(addr: BlockAddr) {
		return new AddressSet(this.dominanceMap.get(addr));
	}

	strictlyDominatedBy(addr: BlockAddr) {
		const set = new AddressSet(this.dominanceMap.get(addr));
		set.delete(addr);
		return set;
	}
	
	dominanceFrontierOf(addr: BlockAddr) {
		return new AddressSet(this.dominanceFrontierMap.get(addr));
	}
	
	immediatelyDominatedBy(addr: BlockAddr) {
		return new AddressSet(this.dominatorTree.get(addr));
	}

	constructor(func: T) {
		this.mapEdges(func);
		this.analyseDominators(func.basicBlocks);
	}
}
