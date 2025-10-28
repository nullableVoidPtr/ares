import { BlockAddr } from '../disassembly/function.ts';

export default function mapEachBlocks<B, R>(basicBlocks: Map<BlockAddr, B>, callback: () => R): Map<BlockAddr, R> {
	const map = new Map<BlockAddr, R>();
	for (const addr of basicBlocks.keys()) {
		map.set(addr, callback());
	}

	return map;
}