import { SSAFunction, SSARegister } from '../ssa.ts';
import { BlockAddr } from '../hbc/disassembly/function.ts';
import { isStringRef } from '../hbc/disassembly/instruction.ts';
import { HBCFile } from '../parser/file.ts';
import { exceptionHandlersByAddress } from '../hbc/utils/exceptions.ts';
import { AddressSet } from './set.ts';
import { AddressMap } from './map.ts';
import { AddressGraph } from './graph.ts';

function r(reg: SSARegister) {
	return `r${reg.index}.${reg.version}`;
}

function blockName(addr: BlockAddr) {
	return `block_${addr.toString().toUpperCase()}`
}

function regionName(addr: BlockAddr) {
	return `cluster_try_${addr.toString().toUpperCase()}`
}

export default function visualiseSSA(func: SSAFunction, file?: HBCFile) {
	let graph = 'digraph G {\n';

	graph += [
		'mclimit=1.5;',
		'node [shape=box];',
		'rankdir=TB;',
		'ordering=out;',
		'compound=true;',
	].map(a => `\t${a}\n`).join('');
	
	/*
	for (const [addr, block] of func.ssaBasicBlocks) {
		const text = block.ssaInstructions.map(instr => {
			if (instr.instruction == 'Phi') {
				return instr.instruction + ' ' + r(instr.destination) + ' ' + instr.sources.values().map(r);
			}
			return instr.instruction + ' ' + [...Object.entries(instr.defs), ...Object.entries(instr.uses)].map(([name, reg]) => {
				if (Array.isArray(reg)) {
					return name + ': [' + reg.map(r) + ']';
				}
				return name + ': ' + r(reg);
			}).join(', ');
		}).join('\\n')
		graph += `\tblock_${addr} [label="${text.replaceAll('"', '\\"')}"];\n`;
	}
	*/

	type Cluster = {
		nodes: string[];
		children: AddressMap<Cluster>;
		catchHandlers: AddressSet;
	}
	const clusters = new AddressMap<Cluster>();
	const nestedClusters = new AddressGraph();
	for (const [addr, block] of func.basicBlocks) {
		const text = block.ssaInstructions.map(instr => {
			if (instr.instruction == 'Phi') {
				return instr.instruction + ' ' + r(instr.destination) + ' ' + instr.sources.values().map(r);
			}
			return instr.instruction + ' ' + [
				...[...Object.entries(instr.defs), ...Object.entries(instr.uses)].map(([name, reg]) => {
					if (Array.isArray(reg)) {
						return name + ': [' + reg.map(r) + ']';
					}
					return name + ': ' + r(reg);
				}),
				...Object.entries(instr).flatMap(([key, value]) => {
					if (['instruction', 'defs', 'uses', 'functionLocalOffset', 'type', 'length'].includes(key)) return [];
					if (key in instr.defs || key in instr.uses) return [];

					let repr = value.toString();
					if (file) {
						if (isStringRef(value)) {
							repr = `"${file.getString(value.stringTableIndex).replaceAll('"', '\"')}"`
						}
					}

					return [key + ': ' + repr];
				}),
			].join(', ');
		}).join('\\l');
		const node = `\t${blockName(addr)} [label="${text.replaceAll('"', '\\"')}"];\n`;

		const exceptionHandlers = exceptionHandlersByAddress(block.address, func.exceptionHandlers);
		if (exceptionHandlers.length === 0) {
			graph += node;
		} else {
			for (const { tryStart, catchOffset } of exceptionHandlers) {
				clusters.getWithDefault(
					tryStart,
					() => ({ nodes: [], children: new AddressMap(), catchHandlers: new AddressSet() })
				).catchHandlers.add(catchOffset);

				nestedClusters.getWithDefault(tryStart, () => new AddressSet());
			}
			const sorted = exceptionHandlers.toSorted(
				({tryStart: leftStart, tryEnd: leftEnd}, {tryStart: rightStart, tryEnd: rightEnd}) =>
					(rightEnd - rightStart) - (leftEnd - leftStart)
			);

			for (let i = 1; i < sorted.length; i++) {
				const { tryStart: surroundingTry } = sorted[i - 1];
				const { tryStart: childTry } = sorted[i];
				nestedClusters.get(surroundingTry)!.add(childTry);
			}

			const { tryStart: surroundingTry } = sorted.at(-1)!;
			
			clusters.get(surroundingTry)!.nodes.push(node);
		}
	}

	const toDelete = new AddressSet();
	for (const [tryStart, children] of nestedClusters) {
		if (children.size === 0) continue;

		clusters.get(tryStart)!.children = new AddressMap([...children].flatMap(c => {
			if (c === tryStart) return [];
			const child = clusters.get(c)!
			toDelete.add(c);

			return [[c, child]];
		}));
	}

	for (const c of toDelete) {
		clusters.delete(c);
	}

	const catchEdges: string[] = [];

	function genCluster(start: number, cluster: Cluster, level = 1): string {
		graph += '\t'.repeat(level) + `subgraph ${regionName(start)} {`;
		graph += '\t'.repeat(level + 1) + `style=dotted;`;

		let firstNode: string | undefined;
		for (const n of cluster.nodes) {
			firstNode ??= n.split(' [')[0];
			graph += '\t'.repeat(level + 1) + n + '\n';
		}

		for (const [childStart, child] of cluster.children) {
			const innerNode = genCluster(childStart, child, level + 1);
			firstNode ??= innerNode;
		}

		graph += '\t'.repeat(level) + `}`;

		for (const catchHandler of cluster.catchHandlers) {
			catchEdges.push(`${firstNode} -> ${blockName(catchHandler)}[ltail=${regionName(start)}];`);
		}

		if (!firstNode) {
			throw new Error();
		}

		return firstNode;
	}

	for (const [start, cluster] of clusters) {
		genCluster(start, cluster);
	}

	graph += '\n';

	for (const [addr, block] of func.basicBlocks) {
		graph += [
			block.consequentAddresses.map(succ => {
				return `\t${blockName(addr)} -> ${blockName(succ)};\n`;
			}).join(''),
			/*
			...block.exceptionHandlers.map(exc => {
				return `\tblock_${addr} -> block${exc.catchOffset}`;
			})
			*/
		].join('');
	}

	graph += '\n';
	graph += catchEdges.join('\n') + '\n';

	graph += '}'
	return graph;
}