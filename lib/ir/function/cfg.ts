import * as t from '@babel/types';
import { BlockAddr } from '../../hbc/disassembly/function.ts';
import { IRFunction } from './mod.ts';
import { LiftedAST } from '../ast.ts';
import { areExceptionHandlersEqual, areExceptionHandlersParent, exceptionHandlersByAddress } from '../../hbc/utils/exceptions.ts';
import { AddressSet } from '../../utils/set.ts';
import { AddressMap } from '../../utils/map.ts';
import { AddressGraph } from '../../utils/graph.ts';

export function reduceSequence(func: IRFunction) {
	const parents = new AddressMap<BlockAddr>();
	const children = new AddressMap<BlockAddr>();
	for (const [addr, block] of func.blocks) {
		if (block.branch) continue;

		const successors = block.consequentAddresses;
		if (successors.length !== 1) continue

		const [childAddr] = successors;
		if (addr === childAddr) continue;
		if (!areExceptionHandlersEqual(addr, childAddr, func._exceptionHandlers)) {
			if (func.ssa.basicBlocks.get(childAddr)?.consequentAddresses?.length !== 0) continue;
		}

		if (func.predecessorsOf(childAddr).size !== 1) continue;

		parents.set(childAddr, addr);
		children.set(addr, childAddr);
	}

	if (children.size === 0) {
		return false;
	}

	const starts = new AddressSet();
	for (const parent of children.keys()) {
		if (!parents.has(parent)) starts.add(parent);
	}


	for (const start of starts) {
		const parent = func.blocks.get(start)!;

		const rootAddr = start;
		let parentAddr = rootAddr;
		while (true) {
			const childAddr = children.get(parentAddr);
			if (!childAddr) break;

			const child = func.blocks.get(childAddr)!;
			parent.body.push(...child.body)
			parent.branch = child.branch;
			parent.consequentAddresses = child.consequentAddresses;

			func.markMergedBlocks(rootAddr, childAddr);
			
			parentAddr = childAddr;
		}
	}

	return true;
}

export function reduceSimpleIf(func: IRFunction) {
	const simpleIfs = new AddressMap<{
		test: LiftedAST<t.Expression>;
		consequent: BlockAddr;
		alternate: BlockAddr | null;
		successor: BlockAddr | null;
	}>();

	for (const [addr, block] of func.blocks) {
		if (!block.branch) continue;

		const successors = block.consequentAddresses;
		if (successors.length !== 2) {
			throw new TypeError();
		}

		const [left, right] = successors;
		const leftSuccessors = func.blocks.get(left)!.consequentAddresses;
		const rightSuccessors = func.blocks.get(right)!.consequentAddresses;

		let ifTest: LiftedAST<t.Expression>;
		let consequent: BlockAddr;
		let alternate: BlockAddr | null;
		let successor: BlockAddr | null;

		const containedLeft = func.predecessorsOf(left).size === 1;
		const containedRight = func.predecessorsOf(right).size === 1;

		const leftConsequent = (
			leftSuccessors.length === 1 &&
			leftSuccessors[0] === right &&
			containedLeft
		);
		const rightConsequent = (
			rightSuccessors.length === 1 &&
			rightSuccessors[0] === left &&
			containedRight
		);
		const ifElse = (
			leftSuccessors.length === 1 &&
			rightSuccessors.length === 1 &&
			leftSuccessors[0] === rightSuccessors[0] &&
			containedLeft &&
			containedRight
		);

		const leftEarlyReturn = (
			leftSuccessors.length === 0 &&
			containedLeft
		);
		const rightEarlyReturn = (
			rightSuccessors.length === 0 &&
			containedRight
		);
		const bothEarlyReturn = leftEarlyReturn && rightEarlyReturn;

		if (ifElse || bothEarlyReturn) {
			ifTest = block.branch;
			successor = leftSuccessors[0] ?? null;

			consequent = right;
			alternate  = left;
		} else if (leftConsequent || leftEarlyReturn) {
			ifTest = t.unaryExpression('!', <t.Expression>block.branch);

			consequent = left;
			alternate = null;
			successor = right;
		} else if (rightConsequent || rightEarlyReturn) {
			ifTest = block.branch;

			consequent = right;
			alternate = null;
			successor = left;
		} else {
			continue;
		}

		const headerCatches = exceptionHandlersByAddress(addr, func._exceptionHandlers);
		if (!areExceptionHandlersParent(headerCatches, consequent, func._exceptionHandlers)) {
			if (func.blocks.get(consequent)!.consequentAddresses.length !== 0) continue;
		} else if (alternate && !areExceptionHandlersParent(headerCatches, alternate, func._exceptionHandlers)) {
			if (func.blocks.get(alternate)!.consequentAddresses.length !== 0) continue;
		}

		simpleIfs.set(addr, {
			test: ifTest,
			consequent,
			alternate,
			successor,
		});
	}

	if (simpleIfs.size === 0) {
		return false;
	}

	for (const [headerAddr, {test, consequent: consequentAddr, alternate: alternateAddr, successor: successorAddr}] of simpleIfs) {
		const header = func.blocks.get(headerAddr)!;
		const consequent = func.blocks.get(consequentAddr)!;
		const alternate = (alternateAddr) ? func.blocks.get(alternateAddr)! : null;

		header.branch = undefined;
		header.body.push(
			t.ifStatement(
				<t.Expression>test,
				t.blockStatement(<t.Statement[]>consequent.body),
				alternate ? t.blockStatement(<t.Statement[]>alternate.body) : null
			)
		);

		func.markMergedBlocks(headerAddr, consequentAddr);
		if (alternateAddr) {
			func.markMergedBlocks(headerAddr, alternateAddr);
		}

		if (successorAddr !== null) {
			header.consequentAddresses = [successorAddr];
		} else {
			header.consequentAddresses = [];
		}
	}

	return true;
}

export function reduceTryCatch(func: IRFunction) {
	const catchMap = new AddressGraph();
	for (const addr of func.blocks.keys()) {
		for (const { catchOffset } of exceptionHandlersByAddress(addr, func._exceptionHandlers)) {
			catchMap.addEdge(catchOffset, addr);
		}
	}

	if (catchMap.size === 0) {
		return false;
	}

	let changed = false;
	for (const [catchAddr, bodyBlocks] of catchMap) {
		if (bodyBlocks.size > 1) continue;

		const catcher = func.blocks.get(catchAddr)!;
		const body = func.blocks.get(bodyBlocks.values().next().value!)!;

		if (catcher.consequentAddresses.length !== 1) continue;
		if (body.consequentAddresses.length !== 1) continue;
		if (catcher.consequentAddresses[0] !== body.consequentAddresses[0]) continue;

		if (!areExceptionHandlersParent(body.address, catchAddr, func._exceptionHandlers)) continue;

		const catchBody = t.blockStatement(<t.Statement[]>catcher.body.slice());

		const catchInstIndex = catchBody.body.findIndex((errorAssign) => {
			if (!t.isVariableDeclaration(errorAssign, { kind: 'const' })) return false;
			if (!t.isVariableDeclarator(errorAssign.declarations[0])) return false;
			if (!t.isCallExpression(errorAssign.declarations[0].init)) return false;
			if (!t.isV8IntrinsicIdentifier(errorAssign.declarations[0].init.callee, { name: 'Catch' })) return false;

			return true;
		});

		const errorAssign = <t.VariableDeclaration>t.cloneNode(<t.Statement>catcher.body[catchInstIndex], true);

		const errorName = `e_${catchAddr}`;
		errorAssign.declarations[0].init = t.identifier(errorName);
		catchBody.body.splice(catchInstIndex, 1, errorAssign);

		body.body = [
			t.tryStatement(
				t.blockStatement(<t.Statement[]>body.body),
				t.catchClause(t.identifier(errorName), catchBody),
			)
		];

		func._exceptionHandlers = func._exceptionHandlers.filter(({catchOffset}) => catchOffset !== catchAddr);

		func.markMergedBlocks(body.address, catchAddr);

		changed = true;
	}

	return changed;
}