import * as t from '@babel/types';
import traverse from '@babel/traverse';
import { type SSARegister, ssaRegisterEquals } from '../../../ssa.ts';
import type { IRFunction } from '../mod.ts';
import { setRestParameter } from './parameterPlan.ts';

function registerName(register: SSARegister): string {
	return `r${register.index}_${register.version}`;
}

function same(
	left: SSARegister | null | undefined,
	right: SSARegister | null | undefined,
): boolean {
	return left != null && right != null && ssaRegisterEquals(left, right);
}

function replaceArrayUses(
	func: IRFunction,
	arrayName: string,
	restName: string,
): void {
	for (const block of func.blocks.values()) {
		const wrapped = t.file(t.program(block.body as t.Statement[]));
		if (block.branch) {
			wrapped.program.body.push(
				t.expressionStatement(block.branch as t.Expression),
			);
		}
		traverse(wrapped, {
			Function(path) {
				path.skip();
			},
			Identifier(path) {
				if (!path.isReferencedIdentifier({ name: arrayName })) return;
				path.replaceWith(t.identifier(restName));
			},
		});
	}
}

function reduceZeroStartArgumentsCopyRest(func: IRFunction): boolean {
	const entryAddress = func.entryAddress;
	const entrySSA = func.ssa.basicBlocks.get(entryAddress);
	const entryIR = func.blocks.get(entryAddress);
	if (
		!entrySSA || !entryIR || entrySSA.consequentAddresses.length !== 2 ||
		func.exceptions.activeHandlersAtBlock(entryAddress).size !== 0
	) return false;
	const instructions = entrySSA.ssaInstructions;
	const arrayCtor = instructions.find((instruction) =>
		instruction.instruction === 'TryGetById' &&
		func.file.getIdentifier(instruction.property.stringTableIndex) ===
			'Array'
	);
	const length = instructions.find((instruction) =>
		instruction.instruction === 'GetArgumentsLength'
	);
	const zero = instructions.find((instruction) =>
		instruction.instruction === 'LoadConst' && instruction.value === 0
	);
	if (
		!arrayCtor || arrayCtor.instruction !== 'TryGetById' ||
		!length || length.instruction !== 'GetArgumentsLength' ||
		!zero || zero.instruction !== 'LoadConst'
	) return false;
	const prototype = instructions.find((instruction) =>
		instruction.instruction === 'GetById' &&
		same(instruction.uses.object, arrayCtor.defs.destination) &&
		func.file.getIdentifier(instruction.property.stringTableIndex) ===
			'prototype'
	);
	if (!prototype || prototype.instruction !== 'GetById') return false;
	const receiver = instructions.find((instruction) =>
		instruction.instruction === 'CreateThis' &&
		same(instruction.uses.prototype, prototype.defs.destination) &&
		same(instruction.uses.constructorRef, arrayCtor.defs.destination)
	);
	if (!receiver || receiver.instruction !== 'CreateThis') return false;
	const receiverArgument = instructions.find((instruction) =>
		instruction.instruction === 'Mov' &&
		same(instruction.uses.source, receiver.defs.destination)
	);
	const lengthArgument = instructions.find((instruction) =>
		instruction.instruction === 'Mov' &&
		same(instruction.uses.source, length.defs.destination)
	);
	if (
		!receiverArgument || receiverArgument.instruction !== 'Mov' ||
		!lengthArgument || lengthArgument.instruction !== 'Mov'
	) return false;
	const construct = instructions.find((instruction) =>
		instruction.instruction === 'Construct' &&
		same(instruction.uses.closure, arrayCtor.defs.destination) &&
		instruction.uses.arguments.length === 2 &&
		same(
			instruction.uses.arguments[0],
			receiverArgument.defs.destination,
		) &&
		same(instruction.uses.arguments[1], lengthArgument.defs.destination)
	);
	if (!construct || construct.instruction !== 'Construct') return false;
	const selected = instructions.find((instruction) =>
		instruction.instruction === 'SelectObject' &&
		same(instruction.uses.thisObject, receiver.defs.destination) &&
		same(
			instruction.uses.constructorReturnValue,
			construct.defs.destination,
		)
	);
	if (!selected || selected.instruction !== 'SelectObject') return false;
	const less = instructions.find((instruction) =>
		instruction.instruction === 'Less' &&
		same(instruction.uses.left, zero.defs.destination) &&
		same(instruction.uses.right, length.defs.destination)
	);
	const guard = instructions.at(-1);
	if (
		!less || less.instruction !== 'Less' || !guard ||
		guard.instruction !== 'JmpFalse' ||
		!same(guard.uses.predicate, less.defs.destination)
	) return false;

	const [loopAddress, joinAddress] = entrySSA.consequentAddresses;
	const loop = func.ssa.basicBlocks.get(loopAddress);
	if (
		!loop || loop.consequentAddresses.length !== 2 ||
		!loop.consequentAddresses.includes(loopAddress) ||
		!loop.consequentAddresses.includes(joinAddress) ||
		func.cfgPredecessorsOf(loopAddress).size !== 2 ||
		!func.exceptions.activeHandlersEqual(entryAddress, loopAddress)
	) return false;
	const phi = loop.ssaInstructions.find((instruction) =>
		instruction.instruction === 'Phi' &&
		instruction.sources.size === 2 &&
		same(instruction.sources.get(entryAddress), zero.defs.destination)
	);
	if (!phi || phi.instruction !== 'Phi') return false;
	const argumentRead = loop.ssaInstructions.find((instruction) =>
		instruction.instruction === 'GetArgumentsPropByVal' &&
		same(instruction.uses.argumentsIndex, phi.destination)
	);
	if (!argumentRead || argumentRead.instruction !== 'GetArgumentsPropByVal') {
		return false;
	}
	const write = loop.ssaInstructions.find((instruction) =>
		instruction.instruction === 'PutByVal' &&
		same(instruction.uses.object, selected.defs.destination) &&
		same(instruction.uses.property, phi.destination) &&
		same(instruction.uses.value, argumentRead.defs.destination)
	);
	if (!write || write.instruction !== 'PutByVal') return false;
	const next = loop.ssaInstructions.find((instruction) =>
		instruction.instruction === 'Inc' &&
		same(instruction.uses.argument, phi.destination)
	);
	if (!next || next.instruction !== 'Inc') return false;
	if (!same(phi.sources.get(loopAddress), next.defs.destination)) {
		return false;
	}
	const loopBranch = loop.ssaInstructions.at(-1);
	if (
		!loopBranch || loopBranch.instruction !== 'JLess' ||
		!same(loopBranch.uses.left, next.defs.destination) ||
		!same(loopBranch.uses.right, length.defs.destination)
	) return false;

	const allocationOffsets = new Set([
		arrayCtor.functionLocalOffset,
		length.functionLocalOffset,
		prototype.functionLocalOffset,
		receiver.functionLocalOffset,
		receiverArgument.functionLocalOffset,
		lengthArgument.functionLocalOffset,
		construct.functionLocalOffset,
		selected.functionLocalOffset,
		zero.functionLocalOffset,
		less.functionLocalOffset,
	]);
	entryIR.body = entryIR.body.filter((statement) =>
		!allocationOffsets.has(statement.extra?.address ?? -1)
	);
	entryIR.branch = undefined;
	entryIR.consequentAddresses = [joinAddress];
	const restName = `_rest_${func.id}_`;
	const arrayName = registerName(selected.defs.destination);
	func.markMergedBlocks(entryAddress, loopAddress);
	replaceArrayUses(func, arrayName, restName);
	setRestParameter(func.parameterPlan, func.id, 0, 'arguments-copy-loop');
	func.rebuildPredecessorMap();
	return true;
}

/**
 * Recognize Hermes' manual arguments-to-rest loop while SSA and CFG provenance
 * are still intact. The match owns the complete empty/non-empty diamond and
 * loop; a source-written argument loop missing any edge or index invariant is
 * left unchanged.
 */
export function reduceArgumentsCopyRest(func: IRFunction): boolean {
	if (reduceZeroStartArgumentsCopyRest(func)) return true;
	const entryAddress = func.entryAddress;
	const entrySSA = func.ssa.basicBlocks.get(entryAddress);
	const entryIR = func.blocks.get(entryAddress);
	if (
		!entrySSA || !entryIR || entrySSA.consequentAddresses.length !== 2 ||
		func.exceptions.activeHandlersAtBlock(entryAddress).size !== 0
	) return false;
	const instructions = entrySSA.ssaInstructions;
	const arrayCtor = instructions.find((instruction) =>
		instruction.instruction === 'TryGetById' &&
		func.file.getIdentifier(instruction.property.stringTableIndex) ===
			'Array'
	);
	if (!arrayCtor || arrayCtor.instruction !== 'TryGetById') return false;
	const size = instructions.find((instruction) =>
		instruction.instruction === 'Sub' &&
		instructions.some((candidate) =>
			candidate.instruction === 'GetArgumentsLength' &&
			same(candidate.defs.destination, instruction.uses.left)
		)
	);
	if (!size || size.instruction !== 'Sub') return false;
	const start = instructions.find((instruction) =>
		instruction.instruction === 'LoadConst' &&
		typeof instruction.value === 'number' &&
		Number.isSafeInteger(instruction.value) && instruction.value >= 0 &&
		same(instruction.defs.destination, size.uses.right)
	);
	if (
		!start || start.instruction !== 'LoadConst' ||
		typeof start.value !== 'number'
	) return false;
	const startIndex = start.value;
	const receiver = instructions.find((instruction) =>
		instruction.instruction === 'CreateThisForNew' &&
		same(instruction.uses.closure, arrayCtor.defs.destination)
	);
	if (!receiver || receiver.instruction !== 'CreateThisForNew') return false;
	const receiverArgument = instructions.find((instruction) =>
		instruction.instruction === 'Mov' &&
		same(instruction.uses.source, receiver.defs.destination)
	);
	if (!receiverArgument || receiverArgument.instruction !== 'Mov') {
		return false;
	}
	const construct = instructions.find((instruction) =>
		instruction.instruction === 'Construct' &&
		same(instruction.uses.closure, arrayCtor.defs.destination) &&
		instruction.uses.arguments.length === 2 &&
		same(
			instruction.uses.arguments[0],
			receiverArgument.defs.destination,
		) &&
		same(instruction.uses.arguments[1], size.defs.destination)
	);
	if (!construct || construct.instruction !== 'Construct') return false;
	const selected = instructions.find((instruction) =>
		instruction.instruction === 'SelectObject' &&
		same(instruction.uses.thisObject, receiver.defs.destination) &&
		same(
			instruction.uses.constructorReturnValue,
			construct.defs.destination,
		)
	);
	if (!selected || selected.instruction !== 'SelectObject') return false;

	const guard = instructions.at(-1);
	if (
		!guard || guard.instruction !== 'JNotGreater' ||
		!entrySSA.ssaInstructions.some((instruction) =>
			instruction.instruction === 'GetArgumentsLength' &&
			same(instruction.defs.destination, guard.uses.left)
		) || !same(guard.uses.right, start.defs.destination)
	) return false;

	const [joinAddress, nonEmptyAddress] = entrySSA.consequentAddresses;
	const setup = func.ssa.basicBlocks.get(nonEmptyAddress);
	if (
		!setup || setup.consequentAddresses.length !== 2 ||
		func.cfgPredecessorsOf(nonEmptyAddress).size !== 1 ||
		!func.exceptions.activeHandlersEqual(entryAddress, nonEmptyAddress)
	) return false;
	const setupLess = setup.ssaInstructions.find((instruction) =>
		instruction.instruction === 'Less' &&
		same(instruction.uses.left, start.defs.destination) &&
		setup.ssaInstructions.some((candidate) =>
			candidate.instruction === 'GetArgumentsLength' &&
			same(candidate.defs.destination, instruction.uses.right)
		)
	);
	const inductionStart = setup.ssaInstructions.find((instruction) =>
		instruction.instruction === 'Mov' &&
		same(instruction.uses.source, start.defs.destination)
	);
	if (
		!setupLess || setupLess.instruction !== 'Less' ||
		!inductionStart || inductionStart.instruction !== 'Mov'
	) return false;
	const loopAddress = setup.consequentAddresses.find((address) =>
		address !== joinAddress
	);
	if (loopAddress == null) return false;
	const loop = func.ssa.basicBlocks.get(loopAddress);
	if (
		!loop || loop.consequentAddresses.length !== 2 ||
		!loop.consequentAddresses.includes(loopAddress) ||
		!loop.consequentAddresses.includes(joinAddress) ||
		!func.exceptions.activeHandlersEqual(entryAddress, loopAddress)
	) return false;
	const phi = loop.ssaInstructions.find((instruction) =>
		instruction.instruction === 'Phi' &&
		instruction.sources.size === 2 &&
		same(
			instruction.sources.get(nonEmptyAddress),
			inductionStart.defs.destination,
		)
	);
	if (!phi || phi.instruction !== 'Phi') return false;
	const argumentRead = loop.ssaInstructions.find((instruction) =>
		instruction.instruction === 'GetArgumentsPropByVal' &&
		same(instruction.uses.argumentsIndex, phi.destination)
	);
	if (!argumentRead || argumentRead.instruction !== 'GetArgumentsPropByVal') {
		return false;
	}
	const destinationSub = loop.ssaInstructions.find((instruction) =>
		instruction.instruction === 'Sub' &&
		same(instruction.uses.left, phi.destination) &&
		same(instruction.uses.right, start.defs.destination)
	);
	const destinationIndex = startIndex === 0
		? phi.destination
		: destinationSub?.instruction === 'Sub'
		? destinationSub.defs.destination
		: undefined;
	if (!destinationIndex) return false;
	const write = loop.ssaInstructions.find((instruction) =>
		instruction.instruction === 'PutByVal' &&
		same(instruction.uses.object, selected.defs.destination) &&
		same(instruction.uses.property, destinationIndex) &&
		same(instruction.uses.value, argumentRead.defs.destination)
	);
	if (!write || write.instruction !== 'PutByVal') return false;
	const one =
		loop.ssaInstructions.find((instruction) =>
			instruction.instruction === 'LoadConst' && instruction.value === 1
		) ?? instructions.find((instruction) =>
			instruction.instruction === 'LoadConst' && instruction.value === 1
		);
	if (!one || one.instruction !== 'LoadConst') return false;
	const next = loop.ssaInstructions.find((instruction) =>
		instruction.instruction === 'Add' &&
		same(instruction.uses.left, phi.destination) &&
		same(instruction.uses.right, one.defs.destination)
	);
	if (!next || next.instruction !== 'Add') return false;
	if (!same(phi.sources.get(loopAddress), next.defs.destination)) {
		return false;
	}
	const loopBranch = loop.ssaInstructions.at(-1);
	if (
		!loopBranch || loopBranch.instruction !== 'JLess' ||
		!same(loopBranch.uses.left, next.defs.destination) ||
		!loop.ssaInstructions.some((instruction) =>
			instruction.instruction === 'GetArgumentsLength' &&
			same(instruction.defs.destination, loopBranch.uses.right)
		)
	) return false;

	const allocationOffsets = new Set([
		arrayCtor.functionLocalOffset,
		size.functionLocalOffset,
		receiver.functionLocalOffset,
		receiverArgument.functionLocalOffset,
		construct.functionLocalOffset,
		selected.functionLocalOffset,
		...instructions.flatMap((instruction) =>
			instruction.instruction === 'GetArgumentsLength'
				? [instruction.functionLocalOffset]
				: []
		),
	]);
	entryIR.body = entryIR.body.filter((statement) =>
		!allocationOffsets.has(statement.extra?.address ?? -1)
	);
	entryIR.branch = undefined;
	entryIR.consequentAddresses = [joinAddress];
	const restName = `_rest_${func.id}_`;
	const arrayName = registerName(selected.defs.destination);
	func.markMergedBlocks(entryAddress, nonEmptyAddress);
	func.markMergedBlocks(entryAddress, loopAddress);
	replaceArrayUses(func, arrayName, restName);
	setRestParameter(
		func.parameterPlan,
		func.id,
		startIndex,
		'arguments-copy-loop',
	);
	func.rebuildPredecessorMap();
	return true;
}
