import {
	createInstruction,
	RAW_OPERANDS,
	StringSwitchImmInst,
	UIntSwitchImmInst,
} from '../hbc/disassembly/instruction.ts';
import { VersionInfo } from '../hbc/data/VersionInfo.ts';
import { DataReader } from '../utils/DataReader.ts';
import { BlockAddr } from '../hbc/disassembly/function.ts';

function align(value: number, alignment: number): number {
	return Math.ceil(value / alignment) * alignment;
}

function getUIntSwitchImmTargets(
	instruction: UIntSwitchImmInst,
	bytecode: Uint8Array,
	functionOffset: number,
): BlockAddr[] {
	if (!bytecode) {
		throw new Error('SwitchImm target decoding requires function bytecode');
	}

	const count = instruction.maxValue - instruction.minValue + 1;
	if (!Number.isSafeInteger(count) || count <= 0 || count > 0x10000) {
		throw new Error(`Unsupported SwitchImm table size: ${count}`);
	}
	const byteLength = bytecode.byteLength;
	const view = new DataReader(bytecode);
	const tableOffset = align(
		functionOffset + instruction.functionLocalOffset +
			instruction.jumpTableOffset,
		4,
	);
	if (tableOffset < 0 || tableOffset + count * 4 > byteLength) {
		console.log(instruction.functionLocalOffset, tableOffset, byteLength);
		throw new Error('SwitchImm jump table is outside bytecode');
	}
	view.pos = tableOffset;
	const targets = [];
	for (let i = 0; i < count; i++) {
		const relativeTarget = view.UInt32();
		targets.push(relativeTarget);
	}
	return targets;
}

function getUIntSwitchImmTableRange(
	instruction: UIntSwitchImmInst,
	functionOffset: number,
): [number, number] {
	const count = instruction.maxValue - instruction.minValue + 1;
	const unalignedStart = functionOffset + instruction.functionLocalOffset +
		instruction.jumpTableOffset;
	const start = align(
		functionOffset + instruction.functionLocalOffset +
			instruction.jumpTableOffset,
		4,
	) - functionOffset;
	return [unalignedStart - functionOffset, start + count * 4];
}

function getStringSwitchImmTargets(
	instruction: StringSwitchImmInst,
	bytecode: Uint8Array,
	functionOffset: number,
): { stringTableIndices: number[]; targets: BlockAddr[] } {
	if (!bytecode) {
		throw new Error(
			'StringSwitchImm target decoding requires function bytecode',
		);
	}

	const count = instruction.size;
	if (!Number.isSafeInteger(count) || count <= 0 || count > 0x10000) {
		throw new Error(`Unsupported StringSwitchImm table size: ${count}`);
	}
	const byteLength = bytecode.byteLength;
	const view = new DataReader(bytecode);
	const tableOffset = align(
		functionOffset + instruction.functionLocalOffset +
			instruction.jumpTableOffset,
		4,
	);
	if (tableOffset < 0 || tableOffset + count * 8 > byteLength) {
		throw new Error('StringSwitchImm jump table is outside bytecode');
	}
	view.pos = tableOffset;
	const stringTableIndices = [];
	const targets = [];
	for (let i = 0; i < count; i++) {
		stringTableIndices.push(view.UInt32());
		const relativeTarget = view.UInt32();
		targets.push(relativeTarget);
	}
	return { stringTableIndices, targets };
}

function getStringSwitchImmTableRange(
	instruction: StringSwitchImmInst,
	functionOffset: number,
): [number, number] {
	const unalignedStart = functionOffset + instruction.functionLocalOffset +
		instruction.jumpTableOffset;
	const start = align(
		functionOffset + instruction.functionLocalOffset +
			instruction.jumpTableOffset,
		4,
	) - functionOffset;
	return [unalignedStart - functionOffset, start + instruction.size * 8];
}

export function disassemble(
	bytecode: ArrayBufferLike | ArrayBufferView,
	version: VersionInfo,
	frameSize?: number,
	rawBytes?: Uint8Array,
	functionOffset?: number,
) {
	const io = new DataReader(bytecode);

	const instructions = [];
	const skipRanges: [number, number][] = [];
	const { opcodeMap, legacyOperands } = version;
	while (io.remaining) {
		const skipRange = skipRanges.find(([start, end]) =>
			io.pos >= start && io.pos < end
		);
		if (skipRange) {
			io.pos = skipRange[1];
			continue;
		}

		const functionLocalOffset = io.pos;
		const opcode = io.UInt8();
		const instruction = opcodeMap[opcode];
		const operandReaders = legacyOperands[instruction] ??
			RAW_OPERANDS[instruction];
		try {
			const disassembled = createInstruction(
				instruction,
				operandReaders?.map((r) => r(io)) ?? [],
				functionLocalOffset,
				version,
				frameSize,
			);
			if (disassembled.instruction === 'UIntSwitchImm') {
				if (!rawBytes || typeof functionOffset == 'undefined') {
					throw new Error();
				}
				disassembled.relativeTargets = getUIntSwitchImmTargets(
					disassembled,
					rawBytes,
					functionOffset,
				);
				skipRanges.push(
					getUIntSwitchImmTableRange(disassembled, functionOffset),
				);
			} else if (disassembled.instruction === 'StringSwitchImm') {
				if (!rawBytes || typeof functionOffset == 'undefined') {
					throw new Error();
				}
				const { stringTableIndices, targets } =
					getStringSwitchImmTargets(
						disassembled,
						rawBytes,
						functionOffset,
					);
				disassembled.stringTableIndices = stringTableIndices;
				disassembled.relativeTargets = targets;
				skipRanges.push(
					getStringSwitchImmTableRange(disassembled, functionOffset),
				);
			}

			instructions.push(disassembled);
		} catch (e) {
			console.log(instructions.pop());
			console.log(instructions.pop());
			console.log(instructions.pop());
			console.log(instructions.pop());
			throw e;
		}
	}

	return instructions;
}
