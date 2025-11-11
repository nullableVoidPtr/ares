import { createInstruction, RAW_OPERANDS } from '../disassembly/instruction.ts';
import { VersionInfo } from '../hbcConsts/VersionInfo.ts';
import { DataViewStream } from '../utils/DataViewStream.ts';

export function disassemble(bytecode: ArrayBufferLike, version: VersionInfo, frameSize?: number) {
	const io = new DataViewStream(bytecode);

	const instructions = [];
	const { opcodeMap, legacyOperands } = version;
	while (io.remaining) {
		const functionLocalOffset = io.pos;
		const opcode = io.UInt8();
		const instruction = opcodeMap[opcode];
		try {
			instructions.push(
				createInstruction(
					instruction,
					(legacyOperands[instruction] ?? RAW_OPERANDS[instruction]).map(r => r(io)),
					functionLocalOffset,
					version,
					frameSize,
				),
			);
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