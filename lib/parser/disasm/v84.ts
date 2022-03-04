import IDisassembler from './IDisassembler.ts'

export class V84Disassembler extends IDisassembler {
	static canDisassembleVersion(fileVersion: number): boolean {
		return fileVersion === 84;
	}

	disassembler(bytecode: ArrayBuffer) {
	}
}
