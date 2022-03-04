export abstract class IDisassembler {
	static canDisassembleVersion: (fileVersion: number) => boolean;
	disassembler: (bytecode: ArrayBuffer) => VMInstruction[];
}
