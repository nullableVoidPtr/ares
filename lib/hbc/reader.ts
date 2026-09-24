import { DataReader, Int32, Int8, UInt32 } from '../utils/DataReader.ts';

export const Imm32 = Int32;

export const Addr8 = Int8;
export const Addr32 = Int32;

export function StringRef8(io: DataReader) {
	return io.StringRef8();
}
export function StringRef16(io: DataReader) {
	return io.StringRef16();
}
export function StringRef32(io: DataReader) {
	return io.StringRef32();
}

export function BigIntRef16(io: DataReader) {
	return io.BigIntRef16();
}
export function BigIntRef32(io: DataReader) {
	return io.BigIntRef32();
}

export function FunctionRef16(io: DataReader) {
	return io.FunctionRef16();
}
export function FunctionRef32(io: DataReader) {
	return io.FunctionRef32();
}

export function Reg8(io: DataReader) {
	return io.Reg8();
}
export function Reg32(io: DataReader) {
	return io.Reg32();
}
