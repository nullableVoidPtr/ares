import { Register, asRegister, StringRef, asStringRef, BigIntRef, asBigIntRef, FunctionRef, asFunctionRef } from '../hbc/disassembly/instruction.ts';

export class DataReader {
	view: DataView
	pos: number = 0;

	constructor(data: ArrayBufferLike) {
		this.view = new DataView(data);
	}

	Int8() {
		const value = this.view.getInt8(this.pos);
		this.pos += 1;
		return value;
	}
	Int16() {
		const value = this.view.getInt16(this.pos, true);
		this.pos += 2;
		return value;
	}
	Int32() {
		const value = this.view.getInt32(this.pos, true);
		this.pos += 4;
		return value;
	}

	UInt8() {
		const value = this.view.getUint8(this.pos);
		this.pos += 1;
		return value;
	}
	UInt16() {
		const value = this.view.getUint16(this.pos, true);
		this.pos += 2;
		return value;
	}
	UInt32() {
		const value = this.view.getUint32(this.pos, true);
		this.pos += 4;
		return value;
	}

	Double() {
		const value = this.view.getFloat64(this.pos, true);
		this.pos += 8;
		return value;
	}

	Reg8(): Register {
		return asRegister(this.UInt8());
	}
	Reg32(): Register {
		return asRegister(this.UInt32());
	}

	StringRef8(): StringRef {
		return asStringRef(this.UInt8());
	}
	StringRef16(): StringRef {
		return asStringRef(this.UInt16());
	}
	StringRef32(): StringRef {
		return asStringRef(this.UInt32());
	}
	
	BigIntRef16(): BigIntRef {
		return asBigIntRef(this.UInt16());
	}
	BigIntRef32(): BigIntRef {
		return asBigIntRef(this.UInt32());
	}

	FunctionRef16(): FunctionRef {
		return asFunctionRef(this.UInt16());
	}
	FunctionRef32(): FunctionRef {
		return asFunctionRef(this.UInt32());
	}

	get remaining(): boolean {
		return this.pos < this.view.byteLength;
	}
}

export function Int8(io: DataReader) { return io.Int8(); }
export function Int32(io: DataReader) { return io.Int32(); }

export function UInt8(io: DataReader) { return io.UInt8(); }
export function UInt16(io: DataReader) { return io.UInt16(); }
export function UInt32(io: DataReader) { return io.UInt32(); }

export function Double(io: DataReader) { return io.Double(); }
