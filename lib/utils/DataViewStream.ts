import { Register, asRegister, StringRef, asStringRef, BigIntRef, asBigIntRef, FunctionRef, asFunctionRef } from '../disassembly/instruction.ts';

export class DataViewStream {
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

export function Int8(io: DataViewStream) { return io.Int8(); }
export function Int32(io: DataViewStream) { return io.Int32(); }

export function UInt8(io: DataViewStream) { return io.UInt8(); }
export function UInt16(io: DataViewStream) { return io.UInt16(); }
export function UInt32(io: DataViewStream) { return io.UInt32(); }

export function Double(io: DataViewStream) { return io.Double(); }

export function StringRef8(io: DataViewStream) { return io.StringRef8(); }
export function StringRef16(io: DataViewStream) { return io.StringRef16(); }
export function StringRef32(io: DataViewStream) { return io.StringRef32(); }

export function BigIntRef16(io: DataViewStream) { return io.BigIntRef16(); }
export function BigIntRef32(io: DataViewStream) { return io.BigIntRef32(); }

export function FunctionRef16(io: DataViewStream) { return io.FunctionRef16(); }
export function FunctionRef32(io: DataViewStream) { return io.FunctionRef32(); }

export function Reg8(io: DataViewStream) { return io.Reg8(); }
export function Reg32(io: DataViewStream) { return io.Reg32(); }