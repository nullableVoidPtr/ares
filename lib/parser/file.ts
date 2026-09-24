import fs from 'node:fs';
import type * as t from '@babel/types';
import { HermesBytecode, StringKind } from './wasm/hermes_bytecode_parser.js';
import { Function } from '../hbc/disassembly/function.ts';
import { structureInstructions } from '../hbc/disassembly/mod.ts';
import { disassemble } from './bytecode.ts';
import { getVersionInfo, VersionInfo } from '../hbc/data/VersionInfo.ts';
import { DataReader } from '../utils/DataReader.ts';
import { StringRef } from '../hbc/disassembly/instruction.ts';

/**
 * The parser hands out `KindedString`/`ObjectShape` instances, which are
 * wasm-bindgen handles: every property read is a call into WASM, and the values
 * are meaningless once the parser is gone. Everything downstream only reads
 * these fields, so the file is typed structurally and a caller that has
 * materialised plain objects -- `lib/coldstore/` does, because handles cannot be
 * stored -- is just as valid a source.
 */
export interface StringTableEntry {
	readonly kind: StringKind;
	readonly value: string;
}

export interface ObjectShapeEntry {
	readonly keyBufferOffset: number;
	readonly numProps: number;
}

export type SerializedLiteralValue =
	| undefined
	| null
	| boolean
	| number
	| StringRef;

/**
 * Everything an `HBCFile` needs that is not derived from something else.
 *
 * `functions` is deliberately the whole array rather than a loader: an
 * `HBCFile` hands it out directly, so a caller that wants lazily paged
 * functions supplies a proxy here rather than teaching this class about paging.
 */
export interface HBCFileParts {
	data: Uint8Array;
	version: number;
	stringTable: StringTableEntry[];
	arrayBuffer: Uint8Array;
	literalValueBuffer: Uint8Array;
	objectKeyBuffer: Uint8Array;
	objectValueBuffer: Uint8Array;
	objectShapes: ObjectShapeEntry[];
	bigintTable: Uint8Array[];
	functions: Function[];
}

export class HBCFile {
	version: number;
	versionInfo: VersionInfo;

	stringTable: StringTableEntry[];
	functions: Function[];

	arrayBuffer: Uint8Array;
	literalValueBuffer: Uint8Array;
	objectKeyBuffer: Uint8Array;
	objectValueBuffer: Uint8Array;
	objectShapes: ObjectShapeEntry[];
	/** Little-endian two's-complement digits, one entry per bigint. */
	bigintTable: Uint8Array[];
	data: Uint8Array;
	loweredGeneratorWrapperSlotAliases = new Map<
		number,
		Map<number, t.Expression>
	>();

	/**
	 * Absent on a file rebuilt from parts rather than parsed -- see
	 * `HBCFile.fromParts`. Nothing outside this constructor reads it.
	 */
	_parsed?: HermesBytecode;

	static fromFile(path: string) {
		return HBCFile.fromBytes(fs.readFileSync(path));
	}

	static fromBytes(data: ArrayBufferLike | ArrayBufferView) {
		return new HBCFile(data);
	}

	/**
	 * Rebuild a file from pieces someone else already extracted.
	 *
	 * The parser is eager: constructing an `HBCFile` disassembles every function
	 * in the bundle, which is 2.5GB of resident set on a large one. A caller
	 * that has those pieces stored elsewhere -- `lib/coldstore/` keeps them in
	 * LMDB and pages functions in on demand -- needs a file that behaves
	 * identically without paying for the parse, so all the accessors below stay
	 * available and only the source of `functions` differs.
	 */
	static fromParts(parts: HBCFileParts): HBCFile {
		const file = Object.create(HBCFile.prototype) as HBCFile;
		file.data = parts.data;
		file.version = parts.version;
		file.versionInfo = getVersionInfo(parts.version);
		file.stringTable = parts.stringTable;
		file.arrayBuffer = parts.arrayBuffer;
		file.literalValueBuffer = parts.literalValueBuffer;
		file.objectKeyBuffer = parts.objectKeyBuffer;
		file.objectValueBuffer = parts.objectValueBuffer;
		file.objectShapes = parts.objectShapes;
		file.bigintTable = parts.bigintTable;
		file.functions = parts.functions;
		file.loweredGeneratorWrapperSlotAliases = new Map();
		return file;
	}

	constructor(data: ArrayBufferLike | ArrayBufferView) {
		this.data = ArrayBuffer.isView(data)
			? new Uint8Array(data.buffer, data.byteOffset, data.byteLength)
			: new Uint8Array(data);
		this._parsed = new HermesBytecode(this.data);

		this.version = this._parsed.version;
		this.versionInfo = getVersionInfo(this.version);

		this.stringTable = this._parsed.strings;

		this.arrayBuffer = this._parsed.arrayBuffer;
		this.literalValueBuffer = this._parsed.literalValueBuffer;
		this.objectKeyBuffer = this._parsed.objectKeyBuffer;
		this.objectValueBuffer = this._parsed.objectValueBuffer;
		this.objectShapes = this._parsed.objectShapes;
		this.bigintTable = this._parsed.bigints.map((entry) => entry.bytes);

		this.functions = this._parsed.functions.map((func, id) => {
			let name: string | undefined = this.stringTable[func.functionNameID]
				?.value;
			if (name == 'function-name-stripped') {
				name = undefined;
			}

			const exceptionHandlers = func.excHandlers.map((e) => ({
				tryStart: e.start,
				tryEnd: e.end,
				catchOffset: e.target,
			}));

			return <Function> {
				id,
				offset: func.offset,
				bytecodeLength: func.bytecode.byteLength,
				name,
				paramCount: func.paramCount,
				frameSize: func.frameSize,
				envSize: func.envSize,
				loopDepth: func.loopDepth,
				numberRegCount: func.numberRegCount,
				nonPtrRegCount: func.nonPtrRegCount,
				highestReadCacheIndex: func.highestReadCacheIndex,
				highestWriteCacheIndex: func.highestWriteCacheIndex,
				readCacheSize: func.readCacheSize,
				writeCacheSize: func.writeCacheSize,
				privateNameCacheSize: func.privateNameCacheSize,
				strict: func.strict,
				prohibitInvoke: func.prohibitInvoke,
				functionKind: func.functionKind,
				exceptionHandlers,
				...structureInstructions(
					disassemble(
						func.bytecode,
						this.versionInfo,
						func.frameSize,
						this.data,
						func.offset,
					),
					exceptionHandlers,
				),
			};
		});
	}

	/**
	 * Take over another file's parts and release this one's.
	 *
	 * Once the cold store holds the bundle, the eagerly parsed copy that filled
	 * it is redundant -- but the caller still holds a reference to *this*
	 * object, so dropping it here is the only way the 2.5GB of disassembly
	 * becomes collectable. Adopting the paged parts rather than nulling them
	 * means every accessor keeps working; reads just page in from now on.
	 *
	 * `loweredGeneratorWrapperSlotAliases` is deliberately not adopted: it is
	 * per-file mutable state recorded during lifting, and in the parallel path
	 * lifting happens in workers against their own files, so neither map has
	 * anything the other needs.
	 */
	adoptPartsFrom(other: HBCFile): void {
		this.version = other.version;
		this.versionInfo = other.versionInfo;
		this.stringTable = other.stringTable;
		this.arrayBuffer = other.arrayBuffer;
		this.literalValueBuffer = other.literalValueBuffer;
		this.objectKeyBuffer = other.objectKeyBuffer;
		this.objectValueBuffer = other.objectValueBuffer;
		this.objectShapes = other.objectShapes;
		this.bigintTable = other.bigintTable;
		this.functions = other.functions;
		this._parsed = undefined;
	}

	getString(id: number) {
		const { value } = this.stringTable[id];

		return value;
	}

	/**
	 * Hermes stores each bigint as little-endian two's-complement digits, so a
	 * set top bit is a negative value rather than a large positive one.
	 */
	getBigInt(id: number): bigint {
		const bytes = this.bigintTable[id];
		if (!bytes || bytes.length === 0) return 0n;

		let value = 0n;
		for (let i = bytes.length - 1; i >= 0; i--) {
			value = (value << 8n) | BigInt(bytes[i]!);
		}
		if (bytes[bytes.length - 1]! & 0x80) {
			value -= 1n << BigInt(bytes.length * 8);
		}

		return value;
	}

	getIdentifier(id: number) {
		const { kind, value } = this.stringTable[id];
		if (kind !== StringKind.Identifier) throw new Error();

		return value;
	}

	readSerializedLiterals(
		buffer: Uint8Array,
		byteOffset: number,
		count: number,
		currentTags = this.version >= 97,
	): SerializedLiteralValue[] {
		const view = new DataReader(buffer);
		view.pos = byteOffset;
		const values: SerializedLiteralValue[] = [];

		while (values.length < count) {
			const keyTag = view.UInt8();
			let itemCount = keyTag & 0xF;
			if (keyTag & 0x80) {
				itemCount <<= 8;
				itemCount |= view.UInt8();
			}
			const tag = (keyTag & 0x70) >> 4;

			for (let i = 0; i < itemCount && values.length < count; i++) {
				if (currentTags) {
					switch (tag) {
						case 0:
							values.push(null);
							break;
						case 1:
							values.push(true);
							break;
						case 2:
							values.push(false);
							break;
						case 3:
							values.push(view.Double());
							break;
						case 4:
							values.push(view.StringRef32());
							break;
						case 5:
							values.push(view.StringRef16());
							break;
						case 6:
							values.push(undefined);
							break;
						case 7:
							values.push(view.Int32());
							break;
						default:
							throw new Error(
								`Unknown serialized literal tag: ${tag}`,
							);
					}
				} else {
					switch (tag) {
						case 0:
							values.push(null);
							break;
						case 1:
							values.push(true);
							break;
						case 2:
							values.push(false);
							break;
						case 3:
							values.push(view.Double());
							break;
						case 4:
							values.push(view.StringRef32());
							break;
						case 5:
							values.push(view.StringRef16());
							break;
						case 6:
							values.push(view.StringRef8());
							break;
						case 7:
							values.push(view.UInt32());
							break;
						default:
							throw new Error(
								`Unknown serialized literal tag: ${tag}`,
							);
					}
				}
			}
		}

		return values;
	}

	getArrayBufferElements(
		byteOffset: number,
		count: number,
	): SerializedLiteralValue[] {
		const buffer = this.version >= 97
			? this.literalValueBuffer
			: this.arrayBuffer;
		return this.readSerializedLiterals(buffer, byteOffset, count);
	}

	getObjectKeyBufferElements(
		byteOffset: number,
		count: number,
	): SerializedLiteralValue[] {
		return this.readSerializedLiterals(
			this.objectKeyBuffer,
			byteOffset,
			count,
		);
	}

	getObjectValueBufferElements(
		byteOffset: number,
		count: number,
	): SerializedLiteralValue[] {
		const buffer = this.version >= 97
			? this.literalValueBuffer
			: this.objectValueBuffer;
		return this.readSerializedLiterals(buffer, byteOffset, count);
	}

	getObjectBufferElements(params: {
		noOfStaticElements?: number;
		objectKeyBufferIndex?: number;
		objectValueBufferIndex: number;
		shapeTableIndex?: number;
	}): { keys: SerializedLiteralValue[]; values: SerializedLiteralValue[] } {
		if (this.version >= 97) {
			if (typeof params.shapeTableIndex !== 'number') {
				throw new Error('Missing object shape table index');
			}
			const shape = this.objectShapes[params.shapeTableIndex];
			if (!shape) {
				throw new Error(
					`Invalid object shape table index: ${params.shapeTableIndex}`,
				);
			}
			return {
				keys: this.getObjectKeyBufferElements(
					shape.keyBufferOffset,
					shape.numProps,
				),
				values: this.getObjectValueBufferElements(
					params.objectValueBufferIndex,
					shape.numProps,
				),
			};
		}

		if (
			typeof params.objectKeyBufferIndex !== 'number' ||
			typeof params.noOfStaticElements !== 'number'
		) {
			throw new Error('Missing legacy object buffer metadata');
		}
		return {
			keys: this.getObjectKeyBufferElements(
				params.objectKeyBufferIndex,
				params.noOfStaticElements,
			),
			values: this.getObjectValueBufferElements(
				params.objectValueBufferIndex,
				params.noOfStaticElements,
			),
		};
	}
}
