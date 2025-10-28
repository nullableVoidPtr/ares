import fs from "node:fs";
import type { Buffer } from "node:buffer";
// deno-lint-ignore no-sloppy-imports
import { type HermesBytecode, default as init } from "./wasm/build/hermes_bytecode.mjs";
import { Function } from '../disassembly/function.ts';
import { structureInstructions } from '../disassembly/mod.ts';
import { disassemble } from './bytecode.ts';
import { getVersionInfo, VersionInfo } from '../hbcConsts/VersionInfo.ts';

const { HermesBytecode } = await init();

enum StringKind {
	STRING = 0,
	IDENTIFIER = 1,
}

interface KindedString {
	kind: StringKind,
	value: string,
}

interface Vector<T> {
	size(): number;
	get(i: number): T | undefined;
}

function mapVector<T, R>(vector: Vector<T>, callback: (e: T, i: number) => R ): R[] {
	const result: R[] = [];
	for (let i = 0; i < vector.size(); i++) {
		result.push(callback(vector.get(i)!, i));
	}

	return result;
}

export class HBCFile {
	version: number;
	versionInfo: VersionInfo;

	stringTable: KindedString[];
	functions: Function[];

	_parsed: HermesBytecode;

	static fromFile(path: string) {
		return HBCFile.fromBytes(fs.readFileSync(path));
	}

	static fromBytes(data: Buffer) {
		return new HBCFile(
			new HermesBytecode(new Uint8Array(data))
		);
	}

	constructor(parsed: HermesBytecode) {
		this._parsed = parsed;

		this.version = parsed.version;
		this.versionInfo = getVersionInfo(this.version)

		const utf8Decoder = new TextDecoder('utf-8');
		const utf16Decoder = new TextDecoder('utf-16le');
		this.stringTable = mapVector(parsed.strings, (entry) => ({
			kind: entry.kind,
			value: (entry.isUTF16 ? utf16Decoder : utf8Decoder).decode(entry.value),
		}));

		this.functions = mapVector(parsed.functions, (func, id) => {
			let name: string | undefined = this.stringTable[func.functionNameID]?.value;
			if (name == 'function-name-stripped') {
				name = undefined;
			}

			const exceptionHandlers = mapVector(func.excHandlers, (e) => ({
				tryStart: e.start,
				tryEnd: e.end,
				catchOffset: e.target,
			})); 

			return <Function>{
				id,
				offset: func.offset,
				name,
				paramCount: func.paramCount,
				frameSize: func.frameSize,
				envSize: func.envSize,
				highestReadCacheIndex: func.highestReadCacheIndex,
				highestWriteCacheIndex: func.highestWriteCacheIndex,
				strict: func.strict,
				prohibitInvoke: func.prohibitInvoke,
				exceptionHandlers,
				...structureInstructions(
					disassemble(func.bytecode.buffer, this.versionInfo, this.version, func.frameSize),
					exceptionHandlers,
				),
			}
		});
	}

	getString(id: number) {
		const { value } = this.stringTable[id];

		return value;
	}

	getIdentifier(id: number) {
		const { kind, value } = this.stringTable[id];
		if (kind !== StringKind.IDENTIFIER) throw new Error();

		return value;
	}
}