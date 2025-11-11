import { identifier, memberExpression, MemberExpression } from '@babel/types';
import { Operand, RawMnemonic } from '../disassembly/instruction.ts';
import { DataViewStream } from '../utils/DataViewStream.ts';
import VERSION_DELTAS from './versions/mod.ts';

type ArrayDelta<T> = {
	exclude?: T[];
	prepend?: T[];
	append?: T[];
	insertAfter?: [T, T];
} | T[];

export interface VersionDelta {
	opcodeMap?: ArrayDelta<RawMnemonic>;
	legacyOperands?: Partial<Record<RawMnemonic, ((io: DataViewStream) => Operand)[]>>;

	/*
	Regular_expression('User defined','^(// )?(BUILTIN_METHOD|PRIVATE_BUILTIN|JS_BUILTIN)\\((.+)\\)$',true,true,false,false,false,false,'List matches')
	Find_/_Replace({'option':'Regex','string':'(// )?BUILTIN_METHOD\\((.+)\\)'},'\\t$1["$2"],',true,false,true,false)
	Find_/_Replace({'option':'Regex','string':', '},'", ',true,false,true,false)
	Find_/_Replace({'option':'Regex','string':'.+_BUILTIN\\((.+)\\)'},'\\t"$1",',true,false,true,false)
	*/
	publicBuiltins?: ArrayDelta<[string, string]>;
	privateBuiltins?: ArrayDelta<string>;
	jsBuiltins?: ArrayDelta<string>;
}

export interface VersionInfo {
	bytecodeVersion: number;
	opcodeMap: RawMnemonic[];
	legacyOperands: Partial<Record<RawMnemonic, ((io: DataViewStream) => Operand)[]>>;

	builtins: MemberExpression[];
}

export function getVersionInfo(bytecodeVersion: number): VersionInfo {
	const versions = Array.from(VERSION_DELTAS.keys());
	let nearestVersion: number;
	const oldestSupportedVersion = versions[0];
	const latestSupportedVersion = versions[versions.length - 1];
	if (bytecodeVersion <= oldestSupportedVersion) {
		nearestVersion = oldestSupportedVersion;
	} else if (bytecodeVersion >= latestSupportedVersion) {
		nearestVersion = latestSupportedVersion;
	} else {
		const nearestIndex = versions.findLastIndex(k => k < bytecodeVersion);
		if (typeof nearestIndex == 'undefined') throw new Error();
		nearestVersion = versions[nearestIndex + 1];
	}

	let opcodeMap: RawMnemonic[] | undefined;
	let legacyOperands: VersionInfo['legacyOperands'] = {};
	let publicBuiltins: [string, string][] | undefined;
	let privateBuiltins: string[] | undefined;
	let jsBuiltins: string[] | undefined;
	for (let i = versions.length - 1; versions[i] >= nearestVersion; i--) {
		const delta = VERSION_DELTAS.get(versions[i])!;

		if (delta.opcodeMap) {
			if (Array.isArray(delta.opcodeMap)) {
				opcodeMap = delta.opcodeMap;
			} else if (opcodeMap && delta.opcodeMap) {
				const { exclude, prepend, append, insertAfter } = delta.opcodeMap;
				if (exclude) {
					opcodeMap = opcodeMap.filter(o => !exclude.includes(o))
				}
				if (prepend) {
					opcodeMap.unshift(...prepend);
				}
				if (append) {
					opcodeMap.push(...append);
				}
				for (const [after, value] of insertAfter ?? []) {
					const index = opcodeMap.indexOf(<RawMnemonic>after);
					if (index === -1) continue;

					opcodeMap.splice(index + 1, 0, <RawMnemonic>value);
				}
			}
		}
		legacyOperands = {
			...legacyOperands,
			...delta.legacyOperands,
		}

		if (delta.publicBuiltins) {
			if (Array.isArray(delta.publicBuiltins)) {
				publicBuiltins = delta.publicBuiltins;
			} else if (publicBuiltins && delta.publicBuiltins) {
				const { exclude, prepend, append, insertAfter } = delta.publicBuiltins;
				if (exclude) {
					publicBuiltins = publicBuiltins.filter(
						([o, p]) => !exclude.some(([oo, op]) => oo == o && p == op)
					)
				}
				if (prepend) {
					publicBuiltins.unshift(...prepend);
				}
				if (append) {
					publicBuiltins.push(...append);
				}
				for (const [[aftero, afterp], [o, p]] of insertAfter ?? []) {
					const index = publicBuiltins.findIndex(([o, p]) => o == aftero && p == afterp);
					if (index === -1) continue;

					publicBuiltins.splice(index + 1, 0, [o, p]);
				}
			}
		}

		if (delta.privateBuiltins) {
			if (Array.isArray(delta.privateBuiltins)) {
				privateBuiltins = delta.privateBuiltins;
			} else if (privateBuiltins && delta.privateBuiltins) {
				const { exclude, prepend, append, insertAfter } = delta.privateBuiltins;
				if (exclude) {
					privateBuiltins = privateBuiltins.filter(
						b => !exclude.includes(b)
					)
				}
				if (prepend) {
					privateBuiltins.unshift(...prepend);
				}
				if (append) {
					privateBuiltins.push(...append);
				}
				for (const [after, value] of insertAfter ?? []) {
					const index = privateBuiltins.indexOf(after);
					if (index === -1) continue;

					privateBuiltins.splice(index + 1, 0, value);
				}
			}
		}

		if (delta.jsBuiltins) {
			if (Array.isArray(delta.jsBuiltins)) {
				jsBuiltins = delta.jsBuiltins;
			} else if (jsBuiltins && delta.jsBuiltins) {
				const { exclude, prepend, append, insertAfter } = delta.jsBuiltins;
				if (exclude) {
					jsBuiltins = jsBuiltins.filter(
						b => !exclude.includes(b)
					)
				}
				if (prepend) {
					jsBuiltins.unshift(...prepend);
				}
				if (append) {
					jsBuiltins.push(...append);
				}
				for (const [after, value] of insertAfter ?? []) {
					const index = jsBuiltins.indexOf(after);
					if (index === -1) continue;

					jsBuiltins.splice(index + 1, 0, value);
				}
			}
		}
	}

	if (!opcodeMap || !publicBuiltins || !privateBuiltins || !jsBuiltins) {
		throw new Error();
	}

	const builtins: VersionInfo['builtins'] = [];
	for (const [object, property] of publicBuiltins) {
		builtins.push(memberExpression(
			identifier(object),
			identifier(property),
			false,
			false,
		));
	}
	for (const name of privateBuiltins) {
		builtins.push(memberExpression(
			identifier('HermesInternal'),
			identifier(name),
		));
	}
	for (const name of jsBuiltins) {
		builtins.push(memberExpression(
			identifier('HermesInternal'),
			identifier(name),
		));
	}

	return {
		bytecodeVersion,
		opcodeMap,
		legacyOperands,
		builtins, 
	};
}