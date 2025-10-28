import { identifier, memberExpression, MemberExpression } from '@babel/types';
import { Operand, RawMnemonic } from '../disassembly/instruction.ts';
import { DataViewStream } from '../utils/DataViewStream.ts';
import VERSION_DELTAS from './versions/mod.ts';

export interface VersionDelta {
	opcodeMap?: RawMnemonic[];
	legacyOperands?: Partial<Record<RawMnemonic, ((io: DataViewStream) => Operand)[]>>;

	/*
	Regular_expression('User defined','^(// )?(BUILTIN_METHOD|PRIVATE_BUILTIN|JS_BUILTIN)\\((.+)\\)$',true,true,false,false,false,false,'List matches')
	Find_/_Replace({'option':'Regex','string':'(// )?BUILTIN_METHOD\\((.+)\\)'},'\\t$1["$2"],',true,false,true,false)
	Find_/_Replace({'option':'Regex','string':', '},'", ',true,false,true,false)
	Find_/_Replace({'option':'Regex','string':'.+_BUILTIN\\((.+)\\)'},'\\t"$1",',true,false,true,false)
	*/
	publicBuiltins?: string[][];
	privateBuiltins?: string[];
	jsBuiltins?: string[];
}

export interface VersionInfo {
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

	let opcodeMap: VersionInfo['opcodeMap'] | undefined;
	let legacyOperands: VersionInfo['legacyOperands'] = {};
	let publicBuiltins: VersionDelta['publicBuiltins'] | undefined;
	let privateBuiltins: VersionDelta['privateBuiltins'] | undefined;
	let jsBuiltins: VersionDelta['jsBuiltins'] | undefined;
	for (let i = versions.length - 1; versions[i] >= nearestVersion; i--) {
		const delta = VERSION_DELTAS.get(versions[i])!;

		opcodeMap = delta.opcodeMap ?? opcodeMap;
		legacyOperands = {
			...legacyOperands,
			...delta.legacyOperands,
		}
		publicBuiltins = delta.publicBuiltins ?? publicBuiltins;
		privateBuiltins = delta.privateBuiltins ?? privateBuiltins;
		jsBuiltins = delta.jsBuiltins ?? jsBuiltins;
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
		opcodeMap,
		legacyOperands,
		builtins, 
	};
}