import { identifier, MemberExpression, memberExpression } from '@babel/types';
import type { Operand, RawMnemonic } from '../disassembly/instruction.ts';
import { DataReader } from '../../utils/DataReader.ts';
import VERSION_DELTAS from './versions/mod.ts';
import { applyArrayDelta, ArrayDelta } from './arrayDelta.ts';

export interface VersionDelta {
	opcodeMap?: ArrayDelta<RawMnemonic>;
	legacyOperands?: Partial<
		Record<RawMnemonic, ((io: DataReader) => Operand)[]>
	>;

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
	legacyOperands: Partial<
		Record<RawMnemonic, ((io: DataReader) => Operand)[]>
	>;

	builtins: MemberExpression[];
}

function sameBuiltin(
	left: readonly [string, string],
	right: readonly [string, string],
): boolean {
	return left[0] === right[0] && left[1] === right[1];
}

export function getVersionInfo(bytecodeVersion: number): VersionInfo {
	const versions = Array.from(VERSION_DELTAS.keys()).toSorted((a, b) =>
		a - b
	);
	let nearestVersion: number;
	const oldestSupportedVersion = versions[0];
	const latestSupportedVersion = versions[versions.length - 1];
	if (bytecodeVersion <= oldestSupportedVersion) {
		nearestVersion = oldestSupportedVersion;
	} else if (bytecodeVersion >= latestSupportedVersion) {
		nearestVersion = latestSupportedVersion;
	} else if (versions.includes(bytecodeVersion)) {
		nearestVersion = bytecodeVersion;
	} else {
		const nearestIndex = versions.findLastIndex((k) => k < bytecodeVersion);
		if (nearestIndex === -1) {
			throw new Error(`No supported version before ${bytecodeVersion}`);
		}
		nearestVersion = versions[nearestIndex];
	}

	let opcodeMap: RawMnemonic[] | undefined;
	let legacyOperands: VersionInfo['legacyOperands'] = {};
	let publicBuiltins: [string, string][] | undefined;
	let privateBuiltins: string[] | undefined;
	let jsBuiltins: string[] | undefined;
	for (let i = versions.length - 1; versions[i] >= nearestVersion; i--) {
		const delta = VERSION_DELTAS.get(versions[i])!;

		opcodeMap = applyArrayDelta(opcodeMap, delta.opcodeMap);
		legacyOperands = {
			...legacyOperands,
			...delta.legacyOperands,
		};
		publicBuiltins = applyArrayDelta(
			publicBuiltins,
			delta.publicBuiltins,
			sameBuiltin,
		);
		privateBuiltins = applyArrayDelta(
			privateBuiltins,
			delta.privateBuiltins,
		);
		jsBuiltins = applyArrayDelta(jsBuiltins, delta.jsBuiltins);
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
