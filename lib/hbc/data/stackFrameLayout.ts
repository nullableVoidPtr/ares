import { VersionInfo } from './VersionInfo.ts';

export enum NamedStackVariables {
	FirstLocal,
	Scratch,
	DebugEnvironment,
	PreviousFrame,
	SavedIP,
	SavedCodeBlock,
	SHLocals,
	ArgCount,
	NewTarget,
	CalleeClosureOrCB,
	ThisArg,
	FirstArg,
	// CallerExtraRegistersAtEnd,
	// CalleeExtraRegistersAtStart,
}

export function getStackOffset(
	version: number | VersionInfo,
	name: NamedStackVariables,
): number {
	if (typeof version != 'number') {
		version = version.bytecodeVersion;
	}

	if (version < 97 && name == NamedStackVariables.SHLocals) {
		throw new Error();
	}

	switch (name) {
		case NamedStackVariables.FirstLocal:
			return version >= 94 ? 1 : 2;
		case NamedStackVariables.DebugEnvironment:
			return version >= 94 ? 0 : 1;
	}

	// v97+ (SH layout) inserts SHLocals at -4, shifting ArgCount and everything
	// below it one slot further negative.
	if (version >= 97) {
		return {
			[NamedStackVariables.Scratch]: 0,
			[NamedStackVariables.PreviousFrame]: -1,
			[NamedStackVariables.SavedIP]: -2,
			[NamedStackVariables.SavedCodeBlock]: -3,
			[NamedStackVariables.SHLocals]: -4,
			[NamedStackVariables.ArgCount]: -5,
			[NamedStackVariables.NewTarget]: -6,
			[NamedStackVariables.CalleeClosureOrCB]: -7,
			[NamedStackVariables.ThisArg]: -8,
			[NamedStackVariables.FirstArg]: -9,
		}[name];
	}

	return ({
		[NamedStackVariables.Scratch]: 0,
		[NamedStackVariables.PreviousFrame]: -1,
		[NamedStackVariables.SavedIP]: -2,
		[NamedStackVariables.SavedCodeBlock]: -3,
		[NamedStackVariables.ArgCount]: -4,
		[NamedStackVariables.NewTarget]: -5,
		[NamedStackVariables.CalleeClosureOrCB]: -6,
		[NamedStackVariables.ThisArg]: -7,
		[NamedStackVariables.FirstArg]: -8,
	} as Record<number, number>)[name];
}
