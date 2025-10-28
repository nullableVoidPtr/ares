export enum NamedStackVariables {
	FirstLocal,
	Scratch,
	DebugEnvironment,
	PreviousFrame,
	SavedIP,
	SavedCodeBlock,
	ArgCount,
	NewTarget,
	CalleeClosureOrCB,
	ThisArg,
	FirstArg,

	// CallerExtraRegistersAtEnd,
	// CalleeExtraRegistersAtStart,
};

export function getStackOffset(bytecodeVersion: number, name: NamedStackVariables): number {
	switch (name) {
		case NamedStackVariables.FirstLocal:
			if (bytecodeVersion >= 94) {
				return 1;
			} else {
				return 2;
			}
		case NamedStackVariables.DebugEnvironment:
			if (bytecodeVersion >= 94) {
				return 0;
			} else {
				return 1;
			}
	}

	return {
		[NamedStackVariables.Scratch]: 0,
		[NamedStackVariables.PreviousFrame]: -1,
		[NamedStackVariables.SavedIP]: -2,
		[NamedStackVariables.SavedCodeBlock]: -3,
		[NamedStackVariables.ArgCount]: -4,
		[NamedStackVariables.NewTarget]: -5,
		[NamedStackVariables.CalleeClosureOrCB]: -6,
		[NamedStackVariables.ThisArg]: -7,
		[NamedStackVariables.FirstArg]: -8,
	}[name];
}