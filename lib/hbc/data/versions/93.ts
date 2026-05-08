import { VersionDelta } from '../VersionInfo.ts';

export default {
	opcodeMap: {
		exclude: [
			'CreateInnerEnvironment',
			'ThrowIfHasRestrictedGlobalProperty',
		],
	},
	privateBuiltins: {
		exclude: ['getOriginalNativeErrorConstructor']
	},
} satisfies VersionDelta;