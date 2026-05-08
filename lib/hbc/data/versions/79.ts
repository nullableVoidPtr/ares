import { VersionDelta } from '../VersionInfo.ts';

export default {
	opcodeMap: {
		exclude: [
			'CallBuiltinLong',
		],
	},
} satisfies VersionDelta;
