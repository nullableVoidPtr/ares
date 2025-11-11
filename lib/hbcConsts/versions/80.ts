import { VersionDelta } from '../VersionInfo.ts';

export default {
	opcodeMap: {
		exclude: [
			'ThrowIfEmpty',
			'LoadConstEmpty',
		],
	},
} satisfies VersionDelta;
