import { VersionDelta } from '../VersionInfo.ts';

export default {
	opcodeMap: {
		exclude: [
			'IteratorBegin',
			'IteratorNext',
			'IteratorClose',
		],
	},
} satisfies VersionDelta;
