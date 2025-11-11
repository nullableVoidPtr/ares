import { VersionDelta } from '../VersionInfo.ts';

export default {
	opcodeMap: {
		exclude: ['Unreachable'],
		insertAfter: ['ProfilePoint', 'Unreachable'],
	},
} satisfies VersionDelta;

