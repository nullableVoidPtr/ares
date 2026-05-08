import { VersionDelta } from '../VersionInfo.ts';

export default {
	opcodeMap: {
		exclude: [
			'LoadConstBigInt',
			'LoadConstBigIntLongIndex',
			'ToNumeric',
		],
	},
} satisfies VersionDelta;
