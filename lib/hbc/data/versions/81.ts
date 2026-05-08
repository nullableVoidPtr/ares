import { VersionDelta } from '../VersionInfo.ts';

export default {
	opcodeMap: {
		exclude: [
			'GetBuiltinClosure',
			'CreateAsyncClosure',
			'ToNumeric',
		],
	},
} satisfies VersionDelta;
