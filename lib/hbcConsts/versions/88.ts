import { VersionDelta } from '../VersionInfo.ts';

export default {
	publicBuiltins: {
		exclude: [
			["Date", "now"],
		],
	},
} satisfies VersionDelta;