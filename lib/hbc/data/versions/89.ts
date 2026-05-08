import { VersionDelta } from '../VersionInfo.ts';

export default {
	privateBuiltins: {
		exclude: ['initRegexNamedGroups'],
	}
} satisfies VersionDelta;