import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './91.ts';

export default {
	privateBuiltins: VNEXT.privateBuiltins.filter(
		b => b != 'initRegexNamedGroups'
	),
} satisfies VersionDelta;