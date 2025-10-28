import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './71.ts';

export default {
	privateBuiltins: VNEXT.privateBuiltins.filter(
		b => b != "apply",
	),
} satisfies VersionDelta;
