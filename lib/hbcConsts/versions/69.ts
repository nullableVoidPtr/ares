import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './70.ts';

export default {
	privateBuiltins: VNEXT.privateBuiltins.filter(
		b => b != "arraySpread",
	),
} satisfies VersionDelta;
