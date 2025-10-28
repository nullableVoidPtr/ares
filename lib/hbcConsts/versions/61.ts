import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './69.ts';

export default {
	privateBuiltins: VNEXT.privateBuiltins.filter(
		b => b != "exponentiationOperator",
	),
} satisfies VersionDelta;
