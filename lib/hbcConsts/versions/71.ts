import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './75.ts';

export default {
	privateBuiltins: VNEXT.privateBuiltins.filter(
		b => b != "getEpilogues",
	),
} satisfies VersionDelta;
