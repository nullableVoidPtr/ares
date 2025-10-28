import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './89.ts';

export default {
	privateBuiltins: VNEXT.privateBuiltins.filter(
		b => b != 'getMethod'
	),
} satisfies VersionDelta;