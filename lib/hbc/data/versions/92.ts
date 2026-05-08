import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './95.ts';

export default {
	opcodeMap: VNEXT.opcodeMap,
	privateBuiltins: VNEXT.privateBuiltins,
} satisfies VersionDelta;