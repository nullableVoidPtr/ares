import { VersionDelta } from '../VersionInfo.ts';
import VREVERT from './93.ts';

export default {
	opcodeMap: VREVERT.opcodeMap,
	privateBuiltins: VREVERT.privateBuiltins,
} satisfies VersionDelta;