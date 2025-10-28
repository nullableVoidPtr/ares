import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './84.ts';

export default {
	opcodeMap: [
		...VNEXT.opcodeMap.slice(1, VNEXT.opcodeMap.indexOf('CreateClosure')),
		'Unreachable',
		...VNEXT.opcodeMap.slice(VNEXT.opcodeMap.indexOf('CreateClosure')),
	],
} satisfies VersionDelta;

