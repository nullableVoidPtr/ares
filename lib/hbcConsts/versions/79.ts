import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './81.ts';

export default {
	opcodeMap: VNEXT.opcodeMap.filter(
		m => ![
			'CallBuiltinLong',
		].includes(m),
	),
} satisfies VersionDelta;
