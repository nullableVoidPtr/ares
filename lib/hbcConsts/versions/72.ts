import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './79.ts';

export default {
	opcodeMap: VNEXT.opcodeMap.filter(
		m => ![
			'IteratorBegin',
			'IteratorNext',
			'IteratorClose',
		].includes(m),
	),
} satisfies VersionDelta;
