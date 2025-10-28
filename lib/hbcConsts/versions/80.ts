import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './81.ts';

export default {
	opcodeMap: VNEXT.opcodeMap.filter(
		m => ![
			'ThrowIfEmpty',
			'LoadConstEmpty',
		].includes(m),
	),
} satisfies VersionDelta;
