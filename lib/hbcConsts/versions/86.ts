import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './92.ts';

export default {
	opcodeMap: VNEXT.opcodeMap.filter(
		m => ![
			'LoadConstBigInt',
			'LoadConstBigIntLongIndex',
			'ToNumeric',
		].includes(m),
	),
} satisfies VersionDelta;
