import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './82.ts';

export default {
	opcodeMap: VNEXT.opcodeMap.filter(
		m => ![
			'GetBuiltinClosure',
			'CreateAsyncClosure',
			'ToNumeric',
		].includes(m),
	),
} satisfies VersionDelta;
