import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './86.ts';

export default {
	opcodeMap: VNEXT.opcodeMap.filter(
		m => ![
			'Add32',
			'Sub32',
			'Mul32',
			'Divi32',
			'Divu32',
			'Loadi8',
			'Loadu8',
			'Loadi16',
			'Loadu16',
			'Loadi32',
			'Loadu32',
			'Store8',
			'Store16',
			'Store32',
			'Inc',
			'Dec',
		].includes(m),
	),
} satisfies VersionDelta;
