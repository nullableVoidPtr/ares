import { VersionDelta } from '../VersionInfo.ts';

export default {
	opcodeMap: {
		exclude: [
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
		],
	},
} satisfies VersionDelta;
