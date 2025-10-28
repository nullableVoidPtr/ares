import { VersionDelta } from '../VersionInfo.ts';
import { Reg8 } from '../../utils/DataViewStream.ts';

export default {
	legacyOperands: {
		"DirectEval": [Reg8, Reg8],
	},
} satisfies VersionDelta;
