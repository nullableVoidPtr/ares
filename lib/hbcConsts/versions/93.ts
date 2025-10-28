import { VersionDelta } from '../VersionInfo.ts';
import VNEXT from './95.ts';

export default {
	opcodeMap: VNEXT.opcodeMap.filter(
		m => ![
			'CreateInnerEnvironment',
			'ThrowIfHasRestrictedGlobalProperty',
		].includes(m)
	),
	privateBuiltins: VNEXT.privateBuiltins.filter(
		b => b != 'getOriginalNativeErrorConstructor'
	),
} satisfies VersionDelta;