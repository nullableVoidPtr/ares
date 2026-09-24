import { VersionDelta } from '../VersionInfo.ts';

export default {
	opcodeMap: {
		exclude: ['NewTypedObjectWithBuffer', 'ToUint32'],
		insertAfter: [
			['FastArrayAppend', ['CacheNewObject']],
		],
	},
	privateBuiltins: {
		exclude: [
			'copyRestArgsFast',
			'checkedTypeCast',
			'setFunctionName',
			'fastArrayPop',
			'fastArraySlice',
		],
	},
	jsBuiltins: {
		exclude: ['awaitAsyncIterator'],
	},
} satisfies VersionDelta;
