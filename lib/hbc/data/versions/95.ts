import { UInt16, UInt32 } from '../../../utils/DataReader.ts';
import { Reg8 } from '../../reader.ts';
import { VersionDelta } from '../VersionInfo.ts';

export default {
	opcodeMap: {
		exclude: [
			'AddS',
			'GetParentEnvironment',
			'GetClosureEnvironment',
			'CreateFunctionEnvironment',
			'CreateTopLevelEnvironment',
			'PutByIdLoose',
			'PutByIdStrict',
			'PutByIdLooseLong',
			'PutByIdStrictLong',
			'TryPutByIdLoose',
			'TryPutByIdStrict',
			'TryPutByIdLooseLong',
			'TryPutByIdStrictLong',
			'PutOwnBySlotIdx',
			'PutOwnBySlotIdxLong',
			'DelByIdLoose',
			'DelByIdStrict',
			'DelByIdLooseLong',
			'DelByIdStrictLong',
			'GetByIndex',
			'PutByValLoose',
			'PutByValStrict',
			'DelByValLoose',
			'DelByValStrict',
			'CallWithNewTarget',
			'CallWithNewTargetLong',
			'GetArgumentsPropByValLoose',
			'GetArgumentsPropByValStrict',
			'ReifyArgumentsStrict',
			'ReifyArgumentsLoose',
		],
		insertAfter: [
			['CreateEnvironment', ['CreateInnerEnvironment']],
			['DeclareGlobalVar', ['ThrowIfHasRestrictedGlobalProperty']],
			['TryGetByIdLong', [
				'PutById',
				'PutByIdLong',
				'TryPutById',
				'TryPutByIdLong',
			]],
			['PutOwnByVal', ['DelById', 'DelByIdLong']],
			['GetByVal', ['PutByVal', 'DelByVal']],
			['Call1', ['CallDirect']],
			['Call4', [
				'CallLong',
				'ConstructLong',
				'CallDirectLongIndex',
			]],
			['CreateClosureLongIndex', [
				'CreateGeneratorClosure',
				'CreateGeneratorClosureLongIndex',
				'CreateAsyncClosure',
				'CreateAsyncClosureLongIndex',
			]],
			['AddEmptyString', ['GetArgumentsPropByVal']],
			['GetArgumentsLength', ['ReifyArguments']],
			['SwitchImm', [
				'StartGenerator',
				'ResumeGenerator',
				'CompleteGenerator',
			]],
			['JmpUndefinedLong', ['SaveGenerator', 'SaveGeneratorLong']],
		],
		append: [
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
		],
	},

	legacyOperands: {
		'NewObjectWithBuffer': [Reg8, UInt16, UInt16, UInt16, UInt16],
		'NewObjectWithBufferLong': [Reg8, UInt16, UInt16, UInt32, UInt32],
	},

	publicBuiltins: {
		exclude: [
			['globalThis', 'Symbol'],
			['globalThis', 'eval'],
		],
	},

	privateBuiltins: {
		insertAfter: [
			['throwTypeError', ['generatorSetDelegated']],
		],
		append: ['getOriginalNativeErrorConstructor'],
	},
} satisfies VersionDelta;
