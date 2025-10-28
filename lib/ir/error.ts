import { BytecodeLocatedError } from '../utils/BytecodeLocatedError.ts';

export class LiftError extends BytecodeLocatedError {
	override get name() { return 'LiftingError' }
}
