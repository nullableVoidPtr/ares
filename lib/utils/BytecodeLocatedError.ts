
export type BytecodeLocatedErrorOptions = ErrorOptions & {
	functionId?: number;
	address?: number;
};

export abstract class BytecodeLocatedError extends Error {
	functionId?: number;
	address?: number;

	constructor(message: string, options?: BytecodeLocatedErrorOptions) {
		let suffix = '';
		if (options?.functionId || options?.address) {
			suffix += ` @ `
		}
		if (options?.functionId) {
			suffix += `<function ${options.functionId}>`
			if (options.address) {
				suffix += ':'
			}
		}
		if (options?.address) {
			suffix += `0x${options.address.toString(16).padStart(6, '0')}`
		}
		super(message + suffix, options);

		this.functionId = options?.functionId;
		this.address = options?.address;
	}

	abstract override get name(): string;
}