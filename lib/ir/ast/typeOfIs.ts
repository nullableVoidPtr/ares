import * as t from '@babel/types';
import {
	TYPEOF_IS_ALL_MASK,
	TYPEOF_IS_TYPES,
	TypeOfIsType,
	typeOfIsTypes,
} from '../../hbc/disassembly/instruction.ts';

export function typeOfIsExpression(value: t.Expression, typeIndex: number) {
	const types = typeOfIsTypes(typeIndex);
	if (types.length === 0) return t.booleanLiteral(false);
	if (typeIndex === TYPEOF_IS_ALL_MASK) return t.booleanLiteral(true);

	const selected = new Set<TypeOfIsType>(types);
	const missing = TYPEOF_IS_TYPES.filter((type) => !selected.has(type));

	const cloneValue = () => t.cloneNode(value);

	const typeOfEquals = (type: string) =>
		t.binaryExpression(
			'===',
			t.unaryExpression('typeof', cloneValue()),
			t.stringLiteral(type),
		);

	const typeOfNotEquals = (type: string) =>
		t.binaryExpression(
			'!==',
			t.unaryExpression('typeof', cloneValue()),
			t.stringLiteral(type),
		);

	const valueEqualsNull = () =>
		t.binaryExpression('===', cloneValue(), t.nullLiteral());

	const valueNotEqualsNull = () =>
		t.binaryExpression('!==', cloneValue(), t.nullLiteral());

	const and = (exprs: t.Expression[]) =>
		exprs.reduce((left, right) => t.logicalExpression('&&', left, right));

	const or = (exprs: t.Expression[]) =>
		exprs.reduce((left, right) => t.logicalExpression('||', left, right));

	const hasExactly = (...wanted: TypeOfIsType[]) =>
		selected.size === wanted.length &&
		wanted.every((type) => selected.has(type));

	const testFor = (type: TypeOfIsType): t.Expression => {
		switch (type) {
			case 'Undefined':
				return typeOfEquals('undefined');
			case 'String':
				return typeOfEquals('string');
			case 'Symbol':
				return typeOfEquals('symbol');
			case 'Boolean':
				return typeOfEquals('boolean');
			case 'Number':
				return typeOfEquals('number');
			case 'Bigint':
				return typeOfEquals('bigint');
			case 'Function':
				return typeOfEquals('function');
			case 'Null':
				return valueEqualsNull();
			case 'Object':
				return and([
					typeOfEquals('object'),
					valueNotEqualsNull(),
				]);
		}
	};

	const notTestFor = (type: TypeOfIsType): t.Expression => {
		switch (type) {
			case 'Undefined':
				return typeOfNotEquals('undefined');
			case 'String':
				return typeOfNotEquals('string');
			case 'Symbol':
				return typeOfNotEquals('symbol');
			case 'Boolean':
				return typeOfNotEquals('boolean');
			case 'Number':
				return typeOfNotEquals('number');
			case 'Bigint':
				return typeOfNotEquals('bigint');
			case 'Function':
				return typeOfNotEquals('function');
			case 'Null':
				return valueNotEqualsNull();
			case 'Object':
				return or([
					typeOfNotEquals('object'),
					valueEqualsNull(),
				]);
		}
	};

	// Object | Null is just JS typeof === "object".
	if (hasExactly('Object', 'Null')) {
		return typeOfEquals('object');
	}

	// Everything except Object | Null is just JS typeof !== "object".
	if (
		missing.length === 2 &&
		missing.includes('Object') &&
		missing.includes('Null')
	) {
		return typeOfNotEquals('object');
	}

	// Everything except undefined: x !== undefined.
	if (missing.length === 1 && missing[0] === 'Undefined') {
		return typeOfNotEquals('undefined');
	}

	// Everything except null: x !== null.
	if (missing.length === 1 && missing[0] === 'Null') {
		return valueNotEqualsNull();
	}

	// Everything except null/undefined: x != null.
	if (
		missing.length === 2 &&
		missing.includes('Null') &&
		missing.includes('Undefined')
	) {
		return t.binaryExpression('!=', cloneValue(), t.nullLiteral());
	}

	// Prefer complement form if it is shorter.
	if (missing.length < types.length) {
		return and(missing.map(notTestFor));
	}

	return or(types.map(testFor));
}
