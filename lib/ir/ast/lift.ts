import { assert } from 'node:console';
import * as t from '@babel/types';
import generate from '@babel/generator';
import {
	FunctionRef,
	HermesEmpty,
	isBigIntRef,
	isStringRef,
	type LoadConstInst,
	StringRef,
} from '../../hbc/disassembly/instruction.ts';
import { type SerializedLiteralValue } from '../../parser/file.ts';
import {
	SSABasicBlock,
	SSAFunction,
	SSAInstruction,
	SSARegister,
} from '../../ssa.ts';
import { exceptionHandlersByAddress } from '../../hbc/utils/exceptions.ts';
import { ssaLivenessAnalysis } from '../../utils/liveness.ts';
import { IRFunction } from '../function/mod.ts';
import { LiftError } from '../error.ts';
import { IRBlock, LiftedAST, LiftedExtra } from './mod.ts';
import { typeOfIsExpression } from './typeOfIs.ts';
import { tagStorageLocation } from './alias.ts';

let DEBUG_LITERAL_SLICE = false;
let DEBUG_LITERAL_SLICE_FUNCTION: string | undefined;
try {
	DEBUG_LITERAL_SLICE_FUNCTION = Deno.env.get('ARES_DEBUG_LITERAL_SLICE');
	DEBUG_LITERAL_SLICE = DEBUG_LITERAL_SLICE_FUNCTION != null &&
		DEBUG_LITERAL_SLICE_FUNCTION !== '0';
} catch { /**/ }

function debugLiteralSlice(
	func: IRFunction,
	...args: unknown[]
) {
	if (!DEBUG_LITERAL_SLICE) return;
	if (
		DEBUG_LITERAL_SLICE_FUNCTION &&
		DEBUG_LITERAL_SLICE_FUNCTION !== '1' &&
		DEBUG_LITERAL_SLICE_FUNCTION !== String(func.id)
	) return;
	console.error('[literal-slice]', ...args);
}

function registerAsIdentifier(
	register: SSARegister | undefined,
	extra?: LiftedExtra,
) {
	if (!register) throw new Error();

	const id: LiftedAST<t.Identifier> = t.identifier(
		`r${register.index}_${register.version}`,
	);
	id.extra = { ...extra, sourceRegister: register };

	return id;
}

function declareConst(
	id: t.Identifier,
	init: t.Expression,
	extra?: LiftedExtra,
) {
	const decl: LiftedAST<t.VariableDeclaration> = t.variableDeclaration(
		'const',
		[
			t.variableDeclarator(
				id,
				init,
			),
		],
	);
	decl.extra = extra;

	return decl;
}

/** A register the lifter goes on to mutate, so `const` will not do. */
function declareLet(
	destination: SSARegister,
	init: t.Expression,
	extra?: LiftedExtra,
) {
	const decl: LiftedAST<t.VariableDeclaration> = t.variableDeclaration(
		'let',
		[t.variableDeclarator(registerAsIdentifier(destination), init)],
	);
	decl.extra = extra;
	return decl;
}

function assignRegister(
	destination: SSARegister,
	expr: t.Expression,
	declExtra?: LiftedExtra,
	initExtra?: LiftedExtra,
) {
	if (!expr.extra) {
		expr.extra = initExtra;
	} else {
		expr.extra = {
			...initExtra,
			...expr.extra,
		};
	}

	const decl = declareConst(
		registerAsIdentifier(destination),
		expr,
		declExtra,
	);

	return decl;
}

function loadConstValueNode(
	func: IRFunction,
	value: LoadConstInst['value'],
): t.Expression {
	if (isStringRef(value)) return func.fromStringRef(value);
	if (isBigIntRef(value)) return func.fromBigIntRef(value);
	if (value === HermesEmpty) return t.identifier('__hermes_empty__');
	return t.valueToNode(value);
}

function asAssigningIntrinsic(
	instruction: string,
	destination: SSARegister,
	args: t.Expression[],
	extra?: LiftedExtra,
) {
	const call = t.callExpression(t.v8IntrinsicIdentifier(instruction), args);
	call.extra = extra;
	const assign = declareConst(
		registerAsIdentifier(destination),
		call,
	);
	assign.extra = extra;

	return assign;
}

// `const [r0, r1, …] = %instruction(args)` — for instructions that initialise
// multiple destination registers in one operation (e.g. GetPNameList).
function asMultiAssigningIntrinsic(
	instruction: string,
	destinations: SSARegister[],
	args: t.Expression[],
	extra?: LiftedExtra,
): LiftedAST<t.VariableDeclaration> {
	const call = t.callExpression(t.v8IntrinsicIdentifier(instruction), args);
	call.extra = extra;
	const decl: LiftedAST<t.VariableDeclaration> = t.variableDeclaration(
		'const',
		[
			t.variableDeclarator(
				t.arrayPattern(
					destinations.map((d) => registerAsIdentifier(d)),
				),
				call,
			),
		],
	);
	decl.extra = extra;
	return decl;
}

function getFunctionRef(ref: FunctionRef, extra?: LiftedExtra) {
	const call = t.callExpression(
		t.v8IntrinsicIdentifier('getFunctionById'),
		[t.valueToNode(ref.functionId)],
	);
	call.extra = <LiftedExtra> { ...extra, ref };

	return call;
}

function memberById(
	func: IRFunction,
	instr: SSAInstruction & {
		uses: { object?: SSARegister };
		property: StringRef;
	},
	extra?: LiftedExtra,
) {
	const property = func.fromIdentifierRef(instr.property);
	if (extra?.memberReadDestination) {
		property.extra = {
			...property.extra,
			memberReadDestination: extra.memberReadDestination,
		};
	}
	const memberExpr = t.memberExpression(
		registerAsIdentifier(instr.uses.object),
		property,
		t.isStringLiteral(property),
	);
	memberExpr.extra = extra;

	return memberExpr;
}

// `%expectEnvironment(handle)[slot]`. Environment resolution keys on this exact
// shape, so every reader and writer of a slot must build it identically.
function environmentSlotMember(
	instr: SSAInstruction & {
		uses: { environment?: SSARegister };
		slotIndex: number;
	},
	extra?: LiftedExtra,
) {
	const envCall = t.callExpression(
		t.v8IntrinsicIdentifier('expectEnvironment'),
		[registerAsIdentifier(instr.uses.environment)],
	);
	envCall.extra = extra;
	return t.memberExpression(
		envCall,
		t.valueToNode(instr.slotIndex),
		true,
	);
}

function serializedLiteralToNode(
	func: IRFunction,
	value: SerializedLiteralValue,
): t.Expression {
	if (typeof value === 'undefined') return t.identifier('undefined');
	if (value === null) return t.nullLiteral();
	if (typeof value === 'boolean') return t.valueToNode(value);
	if (typeof value === 'number') return t.valueToNode(value);
	if (isStringRef(value)) {
		return t.stringLiteral(func.file.getString(value.stringTableIndex));
	}
	throw new Error(`Unknown serialized literal value: ${value}`);
}

function shapeKeyToMemberProperty(
	func: IRFunction,
	value: SerializedLiteralValue,
): { property: t.Expression; computed: boolean } {
	if (isStringRef(value)) {
		const name = func.file.getString(value.stringTableIndex);
		if (t.isValidIdentifier(name)) {
			return { property: t.identifier(name), computed: false };
		}
		return { property: t.stringLiteral(name), computed: true };
	}

	return { property: serializedLiteralToNode(func, value), computed: true };
}

function objectShapeSlotMember(
	func: IRFunction,
	object: SSARegister,
	slotIndex: number,
	objectShapeKeysByRegister: Map<string, SerializedLiteralValue[]>,
	extra?: LiftedExtra,
) {
	const objectId = registerAsIdentifier(object);
	const keys = objectShapeKeysByRegister.get(
		`${object.index}_${object.version}`,
	);
	const key = keys?.[slotIndex];
	if (typeof key === 'undefined') {
		const fallback = t.memberExpression(
			objectId,
			t.numericLiteral(slotIndex),
			true,
		);
		fallback.extra = extra;
		return fallback;
	}

	const { property, computed } = shapeKeyToMemberProperty(func, key);
	const member = t.memberExpression(objectId, property, computed);
	member.extra = extra;
	return member;
}

const LARGE_CONSTRUCTION_SLICE_MIN_INSTRUCTIONS = 128;

type TrackedLiteralValue =
	| { kind: 'expr'; expr: t.Expression }
	| { kind: 'builder'; builder: LiteralBuilder };

type LiteralBuilder = ObjectLiteralBuilder | ArrayLiteralBuilder;

interface BaseLiteralBuilder {
	register: SSARegister;
	propertyKeys: Set<string>;
	embeddedUses: number;
}

interface ObjectLiteralBuilder extends BaseLiteralBuilder {
	kind: 'object';
	expr: LiftedAST<t.ObjectExpression>;
}

interface ArrayLiteralBuilder extends BaseLiteralBuilder {
	kind: 'array';
	expr: LiftedAST<t.ArrayExpression>;
}

function ssaRegisterKey(register: SSARegister): string {
	return `${register.index}_${register.version}`;
}

function ssaRegisterFromValue(value: unknown): SSARegister | null {
	if (
		typeof value !== 'object' || value === null ||
		!('index' in value) || !('version' in value)
	) return null;
	const register = value as { index: unknown; version: unknown };
	if (
		typeof register.index !== 'number' ||
		typeof register.version !== 'number'
	) return null;
	return register as SSARegister;
}

function ssaInstructionUseRecord(
	instr: SSAInstruction,
): Record<string, unknown> | null {
	if (!('uses' in instr)) return null;
	const uses: Record<string, unknown> = instr.uses;
	return uses;
}

function ssaInstructionUses(instr: SSAInstruction): SSARegister[] {
	if ('sources' in instr) return [...instr.sources.values()];
	const uses = ssaInstructionUseRecord(instr);
	if (!uses) return [];
	const registers: SSARegister[] = [];
	for (const value of Object.values(uses)) {
		if (Array.isArray(value)) {
			for (const entry of value) {
				const register = ssaRegisterFromValue(entry);
				if (register) registers.push(register);
			}
			continue;
		}
		const register = ssaRegisterFromValue(value);
		if (register) registers.push(register);
	}
	return registers;
}

function instructionUsesAny(
	instr: SSAInstruction,
	registers: Set<string>,
): boolean {
	return ssaInstructionUses(instr).some((register) =>
		registers.has(ssaRegisterKey(register))
	);
}

function cloneExpr(expr: t.Expression): t.Expression {
	return t.cloneNode(expr, true) as t.Expression;
}

function builderExpression(builder: LiteralBuilder): t.Expression {
	return builder.expr as t.Expression;
}

function trackedExpressionForRegister(
	register: SSARegister,
	values: Map<string, TrackedLiteralValue>,
): t.Expression {
	const tracked = values.get(ssaRegisterKey(register));
	if (!tracked) return registerAsIdentifier(register);
	if (tracked.kind === 'expr') return cloneExpr(tracked.expr);
	tracked.builder.embeddedUses++;
	return builderExpression(tracked.builder);
}

function trackedConstructionValueForRegister(
	register: SSARegister,
	values: Map<string, TrackedLiteralValue>,
): t.Expression | null {
	const tracked = values.get(ssaRegisterKey(register));
	if (!tracked) return null;
	if (tracked.kind === 'expr') return cloneExpr(tracked.expr);
	tracked.builder.embeddedUses++;
	return builderExpression(tracked.builder);
}

function objectPropertyIdentity(
	key: t.Expression | t.PrivateName,
	computed?: boolean | null,
): string {
	if (!computed && t.isIdentifier(key)) return `id:${key.name}`;
	if (t.isStringLiteral(key)) return `str:${key.value}`;
	return generate(key).code;
}

function objectLiteralPropertyKey(
	func: IRFunction,
	property: StringRef,
): { key: t.Expression; computed: boolean; identity: string } {
	const key = func.fromIdentifierRef(property);
	const computed = t.isStringLiteral(key);
	const identity = objectPropertyIdentity(key, computed);
	return { key, computed, identity };
}

function pushObjectBuilderProperty(
	builder: LiteralBuilder,
	key: t.Expression,
	value: t.Expression,
	computed: boolean,
	identity: string,
): boolean {
	if (builder.kind !== 'object') return false;
	const property = t.objectProperty(key, value, computed);
	if (builder.propertyKeys.has(identity)) {
		const properties = builder.expr.properties;
		for (let i = properties.length - 1; i >= 0; i--) {
			const existing = properties[i];
			if (!t.isObjectProperty(existing)) continue;
			if (
				objectPropertyIdentity(existing.key, existing.computed) !==
					identity
			) continue;
			properties[i] = property;
			return true;
		}
	}
	builder.propertyKeys.add(identity);
	builder.expr.properties.push(property);
	return true;
}

function pushArrayBuilderElement(
	builder: LiteralBuilder,
	index: number,
	value: t.Expression,
): boolean {
	if (builder.kind !== 'array') return false;
	if (!Number.isSafeInteger(index) || index < 0) return false;
	const elements = builder.expr.elements;
	while (elements.length < index) elements.push(null);
	if (typeof elements[index] !== 'undefined') {
		elements[index] = value;
		return true;
	}
	elements[index] = value;
	return true;
}

function newLiteralBuilder(
	func: IRFunction,
	instr: SSAInstruction,
	extra: LiftedExtra,
	objectShapeKeysByRegister: Map<string, SerializedLiteralValue[]>,
): LiteralBuilder | null {
	switch (instr.instruction) {
		case 'NewObject': {
			const destination = instr.defs.destination;
			const expr = t.objectExpression([]) as LiftedAST<
				t.ObjectExpression
			>;
			expr.extra = extra;
			return {
				kind: 'object',
				register: destination,
				expr,
				propertyKeys: new Set(),
				embeddedUses: 0,
			};
		}
		case 'NewObjectWithBuffer': {
			const destination = instr.defs.destination;
			const registerKey = ssaRegisterKey(destination);
			const { keys, values } = func.file.getObjectBufferElements(instr);
			if (typeof instr.shapeTableIndex !== 'undefined') {
				objectShapeKeysByRegister.set(registerKey, keys);
			}
			const propertyKeys = new Set<string>();
			const properties = keys.map((key, i) => {
				let propertyKey = serializedLiteralToNode(func, key);
				let computed = undefined;
				if (
					t.isStringLiteral(propertyKey) &&
					t.isValidIdentifier(propertyKey.value, false)
				) {
					propertyKey = t.identifier(propertyKey.value);
					computed = false;
				}
				const identity = objectPropertyIdentity(
					propertyKey,
					computed,
				);
				propertyKeys.add(identity);
				return t.objectProperty(
					propertyKey,
					serializedLiteralToNode(func, values[i]),
					computed,
				);
			});
			const expr = t.objectExpression(properties) as LiftedAST<
				t.ObjectExpression
			>;
			expr.extra = {
				...extra,
				objectShapeKeys: typeof instr.shapeTableIndex !== 'undefined'
					? keys
					: undefined,
			};
			return {
				kind: 'object',
				register: destination,
				expr,
				propertyKeys,
				embeddedUses: 0,
			};
		}
		case 'NewArray': {
			const destination = instr.defs.destination;
			const expr = t.arrayExpression(
				Array.from({ length: instr.size }, () => null),
			) as LiftedAST<t.ArrayExpression>;
			expr.extra = extra;
			return {
				kind: 'array',
				register: destination,
				expr,
				propertyKeys: new Set(),
				embeddedUses: 0,
			};
		}
		case 'NewArrayWithBuffer': {
			const destination = instr.defs.destination;
			const elements = func.file.getArrayBufferElements(
				instr.arrayBufferIndex,
				instr.noOfStaticElements,
			);
			const expr = t.arrayExpression(
				elements.map((e) => serializedLiteralToNode(func, e)),
			) as LiftedAST<t.ArrayExpression>;
			expr.extra = extra;
			return {
				kind: 'array',
				register: destination,
				expr,
				propertyKeys: new Set(),
				embeddedUses: 0,
			};
		}
		default:
			return null;
	}
}

function loadParamValueNode(
	func: IRFunction,
	instr: SSAInstruction,
): t.Expression {
	if (instr.instruction !== 'LoadParam') throw new Error();
	if (instr.parameterIndex >= func.paramCount) {
		return tagStorageLocation(
			t.memberExpression(
				t.identifier('arguments'),
				t.numericLiteral(instr.parameterIndex),
				true,
			),
			{
				kind: 'parameter',
				owner: { functionId: func.id },
				parameter: {
					index: instr.parameterIndex,
					form: 'overflow',
				},
			},
		);
	}
	return func.getParam(instr.parameterIndex);
}

function recordLiteralWrite(
	func: IRFunction,
	instr: SSAInstruction,
	builders: Map<string, LiteralBuilder>,
	values: Map<string, TrackedLiteralValue>,
	objectShapeKeysByRegister: Map<string, SerializedLiteralValue[]>,
): boolean {
	switch (instr.instruction) {
		case 'PutById':
		case 'DefineOwnById':
		case 'PutNewOwnById': {
			const object = instr.uses.object;
			const builder = builders.get(ssaRegisterKey(object));
			if (!builder) return false;
			const valueExpr = trackedConstructionValueForRegister(
				instr.uses.value,
				values,
			);
			if (!valueExpr) return false;
			const { key, computed, identity } = objectLiteralPropertyKey(
				func,
				instr.property,
			);
			return pushObjectBuilderProperty(
				builder,
				key,
				valueExpr,
				computed,
				identity,
			);
		}
		case 'PutOwnBySlotIdx': {
			const object = instr.uses.object;
			const builder = builders.get(ssaRegisterKey(object));
			if (!builder) return false;
			const valueExpr = trackedConstructionValueForRegister(
				instr.uses.value,
				values,
			);
			if (!valueExpr) return false;
			const keys = objectShapeKeysByRegister.get(ssaRegisterKey(object));
			const key = keys?.[instr.slotIndex];
			if (typeof key === 'undefined') return false;
			const { property, computed } = shapeKeyToMemberProperty(func, key);
			return pushObjectBuilderProperty(
				builder,
				property,
				valueExpr,
				computed,
				generate(property).code,
			);
		}
		case 'DefineOwnByIndex': {
			const object = instr.uses.object;
			const builder = builders.get(ssaRegisterKey(object));
			if (!builder) return false;
			const valueExpr = trackedConstructionValueForRegister(
				instr.uses.value,
				values,
			);
			if (!valueExpr) return false;
			return pushArrayBuilderElement(builder, instr.property, valueExpr);
		}
		default:
			return false;
	}
}

function terminalStatementWithLiteral(
	func: IRFunction,
	instr: SSAInstruction,
	root: LiteralBuilder,
	values: Map<string, TrackedLiteralValue>,
	extra: LiftedExtra,
): LiftedAST<t.Statement> | null {
	const rootKey = ssaRegisterKey(root.register);
	switch (instr.instruction) {
		case 'PutById':
		case 'DefineOwnById':
		case 'PutNewOwnById': {
			if (ssaRegisterKey(instr.uses.value) !== rootKey) return null;
			if (
				values.get(ssaRegisterKey(instr.uses.object))?.kind ===
					'builder'
			) {
				return null;
			}
			const object = trackedExpressionForRegister(
				instr.uses.object,
				values,
			);
			const { key, computed } = objectLiteralPropertyKey(
				func,
				instr.property,
			);
			const member = t.memberExpression(object, key, computed);
			member.extra = extra;
			const stmt = t.expressionStatement(
				t.assignmentExpression('=', member, root.expr),
			) as LiftedAST<t.ExpressionStatement>;
			stmt.extra = extra;
			return stmt;
		}
		case 'DefineOwnByIndex': {
			if (ssaRegisterKey(instr.uses.value) !== rootKey) return null;
			if (
				values.get(ssaRegisterKey(instr.uses.object))?.kind ===
					'builder'
			) {
				return null;
			}
			const member = t.memberExpression(
				trackedExpressionForRegister(instr.uses.object, values),
				t.valueToNode(instr.property),
				true,
			);
			member.extra = extra;
			const stmt = t.expressionStatement(
				t.assignmentExpression('=', member, root.expr),
			) as LiftedAST<t.ExpressionStatement>;
			stmt.extra = extra;
			return stmt;
		}
		case 'Ret': {
			if (ssaRegisterKey(instr.uses.argument) !== rootKey) return null;
			const stmt = t.returnStatement(root.expr) as LiftedAST<
				t.ReturnStatement
			>;
			stmt.extra = extra;
			return stmt;
		}
		default:
			return null;
	}
}

function hasUseOutsideRange(
	instructions: SSAInstruction[],
	registers: Set<string>,
	startIndex: number,
	endIndex: number,
): boolean {
	for (let i = 0; i < instructions.length; i++) {
		if (i >= startIndex && i <= endIndex) continue;
		if (instructionUsesAny(instructions[i], registers)) return true;
	}
	return false;
}

function hasLiveOutUse(
	func: IRFunction,
	block: SSABasicBlock,
	registerIndexes: Set<number>,
): boolean {
	const liveOut = ssaLivenessAnalysis(func.ssa).blockLiveness.get(
		block.address,
	)?.liveOut;
	if (!liveOut) return false;
	for (const registerIndex of registerIndexes) {
		if (liveOut.has(registerIndex)) return true;
	}
	return false;
}

const ssaUseCountCache = new WeakMap<SSAFunction, Map<string, number>>();

// Exact per-version use counts. SSA versions are unique per register index
// across the whole function, so a count of `n` means exactly `n` reads of that
// definition anywhere — including Phi operands in successor blocks.
function ssaUseCounts(ssa: SSAFunction): Map<string, number> {
	const cached = ssaUseCountCache.get(ssa);
	if (cached) return cached;
	const counts = new Map<string, number>();
	for (const block of ssa.basicBlocks.values()) {
		for (const instr of block.ssaInstructions) {
			for (const register of ssaInstructionUses(instr)) {
				const key = ssaRegisterKey(register);
				counts.set(key, (counts.get(key) ?? 0) + 1);
			}
		}
	}
	ssaUseCountCache.set(ssa, counts);
	return counts;
}

const ssaDefinitionCache = new WeakMap<
	SSAFunction,
	Map<string, SSAInstruction>
>();

/** Defining instruction of every SSA version, across the whole function. */
function ssaDefinitions(ssa: SSAFunction): Map<string, SSAInstruction> {
	const cached = ssaDefinitionCache.get(ssa);
	if (cached) return cached;
	const definitions = new Map<string, SSAInstruction>();
	for (const block of ssa.basicBlocks.values()) {
		for (const instr of block.ssaInstructions) {
			if (instr.instruction === 'Phi') {
				definitions.set(ssaRegisterKey(instr.destination), instr);
				continue;
			}
			for (const value of Object.values(instr.defs)) {
				const register = ssaRegisterFromValue(value);
				if (register) {
					definitions.set(ssaRegisterKey(register), instr);
				}
			}
		}
	}
	ssaDefinitionCache.set(ssa, definitions);
	return definitions;
}

const ssaUseSiteCache = new WeakMap<SSAFunction, Map<string, SSAUseSite[]>>();

/** Where a value is read, with the position needed to order against a rewrite. */
interface SSAUseSite {
	instr: SSAInstruction;
	block: number;
	index: number;
}

function ssaUseSites(ssa: SSAFunction): Map<string, SSAUseSite[]> {
	const cached = ssaUseSiteCache.get(ssa);
	if (cached) return cached;
	const sites = new Map<string, SSAUseSite[]>();
	for (const [address, block] of ssa.basicBlocks) {
		block.ssaInstructions.forEach((instr, index) => {
			for (const register of ssaInstructionUses(instr)) {
				const key = ssaRegisterKey(register);
				const list = sites.get(key) ?? [];
				list.push({ instr, block: address, index });
				sites.set(key, list);
			}
		});
	}
	ssaUseSiteCache.set(ssa, sites);
	return sites;
}

const ssaDefinitionBlockCache = new WeakMap<
	SSAFunction,
	Map<string, number>
>();

/** Which block defines each SSA version. */
function ssaDefinitionBlocks(ssa: SSAFunction): Map<string, number> {
	const cached = ssaDefinitionBlockCache.get(ssa);
	if (cached) return cached;
	const blocks = new Map<string, number>();
	for (const [address, block] of ssa.basicBlocks) {
		for (const instr of block.ssaInstructions) {
			if (instr.instruction === 'Phi') {
				blocks.set(ssaRegisterKey(instr.destination), address);
				continue;
			}
			for (const value of Object.values(instr.defs)) {
				const register = ssaRegisterFromValue(value);
				if (register) blocks.set(ssaRegisterKey(register), address);
			}
		}
	}
	ssaDefinitionBlockCache.set(ssa, blocks);
	return blocks;
}

interface PhiEdgeUse {
	phi: SSAInstruction & { instruction: 'Phi' };
	pred: number;
}

/** Instructions whose result is a Number no matter what the operands are. */
const ALWAYS_NUMBER = new Set([
	'Sub',
	'Mul',
	'Div',
	'Mod',
	'BitAnd',
	'BitOr',
	'BitXor',
	'LShift',
	'RShift',
	'URShift',
	'ToInt32',
	'ToNumber',
	'Negate',
	'GetArgumentsLength',
	// `Add` is absent deliberately: it concatenates strings.
]);

const ssaNumericCache = new WeakMap<
	SSAFunction,
	(register: SSARegister) => boolean
>();

/**
 * Is this register always a Number?
 *
 * Hermes abandons its own inference on a Phi cycle, which is why an `Inc` over
 * a loop counter survives as an opcode instead of being rewritten to an add.
 * An optimistic fixpoint recovers what it gave up on: assume Number, retract
 * on evidence, and a counter seeded by a numeric constant settles as Number
 * however many times it goes round the loop.
 *
 * `Inc`, `Dec` and `ToNumeric` are only a Number when their operand already is
 * one -- on a BigInt they stay a BigInt, which `+ 1` would reject outright.
 */
function ssaNumericRegisters(
	ssa: SSAFunction,
): (register: SSARegister) => boolean {
	const cached = ssaNumericCache.get(ssa);
	if (cached) return cached;
	const definitions = ssaDefinitions(ssa);
	// Only these carry their operand's numeric-ness; everything else either is
	// a Number outright or settles the question on its own.
	const forwarding = new Set(['Mov', 'Inc', 'Dec', 'ToNumeric', 'Phi']);
	// Retraction is monotone, so a worklist over the users of each retracted
	// register settles it in one pass over the graph. Re-deciding every
	// definition per round instead is quadratic, and these are functions with
	// thousands of definitions apiece.
	const numeric = new Map<string, boolean>();
	const pending: string[] = [];
	for (const [key, definition] of definitions) {
		let holds: boolean;
		if (definition.instruction === 'LoadConst') {
			holds = typeof definition.value === 'number';
		} else if (forwarding.has(definition.instruction)) {
			// A register this analysis never saw defined -- a parameter, say --
			// settles the question against us.
			holds = ssaInstructionUses(definition).every((source) =>
				definitions.has(ssaRegisterKey(source))
			);
		} else {
			holds = ALWAYS_NUMBER.has(definition.instruction);
		}
		numeric.set(key, holds);
		if (!holds) pending.push(key);
	}
	const sites = ssaUseSites(ssa);
	for (let cursor = 0; cursor < pending.length; cursor++) {
		for (const site of sites.get(pending[cursor]) ?? []) {
			if (!forwarding.has(site.instr.instruction)) continue;
			const destination = site.instr.instruction === 'Phi'
				? site.instr.destination
				: ssaRegisterFromValue(
					(site.instr.defs as { destination?: unknown }).destination,
				);
			if (!destination) continue;
			const key = ssaRegisterKey(destination);
			if (numeric.get(key) === false) continue;
			numeric.set(key, false);
			pending.push(key);
		}
	}
	const query = (register: SSARegister) =>
		numeric.get(ssaRegisterKey(register)) === true;
	ssaNumericCache.set(ssa, query);
	return query;
}

/**
 * Is this value already in the ECMAScript Numeric domain?
 *
 * Number proof is enough. Independently, `ToNumeric`, `Inc`, and `Dec` always
 * produce either a Number or a BigInt, so another `ToNumeric` is an identity.
 * Follow allocator copies because they do not change that domain.
 */
function ssaValueIsNumeric(
	ssa: SSAFunction,
	register: SSARegister,
): boolean {
	if (ssaNumericRegisters(ssa)(register)) return true;
	const definitions = ssaDefinitions(ssa);
	const seen = new Set<string>();
	let current = register;
	while (true) {
		const key = ssaRegisterKey(current);
		if (seen.has(key)) return false;
		seen.add(key);
		const definition = definitions.get(key);
		if (!definition) return false;
		switch (definition.instruction) {
			case 'ToNumeric':
			case 'Inc':
			case 'Dec':
				return true;
			case 'Mov':
				current = definition.uses.source;
				continue;
			default:
				return false;
		}
	}
}

const ssaPhiSourceCache = new WeakMap<
	SSAFunction,
	Map<string, PhiEdgeUse[]>
>();

/**
 * Which Phi edges read each SSA version.
 *
 * Asked once per update on bundles with six figures of functions, so the
 * alternative -- scanning every Phi of the variable's class per call -- is the
 * difference between a half-hour run and an hour.
 */
function ssaPhiSources(ssa: SSAFunction): Map<string, PhiEdgeUse[]> {
	const cached = ssaPhiSourceCache.get(ssa);
	if (cached) return cached;
	const edges = new Map<string, PhiEdgeUse[]>();
	for (const block of ssa.basicBlocks.values()) {
		for (const instr of block.ssaInstructions) {
			if (instr.instruction !== 'Phi') continue;
			for (const [pred, source] of instr.sources) {
				const key = ssaRegisterKey(source);
				const list = edges.get(key);
				if (list) list.push({ phi: instr, pred });
				else edges.set(key, [{ phi: instr, pred }]);
			}
		}
	}
	ssaPhiSourceCache.set(ssa, edges);
	return edges;
}

interface SSAVariableIndex {
	/** Canonical key of the variable a register version belongs to. */
	classOf: (key: string) => string;
	/** Every register version in a variable, so a scan stays proportional. */
	membersOf: (root: string) => readonly string[];
	/** Blocks whose Phi redefines the variable. */
	phiBlocksOf: (root: string) => ReadonlySet<number>;
}

const ssaVariableClassCache = new WeakMap<SSAFunction, SSAVariableIndex>();

/**
 * Group the SSA versions that denote one source-level variable.
 *
 * The register allocator splits a loop counter across a header Phi and the
 * scratch copies around it, so no single version spans the loop. Union-find
 * over Phi operands and `Mov` copies re-joins them, which is what lets a
 * rewrite ask "is this variable read anywhere else" rather than the much
 * weaker "is this version read anywhere else".
 */
function ssaVariableClasses(ssa: SSAFunction): SSAVariableIndex {
	const cached = ssaVariableClassCache.get(ssa);
	if (cached) return cached;
	const definitions = ssaDefinitions(ssa);
	const parent = new Map<string, string>();
	const find = (key: string): string => {
		let root = key;
		while (true) {
			const next = parent.get(root);
			if (next === undefined || next === root) break;
			root = next;
		}
		let cursor = key;
		while (cursor !== root) {
			const next = parent.get(cursor) ?? root;
			parent.set(cursor, root);
			cursor = next;
		}
		return root;
	};
	const union = (left: string, right: string) => {
		const a = find(left);
		const b = find(right);
		if (a !== b) parent.set(b, a);
	};
	for (const block of ssa.basicBlocks.values()) {
		for (const instr of block.ssaInstructions) {
			if (instr.instruction === 'Phi') {
				const destination = ssaRegisterKey(instr.destination);
				parent.set(destination, parent.get(destination) ?? destination);
				for (const source of instr.sources.values()) {
					const key = ssaRegisterKey(source);
					parent.set(key, parent.get(key) ?? key);
					union(destination, key);
				}
				continue;
			}
			if (instr.instruction === 'Inc' || instr.instruction === 'Dec') {
				// `i++` does not change which variable `i` is. Without this
				// edge the value a join Phi receives looks like a different
				// variable from the one the update read, and only a self-edged
				// loop header -- where the reader and the writer are the same
				// Phi -- can be recognised at all.
				const coerce = definitions.get(
					ssaRegisterKey(instr.uses.argument),
				);
				const read = coerce?.instruction === 'ToNumeric'
					? coerce.uses.argument
					: instr.uses.argument;
				const destination = ssaRegisterKey(instr.defs.destination);
				const source = ssaRegisterKey(read);
				parent.set(destination, parent.get(destination) ?? destination);
				parent.set(source, parent.get(source) ?? source);
				union(destination, source);
				continue;
			}
			if (instr.instruction !== 'Mov') continue;
			const destination = ssaRegisterKey(instr.defs.destination);
			const source = ssaRegisterKey(instr.uses.source);
			parent.set(destination, parent.get(destination) ?? destination);
			parent.set(source, parent.get(source) ?? source);
			union(destination, source);
		}
	}
	// Resolve every member once so callers can walk a variable rather than the
	// whole function; the analysis runs per update on bundles with six figures
	// of functions, so an unbounded scan there is the difference between a
	// half-hour and an hour.
	const members = new Map<string, string[]>();
	for (const key of parent.keys()) {
		const root = find(key);
		const list = members.get(root);
		if (list) list.push(key);
		else members.set(root, [key]);
	}
	const phiBlocks = new Map<string, Set<number>>();
	for (const [address, block] of ssa.basicBlocks) {
		for (const instr of block.ssaInstructions) {
			if (instr.instruction !== 'Phi') continue;
			const root = find(ssaRegisterKey(instr.destination));
			const set = phiBlocks.get(root);
			if (set) set.add(address);
			else phiBlocks.set(root, new Set([address]));
		}
	}
	const index: SSAVariableIndex = {
		classOf: find,
		membersOf: (root) => members.get(root) ?? [root],
		phiBlocksOf: (root) => phiBlocks.get(root) ?? EMPTY_BLOCK_SET,
	};
	ssaVariableClassCache.set(ssa, index);
	return index;
}

const EMPTY_BLOCK_SET: ReadonlySet<number> = new Set();

interface NewExpressionPlan {
	/** Instruction indexes the construction idiom subsumes; they lift to nothing. */
	elided: Set<number>;
	/** `SelectObject` index -> the `new` it becomes. */
	constructions: Map<number, {
		destination: SSARegister;
		constructorRef: SSARegister;
		args: SSARegister[];
	}>;
}

const NO_NEW_EXPRESSIONS: NewExpressionPlan = {
	elided: new Set(),
	constructions: new Map(),
};

// `Construct` receives the receiver in a call-frame slot, so the `CreateThis`
// destination reaches it through one or more `Mov` copies. Returns the indexes
// of those copies, or `null` when the chain is not a private copy of the
// freshly created receiver.
function receiverCopyChain(
	instructions: SSAInstruction[],
	definitionIndex: Map<string, number>,
	useCounts: Map<string, number>,
	receiver: SSARegister,
	receiverKey: string,
	createIndex: number,
	constructIndex: number,
): number[] | null {
	const copies: number[] = [];
	let current = receiver;
	let limit = constructIndex;
	while (ssaRegisterKey(current) !== receiverKey) {
		const key = ssaRegisterKey(current);
		const index = definitionIndex.get(key);
		if (index === undefined || index <= createIndex || index >= limit) {
			return null;
		}
		const copy = instructions[index];
		if (copy.instruction !== 'Mov') return null;
		if (useCounts.get(key) !== 1) return null;
		copies.push(index);
		limit = index;
		current = copy.uses.source;
	}
	return copies;
}

// Hermes lowers `new C(…)` to a fixed, block-local instruction idiom:
//
//     GetById      proto, C, "prototype"
//     CreateThis   this, proto, C
//     Mov          arg0, this
//     Construct    ret, C, [arg0, …]
//     SelectObject value, this, ret
//
// Recognising it here keeps `%CreateThis`/`%Construct`/`%SelectObject` out of
// the IR entirely, instead of emitting them and reconstructing the
// `NewExpression` later from Babel bindings. Shapes that break the idiom —
// `super()` (`CreateThisForSuper` + `Call`), a `new.target` distinct from the
// callee, or a state machine that splits the triple across blocks — do not
// match and stay with the intrinsic-level cleanup.
function planNewExpressions(
	func: IRFunction,
	block: SSABasicBlock,
): NewExpressionPlan {
	const instructions = block.ssaInstructions;
	if (!instructions.some((instr) => instr.instruction === 'SelectObject')) {
		return NO_NEW_EXPRESSIONS;
	}

	const definitionIndex = new Map<string, number>();
	instructions.forEach((instr, index) => {
		if (instr.instruction === 'Phi') {
			definitionIndex.set(ssaRegisterKey(instr.destination), index);
			return;
		}
		for (const value of Object.values(instr.defs)) {
			const register = ssaRegisterFromValue(value);
			if (register) definitionIndex.set(ssaRegisterKey(register), index);
		}
	});

	const useCounts = ssaUseCounts(func.ssa);
	const elided = new Set<number>();
	const constructions: NewExpressionPlan['constructions'] = new Map();

	for (let index = 0; index < instructions.length; index++) {
		const select = instructions[index];
		if (select.instruction !== 'SelectObject') continue;

		// The idiom emits `SelectObject` directly after `Construct`; anything in
		// between means the result was reused, so leave it to later analysis.
		const constructIndex = index - 1;
		const construct = instructions[constructIndex];
		if (!construct || construct.instruction !== 'Construct') continue;
		const returnKey = ssaRegisterKey(construct.defs.destination);
		if (
			returnKey !==
				ssaRegisterKey(select.uses.constructorReturnValue) ||
			useCounts.get(returnKey) !== 1
		) continue;

		const receiverKey = ssaRegisterKey(select.uses.thisObject);
		const createIndex = definitionIndex.get(receiverKey);
		if (createIndex === undefined || createIndex >= constructIndex) {
			continue;
		}
		// The receiver copy feeding `Construct` and this `SelectObject` are the
		// only readers; any third reader would lose its definition.
		if (useCounts.get(receiverKey) !== 2) continue;

		const create = instructions[createIndex];
		let constructorRef: SSARegister;
		let prototypeIndex: number | undefined;
		if (create.instruction === 'CreateThis') {
			constructorRef = create.uses.constructorRef;
			// `new.target === callee` only holds when the prototype operand is
			// the callee's own `.prototype`; `Reflect.construct` and derived
			// constructors pass a foreign one.
			const prototypeKey = ssaRegisterKey(create.uses.prototype);
			prototypeIndex = definitionIndex.get(prototypeKey);
			const prototype = prototypeIndex === undefined
				? undefined
				: instructions[prototypeIndex];
			if (
				!prototype ||
				(prototype.instruction !== 'GetById' &&
					prototype.instruction !== 'TryGetById') ||
				func.file.getIdentifier(
						prototype.property.stringTableIndex,
					) !== 'prototype' ||
				ssaRegisterKey(prototype.uses.object) !==
					ssaRegisterKey(constructorRef)
			) continue;
			// A shared `.prototype` read has other consumers; keep it.
			if (useCounts.get(prototypeKey) !== 1) prototypeIndex = undefined;
		} else if (create.instruction === 'CreateThisForNew') {
			constructorRef = create.uses.closure;
		} else continue;

		if (
			ssaRegisterKey(construct.uses.closure) !==
				ssaRegisterKey(constructorRef)
		) continue;

		const [receiverArgument, ...args] = construct.uses.arguments;
		if (!receiverArgument) continue;
		const copies = receiverCopyChain(
			instructions,
			definitionIndex,
			useCounts,
			receiverArgument,
			receiverKey,
			createIndex,
			constructIndex,
		);
		if (!copies) continue;

		if (prototypeIndex !== undefined) elided.add(prototypeIndex);
		elided.add(createIndex);
		for (const copy of copies) elided.add(copy);
		elided.add(constructIndex);
		constructions.set(index, {
			destination: select.defs.destination,
			constructorRef,
			args,
		});
	}

	if (constructions.size === 0) return NO_NEW_EXPRESSIONS;
	return { elided, constructions };
}

/**
 * Where an update writes.
 *
 * A stored l-reference names a location in the bytecode: the window reloads it
 * and writes it back. A register-carried one names a variable the allocator
 * keeps in a register across a loop-header Phi, so the write back is that Phi's
 * back edge rather than a store instruction.
 */
type UpdateTarget =
	| {
		kind: 'stored';
		load: UpdateTargetLoad;
		/** The location is a property of the global object. */
		onGlobalObject: boolean;
	}
	| {
		kind: 'register';
		register: SSARegister;
		/**
		 * The variable's binding does not hold the value yet: a peeled first
		 * update reads a register the loop's own binding only receives later.
		 */
		initialiseFrom?: SSARegister;
		/**
		 * The target is the update's own destination rather than a variable
		 * the loop shares, so nothing else has declared it.
		 */
		declareTarget?: boolean;
	};

interface UpdateExpressionPlan {
	/** Instruction indexes the update idiom subsumes; they lift to nothing. */
	elided: Set<number>;
	/** `Inc`/`Dec` index -> the `++`/`--` it becomes. */
	updates: Map<number, {
		operator: '++' | '--';
		/** `++x` rather than `x++`: the expression yields the new value. */
		prefix: boolean;
		target: UpdateTarget;
		/** Set when the pre-update value still has a consumer. */
		value: SSARegister | null;
	}>;
}

const NO_UPDATE_EXPRESSIONS: UpdateExpressionPlan = {
	elided: new Set(),
	updates: new Map(),
};

// Hermes lowers a postfix `x++` / `x--` to a read-modify-write window over one
// l-reference. `genUpdateExpr` (ESTreeIRGen-expr.cpp) emits exactly:
//
//     <lref load>          old
//     ToNumeric   value, old
//     Inc | Dec   next, value
//     <lref store> next
//
// and `ToNumeric` has no other emitter in the compiler, so every one of these
// is an update expression whose l-reference we have to name. `value` is the
// pre-update value the expression yields.
//
// The AST-level recogniser needs the store to survive as the immediately
// following sibling statement with a standard l-value on the left. An
// environment slot (`%expectEnvironment(e)[n]`) never satisfies that, a global
// reloads the global object between the two, and CFG structuring sinks and
// duplicates the store past branches. Register provenance settles all of it
// here instead.

/** The load half of an l-reference, and how to prove a store writes it back. */
type UpdateTargetLoad = SSAInstruction & {
	instruction:
		| 'LoadFromEnvironment'
		| 'GetById'
		| 'TryGetById'
		| 'GetByVal';
};

function updateTargetLoad(
	instr: SSAInstruction | undefined,
): UpdateTargetLoad | null {
	if (!instr) return null;
	switch (instr.instruction) {
		case 'LoadFromEnvironment':
		case 'GetById':
		case 'TryGetById':
		case 'GetByVal':
			return instr;
		default:
			return null;
	}
}

// `global` is one object, so two `GetGlobalObject` results denote the same
// receiver even though they are different registers. Hermes reloads it before
// the store of a global update, which is the only way the object registers of
// a matched load/store pair legitimately differ.
function sameReceiver(
	left: SSARegister,
	right: SSARegister,
	definitionOf: (register: SSARegister) => SSAInstruction | undefined,
): boolean {
	if (ssaRegisterKey(left) === ssaRegisterKey(right)) return true;
	return definitionOf(left)?.instruction === 'GetGlobalObject' &&
		definitionOf(right)?.instruction === 'GetGlobalObject';
}

function storeWritesBackTo(
	load: UpdateTargetLoad,
	store: SSAInstruction,
	updatedKey: string,
	definitionOf: (register: SSARegister) => SSAInstruction | undefined,
): boolean {
	if (load.instruction === 'LoadFromEnvironment') {
		if (
			store.instruction !== 'StoreToEnvironment' &&
			store.instruction !== 'StoreNPToEnvironment'
		) return false;
		return store.slotIndex === load.slotIndex &&
			ssaRegisterKey(store.uses.environment) ===
				ssaRegisterKey(load.uses.environment) &&
			ssaRegisterKey(store.uses.value) === updatedKey;
	}
	if (load.instruction === 'GetByVal') {
		if (store.instruction !== 'PutByVal') return false;
		return ssaRegisterKey(store.uses.property) ===
				ssaRegisterKey(load.uses.property) &&
			ssaRegisterKey(store.uses.value) === updatedKey &&
			sameReceiver(store.uses.object, load.uses.object, definitionOf);
	}
	if (store.instruction !== 'PutById' && store.instruction !== 'TryPutById') {
		return false;
	}
	return store.property.stringTableIndex === load.property.stringTableIndex &&
		ssaRegisterKey(store.uses.value) === updatedKey &&
		sameReceiver(store.uses.object, load.uses.object, definitionOf);
}

// Instructions Hermes may schedule between the `Inc`/`Dec` and the store that
// cannot observe the l-reference: reloading the global object, and copying the
// updated value into the store's argument register. Returns the register the
// skipped instruction defines, so the caller can prove the store is its only
// consumer before eliding it.
function skippableBeforeStore(
	instr: SSAInstruction,
	updatedKey: string,
): { destination: SSARegister; isCopy: boolean } | null {
	if (instr.instruction === 'GetGlobalObject') {
		return { destination: instr.defs.destination, isCopy: false };
	}
	if (
		instr.instruction === 'Mov' &&
		ssaRegisterKey(instr.uses.source) === updatedKey
	) return { destination: instr.defs.destination, isCopy: true };
	return null;
}

/**
 * The register this value is copied into, if a single `Mov` is its only reader.
 *
 * Retargeting a Phi operand leaves the copy on the way dead, which is only
 * sound when nothing else was reading it.
 */
function copiedInto(
	key: string,
	useCounts: Map<string, number>,
	ssa: SSAFunction,
): SSARegister | null {
	if (useCounts.get(key) !== 1) return null;
	const [site] = ssaUseSites(ssa).get(key) ?? [];
	if (site?.instr.instruction !== 'Mov') return null;
	return site.instr.defs.destination;
}

/**
 * Recognise an update whose write back is a Phi edge rather than a store.
 *
 * A loop counter never leaves its register, so `genUpdateExpr`'s store half is
 * the register allocator's copy into the loop-header Phi. Naming that as the
 * l-reference is sound when two things hold:
 *
 *  - the read and the write are the same source-level variable, which Phi and
 *    `Mov` union-find establishes across the version split the allocator makes;
 *  - nothing reads that variable at a point reachable from the update without
 *    first passing through the Phi that redefines it, so rewriting the read
 *    into an in-place update cannot be observed. A protected block is declined
 *    outright: the catch Phi captures the register state at the throw, and the
 *    bytecode's state there still holds the pre-update value.
 *
 * The caller retargets the Phi operand at the returned edge to the Phi's own
 * destination: the update already wrote it, so the edge needs no copy.
 */
function phiCarriedUpdateTarget(
	func: IRFunction,
	blockAddress: number,
	index: number,
	operand: SSARegister,
	updated: SSARegister,
	own: ReadonlySet<SSAInstruction>,
): {
	phi: SSAInstruction & { instruction: 'Phi' };
	edge: number;
	register: SSARegister;
	/** Materialise the variable from this register before updating it. */
	initialiseFrom?: SSARegister;
} | null {
	// A handler entered from this block reads the register state at the throw,
	// where the bytecode has not yet copied the update into the variable.
	if (
		exceptionHandlersByAddress(blockAddress, func.ssa.exceptionHandlers)
			.length > 0
	) return null;
	const definitions = ssaDefinitions(func.ssa);
	const variables = ssaVariableClasses(func.ssa);
	const useCounts = ssaUseCounts(func.ssa);
	// The register allocator copies the loop variable into a scratch register
	// before coercing it, so the operand names the Phi only through a chain of
	// `Mov`s. Walking it proves the operand holds the Phi's current value,
	// which mere membership of the variable class would not.
	let carrier = operand;
	let phi: (SSAInstruction & { instruction: 'Phi' }) | null = null;
	for (;;) {
		const definition = definitions.get(ssaRegisterKey(carrier));
		if (definition?.instruction === 'Phi') {
			phi = definition;
			break;
		}
		if (definition?.instruction !== 'Mov') break;
		carrier = definition.uses.source;
	}
	// `var n = arguments.length; while (n--)` peels its first update above the
	// loop, where the binding the later iterations share does not exist yet.
	// There is no Phi to anchor to, so the variable is named by the Phi that
	// receives the result while the operand keeps its own register: other
	// readers of it still see the value it always held, and the scan below
	// rejects exactly the ones that would have observed the update.
	const variable = variables.classOf(
		ssaRegisterKey(phi ? phi.destination : operand),
	);
	if (variables.classOf(ssaRegisterKey(updated)) !== variable) return null;

	// The edge whose copy the run subsumes. It need not belong to the Phi the
	// operand came from: a loop header reads and writes through one self-edged
	// Phi, but at a join the value is read from the Phi that dominates the
	// block and written into the Phi at the join. Both are the same variable.
	//
	// Walk the result forward through the allocator's copies to the Phi edges
	// that read it. A copy on the way is only skippable if its reader is the
	// one found here; a second reader would still expect the value the fused
	// update no longer produces.
	const phiSources = ssaPhiSources(func.ssa);
	let writeBack: PhiEdgeUse | null = null;
	let cursor: SSARegister | null = updated;
	while (cursor) {
		const key = ssaRegisterKey(cursor);
		for (const candidate of phiSources.get(key) ?? []) {
			if (
				variables.classOf(
					ssaRegisterKey(candidate.phi.destination),
				) !== variable
			) continue;
			// Two edges carrying the run's result would each need the value,
			// and only one can be dropped.
			if (writeBack) return null;
			writeBack = candidate;
		}
		if (writeBack) break;
		cursor = copiedInto(key, useCounts, func.ssa);
	}
	if (!writeBack) return null;

	// A Phi that redefines the variable ends its live range: a read below one
	// sees the new binding either way, so it is no evidence. That holds only
	// for reads of what the Phi defines -- a read in the same block of a
	// register the Phi does not supersede still sees the register this rewrite
	// mutated, so those blocks are recorded rather than dismissed.
	const barriers = variables.phiBlocksOf(variable);
	const reachable = new Set<number>();
	const frontier = new Set<number>();
	const queue: number[] = [];
	const advance = (from: number) => {
		for (
			const successor of func.ssa.basicBlocks.get(from)
				?.consequentAddresses ?? []
		) {
			if (barriers.has(successor)) {
				frontier.add(successor);
				continue;
			}
			if (reachable.has(successor)) continue;
			reachable.add(successor);
			queue.push(successor);
		}
	};
	advance(blockAddress);
	for (let cursor = 0; cursor < queue.length; cursor++) {
		advance(queue[cursor]);
	}

	const sitesByRegister = ssaUseSites(func.ssa);
	const definitionBlocks = ssaDefinitionBlocks(func.ssa);
	for (const key of variables.membersOf(variable)) {
		const sites = sitesByRegister.get(key) ?? [];
		for (const site of sites) {
			// The run's own reads, the Phi operand being retargeted, and the
			// copies between the run's result and that operand.
			if (site.instr === writeBack.phi || own.has(site.instr)) continue;
			if (site.block === blockAddress) {
				if (site.index <= index) continue;
				return null;
			}
			if (reachable.has(site.block)) return null;
			// In a barrier block only what its Phi defines is safe to read;
			// anything carried in from before still holds the mutated value.
			if (
				frontier.has(site.block) &&
				definitionBlocks.get(key) !== site.block
			) return null;
		}
	}
	// The run wrote the register the operand names, so that is what the edge
	// must carry and what the update expression targets.
	// A peeled window has no Phi of its own, so the variable is named by the
	// Phi that receives it and the value has to be moved there first.
	return {
		phi: writeBack.phi,
		edge: writeBack.pred,
		register: phi ? phi.destination : writeBack.phi.destination,
		initialiseFrom: phi ? undefined : operand,
	};
}
/**
 * Does anything the scheduler placed between the coercion and the update read
 * or write the variable being updated?
 *
 * The rewrite moves the write to where the read was, so only an access to the
 * same variable can tell the difference. Version equality is too weak -- the
 * allocator splits a loop counter across a Phi and its copies -- so this asks
 * the variable class.
 */
function gapTouchesLReference(
	instructions: readonly SSAInstruction[],
	start: number,
	end: number,
	operand: SSARegister,
	variables: SSAVariableIndex,
	ignored?: ReadonlySet<number>,
): boolean {
	const classOf = variables.classOf;
	const variable = classOf(ssaRegisterKey(operand));
	for (let j = start; j < end; j++) {
		if (ignored?.has(j)) continue;
		const instr = instructions[j];
		for (const register of ssaInstructionUses(instr)) {
			if (classOf(ssaRegisterKey(register)) === variable) return true;
		}
		if (instr.instruction === 'Phi') continue;
		for (const value of Object.values(instr.defs)) {
			const register = ssaRegisterFromValue(value);
			if (
				register && classOf(ssaRegisterKey(register)) === variable
			) return true;
		}
	}
	return false;
}

type UpdateCoercionInput = {
	coerced: Extract<SSAInstruction, { instruction: 'ToNumeric' }> | null;
	coerceIndex: number;
	emitIndex: number;
	resultRegister: SSARegister;
	elidedInstructions: number[];
};

function planUpdateExpressions(
	func: IRFunction,
	block: SSABasicBlock,
): UpdateExpressionPlan {
	const instructions = block.ssaInstructions;
	if (
		!instructions.some((instr) =>
			instr.instruction === 'Inc' || instr.instruction === 'Dec'
		)
	) return NO_UPDATE_EXPRESSIONS;

	const useCounts = ssaUseCounts(func.ssa);
	const definitions = ssaDefinitions(func.ssa);
	const definitionOf = (register: SSARegister) =>
		definitions.get(ssaRegisterKey(register));
	const elided = new Set<number>();
	const updates: UpdateExpressionPlan['updates'] = new Map();
	// `indexOf` over a block per update is quadratic on the large blocks a
	// minified bundle produces; the position is asked for several times per
	// window, so index it once.
	const positionOf = new Map<SSAInstruction, number>();
	instructions.forEach((instr, at) => positionOf.set(instr, at));
	const classOf = ssaVariableClasses(func.ssa);
	const coercionCache = new Map<number, UpdateCoercionInput | undefined>();
	const coercionBeforeUpdate = (
		update: Extract<SSAInstruction, { instruction: 'Inc' | 'Dec' }>,
		index: number,
	): UpdateCoercionInput | undefined => {
		if (coercionCache.has(index)) return coercionCache.get(index);
		let argument = update.uses.argument;
		const copies: Array<{
			instruction: Extract<SSAInstruction, { instruction: 'Mov' }>;
			index: number;
		}> = [];
		while (true) {
			const definition = definitionOf(argument);
			if (definition?.instruction === 'Mov') {
				const copyIndex = positionOf.get(definition) ?? -1;
				if (copyIndex < 0 || copyIndex >= index) {
					coercionCache.set(index, undefined);
					return undefined;
				}
				copies.push({ instruction: definition, index: copyIndex });
				argument = definition.uses.source;
				continue;
			}
			if (definition?.instruction !== 'ToNumeric') {
				const result = {
					coerced: null,
					coerceIndex: -1,
					emitIndex: index,
					resultRegister: update.uses.argument,
					elidedInstructions: [],
				};
				coercionCache.set(index, result);
				return result;
			}
			const coerceIndex = positionOf.get(definition) ?? -1;
			if (coerceIndex < 0 || coerceIndex >= index) {
				coercionCache.set(index, undefined);
				return undefined;
			}
			// A copy with another consumer is the name of the postfix value,
			// not disposable allocator traffic. Emit the update in that copy's
			// slot and keep its destination; all private copies around it can
			// still disappear. More than one public copy would require two
			// result bindings and is not one update expression.
			const publicCopies = copies.filter(({ instruction }) =>
				useCounts.get(
					ssaRegisterKey(instruction.defs.destination),
				) !== 1
			);
			if (publicCopies.length > 1) {
				coercionCache.set(index, undefined);
				return undefined;
			}
			const publicCopy = publicCopies[0];
			if (publicCopy) {
				if (publicCopy.index <= coerceIndex) {
					coercionCache.set(index, undefined);
					return undefined;
				}
				const copyIndexes = new Set(copies.map(({ index }) => index));
				for (let j = coerceIndex + 1; j < publicCopy.index; j++) {
					if (!copyIndexes.has(j)) {
						coercionCache.set(index, undefined);
						return undefined;
					}
				}
			}
			const result = {
				coerced: definition,
				coerceIndex,
				emitIndex: publicCopy?.index ?? coerceIndex,
				resultRegister: publicCopy?.instruction.defs.destination ??
					definition.defs.destination,
				elidedInstructions: [
					...copies
						.filter((copy) => copy !== publicCopy)
						.map(({ index }) => index),
					...(publicCopy ? [coerceIndex] : []),
				],
			};
			coercionCache.set(index, result);
			return result;
		}
	};

	// `p[i++] | p[i++]` updates one variable twice in a row: the second
	// window's read is the first window's result, so neither reaches a store
	// or a Phi edge on its own. Link them, plan the run from its head, and let
	// the tail's result name the write-back for all of them.
	const chainSuccessor = new Map<number, number>();
	const chained = new Set<number>();
	for (let index = 0; index < instructions.length; index++) {
		const instr = instructions[index];
		if (instr.instruction !== 'Inc' && instr.instruction !== 'Dec') {
			continue;
		}
		const input = coercionBeforeUpdate(instr, index);
		if (!input) continue;
		const read = input.coerced?.uses.argument ?? instr.uses.argument;
		const previous = definitionOf(read);
		if (
			previous?.instruction !== 'Inc' && previous?.instruction !== 'Dec'
		) continue;
		const previousIndex = positionOf.get(previous) ?? -1;
		// Only a forward run inside one block is a straight-line sequence; a
		// link that points backwards would make the run's last index not its
		// last instruction, and the store walk would start behind itself.
		if (previousIndex < 0 || previousIndex >= index) continue;
		// A result consumed twice is not a chain: the other reader would see a
		// value the fused update no longer produces.
		if (useCounts.get(ssaRegisterKey(previous.defs.destination)) !== 1) {
			continue;
		}
		chainSuccessor.set(previousIndex, index);
		chained.add(index);
	}

	// A register-carried update needs no load in front of it, so the `Inc`/
	// `Dec` can open the block.
	for (let index = 0; index < instructions.length; index++) {
		const update = instructions[index];
		if (
			update.instruction !== 'Inc' && update.instruction !== 'Dec'
		) continue;
		// The head of a run owns the whole run.
		if (chained.has(index)) continue;
		const run = [index];
		for (
			let next = chainSuccessor.get(index);
			next !== undefined;
			next = chainSuccessor.get(next)
		) run.push(next);
		const tailIndex = run[run.length - 1];
		const tail = instructions[tailIndex];
		if (tail.instruction !== 'Inc' && tail.instruction !== 'Dec') continue;

		// A `ToNumeric` coerces the pre-update value, which Hermes only needs
		// for a postfix update whose operand it could not type as numeric.
		// Without one, the operand feeds `Inc`/`Dec` directly.
		//
		// It is usually the immediately preceding instruction, but the
		// scheduler hoists consumers of the coerced value above the update --
		// `a[i++]` emits the `GetByVal` between the two. Locate it by
		// definition rather than by position, and let `gapTouchesLReference`
		// decide whether the window can close over what sits in between.
		const input = coercionBeforeUpdate(update, index);
		if (!input) continue;
		const coerced = input.coerced;
		const coerceIndex = input.coerceIndex;
		const loadIndex = coerced ? coerceIndex - 1 : index - 1;
		const oldRegister = coerced
			? coerced.uses.argument
			: update.uses.argument;
		const oldKey = ssaRegisterKey(oldRegister);
		// The run's last result is what a store or a Phi edge writes back.
		const updatedRegister = tail.defs.destination;

		// The load must sit directly in front, so nothing can observe the
		// location between the read and the write the update fuses.
		const load = loadIndex >= 0
			? updateTargetLoad(instructions[loadIndex])
			: null;
		// With a coercion the loaded value is consumed by it alone; without
		// one the loaded value may also be the postfix result.
		const storedTarget = load != null &&
				ssaRegisterKey(load.defs.destination) === oldKey &&
				!(coerced && useCounts.get(oldKey) !== 1)
			? load
			: null;

		let updatedKey = ssaRegisterKey(updatedRegister);
		const skipped: number[] = [];
		let storeIndex = -1;
		if (storedTarget) {
			// Walk forward to the store, allowing only the reloads and copies
			// the store itself needs. Every register defined on the way is
			// consumed by the store, so eliding them with it strands nothing.
			for (let j = tailIndex + 1; j < instructions.length; j++) {
				const candidate = instructions[j];
				if (
					storeWritesBackTo(
						storedTarget,
						candidate,
						updatedKey,
						definitionOf,
					)
				) {
					storeIndex = j;
					break;
				}
				const skippable = skippableBeforeStore(candidate, updatedKey);
				if (!skippable) break;
				const definedKey = ssaRegisterKey(skippable.destination);
				if (useCounts.get(definedKey) !== 1) break;
				if (skippable.isCopy) updatedKey = definedKey;
				skipped.push(j);
			}
		}

		// Each window is emitted at its coercion result, so the write moves
		// ahead of whatever the scheduler put before the update. That is
		// unobservable only for a register l-reference nothing in the gap
		// touches; a store could be reloaded or aliased by any of it, so it
		// keeps the original adjacency requirement. A load with no store is
		// not an l-reference at all -- `var n = a.length` reads a property into
		// a local -- so there is nothing there to move.
		const members: Array<{
			/** The gap would be observable if the variable were rewritten. */
			gapTouches: boolean;
			index: number;
			coerced:
				| Extract<SSAInstruction, { instruction: 'ToNumeric' }>
				| null;
			/** Allocator instructions subsumed by this window. */
			elidedInstructions: number[];
			emitIndex: number;
			operator: '++' | '--';
			/** The register the coercion read, before it was coerced. */
			read: SSARegister;
			resultRegister: SSARegister;
			updatedRegister: SSARegister;
		}> = [];
		let runIsPlannable = true;
		for (const memberIndex of run) {
			const member = instructions[memberIndex];
			if (
				member.instruction !== 'Inc' && member.instruction !== 'Dec'
			) {
				runIsPlannable = false;
				break;
			}
			const memberInput = coercionBeforeUpdate(member, memberIndex);
			if (!memberInput) {
				runIsPlannable = false;
				break;
			}
			const memberCoerced = memberInput.coerced;
			const memberRead = memberCoerced
				? memberCoerced.uses.argument
				: member.uses.argument;
			const gapStart = memberCoerced
				? memberInput.emitIndex + 1
				: memberIndex;
			// Whether the gap matters depends on what the write-back turns
			// out to be, which is not known yet: an in-place rewrite must not
			// move the write across a read of the variable, but an update on
			// its own destination touches no variable at all. Record it and
			// decide below.
			const privateCopies = new Set(memberInput.elidedInstructions);
			let gapTouches = false;
			if (gapStart < memberIndex) {
				if (storeIndex >= 0) {
					for (let j = gapStart; j < memberIndex; j++) {
						if (!privateCopies.has(j)) {
							gapTouches = true;
							break;
						}
					}
				} else {
					gapTouches = gapTouchesLReference(
						instructions,
						gapStart,
						memberIndex,
						memberRead,
						classOf,
						privateCopies,
					);
				}
			}
			members.push({
				gapTouches,
				elidedInstructions: memberInput.elidedInstructions,
				index: memberIndex,
				coerced: memberCoerced,
				emitIndex: memberCoerced ? memberInput.emitIndex : memberIndex,
				operator: member.instruction === 'Inc' ? '++' : '--',
				read: memberRead,
				resultRegister: memberCoerced
					? memberInput.resultRegister
					: memberRead,
				updatedRegister: member.defs.destination,
			});
		}
		if (!runIsPlannable) continue;
		// Two windows reading one coercion would claim the same slot, and the
		// second would silently replace the first while both `Inc`s stay
		// elided -- an update dropped with nothing left to write the register.
		const slots = new Set(members.map(({ emitIndex }) => emitIndex));
		if (
			slots.size !== members.length ||
			members.some(({ emitIndex }) => updates.has(emitIndex))
		) continue;

		// No store closes the window: the write back may still be a Phi edge.
		// The run's own coercions and updates read the variable by
		// construction, so they are not evidence that anything observes it.
		const own = new Set<SSAInstruction>();
		for (const member of members) {
			own.add(instructions[member.index]);
			if (member.coerced) own.add(member.coerced);
			for (const skipped of member.elidedInstructions) {
				own.add(instructions[skipped]);
			}
		}
		const carried = storeIndex < 0
			? phiCarriedUpdateTarget(
				func,
				block.address,
				coerced ? coerceIndex : index,
				oldRegister,
				updatedRegister,
				own,
			)
			: null;
		// Nothing names the variable, so the update cannot be written in
		// place. The pair is still expressible without an intrinsic: the
		// coercion is what `x--` performs, so run it on an SSA destination and
		// let the coercion's register take the old value it yields.
		//
		// A run must share one destination. Its tail register can be declared
		// at the head, mutated by every member, and then retain the final value
		// for its ordinary consumers. Separate destinations would snapshot the
		// value before an earlier update and sever the dependency.
		const ownDestination = storeIndex < 0 && !carried;
		// Every member of a destination-only run needs the coercion register
		// that receives its postfix result. Otherwise eliding its update would
		// strand a value with no equivalent binding.
		if (ownDestination && members.some(({ coerced }) => coerced == null)) {
			continue;
		}
		if (!ownDestination && members.some(({ gapTouches }) => gapTouches)) {
			continue;
		}

		// Which value each window yields decides prefix from postfix. One use
		// of each register is structural — the coercion or the update reads
		// the old value, the store or the next window reads the new one — so
		// anything beyond that is the consumer of that window's result.
		const plans = members.map((member) => {
			const resultKey = ssaRegisterKey(member.resultRegister);
			const updatedIsTail = member.index === tailIndex;
			const oldIsRead = (useCounts.get(resultKey) ?? 0) > 1;
			const newIsRead = updatedIsTail
				? (useCounts.get(updatedKey) ?? 0) > 1
				: false;
			return { member, oldIsRead, newIsRead };
		});
		// Both halves live means neither `x++` nor `++x` reproduces it -- but
		// on its own destination the update holds the new value and the
		// coercion holds the old, so both survive. A carried update writes the
		// register the expression reads, so without the coercion the
		// pre-update value has no register of its own to survive in and naming
		// it would emit `r = r++`.
		if (
			!ownDestination &&
			plans.some(({ member, oldIsRead, newIsRead }) =>
				(oldIsRead && newIsRead) ||
				(carried && oldIsRead && !member.coerced)
			)
		) continue;

		const sharedTarget: UpdateTarget | null = ownDestination ? null : (
			carried
				? {
					kind: 'register',
					register: carried.register,
					initialiseFrom: carried.initialiseFrom,
				}
				: {
					kind: 'stored',
					load: storedTarget!,
					onGlobalObject:
						storedTarget!.instruction !== 'LoadFromEnvironment' &&
						definitionOf(storedTarget!.uses.object)?.instruction ===
							'GetGlobalObject',
				}
		);
		if (carried) {
			// The run writes the Phi's destination in place, so the back edge
			// already carries the value its last window left there.
			carried.phi.sources.set(carried.edge, carried.register);
		} else if (!ownDestination) {
			elided.add(loadIndex);
			for (const skip of skipped) elided.add(skip);
			elided.add(storeIndex);
		}
		for (const { member, oldIsRead, newIsRead } of plans) {
			// Each window yields its value where the coercion result was
			// materialized, and the `Inc`/`Dec` lifts to nothing.
			if (member.coerced) elided.add(member.index);
			// The update subsumes allocator copies on its operand/result path.
			for (const skipped of member.elidedInstructions) {
				elided.add(skipped);
			}
			// On its own destination the expression always yields the old
			// value, which is what the coercion's result register held.
			const prefix = ownDestination ? false : !oldIsRead && newIsRead;
			updates.set(member.emitIndex, {
				operator: member.operator,
				prefix,
				target: ownDestination
					? {
						kind: 'register',
						register: updatedRegister,
						initialiseFrom: member.index === index
							? oldRegister
							: undefined,
						declareTarget: member.index === index,
					}
					: sharedTarget!,
				value: prefix
					? (newIsRead ? member.updatedRegister : null)
					: (oldIsRead ? member.resultRegister : null),
			});
		}
	}

	if (updates.size === 0) return NO_UPDATE_EXPRESSIONS;
	return { elided, updates };
}

function liftExtraForSSAInstruction(
	func: IRFunction,
	instr: SSAInstruction,
): LiftedExtra {
	const extra: LiftedExtra = {
		parentFunctionId: func.id,
		address: 'functionLocalOffset' in instr ? instr.functionLocalOffset : 0,
	};
	if (instr.instruction !== 'Phi') extra.instruction = instr.instruction;
	return extra;
}

function tryLiftLargeSingleUseConstructionSlice(
	func: IRFunction,
	block: SSABasicBlock,
	startIndex: number,
	objectShapeKeysByRegister: Map<string, SerializedLiteralValue[]>,
): { endIndex: number; statement: LiftedAST<t.Statement> } | null {
	const instructions = block.ssaInstructions;
	const start = instructions[startIndex];
	const startExtra = liftExtraForSSAInstruction(func, start);
	const root = newLiteralBuilder(
		func,
		start,
		startExtra,
		objectShapeKeysByRegister,
	);
	if (!root) return null;

	const builders = new Map<string, LiteralBuilder>();
	const values = new Map<string, TrackedLiteralValue>();
	const definedRegisters = new Set<string>();
	const definedRegisterIndexes = new Set<number>();
	const rootKey = ssaRegisterKey(root.register);
	builders.set(rootKey, root);
	values.set(rootKey, { kind: 'builder', builder: root });
	definedRegisters.add(rootKey);
	definedRegisterIndexes.add(root.register.index);

	for (let i = startIndex + 1; i < instructions.length; i++) {
		const instr = instructions[i];
		const extra = liftExtraForSSAInstruction(func, instr);

		const terminal = terminalStatementWithLiteral(
			func,
			instr,
			root,
			values,
			extra,
		);
		if (terminal) {
			if (i - startIndex < LARGE_CONSTRUCTION_SLICE_MIN_INSTRUCTIONS) {
				return null;
			}
			for (const builder of builders.values()) {
				if (builder.embeddedUses > 1) {
					debugLiteralSlice(func, 'reject shared builder', {
						startIndex,
						endIndex: i,
						span: i - startIndex,
						root: rootKey,
						builders: builders.size,
						values: values.size,
					});
					return null;
				}
			}
			if (
				hasLiveOutUse(func, block, definedRegisterIndexes) ||
				hasUseOutsideRange(
					instructions,
					definedRegisters,
					startIndex,
					i,
				)
			) {
				debugLiteralSlice(func, 'reject outside use', {
					startIndex,
					endIndex: i,
					span: i - startIndex,
					root: rootKey,
					builders: builders.size,
					values: values.size,
				});
				return null;
			}
			debugLiteralSlice(func, 'accept', {
				startIndex,
				endIndex: i,
				span: i - startIndex,
				root: rootKey,
				builders: builders.size,
				values: values.size,
			});
			return { endIndex: i, statement: terminal };
		}

		if (
			recordLiteralWrite(
				func,
				instr,
				builders,
				values,
				objectShapeKeysByRegister,
			)
		) {
			continue;
		}

		const builder = newLiteralBuilder(
			func,
			instr,
			extra,
			objectShapeKeysByRegister,
		);
		if (builder) {
			const key = ssaRegisterKey(builder.register);
			builders.set(key, builder);
			values.set(key, { kind: 'builder', builder });
			definedRegisters.add(key);
			definedRegisterIndexes.add(builder.register.index);
			continue;
		}

		if (instr.instruction === 'LoadConst') {
			const destination = instr.defs.destination;
			const expr = loadConstValueNode(func, instr.value);
			expr.extra = { ...extra, isNonVolatile: true };
			const key = ssaRegisterKey(destination);
			values.set(key, { kind: 'expr', expr });
			definedRegisters.add(key);
			definedRegisterIndexes.add(destination.index);
			continue;
		}

		if (instr.instruction === 'LoadParam') {
			const destination = instr.defs.destination;
			const expr = loadParamValueNode(func, instr);
			expr.extra = { ...expr.extra, ...extra };
			const key = ssaRegisterKey(destination);
			values.set(key, { kind: 'expr', expr });
			definedRegisters.add(key);
			definedRegisterIndexes.add(destination.index);
			continue;
		}

		if (instr.instruction === 'Mov') {
			const source = instr.uses.source;
			const tracked = values.get(ssaRegisterKey(source));
			if (tracked) {
				const destination = instr.defs.destination;
				const key = ssaRegisterKey(destination);
				values.set(key, tracked);
				if (tracked.kind === 'builder') {
					builders.set(key, tracked.builder);
				}
				definedRegisters.add(key);
				definedRegisterIndexes.add(destination.index);
				continue;
			}
		}

		if (instructionUsesAny(instr, definedRegisters)) {
			debugLiteralSlice(func, 'reject unsupported use', {
				startIndex,
				endIndex: i,
				span: i - startIndex,
				root: rootKey,
				instruction: instr.instruction,
				builders: builders.size,
				values: values.size,
			});
			return null;
		}
		debugLiteralSlice(func, 'reject unsupported instruction', {
			startIndex,
			endIndex: i,
			span: i - startIndex,
			root: rootKey,
			instruction: instr.instruction,
			builders: builders.size,
			values: values.size,
		});
		return null;
	}

	return null;
}

export function liftSSABlocktoIR(
	func: IRFunction,
	block: SSABasicBlock,
): IRBlock {
	const body: LiftedAST<t.Statement>[] = [];

	// Hoisted to the function so buffer shape keys survive across (split) blocks; a slot
	// access in a later block can then resolve the original property name.
	const objectShapeKeysByRegister = func.objectShapeKeysByRegister;
	const newExpressions = planNewExpressions(func, block);
	const updateExpressions = planUpdateExpressions(func, block);

	let branchStmt: t.Statement | undefined = undefined;
	for (let i = 0; i < block.ssaInstructions.length; i++) {
		const instr = block.ssaInstructions[i];
		if (instr.instruction == 'Phi') {
			body.push(
				asAssigningIntrinsic(
					instr.instruction,
					instr.destination,
					[...instr.sources.values()].map((r) =>
						registerAsIdentifier(r)
					),
				),
			);
			continue;
		}
		if (newExpressions.elided.has(i) || updateExpressions.elided.has(i)) {
			continue;
		}
		const largeConstructionSlice = tryLiftLargeSingleUseConstructionSlice(
			func,
			block,
			i,
			objectShapeKeysByRegister,
		);
		if (largeConstructionSlice) {
			body.push(largeConstructionSlice.statement);
			i = largeConstructionSlice.endIndex;
			continue;
		}

		const extra: LiftedExtra = {
			parentFunctionId: func.id,
			address: instr.functionLocalOffset,
			instruction: instr.instruction,
		};
		const construction = newExpressions.constructions.get(i);
		if (construction) {
			body.push(assignRegister(
				construction.destination,
				t.newExpression(
					registerAsIdentifier(construction.constructorRef),
					construction.args.map((arg) => registerAsIdentifier(arg)),
				),
				extra,
				{ ...extra },
			));
			continue;
		}
		const update = updateExpressions.updates.get(i);
		if (update) {
			let target: t.Expression;
			if (update.target.kind === 'register') {
				target = registerAsIdentifier(update.target.register);
				// A peeled update names a binding the loop only fills in
				// later, so move the value it read into it first. An update on
				// its own destination has no such binding: the register is
				// declared here and the coercion is what `--` performs.
				if (update.target.initialiseFrom) {
					if (update.target.declareTarget) {
						body.push(
							declareLet(
								update.target.register,
								registerAsIdentifier(
									update.target.initialiseFrom,
								),
								extra,
							),
						);
					} else {
						const move = t.expressionStatement(
							t.assignmentExpression(
								'=',
								t.cloneNode(target, true),
								registerAsIdentifier(
									update.target.initialiseFrom,
								),
							),
						);
						move.extra = { ...extra };
						body.push(move);
					}
				}
			} else {
				// The location node keeps the load's provenance; environment
				// resolution and storage tagging both read it.
				const load = update.target.load;
				const targetExtra = liftExtraForSSAInstruction(func, load);
				target = load.instruction === 'LoadFromEnvironment'
					? environmentSlotMember(load, targetExtra)
					: load.instruction === 'GetByVal'
					? t.memberExpression(
						registerAsIdentifier(load.uses.object),
						registerAsIdentifier(load.uses.property),
						true,
					)
					: memberById(func, load, targetExtra);
				// `global.x++` only unqualifies back to `x++` when composition
				// has seen the name referenced; the intrinsic-level global fold
				// this window consumed is what used to register it.
				if (
					update.target.onGlobalObject && t.isMemberExpression(target)
				) {
					const property = target.property;
					if (t.isIdentifier(property)) {
						property.extra = {
							...property.extra,
							isReferencedGlobal: true,
						};
					}
				}
			}
			const expression = t.updateExpression(
				update.operator,
				target,
				update.prefix,
			);
			expression.extra = { ...extra };
			if (update.value) {
				body.push(
					declareConst(
						registerAsIdentifier(update.value),
						expression,
						extra,
					),
				);
			} else {
				const stmt = t.expressionStatement(expression);
				stmt.extra = extra;
				body.push(stmt);
			}
			continue;
		}
		switch (instr.instruction) {
			case 'GetGlobalObject': {
				body.push(assignRegister(
					instr.defs.destination,
					t.identifier('global'),
					extra,
					{ ...extra, isNonVolatile: true },
				));
				break;
			}
			case 'DeclareGlobalVar': {
				const id = func.fromIdentifierRef(instr.identifier);
				if (!t.isIdentifier(id)) {
					throw Error();
				}
				const decl = t.variableDeclarator(id);
				decl.extra = { ...extra, isDeclaredGlobal: true };
				const decn = t.variableDeclaration('var', [decl]);
				decn.extra = extra;

				body.push(decn);
				break;
			}
			case 'GetById': {
				body.push(
					assignRegister(
						instr.defs.destination,
						memberById(func, instr, {
							...extra,
							memberReadDestination: instr.defs.destination,
						}),
						extra,
					),
				);
				break;
			}
			case 'GetByIdWithReceiver': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.callExpression(
							t.memberExpression(
								t.identifier('Reflect'),
								t.identifier('get'),
							),
							[
								registerAsIdentifier(instr.uses.object),
								t.valueToNode(
									func.file.getIdentifier(
										instr.property.stringTableIndex,
									),
								),
								registerAsIdentifier(instr.uses.receiver),
							],
						),
						extra,
					),
				);
				break;
			}
			case 'GetBySlotIdx': {
				body.push(
					assignRegister(
						instr.defs.destination,
						objectShapeSlotMember(
							func,
							instr.uses.object,
							instr.slotIndex,
							objectShapeKeysByRegister,
							extra,
						),
						extra,
					),
				);
				break;
			}
			case 'GetByVal': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.memberExpression(
							registerAsIdentifier(instr.uses.object),
							registerAsIdentifier(instr.uses.property),
							true,
						),
						extra,
					),
				);
				break;
			}
			case 'GetByIndex': {
				const property = t.numericLiteral(instr.index);
				property.extra = {
					memberReadDestination: instr.defs.destination,
				};
				body.push(
					assignRegister(
						instr.defs.destination,
						t.memberExpression(
							registerAsIdentifier(instr.uses.object),
							property,
							true,
						),
						extra,
					),
				);
				break;
			}
			case 'TryGetById': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.object),
							t.valueToNode(
								func.file.getIdentifier(
									instr.property.stringTableIndex,
								),
							),
						],
						extra,
					),
				);
				break;
			}

			case 'TryPutById':
			case 'PutById':
			case 'DefineOwnById':
			case 'PutNewOwnById': {
				const assign = t.expressionStatement(
					t.assignmentExpression(
						'=',
						memberById(func, instr),
						registerAsIdentifier(instr.uses.value),
					),
				);
				assign.extra = extra;

				body.push(assign);
				break;
			}
			case 'PutOwnBySlotIdx': {
				const assign = t.expressionStatement(
					t.assignmentExpression(
						'=',
						objectShapeSlotMember(
							func,
							instr.uses.object,
							instr.slotIndex,
							objectShapeKeysByRegister,
							extra,
						),
						registerAsIdentifier(instr.uses.value),
					),
				);
				assign.extra = extra;

				body.push(assign);
				break;
			}

			case 'DefineOwnByIndex': {
				const assign = t.expressionStatement(
					t.assignmentExpression(
						'=',
						t.memberExpression(
							registerAsIdentifier(instr.uses.object),
							t.valueToNode(instr.property),
							true,
						),
						registerAsIdentifier(instr.uses.value),
					),
				);
				assign.extra = extra;

				body.push(assign);
				break;
			}

			case 'DefineOwnInDenseArray': {
				const assign = t.expressionStatement(
					t.assignmentExpression(
						'=',
						t.memberExpression(
							registerAsIdentifier(instr.uses.object),
							t.valueToNode(instr.index),
							true,
						),
						registerAsIdentifier(instr.uses.value),
					),
				);
				assign.extra = extra;

				body.push(assign);
				break;
			}

			case 'PutByVal':
			case 'DefineOwnByVal': {
				const assign = t.expressionStatement(
					t.assignmentExpression(
						'=',
						t.memberExpression(
							registerAsIdentifier(instr.uses.object),
							registerAsIdentifier(instr.uses.property),
							true,
						),
						registerAsIdentifier(instr.uses.value),
					),
				);
				assign.extra = extra;

				body.push(assign);
				break;
			}

			case 'DefineOwnGetterSetterByVal': {
				const options = t.objectExpression([
					t.objectProperty(
						t.identifier('get'),
						registerAsIdentifier(instr.uses.getter),
					),
					t.objectProperty(
						t.identifier('set'),
						registerAsIdentifier(instr.uses.setter),
					),
				]);

				if (instr.enumerable) {
					options.properties.push(t.objectProperty(
						t.identifier('enumerable'),
						t.booleanLiteral(true),
					));
				}

				body.push(t.expressionStatement(t.callExpression(
					t.memberExpression(
						t.identifier('Object'),
						t.identifier('defineProperty'),
					),
					[
						registerAsIdentifier(instr.uses.object),
						registerAsIdentifier(instr.uses.property),
						options,
					],
				)));
				break;
			}

			case 'DelById': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.unaryExpression('delete', memberById(func, instr)),
						extra,
					),
				);
				break;
			}
			case 'DelByVal': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.unaryExpression(
							'delete',
							t.memberExpression(
								registerAsIdentifier(instr.uses.object),
								registerAsIdentifier(instr.uses.property),
								true,
							),
						),
						extra,
					),
				);
				break;
			}

			case 'CreateTopLevelEnvironment':
			case 'CreateFunctionEnvironment': {
				const args = [];
				if (typeof instr.envSize !== 'undefined') {
					args.push(t.numericLiteral(instr.envSize));
				}
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						args,
						extra,
					),
				);
				break;
			}

			case 'CreateEnvironment': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.parent),
							t.numericLiteral(instr.envSize),
						],
						extra,
					),
				);
				break;
			}

			case 'GetParentEnvironment': {
				extra.isNonVolatile = true;
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[t.valueToNode(instr.levelIndex)],
						extra,
					),
				);
				break;
			}

			case 'GetEnvironment': {
				extra.isNonVolatile = true;
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.parentEnv),
							t.valueToNode(instr.levelIndex),
						],
						extra,
					),
				);
				break;
			}

			case 'GetClosureEnvironment': {
				extra.isNonVolatile = true;
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.closure),
						],
						extra,
					),
				);
				break;
			}

			case 'GetBuiltinClosure': {
				extra.isBuiltin = true;
				body.push(
					assignRegister(
						instr.defs.destination,
						func.getBuiltin(instr.builtinNo),
						extra,
						{ ...extra, isNonVolatile: true },
					),
				);
				break;
			}

			case 'CreateThis': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.prototype),
							registerAsIdentifier(instr.uses.constructorRef),
						],
						extra,
					),
				);
				break;
			}
			case 'CreateThisForNew': {
				body.push(
					asAssigningIntrinsic(
						'CreateThisForNew',
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.closure),
						],
						extra,
					),
				);
				break;
			}
			case 'CreateThisForSuper': {
				body.push(
					asAssigningIntrinsic(
						'CreateThisForSuper',
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.closure),
							registerAsIdentifier(instr.uses.newTarget),
						],
						extra,
					),
				);
				break;
			}
			case 'CacheNewObject': {
				// noop this
				break;
			}
			case 'SelectObject': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.thisObject),
							registerAsIdentifier(
								instr.uses.constructorReturnValue,
							),
						],
						extra,
					),
				);
				break;
			}

			case 'LoadThisNS': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.thisExpression(),
						extra,
					),
				);
				break;
			}

			case 'CoerceThisNS': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.argument),
						],
						extra,
					),
				);
				break;
			}

			case 'CreateClosure':
			case 'CreateGeneratorClosure':
			case 'CreateAsyncClosure': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							getFunctionRef(instr.function),
							registerAsIdentifier(instr.uses.environment),
						],
						extra,
					),
				);
				break;
			}
			case 'CreateBaseClass': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.classOut,
						[
							getFunctionRef(instr.function),
							registerAsIdentifier(instr.uses.environment),
						],
						{ ...extra },
					),
				);
				if ('homeObject' in instr.defs) {
					body.push(
						assignRegister(
							instr.defs.homeObject,
							t.memberExpression(
								registerAsIdentifier(instr.defs.classOut),
								t.identifier('prototype'),
								false,
							),
							{ ...extra, isHomeObject: true },
						),
					);
				}
				break;
			}
			case 'CreateDerivedClass': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.classOut,
						[
							getFunctionRef(instr.function),
							registerAsIdentifier(instr.uses.environment),
							registerAsIdentifier(instr.uses.superClass),
						],
						{ ...extra },
					),
				);
				if ('homeObject' in instr.defs) {
					body.push(
						assignRegister(
							instr.defs.homeObject,
							t.memberExpression(
								registerAsIdentifier(instr.defs.classOut),
								t.identifier('prototype'),
								false,
							),
							{ ...extra, isHomeObject: true },
						),
					);
				}
				break;
			}

			case 'Mov': {
				body.push(
					assignRegister(
						instr.defs.destination,
						registerAsIdentifier(instr.uses.source),
						extra,
					),
				);
				break;
			}

			case 'LoadConst': {
				body.push(assignRegister(
					instr.defs.destination,
					loadConstValueNode(func, instr.value),
					extra,
					{ ...extra, isNonVolatile: true },
				));

				break;
			}

			case 'NewArray': {
				const value = instr.size > 0
					? t.newExpression(
						t.identifier('Array'),
						[t.valueToNode(instr.size)],
					)
					: t.arrayExpression([]);
				body.push(assignRegister(instr.defs.destination, value, extra));
				break;
			}

			case 'NewArrayWithBuffer': {
				const elements = func.file.getArrayBufferElements(
					instr.arrayBufferIndex,
					instr.noOfStaticElements,
				);
				body.push(
					assignRegister(
						instr.defs.destination,
						t.arrayExpression(
							elements.map((e) =>
								serializedLiteralToNode(func, e)
							),
						),
						extra,
					),
				);
				break;
			}

			case 'NewObjectWithBuffer': {
				const { keys, values } = func.file.getObjectBufferElements(
					instr,
				);
				if (typeof instr.shapeTableIndex !== 'undefined') {
					objectShapeKeysByRegister.set(
						`${instr.defs.destination.index}_${instr.defs.destination.version}`,
						keys,
					);
				}
				body.push(
					assignRegister(
						instr.defs.destination,
						t.objectExpression(
							keys.map((key, i) => {
								let propertyKey = serializedLiteralToNode(
									func,
									key,
								);
								let computed = undefined;
								if (
									t.isStringLiteral(propertyKey) &&
									t.isValidIdentifier(
										propertyKey.value,
										false,
									)
								) {
									propertyKey = t.identifier(
										propertyKey.value,
									);
									computed = false;
								}

								return t.objectProperty(
									propertyKey,
									serializedLiteralToNode(func, values[i]),
									computed,
								);
							}),
						),
						extra,
						{
							...extra,
							objectShapeKeys:
								typeof instr.shapeTableIndex !== 'undefined'
									? keys
									: undefined,
						},
					),
				);
				break;
			}

			case 'NewObjectWithBufferAndParent': {
				const { keys, values } = func.file.getObjectBufferElements(
					instr,
				);
				objectShapeKeysByRegister.set(
					`${instr.defs.destination.index}_${instr.defs.destination.version}`,
					keys,
				);
				const objectLiteral = t.objectExpression(
					keys.map((key, i) =>
						t.objectProperty(
							serializedLiteralToNode(func, key),
							serializedLiteralToNode(func, values[i]),
						)
					),
				);
				body.push(
					assignRegister(
						instr.defs.destination,
						t.callExpression(
							t.memberExpression(
								t.identifier('Object'),
								t.identifier('assign'),
							),
							[
								t.callExpression(
									t.memberExpression(
										t.identifier('Object'),
										t.identifier('create'),
									),
									[registerAsIdentifier(instr.uses.parent)],
								),
								objectLiteral,
							],
						),
						extra,
						{
							...extra,
							objectShapeKeys: keys,
						},
					),
				);
				break;
			}

			case 'NewObject': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.objectExpression([]),
						extra,
						extra,
					),
				);
				break;
			}

			case 'NewObjectWithParent': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.callExpression(
							t.memberExpression(
								t.identifier('Object'),
								t.identifier('create'),
							),
							[registerAsIdentifier(instr.uses.parent)],
						),
						extra,
					),
				);
				break;
			}

			case 'CreateRegExp': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.regExpLiteral(
							func.file.getString(instr.pattern.stringTableIndex),
							func.file.getString(instr.flags.stringTableIndex),
						),
						extra,
					),
				);
				break;
			}

			case 'LoadFromEnvironment': {
				body.push(
					declareConst(
						registerAsIdentifier(instr.defs.destination),
						environmentSlotMember(instr, extra),
						extra,
					),
				);
				break;
			}

			case 'StoreNPToEnvironment':
			case 'StoreToEnvironment': {
				const stmt = t.expressionStatement(
					t.assignmentExpression(
						'=',
						environmentSlotMember(instr, extra),
						registerAsIdentifier(instr.uses.value),
					),
				);
				stmt.extra = extra;
				body.push(stmt);
				break;
			}

			case 'Call': {
				body.push(assignRegister(
					instr.defs.destination,
					t.callExpression(
						t.memberExpression(
							registerAsIdentifier(instr.uses.closure),
							t.identifier('call'),
						),
						instr.uses.arguments.map((a) =>
							registerAsIdentifier(a)
						),
					),
					extra,
					{ ...extra },
				));
				break;
			}

			case 'Construct': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.closure),
							...instr.uses.arguments.map((a) =>
								registerAsIdentifier(a)
							),
						],
						extra,
					),
				);
				break;
			}

			case 'CallDirect': {
				body.push(assignRegister(
					instr.defs.destination,
					t.callExpression(
						t.v8IntrinsicIdentifier('CallDirect'),
						[
							t.numericLiteral(instr.function.functionId),
							...instr.uses.arguments.map((a) =>
								registerAsIdentifier(a)
							),
						],
					),
					extra,
				));
				break;
			}

			case 'CallBuiltin': {
				body.push(assignRegister(
					instr.defs.destination,
					t.callExpression(
						func.getBuiltin(instr.builtinNo),
						instr.uses.arguments.map((a) =>
							registerAsIdentifier(a)
						),
					),
					extra,
					{ ...extra },
				));
				break;
			}

			case 'CreateGenerator': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.environment),
							getFunctionRef(instr.function),
						],
						extra,
					),
				);
				break;
			}

			case 'LoadParam': {
				// An index past `paramCount` has no name to be spelled with, so
				// it is read out of `arguments`. Tagging it keeps it in the
				// parameter domain: a name test sees only a member expression
				// on `arguments` and reports an unknown value.
				const param = instr.parameterIndex >= func.paramCount
					? tagStorageLocation(
						t.memberExpression(
							tagStorageLocation(t.identifier('arguments'), {
								kind: 'arguments-object',
								owner: { functionId: func.id },
							}),
							t.valueToNode(instr.parameterIndex - 1),
							true,
						),
						{
							kind: 'parameter',
							owner: { functionId: func.id },
							parameter: {
								index: instr.parameterIndex,
								form: 'overflow',
							},
						},
					)
					: func.getParam(instr.parameterIndex);
				body.push(assignRegister(instr.defs.destination, param, extra));
				break;
			}

			case 'Ret': {
				const stmt = t.returnStatement(
					registerAsIdentifier(instr.uses.argument),
				);
				stmt.extra = extra;

				body.push(stmt);
				break;
			}

			case 'Not': {
				body.push(
					assignRegister(
						instr.defs.destination!,
						t.unaryExpression(
							'!',
							registerAsIdentifier(instr.uses.argument),
							true,
						),
						extra,
					),
				);
				break;
			}

			case 'Negate': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.unaryExpression(
							'-',
							registerAsIdentifier(instr.uses.argument),
							true,
						),
						extra,
					),
				);
				break;
			}

			case 'Add':
			case 'AddS': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'+',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'Sub': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'-',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'Mul': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'*',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'Div': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'/',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'Mod': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'%',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'Inc':
			case 'Dec': {
				// `Inc` coerces its operand, so `arg + 1` only reproduces it
				// when the operand is already a Number -- otherwise `'3' + 1`
				// concatenates where the instruction would have counted. An
				// update expression on a copy is the faithful form, and needs
				// no intrinsic to say so.
				const operator = instr.instruction === 'Inc' ? '+' : '-';
				if (!ssaNumericRegisters(func.ssa)(instr.uses.argument)) {
					body.push(
						declareLet(
							instr.defs.destination,
							registerAsIdentifier(instr.uses.argument),
							extra,
						),
					);
					const step = t.expressionStatement(
						t.updateExpression(
							operator === '+' ? '++' : '--',
							registerAsIdentifier(instr.defs.destination),
							false,
						),
					);
					step.extra = { ...extra };
					body.push(step);
					break;
				}
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							operator,
							registerAsIdentifier(instr.uses.argument),
							t.numericLiteral(1),
						),
						extra,
					),
				);
				break;
			}

			case 'BitAnd': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'&',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'BitNot': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.unaryExpression(
							'~',
							registerAsIdentifier(instr.uses.argument),
						),
						extra,
					),
				);
				break;
			}

			case 'BitOr': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'|',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'BitXor': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'^',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'LShift': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'<<',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'RShift': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'>>',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}
			case 'URShift': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'>>>',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'Eq': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'==',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'StrictEq': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'===',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'Neq': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'!=',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'StrictNeq': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'!==',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'Less': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'<',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'LessEq': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'<=',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'Greater': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'>',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'GreaterEq': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'>=',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'TypeOf': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.unaryExpression(
							'typeof',
							registerAsIdentifier(instr.uses.argument),
						),
						extra,
					),
				);
				break;
			}

			case 'TypeOfIs': {
				body.push(
					assignRegister(
						instr.defs.destination,
						typeOfIsExpression(
							registerAsIdentifier(instr.uses.value),
							instr.typeIndex,
						),
						extra,
					),
				);
				break;
			}

			case 'AddEmptyString': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'+',
							registerAsIdentifier(instr.uses.argument),
							t.stringLiteral(''),
						),
						extra,
					),
				);
				break;
			}

			case 'ToInt32': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'|',
							registerAsIdentifier(instr.uses.argument),
							t.numericLiteral(0),
						),
						extra,
					),
				);
				break;
			}

			case 'ToUint32': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'>>>',
							registerAsIdentifier(instr.uses.argument),
							t.numericLiteral(0),
						),
						extra,
					),
				);
				break;
			}

			case 'ToPropertyKey': {
				extra.isNonVolatile = true;
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[registerAsIdentifier(instr.uses.argument)],
						extra,
					),
				);
				break;
			}

			case 'ToNumber': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'-',
							registerAsIdentifier(instr.uses.argument),
							t.numericLiteral(0),
						),
						extra,
					),
				);
				break;
			}

			case 'LoadParentNoTraps': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.callExpression(
							t.memberExpression(
								t.identifier('Object'),
								t.identifier('getPrototypeOf'),
							),
							[registerAsIdentifier(instr.uses.argument)],
						),
						extra,
					),
				);
				break;
			}

			case 'Jmp':
				break;

			case 'JmpBuiltinIs':
			case 'JmpBuiltinIsNot':
			case 'JmpTypeOfIs':
			case 'JmpFalse':
			case 'JmpTrue':
			case 'JmpUndefined': {
				if (branchStmt != null) {
					throw new LiftError('Non-terminating jmp');
				}

				let predicate: t.Expression;
				if (instr.instruction == 'JmpTypeOfIs') {
					predicate = typeOfIsExpression(
						registerAsIdentifier(instr.uses.value),
						instr.typeIndex,
					);
				} else {
					predicate = registerAsIdentifier(instr.uses.predicate);
				}

				if (instr.instruction == 'JmpFalse') {
					predicate = t.unaryExpression('!', predicate, true);
				} else if (instr.instruction == 'JmpUndefined') {
					predicate = t.binaryExpression(
						'===',
						predicate,
						t.identifier('undefined'),
					);
				} else if (
					instr.instruction == 'JmpBuiltinIs' ||
					instr.instruction == 'JmpBuiltinIsNot'
				) {
					const builtin = func.getBuiltin(instr.builtinNo);
					predicate = t.binaryExpression(
						instr.instruction == 'JmpBuiltinIs' ? '===' : '!==',
						predicate,
						builtin,
					);
				}

				body.push(
					branchStmt = t.expressionStatement(t.callExpression(
						t.v8IntrinsicIdentifier('jmpIf'),
						[
							predicate,
							t.valueToNode(block.consequentAddresses[1]),
						],
					)),
				);
				branchStmt.extra = predicate.extra = extra;
				break;
			}

			case 'JLess':
			case 'JNotLess':
			case 'JLessEqual':
			case 'JNotLessEqual':
			case 'JGreater':
			case 'JNotGreater':
			case 'JGreaterEqual':
			case 'JNotGreaterEqual':
			case 'JEqual':
			case 'JNotEqual':
			case 'JStrictEqual':
			case 'JStrictNotEqual': {
				if (branchStmt != null) {
					throw new LiftError('Non-terminating jmp');
				}

				let predicate: t.Expression = t.binaryExpression(
					({
						'JLess': '<',
						'JNotLess': '<',
						'JLessEqual': '<=',
						'JNotLessEqual': '<=',
						'JGreater': '>',
						'JNotGreater': '>',
						'JGreaterEqual': '>=',
						'JNotGreaterEqual': '>=',
						'JEqual': '==',
						'JNotEqual': '==',
						'JStrictEqual': '===',
						'JStrictNotEqual': '===',
					} as const)[instr.instruction],
					registerAsIdentifier(instr.uses.left),
					registerAsIdentifier(instr.uses.right),
				);

				if (
					[
						'JNotEqual',
						'JStrictNotEqual',
					].includes(instr.instruction)
				) {
					predicate = t.unaryExpression('!', predicate, true);
				}

				body.push(
					branchStmt = t.expressionStatement(t.callExpression(
						t.v8IntrinsicIdentifier('jmpIf'),
						[
							predicate,
							t.valueToNode(block.consequentAddresses[1]),
						],
					)),
				);
				break;
			}

			case 'UIntSwitchImm': {
				if (branchStmt != null) {
					throw new LiftError('Non-terminating switch');
				}
				const stmt = t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('UIntSwitchImm'),
					[
						registerAsIdentifier(instr.uses.discriminant),
						t.valueToNode(instr.minValue),
						t.valueToNode(instr.maxValue),
					],
				));
				stmt.extra = extra;
				body.push(stmt);
				break;
			}

			case 'StringSwitchImm': {
				if (branchStmt != null) {
					throw new LiftError('Non-terminating switch');
				}
				const stmt = t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier('StringSwitchImm'),
					[
						registerAsIdentifier(instr.uses.discriminant),
						t.arrayExpression(
							instr.stringTableIndices.map((stringTableIndex) =>
								t.stringLiteral(
									func.file.getString(stringTableIndex),
								)
							),
						),
					],
				));
				stmt.extra = extra;
				body.push(stmt);
				break;
			}

			case 'SaveGenerator': {
				const source = func.yieldingBlocks.get(block.address);
				if (!source) throw new Error();
				assert(block.ssaInstructions[++i].instruction == 'Ret');

				const endInfo = func.yieldEndBlocks.get(
					block.consequentAddresses[0],
				);
				if (!endInfo) {
					body.push(
						t.expressionStatement(
							t.yieldExpression(registerAsIdentifier(source)),
						),
					);
					break;
				}

				const { destination, spills, initializers } = endInfo;
				body.push(
					assignRegister(
						destination,
						t.yieldExpression(registerAsIdentifier(source)),
						extra,
					),
				);
				for (const [dst, src] of spills) {
					body.push(
						assignRegister(dst, registerAsIdentifier(src), extra),
					);
				}
				for (const initializer of initializers) {
					const initializerExtra: LiftedExtra = {
						parentFunctionId: func.id,
						address: initializer.address,
						instruction: 'LoadConst',
					};
					body.push(assignRegister(
						initializer.destination,
						loadConstValueNode(func, initializer.value),
						initializerExtra,
						{ ...initializerExtra, isNonVolatile: true },
					));
				}
				break;
			}

			case 'ReifyArguments': {
				body.push(
					assignRegister(
						instr.defs.lazyLoad,
						t.identifier('arguments'),
						extra,
					),
				);
				break;
			}

			case 'GetArgumentsLength': {
				const argumentsLength = t.memberExpression(
					t.identifier('arguments'),
					t.identifier('length'),
				);
				body.push(
					assignRegister(
						instr.defs.destination,
						argumentsLength,
						extra,
						extra,
					),
				);
				break;
			}

			case 'GetArgumentsPropByVal': {
				const argument = t.memberExpression(
					t.identifier('arguments'),
					registerAsIdentifier(instr.uses.argumentsIndex),
					true,
				);
				body.push(
					assignRegister(
						instr.defs.destination,
						argument,
						extra,
						extra,
					),
				);
				break;
			}

			case 'GetNewTarget': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.metaProperty(
							t.identifier('new'),
							t.identifier('target'),
						),
						extra,
					),
				);
				break;
			}

			case 'ToNumeric': {
				const argument = registerAsIdentifier(instr.uses.argument);
				body.push(
					ssaValueIsNumeric(func.ssa, instr.uses.argument)
						? assignRegister(
							instr.defs.destination,
							argument,
							extra,
						)
						: asAssigningIntrinsic(
							instr.instruction,
							instr.defs.destination,
							[argument],
							extra,
						),
				);
				break;
			}

			case 'InstanceOf': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'instanceof',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'IsIn': {
				body.push(
					assignRegister(
						instr.defs.destination,
						t.binaryExpression(
							'in',
							registerAsIdentifier(instr.uses.left),
							registerAsIdentifier(instr.uses.right),
						),
						extra,
					),
				);
				break;
			}

			case 'Throw': {
				// exception binding to be handled later
				const throwStmt = t.throwStatement(
					registerAsIdentifier(instr.uses.exception),
				);
				throwStmt.extra = extra;
				body.push(throwStmt);
				break;
			}

			case 'DirectEval': {
				// `DirectEval` is only ever emitted for a source `eval(text)`
				// call (`ESTreeIRGen::genCallEvalExpr`), so that is what it
				// decompiles to. The spelling is also what it does: the
				// instruction evaluates its text with a null `Environment` and
				// the global as `this` — hermesc warns "Direct call to eval(),
				// but lexical scope is not supported" — which is exactly the
				// `globalThis.eval` builtin, and global property reads already
				// render as bare identifiers.
				//
				// `strictCaller` is the enclosing function's own strictness,
				// recoverable from the function it lands in, and it is what a
				// source `eval(text)` compiles back to from that function. It
				// stays out of the output rather than becoming an intrinsic no
				// consumer can evaluate.
				body.push(assignRegister(
					instr.defs.destination,
					t.callExpression(t.identifier('eval'), [
						registerAsIdentifier(instr.uses.code),
					]),
					extra,
					{ ...extra },
				));
				break;
			}

			case 'ThrowIfUndefined': {
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[
							registerAsIdentifier(instr.uses.source),
						],
						extra,
					),
				);
				break;
			}

			case 'ThrowIfThisInitialized': {
				const stmt = t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier(instr.instruction),
					[registerAsIdentifier(instr.uses.thisObject)],
				));
				stmt.extra = extra;
				body.push(stmt);
				break;
			}

			case 'Catch':
				// exception binding to be handled later
				body.push(
					asAssigningIntrinsic(
						instr.instruction,
						instr.defs.destination,
						[],
						extra,
					),
				);
				break;

			case 'GetPNameList': {
				body.push(asMultiAssigningIntrinsic(
					instr.instruction,
					[
						instr.defs.destination,
						instr.defs.index,
						instr.defs.propertyListSize,
					],
					[registerAsIdentifier(instr.uses.object)],
					extra,
				));
				break;
			}

			case 'GetNextPName': {
				body.push(asMultiAssigningIntrinsic(instr.instruction, [
					instr.defs.destination,
					instr.defs.index,
				], [
					registerAsIdentifier(instr.uses.object),
					registerAsIdentifier(instr.uses.index),
					registerAsIdentifier(instr.uses.propertyListSize),
				], extra));
				break;
			}

			case 'IteratorBegin': {
				body.push(asMultiAssigningIntrinsic(
					instr.instruction,
					[
						instr.defs.destination,
						instr.defs.source,
					],
					[registerAsIdentifier(instr.uses.source)],
					extra,
				));
				break;
			}

			case 'IteratorNext': {
				body.push(asMultiAssigningIntrinsic(instr.instruction, [
					instr.defs.destination,
					instr.defs.iterator,
				], [
					registerAsIdentifier(instr.uses.iterator),
					registerAsIdentifier(instr.uses.sourceOrNext),
				], extra));
				break;
			}

			case 'IteratorClose': {
				const stmt = t.expressionStatement(t.callExpression(
					t.v8IntrinsicIdentifier(instr.instruction),
					[
						registerAsIdentifier(instr.uses.iterator),
						t.booleanLiteral(instr.ignoreException !== 0),
					],
				));
				stmt.extra = extra;
				body.push(stmt);
				break;
			}

			case 'Debugger': {
				const stmt = t.debuggerStatement();
				stmt.extra = extra;
				body.push(stmt);
				break;
			}

			case 'DebuggerCheckBreak':
			case 'AsyncBreakCheck':
			case 'Unreachable':
				break;

			case 'StartGenerator':
			case 'CompleteGenerator':
				break;

			default:
				console.log(
					generate(
						t.blockStatement(
							body as t.Statement[],
						),
					).code,
				);
				throw new Error(instr.instruction + ' ' + block.address);
		}
	}

	if (branchStmt) assert(body[body.length - 1] == branchStmt);

	let branch: t.Expression | undefined;
	if (branchStmt != null) {
		assert(body.pop() == branchStmt);
		t.assertCallExpression(branchStmt.expression);
		t.assertV8IntrinsicIdentifier(branchStmt.expression.callee, {
			name: 'jmpIf',
		});
		assert(branchStmt.expression.arguments.length === 2);

		t.assertExpression(branchStmt.expression.arguments[0]);
		branch = branchStmt.expression.arguments[0];
	}

	// A register number/version is only unique inside its function. Stamp the
	// owner after lifting the block so every definition and use receives the
	// same identity without threading `func.id` through every instruction case.
	for (const root of [...body, ...(branch ? [branch] : [])]) {
		t.traverseFast(root as t.Node, (node) => {
			if (!t.isIdentifier(node)) return;
			const lifted = node as LiftedAST<t.Identifier>;
			if (!lifted.extra?.sourceRegister) return;
			lifted.extra = {
				...lifted.extra,
				bindingOwnerFunctionId: func.id,
			};
		});
	}

	return {
		address: block.address,

		body,
		branch,
		consequentAddresses: block.consequentAddresses,
	};
}
