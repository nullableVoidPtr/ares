import * as t from '@babel/types';
import type { BlockAddr } from '../../../hbc/disassembly/function.ts';
import {
	getIRInstruction,
	type IRBlock,
	type LiftedAST,
} from '../../ast/mod.ts';
import { comparableAst } from '../../ast/utils.ts';
import type { IRFunction } from '../mod.ts';

/**
 * Hermes compiles every `eval(...)` call site — any call whose callee is the
 * *identifier* `eval`, bound or not — into a fixed diamond
 * (`ESTreeIRGen::genCallEvalExpr`):
 *
 *     callee = eval; evaluate every argument
 *     if (callee === %GetBuiltinClosure(globalThis.eval))
 *         dst1 = DirectEval(args[0] ?? undefined, isStrictMode)
 *     else
 *         dst2 = Call(callee, undefined, args...)
 *     dst  = Phi(dst1, dst2)
 *
 * Only the call arm carries the source: `DirectEval` receives `args[0]` alone
 * (a synthetic `undefined` for `eval()`), while the call arm keeps the original
 * callee expression and the full argument list. Both arms are also
 * observationally equal — `DirectEval` evaluates its text with a null
 * `Environment` and the global as `this`, which is exactly what the
 * `globalThis.eval` builtin does — so the guard decides nothing.
 *
 * Collapsing the diamond onto the call arm recovers the source call and the
 * arguments the eval arm dropped. It has to run before CFG reduction: a
 * structured guard inlines the eval arm's rematerialized constants and the
 * call arm's receiver register, which is the provenance this match needs, and
 * it sinks argument side effects the bytecode evaluates unconditionally into
 * one arm of a ternary.
 */
type Declarator = {
	statement: LiftedAST<t.VariableDeclaration>;
	name: string;
	init: t.Expression;
};

type Diamond = {
	guardAddress: BlockAddr;
	guard: IRBlock;
	evalArmAddress: BlockAddr;
	callArmAddress: BlockAddr;
	callArm: IRBlock;
	joinAddress: BlockAddr;
	join: IRBlock;
	/** `DirectEval` destination register name. */
	evalRegister: string;
	/** `Call` destination register name. */
	callRegister: string;
	/** The lifted `callee.call(thisArg, …)` declaration, last in `callArm`. */
	callDeclarator: Declarator;
};

function asDeclarator(
	statement: LiftedAST<t.Statement> | undefined,
): Declarator | null {
	const declaration = <t.Statement | undefined> statement;
	if (!t.isVariableDeclaration(declaration)) return null;
	if (declaration.declarations.length !== 1) return null;
	const [declarator] = declaration.declarations;
	if (!t.isIdentifier(declarator.id) || !declarator.init) return null;
	return {
		statement: statement as LiftedAST<t.VariableDeclaration>,
		name: declarator.id.name,
		init: declarator.init,
	};
}

/**
 * Every register definition in the function, by name.
 *
 * The guard's operands are not necessarily defined in the guard: the builtin
 * closure fetch and the `undefined` receiver are hoisted out of loops and
 * shared between neighbouring eval sites. SSA names are unique, so a name
 * identifies one definition wherever it lives.
 */
function declarationsByRegister(func: IRFunction): Map<string, Declarator> {
	const declarations = new Map<string, Declarator>();
	for (const block of func.blocks.values()) {
		for (const statement of block.body) {
			const declarator = asDeclarator(statement);
			if (declarator) declarations.set(declarator.name, declarator);
		}
	}
	return declarations;
}

/** A `LoadConst`/`Mov` declaration: droppable with the arm that holds it. */
function isRematerialization(statement: LiftedAST<t.Statement>): boolean {
	const instruction = getIRInstruction(statement);
	if (instruction !== 'LoadConst' && instruction !== 'Mov') return false;
	return asDeclarator(statement) != null;
}

function isLoadedUndefined(declarator: Declarator | undefined): boolean {
	if (!declarator) return false;
	return getIRInstruction(declarator.statement) === 'LoadConst' &&
		t.isIdentifier(declarator.init, { name: 'undefined' });
}

/**
 * Whether two registers hold the same value. Register allocation routinely
 * rematerializes the eval text per arm, so identity is not enough; anything
 * beyond a duplicated constant is refused.
 */
function sameValue(
	declarations: ReadonlyMap<string, Declarator>,
	left: string,
	right: string,
): boolean {
	if (left === right) return true;
	const leftDeclarator = declarations.get(left);
	const rightDeclarator = declarations.get(right);
	if (!leftDeclarator || !rightDeclarator) return false;
	if (
		getIRInstruction(leftDeclarator.statement) !== 'LoadConst' ||
		getIRInstruction(rightDeclarator.statement) !== 'LoadConst'
	) return false;
	return JSON.stringify(comparableAst(leftDeclarator.init)) ===
		JSON.stringify(comparableAst(rightDeclarator.init));
}

function countReferences(
	func: IRFunction,
	names: ReadonlySet<string>,
	excluded: ReadonlySet<BlockAddr>,
): number {
	let count = 0;
	for (const [address, block] of func.blocks) {
		if (excluded.has(address)) continue;
		const roots = <(t.Node | undefined)[]> [...block.body, block.branch];
		for (const node of roots) {
			if (!node) continue;
			t.traverseFast(node, (child: t.Node) => {
				if (t.isIdentifier(child) && names.has(child.name)) count++;
			});
		}
	}
	return count;
}

/** The leading `const dst = %Phi(dst1, dst2)` merging both arms, if live. */
function joinPhi(
	join: IRBlock,
	evalRegister: string,
	callRegister: string,
): Declarator | null {
	const declarator = asDeclarator(join.body[0]);
	if (!declarator || !t.isCallExpression(declarator.init)) return null;
	if (!t.isV8IntrinsicIdentifier(declarator.init.callee, { name: 'Phi' })) {
		return null;
	}
	const operands = declarator.init.arguments;
	const names = operands.filter((operand) => t.isIdentifier(operand))
		.map((operand) => operand.name);
	if (operands.length !== 2 || names.length !== 2) return null;
	return names.includes(evalRegister) && names.includes(callRegister)
		? declarator
		: null;
}

/**
 * An arm this pass may absorb into the guard: reached only by the guard, under
 * the same handlers, and not load-bearing for generator or handler structure.
 */
function isOrdinaryArm(
	func: IRFunction,
	address: BlockAddr,
	block: IRBlock,
	guardAddress: BlockAddr,
): boolean {
	if (block.branch || block.consequentAddresses.length !== 1) return false;
	if (block.kind != null && block.kind !== 'normal') return false;
	if (block.handlerFor && block.handlerFor.size > 0) return false;
	if (
		func.returnBlocks.has(address) || func.yieldingBlocks.has(address) ||
		func.yieldEndBlocks.has(address) || func.yieldRetBlocks.has(address)
	) return false;
	if (func.exceptions.isCatchTarget(address)) return false;
	if (!func.exceptions.activeHandlersEqual(guardAddress, address)) {
		return false;
	}
	const predecessors = func.predecessorsOf(address);
	return predecessors.size === 1 && predecessors.has(guardAddress);
}

function matchDiamond(
	func: IRFunction,
	guardAddress: BlockAddr,
	guard: IRBlock,
	declarations: () => ReadonlyMap<string, Declarator>,
): Diamond | null {
	if (!guard.branch || guard.consequentAddresses.length !== 2) return null;
	const branch = <t.Expression> guard.branch;
	if (!t.isBinaryExpression(branch)) return null;
	if (branch.operator !== '===' && branch.operator !== '!==') return null;
	if (!t.isIdentifier(branch.left) || !t.isIdentifier(branch.right)) {
		return null;
	}

	// `%jmpIf` takes the second successor when the predicate holds.
	const [fallthrough, taken] = guard.consequentAddresses;
	const evalArmAddress = branch.operator === '===' ? taken : fallthrough;
	const callArmAddress = branch.operator === '===' ? fallthrough : taken;
	if (evalArmAddress === callArmAddress) return null;
	const evalArm = func.blocks.get(evalArmAddress);
	const callArm = func.blocks.get(callArmAddress);
	if (!evalArm || !callArm) return null;

	// The eval arm is deleted wholesale, so it may hold nothing but the
	// `DirectEval` and the constant loads feeding it.
	const evalDeclarator = asDeclarator(evalArm.body.at(-1));
	if (!evalDeclarator) return null;
	if (getIRInstruction(evalDeclarator.statement) !== 'DirectEval') {
		return null;
	}
	if (!evalArm.body.slice(0, -1).every(isRematerialization)) return null;
	if (!t.isCallExpression(evalDeclarator.init)) return null;
	const [evalText] = evalDeclarator.init.arguments;
	if (!t.isIdentifier(evalText)) return null;

	const callDeclarator = asDeclarator(callArm.body.at(-1));
	if (!callDeclarator) return null;
	if (getIRInstruction(callDeclarator.statement) !== 'Call') return null;
	const call = callDeclarator.init;
	if (!t.isCallExpression(call)) return null;
	if (
		!t.isMemberExpression(call.callee) ||
		!t.isIdentifier(call.callee.object) ||
		!t.isIdentifier(call.callee.property, { name: 'call' })
	) return null;
	const calleeName = call.callee.object.name;

	// The compared closure must be the call's own receiver, tested against the
	// `globalThis.eval` builtin: that is what makes the two arms equivalent.
	const builtinName = calleeName === branch.left.name
		? branch.right.name
		: calleeName === branch.right.name
		? branch.left.name
		: null;
	if (builtinName == null || builtinName === calleeName) return null;
	const builtin = declarations().get(builtinName);
	if (!builtin) return null;
	if (getIRInstruction(builtin.statement) !== 'GetBuiltinClosure') {
		return null;
	}
	if (
		!t.isMemberExpression(builtin.init) ||
		!t.matchesPattern(builtin.init, ['globalThis', 'eval'])
	) return null;

	if (!isOrdinaryArm(func, evalArmAddress, evalArm, guardAddress)) {
		return null;
	}
	if (!isOrdinaryArm(func, callArmAddress, callArm, guardAddress)) {
		return null;
	}
	const [joinAddress] = evalArm.consequentAddresses;
	if (joinAddress !== callArm.consequentAddresses[0]) return null;
	if (
		joinAddress === guardAddress || joinAddress === evalArmAddress ||
		joinAddress === callArmAddress
	) return null;
	const join = func.blocks.get(joinAddress);
	if (!join) return null;

	// `genCallEvalExpr` calls the callee with an `undefined` receiver, and the
	// eval arm's text is the first source argument.
	const [thisArgument, ...callArguments] = call.arguments;
	if (!t.isIdentifier(thisArgument)) return null;
	if (!isLoadedUndefined(declarations().get(thisArgument.name))) return null;
	const [firstArgument] = callArguments;
	if (firstArgument == null) {
		if (!isLoadedUndefined(declarations().get(evalText.name))) return null;
	} else if (
		!t.isIdentifier(firstArgument) ||
		!sameValue(declarations(), evalText.name, firstArgument.name)
	) return null;

	return {
		guardAddress,
		guard,
		evalArmAddress,
		callArmAddress,
		callArm,
		joinAddress,
		join,
		evalRegister: evalDeclarator.name,
		callRegister: callDeclarator.name,
		callDeclarator,
	};
}

function collapse(func: IRFunction, diamond: Diamond): boolean {
	const armAddresses = new Set([
		diamond.evalArmAddress,
		diamond.callArmAddress,
	]);
	const armRegisters = new Set([diamond.evalRegister, diamond.callRegister]);
	const phi = joinPhi(
		diamond.join,
		diamond.evalRegister,
		diamond.callRegister,
	);
	// Either the merged value is consumed by exactly the join phi's two
	// operands, or the call result is dead and nothing outside the arms can
	// observe the registers the arms define.
	if (countReferences(func, armRegisters, armAddresses) !== (phi ? 2 : 0)) {
		return false;
	}

	// The call stays in the guard rather than moving to the join: the guard is
	// the block whose handlers the arm shared, and a join can sit outside the
	// protected range the call was made in.
	diamond.guard.body.push(...diamond.callArm.body);
	if (phi) {
		const [declarator] = phi.statement.declarations;
		declarator.init = t.identifier(diamond.callRegister);
	}

	diamond.guard.branch = undefined;
	diamond.guard.consequentAddresses = [diamond.joinAddress];
	func.markMergedBlocks(diamond.guardAddress, diamond.callArmAddress);
	func.markMergedBlocks(diamond.guardAddress, diamond.evalArmAddress);
	func.rebuildPredecessorMap();
	return true;
}

/** Collapse every `genCallEvalExpr` diamond back to its source `eval` call. */
export function reduceDirectEvalDiamonds(func: IRFunction): boolean {
	let changed = false;
	let cached: ReadonlyMap<string, Declarator> | null = null;
	// Built on the first guard that reaches the provenance checks, which no
	// eval-free function has. A collapse moves statements between blocks and
	// retargets one phi initializer, so the register index stays valid.
	const declarations = () => cached ??= declarationsByRegister(func);
	// A collapsed join can be the next diamond's guard, so iterate: block order
	// is not guaranteed to present them bottom-up.
	for (let progress = true; progress;) {
		progress = false;
		for (const [address, block] of [...func.blocks]) {
			if (!func.blocks.has(address)) continue;
			const diamond = matchDiamond(func, address, block, declarations);
			if (!diamond) continue;
			if (!collapse(func, diamond)) continue;
			progress = true;
			changed = true;
		}
	}
	return changed;
}
