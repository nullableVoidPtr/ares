# JavaScript bindings

How Ares turns Hermes binding bytecode into emitted JavaScript declarations.

This is a map, not a source-language guarantee. Hermes bytecode does not carry
an explicit `var` / `let` / `const` tag for most bindings. Ares therefore keeps
three separate concepts apart:

- **runtime storage** — registers, parameters, global object properties, and
  environment slots;
- **storage identity** — provenance such as `(environment creation site, slot)`,
  not the generated identifier spelling;
- **emitted declaration form** — `var`, `let`, `const`, function declarations,
  and class declarations chosen by conservative cleanup passes.

Line references are against the tree this document was written on; treat them as
starting points, not stable anchors.

## Contents

- [1. What Hermes bytecode preserves](#1-what-hermes-bytecode-preserves)
- [2. Raw lift conventions](#2-raw-lift-conventions)
- [3. Storage identity](#3-storage-identity)
- [4. Environment slots](#4-environment-slots)
- [5. Environment-slot promotion](#5-environment-slot-promotion)
- [6. Parameters and coalescing](#6-parameters-and-coalescing)
- [7. Stable storage alias coalescing](#7-stable-storage-alias-coalescing)
- [8. Declared globals](#8-declared-globals)
- [9. Overlap between env promotion and globals](#9-overlap-between-env-promotion-and-globals)
- [10. Binding-kind recovery heuristics](#10-binding-kind-recovery-heuristics)
- [11. Invariants](#11-invariants)

## 1. What Hermes bytecode preserves

Hermes sema and IR know declaration kind, but ordinary HBC mostly preserves only
storage effects.

Current Hermes lowering, as observed in `../hermes`:

| Source binding                | Typical bytecode shape                                                                    | Ares confidence                                                    |
| ----------------------------- | ----------------------------------------------------------------------------------------- | ------------------------------------------------------------------ |
| global `var x`                | `DeclareGlobalVar "x"`, then global object `PutById*` for initializers                    | high: global var-like declaration                                  |
| function/local `var x`        | environment slot initialized to `undefined`; later env loads/stores                       | medium: mutable function storage, exact source kind lost           |
| `let x`                       | environment slot; with TDZ enabled, `LoadConstEmpty` prologue and `ThrowIfEmpty` on reads | high: lexical/TDZ; low for `let` vs `const`                        |
| `const x`                     | same slot shape as `let`; non-declaration writes emit TypeError logic                     | low unless reassignment throw pattern is present                   |
| parameter captured by closure | parameter copied into an environment slot in the prologue                                 | high for parameter storage once `LoadParam` provenance is retained |

Important non-signals:

- `StoreToEnvironment` vs `StoreNPToEnvironment` is value representation
  (`non-pointer` vs pointer-ish), not declaration kind.
- SSA `const rN_M = ...` declarations are generated temporaries, not source
  `const`.
- An environment slot name such as `_env_1_0` is a surface spelling. Its durable
  identity is the creation site and slot index.

## 2. Raw lift conventions

The instruction lifter lives in `lib/ir/ast/lift.ts`.

Raw SSA definitions are emitted as one-assignment generated bindings:

```js
const r3_1 = expr;
```

The helper path is `registerAsIdentifier` -> `declareConst` / `assignRegister`
(`lib/ir/ast/lift.ts:21-76`). Later passes may turn some generated `const`
declarations into `let` plus assignments when placement or Phi handling requires
mutation. That still describes generated storage, not source declaration kind.

Environment instructions initially lift to intrinsics:

```js
const r0_1 = %CreateEnvironment(parent, size);
const r1_1 = %expectEnvironment(r0_1)[0];
%expectEnvironment(r0_1)[1] = r2_1;
```

Relevant cases:

- `CreateTopLevelEnvironment` / `CreateFunctionEnvironment` /
  `CreateEnvironment` in `lib/ir/ast/lift.ts:518-545`.
- `LoadFromEnvironment` in `lib/ir/ast/lift.ts:959-977`.
- `StoreToEnvironment` / `StoreNPToEnvironment` in
  `lib/ir/ast/lift.ts:981-1002`.

Global declarations lift differently. `DeclareGlobalVar` becomes a real `var`
declarator immediately and is tagged as declared-global metadata
(`lib/ir/ast/lift.ts:256-266`):

```js
var x; // declarator.extra.isDeclaredGlobal = true
```

## 3. Storage identity

Storage provenance is defined in `lib/ir/ast/alias.ts`.

`StorageLocation` distinguishes:

- SSA registers: `(owner function id, register index, SSA version)`;
- parameters: `(owner function id, Hermes parameter index, form)`;
- the `arguments` object;
- environment handles;
- environment slots: `(environment creation site, slot)`.

`locationKey()` (`lib/ir/ast/alias.ts:86-104`) is the stable key. Use it instead
of generated identifier text when comparing storage.

Parameter identity is deliberately not just name-based:

- Hermes parameter index `0` is `this`.
- Named parameter `i` is usually emitted as `_param_<functionId>_<i - 1>_`.
- Overflow parameters may lift through `arguments[i - 1]`.

`locationOf()` can read explicit `extra.storageLocation` tags and falls back to
legacy `_param_...` spelling where needed. Unknown is `null`; callers must not
interpret unknown as “no alias”.

## 4. Environment slots

Environment graph construction lives in `lib/ir/environment.ts`:

- `Environment` stores the owning function id, parent environment, generated
  name prefix, and optional creation-site identity.
- `slotName(slot)` emits names like `_env_3_0`.
- `isEnvironmentSlotName()` recognizes generated env names.

Composition rewrites `%expectEnvironment(env)[slot]` into generated identifiers
in `lib/ir/lift.ts:6826-6990`:

1. Resolve the environment handle with `resolveEnvToEnvironment`.
2. Tag the handle with `StorageLocation.kind === 'environment-handle'` when the
   creation site is known.
3. Replace the member expression or assignment target with `env.slotName(slot)`.
4. Tag the slot identifier with `StorageLocation.kind === 'environment-slot'`
   keyed by creation site and slot.

After this rewrite, the tree contains normal-looking JavaScript identifiers:

```js
_env_1_0 = value;
const r4_1 = _env_1_0;
```

The tags keep those identifiers tied to runtime cells even if names collide,
move, or get cloned.

## 5. Environment-slot promotion

Two passes cooperate: placement first, cleanup/promotion second.

### 5.1 Placement

`placeEnvironmentSlotsInTree()` (`lib/ir/ast/environmentPlacement.ts:58`) gives
each structured environment slot one declaration in its creating function.

Core rule from the implementation comment: an environment slot is a runtime
cell, so its identity is `(creation-site, slot)`, never its `_env_*` spelling.
The creating function body is the authoritative declaration location because it
contains every closure that can capture the cell.

The pass:

- groups all tagged environment-slot references by `locationKey()`;
- bridges untagged textual `var _env_*;` declarations onto provenance when
  exactly one tagged group uses the same spelling;
- inserts a missing `var _env_*;` declaration at the creator body's directive
  prologue boundary;
- removes duplicate/misplaced declarations;
- tracks captured slots when reference owners cross function boundaries.

It deliberately inserts `var`, because at that stage the pass is placing the
runtime cell, not yet deciding whether a first assignment can be narrowed to
`let` or `const`.

### 5.2 Cleanup and promotion

`cleanupEnvironmentBody()` (`lib/ir/ast/module/environment.ts:292`) runs on a
program or function body. It removes compiler prologue scaffolding and promotes
first real assignments when that does not change control flow.

The pass first records env declarations in the current body:

```js
var _env_1_0;
var _env_1_1 = undefined;
```

Then it scans the leading declaration/prologue assignment area:

- `var _env = undefined` is removed and the slot is recorded as having only a
  prologue undefined initializer.
- `_env = undefined` is removed for the same reason.
- `var _env = _param` or `_env = _param` may be coalesced to the parameter if
  the parameter alias is safe; see [Parameters and coalescing](#6-parameters-and-coalescing).
- scanning stops on the first non-prologue assignment that cannot be removed.

For a removed undefined prologue, the pass finds the first later assignment to
that slot with `findFirstEnvAssignmentNode()` (`lib/ir/ast/module/environment.ts:134`).
It does not descend into nested functions. If the first assignment lives in the
same body list, the assignment can be promoted:

```js
var _env_1_0;
_env_1_0 = value;
```

becomes either:

```js
const _env_1_0 = value;
```

or:

```js
let _env_1_0 = value;
```

`hasOtherBindingWriteNode()` (`lib/ir/ast/module/environment.ts:183`) decides
`let` vs `const`: any other assignment/update to the same name anywhere under
the body, including nested functions, makes the binding mutable.

Promotion is blocked when:

- the first assignment is still `undefined`;
- the RHS reads the same slot, except function expressions are allowed;
- the first assignment is inside a conditional, loop, `try`, or nested statement
  list. Moving a declaration out of those lists would change which paths
  initialize a captured runtime cell.

### 5.3 Function-expression promotion

`declarationForEnvironmentAssignment()` (`lib/ir/ast/module/environment.ts:217`)
handles RHS function expressions specially.

```js
var _env_1_0;
_env_1_0 = function f() {
	return f;
};
```

can become:

```js
function f() {
	return f;
}
```

When the function expression has a name that differs from the slot name, the pass
checks that:

- the LHS has environment-slot provenance;
- no existing binding conflicts with the function-expression name, except the
  function expression's own local name.

If safe, it tags the declaration id with the old slot location and rewrites all
old `_env_*` reads/writes to the promoted function name. This preserves recursive
uses after the `FunctionExpression`'s inner name binding disappears.

If unsafe, it falls back to preserving the function expression under the env
identifier:

```js
var _env_1_0 = function f() {};
```

## 6. Parameters and coalescing

Hermes copies captured parameters into environment slots so inner functions can
read them through the environment chain. Ares tries to remove the duplicate slot
when doing so is observably equivalent.

### 6.1 Env-slot to parameter coalescing

Inside `cleanupEnvironmentBody()`, `claimParameterAlias()`
(`lib/ir/ast/module/environment.ts:318`) accepts an initializer only when:

- `locationOf(init)` is a parameter;
- the parameter has exactly one direct reference in the body, the prologue copy;
- that parameter location has not already been claimed by another slot.

The one-claim rule matters. `replaceEnvAliasIdentifiers()` rewrites writes to
the env slot onto the parameter. If two different env slots were coalesced onto
one parameter, writes through one slot would accidentally update the other slot's
storage.

Accepted shapes:

```js
var _env_1_0 = _param_1_0_;
```

or:

```js
_env_1_0 = _param_1_0_;
```

After coalescing, every `_env_1_0` read/write in the current body is replaced
with `_param_1_0_`, and the env declarator/assignment is removed.

### 6.2 Materialized parameter aliases

`coalesceParameterAliases()` (`lib/ir/ast/alias.ts:409`) handles a different
surface shape:

```js
let r26_r7_11_0 = _param_3_0_;
yield r26_r7_11_0;
r26_r7_11_0 += 1;
```

This can appear after environment recovery materializes a slot as a generated
local rather than keeping the `_env_*` spelling. The pass folds the local into
the parameter only when:

- the local is a generated local name;
- the initializer denotes a named parameter;
- the parameter has exactly one reference, the initializer;
- no nested function shadows either name;
- the rewrite does not cross `this` or `arguments` rebinding hazards.

`this` and `arguments` are excluded because a nested non-arrow function rebinds
both. Folding them across a function boundary changes semantics.

## 7. Stable storage alias coalescing

`coalesceStableStorageAliases()` (`lib/ir/ast/alias.ts:688`) removes generated
snapshot aliases after composition has attached storage provenance.

Typical source shape after composition:

```js
const r7_1 = _env_2_4;
return r7_1;
```

If the source location has no intervening writes and visibility is unambiguous,
the local can be removed:

```js
return _env_2_4;
```

The pass works over storage locations, not text. It collects writes by
`locationKey()` first (`lib/ir/ast/alias.ts:700-734`), then evaluates alias
candidates.

Two directions are supported:

1. **Snapshot aliases**: generated register/local aliases of parameters or env
   slots can be replaced by the source storage when the source is stable.
2. **Register-to-environment sinks**: a dominating `const _env = rN` can promote
   the register's defining binding to the environment slot because the env slot
   is the durable captured storage.

The pass blocks on:

- local mutation of the alias binding;
- more than one write to the source location;
- a write that does not dominate the alias;
- visibility/binding mismatches across scopes;
- unresolved external writes to textual `_env_*` names.

## 8. Declared globals

Global `var` has a different source of truth: the `DeclareGlobalVar` bytecode
instruction.

Raw lift emits:

```js
var x; // extra.isDeclaredGlobal
```

Then normal global stores become assignments:

```js
x = value;
```

`unhoistDeclaredGlobals()` (`lib/ir/ast/module/binding.ts:71`) turns the hoisted
marker plus assignment into a source-looking declaration.

Algorithm:

1. Require a `var` declarator with `extra.isDeclaredGlobal`.
2. Crawl the Babel scope and get the binding for the declared name.
3. Find the shallowest assignment with `findShallowestAssignment()`:
   - bare `x = expr` expression statements;
   - `for (x in obj)` / `for (x of iter)` targets.
4. Replace the assignment site with a declaration.
5. Remove the original hoisted declaration.

Plain assignment promotion:

```js
var x;
x = value;
```

becomes:

```js
var x = value;
```

Matching function expression promotion:

```js
var f;
f = function f() {};
```

becomes:

```js
function f() {}
```

Matching class expression promotion:

```js
var C;
C = class C {};
```

becomes:

```js
class C {}
```

A second fallback in `lib/ir/lift.ts:7009-7030` records inferred function globals
for top-level `global.foo = function foo() {}` shapes. Later,
`lib/ir/lift.ts:7340-7357` can replace `foo = function foo() {}` with a function
declaration when that inferred global name is known.

Declared globals stay `var` because `DeclareGlobalVar` is var-like by
construction. Do not rewrite these to `let` or `const` without an independent
source of evidence.

## 9. Overlap between env promotion and globals

The two systems share a shape:

```text
hoisted/prologue marker + later first assignment -> declaration at assignment
```

They also both promote matching function expressions to declarations.

The implementation is intentionally separate because the invariants differ:

| Concern              | Environment slots                                                | Declared globals                                   |
| -------------------- | ---------------------------------------------------------------- | -------------------------------------------------- |
| Identity             | `(environment creation site, slot)`                              | source/global property name                        |
| Initial marker       | generated `var _env_*;` or `undefined` prologue store            | `DeclareGlobalVar` -> tagged `var name;`           |
| Captured by closures | yes, runtime cell must stay in creating function                 | global object property, not a closure cell         |
| Kind narrowing       | `const`/`let` by later writes; function declaration special case | always `var`/function/class from var-like bytecode |
| Main pass            | `cleanupEnvironmentBody()`                                       | `unhoistDeclaredGlobals()`                         |
| Promotion guard      | same body list to preserve initialization paths                  | shallowest binding assignment                      |

A shared helper for “turn assignment into declaration” would be possible, but a
shared pass would be risky. Env slots need provenance and capture/dominance
checks; globals need Babel binding and `isDeclaredGlobal` metadata.

## 10. Binding-kind recovery heuristics

Ares should treat binding kind as recovered evidence, not as bytecode truth.

Recommended confidence levels:

- **High**: `DeclareGlobalVar name` -> global `var name`, or matching
  function/class declaration after unhoisting.
- **High**: env slot initialized with `LoadConstEmpty` and checked with
  `ThrowIfEmpty` -> TDZ lexical binding. This does not distinguish `let` from
  `const`.
- **Medium**: env slot with a single dominating non-`undefined` assignment and
  no other writes -> emit `const` for readability.
- **Medium**: env slot with later writes/updates -> emit `let`.
- **Low**: env slot initialized to `undefined` and no TDZ evidence -> source may
  have been `var`, `let` with TDZ disabled, or compiler storage. Keep current
  conservative output unless more evidence exists.
- **None**: `StoreNPToEnvironment` vs `StoreToEnvironment`, register temporary
  `const`, and generated `_env_*` spelling do not encode source binding kind.

Current known blocker for TDZ-based recovery: `ThrowIfEmpty` is modelled in the
bytecode/disassembly layer but raw AST lifting does not yet lower it like
`ThrowIfUndefined`.

## 11. Invariants

Preserve these when changing binding recovery:

1. Compare storage by provenance (`locationKey()`), not by emitted identifier
   text.
2. Unknown provenance is unknown, not proof that two values are distinct.
3. Captured environment slots belong to their creating function unless moving
   them is proven safe.
4. Do not move an environment declaration out of a conditional/loop/try first
   assignment; that changes which paths initialize the cell.
5. Do not coalesce two environment slots onto one parameter.
6. Do not fold `this` or `arguments` aliases across non-arrow function
   boundaries.
7. Do not infer source `const` from generated SSA `const` declarations.
8. Do not infer global `let`/`const` from `DeclareGlobalVar`.
9. Function-expression promotion must preserve recursive self-reference and avoid
   clobbering an existing binding with the function expression's name.
10. Prefer local, late rewrites after composition and environment placement;
    early rewrites fight passes that still need explicit runtime storage.
