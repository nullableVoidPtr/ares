# Composition and the parallel pipeline

How Ares turns per-function IR into one program, and how it does that on a
bundle too large to hold in memory.

This covers `composeLiftedFile` and everything around it: composition units,
function stores, environment reconstruction, the LMDB cold store, and the
lift/compose/extract worker pools. [`PASSES.md`](PASSES.md) catalogues the
individual passes in pipeline order and [`CFG.md`](CFG.md) documents the
per-function structurer; this document is about what happens once those
functions have to become a single file.

Line references are against the tree this document was written on; treat them
as starting points, not as guarantees. Design direction and open work for the
binding/environment half live in `BINDING-TODO.md`.

## Contents

- [Entry points](#entry-points)
- [1. The bytecode-derived plan](#1-the-bytecode-derived-plan)
- [2. Function stores and consumption](#2-function-stores-and-consumption)
- [3. Composition units](#3-composition-units)
- [4. Inside composeLiftedFile](#4-inside-composeliftedfile)
- [5. Environments](#5-environments)
- [6. Metro modules](#6-metro-modules)
- [7. The cold store](#7-the-cold-store)
- [8. Workers](#8-workers)
- [9. The pipelined Metro path](#9-the-pipelined-metro-path)
- [10. Degradation and failure](#10-degradation-and-failure)
- [11. Invariants worth preserving](#11-invariants-worth-preserving)
- [12. Debugging](#12-debugging)

## Entry points

All in `lib/ir/lift.ts`:

| Entry | What it does |
| --- | --- |
| `liftFile` / `liftFileWithAnalysis` (`:7485`, `:7493`) | Serial. Lifts lazily as composition asks, composes in-process |
| `liftFileParallel` / `liftFileParallelWithAnalysis` (`:7595`, `:7608`) | `--parallel-lift`. Opens a cold store, lifts in workers, then composes — or, on a Metro bundle, does both at once |
| `liftFunctionsIncrementally` (`:7406`) | `--lift-only`. One standalone function at a time, no composition, nothing retained between functions |
| `collectRecursiveCFGMigrationSummaries` (`:7439`) | `--cfg-migration-audit`. Summaries only; never generates code |

Composition is on unless a function range narrows the run:
`compose = options.compose ?? (options.functionIds == null)`. Metro extraction
requires composition and throws without it.

The serial composed path runs these phases, each wrapped in `startPhase`
(`:7263`) so `--no-progress` can silence the timing without silencing
diagnostics:

1. `planning bottom-up composition` — `buildBytecodeDerivedPlan`
2. `spilling Metro module fragments` — bundles of ≥ 1,000 functions only
3. `composing lifted file bottom-up` — `composeLiftedFile`
4. `completing recursive CFG summaries`
5. `extracting Metro modules` — `--metro-modules` only
6. `generating code`

The parallel path (`liftFileParallelWithColdSession`, `:7628`) replaces the
first two with `preparing cold store`, `planning bottom-up composition` from
the stored plan, and then either `lifting IR functions (parallel)` or
`lifting and composing Metro modules (pipelined)`.

## 1. The bytecode-derived plan

`buildBytecodeDerivedPlan` (`lib/coldstore/plan.ts:106`) makes **one** pass
over every instruction in the bundle and produces everything whole-file that
composition needs:

| Field | Meaning |
| --- | --- |
| `soleFunctionParents` | Each function's unique referencing parent, or `null` when more than one function references it |
| `nonSoleFunctionReferences` | Functions referenced more than once from a single parent |
| `closureReferences` | Which functions each function creates a closure over, in order |
| `environmentCreators` | Functions that add an entry to the environment chain |
| `environmentCreationSites` | Every `CreateFunctionEnvironment` / `CreateTopLevelEnvironment` / `CreateEnvironment` site, per function, in address order |
| `bytecodeGlobalNames` | Every name reached by `TryGetById` or `DeclareGlobalVar` |

Four separate passes used to compute these, and a compose worker ran two of
them itself. On a 127k-function bundle that is 5.9M instructions per pass. They
are all pure functions of the bytes, so they are folded into one scan, stored,
and read back by every thread.

The second reason matters more than the first: this is the only thing that
still iterates `file.functions`. Against a paged cold file, iterating that
array would drag the entire bundle back into memory and undo the point of
paging it — so the plan exists partly to give every other caller an answer that
does not require the walk.

`buildCompositionPlan` (`lib/ir/lift.ts:3146`) reshapes it into what
composition consumes:

- `safelyNestedFunctions` — functions with exactly one referencing parent and
  no second reference from it. Only these may be **consumed** (inlined into
  their creation site); everything else is cloned.
- `parentFunctions` — the composition forest, child to parent.
- `funcEnvs` — the environment graph (section 5).

Address ordering is load-bearing in two places: creation sites are sorted by
address because their order assigns namespace indices, and
`buildEnvironmentGraph` walks function ids ascending because
`findParentEnvironment` looks ancestors up in the map it is still building.

## 2. Function stores and consumption

Composition never touches `IRFunction` construction directly. It goes through
`IRFunctionStore` (`lib/ir/function/store.ts`):

```ts
has(id): boolean
get(id): IRFunction | undefined
delete(id): boolean        // consume
set(id, func): void        // write back
relift(id): IRFunction | undefined
```

The interface is declared apart from `lift.ts` so implementations can live
elsewhere — `lib/coldstore/store.ts` backs one with LMDB, and `lift.ts` already
imports the cold store's plan builder, so the other direction would make the
two modules mutually dependent.

**Consumption is the model.** `delete` means "this function has been inlined
somewhere"; after it, `has` is false and `get` returns undefined, permanently.
That is what stops one function body appearing twice in the output. `relift`
is the deliberate exception: lifting is deterministic, so a consumed function
can be rebuilt from bytecode when a *clone* needs it — and only consumed ids
may be relifted, because generator and async lowering consume the functions
they absorb and those must never be materialized a second time.

Four implementations:

| Store | Used by | Behaviour |
| --- | --- | --- |
| `EagerIRFunctionStore` (`lift.ts:3180`) | Callers that lifted everything up front | A `Map`, plus a consumed set so a deleted function is distinguishable from an absent one |
| `LazyIRFunctionStore` (`:3220`) | The serial path | Lifts on first `get`, LRU cache of 32. This is why serial mode never holds the whole bundle |
| `ColdIRFunctionStore` (`coldstore/store.ts:41`) | The parallel path | Materializes from the store on demand; bounded cache of 512, plus an unbounded *pinned* map for functions composition wrote back |
| `SubtreeIRFunctionStore` (`lift.ts:5981`) | One Metro unit | Wraps another store; restricts **consumption** to the unit's subtree while leaving reads wide |

Two details in `ColdIRFunctionStore` are worth keeping:

**`set` is an overlay, never a write back.** The store is the clean baseline
for the run. A function composition has rewritten is run state, and persisting
it would make a resumed run start from half-composed input.

**Materialized functions are held until consumed, deliberately.** Composition
mutates what the store hands it — `tryGetFunctionExpr` reduces in place — so
returning a fresh object for a second `get` of a live function would silently
discard the first one's work. Consumption is what bounds the map, which on the
Metro path is exactly what happens. The cache limit exists because a *resumed*
run finds nearly every module ready at once and materializes each factory just
to test it: 16,646 factories at ~280KB is ~4.6GB against V8's ~4GB cap, and the
main thread used to die in 21 seconds with `consumed=0`.

`SubtreeIRFunctionStore` restricts consumption and not reads for a specific
reason: a function referenced from several places is cloned rather than
consumed and belongs to no single subtree, so restricting reads would leave
those closures uncomposed.

## 3. Composition units

`composeLiftedFile` (`lift.ts:3339`) runs **per unit**, not once per bundle.
Its `root` parameter selects one:

| Root | Called from | Scope |
| --- | --- | --- |
| `kind: 'function'` | `composeMetroModuleUnits` (`:6598`), `spillMetroModuleFactories` (`:6671`) | One Metro factory and its subtree |
| `kind: 'file'` | `liftFileWithAnalysis` (`:7493`), the cold-store path (`:7628`) | Whatever remains of the root program |

A unit is composed once and never revisited, which is what makes the Metro
units independent enough to run in separate workers.

`root.creationEnv` carries the environment argument from the closure-creation
site that produced the unit's root function, so `%GetParentEnvironment` inside
a unit still resolves outward to the caller's environment. Metro units pass
`callerFuncId: 0`.

Two refusals guard the boundary:

- **An unstructured file root is fatal.** Composition takes the entry block as
  the whole file, which is only sound once the root has reduced to one block.
  When it has not, every other block is code that would silently vanish — on
  `v99/destructuring-init` that was 11 of 12 blocks, and the result still
  passed generated-output validation because the intrinsics it would have
  reported were in the part that disappeared. The analysis-only modes
  (`--cfg-recursive-ast` and friends) are exempt: they disable materialization
  on purpose, so an unstructured root is the state they exist to inspect.
- **A factory that did not reduce to one block is not a module boundary.** It
  stays in the root program rather than becoming a unit.

Synthetic function ids start at `file.functions.length` and are allocated per
unit. They are local identities, not additions to the plan: sharing one
counter across a worker batch made module B reuse module A's synthetic
`Environment` and then claim it for a second creation site.

## 4. Inside composeLiftedFile

The unit's root body becomes a `t.File`, and everything else is folded into
it. Two mechanisms do the folding:

**Inlining** (`popNestedFunction`, `:3473`) takes a safely-nested function out
of the store and drops its body at the creation site. The function is consumed:
it will not appear anywhere else.

**Cloning** (`cloneNestedFunctionRef`, `:3518`) handles everything else — a
function referenced from more than one place, or one already consumed. It
takes a copy, gives it a synthetic id, retargets every `extra.parentFunctionId`
in the copy to that id, clones the original's environment creation sites onto
it, and recursively inlines closures inside it. A bounded cache of 64
`reusableFunctionExpressions` avoids rebuilding the common ones; on a miss it
falls back to `functions.get(id) ?? functions.relift(id)`, because consumption
is irreversible and without the rebuild a raw `%CreateClosure` intrinsic
reaches the output.

Generators and async functions are inlined by dedicated paths —
`inlineLoweredGeneratorFunction` (`:3963`), `inlineGeneratorClosureFunction`
(`:4001`), `inlineAsyncClosureFunction` (`:4071`), `inlineCreateGeneratorObject`
(`:4163`) — because each has a wrapper whose removal changes what the inner
body's environment operand means. That is what
`ElidedWrapperEnvironmentCapture` (`lib/ir/environment.ts:16`) records: `local`
preserves the environment the wrapper created, `parent` preserves an explicit
`GetParentEnvironment` walk from the wrapper's captured environment. Keeping it
as provenance avoids compensating for a removed wrapper by adjusting every
environment depth in the inner body.

Then a fixed sequence of traversals runs over the composed tree. The order is
not incidental — each stage assumes the previous one's output shape:

| # | Stage | Location | Responsibility |
| --- | --- | --- | --- |
| 1 | `indexEnvironmentCreationSites` | `:3827` | Give every creation site a stable key *before* anything resolves one |
| 2 | Primary traversal | `:5033` | Globals, `%DelegateYield`, environment creation, class recovery, slot reads and writes, update/compound folding |
| 3 | `placeEnvironmentSlotsInTree` | `ast/environmentPlacement.ts:58` | One declaration per structured slot, in its creating function |
| 4 | `reduceForAwaitLoopsInBody`, `cleanupEnvironmentBody`, iterator/destructured param hoisting, class and object-method reconstruction | `:5475` | |
| 5 | `global.X` → `X`, class-definition closure and `super` cleanup, guarded natural loops | `:5609` | |
| 6 | `insertDeferredEnvironmentDeclarations` + a second `cleanupEnvironmentBody` | `:5636` | |
| 7 | `coalesceStableStorageAliases`, composed object-rest recovery, `inlineObjectConstructionsToFixpoint` | `:5648`–`:5679` | |
| 8 | `postfixUpdateFromToNumericTemp`, `unhoistDeclaredGlobals`, program-level `f = function f(){}` → declaration | `:5681` | |
| 9 | `repairPerIterationEnvironmentBindings`, `repairCopiedFinalizerContinuations`, `declareUnboundGeneratedAssignments` | `:5716`–`:5718` | |
| 10 | Receiver cleanup (`fn.call(unboundTemp, …)` → `fn(…)`), dead register/env statements, `stripUnreachableStatementTail` | `:5719` | |
| 11 | `repairCopiedFinalizerContinuations` again | `:5771` | Step 10 can make two bytecode copies structurally identical for the first time |
| 12 | `lowerProgramCompletionReturns` and completion-value trimming | `:5785` | File root only |

`normalizeDuplicateRegisterDeclarations` runs between most of these, because
inlining routinely brings two `const rN_M` declarations into one scope.
`traverse.cache.clear()` is called at several points and once per composed
module: Babel's path cache is strongly rooted through `parentPath._store`, so a
function's whole `NodePath` tree is retained until its AST is collected, and
holding a batch's worth of that is what once OOM-killed parallel compose.

The step-9 repairs are placed after every binding and environment rewrite on
purpose. Recursive region emission can expose bytecode-only completion values
and copied finalizer continuations at the composed-AST boundary; deciding on
the *final* syntax is what keeps those decisions from being sample-specific
text matching.

## 5. Environments

Hermes closures capture environments, not variables. A function that needs to
share state with its closures issues `CreateFunctionEnvironment`, writes slots
by index, and its children reach them through `GetParentEnvironment(depth)` or
`GetEnvironment(env, depth)`. Composition's job is to turn that back into
lexical scope: real declarations, in the function that owns them, read by the
closures that captured them.

### 5.1 The environment graph

`Environment` (`lib/ir/environment.ts:24`) is the abstract cell:

- `functionId` — whose environment it is;
- `parent` — the next entry up the chain;
- `namePrefix` — `_env_<id>`, or `_env_<id>_x<index>` for a secondary creation
  site in the same function;
- `siteId` — the bytecode creation site, claimed once composition resolves it.
  `claimSite` throws if two different sites claim one environment.

`slotName(slot)` is `${namePrefix}_${slot}`, and `isEnvironmentSlotName`
(`:20`) is the matching predicate every downstream pass uses.

`buildEnvironmentGraph` (`:66`) builds the chain from the plan's
`environmentCreators` and the composition forest, and `capturedEnvironment`
(`:105`) walks *n* parents up from a function. The graph is built once, from
the bytecode plan, rather than per worker — and it takes the creator set rather
than the file, because working that set out means reading every instruction in
the bundle.

### 5.2 Creation sites and identity

An environment's identity is its **creation site**, `(functionId, kind,
address)`, keyed as `<fn>:<kind>:0x<address>` (`plan.ts:53`). Not its emitted
name, and not AST node identity.

That distinction was learned the expensive way. The site table used to be built
by traversing the composed tree, which ran once before child functions were
inlined and therefore only ever saw the root's creation calls — on TestApp, 30
sites out of a bundle whose output names 322 functions' worth of namespaced
environments. It also keyed sites on node identity, which a clone does not
share, and fell back to a traversal counter for anything it had not seen. The
bytecode has every site, in address order, before any of that happens.

`indexFunctionCreationSites` (`:3833`) assigns each function:

- a **primary** site — the first `CreateFunctionEnvironment` or
  `CreateTopLevelEnvironment` — which owns the bare `_env_<fn>` prefix, because
  that is what its children's `GetParentEnvironment` resolves to;
- an **explicit index** for every other site, which becomes
  `_env_<fn>_x<index>`, so an inlined IIFE's second environment can never share
  a slot name with the first.

`creationSiteOf` (`:3898`) reads the key off the call's own provenance
(`extra.parentFunctionId` and `extra.address`) rather than any map, so a clone
answers the same as the original and a call that only appears after inlining
answers the same as one present from the start. `environmentCreationIndex`
(`:3936`) throws a `LiftError` rather than guessing when a site has no key —
guessing is what produced traversal-order-dependent names.

Clones get `cloneEnvironmentCreationSites` (`:3880`): addresses are unchanged
by cloning, so the original's site list transfers wholesale under the synthetic
id. Without it a clone's own primary environment is not recognized as primary,
and it is emitted in the `_x<index>` namespace while its children still resolve
to the bare prefix.

### 5.3 Resolving an operand

`resolveEnvToEnvironment` (`:4697`) is the pointer analysis behind everything
else. Given an environment-valued expression it returns the `Environment` it
denotes, or `undefined` — in which case the intrinsic is left in place rather
than guessed at.

It answers a tagged `environment-handle` location immediately; otherwise it
resolves structurally, following:

- `%CreateFunctionEnvironment` / `%CreateTopLevelEnvironment` →
  `localEnvironmentForCreate` (`:4817`): the function's primary environment
  when the site is primary, an already-claimed environment when the site key
  matches one, otherwise a fresh `_env_<fn>_x<index>` namespace;
- `%CreateEnvironment` → an explicit environment whose parent comes from the
  call's first argument;
- `%GetParentEnvironment(depth)` → the `localEnvironment` tag if present, else
  the creation-site environment, else `capturedEnvironment` up the static
  chain;
- `%GetClosureEnvironment(closure)` → back through `CreateClosure` /
  `CreateGeneratorClosure` / `CreateAsyncClosure`, or through
  `funcCreationEnvArgs` to the site that created the closure's function;
- a bare identifier → the const binding's initializer, with
  `assignedEnvironmentLookupForUse` (`:3099`) recovering the case where Babel
  sees only assignments, provided every candidate is equivalent and one of them
  dominates the use.

Cycles are cut by a `seen` key set; every recursive entry adds and removes its
own key.

Resolution emits `localEnvironmentCall` (`:4979`) — a `%GetParentEnvironment(0)`
carrying `extra.localEnvironment` and, when the site is known, an
`environment-handle` storage tag. Keeping a marker rather than a name is what
lets later stages re-resolve the same cell after the tree has been rewritten
around it.

Clones need one extra edge: a synthetic id has no entry in the bytecode-derived
parent graph, so its captured creation environment becomes the parent of the
clone's local function environment. Without that edge, nested closures resolve
the clone's own slots but every `GetParentEnvironment` depth above it leaks
into the output.

### 5.4 Slots

A slot access lifts as `%expectEnvironment(handle)[slot]`. The primary
traversal's `MemberExpression` and `AssignmentExpression` visitors (`:5240`,
`:5316`) resolve the handle and replace the access with an `_env_*` identifier
tagged `{kind: 'environment-slot', environment: site, slot}`. An unresolved
handle leaves the intrinsic alone and increments `unresolvedSlots`.

Three passes then turn those identifiers into declarations:

**`placeEnvironmentSlotsInTree`** (`ast/environmentPlacement.ts:58`) gives each
structured slot exactly one declaration, in its creating function. The creating
function's body is the authoritative placement because it contains every
closure that can capture the cell and preserves the slot's initial `undefined`
value. Later dataflow may narrow an uncaptured, single-write slot — it may
never copy a captured declaration into a child.

**`cleanupEnvironmentBody`** (`ast/module/environment.ts:292`) turns the flat
store sequence into idiomatic declarations: drop the `= undefined` prologue,
rename a slot that only ever holds a parameter, promote the first write to
`const`/`let`/`function`, and drop the declaration of a slot nothing *reads*.
That last one counts reads only — counting writes would block the promotion the
pass exists to perform.

**`coalesceStableStorageAliases`** (`ast/alias.ts:534`) removes the generated
locals that alias a stable source. `lib/ir/ast/alias.ts` is where storage
identity is defined: registers, parameters (including `this` at index 0 and
overflow parameters spelled `arguments[i]`), the `arguments` object, an
environment handle, and an environment slot. It exists because five files had
each grown their own textual answer to "which location does this expression
denote", keyed on a `_param_\d+_\d+_` shape that matches one of three surface
forms at a shifted index. A location that cannot be established is `null`,
which every caller must read as *unknown*, never as *no alias*.

### 5.5 Identity telemetry

`EnvironmentIdentityDiagnostics` (`lift.ts:2217`) counts every path by which a
site or slot was identified — `byAddress` versus `positional` versus `unowned`,
resolved versus ambiguous versus unresolved handles, slot placement outcomes,
and each reason an alias fold was refused. It accumulates across every unit in
a run, including compose workers, whose counts are merged back by
`addEnvironmentIdentityDiagnostics` (`:2323`).

The point is that every site key feeds `_env_<fn>_x<index>` naming, so a key
that depends on traversal order makes emitted *names* depend on it. These
counters exist so the remaining fallbacks can be retired against a measurement
rather than an assumption. `ARES_DEBUG_ENV_IDENTITY=1` prints the record.

## 6. Metro modules

A Metro bundle is one `__d(factory, id, deps)` call per module in the entry
body. That shape is the only one in which the bundle has *independent*
composition units, and the pipeline exploits it three times over: to compose
modules apart from the root program, to compose them in parallel, and to
overlap composition with lifting.

`resolveMetroFactoryUnit` (`:6089`) recognizes one: a `__d` call whose first
argument is a `%CreateClosure` of a safely-nested function that the store still
has and whose body reduced to a single block. `forEachMetroFactoryCall`
(`:6132`) visits the top-level calls first and then sweeps nested ones the
first pass did not claim, which is the order the fragments are composed in.

Composing a unit produces a `t.FunctionExpression`, which is generated to
source immediately and replaced in the entry body with a placeholder
identifier, `__ARES_METRO_FRAGMENT_<index>__`. The placeholders are spliced
back at emit time by `insertMetroFragments` (`:6789`) through a
`MetroFragmentSource` (`:6771`) — an indirection, not an array, because on the
parallel path the fragments are never in this process's memory at all: compose
workers write them into the store's `frag` database and the emitter streams
them straight back out. `take` rather than `get`, because each fragment is
emitted exactly once and dropping the reference on the way out is the point.

Two things are shared into each unit rather than recomputed:
`collectSharedGlobalNames` (`:5925`) merges the plan's bytecode global names
with what the root entry body references, and the unit's `creationEnv` carries
the factory's captured environment.

`--metro-modules <dir>` is a separate, later step: it takes the composed
program and writes one file per module plus a manifest.
`createIncrementalMetroExtractor` (`ast/module/metro.ts:440`) writes each
module as soon as its factory is composed, so a module AST can be released
before the next one is built; `extractMetroModulesParallel` (`:589`)
distributes the per-module transform, codegen and file write across workers
while keeping filename assignment and the `program.body` rewrite on the main
thread. `liftFactory` (`:158`) is what turns `_param_608_1_(…)` into
`require(…)`: it renames the five factory parameters to `global`, `require`,
`module`, `exports`, `dependencyMap` and rewrites their const aliases.

## 7. The cold store

`--parallel-lift` used to hand every worker a copy of the bundle bytes and let
each rebuild the whole `HBCFile`. `new HBCFile(bytes)` disassembles every
function up front: on a 127k-function bundle that is 2,583MB of resident set
and six seconds — per worker.

Everything replicated that way — the per-function disassembly, the whole-file
plans derived from it, and the lifted IR snapshots — is a deterministic
function of the bundle bytes. So it is computed once and written to an LMDB
store (`lib/coldstore/`). LMDB is the right shape for it: readers are lock-free
and zero-copy out of a shared mmap, so the OS page cache becomes one
reclaimable cache shared by every thread instead of *n* private V8 heaps the
collector will never hand back. It is also durable, which is what makes
`--spill-reuse` possible.

It is deliberately not called "spill": `spillMetroModuleFactories` already
means something unrelated.

### 7.1 Layout

| Database | Contents |
| --- | --- |
| `meta` | Fingerprint and phase markers |
| `fn` | `functionId` → encoded disassembled `Function` |
| `plan` | The file header and the bytecode-derived plan |
| `snapHead` | `functionId` → `IRFunctionSnapshot` minus `blocks` |
| `snapBody` | `functionId` → the `blocks` array |
| `frag` | Composed module fragment source, by function id |

The snapshot split is the interesting one. Everything except `blocks` is small
and is what cheap questions want — whether a function is a generator, what it
references, its handler graph, its recursive-CFG summary. `blocks` is the Babel
AST, and on that bundle it is ~3.2GiB of the store. Keeping them apart means a
cheap question never pages in an AST, which is what lets recursive-summary
collection walk every function without materializing one.

### 7.2 Sessions, fingerprints, phases

`openColdSession` (`coldstore/session.ts:64`) prepares the store for a run. The
fingerprint is the schema version, the SHA-256 and length of the bundle bytes,
the Hermes version, and a hash of the lift options; the store directory is
*named* by it, which is what makes two runs with different options — say both
halves of `--cfg-reducer=compare` — safe to run at once.

A store whose fingerprint does not match is **rebuilt, never migrated**: the
contents are a cache of work that can always be redone, so migration code would
be pure liability. Same reason `COLDSTORE_SCHEMA_VERSION` is bumped rather than
handled.

Three phase markers record what a resumed run may trust: `fn` and `plan` for
the bytes-derived work, `snap` for lifting. `snap` is only marked when a run
lifted the *whole* file with no failures — a `--function` range writes perfectly
good snapshots and a later run is welcome to find them, but marking the phase
complete would tell that run every other function is present too. Nor may a run
that left functions unlifted mark it, or a later run with the bug fixed would
be told there is nothing left to attempt.

Reuse is opt-in (`--spill-reuse`) even though the fingerprint covers everything
that changes the output, because a store that is wrongly reused produces
yesterday's output silently — a far worse failure than redoing the work.
`--spill-keep` keeps the store without reusing it; `--spill-dir` overrides the
default `$XDG_CACHE_HOME/ares/spill`.

Phase completeness is coarse on purpose, so it is not the only question asked:
`unliftedFunctionIds` (`:2765`) filters by actual snapshot presence, because
snapshots commit batch by batch and a run that dies partway leaves real work on
disk — 39,360 functions of it, in the first attempt at that bundle.

### 7.3 The paged file

`readColdFile` (`coldstore/file.ts:155`) rebuilds an `HBCFile` whose functions
are paged. The split is between what is small enough to hold and what is not:
the string table, literal buffers and object shapes are tens of megabytes and
are read by index from all over the lifter, so they live in one header record
held whole; the functions are the 2.5GB, so they are one record each behind a
`DecodedCache` (default 64 entries).

`file.functions` is a `Proxy` over a sparse array rather than a class with a
`get` method, because it is a plain array everywhere it is used — indexed,
`.length`-ed, iterated. The proxy keeps every one of those working. The
iterating callers are the ones that had to be routed through the plan instead;
iterating a paged file pages in the whole bundle and the store buys nothing.

On the parallel path the caller's eagerly parsed file hands its parts over
(`file.adoptPartsFrom(coldFile)`) once the store is written, so the main thread
pages like everyone else rather than keeping a second full copy alive.

### 7.4 Encoding

`lib/coldstore/codec.ts` exists for exactly two values msgpackr cannot carry.
`HermesEmpty` is a `Symbol`, which the encoder rejects outright. Negative zero
is worse, because it fails *silently*: msgpackr writes `-0` as integer `0`, and
a byte comparison of the composed TestApp bundle turned up 452 lines that
differed for that reason alone. Both are replaced with tagged placeholders by a
copy-on-write walk that returns its input unchanged when there is nothing to
do, and records whether it changed anything so decoding can skip the walk —
which is the common case for every record in the store.

## 8. Workers

Three separate pools, with different lifetimes and different reasons to exist.

### 8.1 Lift workers

`lib/ir/function/worker.ts` takes batches until told to stop. It receives no
bundle and hands back no snapshots: it pages the functions it was asked for out
of the store and writes their snapshots straight back in, so nothing crosses
the message boundary but ids.

`written` is reported *after the transaction commits*, not after lifting. A
scheduler acting on "lifted" would dispatch a module whose dependencies are
still sitting in an uncommitted batch. One transaction per batch, because a
commit per function would serialize every worker on LMDB's single writer.

`traverse.cache.clear()` runs after every function, success or failure. Babel's
path cache is only weakly rooted at the top — child paths hang off
`parentPath._store`, a strong `Map` — so a function's whole `NodePath` tree is
retained until its AST is collected. Outrunning the collector that way is what
OOM-killed the first parallel compose attempt. A throwing traversal leaves its
paths behind too, so the failure path clears as well, or a failure leaks what a
success would not.

`LiftWorkerPool` (`lift.ts:2466`) owns the queue:

- **One ordered list, not a static chunk per worker.** That is the whole point:
  the queue can be reordered while the pool runs, and a worker that draws a
  function taking minutes no longer strands a batch behind it.
- **`prioritise(first)`** moves ids to the front, ordered by their position in
  `first` rather than in the queue. Partitioning while keeping queue order
  threw that away — the module closures together name nearly every function, so
  the head came back as the whole queue unchanged, no module completed early
  and composition could not start until lifting had ended.
- **Recycling.** V8 grows a heap to its high-water mark and never returns it, so
  a worker that once drew a very large function keeps that peak for as long as
  it lives. Harmless when a worker took one chunk and exited; fatal once they
  live for the whole run — that bundle died at 12.5GB. Workers are retired every
  16 batches (~256 functions) against a reopen measured at ~0.1s, and the peak
  reported heap is printed at the end.
- **Retirement is a handshake, not a `terminate()`.** The worker releases its
  LMDB *reader* and leaves the shared environment alone. `close()` from a worker
  unmaps the env under every other thread — lmdb-js hands every open of a path
  the same native env with no refcount, and zeroes only the calling handle's
  address, so the others keep a live-looking handle onto freed memory. That
  surfaced as a garbled instruction name mid-lift.
- **Failures are reported when they happen.** Settling waits for whatever is
  still in flight, and a batch of large functions can run for hours; a run that
  has already lost its queue then looks alive with no clue why.

Defaults: `workerCountFor` (`:2441`) is `--workers` or
`hardwareConcurrency - 1`, clamped to the number of functions and to the number
of batches that actually exist. Batch size 16, recycle after 16 batches.

### 8.2 Compose workers

`lib/ir/compose/worker.ts` composes a batch of Metro units. It is given a store
path, the units, and a `readable` list of ids — the reference closure of those
modules, everything they may read. It opens the store, reads the file and the
plan from it, and builds a `ColdIRFunctionStore` restricted to that read set.

The read set is passed explicitly because a worker used to be handed snapshots
and could therefore only see what it was sent; reading straight from the store
would silently widen that to the entire program. It is a *read* set, not a
consume set — `SubtreeIRFunctionStore` still owns consumption.

Results come back as ids: which factories produced a fragment, what composing
them consumed, and the environment-identity counters. The fragment *source*
goes into the store's `frag` database instead, because a bundle's worth of
composed modules is hundreds of megabytes of string and the emitter streams it
straight out again. On the way out the worker releases its reader — not
`close()`, for the reason above.

### 8.3 Metro extraction workers

`runMetroModuleWorker` (`ast/module/metro.ts:548`) is the simplest pool: tasks
are round-robin chunked, each task is a structured-cloneable `__d` statement
(the lifted `.extra` markers and comments survive the clone), and the worker
transforms, generates and writes one module per task.

## 9. The pipelined Metro path

`liftAndComposeMetroParallel` (`:6293`) removes the barrier between lifting and
composing. That barrier was never a dependency — a module needs its own
reference closure lifted and nothing else — it was just the shape the code had,
and on a bundle where lifting runs for hours it meant every core sat idle
through a composition phase that could have overlapped all along.

It is selected when composition is on, `--metro-modules` is not, and the bundle
has at least 1,000 functions. Everything else lifts to completion and composes
once, because a Metro bundle is the only shape with independent units.

The sequence:

1. Function #0 jumps the queue, because enumerating the modules needs the entry
   body. Everything else keeps lifting behind it. On a resumed run #0 is
   usually already committed and enumeration fires off the first `written`
   batch instead.
2. `enumerate` collects the factory candidates in source order, computes each
   one's reference closure from `closureReferences`, and builds `waitingOn`
   (closure ids a candidate still needs) plus `wantedBy` (the reverse index, so
   a written id only touches the candidates that want it).
3. The remaining lift queue is reordered to module order, so modules become
   composable roughly as fast as the bundle can produce them.
4. As batches commit, candidates whose closures are complete become ready and
   are dispatched in batches of 8 to at most 4 compose workers. A partial batch
   is sent rather than leaving a worker idle when nothing else is composing.
5. When lifting finishes, whatever is still ready is drained; anything never
   released was outside every module's closure or was never composable, and the
   root program takes it.
6. Placeholders are assigned in **source order** regardless of completion
   order, the consumption reported by each worker is replayed against the main
   thread's store, and the root function — captured at enumeration — is put
   back, because the consumption replay above it would otherwise turn "root was
   consumed" into "root is gone".

A resumed run seeds `written` from the store rather than from a flag: treating
already-committed functions as unsatisfied would leave every module waiting
forever on ids no worker is going to lift again.

## 10. Degradation and failure

The pipeline is built to finish with a worse answer rather than not finish.
Each of these is a deliberate downgrade, and each reports itself:

| Failure | Consequence |
| --- | --- |
| A function cannot be lifted | It is skipped, not thrown. `has` is false, `get` is undefined, and `cloneNestedFunctionRef` leaves the raw `%CreateClosure` in place — one un-inlined closure rather than no output. One unliftable function must not end a run over 127,282 of them |
| An unliftable function blocks a module | It still *resolves*: modules waiting on it are released and compose without it. Otherwise one bad function silently hangs every module whose closure reaches it |
| A compose batch throws | Its `__d` calls are left unrewritten and the root program composes those modules inline — worse output for a few, a complete run rather than none |
| Summary emission throws after reduction | Recorded as `recursiveCFGSummaryEmissionError`; the function's own reduction already succeeded and stands |
| The store's fingerprint does not match | Rebuilt from scratch |

Reporting for all of these goes through `writeDiagnostic` (`:2813`), which
writes straight to the file descriptor. `--no-progress` used to replace
`console.error` with a no-op for the whole run, which reached far past progress
— three separate reports had to escape it this way before progress got its own
sink (`lib/utils/progress.ts`). A report that a function could not be lifted is
the run's actual output; suppressing it turns "one closure was left raw" into
"the run looked clean".

The failure summary is printed as a block at the end as well as inline, because
on a bundle that size the inline notices scroll past long before the run
finishes, and each entry is a reproducible single-function bug — the line even
prints the `--function` invocation that reproduces it.

## 11. Invariants worth preserving

- **Consumption is irreversible.** `delete` means the body is now somewhere
  else. Only a consumed id may be relifted, and the rebuilt copy belongs to
  whoever asked for it — it is never put back.
- **The store is a clean baseline.** `set` is an overlay on the run, never a
  write back. Persisting composed state would make a resumed run start from
  half-composed input.
- **Only ids cross a worker boundary.** Snapshots, fragments and plans travel
  through the store. Anything sent by `postMessage` is paid for twice, in
  structured clone and in main-thread residency.
- **Never iterate `file.functions` on a paged file.** Route the question
  through `buildBytecodeDerivedPlan` instead, or the store buys nothing.
- **Only the session owner closes the store.** Workers call `releaseReader`.
  Closing a shared env from a worker unmaps it under every other thread and the
  reads that follow return freed memory rather than an error.
- **Environment identity is `(creation site, slot)`**, never the `_env_*`
  spelling and never AST node identity. A clone shares its original's sites; a
  name is an output detail.
- **A slot's declaration belongs to its creating function.** Narrowing an
  uncaptured single-write slot is allowed; copying a captured declaration into
  a child is not.
- **An unknown storage location is unknown, not absent.** `locationOf` returning
  `null` must never be read as "no alias".
- **Fragment order is source order.** Completion order is a scheduling detail
  and must not reach the output.
- **Progress is silenceable; diagnostics are not.** `reportProgress` for one,
  `writeDiagnostic` for the other.

## 12. Debugging

CLI:

```sh
# Serial, whole bundle
deno run --allow-read --allow-env src/ares.ts bundle.hbc

# Parallel, with a store that survives the run
deno run --allow-read --allow-env --allow-write --allow-ffi src/ares.ts \
	bundle.hbc --parallel-lift --spill-keep

# Reuse a matching store: skips lifting entirely
deno run --allow-read --allow-env --allow-write --allow-ffi src/ares.ts \
	bundle.hbc --parallel-lift --spill-reuse

# One function, no composition
deno run --allow-read --allow-env src/ares.ts bundle.hbc --function 852

# Standalone functions, no composition, nothing retained between them
deno run --allow-read --allow-env src/ares.ts bundle.hbc --lift-only

# Modules to a directory, plus a manifest
deno run --allow-read --allow-env --allow-write src/ares.ts bundle.hbc \
	--metro-modules out/modules
```

`--parallel-lift` needs `--allow-ffi` for LMDB's native addon; the serial path
never opens a store and never loads it, which is why `lib/coldstore/mod.ts`
imports the module type-only.

Environment flags:

| Flag | Effect |
| --- | --- |
| `ARES_COLDSTORE_STATS=1` | Print `materialised` / `consumed` / `live` / `pinned` / `peakLive` for each `ColdIRFunctionStore`, from the main thread and from every compose batch |
| `ARES_DEBUG_ENV_IDENTITY=1` | Dump `EnvironmentIdentityDiagnostics` as JSON at the end of each composition unit |
| `ARES_FAULT_FN=<id>` | Make one function unliftable, so the skip-and-continue path can be exercised without finding a real decompiler bug |

Working out where a run went wrong:

1. **Wrong or missing code for one function** — reproduce it alone with
   `--function <id>`; that takes composition out of the picture entirely. If it
   is right alone and wrong in the bundle, the problem is composition.
2. **A raw `%CreateClosure`, `%CreateEnvironment` or `%expectEnvironment` in
   the output** — an intrinsic reaching the output means resolution declined.
   For closures, check whether the function was consumed and the clone path hit
   an empty store; for environments, `ARES_DEBUG_ENV_IDENTITY=1` says whether
   the site was identified at all (`unowned` / `positional`) or identified and
   left unresolved (`unresolvedHandles`, `unresolvedSlots`).
3. **A slot declared in the wrong scope** — the placement counters separate the
   cases: `slotPlacementUnresolved` means the owner could not be proved,
   `slotPlacementCaptured` means it was placed at the owner and a nested
   function reads it.
4. **Memory** — `ARES_COLDSTORE_STATS=1` for what the stores hold, and the
   `[lift] peak lift-worker heap` line for what a worker reached. A high
   `peakLive` with `consumed=0` is the resumed-run shape described in section 2.
5. **A run that seems stuck** — the pool prints when it stops dispatching and
   how many batches are still in flight. Nothing after that line means it is
   waiting on those, not deadlocked.
