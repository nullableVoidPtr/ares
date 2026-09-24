# Passes

A catalogue of every transformation Ares runs, in the order it runs them.

This is a map, not a tutorial. Each entry names the pass, where it lives, and
what it is responsible for. Two parts are only summarised here and have their
own documents: the recursive CFG structurer in [`CFG.md`](CFG.md), and
composition, environments and the parallel pipeline in
[`COMPOSE.md`](COMPOSE.md). Line references are against the tree this document
was added to; treat them as starting points, not as guarantees.

## Contents

- [Pipeline overview](#pipeline-overview)
- [1. Bytecode to SSA](#1-bytecode-to-ssa)
- [2. Per-function IR](#2-per-function-ir)
  - [2.1 Function-kind detection](#21-function-kind-detection)
  - [2.2 Lowered-generator recovery](#22-lowered-generator-recovery)
  - [2.3 SSA block to AST](#23-ssa-block-to-ast)
  - [2.4 CFG reduction](#24-cfg-reduction)
  - [2.5 cleanupLiftedBlocks](#25-cleanupliftedblocks)
- [3. Composition](#3-composition)
- [4. Metro module extraction](#4-metro-module-extraction)
- [5. Emission](#5-emission)
- [6. Cross-cutting normalizers](#6-cross-cutting-normalizers)
- [7. Known gaps](#7-known-gaps)

## Pipeline overview

```text
.hbc ─► parse ─► SSA ─► per-function IR ─► composition ─► code
                        │                  │  (per unit)
                        │                  ├─ environment resolution
                        ├─ kind detection  ├─ closure/class inlining
                        ├─ block AST lift  ├─ env slot promotion
                        ├─ CFG reduction   └─ repairs + unreachable strip
                        └─ block cleanup
```

Two entry points, both in `lib/ir/lift.ts`:

| Entry | Mode |
| --- | --- |
| `liftFileWithAnalysis` (`lib/ir/lift.ts:6067`) | Whole bundle, bottom-up composition |
| same, with `compose: false` | `--lift-only`: standalone per-function output, no composition |

The composed path runs these phases, each wrapped in `startPhase`
(`lib/ir/lift.ts:5837`) so `--no-progress` can silence them:

1. `planning bottom-up composition` — `buildBytecodeDerivedPlan`
   (`lib/coldstore/plan.ts:53`) makes the four whole-file bytecode scans once,
   so no worker repeats them.
2. `spilling Metro module fragments` — only for bundles of ≥ 1000 functions.
3. `composing lifted file bottom-up` — `composeLiftedFile`
   (`lib/ir/lift.ts:2528`), section 3 below.
4. `completing recursive CFG summaries`
5. `extracting Metro modules` — only under `--metro-modules`.
6. `generating code` — `emitGeneratedCode` (`lib/ir/lift.ts:5377`).

Per-function IR is built lazily by `LazyIRFunctionStore`, so a function is
only reduced when composition first asks for it.

## 1. Bytecode to SSA

`SSAFunction`'s constructor (`lib/ssa.ts:211`) runs, in order:

| Pass | Location | Responsibility |
| --- | --- | --- |
| `trimProtectedRangeStarts` | `lib/ssa.ts:129` | Hoist instructions out of the head of a protected range when they cannot throw, so the range starts at a real boundary |
| `splitProtectedBlocks` | `lib/ssa.ts:156` | Split basic blocks so no block straddles a `try` boundary |
| `livenessAnalysis` | `lib/utils/liveness.ts:258` | Live registers per block |
| Dominance frontier | `lib/utils/DominanceGraph.ts` | Classic Cytron placement — one `Phi` per register per frontier block |
| Renaming | `lib/ssa.ts` (`renameBlock`) | Version every register definition and use; record per-edge `Phi` sources |

The result is `AddressMap<SSABasicBlock>`, still opcode-shaped — no JavaScript
yet.

## 2. Per-function IR

`IRFunction`'s constructor (`lib/ir/function/mod.ts:1849`) does the whole
per-function pipeline eagerly: handler graph, block graph, then
`detectFunctionKind` → `liftSSABlocks` → `runCFGReduction`.

### 2.1 Function-kind detection

`detectFunctionKind` (`lib/ir/function/mod.ts:1998`) sets `isNativeGenerator`
(entry block opens with `StartGenerator`), `isGenerator`, `isAsync`. If the
function is *not* a native generator, it then tries lowered-generator recovery
and, on success, returns `false` — which aborts the ordinary pipeline, because
recovery has already produced a finished CFG.

### 2.2 Lowered-generator recovery

For Hermes builds that compile generators into a `switch`-over-state machine
rather than using `StartGenerator`. Driven by
`tryInitializeLoweredGeneratorStateMachine`
(`lib/ir/function/loweredGenerator/mod.ts:22`):

| Step | Location |
| --- | --- |
| Recognise the state machine, build a model | `model.ts` / `recognition.ts` |
| Rebuild a real CFG from the case bodies | `recoveryCFG.ts` |
| `finishRecoveredGenerator` | `postRecovery.ts:40` |
| Bounded re-reduction (`sequence`, `shared-sequence-edge`, `inline-terminal`, `shared-alternate-guard`, `simple-if`) to fixpoint | `mod.ts:43` |
| Record a recursive-CFG summary for the recovered body | `mod.ts:55` |

`finishRecoveredGenerator` is itself a long sequence: initial reduce, duplicate
register-scope preservation, iterator-environment destructuring normalization,
`cleanupLiftedBlocks`, environment-scaffolding strip
(`environmentScaffolding.ts`), suspended-finalizer continuation merging and
catch recovery, then `yield*` (`delegateYield`) recovery and a try/catch
re-reduce.

Related: `recordLoweredGeneratorWrapperSlotAliases` /
`applyLoweredGeneratorWrapperSlotAliases` (`loweredGenerator/aliases.ts`) carry
slot aliases from the wrapper function to the recovered body across the
function boundary.

### 2.3 SSA block to AST

`liftSSABlocks` (`lib/ir/function/mod.ts:2024`) walks each SSA block and calls
`liftSSABlocktoIR` (`lib/ir/ast/lift.ts:213`), which turns each SSA instruction
into a statement. Unmodelled or semantically-loaded opcodes become V8 intrinsic
calls (`%Phi`, `%Catch`, `%expectEnvironment`, `%CreateClosure`,
`%getFunctionById`, `%IteratorBegin`, `%ToNumeric`, …) that later passes are
expected to consume. Every register-use identifier is tagged with a
`sourceRegister` `LiftedExtra` (`lib/ir/ast/lift.ts:28`) so later passes can
compare by SSA identity rather than by the textual `rN_M` name.

For native generators, this step also recognises the `ResumeGenerator` prologue
and its `Mov`/`LoadConst` spill-restore run.

### 2.4 CFG reduction

`runCFGReduction` (`lib/ir/function/mod.ts:2267`) wraps
`runCFGReductionInner` (`:2341`) with two speculative retries — see
[`CFG.md` §8](CFG.md#8-phi-rescue) for the full rescue ladder:

- **Short-circuit collapse.** If collapsing short-circuit chains produced an
  unsound body, restore the snapshot and redo the reduction with it suppressed.
- **Destructuring retry.** If the recursive path left a raw iterator protocol
  behind, retry the *original* CFG through the legacy reducer and adopt that
  result when it collapses to one clean block.

`runCFGReductionInner` optionally runs the recursive structurer first
(`runRecursiveCFGAnalysis`, opt-in via `--cfg-reducer=recursive` or
`ARES_RECURSIVE_CFG=1`), and skips the legacy reducer entirely when
`legacyReductionIsRedundant` holds. Otherwise it builds a reduction context
(`createReductionContext`, `:2859`) and runs
`runConfiguredReductionPhases` (`:2880`).

All phases run through `runFixpoint`
(`lib/ir/function/cfg/reductionPipeline.ts:16`): an ordered list of named
`ReductionPass`es, iterated until nothing changes. A pass may return
`'restart'` to abandon the rest of the list and begin the iteration again;
`onStall` passes are attempted only when the ordinary list has stalled;
`cleanup` runs after any productive iteration.

Before the first phase: `normalizeGlobalObjectRegisterUses`.

**Phase `primary`** (`lib/ir/function/mod.ts:2934`):

| Pass | Reducer | Note |
| --- | --- | --- |
| `recursive-leading-phi` | `reduceSharedLeadingPhi` | recursive mode, ≤ 64 blocks; `restart` |
| `guarded-leading-phi` | `reduceSharedLeadingPhi` | guarded-Phi experiment only |
| `wide-acyclic-leading-phi` | `reduceSharedLeadingPhi` | > 64 blocks, loop-free; `restart` |
| `sequence` | `reduceSequence` | merge single-successor/single-predecessor edges |
| `shared-sequence-edge` | `reduceSharedSequenceEdge` | |
| `dangling-guard-tail` | `reduceDanglingGuardTail` | |
| `shared-terminal-phi` | `reduceSharedTerminalPhi` | |
| `predicate-guard-chain` | `reducePredicateGuardChains` | |
| `inline-terminal` | `reduceInlineTerminal` | |
| `shared-alternate-guard` | `reduceSharedAlternateGuard` | |
| `array-destructuring` | `reduceSequentialArrayDestructuring` | |
| `iterator-destructuring` | `reduceIteratorDestructuringSequence` / `…Defaults` | `restart` |
| `switch` | `reduceSwitch` | real switches and recovered compare-chains |
| `shared-guarded-prelude` | `reduceSharedGuardedPrelude` | |
| `or-chain` | `reduceOrChain` | |
| `predicate-guard-chain-after-or` | `reducePredicateGuardChains` | second look after `or-chain` |
| `guarded-boolean-phi` | `reduceGuardedBooleanPhiPredicate` | |
| `nullish-default-return-phi` | `reduceNullishDefaultReturnPhi` | |
| `simple-if` | `reduceSimpleIf` | |
| `delegate-yield-cfg` | `reduceDelegateYieldCFG` | `yield*` protocol loop |
| `delegate-yield-structured` | `reduceDelegateYieldStructuredBodies` | |
| `try-catch` | `reduceTryCatch` | |
| `finalizer-cleanup-plan` | `applyFinalizerCleanupPlan` | |
| `delegate-yield-cfg-after-finalizer` | `reduceDelegateYieldCFG` | |
| `delegate-yield-structured-after-finalizer` | `reduceDelegateYieldStructuredBodies` | |
| `prune-orphaned-blocks` | `IRFunction.pruneOrphanedBlocks` | |
| **stall** `natural-loop` | `reduceNaturalLoop` | only when everything above has stalled |

Passes marked `inline-terminal` / `shared-alternate-guard` /
`shared-sequence-edge` are `legacyBranchPass`es: they are skipped entirely when
the recursive structurer already produced a complete, diagnostic-free,
loop-free, handler-free emission for the function.

Then one `cleanupLiftedBlocks({ preserveStructuredTerminalSiblings: true })`.

**Phase `post-cleanup`** (`:3031`), with `cleanupLiftedBlocks` as the
per-iteration `cleanup`: `sequence`, `shared-sequence-edge`, `switch`,
`predicate-guard-chain`, `merged-guard-phi-terminal`,
`nullish-default-return-phi`, `shared-alternate-guard`, `simple-if`,
`try-catch`, `prune-orphaned-blocks`.

**Phase `timer-fan-in`** (`:3057`) — only when `hasSmallTimerClosureFanIn`:
`sequence`, `dangling-guard-tail`, `shared-terminal-phi`, `shared-leading-phi`,
`predicate-guard-chain`, `inline-terminal`, `shared-alternate-guard`,
`array-destructuring`, `or-chain`, `predicate-guard-chain-after-or`,
`guarded-boolean-phi`, `simple-if`.

Then an unconditional `yield*` pass (`reduceDelegateYieldCFG` +
`reduceDelegateYieldStructuredBodies`), and a per-block statement fixpoint
(`:3097`): `local-for-in` (`cleanupLocalPNameForInLoops`) and
`iterator-close-before-abrupt-exit`
(`stripIteratorCloseBeforeIteratorAbruptExits`).

**Phase `final`** (`:3108`), again with `cleanupLiftedBlocks` as cleanup:
`final-sequence`, `final-shared-sequence-edge`, `final-dangling-guard-tail`,
`final-shared-terminal-phi`, `final-shared-leading-phi`,
`final-inline-terminal`, `final-shared-alternate-guard`, `final-switch`,
`final-simple-if`, `final-prune-orphaned-blocks`.

When `cfgReducer.migrationAudit` is set, every pass invocation is recorded with
its stage, block count and unresolved-Phi count before and after
(`recordMigrationPass`, `:2671`).

### 2.5 cleanupLiftedBlocks

`IRFunction.cleanupLiftedBlocks` (`lib/ir/function/mod.ts:3546`) is the
general-purpose simplifier. It runs many times — after each reduction phase and
as the per-iteration cleanup of two of them.

**It works one basic block at a time.** Each block is wrapped as its own
`t.Program` (`blockProgramWithBranch`) and traversed independently. Nothing in
this pass can see a use that still lives in another CFG block.

Prologue, before the fixpoint:

| Step | Responsibility |
| --- | --- |
| Generator completion registers | Collect `ResumeGenerator` destinations and `yieldRetBlocks` so they are never inlined away |
| `preserveAcrossBlocks` marking (`:3574`) | Mark declarations whose register is referenced from more than one block, so per-block cleanup cannot substitute-then-delete them. Limited to environment handles, scalar initializers and `_param_` aliases — plus, for large loop-free recursive CFGs,everything — so that retaining values does not defeat incremental IR eviction. Recomputed every call, so it stops inhibiting inlining once the CFG has collapsed to one block |
| `liftPhiNodesInBody` (`lib/ir/ast/phi.ts:1449`) | Loop-header Phis, Phi-across-container, unused-Phi removal, Phi assignment lifting, then each `%Phi` declaration |

Then a `do … while (changed)` fixpoint over:

| Pass | Location | Responsibility |
| --- | --- | --- |
| `applyFinalizerCleanupPlan` | `mod.ts:1117` | Finalizer copy classification and removal |
| `stripAdjacentRethrowFinalizerCopies`, `stripTerminalEnclosingFinalizerCopies` | `finalizer.ts:155`, `:246` | Legacy finalizer AST cleanup (legacy reducer only) |
| `reduceSequentialObjectDestructuring` | `cfg/destructuring.ts` | |
| `placeGeneratedBindingsInTree` | `ast/placement.ts` | Authoritative generated-register placement before any Babel binding cleanup; hoist try declarations visible to `catch`, consolidate duplicates and colliding `var` patterns, and fail closed on references with no reaching write |
| `normalizeDuplicateRegisterDeclarationsInBody` | `lift.ts:143` | |
| `foldConditionalValuesInBody` | `ast/phi.ts:2046` | Deferred conditional-value folding |
| `chainSharedRegisterAssignmentsInBody` | `ast/assignment.ts:72` | Fold an adjacent run of stores of one SSA register into `a = b = R` |
| `assignmentUpdateExpression`, `toCompoundAssignment` | `ast/expression.ts:73`, `:155` | `x = x + 1` → `x++`, `x = x + y` → `x += y` |
| `inlineObjectConstruction` | `ast/expression.ts:669` | `new Array(N)` + index writes, array/object literals + `arraySpread` / `copyDataProperties`build-up → one literal |
| `postfixUpdateFromToNumericTemp` | `ast/expression.ts:96` | `%ToNumeric` temp pattern → postfix `++`/`--` |
| **Register inlining** (`mod.ts:3760`) | | The copy propagator; see below |
| `invertTest` on `!(a && b)` | `ast/expression.ts:1186` | De Morgan |
| `flattenElseIfBlock`, `rotateTerminatingGuardIntoElseIf` | `ast/expression.ts:1222`, `:1239` | |
| Phi simplifications (`mod.ts:4615`–`4639`) | `ast/phi.ts` | `simplifyScopedPhiCalls`, `simplifyScopedPhiDeclarations`, `simplifyScopedPhiAssignments`,`simplifyGuardedPrimitivePhiCalls`, `simplifyTerminalReturnPhis`, `liftLoopHeaderPhiAssignments`, `simplifyNullGuardedPhiDeclarations`, `simplifySelfUpdatePhiAssignments`, `removeUnusedPhiExpressions` |
| `stripConsecutiveRethrowFinalizerCopy`, `stripStatementsAfterTerminal` | `mod.ts:923` | |
| `reduceSequentialArrayDestructuring` | `cfg/destructuring.ts` | |
| `cleanupLocalPNameForInLoops` | | `%GetPNameList` → `for…in` |

Recursive Region materialization also runs function-tree placement on the
complete selected candidate before cleanup and again before migration-audit
safety gates. The complete-tree pass is the final lexical-placement authority;
per-block calls protect catch-visible values from being inlined away earlier.

The traversal also carries class/closure/`Construct` reconstruction visitors
(`CallExpression` at `mod.ts:3860`), a `TryStatement` visitor (`:4430`) and a
`BlockStatement` visitor (`:4534`).

After the fixpoint: `simplifyForwardExitLabels` (recursive path only, because
the shape it matches only appears once registers have been folded into the
tests), `stripGeneratorCompletionReturnAfterYield`, a rebuild of
`referencedFunctionIds` from `%getFunctionById` calls, removal of a lone
trailing bare `return`, and `hoistDestructuredParams`.

#### The register inliner

`mod.ts:3760`, keyed on `extractRegisterAssign` (`ast/utils.ts:17`) —
`const rN_M = init`. Guards, in order:

1. Skip declarations tagged `preserveAcrossBlocks`.
2. Skip if the name is a Phi source anywhere in the function (Phi operands are
   cross-block by construction, so the protected set spans the whole function,
   not the block).
3. Skip if `init` contains a `%Phi` call — burying it where no later pass can
   lift it.
4. Require `binding.constant`.
5. Skip `CreateThis` feeding a `%SelectObject` this-argument, `IRCreateClass`
   inits, and non-movable inits feeding `HermesInternal.ensureObject`.
6. Skip an identifier init that would cross an assignment to that same name.

Then:

- **Freely duplicable** (`isFreelyDuplicableInit`, `function/utils.ts:86`:
  scalars, identifiers, or Babel-pure and non-allocating) — substituted into
  *every* reference.
- **Zero references** — dropped, or demoted to a bare expression statement when
  the init is neither pure nor already `consumed`.
- **Exactly one reference**, and that reference does not `crossesControlBoundary`
  (`function/utils.ts:5`) — substituted once.
- Otherwise the declaration stays.

## 3. Composition

Summarised here; [`COMPOSE.md`](COMPOSE.md) covers composition units, function
stores, environment reconstruction, and the cold store and worker pools behind
`--parallel-lift`.

`composeLiftedFile` (`lib/ir/lift.ts:2528`) walks the composition plan
bottom-up, inlining each function body into its creation site, then runs a
fixed sequence of traversals over the result. Composition is where
per-function IR stops being independent, and therefore where anything
cross-function first becomes visible.

It runs **per composition unit**, not once over the bundle. The `root`
parameter (`:2534`) selects the unit:

| Root | Called from | Scope |
| --- | --- | --- |
| `kind: 'function'` | `composeMetroModuleUnits` (`:5203`), `spillMetroModuleFactories` (`:5269`) | One Metro module factory and its subtree, through a `SubtreeIRFunctionStore` over `subtreeFunctionIds` (`:4652`) |
| `kind: 'file'` | `liftFileWithAnalysis` (`:6127`), cold-store path (`:6335`) | The remaining root program |

A unit composed this way is never revisited, so the traversals below run once
per module rather than once per bundle — which is also what lets the Metro
path compose modules in parallel workers (`runComposeWorker`, `:4761`).

`root.creationEnv` (`:2550`) carries the environment argument from the
closure-creation site that produced the unit's root function, so
`%GetParentEnvironment` inside a unit can still resolve outward to the
caller's environment. Metro units pass `callerFuncId: 0`. A unit is therefore
*not* guaranteed to be free of references to an ancestor's environment slots —
see [§7](#7-known-gaps) for why that matters.

Nested function bodies are inlined by `inlineNestedFunctionRef` (`:2627`) and
`inlineCreateGeneratorObject` (`:3055`).

Order of operations:

| # | Step | Location | Responsibility |
| --- | --- | --- | --- |
| 1 | `normalizeDuplicateRegisterDeclarations` | `:3316` | |
| 2 | Generator/async closure composition | `:3464`, `:3487` | `CreateGenerator*` / `CreateAsyncClosure` sites |
| 3 | `indexEnvironmentCreationSites` | `:2827` | Give every `CreateEnvironment` site a stable key before resolution |
| 4 | **Primary traversal** | `:3760` | see below |
| 5 | `reduceForAwaitLoopsInBody`, `hoistYieldStarCompletion`, `cleanupEnvironmentBody`, iterator/destructured param hoisting, `liftHermesES6Class`, object method/getter/setter reconstruction | `:4116` | |
| 6 | `global.X` → `X`, `cleanupClassDefinitionClosure`, `cleanupClassSuper`, `cleanupGuardedNaturalLoops` | `:4250` | |
| 7 | `insertDeferredEnvironmentDeclarations` + second `cleanupEnvironmentBody` | `:4277` | |
| 8 | `postfixUpdateFromToNumericTemp`, `unhoistDeclaredGlobals`, program-level statement cleanup | `:4290` | |
| 9 | `repairPerIterationEnvironmentBindings`, `repairCopiedFinalizerContinuations`, `declareUnboundGeneratedAssignments` | `:5728`, `:5409`, `:5795` | |
| 10 | `fn.call(unboundTemp, …)` → `fn(…)`, dead register/env expression statements, unbound-undefined guards, `stripUnreachableStatementTail` | `:4328` | |
| 11 | `repairCopiedFinalizerContinuations` again, then a final `stripUnreachableStatementTail` sweep | `:4380` | Receiver cleanup in step 10 can make two copies structurally identical for the first time |
| 12 | `lowerProgramCompletionReturns` (file root only) | `:4456` | |

### The primary traversal (`lib/ir/lift.ts:3760`)

| Visitor | Responsibility |
| --- | --- |
| `CallExpression` `%TryGetById` | Global property read → bare identifier, tagged `isReferencedGlobal` |
| `CallExpression` `%DelegateYield` | → `yield*` |
| `CallExpression` `%CreateFunctionEnvironment` / `%CreateTopLevelEnvironment` / `%CreateEnvironment` | Resolve to an `Environment`, replace every owned reference with a `localEnvironment`-tagged marker, give foreign owners an explicit local binding first so they cannot become accidental captures, thendelete the declaration |
| `CallExpression` `%CreateBaseClass` / `%CreateDerivedClass` | → `class` expression, then `inlineAdjacentClassMethods` |
| `MemberExpression` on `%expectEnvironment` (`:3967`) | Slot **read** → `_env_<fn>_<slot>` |
| `AssignmentExpression` to `%expectEnvironment` (`:4006`) | Slot **write** → `_env_<fn>_<slot> = …` |
| `VariableDeclaration` / `Identifier` (`:4045`, `:4057`) | Collect declared and referenced globals |
| `ExpressionStatement` (`:4062`) | `%ThrowIfThisInitialized` cleanup, update/compound assignment folding |

### Environment resolution

`resolveEnvToEnvironment` (`lib/ir/lift.ts:3508`) is the pointer analysis
behind the two `%expectEnvironment` visitors. Given an environment-valued
expression it returns the abstract `Environment` (`lib/ir/environment.ts`) it
denotes, or `undefined` — in which case the intrinsic is left in place rather
than guessed at.

It resolves:

- `%CreateFunctionEnvironment` / `%CreateTopLevelEnvironment` → the function's
  single `Environment`, or a namespaced `_env_<fn>_x<n>` for the second and
  later creation sites in one function (an inlined IIFE, most visibly), so two
  distinct runtime environments never share a slot name.
- `%CreateEnvironment` → an explicit environment whose parent is resolved from
  the call's first argument.
- `%GetParentEnvironment(depth)` → the `localEnvironment` tag if present, else
  the creation-site environment, else `capturedEnvironment` walking the static
  parent chain.
- `%GetEnvironment(env, depth)` → resolve `env`, then walk `depth` parents.
- `%GetClosureEnvironment(closure)` → back through `CreateClosure` /
  `CreateGeneratorClosure` / `CreateAsyncClosure`, or through
  `funcCreationEnvArgs` to the site that created the closure's function.
- A bare identifier → follow the const binding's initializer.

Cycles are cut by a `seen` key set; every recursive entry adds and removes its
own key.

### Environment slot promotion

`cleanupEnvironmentBody` (`lib/ir/ast/module/environment.ts:256`) turns the
flat store sequence into declarations. It early-outs via
`bodyNeedsEnvironmentCleanup` (`:224`) — checked on plain nodes, because most
bodies carry no environment prologue and the expensive part is asking Babel for
a `NodePath` per statement.

| Rewrite | Note |
| --- | --- |
| Drop `_env_x = undefined` prologue stores | Records the name so the later promotion knows to look for a real first write |
| `_env_x = _param_N_M_` → rename | `replaceEnvAliasIdentifiers` rewrites every use to the parameter and deletes the slot |
| First write → `const` / `let` / `function` declaration | `findFirstEnvAssignmentNode` (`:120`) in document order, skipping nested functions. `let` iff`hasOtherBindingWriteNode` (`:171`) finds another write anywhere, nested functions included. A function-expression value becomes a `function` declaration |
| Drop the `var` for a slot nothing reads | Reads only — `referencesIdentifierNode` (`:78`) deliberately ignores writes, since counting one would block the promotion this pass exists to perform |

## 4. Metro module extraction

Opt-in, `--metro-modules <dir>`. Requires composition — it throws under
`--lift-only` (`lib/ir/lift.ts:6073`).

| Pass | Location | Responsibility |
| --- | --- | --- |
| `isMetroDefineStatement` | `ast/module/metro.ts:95` | Recognise `__d(factory, id, deps)` |
| `liftFactory` | `:158` | Rename the five factory parameters to `global`, `require`, `module`, `exports`, `dependencyMap`; rewrite const aliases of them (`constAliasesOf`, `:125`) and delete the alias bindings |
| `planMetroModuleExtraction` | `:370` | Map module ids to output file names (`uniqueModuleFileName`) |
| `extractMetroModules` / `createIncrementalMetroExtractor` | `:517`, `:444` | Write one file per module plus a manifest; incremental variant for bundlesof ≥ 1000 functions |

This is the pass that turns `_param_608_1_(…)` into `require(…)` and
`_param_608_5_["default"]` into `exports["default"]`.

## 5. Emission

`emitGeneratedCode` (`lib/ir/lift.ts:5377`) runs `@babel/generator` over the
composed program and splices in any spilled Metro fragments
(`insertMetroFragments`, `:5363`).

On the recursive path, region emission is a separate stage entirely —
`emitRegionToAST` in `lib/ir/function/cfg/emit/emitRegion.ts`, documented in
[`CFG.md` §6](CFG.md#6-emission). Its local cleanups include
`removeWriteOnlyIdentifierStatements` (`:3451`), which drops assignments to
identifiers declared in that scope and never read.

## 6. Cross-cutting normalizers

Called from many places rather than sitting at one point in the pipeline:

| Pass | Location | Responsibility |
| --- | --- | --- |
| `normalizeDuplicateRegisterDeclarations` | `lib/ir/lift.ts:351` | Two `const rN_M` in one scope — de-duplicate or scope |
| `preserveDuplicateRegisterScopesInBody` | `ast/registerScope.ts:98` | Wrap a run of statements in a block so a re-declared `rN_M` or `_env_…` stays legal. Also handles switch cases |
| `rewriteStructuredStatementLists` | `ast/statementLists.ts:11` | Shared statement-list rewriting for finalizer and recovered-generator cleanup |
| `isRegisterTempName` | `ast/registerScope.ts:19` | `r<reg>_<version>` or `_env_<fn>_<slot>` |
| `isEnvironmentSlotName` | `ir/environment.ts:3` | `_env_<fn>[_x<n>]_<slot>` |
| `comparableAst` / `expressionsEqual` | `ast/utils.ts:52`, `function/utils.ts` | Structural comparison, used heavily by finalizer copy detection |

## 7. Known gaps

Accurate as of this document; the passes above do not cover these.

**No register/env-slot coalescing.** `const r3_6 = require("x"); const
_env_A = r3_6;` keeps both names. The register has two uses and a call is not
freely duplicable, so the inliner correctly declines — but the env slot is a
`const` alias of the same SSA value, so the register could be *renamed* into
it. Nothing does that; `chainSharedRegisterAssignmentsInBody` only chains
adjacent stores.

**No copy propagation after slot naming.** `const r1_1 = _env_A;` inside a
nested function survives because the only general copy propagator
(§2.5) runs per basic block during per-function IR, before slots have names —
at that point the statement is still `const r1_1 = %expectEnvironment(…)[2]`,
which is neither pure nor duplicable. By the time it becomes a trivially
foldable identifier copy, no pass looks at it again: `cleanupLiftedBlocks` has
no call site in `lib/ir/lift.ts`.

Both belong at the end of `composeLiftedFile`, after step 7 of [§3](#3-composition).
The second `cleanupEnvironmentBody` is what decides `const` versus `let` (via
`hasOtherBindingWriteNode`), and single-assignment is exactly the precondition
for forwarding a slot read unconditionally — so the declaration kind that pass
just emitted answers the question without a separate write analysis. Placing
them there also keeps the work per-unit and inside the parallel compose
workers, rather than as one sweep over an assembled bundle.

The soundness condition is slot *ownership*, not unit membership. A unit can
legitimately contain references to an ancestor's slots — `root.creationEnv`
exists precisely so `%GetParentEnvironment` resolves outward — and those are
not complete at that moment, because the owning function's body has not been
composed yet and can still add reads and writes. `envSlotNameOwner`
(`lib/ir/lift.ts:915`) parses the owner id out of the name, including the
namespaced `_env_608_x2_3` form, so the check is set membership against
`subtreeFunctionIds(root.functionId, …)` — the same set the unit's store is
built from. For a self-contained Metro factory that admits every slot in the
unit, which is the common case.

**Redundant `var` for a nested promotion.** When the promoted `const` ends up
inside a nested block, `insertDeferredEnvironmentDeclarations`
(`lib/ir/lift.ts:934`) re-inserts a `var` for the slot, because
`directDeclaredNames` (`:921`) only scans direct body statements. The following
`cleanupEnvironmentBody` cannot clear it, since there is no longer an
assignment *statement* to promote. Reproducible on
`samples/v96/while-let-capture.hbc`.

**Partially-dead stores survive.** `removeWriteOnlyIdentifierStatements`
(`emit/emitRegion.ts:3451`) only removes identifiers that are never read, so a
store that is dead along one path but live along another is kept.
