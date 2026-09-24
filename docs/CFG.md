# The recursive CFG reducer

How Ares turns a lifted SSA control-flow graph into structured JavaScript.

This describes the recursive Region structurer under `lib/ir/function/cfg/`.
Line references are against the tree this revision was written on; treat them
as starting points, not as guarantees.

The finite cleanup checklist lives in `TODO.md`, and the longer-term
migration plan, work packages, and status numbers live in `CFG-TODO.md`.
This document describes the machinery those two files talk about; it
deliberately carries no corpus counts, because they change every batch.

## Contents

- [Enabling it](#enabling-it)
- [Pipeline overview](#pipeline-overview)
- [1. The canonical CFG](#1-the-canonical-cfg)
- [2. Descriptors](#2-descriptors)
- [3. Regions](#3-regions)
- [4. The recursive descent](#4-the-recursive-descent)
- [5. Exception regions](#5-exception-regions)
- [6. The bounded control forest](#6-the-bounded-control-forest)
- [7. Emission](#7-emission)
- [8. Verdict, selection, materialization](#8-verdict-selection-materialization)
- [9. Retries and speculation](#9-retries-and-speculation)
- [10. Compatibility telemetry](#10-compatibility-telemetry)
- [11. Invariants worth preserving](#11-invariants-worth-preserving)
- [12. Debugging](#12-debugging)

## Enabling it

The recursive reducer is opt-in. The CLI default is still `legacy`
(`src/ares.ts:99`), and `envCFGReducerOptions()` only returns `recursive`
under `ARES_RECURSIVE_CFG=1` (`lib/ir/function/cfg/options.ts:25`).

```sh
deno run --allow-read --allow-env src/ares.ts bundle.hbc --cfg-reducer=recursive
```

`--cfg-reducer` takes `legacy`, `recursive`, or `compare`; `compare` lifts the
bundle twice, reports the first differing line, and exits non-zero when the two
outputs disagree (`src/ares.ts:873`). Changing the default is Phase 7 policy in
`CFG-TODO.md`, not a recognition task.

`deno task coverage:samples` runs with `--cfg-reducer=recursive`, so the
sample corpus validates the recursive path rather than the legacy one.

## Pipeline overview

```text
bytecode -> SSA -> canonical CFG -> descriptors -> Region -> emitted AST
                         |                |
                   graph-only work   HandlerGraph actions
```

Entry is `runCFGReductionInner()` (`lib/ir/function/mod.ts:2689`), which
calls `runRecursiveCFGAnalysis` (`recursiveAnalysis.ts:17`) and thence
`structureCFG` (`structure/structureRegion.ts:104`).

The defining constraint is that **nothing in the recursive path mutates the
CFG**. The legacy reducers rewrote blocks in place, folding control flow
into block bodies; the recursive reducer builds an `ImmutableCFG` and
produces a separate `Region` tree over it, leaving the graph untouched.
That immutability is what lets `CFGAnalyses` cache all nine derived analyses
with no invalidation at all (`algorithms/mod.ts:45`) — the input an analysis
was derived from cannot change under it, so a stored result stays true for
as long as the object lives.

It is also why `hasPrestructuredControl(cfg)` exists (`regions/region.ts:408`):
recovery rules read boundaries out of the raw branch graph, so once an ordinary
reducer has folded control into a block body the remaining edges no longer
describe the interior of those statements, and the rules must decline.

One graph rewrite runs _before_ the first analysis rather than after it:
`reduceProtectedArrayDestructuring` is driven to a fixpoint at
`lib/ir/function/mod.ts:2707`. Hermes lowers protected array destructuring so
that both default evaluation and target assignment can throw into an
iterator-close-and-rethrow tail; native destructuring has exactly those
completion semantics, so collapsing the protocol first is strictly clearer than
letting Region turn its exception edges into labelled completion carries. The
pass verifies and removes its own handlers, which is what makes it safe here.

## 1. The canonical CFG

`ImmutableCFG.fromIRFunction` freezes, per block:

- `body` — deep-cloned statements;
- `ssaInstructions` — the SSA form, retained for descriptor recovery;
- `sourceAddresses` — provenance back to the original bytecode blocks;
- `terminator` — a typed `Terminator` rather than a trailing statement.

Normal and exceptional edges are kept in **separate** graphs
(`normalSuccessors`/`normalPredecessors` versus
`exceptionalSuccessors`/`exceptionalPredecessors`). The whole design leans
on that split: normal-graph dominance says nothing about a handler block
that is only ever entered by an exceptional edge, so any rule that walks one
graph has to decide explicitly what it does about the other.

`normalizeCFGForRegions` (`normalization.ts:70`) is deliberately thin —
currently a single `prune-unreachable` pass. It is now **always enabled on the
primary recursive path**: `runCFGReductionInner` passes
`normalizeForRegions: true` unconditionally, because Region must consume the
canonical reachable graph. That matters most on a re-analysis after a
graph-level cleanup such as short-circuit collapse, which can detach old branch
blocks even when the bytecode CFG started fully reachable; leaving them in made
the same Region succeed only under debug or audit. Validation is the part that
stays opt-in — under audit or debug, `structureCFG` also runs
`validateRegionDescriptorInvariants` and `validateRegionFunctionMetadata`,
recording anything they find as `invalidNormalization` diagnostics.
Normalization is graph-only by charter: it may reshape the CFG, but it must
never build the final high-level AST.

`structureCFG` additionally records `unreachableBlock` diagnostics (skipping
blocks that have exceptional predecessors) and `irreducibleSCC` diagnostics
for any normal-flow SCC without a dominating single entry.

## 2. Descriptors

`recoverDescriptors` (`descriptors/mod.ts:36`) precomputes five families
_before_ any structuring decision is taken. This is the central separation
of concerns: **descriptors are recognition, regions are shape.** A
descriptor answers "what does this subgraph mean"; a region answers "how
does it nest".

| Descriptor       | What it recovers                                                                                                                                                                                                                                                        |
| ---------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `phis`           | Each `%Phi` as a set of per-edge assignments (`EdgePhiAssignment`)                                                                                                                                                                                                      |
| `switches`       | Real `switch` terminators **and** recovered compare-chains (`kind: 'compareChain'`), with cases, default target, join, covered blocks                                                                                                                                   |
| `exceptions`     | The handler forest from `HandlerGraph`: protected blocks and entries, catch body, equivalent compiler-split catch aliases, canonical finally address and ownership proof, copy roots, `boundedFinallyBodyBlocks`, copy/suffix descriptors, and the `finalizerCopyModel` |
| `delegateYields` | `yield*` protocol loops (requires `analyses`)                                                                                                                                                                                                                           |
| `destructuring`  | Array/object patterns, plus `protocolCandidates` — sites recognized as destructuring but not yet reconstructed                                                                                                                                                          |

A sixth field, `compatibility`, is not a descriptor: it is the telemetry sink
described in section 10. It is written during structuring and never read by it.

Two details are easy to lose and expensive to rediscover:

**Phi recovery is gated on the lifted declaration.** `recoverPhiDescriptors`
(`descriptors/phis.ts:26`) walks the _unresolved `%Phi` uses in the block body_
and matches each one to an SSA Phi instruction; an instruction with no
surviving use is skipped. Post-reduction Region analysis reuses the original
SSA instructions, so without that gate a Phi already lowered into predecessor
assignments by a legacy reducer would be replayed and duplicated, and an
otherwise structured edge action could be left unplaceable. The lifted `%Phi`
use is the authoritative signal that edge lowering is still required in this
CFG snapshot. Its _target_ is not: a Phi-to-Phi cleanup can rename it, so
matching falls back to the SSA source multiset.

**A Phi source is an edge action, not a block fact.** An incoming value is
kept only while that predecessor edge still exists in this CFG view;
normalization can remove an unreachable predecessor while retaining its
reachable join.

## 3. Regions

`Region` (`regions/region.ts:11`) is a closed union:

`basic`, `sequence`, `if`, `switch`, `tryCatch`, `tryFinally`, `loop`,
`delegateYield`, `break`, `continue`, `labelBreak`, `labelContinue`,
`deferredExit`, `return`, `throw`, `terminalReference`, `fallback`.

### Ownership

Every region carries `sourceBlocks: AddressSet<BlockAddr>` — the ownership
set, and the invariant the whole structurer is policed by. Each block should
be claimed exactly once across the tree.

Ownership alone is not sufficient, so three derived views exist:

- `regionCoveredBlocks` — ownership plus non-owning `terminalReference`
  leaves. Used only when proving that recursive decomposition represented
  every block in a candidate arm.
- `regionStructuredBlocks` — deliberately distrusts aggregate
  `sourceBlocks`, because loop and exception Regions use theirs as
  _boundaries_ and a `fallback` may name an entire failed subgraph. It
  rebuilds coverage from children plus the explicit header the composite
  owns.
- `regionDuplicateOwnership` — catches double-claims.
- `regionDuplicatedSSABlockCounts` — expands every live Region claim through
  `CFGBlock.sourceAddresses`, pairs the normal Basic/control carrier for each
  live block, and counts repeated original SSA blocks even when compatibility
  reduction split them into distinct live blocks.

`RecursiveCFGSummary.duplicatedSSABlockCounts` exposes that last view as
hex-address keys with total claim counts. Recognized canonical finalizer blocks
and compiler-generated finalizer copies are excluded: their repetition is
compiler lowering, not recursive-Region duplication.

A `terminalReference` is the deliberate escape hatch: it proves
control-flow coverage without taking block ownership, so a shared `return`
or `throw` leaf can appear in several arms without any of them claiming it.
It must not satisfy an enclosing loop's body inventory, which is why
`regionStructuredBlocks` returns the empty set for it.

### Weak SESE

A strict single-entry/single-exit region rarely exists in real bytecode.
`findWeakSESE` (`algorithms/sese.ts:99`) takes an entry and an optional
normal exit, collects a dominance-bounded body, then transitively pulls in
exception handlers — a region containing a protected block must contain its
handler, or the recursive builder cannot form the `try` and falls back to a
Basic Region that drops the handler entirely. Handler blocks are added to
the body after the dominance check, because normal-graph dominance says
nothing about them; they belong to the region because the protected block
they guard does.

Every normal edge leaving the body that is not the declared exit becomes a
`DeferredExit`.

### Deferred exits and edge actions

This is the unifying idea for control flow that does not nest. A
`DeferredExit` (`regions/region.ts:722`) is one of:

`toJoin`, `loopBack`, `loopExit`, `exception`, `functionReturn`,
`functionThrow`

each carrying `EdgeAction[]` (`regions/region.ts:750`), where an action is:

- `phi` — a set of `EdgePhiAssignment`s;
- `finally` — a `FinallyCopyAction` (canonical address, copy root, owner
  block, kind: `tryTrailer` / `catchTrailer` / `abruptExitTrailer` /
  `canonical`);
- `statement`, `return`, `throw`.

**Anything that must happen on an edge rather than inside a block is an edge
action.** Phi lowering is just one kind of it, sitting alongside
finalizer-copy replay and abrupt-transfer statements.

`LoopRegionExit` (`regions/region.ts:203`) models the same thing for loops:
`{from, to, kind, label?, targetLoop?, trailer?, continuation?,
normalCompletionFlag?, sequenceExit?}`. An ordered trailer — blocks that
execute on the exit edge before control leaves the loop — belongs to the exit,
not to the body. `sequenceExit` is distinct from the break itself: the loop
first exits normally, then the trailer transfers past the loop's ordinary
continuation. `normalCompletionFlag` is set when a break bypasses a
header-only exit trailer, and exists so recovered iterator syntax can keep
natural exhaustion distinct from an explicit body `break` once both have
collapsed into one JavaScript loop statement.

When a trailer's source blocks are already represented inside the loop body,
the loop records the corresponding exits in `bodyOwnedExits` instead of
duplicating the trailer. Emission still completes the trailer's terminal block
and outgoing Phi edge before transferring control from the loop.

### Retry loops

A `tryCatch` Region may carry a `retryLoop` (`regions/region.ts:76`): a catch
whose trailer re-enters the protected body rather than falling through. It
records `header`, an optional scalar/Phi `prelude` immediately before the
protected entry, `normalExit`, the `backedge`, an optional `conditionalExit`
(`{decision, exit}`, for a trailer that retries on one branch and leaves on the
other), and any path-local `abruptExits` distinct from the normal exit. The
emitter lowers the conditional case itself, placing each edge's Phi actions on
the backedge and the `break` (`emit/emitRegion.ts:949`), which is why
`collectStructuredBranchBlocks` counts the decision block as structured
(`recursiveSummary.ts:1070`).

### Value-level provenance

`ConditionalValueCandidate` records the CFG provenance of a value merged by
an If Region — branch, both arm entries, join — and deliberately **does not
select JavaScript syntax**. It offers `forms: ['shortcut', 'ternary']` and
leaves the choice to the emitter, which can only make it after inspecting
the actual Phi values.

## 4. The recursive descent

`structureRegionAt(entry, cfg, analyses, descriptors, allowed?, active,
structuredHandlers)` (`structure/structureRegion.ts:739`) is the core.

### Threaded state

- **`allowed`** — an optional block restriction set. This is how a parent
  hands a child its scope without slicing the CFG. A cursor outside the set
  yields either a `terminalReference` for a `return`/`throw`/`unreachable`
  terminator whose exceptional scope matches the incoming block, or an empty
  sequence. A root reference still requires an unprotected terminal.
- **`active`** — the ancestor chain, for cycle detection. A repeat, or a
  depth exceeding the block count, yields a `fallback` with reason
  `recursive structuring cycle`.
- **`structuredHandlers`** — a shared, monotonic ledger of handler addresses
  already emitted as a region. It is threaded **by reference and never
  cloned**, so each exception descriptor is structured exactly once: a
  continuation block that still carries a structured descriptor's
  `protectedEntries` must not re-open it.

The ledger is rolled back on discard. If a speculatively structured nested
region is not the one committed, the marks it made are removed so genuine
structuring re-fires. There are now five such rollback sites in
`structure/exceptionRegion.ts` (`:733`, `:891`, `:1034`, `:2168`, `:2321`) —
one per speculative candidate. Any new speculative path that consults the
ledger must do the same, and must roll back _before_ recursively composing its
replacement arms: waiting until afterwards makes a genuine nested `try` look
already consumed.

### Memoisation

Restricted calls are memoised as well as unrestricted ones, keyed by the
restriction. Without it the descent is exponential — it re-derives the same
sub-region once per path that reaches it. The recorded case is function
#115926 of a 127k-function bundle: 66 blocks, 1.82 million calls at a
bounded depth of 52, never finished.

The memo is only enabled when the CFG is **acyclic and handler-free**,
because only then are the extra parameters provably irrelevant to the result
and so safely absent from the key:

- with no handlers, `structuredHandlers` is never mutated — its only write
  is the rollback `delete` under handler structuring;
- on an acyclic CFG, `active` can never fire, since it detects a block that
  is its own ancestor and a DAG has none.

Both preconditions must hold. Weakening either one silently changes results.

### The ladder

The body is a priority ladder. Each rule attempts a shape and returns
immediately on success:

1. `tryStructureExceptionRegion` — first, so that a delegate `yield*` loop
   inside a user `try` is wrapped by the try rather than the reverse. The
   recursion then recognizes the delegate inside the try body, and the
   ledger stops the try re-firing.
2. `tryStructureDelegateYieldRegion`
3. `tryStructureLoopRegion`, plus `tryStructureMixedAbruptLoopSwitch`
4. `tryStructureBoundedLoopForest` — skipped when a for-in dispatch or a
   recovered compare-chain switch owns the shape, so the specialized
   descriptor stays the owning recursive boundary
5. `tryStructureSwitchRegion`
6. `tryStructureOptionalLoopRegion`
7. `tryStructureLoopGuardRegion`
8. `tryStructureSharedAlternateGuardRegion`
9. `tryStructureIfRegion` — cross-checked against
   `tryStructureSharedAcyclicRegion`
10. `tryStructureSharedAcyclicRegion`
11. `tryStructureSharedSwitchContinuation`
12. `tryStructureGuardedTerminalSwitch`
13. `tryStructureTerminalIfLadder`
14. `structureStraightLineSequenceFrom` + `appendSingleTopLevelLoop`, then
    `tryStructureResidualScope` if unstructured branches remain
15. `fallback`

Two entries in that list are conditionally suppressed rather than merely
declining:

- **The loop entry guard.** `shouldDeferLoopEntryGuard`
  (`structureRegion.ts:2421`) recognizes an entry `if` where exactly one arm is
  a natural-loop header and the other is outside that loop. Steps 9 and 13 are
  skipped for it, because an If Region there splits the loop between arms; the
  loop rules and `appendGuardedLoopWithHierarchicalExit`
  (`structureRegion.ts:3007`) own the shape instead and reconstruct the guard
  around a whole loop.
- **The shared-acyclic barrier set.** `tryStructureSharedAcyclicRegion` is
  given switch dispatch blocks _and_ the `protectedEntries` of every exception
  descriptor not yet in the ledger, so a DAG composition cannot cut through a
  protected range that still needs its own owner.

### The continuation pattern

Every composite rule is followed by the same shape: structure the join, and
if the resulting region owns blocks not already inside the composite, wrap
both in a `sequence`.

```ts
const continuation = structureRegionAt(region.join /* ... */);
if (
	continuation.sourceBlocks.size > 0 &&
	!continuation.sourceBlocks.isSubsetOf(region.sourceBlocks)
) return sequenceRegion([region, continuation]);
return region;
```

The subset test is what stops a continuation being claimed twice. It is the
ownership invariant enforced locally at every composition site.

### Why step 9 is a cross-check rather than a preference

Weak-SESE arms contain only nodes dominated by their respective entries. So
when both arms flow through a shared non-terminal node before the real join,
an otherwise valid-_looking_ If Region can omit that node entirely.
`ifRegionIsComplete` compares the If Region's covered blocks against the
exact-SESE DAG and prefers the DAG **only** in that proven
incomplete-coverage case. The ordinary preference is still the readable
nested If.

When both ordinary weak-SESE attempts decline, `tryStructureIfRegion` has one
last narrow case: exactly one direct successor is a terminal block and the
other is the live continuation. It emits a non-owning `terminalReference` only
when the header and terminal have identical exceptional scopes. Running this
after the ordinary forms is load-bearing: Phi joins and loop-owned completion
paths keep their richer Regions instead of being flattened into an early exit.

### Recursion guards inside the arm callbacks

The child callbacks passed to the rules are not plain recursion. They
decline in specific, load-bearing cases:

- A cursor that is the current entry returns `null` — re-forming the same
  region would recurse forever.
- `exceptionSplitsProtectedRange(cursor)` declines: recursing into the
  middle of a protected range would split it and move a finalizer Phi onto a
  different enclosing `if`. Note the deliberate narrowness — declining
  _every_ arm in a protected function instead left the arm a Basic Region
  and orphaned the handler entirely.
- In loop children, when the CFG has exception regions or a for-in dispatch,
  ordinary blocks are declined so the specialized descriptor stays the
  owning boundary; only loop headers, switch dispatches and exception
  entries may recurse.
- An exception entry whose protected blocks are not contained by the child's
  `allowed` set is declined.

Arm construction also trims: `trimEnclosingExceptionalArm`
(`structure/ifRegion.ts:605`) removes the exceptional-only suffix outside
`allowed` from an arm inside a protected body. Weak-SESE discovery pulls the
enclosing handler into _both_ arms even though the surrounding Try Region
already owns it, and the arm then fails its own protected-body ownership
check. A nested handler that genuinely belongs to the arm is itself allowed,
and therefore blocks the rewrite.

### Top-level post-processing

After the descent, `structureCFG`:

1. runs `regionNeedsExactContinuationForest` (`structureRegion.ts:242`), which
   detects two objective failures — a weak-SESE arm that omitted a shared
   continuation, and a conditional block left represented only as Basic — and
   retries with `tryStructureWholeCFGContinuationForest`, which supplies the
   forest with contractible catch ranges (section 5);
2. runs `labelPendingLoopSequenceExits` (`structureRegion.ts:3210`) to name
   deferred sequence exits;
3. records a `local-fallback-region` compatibility selection if any `fallback`
   survives in the final tree;
4. catches a `RangeError` for call-stack exhaustion and downgrades it to an
   `unstructuredRegion` diagnostic rather than failing the whole run.

## 5. Exception regions

`tryStructureExceptionRegion` (`structure/exceptionRegion.ts:23`) is the
largest rule in the ladder and the one that has grown most. It runs first,
and it is where protected code stops being a special case for everything
downstream.

The body of a protected range is not always what the exception table says.
Hermes only has to cover instructions that can throw, so one source-level
`try` may appear as several protected ranges separated by a non-throwing
`Mov` block. `protectedBodyBlocks` (`:1855`) absorbs a _unique, linear_
register-copy bridge whose predecessor is already protected — it is the
lexical path from one range to the next. An inner table can omit a bridge
the enclosing table still covers; that outer ownership is not a competing
lexical scope, so only an unrelated or nested descriptor prevents the
expansion. Anything broader than a transparent bridge belongs to
binding/alias coalescing, not here.

Hermes can also split one source catch when an inlined protected expression
gets its own landing pad. `HandlerGraph.equivalentCatchHandlerAliases` accepts
such a child only when its catch-only prelude leads to value-only completion
instructions, that prefix converges with the enclosing handler, and the full
SSA continuation matches. Region discovery keeps both handlers so exceptional
and loop-exit ownership remain exact. Top-level post-processing then folds the
child into the canonical `tryCatch`, records its blocks in
`subsumedHandlerBlocks`, and removes the duplicate outgoing Phi action. Calls,
stores, throws, and branching handler prefixes therefore remain genuine nested
catches.

Composing the catch body has three tiers, tried in order and each rolling
the handler ledger back before the next:

1. the ordinary weak-SESE builder;
2. the **edge-aware bounded DAG**, which composes branches itself and
   delegates loops and nested ranges back to `regionAt`. This is what makes
   exceptional Phis usable: their mutable state is placed on entry to
   protected blocks, but the handler Phi cannot be removed unless the Region
   owns the handler joins that consume it;
3. `tryStructureCatchScopeForest` (`:945`), an exact composition for a catch
   body whose loops or nested ranges defeat both. Nested ranges are
   contracted as complete try/catch nodes; exceptional edges to an enclosing
   handler or finalizer are lexical boundaries owned by that outer Region,
   while normal edges leaving the bounded catch body are its ordinary
   completion and need no synthetic transfer.

Four further recognizers handle shapes that no generic rule can see:

- `tryStructureCatchExceptionLoop` (`:820`) — a normal loop whose body
  contains a catch that rejoins its latch. The dominator tree cannot classify
  this as a natural loop, because the landing pad looks like a second entry
  into the latch; the normal SCC proves the cyclic core, and the nested
  exception descriptor proves the apparent second entry is a lexical
  try/catch inside the body.
- `handlerRetryControl` (`:379`) / `demoteConditionalRetryDecision` — the
  `retryLoop` metadata of section 3, including the conditional trailer that
  retries on one branch and exits on the other.
- `structureProtectedIteratorGuardLoop` (`:2016`) — Hermes puts the
  zero-property guard before `GetNextPName`, and `for (… in …)` already
  expresses that zero-iteration branch. When the whole machine is protected,
  treating the guard as an ordinary branch prevents the exception Region from
  owning the loop and leaves its landing pad unhandled. The recognizer is
  deliberately exact: the recovered loop must name the guard as its
  preheader, both completion paths must agree, and guard plus loop must own
  the complete protected range.
- `routeNestedExceptionSideExitsInProtectedBody` /
  `routeNestedProtectedSideExit` (`:2535`) — a contracted inner exception
  Region can complete in two ways: continue with the enclosing protected
  body, or leave it at a shared terminal. A plain Sequence makes the second
  path fall into the first, so the original edge is kept at its lexical
  source (which is where its Phi action must be emitted) and a label is
  broken around the remainder of the protected body.

Nested catch descriptors are intersected with the bounded scope that requested
them. Without that boundary, a handler inside a loop can claim the loop's
cyclic continuation and leave the enclosing switch unowned. A protected
zero-trip guard is normalized similarly: when one arm exits through a copied
finalizer and the other continues with the protected suffix, the suffix is
nested in the live arm before finalizer-copy stripping. The resulting `if`
contains no bare `break` outside its loop.

`contractibleCatchRanges` (`structureRegion.ts:589`) exposes the same builder
to the bounded forest: it picks the root descriptors, drops any range a
`finally` already owns, and hands back an `exceptionAt` that builds one
complete try/catch Region per protected entry.

## 6. The bounded control forest

`tryStructureBoundedControlForest` (`structure/loopForest.ts:181`) is the
last resort, and it is structurally different from everything above. Rather
than find a nesting, it **contracts and linearizes**:

1. every top-level natural loop, recovered compare-chain switch, and
   protected range is collapsed into one opaque skeleton node owning all of
   its blocks;
2. the skeleton is topologically ordered;
3. every forward edge that does not fall through to the next node becomes a
   labelled break (`forwardEdgeLabels`, `structure/loopForest.ts:1178`),
   nesting one level per edge.

It has three entry points, which differ only in what they will accept:

| Entry point                                      | Accepts                                                                                                                                                                                                                                             |
| ------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `tryStructureBoundedLoopForest` (`:113`)         | Two or more top-level loop roots, unrestricted scope only. Declines whenever `allowed` is set: a bounded arm may have intentional edges to its enclosing join, and without an explicit scope the forest would own a whole reachable function suffix |
| `tryStructureBoundedContinuationForest` (`:137`) | Any whole CFG, including a fully acyclic one, plus contractible exceptions and recovered switches                                                                                                                                                   |
| `tryStructureBoundedScopeForest` (`:161`)        | One bounded residual subgraph — the remainder of a loop body no branch builder recognized — with the caller supplying the completions for edges leaving the scope                                                                                   |

Contraction is what makes it sound for protected code. Exceptional edges
make every normal-graph answer wrong for protected code, so the skeleton may
only run once each protected range is one node and its edges are internal to
it. That is now buildable rather than merely refused: the continuation and
scope entry points accept `contractibleExceptions`, and each protected entry is
contracted into a complete try/catch Region. What remains absolute is the check
that follows — every exceptional edge between reachable blocks must have the
same owner at both ends, or the contraction has hidden nothing and the attempt
declines with `unowned exceptional edge`. An entry point given protected
entries but no builder still declines outright.

Linearization is also no longer unconditional. `composeNodes` first tries to
split an entry branch at a proven common postdominating node, making the two
disjoint arms an If Region and the shared node the following Sequence trailer.
Besides reading better, that is the ownership distinction Phi-bearing value
joins need: the trailer is caller-side control, not a value returned by a
synthetic function. The labelled order is what it falls back to.

It refuses aggressively — overlapping ownership, a secondary entry into a
contracted loop, switch, or exception node, an external edge into a trailer it
owns, a contracted node with diverging exit targets, a cyclic contracted
skeleton, more than `MAX_LOOP_FOREST_NODES` nodes, or any
`hasPrestructuredControl(cfg)`.

It trades nesting depth for exactness and **records no miss**: the
structurer counts such a function fully structured. `controlForestLabels`
counts the labels for reporting only. The comment is explicit that it is
"reported, never consulted", because `misses` and `emitDiagnostics` drive
materialization and the legacy skip, so a count feeding either would change
output instead of describing it. Keep it that way.

## 7. Emission

`emitRegionToCode` (`emit/emitRegion.ts`) walks the Region tree to Babel
AST. Phi resolution happens here, in `buildPhiEmitState`
(`emit/emitRegion.ts:1644`), in three tiers.

1. **Self-assignments dropped.** Incoming values of the form `r = r` are
   filtered out. If nothing survives, the block is marked covered and the
   `%Phi` statement is simply skipped.
2. **Same-value collapse.** If every surviving incoming carries the same
   expression, one assignment is emitted at the join block
   (`sameValueAssignmentsByBlock`) instead of one per edge.
3. **Edge actions.** Otherwise the assignments are keyed by edge in
   `actionsByEdge` and _taken_ by whichever construct owns that edge:
   `takePhiActionsForEdge` (branch arms), `takePhiActionsForSwitchEntry`,
   `takePhiActionsForLoopEntry`, `takePhiActionsForLoopBackedges`,
   `takePhiActionsForFinallyEntry`, `takePhiActionsForRegionExits`, and
   `takePhiActionsBetweenRegions` for a sequence boundary that is itself an
   edge. `takeFinalizerActionsForBlock`,
   `takeExceptionalStateAssignmentsForBlock` and
   `takeSameValuePhiAssignmentsForBlock` drain the block-keyed maps alongside
   them.

Anything still unconsumed is declared as a single `let` at the top of the
function by `phiTargetDeclarations` (`emit/emitRegion.ts:1773`). Actions
whose source block _was_ emitted but which nobody claimed are reported by
`reportUnplacedPhis` (`emit/emitRegion.ts:5664`) as emit diagnostics — which
is what stops a broken emission being selected downstream.

Two classes of action are deliberately discarded rather than placed:

- Iterator and for-in loops discard their internal Phi actions
  (`discardIteratorInternalPhiActions`, `:1966`), because the recovered
  high-level syntax subsumes the machine registers those Phis were merging.
  `markIteratorBodyBreaks` and `iteratorNormalCompletionFlag` are the other
  half of that recovery: they keep an explicit body `break` distinguishable
  from natural exhaustion once both are one loop. Header exhaustion may itself
  be a terminal `return`/`throw`; the completion flag guards that terminal while
  leaving the body-break continuation after the loop.
- `discardEquivalentFoldedPredicatePhiActions` (`:1079`) drops the absorbed
  copies of a folded short-circuit predicate. Such a predicate represents
  several CFG edges to its shared arm with one JavaScript edge, and
  `shortCircuitBranch` only folds when every Phi sees the same SSA value on
  those edges — so the representative edge keeps the action and its equivalents
  go, instead of becoming duplicate assignments or lingering in the ledger.

`emitConditionalRetryExit` (`:949`) is the emitter half of the `retryLoop`
metadata: it lowers a conditional catch trailer into a backedge and a `break`,
placing each edge's Phi actions on the edge it belongs to.

### Conditional-value folding

Separate from the control-level path, an If Region carrying
`conditionalValue` is offered to `trySynthesizeConditionalPhis`
(`emit/emitRegion.ts:1134`), which folds the join into a single declaration —
`const x = test ? a : b`, or a short-circuit, chosen by
`buildConditionalValueExpression` — and then **deletes the target from
`declaredPhiTargets`**, so the join variable disappears entirely rather than
being declared and assigned.

It declines when:

- there are multiple targets and the test is not pure (evaluating it twice,
  or reordering around it, would not be sound);
- any operand references a pattern-bound name.

`localizeDeferredConditionalPhis` (`:1218`) is the weaker fallback for when the
fold is refused.

### Block scoping

`emitBlockScopedRegion` exists because `try`, `catch`, `finally` and a
recovered `for` body are all block scopes. A value the block computes and
the code after it reads has to be declared outside the block, or it is
emitted as a block-local `const` and read where nothing declares it. Every
such construct needs this; writing it out per construct is how `try` and
`finally` came to be missing it.

Before structuring, `cleanupLiftedBlocks` preserves a generated binding marked
`preserveAcrossBlocks`: its apparent lack of local references may hide a use in
another CFG block. Recursive materialization and completed lowered-generator
recovery have the opposite invariant — the whole structured tree is one block.
Their final cleanup may therefore ignore that stale marker for an actually
unreferenced binding, removing the binding while retaining an effectful
initializer as an expression statement.

## 8. Verdict, selection, materialization

`summarizeRecursiveCFG` (`recursiveSummary.ts:383`) computes a `misses` set:

`no-region`, `basic-branch-not-structured`,
`exception-handler-not-structured`, `finalizer-terminal-not-structured`,
`loops-not-structured`, `switches-not-structured`, `phis-not-lowered`,
`fallback-region`, `weak-sese-arm-not-structured`, and `diagnostic:<kind>`
for every diagnostic except unreachable blocks.

Note that `collectRegionMisses` (`recursiveSummary.ts:1306`) detects the last
two by **substring-matching the printed region text**. Pragmatic, but
text-coupled: changing `printRegion` output can silently change the verdict.

Three independent candidates are recorded:

| Candidate               | Source                                                      |
| ----------------------- | ----------------------------------------------------------- |
| `raw-region`            | Region emitted from the initial, unmutated CFG              |
| `post-reduction-region` | Region analysis re-run after the ordinary reducers converge |
| `reduced-fallback`      | The one-block AST the ordinary reducers produce             |

`reduced-fallback` is a _reference_ result, and now only that: the selection
path that could choose it, along with the AST semantic-feature comparison
that justified it, has been deleted (`CFG-TODO.md` package G) after
telemetry recorded zero selections. `recordReducedFallbackEmission`
(`lib/ir/function/mod.ts:3556`) still records it when reduction converges to
one block, so its presence in a report is evidence of nothing except that
reduction ran. `selectRecursiveCFGEmission` can only ever name `raw-region`
or `post-reduction-region`.

A post-reduction candidate is additionally rejected when
`iteratorEmissionRegresses` — it lost a high-level iterator loop _and_
reintroduced protocol calls relative to the already-selected program. That is a
strict pairwise comparison, not a heuristic preference.

`selectedEmission` names the chosen candidate.
`duplicatedSSABlockCounts` follows that selection, so it describes the candidate
that cleanup and materialization consume rather than whichever Region happened
to be analyzed first. Migration audits snapshot it in both `initial` and `final`
state. Candidates without a Region ownership tree report an empty map.

`tryMaterializeRecursiveCFGEmission` (`lib/ir/function/mod.ts:3876`)
replaces every block with it, but only after
`recursiveEmissionMaterializationRejection()` (`:3770`) returns null. That
gate now has two kinds of reason, and the difference matters:

**Correctness claims — absolute.**

- no Region emission, or incomplete CFG analysis;
- **unbound generated registers** — evidence that materialization lost a
  definition. Waived for native generators, whose resume values are modelled
  outside ordinary lexical bindings until generator cleanup has consumed the
  Region body;
- **generated registers with no write** — evidence that a definition or an
  edge-local assignment was dropped even when binding placement can still
  synthesize a lexical declaration;
- **any remaining `%Phi` call**.

**Quality claims — deferrable.**

- a raw switch intrinsic survives in the emission;
- destructuring protocol survives in the emission.

Those two exist to give the compatibility reducer first refusal, so they only
reject while it can still do better. `tryMaterializeRecursiveCFGEmission(true)`
is called once, at the very end of `runCFGReductionInner`, and passes
`lastResort`: by then every reduction phase has run, and refusing there would
leave the function unstructured. An unstructured root is not a lesser output —
composition takes only its entry block, so the rest of the program is silently
dropped. A complete emission carrying a raw intrinsic is strictly better than
that, and the intrinsic is what generated-output validation reports.

### The switch checkpoint

`checkpointCompleteRecursiveSwitchRegion` (`lib/ir/function/mod.ts:3628`) is
a mid-pipeline exit. When the initial Region reported
`switches-not-structured`, the function is small (≤16 blocks), and a raw
switch intrinsic is still present, each successful reduction pass re-runs
`structureCFG`; if the refreshed Region is complete, diagnostic-free and
free of raw switch intrinsics, it is retained as a post-reduction candidate.
Materializing runs stop the pass loop and install it immediately. Audit-only
and `materialize: false` runs keep the candidate in the summary but continue
the compatibility reducers so their reference output and telemetry remain
complete. The checkpoint is speculative: if final cleanup invalidates it, the
ordinary reducers resume rather than leaving a half-reduced CFG.

### Skipping legacy entirely

`legacyReductionIsRedundant` (`:3833`) skips the ordinary reducers when the
recursive result is provably clean. Materialization overwrites `blocks`, so
whatever legacy left there is discarded anyway.

The handler condition there is deliberately **not** a blanket exclusion. A
function whose handlers the structurer did not represent already reports
`exception-handler-not-structured` among its misses, and the miss check
declines it; refusing every handler-bearing function on top of that kept
legacy reduction alive for functions the recursive path had structured
completely — 167 of 260 in a 6,000-function sample.

The skip is sound only where nothing between the two consumes the reduced
state. The migration audit is such a consumer, and so is
`shouldRefreshRecursiveCFGSummaryAfterReduction`, which rebuilds the summary
from the reduced blocks and hands materialization a different program. The
guarded-Phi retry is not: its only product is `blocks`, which materialization
overwrites.

## 9. Retries and speculation

Recursive mode no longer reconstructs anything with `mode: 'legacy'`. What
remains is a small set of recursive-to-recursive retries and speculative
rewrites. Two of them are snapshot-restore-and-retry, and both preserve
`recursiveCFGSummary` across adoption so telemetry still describes the
recursive attempt rather than the adopted result; the other two are graph
rewrites re-analysed in place.

`CFG-TODO.md` has a standing complaint that these, plus `kind: 'fallback'`
Regions and conservative loop syntax helpers like `fallbackWhileTrue`, are all
conflated under the word "fallback". They are not the same thing.

### 9.1 Guarded-Phi retry

`lib/ir/function/mod.ts:2770`, adopted at `:2802`.

Eligible when the mode is recursive, `phiCount > 0`, and the function has at
most 64 blocks. The main run sets `func.guardedPhiMode = 'enabled'`, which
makes two ordinary reducers refuse merges that would strand a Phi:

- `linear.ts:705` — `reduceSequence` will not merge a block holding both a
  `%Phi` and a `%CreateClosure` whose Phi sources have more than one live
  owner;
- `predicates.ts:1774` — the branch reducer skips a successor that still
  contains a Phi when no lowering exists for it.

If the guarded run still leaves more than one block, the pre-reduction
snapshot is re-reduced with guarding _off_ and adopted if it reaches
strictly fewer blocks. Note that the comparison is on block count, not Phi
count. It is the last retry that adopts a separately reduced candidate, and
`CFG-TODO.md` package B keeps it deliberately until the wider Phi families it
covers are fixed and both corpora show zero semantic dependence on it.

### 9.2 Short-circuit collapse, and its rollback

`collapseShortCircuitsForRegions` (`lib/ir/function/mod.ts:2605`), judged in
`runCFGReduction` (`:2662`).

A short-circuit condition lifts to two blocks whose fallthrough arm branches
into the taken arm's entry, which no weak SESE can express, so the branch and
everything under it falls to a skeleton. Collapsing the chain gives the
structurer an ordinary two-way branch over a logical test. It runs _before_ the
first structuring attempt rather than as an incompleteness retry, because a
skeleton covers every block and therefore never reports as incomplete.

It is speculative: the collapse can fold away the block computing a condition's
value while the merged test still reads it, and that only surfaces after the
ordinary reducers have run. So `runCFGReduction` re-checks
`reducedBodyIsUnsound()` — a surviving `%Phi` or an unbound generated register
— and, if it fires, restores the pre-run snapshot and redoes the whole
reduction with the collapse suppressed. It is skipped up front for functions
that still contain destructuring protocol.

### 9.3 Leading-Phi normalization

`normalizeLeadingPhisForRegions` (`lib/ir/function/mod.ts:2578`) is retried
only when `recursiveRegionIncomplete()` — deliberately after the fact rather
than up front, because a function the structurer already represents must keep
its Phis exactly as lifted for the generator state-machine descriptors to work.

### 9.4 Destructuring protocol consumption

Two passes, at opposite ends of the same problem.

`reduceProtectedArrayDestructuring` runs to a fixpoint _before_ the first
analysis (section "Pipeline overview"). Then, after analysis, a structurally
complete Region whose emitted AST still contains destructuring or spread
protocol calls drives `reduceSequentialObjectDestructuring` and
`reduceSequentialArrayDestructuring` to a fixpoint and re-analyses
(`lib/ir/function/mod.ts:2741`). The ordering is the point: such a Region would
otherwise be rejected by the quality half of the materialization gate and
handed to compatibility reduction, which can regress an already complete
protected Region before cleanup ever gets its first opportunity.

### 9.5 What was removed

Three mechanisms this document previously described are gone:

- **Legacy Phi rescue.** Restored the snapshot, forced `mode: 'legacy'`, and
  adopted the result if it left strictly fewer unresolved Phis.
- **Destructuring legacy retry.** Re-reduced the _original_ CFG under legacy
  when the materialized output still contained raw protocol.
- **Reduced-finalizer fallback selection**, with
  `recursiveCFGEmissionMissesReducedFinalizerFeatures` and
  `syncRecursiveCFGEmissionFromReducedBlock`.

Their audit fields (`legacyPhiRescue`, `destructuringLegacyRescue`) are
retained, zeroed and marked `shadowOnly`, so existing reports keep parsing.
A consequence worth knowing: **`--cfg-migration-audit=strict` is now inert.**
Its only consumer was the legacy shadow's `LiftError`; nothing raises on it
today, and the CLI help text still describes the deleted behaviour.

### 9.6 Where Phis actually get resolved

Worth stating plainly, because the retry paths make it easy to assume
otherwise: in the normal case **no retry runs at all**. Phis are resolved by
the emitter, as edge actions (section 7). The retries exist only for functions
where that entitlement is incomplete — where some construct that should have
taken an edge action did not.

For a clean function they cannot fire, because materialization has already
proved no `%Phi` remains.

## 10. Compatibility telemetry

`compatibility.ts` is the answer to "how often does this function actually need
the escape hatches". It records, per path, attempts, selections, the entry
addresses involved and a deduplicated set of reasons:

| Path                                               | Recorded from                                                             |
| -------------------------------------------------- | ------------------------------------------------------------------------- |
| `whole-cfg-continuation-forest`                    | `structureCFG` replacing a primary Region with the exact forest           |
| `single-top-level-loop`                            | `appendSingleTopLevelLoop` composing a loop the ordinary owner missed     |
| `local-fallback-region`                            | A `fallback` constructed, and separately, one surviving in the final tree |
| `short-circuit-rollback`                           | `runCFGReduction` redoing a reduction with the collapse suppressed        |
| `guarded-phi-retry`                                | The retry of section 9.1                                                  |
| `destructuring-legacy-rescue`, `legacy-phi-rescue` | Retained path names, no longer emitted                                    |

The first three are recorded inside the structurer, into
`descriptors.compatibility`, and surface on the summary as
`compatibilityPaths`, tagged with the phase they came from (`raw-region`,
`reduction`, `post-reduction-region`). The rest are recorded by the reduction
driver through `recordCompatibilityPath` (`lib/ir/function/mod.ts:3234`), which
merges into the same list.

This is measurement, not control: **nothing reads these counters back**. The
descriptor field even says so ("opt-in-by-consumer counters; never consulted
for structuring decisions"). The migration work packages in `CFG-TODO.md` are
driven by these numbers, which is exactly why they must stay outside the
decision path.

The audit also carries a second shadow: `bindingPlacement`
(`recursiveSummary.ts:110`) records what unified binding placement _would_
do to the selected candidate — bindings moved, localized, unresolved
references, and any `divergences` from the incumbent repairs — while the
incumbent repairs stay authoritative. An empty divergence list is the flip
gate; `incumbentChanged` is recorded alongside it so "both agreed" can be
told apart from "neither had anything to do". See `BINDING-TODO.md` Phase 3.

## 11. Invariants worth preserving

- **Ownership is the invariant.** `sourceBlocks` makes every block claimable
  exactly once. Every composition site enforces it locally with a subset
  test; every new one must too.
- **Edges carry the leftovers.** Anything that cannot live in a block — Phi
  merges, finalizer copies, abrupt transfers — becomes a typed action on an
  edge, carried by a `DeferredExit` or a `LoopRegionExit` until some
  construct in the tree is entitled to take it.
- **The CFG is immutable.** The analysis cache has no invalidation because
  it does not need any. Do not introduce a mutation path.
- **Normalization is graph-only.** It may reshape the CFG or its metadata;
  it must not construct the final AST.
- **Descriptors are recognition, Regions are shape.** Prefer provenance from
  instruction, SSA, CFG, or handler-graph metadata over matching AST text.
- **Telemetry is reported, never consulted.** `controlForestLabels`, the
  compatibility paths, and the binding-placement shadow all describe output;
  a quality metric that feeds selection stops being a metric.
- **The memo's two preconditions are load-bearing.** Acyclic and
  handler-free, both, or the key is wrong.
- **Speculative structuring rolls back the handler ledger** — before it
  composes its replacement, not after.
- **A quality rejection is not a correctness rejection.** Deferring one is
  legitimate; deferring an unbound register or a surviving `%Phi` is not.

## 12. Debugging

Environment flags:

| Flag                                             | Effect                                                                                                                                                                                                              |
| ------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `ARES_RECURSIVE_CFG=1`                           | Select the recursive reducer via env rather than CLI                                                                                                                                                                |
| `ARES_RECURSIVE_CFG_STRICT=1`                    | Throw a `LiftError` on the first diagnostic                                                                                                                                                                         |
| `ARES_RECURSIVE_CFG_DEBUG=1`                     | Per-function block/SCC/loop/phi/switch/delegate/destructuring counts, normalization summary, the printed Region, and diagnostics                                                                                    |
| `ARES_DEBUG_REGION=1`                            | Print the stack when the descent exhausts the JavaScript call stack                                                                                                                                                 |
| `ARES_DEBUG_FOREST=<hex entry>`                  | Every decline reason of the bounded control forest for that entry, the loops and roots it found, and whether whole-CFG forest replacement fired. Set to any value, it also reports unplaceable exception-node exits |
| `ARES_DEBUG_PROTECTED=<hex handler>`             | Why the protected forest declined for that handler                                                                                                                                                                  |
| `ARES_DEBUG_RECURSIVE_EMIT_BLOCKS=<addrs>`       | Per-block emission trace: already-emitted blocks, skipped statements and ranges, with reasons. Comma-separated, `0x`-prefixed or decimal                                                                            |
| `ARES_DEBUG_ITERATOR=1`, `ARES_DEBUG_CONSUMED=1` | Iterator recovery and consumed-statement bookkeeping                                                                                                                                                                |

CLI:

```sh
# Structured JS from the recursive path
deno run --allow-read --allow-env src/ares.ts sample.hbc --cfg-reducer=recursive

# The Region IR itself, instead of JS
deno run --allow-read --allow-env src/ares.ts sample.hbc --cfg-recursive-ast

# The emitted Babel AST as JSON
deno run --allow-read --allow-env src/ares.ts sample.hbc --cfg-recursive-babel-ast

# Per-function emitted JS snippets
deno run --allow-read --allow-env src/ares.ts sample.hbc --cfg-recursive-js

# Both reducers, diffed; add --cfg-compare-recursive-js to also validate
# the recursive JS emission
deno run --allow-read --allow-env src/ares.ts sample.hbc --cfg-reducer=compare

# AST-free per-function migration report (expensive; never implicit)
deno run --allow-read --allow-env src/ares.ts bundle.hbc \
	--cfg-migration-audit >report.json 2>report.progress.log
```

Tasks:

```sh
deno task coverage:samples        # sample corpus, recursive reducer
deno task cfg:expect:samples      # registered Region/JS/output expectations
deno task cfg:compare:samples     # per-sample legacy/recursive comparison
deno task cfg:audit:samples       # compare and categorize against legacy
```

Working inward when a function comes out wrong:

1. `--cfg-recursive-ast` — is the Region tree the right shape?
2. If yes, the problem is in `emit/`. Check the emit diagnostics; an
   `unplaced edge phi action` names the exact edge nobody claimed, and
   `divergent loop breaks` names a loop whose exits the structurer could not
   give an ordered suffix. `ARES_DEBUG_RECURSIVE_EMIT_BLOCKS` then shows what
   happened to each statement of the blocks involved.
3. If no, find which ladder rule fired and why the one above it declined.
   `ARES_RECURSIVE_CFG_DEBUG=1` prints the Region and the diagnostics
   together; `ARES_DEBUG_FOREST` and `ARES_DEBUG_PROTECTED` print the decline
   reasons of the two builders that refuse most often.
4. For try/catch/finally, inspect `HandlerGraph` first, and keep
   `func.exceptions` as the source of handler-derived structure rather than
   reading raw `func._exceptionHandlers` in reducers.
