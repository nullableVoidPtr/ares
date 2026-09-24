# AGENTS.md

Guidance for coding agents working in this repository.

## Project Shape

Ares is a Deno/TypeScript Hermes bytecode decompiler. The main pipeline is:

- `lib/hbc/`: Hermes bytecode disassembly and versioned instruction metadata.
  - `lib/hbc/data/`: version-specific metadata — `stackFrameLayout.ts` (SH frame
    offsets), `VersionInfo.ts`, and `versions/` (per-version instruction tables,
    `InstructionNormalisationMap`, and `legacyOperands`).
  - `lib/hbc/disassembly/`: `instruction.ts` (instruction interfaces and
    `createInstruction`), `mod.ts` (`structureInstructions` / CFG edge emitter).
- `lib/ssa.ts` and `lib/utils/liveness.ts`: SSA/liveness support.
- `lib/ir/ast/`: instruction-to-AST lifting and local AST helpers.
- `lib/ir/function/`: function-level IR, CFG reduction, exception/finally handling,
  lowered generator handling, and post-lift cleanup.
  - `lib/ir/function/cfg/`: CFG reducers (`mod.ts`), iterator/for-in pattern
    recognition (`iterator.ts`), and switch lowering (`switch.ts`).
  - `lib/ir/function/except/`: `HandlerGraph` — try/catch/finally region analysis.
  - `lib/ir/function/finalizer.ts`: finally-copy stripping and `comparableAst`.
  - `lib/ir/function/loweredGenerator.ts`: lowered generator state-machine synthesis.
- `lib/coldstore/`: LMDB-backed on-disk store for `--parallel-lift`. Holds the
  per-function disassembly, the whole-file plans derived from it, the lifted IR
  snapshots and the composed Metro fragments, so no worker rebuilds the
  `HBCFile` (which costs ~2.5GB of RSS per copy on a large bundle) and no
  snapshot crosses a `postMessage`. `codec.ts` carries the two values msgpackr
  cannot: the `HermesEmpty` symbol and negative zero.
- `lib/parser/ksy/`: Kaitai schema for Hermes bytecode.
- `lib/parser/wasm/`: generated Kaitai C++ plus Embind/WASM parser wrapper.
- `samples/`: sample `.hbc` corpus.
  - `samples/v95/` and `samples/v99/`: versioned `.hbc` test corpus. Most samples
    have a matching counterpart in both directories.
  - `samples/src/`: the JavaScript sources the samples were compiled from.

## Worktree Rules

- The worktree is often dirty. Do not revert or overwrite changes you did not make.
- Prefer small, targeted edits. This codebase has many intertwined reducers; broad rewrites need broad sample validation.
- Use `rg`/`rg --files` for searching.
- Use `apply_patch` for manual file edits.
- Keep generated parser changes deliberate. If the Kaitai schema or WASM bridge changes, rebuild the parser and expect generated files under `lib/parser/wasm/build/` to change.

## Formatting And Style

- Deno formatting is configured in `deno.json`: tabs, `lineWidth` 80, single quotes for formatted `lib/` files.
- TypeScript is strict. Keep types explicit where they clarify decompiler state or instruction shapes.
- Avoid AST-only semantic workarounds when the problem belongs in disassembly, SSA, lifted IR, CFG structuring, handler graph analysis, or lowered generator synthesis.
- Prefer provenance from instruction/SSA/CFG metadata over matching test-only strings such as `console.log("finally")`.
- Peephole optimizations should be narrow and mechanically justified. For example, method-call rewrites should preserve receiver identity.

## Common Commands

Type-check:

```sh
deno check testharness.ts
```

Decompile one sample:

```sh
deno run --allow-read --allow-env testharness.ts samples/v95/generator.hbc
```

Debug a single sample (faster than testharness, streams errors):

```sh
deno run --allow-read --allow-env dbg_test.ts samples/v99/generator.hbc
```

Dump raw bytecode basic blocks before SSA:

```sh
deno run --allow-read --allow-env tools/dump_blocks.ts samples/v96/tryCatch.test.hbc 2
```

Dump lifted SSA blocks before function-level CFG reduction:

```sh
deno run --allow-read --allow-env tools/dump_ssa.ts samples/v96/tryCatch.test.hbc 2
```

Dump reduced IR blocks after `IRFunction` construction:

```sh
deno run --allow-read --allow-env tools/dump_ir.ts samples/v96/tryCatch.test.hbc 2
```

Use these when CFG reduction or function inlining leaves extra blocks. The optional
function id defaults to `0`. `dump_blocks.ts` shows instruction addresses and raw
successors, `dump_ssa.ts` shows per-block AST immediately after SSA lifting, and
`dump_ir.ts` shows the remaining `IRFunction` blocks after reducers run.

With a timeout to catch hangs:

```sh
timeout 20 deno run --allow-read --allow-env dbg_test.ts samples/v95/main.hbc 2>&1 | head -40
```

`--parallel-lift` needs `--allow-ffi` for the LMDB native addon:

```sh
deno run --allow-read --allow-env --allow-write --allow-ffi src/ares.ts bundle.hbc --parallel-lift
```

Add `--spill-reuse` to keep the on-disk store and skip lifting on a re-run of
the same bundle with the same options; `--spill-dir` chooses where it lives
(default `$XDG_CACHE_HOME/ares/spill`).

Run the full sample corpus:

```sh
deno task coverage:samples
```

Coverage reports:

```sh
deno task coverage:samples:report
deno task coverage:samples:detailed
```

The coverage command commonly emits Embind leaked-instance warnings from parser lifecycle cleanup. Treat them as non-fatal unless the command exits nonzero.

External Hermes disassembler used for bytecode inspection:

```sh
~/ctf/sk8-2025/rev/the-winged-thong-of-hermes/hermes-dec/hbc_disassembler.py ./samples/v95/generator.hbc
```

## Parser / WASM Notes

When editing `lib/parser/ksy/hermes_bytecode.ksy` or `lib/parser/wasm/main.cpp`, rebuild with:

```sh
cmake --build lib/parser/wasm/build
```

Do not hard-code function header sizes if a Kaitai sequence/instance expression can derive the layout. Hermes versions differ, especially around function headers, literal buffers, object shapes, and aliases.

Keep version-delta logic consistent: legacy operands/formats belong to older versions, and current instruction metadata should describe the latest canonical form.

## Version Notes (v97+)

- Stack frame layout gains `SHLocals` at slot -4, shifting all subsequent named
  slots (ArgCount, NewTarget, CalleeClosureOrCB, ThisArg, FirstArg) down by one.
  See `lib/hbc/data/stackFrameLayout.ts`.
- The function-header `envSize` field is removed. Environment size is now expressed
  via the `CreateFunctionEnvironment [Reg8, UInt32]` instruction emitted at function
  entry. `CreateTopLevelEnvironment` is the module-scope variant.
- Instruction renames in v97+: old `CreateEnvironment` →
  `CreateFunctionEnvironment`; old `GetEnvironment` → `GetParentEnvironment`. The
  v97+ `CreateEnvironment` and `GetEnvironment` mnemonics are _new_ 3-operand forms
  with different semantics — handle via `legacyOperands`, not aliasing.
- `AddS` is a distinct instruction (not an alias for `Add`) — give it its own
  interface in `instruction.ts` rather than adding it to `InstructionNormalisationMap`.

## Decompiler Debugging Notes

- For instruction support, update in this order: (1) `instruction.ts` — add the
  interface and `createInstruction` case; (2) `mod.ts` (structureInstructions) —
  add to the skip-first-pass set and/or CFG edge emitter if the instruction is a
  branch; (3) `liveness.ts` — add use/def entries (immediate operands like numeric
  indices are not registers and must be excluded); (4) `lift.ts` — add the AST
  emission case. Use `InstructionNormalisationMap` only for true opcode aliases
  (same semantics, different encoding); give genuinely new instructions their own
  interface even when the lifting logic is identical.
- For try/catch/finally issues, inspect `HandlerGraph` first. Keep `func.exceptions` as the source of handler-derived structure rather than reading raw `func._exceptionHandlers` in reducers.
- For finally deduplication, prefer SSA/CFG-level analysis over AST text matching. Account for copied finalizer bodies, catch trailers, return-override finalizers, and lowered generator state machines.
- For finally-copy stripping, `comparableAst` normalises `%getFunctionById(n)` calls
  by ignoring the function ID so structurally identical closures with different IDs
  compare equal. When adding new call-like intrinsics, extend `comparableAst`
  accordingly.
- For `HandlerGraph` recognition of isolated finally handlers (handlers that throw
  and have no catch children), the `#dominatorTree` must be seeded with all handler
  records before iteration — otherwise isolated entries are skipped.
- For lowered generators, distinguish wrapper generator functions from the lowered body. V95 uses `StartGenerator`/`SaveGenerator` style bodies; v97+ may use the newer lowered state machine. Validate both versions when changing generator handling.
- For loop structuring, the reducer runs `reduceNaturalLoop` after all simpler
  reducers stall. Back-edge detection uses immediate dominators; `collapseNaturalLoop`
  inserts a synthetic-continue block, reduces the body DAG in an inner loop, then
  wraps in `while(true)` (all-terminal exits) or `while(cond)` (one non-terminal
  exit). Do not reintroduce `reducePrimitiveSelfLoop` or `reduce2BlockLoop`; they
  are subsumed.
- For global/member call cleanup, preserve receiver semantics. Rewriting `.call` is only safe when the receiver relationship is proven.

## Validation Expectations

For narrow changes, run at least:

```sh
deno check src/ares.ts
deno run ares <focused-sample>
```

For parser, instruction, liveness, SSA, CFG, exception, generator, or broad AST cleanup changes, also run:

```sh
deno task coverage:samples
```

When reporting results, mention any command that could not be run and why.
