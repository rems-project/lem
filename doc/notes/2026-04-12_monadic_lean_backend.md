# Monadic lifting in the Lem-Lean backend

## Context

Lem's semantic model inherits OCaml's: types can be pure (`unit -> nat`) while implementations have hidden effects (mutable counters, global state). This was a safe assumption when Lem's backends were OCaml, Coq, HOL, and Isabelle — OCaml accepts the model natively, and the proof-assistant backends never execute code. Lean 4 is the first backend that is both pure-typed and executed, and the model breaks: Lean's compiler optimizes based on type-level purity, eliminating duplicated calls to "pure" functions that actually have side effects.

Earlier attempts to paper over this at the call-site level (`runEffectful`, `unsafeBaseIO`, `@[extern]`, thunks) all fail for the same root reason: any function whose type is `unit -> α` will be CSE'd by Lean regardless of implementation. The limitation is fundamental to Lean's design.

This note proposes that the Lem-Lean backend perform a monadic lifting of generated output to faithfully translate Lem's implicit-effect model into Lean's explicit-effect type system.

## The semantic argument

Lem's contract is not "all functions are pure." It's "types don't track effects, and the compiler shouldn't assume purity." Each backend handles this contract in a way compatible with its target:

- OCaml: matches natively — compiler doesn't assume purity, effects just work
- Coq/HOL/Isabelle: effects never matter — code isn't executed
- Lean: requires translation — effects must be explicit in types

The Lean backend is the only one where Lem's model needs active translation. This isn't a hack — it's the correct handling of a semantic mismatch. Other backends happen to get direct translation because their semantics align with Lem's. Lean's semantics don't align, so the backend must do real work.

Framed this way, monadifying Lean output is not "adding complexity to work around Lean" — it's "correctly translating Lem's OCaml-style effect model to Lean's IO/State effect model."

## What this means for each group

**Legacy Lem users (Group 1)**: No changes. Lem's source language, its type system, and all other backends are untouched. Their code, proofs, and OCaml output remain exactly as today.

**Lem-Lean backend (Group 2 — us)**: We take on the engineering work of monadic lifting. The Lean backend generates IO-monadic code for functions that transitively call effectful target_reps, and pure code for everything else. This is a significant backend project but contained to our responsibility.

**Cerberus Lean team**: Their `.lem` sources and target_rep declarations stay as they are today. Their Lean-side implementations of effectful functions become `IO α` / `BaseIO α` (which they largely are already, or would be with trivial changes). The generated Lean code correctly threads effects through, allowing execution to work.

## Design

### High-level strategy

1. **Effect analysis**: During backend processing, compute which functions transitively call effectful target_reps (marked with `declare {lean} effectful val`).
2. **Type lifting**: Functions in the effectful call-graph get their Lean return type lifted from `α` to `IO α`. Pure functions remain pure.
3. **Call-site rewriting**: Calls to lifted functions become monadic binds (`let x ← f ()` instead of `let x := f ()`). Calls from pure functions into effectful ones require explicit `unsafeIO` boundaries, which we generate.
4. **Effectful target_reps**: Declared via `declare {lean} effectful val foo`. Their Lean implementations return `IO α` (as they already do in Cerberus's native code).
5. **Top-level entry**: The generated Lean module exposes a `main : IO Unit` (or similar) that runs the effectful pipeline.

### Effect propagation

The effect analysis is a straightforward fixpoint over the call graph:

- Every function marked `declare {lean} effectful` is effectful.
- Any function that calls an effectful function (directly or transitively) is effectful.
- Functions that only call pure functions are pure.

This analysis runs once per compilation; results are stored in a side table and consulted during expression rendering.

### Lifting rules

Given the effect analysis:

- **Pure function calling pure function**: generate as today (pure `let`).
- **Effectful function calling effectful function**: generate with monadic bind (`let x ← f args`).
- **Effectful function calling pure function**: generate `let x := f args` (pure values lift freely into IO).
- **Pure function calling effectful function**: **forbidden** by the analysis. If a pure function reaches an effectful call, it becomes effectful. This cascades up the call graph until we hit a function declared pure by the user, which is an error.

### The `effectful` annotation

The existing `declare {lean} effectful val foo` annotation marks a target_rep as having side effects. The backend uses this as the seed for the effect analysis. No new Lem syntax needed beyond what we already have.

### Generated code examples

**Currently (CSE'd, broken)**:
```lean
def desugar_decl (d : declaration) : ail_decl :=
  let n := freshIntIO ()   -- CSE'd: all calls return same value
  ...
```

**After monadic lifting**:
```lean
def desugar_decl (d : declaration) : IO ail_decl := do
  let n ← freshIntIO ()    -- correctly sequenced
  ...
  pure result
```

### `unsafeIO` boundaries

For pure contexts that need to invoke effectful computation (e.g., embedded expression positions), the backend emits `unsafeIO` wrappers. These are rare — almost all call sites fall under the lifting rules above.

## Consequences

### What changes

- The Lean backend does substantial new work: effect analysis + monadic code generation. Estimated: 4–6 weeks of focused work.
- Generated Lean code for effectful functions looks different — uses `do` notation, returns `IO α`. More verbose than today.
- Error messages: users who add `effectful` to a function that calls it from a `declare pure` context get a clear error from the analysis.

### What doesn't change

- Lem's source language, type system, parser, and AST.
- All non-Lean backends (OCaml, Coq, HOL, Isabelle, LaTeX, HTML). Byte-for-byte identical output.
- Cerberus's shared `.lem` sources. Group 1's code is untouched.
- Cerberus's existing proofs (Coq/HOL) — no changes needed.

### What Cerberus needs to do

- Continue declaring effectful functions with `declare {lean} effectful val`.
- Ensure Lean target_rep implementations return `IO α` (they already do for `fresh_int`, `tagDefs`, etc.).
- Top-level entry point wraps the pipeline in `IO`. This is already how Lean programs work.

### Risks

1. **Lean idiom mismatches**: `IO` might be too strong for some effects (`State` would be more appropriate for counter-like things). We may want `State`/`StateM` for some functions in the future. Starting with `IO` is simplest and can be refined.

2. **Pure cascade**: A function marked `effectful` forces everything that calls it to be effectful. For Cerberus this is probably desugar/typecheck/translate — most of the pipeline. That's correct but worth knowing.

3. **Performance**: Monadic code has allocation overhead. For a research tool this is almost certainly fine, but worth measuring.

4. **Complexity**: Monadic backend generation is the biggest backend feature we'd add. We should be confident before committing.

## Sequencing

Suggested order:

1. **Prototype branch** (1 week): small throwaway branch implementing the analysis + code generation for a minimal test case. Goal: verify the approach compiles, runs, and actually prevents CSE.
2. **Cerberus sign-off**: share the prototype and this note with the Cerberus team. Confirm it meets their needs.
3. **Real branch** (4–6 weeks): full implementation with tests, documentation, all existing Lem-Lean tests still passing.
4. **Merge**: after the branch is clean and Cerberus has validated it on their full pipeline.

If the prototype reveals showstoppers, we abandon and go back to the drawing board with minimal sunk cost.

## Alternatives considered

- **Path A: Cerberus refactors to state monad in shared Lem source.** Correct but requires Group 1 cooperation. Not politically feasible.
- **Path C: Lean for proofs only.** Doesn't achieve Cerberus Lean team's goal of running Cerberus in Lean.
- **Various call-site tricks** (`unsafeBaseIO`, `@[extern]`, thunks): all fail to CSE at one level or another. Exhausted.

## Decision needed

Approve this direction and proceed to prototype? Or explore alternatives further?
