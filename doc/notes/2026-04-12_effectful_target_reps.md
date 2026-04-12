# Effectful target_rep functions

## Problem

Lem's type system is pure: all functions have types like `unit → nat` with no effect tracking. This is intentional — the same Lem definitions target OCaml, Coq, HOL, Isabelle, and Lean. Target-specific implementations are provided via `declare target_rep function`, which substitutes a target-native function at code generation time.

Some target_rep functions are secretly effectful: mutable counters (`fresh_int`), mutable global state (`tagDefs`), debug levels, etc. In OCaml this is fine — the compiler doesn't optimize based on purity. In Coq/HOL the functions are never executed — they're axiomatized for proofs.

Lean 4 is the first backend that is BOTH pure (type system) AND compiled to native executables. The Lean compiler aggressively CSEs (common subexpression eliminates) calls to pure functions. When `fresh_int : Unit → Nat` is marked pure (by virtue of its type), all calls `fresh_int ()` in the same scope are replaced with a single call. This is correct for pure functions but breaks effectful ones: every symbol gets the same ID, the pipeline fails.

## The fundamental tension

Lem occupies a specific design point: definitions are written ONCE and target MANY languages. The type system is the intersection of what all targets can express. Effects are NOT in this intersection:

- OCaml: effects everywhere, no annotation needed
- Coq/HOL/Isabelle: purely logical, effects are irrelevant
- Lean: pure type system but compiled to run — effects matter

Adding effect tracking to Lem's core type system would be a fundamental change that benefits only compiled-and-executed targets (currently just Lean, possibly Rocq in the future).

## Design space

### Option 1: Principled — thread effects through monads

Change effectful functions to explicitly monadic:

```lem
val fresh_int : unit -> IO nat  (* or: unit -> stateM nat *)
```

The Lem type captures the effect. All backends handle it:
- Lean: natural `IO` monad, no CSE issue
- OCaml: `IO` maps to identity monad or direct execution
- Coq/HOL: `IO` is axiomatized

**Pros**: Correct by construction. The type tells the truth.
**Cons**: Extremely invasive. Changes the type of every effectful function. Propagates monadic context through all callers. For Cerberus, `fresh_int` is called in hundreds of pure contexts — they'd all need monadic lifting. This is a project-level refactor, not a backend fix.

**Assessment**: The right long-term architecture, but not practical as a near-term fix. Worth considering for future Lem evolution.

### Option 2: Target-level — IO-returning target_reps

The target_rep points to a function returning `IO`:

```lem
val fresh_int : unit -> nat
declare lean target_rep function fresh_int = `CerberusFresh.freshIntIO`
(* where freshIntIO : Unit → IO Nat *)
```

The Lean backend detects the type mismatch (`nat` vs `IO Nat`) and wraps each call site in `unsafeBaseIO`:

```lean
let n := unsafeBaseIO (CerberusFresh.freshIntIO ())
```

**Pros**: No Lem language changes. The target_rep already substitutes functions — this just changes what it substitutes.
**Cons**: `unsafeBaseIO` at every call site is ugly. The backend needs to detect IO-returning target_reps. The generated code is not idiomatic Lean (idiomatic code would run in IO monad, not use unsafeBaseIO).

**Assessment**: Works but smells bad. Scattering `unsafeBaseIO` through generated code is a code smell that indicates the architecture is fighting the language.

### Option 3: Annotation — mark target_reps as effectful

Add an annotation to declare that a target_rep is effectful:

```lem
val fresh_int : unit -> nat
declare lean target_rep function fresh_int = `CerberusFresh.freshIntIO` [effectful]
```

The backend knows to generate `unsafeBaseIO` wrapping at call sites.

**Pros**: Explicit. The annotation documents the intent. Could be used by future backends (Rocq executable extraction, etc.).
**Cons**: Still scatters `unsafeBaseIO` through generated code. The annotation is a new concept in Lem's declaration syntax.

**Assessment**: Cleaner than Option 2 (explicit vs implicit detection), same runtime behavior.

### Option 4: Backend wrapper — make the Lean pipeline monadic

Instead of wrapping individual calls, make the ENTIRE generated Lean pipeline run in `IO` monad. The Lean backend generates `do` notation and `←` for all let bindings. Effectful target_reps return `IO` values; pure functions are lifted automatically.

```lean
-- Instead of:
let n := fresh_int ()
let m := fresh_int ()

-- Generate:
do
  let n ← fresh_int ()
  let m ← fresh_int ()
```

**Pros**: Idiomatic Lean. No `unsafeBaseIO`. Effects are explicit. The compiler handles sequencing correctly.
**Cons**: VERY invasive backend change — all generated code becomes monadic. Performance implications (IO overhead). Only needed for files that call effectful functions, but hard to know statically which files those are.

**Assessment**: The "right" Lean answer but enormous implementation effort for the backend.

### Option 5: Cerberus-side — wrap the entry point in IO

The Cerberus team wraps their top-level pipeline in IO monad. Effectful functions (`fresh_int`, `tagDefs`, etc.) return `IO` values. The generated Lem code remains pure, but the Cerberus hand-written glue code manages the IO boundary.

```lean
-- Hand-written pipeline runner:
def runPipeline (cabsJson : String) : IO ExitCode := do
  let fresh_counter ← IO.mkRef 0
  let tag_defs ← IO.mkRef {}
  -- Run the pure Lem pipeline with IO-backed implementations
  ...
```

The key: effectful functions are implemented as closures over IO.Refs, and the pipeline is executed within IO. The generated Lem code calls them as pure functions, but the Lean runtime ensures sequencing because the IO monad forces it.

**Pros**: No Lem changes at all. Idiomatic Lean. Effects are properly managed.
**Cons**: The generated Lem code still calls `fresh_int ()` as a pure function — Lean may still CSE it unless the call goes through IO. This only works if the effectful calls are inside the IO runner's scope.

**Assessment**: Partially works but doesn't solve the CSE problem within pure generated code.

## Analysis

The core question: **where should the IO boundary live?**

- **Option 1** (principled): IO boundary is in Lem's type system. Correct but impractical.
- **Options 2-3** (pragmatic): IO boundary is at individual call sites (`unsafeBaseIO`). Works but ugly.
- **Option 4** (idiomatic): IO boundary is the entire generated module. Correct but enormous effort.
- **Option 5** (Cerberus-side): IO boundary is in hand-written glue. Doesn't fully solve CSE.

The idiomatic Lean approach (Option 4) is the "right" answer — but it's essentially asking the Lean backend to generate monadic code, which changes the character of the generated output significantly. Lem generates pure functional code; making it monadic is a fundamental shift.

## Recommendation

**Near-term: Option 3** (`[effectful]` annotation on target_reps). This is:
- Minimal: a small annotation, not a type system change
- Explicit: documents which functions are effectful
- General: useful for any backend that needs effect information
- Pragmatic: `unsafeBaseIO` isn't pretty but it works

The annotation is a property of the target_rep, not the function itself. The Lem function remains `unit → nat`. The annotation says "the implementation behind this target_rep has side effects, so the backend should prevent purity-based optimizations."

For Lean, the backend generates:
```lean
-- call site: 
let n := unsafeBaseIO (CerberusFresh.freshIntIO ())
```

Where `CerberusFresh.freshIntIO : Unit → BaseIO Nat` is an extern C function that correctly returns through the IO result protocol.

**Long-term: Option 1** (monadic types in Lem). If Cerberus (or another large project) moves to an IO-based architecture, Lem should support `IO`/effect types natively. This is a separate, larger project.

## Impact on Lem's design

The `[effectful]` annotation is consistent with Lem's existing approach:
- `target_rep` already allows target-specific implementation substitution
- `[effectful]` adds metadata to the substitution, not to the type
- Lem's type system stays pure — the effect is a property of the TARGET implementation
- Other backends can use the annotation: HOL could emit a warning, Coq could generate `IO` wrapping for executable extraction

The annotation does NOT break Lem's purity model. It says: "when compiling for this target, the substituted function has side effects, so take appropriate measures." This is pragmatic, like target_reps themselves.

## Open questions

1. **Syntax**: `[effectful]` on the target_rep line, or a separate declaration like `declare {lean} effectful function fresh_int`?

2. **Lean wrapping**: `unsafeBaseIO` at each call site, or a single wrapper function in LemLib that encapsulates the pattern?

3. **Granularity**: Per-function or per-module? If most functions in a module are effectful, a module-level annotation would be cleaner.

4. **Interaction with `do` notation**: Lem supports `do` notation for monads. If the effectful call is already inside a monadic bind, should the backend generate `←` instead of `unsafeBaseIO`?
