# Lean Backend — Open Issues

Updated: 2026-03-09

## FIXED

- **Generated library compiles**: `make lean-libs && lake build` succeeds. Fixed auxiliary file cleanup, namespace qualification, bridge instances.
- **Machine_word.lean compiles**: Fixed class method implicit resolution and standalone BEq instances.
- **Termination annotations respected**: `declare termination_argument = automatic` → `def` instead of `partial def`. Multi-discriminant match decomposes tuple scrutinees.
- **ppcmem-model: 10/10 files compile** (43 Lake jobs): Fixed cross-module name collision, record literal type inference, `setChoose` target rep, propositional equality in indreln.
- **cpp example compiles** (34 Lake jobs): `examples/cpp/Cmm.lean` (~1930 lines).
- **String.lean deprecation**: `String.mk` → `String.ofList`.
- **Dynamic library namespace list**: Detected from module environment, no hardcoded list.
- **deriving BEq, Ord**: Simple non-mutual types use `deriving` instead of sorry stubs.
- **Heterogeneous mutual universe**: All types in heterogeneous mutual blocks emit `Type 1`.
- **Propositional equality in indreln**: Both `Infix` and `App` AST paths convert `==`→`=` and `!=`→`≠` when `lean_prop_equality` is set. Covers direct `=`/`<>` syntax and Lem's `<>` decomposition to `not(isEqual x y)`. Regression tests use `(nat -> nat)` type (no BEq) to ensure correctness.
- **10 library functions: `partial def` → `def`**: Added `{lean}` termination annotations for `map_tr`, `count_map`, `splitAtAcc`, `mapMaybe`, `mapiAux`, `catMaybes`, `init`, `stringFromListAux`, `concat`, `integerOfStringHelper`. All structurally recursive on lists.
- **3 more: `partial def` → total via LemLib target reps**: `stringFromNatHelper`, `stringFromNaturalHelper` (n/10 division with `termination_by n`), `leastFixedPoint` (bounded countdown with `termination_by bound`). Total implementations in `LemLib.lean`, target reps in `.lem` files.
- **2 LemLib.lean partial defs fixed**: `boolListFromNatural` (n/2 division), `bitSeqBinopAux` (dual-list recursion). Both now total with termination proofs.
- **String comparison fixed**: `stringCompare` always returned `EQ` (broken default in `string_extra.lem`). Added `let inline {lean} stringCompare = defaultCompare`. All string ordering functions (`stringLess`, `stringLessEq`, etc.) and the `Ord0 String` instance now work correctly.
- **Unsupported numeric types panic instead of silently wrong**: `rational`, `real`, `float64`, `float32` now map to distinct opaque types (`LemRational`, `LemReal`, `LemFloat64`, `LemFloat32`) instead of `Int`. All operations panic at runtime with clear error messages. Previously `rationalFromFrac 1 3 = 0` (integer division); now panics. Reduces duplicate `Int` typeclass instances (partial fix for #5).
- **`int32`/`int64` now distinct types**: `LemInt32` and `LemInt64` are newtype wrappers around `Int` (same semantics as Coq's `Z` mapping, but distinct types). All arithmetic, comparison, conversion, and bitwise operations forward through the wrapper. Eliminates duplicate typeclass instances with `int`/`integer` (partial fix for #5). ppcmem `bitwiseCompatibility.lem` shift target reps updated (`Int.toNat` → `lemInt32ToNat`).
- **Machine word operations implemented**: `mword 'a` → `BitVec (@Size.size 'a _)` via TYR_subst. All 36 operations have Lean target reps mapping to LemLib BitVec wrappers. Compiler propagates [Size a] constraints from TYR_subst into function/instance signatures. 57 runtime-verified assertions (using Lem `assert` → `#eval` with throw-on-failure). Tested: LemLib, backend tests, comprehensive (32 tests), ppcmem-model, cpp example — all pass.
- **32 comprehensive tests, 288+ assertions**: All passing (57 new mword assertions are runtime-verified via `#eval`).

## Remaining Issues

### ~~1. Machine word operations: 942 `sorry` stubs~~ (Fixed — mword → BitVec)

All 36 mword operations now have real implementations via `BitVec`. The remaining 939 active sorry stubs are `Inhabited`/`BEq`/`Ord` instances on 312 phantom types (`ty1`..`ty4096`) and `itself`. These types are zero-constructor inductives that exist only to carry a width via `Size` — they are never instantiated as values. The sorry stubs are harmless but noisy (942 compiler warnings).

Possible cleanup: Have the backend emit `deriving Inhabited, BEq, Ord` for zero-constructor inductives, or suppress instance generation for phantom types that have `TYR_subst` on their containing type.

### ~~2. Numeric type instances: 27 `sorry` in Num.lean, 3 in Map.lean~~ (Non-issue)

These 30 sorry stubs are ALL inside `/- ... -/` block comments. The target rep mechanism already comments out the entire type definition block (inductive + instances) when a type has a Lean target rep. No active sorry, no compilation impact. Nothing to fix.

### ~~3. Floating-point types map to `Int` (semantically wrong)~~ (Fixed — panic on use)

`rational` → `LemRational`, `real` → `LemReal`, `float64` → `LemFloat64`, `float32` → `LemFloat32`. These are now distinct opaque types (defined in LemLib.lean) that panic on any operation. Previously they silently mapped to `Int`, producing wrong results (e.g., `rationalFromFrac 1 3 = 0` via integer division). All arithmetic instances, comparison functions, and conversion functions panic with clear error messages. For proper support: rational needs Mathlib's `Rat`, real needs Mathlib's `Real`, float64/float32 need IEEE 754 floats.

### ~~4. `int32`/`int64` collapse to `Int` (no overflow semantics)~~ (Fixed — distinct newtype wrappers)

`int32` → `LemInt32`, `int64` → `LemInt64`. These are `structure` wrappers around `Int` with forwarding instances for all arithmetic, comparison, and conversion operations. Same semantics as Coq's mapping to `Z` (arbitrary precision, no overflow), but now distinct types that don't collide with `int`/`integer`. Bitwise operations (`int32Lnot`, `int32Lor`, etc.) updated to use `LemInt32`/`LemInt64`. For proper overflow semantics: map to `BitVec 32` / `BitVec 64` (would require Mathlib dependency).

### ~~5. Duplicate typeclass instances in Machine_word.lean~~ (Resolved)

The mword→BitVec mapping means `mword ty8` resolves to `BitVec 8`, which gets its instances from Lean stdlib — not from the generated code. The remaining `int`/`integer` duplication is inherent (both map to `Int` in all backends, including Coq). No action needed.

### 6. 2 genuinely `partial def` functions in generated library

- List_extra.lean: `unfoldr` (depends on user-supplied termination condition)
- Set_extra.lean: `leastFixedPointUnbounded` (no bound — iterates until fixpoint by design)

These are correctly `partial` — no fix needed. All other previously-partial functions are now total via termination annotations or LemLib target reps.

Additionally, `LemLib.lean` (hand-written runtime) has 2 partial defs: `natSqrtAux` (Newton's method) and `set_tc` (transitive closure iteration) — both genuinely partial.

### ~~7. Audit ALL termination annotations on the branch~~ (Audited — no issues)

**Our additions**: All 10 `{lean}` scoped — affect only the Lean backend. Verified by `git diff` against branch base.

**Pre-existing unscoped annotations** (from upstream): ~35 in list.lem, list_extra.lem, num.lem, word.lem. These are intentionally universal — `try_termination_proof` in `backend.ml` uses them for ALL backends (Coq: `fun` vs `function (sequential)`; HOL: `Define` vs `Hol_defn`; Isabelle: `termination by lexicographic_order`; Lean: `def` vs `partial def`). They've been in the codebase for years and work correctly — all affected functions are structurally recursive. No action needed.

### ~~8. Missing Lean target reps for library functions~~ (Resolved — parity achieved)

Audit shows Lean has 288 `declare lean target_rep function` declarations vs Coq's 260. Lean has equal or better coverage across all library files: num.lem (149/149), list.lem (22/11), basic_classes.lem (21/20), set.lem (18/17), map.lem (12/12), machine_word.lem (36 operations now covered).

Set/map operations use list-based implementations (same as Coq). Switching to `RBTree`/`RBMap` would be an optimization, not a correctness issue.

### ~~9. Phantom type sorry warnings (cosmetic)~~ (Fixed — skip instances for opaque types)

`generate_default_values` and `generate_default_values_mutual` now filter out `Te_opaque` types before generating instances. Opaque types (zero-constructor inductives like `ty1`..`ty4096`, `itself`) are uninhabitable — they exist only to carry type-level information. Generating sorry-based `Inhabited`/`BEq`/`Ord` instances was both unsound and produced 942 compiler warnings. All eliminated.
