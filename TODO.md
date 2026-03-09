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
- **31 comprehensive tests, 236 assertions**: All passing.
- **`int32`/`int64` now distinct types**: `LemInt32` and `LemInt64` are newtype wrappers around `Int` (same semantics as Coq's `Z` mapping, but distinct types). All arithmetic, comparison, conversion, and bitwise operations forward through the wrapper. Eliminates duplicate typeclass instances with `int`/`integer` (partial fix for #5). ppcmem `bitwiseCompatibility.lem` shift target reps updated (`Int.toNat` → `lemInt32ToNat`).

## Remaining Issues

### 1. Machine word operations: 942 `sorry` stubs

`mword` is an empty inductive with no constructors. All 46 machine word operations (`setBit`, `getBit`, `shiftLeft`, `lAnd`, `lOr`, `signedLess`, `wordFromInteger`, etc.) are `sorry` stubs. Code using `mword` compiles but has no real implementation.

Coq/HOL/Isabelle have full machine word libraries. Lean has `BitVec n` in Mathlib which could serve as the backing type.

Fix: Map `mword` to `BitVec n` and add `declare {lean} target_rep` for all 46 operations in `library/machine_word.lem`.

### ~~2. Numeric type instances: 27 `sorry` in Num.lean, 3 in Map.lean~~ (Non-issue)

These 30 sorry stubs are ALL inside `/- ... -/` block comments. The target rep mechanism already comments out the entire type definition block (inductive + instances) when a type has a Lean target rep. No active sorry, no compilation impact. Nothing to fix.

### ~~3. Floating-point types map to `Int` (semantically wrong)~~ (Fixed — panic on use)

`rational` → `LemRational`, `real` → `LemReal`, `float64` → `LemFloat64`, `float32` → `LemFloat32`. These are now distinct opaque types (defined in LemLib.lean) that panic on any operation. Previously they silently mapped to `Int`, producing wrong results (e.g., `rationalFromFrac 1 3 = 0` via integer division). All arithmetic instances, comparison functions, and conversion functions panic with clear error messages. For proper support: rational needs Mathlib's `Rat`, real needs Mathlib's `Real`, float64/float32 need IEEE 754 floats.

### ~~4. `int32`/`int64` collapse to `Int` (no overflow semantics)~~ (Fixed — distinct newtype wrappers)

`int32` → `LemInt32`, `int64` → `LemInt64`. These are `structure` wrappers around `Int` with forwarding instances for all arithmetic, comparison, and conversion operations. Same semantics as Coq's mapping to `Z` (arbitrary precision, no overflow), but now distinct types that don't collide with `int`/`integer`. Bitwise operations (`int32Lnot`, `int32Lor`, etc.) updated to use `LemInt32`/`LemInt64`. For proper overflow semantics: map to `BitVec 32` / `BitVec 64` (would require Mathlib dependency).

### 5. Duplicate typeclass instances in Machine_word.lean

Since `int`/`integer` both map to `Int`, Machine_word generates some duplicate typeclass instances (e.g., multiple `WordNot Int`). Later instances silently override earlier ones. Currently harmless (all sorry), but would cause real conflicts with proper implementations. (Previously `int32`/`int64`/`rational`/`real`/`float64`/`float32` also contributed duplicates — resolved by issues #3 and #4.)

Fix: Resolves naturally once `mword` gets `BitVec` (issue #1). The `int`/`integer` duplication is inherent (both map to `Int` in all backends).

### 6. 2 genuinely `partial def` functions in generated library

- List_extra.lean: `unfoldr` (depends on user-supplied termination condition)
- Set_extra.lean: `leastFixedPointUnbounded` (no bound — iterates until fixpoint by design)

These are correctly `partial` — no fix needed. All other previously-partial functions are now total via termination annotations or LemLib target reps.

Additionally, `LemLib.lean` (hand-written runtime) has 2 partial defs: `natSqrtAux` (Newton's method) and `set_tc` (transitive closure iteration) — both genuinely partial.

### ~~7. Audit ALL termination annotations on the branch~~ (Audited — no issues)

**Our additions**: All 10 `{lean}` scoped — affect only the Lean backend. Verified by `git diff` against branch base.

**Pre-existing unscoped annotations** (from upstream): ~35 in list.lem, list_extra.lem, num.lem, word.lem. These are intentionally universal — `try_termination_proof` in `backend.ml` uses them for ALL backends (Coq: `fun` vs `function (sequential)`; HOL: `Define` vs `Hol_defn`; Isabelle: `termination by lexicographic_order`; Lean: `def` vs `partial def`). They've been in the codebase for years and work correctly — all affected functions are structurally recursive. No action needed.

### ~~8. Missing Lean target reps for library functions~~ (Resolved — parity achieved)

Audit shows Lean has 288 `declare lean target_rep function` declarations vs Coq's 260. Lean has equal or better coverage across all library files: num.lem (149/149), list.lem (22/11), basic_classes.lem (21/20), set.lem (18/17), map.lem (12/12). The only significant gap remaining is machine_word.lem (TODO #1).

Set/map operations use list-based implementations (same as Coq). Switching to `RBTree`/`RBMap` would be an optimization, not a correctness issue.
