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
- **31 comprehensive tests, 231 assertions**: All passing.

## Remaining Issues

### 1. Machine word operations: 942 `sorry` stubs

`mword` is an empty inductive with no constructors. All 46 machine word operations (`setBit`, `getBit`, `shiftLeft`, `lAnd`, `lOr`, `signedLess`, `wordFromInteger`, etc.) are `sorry` stubs. Code using `mword` compiles but has no real implementation.

Coq/HOL/Isabelle have full machine word libraries. Lean has `BitVec n` in Mathlib which could serve as the backing type.

Fix: Map `mword` to `BitVec n` and add `declare {lean} target_rep` for all 46 operations in `library/machine_word.lem`.

### 2. Numeric type instances: 27 `sorry` in Num.lean, 3 in Map.lean

`natural`, `int`, `integer`, `int32`, `int64`, `rational`, `real`, `float64`, `float32` are defined as empty inductives with sorry-based `Inhabited`, `BEq`, and `Ord` instances. The empty inductives are dead code (actual code uses target reps mapping to `Nat`/`Int`), but the sorry instances are unnecessary noise.

Fix: Suppress instance generation for types that have target reps, or replace the empty inductives with `abbrev` aliases to the target types.

### 3. Floating-point types map to `Int` (semantically wrong)

`rational` → `Int`, `real` → `Int`, `float64` → `Int`, `float32` → `Int`. These are silently incorrect — any code using floating-point or rational arithmetic will compute wrong answers.

Coq maps `rational` → `Q` and `real` → `R`. Lean has `Float` (64-bit IEEE) and Mathlib has `Rat`.

Fix: Add proper Lean target reps: `rational` → `Rat` (or a Lean-native rational), `float64`/`float32` → `Float`, `real` → requires Mathlib or sorry. At minimum, these should `panic!` instead of silently returning wrong results.

### 4. `int32`/`int64` collapse to `Int` (no overflow semantics)

Both `int32` and `int64` map to `Int` (arbitrary precision). There is no overflow, wrapping, or range enforcement. Code that depends on 32-bit or 64-bit overflow behavior will be wrong.

Coq has the same issue (maps to `Z`). HOL and Isabelle use proper fixed-width word types.

Fix: Map to `BitVec 32` / `BitVec 64`, or newtype wrappers with modular arithmetic.

### 5. Duplicate typeclass instances in Machine_word.lean

Since `int32`/`int64`/`int`/`integer` all map to `Int`, Machine_word generates identical typeclass instances (e.g., multiple `WordNot Int`). Later instances silently override earlier ones. Currently harmless (all sorry), but would cause real conflicts with proper implementations.

Fix: Resolves naturally once `int32`/`int64` get distinct types (issue #4) and `mword` gets `BitVec` (issue #1).

### 6. 18 `partial def` functions in generated library

These functions are actually structurally recursive (total) but Lean's termination checker rejects them because they lack `declare termination_argument = automatic` or have accumulator patterns the checker can't see:

- Num.lean: `rationalPowInteger`, `realPowInteger`
- List.lean: `map_tr`, `count_map`, `splitAtAcc`, `mapMaybe`, `mapiAux`, `catMaybes`
- List_extra.lean: `init`, `unfoldr`
- Set.lean: `leastFixedPoint`
- Set_extra.lean: `leastFixedPointUnbounded`
- String.lean: `concat`
- String_extra.lean: `stringFromNatHelper`, `stringFromNaturalHelper`
- Show.lean: `stringFromListAux`
- Num_extra.lean: `integerOfStringHelper`

Coq's termination checker accepts most of these. In Lean, `partial def` is safe at runtime but means the function can't be used in proofs.

Fix: Add `declare termination_argument = automatic` to the `.lem` library files for functions where Lean's checker can succeed (list recursion, nat countdown). For the rest, add explicit `termination_by` clauses via target reps or LemLib wrappers.

### 7. `!=` not converted in indreln antecedents

The propositional equality fix converts `==` → `=` in indreln antecedents, but `!=` is not converted to `≠`. An indreln antecedent with `x <> y` where `x` has a function type would fail (no BEq instance for functions).

Fix: Extend `lean_prop_equality` to also handle `!=` → `≠`.

### 8. Missing Lean target reps for library functions

The Lean backend has ~44 declared target reps vs ~200+ in Coq. Many standard library functions fall through to the Lem-defined implementation (which works but may be suboptimal) or to sorry stubs. Key gaps:

- `library/num.lem`: Many numeric conversion/comparison functions lack Lean reps
- `library/set.lem` / `library/set_extra.lem`: Set operations use list-based implementations (correct but O(n))
- `library/map.lem` / `library/map_extra.lem`: Map operations use association list (no `RBMap` target rep)

Fix: Audit all `declare {coq} target_rep` lines and add corresponding `declare {lean} target_rep` where Lean has equivalent stdlib functions. Prioritize hot paths (map lookup, set membership, numeric operations).
