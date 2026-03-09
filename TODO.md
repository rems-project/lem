# Lean Backend — Open Issues

Updated: 2026-03-08

## FIXED

- **Generated library compiles**: `make lean-libs && lake build` succeeds (33 jobs, 0 errors). Fixed auxiliary file cleanup, namespace qualification, bridge instances.
- **Machine_word.lean compiles**: Fixed class method implicit resolution (`@size (a) _`) and standalone BEq instances (without `[Inhabited]` constraint).
- **Termination annotations respected**: Backend now uses `try_termination_proof` (like Coq/Isabelle). Functions with `declare termination_argument = automatic` get `def` instead of `partial def`.
- **Multi-discriminant match**: Tuple scrutinees decomposed for termination checker visibility (`match l1, l2 with` instead of `match (l1, l2) with`).
- **ppcmem-model: 10/10 files compile**: Fixed cross-module name collision (`rename_top_level.ml` seeds constant renaming with all env type names), record literal type inference (type ascription), `sorry` target rep for `Set_extra.choose` (replaced with `setChoose` in LemLib), and propositional equality in indreln antecedents (`=` instead of `==` for function types).
- **String.lean deprecation**: Changed `String.mk` → `String.ofList` target rep in `library/string.lem`.
- **Dynamic library namespace list**: Replaced hardcoded `core_lib_ns` list with dynamic computation from the module environment (`e_env`). No manual maintenance needed when library modules change.
- **deriving BEq, Ord**: Simple types (variants/records without function-typed args, non-mutual) now use `deriving BEq, Ord` instead of sorry-based instances. Eliminates sorry stubs for types like `ordering`, `maybe`, `either`, and user-defined records.

## Remaining Issues

### 1. Word.lean duplicate instances

`int32`/`int64`/`int`/`integer` all map to `Int` in Lean. This causes duplicate typeclass instances (e.g., multiple `WordNot Int` at lines 400, 449, 520, 579). Later instances silently override earlier ones. All implementations are `sorry` stubs anyway.

Fix options:
- Distinct types (`BitVec 32`, `BitVec 64`, or newtype wrappers)
- Or conditional instance generation that detects duplicates

### 2. 942 `sorry` in Machine_word.lean (+ 30 in Num.lean, Map.lean)

Generated from `.lem` library functions that have no Lean target representation. The backend emits `sorry` as placeholder. Nearly every `mword` operation is `sorry` — `mword` is an empty inductive with no constructors.

Fix: Add `declare {lean} target_rep` in the `.lem` files pointing to LemLib helper functions, or implement a proper machine word type (e.g., `BitVec n`).
