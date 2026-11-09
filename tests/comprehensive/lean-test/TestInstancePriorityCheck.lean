/- Arc-14 S2 B4 (be:G1 + sem:S2): the instance-priority resolution probe.
   Normative lattice: doc/notes/2026-08-22_arc14-instance-priority-
   lattice.md; type shapes: tests/comprehensive/test_instance_priority.lem.

   Each #guard asks LEAN's instance resolution (not lem's static
   elaboration, which inlines class methods at known types) which
   instance wins, and fails the BUILD (`make lean` -> lean-compile) if
   the winner is wrong. #guard is evaluator-checked — a TEST, exactly
   what a resolution probe needs (never described as kernel-checked). -/
import Test_instance_priority
open Lem_Basic_classes

/- 1. THE core probe (the sem:S2 shape): prio_pair has a MODEL Eq
   instance (first-field-only, default priority = 1000) AND the
   backend's auto Eq0 trio (structural, priority := 500). The model
   instance must win BY PRIORITY: first fields equal, second differ ->
   isEqual = true iff the model instance decided. Pre-B4 this held only
   by newest-declaration-first ORDER (both at 1000) — the accident this
   probe permanently pins away. -/
#guard Eq0.isEqual (Prio_pair 0 1) (Prio_pair 0 2) == true
#guard Eq0.isInequal (Prio_pair 0 1) (Prio_pair 0 2) == false
/- ... and the model instance still distinguishes first fields. -/
#guard Eq0.isEqual (Prio_pair 1 0) (Prio_pair 2 0) == false

/- 2. No-model-instance leg: prio_auto's Eq0 must resolve to the auto
   trio (structural, 500) — above the generic low defaults and the
   failwithI-bodied fallbacks (a fallback would PANIC here, failing the
   build loudly under the guard's evaluation). -/
#guard Eq0.isEqual (Prio_auto 0 1) (Prio_auto 0 2) == false
#guard Eq0.isEqual (Prio_auto 0 1) (Prio_auto 0 1) == true

/- 3. Auto-wins-where-no-model, ordered classes: prio_pair declares NO
   Ord0/SetType instance, so the auto trio's structural order decides
   (second field 1 < 2). -/
#guard Ord0.isLess (Prio_pair 0 1) (Prio_pair 0 2) == true
#guard (match SetType.setElemCompare (Prio_pair 0 1) (Prio_pair 0 2) with
        | LemOrdering.LT => true | _ => false) == true

/- 4. RG2 (re-mark): the de-tie leg — prio_coarse carries a COARSE model
   SetType (first field only); `==` must resolve to the DERIVED
   structural BEq (1000), not the comparator bridge (400; 500 before
   the BEq-lattice slice of 2026-10-03): second
   fields differ -> false. Plant: reverting the bridge to default
   priority must flip/threaten this guard (measured at RG2). -/
#guard (Prio_coarse 0 1 == Prio_coarse 0 2) == false
#guard (Prio_coarse 0 1 == Prio_coarse 0 1) == true
-- and the coarse comparator itself still decides SetType semantics:
#guard (match SetType.setElemCompare (Prio_coarse 0 1) (Prio_coarse 0 2) with
        | LemOrdering.EQ => true | _ => false) == true

/- 5. The BEq lattice below core ([USER 2026-10-03] chose option (a), 450/400; design
   note doc/lean-backend/2026-10-03_beq-instance-lattice-design.md): the
   `[Eq0 a] : BEq a` bridge (450) and the comparator bridges
   `[SetType a]`/`[MapKeyType a] : BEq a` (400) sit BELOW core's
   `[DecidableEq a] : BEq a` (500, Init/Prelude), so `==` at a base type
   is core's structural equality, with `LawfulBEq` and the core simp set.
   These legs are speedbumps on the elaboration property; value parity is
   carried by the agreement theorems in lean-lib/LemLibTheorems.lean.
   Plant (measured 2026-10-03 against the bridge at 1000 / comparators at
   500): every leg below fails — `#synth` names `instBEqOfEq0` or
   `Lem_Map.instBEqOfMapKeyType`, `LawfulBEq` is not found, `simpa` leaves
   `(a == b) = true`, the `rfl` is a type mismatch. -/
/-- info: instBEqOfDecidableEq -/
#guard_msgs in #synth BEq Nat
/-- info: instBEqOfDecidableEq -/
#guard_msgs in #synth BEq String
-- Lean 4.35.0 (toolchain move 2026-10-21): core's `BEq` at `Int` and the
-- fixed-width types comes from the `Std.LinearOrderPackage` instances
-- (`Int.instLinearOrderPackage.toBEq`, `instLinearOrderPackageUInt64✝.toBEq`,
-- …), which outrank `instBEqOfDecidableEq`; `Nat`/`String`/`Char`/`Bool`
-- still resolve to it. Still core's instance, still above the bridges, and
-- `LawfulBEq UInt64` below is `Std.LawfulBEqOrd.lawfulBEq`. On 4.32.2 this
-- line read `instBEqOfDecidableEq`; the pin tracks the toolchain's name.
/-- info: instLinearOrderPackageUInt64✝.toBEq -/
#guard_msgs in #synth BEq UInt64
example : LawfulBEq Nat := inferInstance
example : LawfulBEq String := inferInstance
example : LawfulBEq UInt64 := inferInstance
-- the operator's example: core's simp set closes a `==` hypothesis at Nat
example (a b : Nat) (h : (a == b) = true) : a = b := by simpa using h
example (a b : String) (h : (a == b) = true) : a = b := by simpa using h
example (a b : Int) : (a == b) = decide (a = b) := rfl

/- 6. What the bridges still do under the new priorities. A type whose ONLY
   equality is a model `Eq0` (no derived BEq, no DecidableEq) gets `==`
   from the Eq0 bridge; polymorphic `[Eq0 a] [SetType a]` code gets the
   Eq0 bridge, not the coarser comparator bridge (450 > 400). -/
inductive ModelOnly where
  | mk : Nat → ModelOnly
instance : Eq0 ModelOnly where
  isEqual _ _ := true
  isInequal _ _ := false
/-- info: instBEqOfEq0 -/
#guard_msgs in #synth BEq ModelOnly
example {a : Type} [Eq0 a] [SetType a] (x y : a) : (x == y) = isEqual x y := rfl
