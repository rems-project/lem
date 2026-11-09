/- Kernel pins for fuel INSTANTIATED FROM A DATA MEASURE (fuel-measure
   slice, 2026-09-04; suite lib root). Every fact here is checked by the
   kernel at build time — `rfl`, `decide`, or a term — no `native_decide`,
   no axioms beyond Lean's own. A failing pin fails the build. -/
import Test_fuel_measure
import Test_fuel_measure_auxiliary
import Test_fuel_measure_tree
import Test_fuel_measure_tree_auxiliary

namespace TestFuelMeasureCheck

/-! ### (1) the kernel COMPUTES through a measured wrapper (closed terms) -/
example : mlen [1, 2, 3] = 3 := by decide
example : mlen [1, 2, 3] = 3 := rfl
example : mlen [] = 0 := rfl
example : mspin 5 = 0 := by decide
example : mspin 0 = 0 := rfl
example : mrev_acc [] [1, 2, 3] = [3, 2, 1] := by decide
example : mev [1, 2] = true := by decide
example : mev [1, 2, 3] = false := by decide
example : modd [1, 2, 3] = true := by decide
example : maps_mspin [1, 2, 3] = [0, 0, 0] := by decide
example : uses_mlen [1, 2, 3] = 4 := by decide

/-! ### (2) the wrapper IS the worker at the measure, definitionally -/
example (l : List Nat) : mlen l = mlen_lemFuel (List.length l + 1) l := rfl
example (n : Nat) : mspin n = mspin_lemFuel (n + 1) n := rfl
example (acc l : List Nat) : mrev_acc acc l = mrev_acc_lemFuel (l.length + 1) acc l := rfl

/-! ### (3) a measured function and its consumers are FUEL-FREE: no
    `[LemFuel]` binder (each line elaborates only if no instance is
    required — with a binder it would fail to synthesize `LemFuel`) -/
example : List Nat → Nat := mlen
example : List Nat → Nat := uses_mlen
example : Nat → Nat := mspin
example : List Nat → List Nat := maps_mspin
example : List Nat → List Nat → List Nat := mrev_acc
example : List Nat → Bool := mev
example : Nat → List Nat → Nat := msum_amb   -- reader-first, no fuel

/-! ### (4) measured ≠ fuel-lifted: a measured function whose body passes
    the ambient on DOES take `[LemFuel]` (its own counter is still the
    measure); the callee starts from the full ambient -/
example : @mouter ⟨4⟩ [1, 2] = 0 := by decide
example : @mouter ⟨4⟩ [1, 2] = @mouter ⟨100⟩ [1, 2] := by decide
example (l : List Nat) : @mouter ⟨4⟩ l = @mouter_lemFuel ⟨4⟩ (List.length l + 1) l := rfl

/-! ### (5) the generated obligations, discharged by the proofs module and
    reused here: at EVERY fuel at or above the measure the worker equals
    the wrapper (the consumer's fuel-irrelevance lemma, per function) -/
example (l : List Nat) (n : Nat) (h : List.length l + 1 ≤ n) : mlen_lemFuel n l = mlen l :=
  mlen_measure_sufficient l n h
example : mlen_lemFuel 100 [1, 2, 3] = mlen [1, 2, 3] :=
  mlen_measure_sufficient _ _ (by decide)
example (n f g : Nat) (hf : n + 1 ≤ f) (hg : n + 1 ≤ g) : mspin_lemFuel f n = mspin_lemFuel g n := by
  rw [mspin_measure_sufficient n f hf, mspin_measure_sufficient n g hg]
example (l : List Nat) (n : Nat) (h : List.length l + 1 ≤ n) : mev_lemFuel n l = mev l :=
  mev_measure_sufficient l n h

/-! ### (6) a measure over a user inductive: a hand-written computable size
    (TestFuelMeasureImpl), the recursion through `List.foldl` AS WRITTEN;
    the kernel computes, the obligation is discharged -/
example : mtsum sample = 10 := by decide
example : mdepth sample = 3 := by decide
example : mdepths [] = 0 := rfl
example : mtree → Nat := mtsum   -- fuel-free
example (t : mtree) : mtsum t = mtsum_lemFuel (TestFuelMeasureImpl.treeSize t) t := rfl
example (t : mtree) (n : Nat) (h : TestFuelMeasureImpl.treeSize t ≤ n) : mtsum_lemFuel n t = mtsum t :=
  mtsum_measure_sufficient t n h

/-! ### (7) the exhaustion lemmas still exist for measured workers -/
example (l : List Nat) : mlen_lemFuel 0 l = 999 := mlen_lemFuel_zero l
example (n : Nat) : mspin_lemFuel 0 n = fuelExhausted n := mspin_lemFuel_zero n

end TestFuelMeasureCheck
