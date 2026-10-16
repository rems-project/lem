/- Kernel pins for the BACKEND-DERIVED computable size functions
   (D2-enablers slice, 2026-09-04; suite lib root). Every fact here is
   checked by the kernel at build time — `rfl`, `decide`, or a term — no
   `native_decide`, no axioms beyond Lean's own. A failing pin fails the
   build. -/
import Test_lem_size
import Test_lem_size_auxiliary
import Test_fuel_measure_types

open Lem_Basic_classes (Eq0)

namespace TestLemSizeCheck

/-! ### (1) the derived sizes COMPUTE in the kernel (closed terms); the
    documented semantics: 1 per constructor node, 1 per `::`/`some`/`inl`/`inr`,
    0 per `[]`/`none`, tuples transparent, leaves 0 -/
example : tm.lemSize (TLeaf 5) = 1 := by decide
example : tm.lemSize (TNode [] none) = 1 := by decide
example : tm.lemSize (TNode [(1, TLeaf 2)] none) = 3 := by decide           -- node + cons + leaf
example : tm.lemSize (TNode [] (some (TLeaf 2))) = 3 := by decide          -- node + some + leaf
example : tm.lemSize sample_tm = 7 := by decide
example : mtree.lemSize (MNode [MLeaf 1, MNode []]) = 5 := by decide       -- node + (cons+leaf) + (cons+node)
example : sbox.lemSize (SB (1 : Nat) [SB 2 [], SE]) = 5 := by decide       -- SB + (cons+SB) + (cons+SE); the `a` field is a leaf
example : sbox.lemSize (SB "a string leaf" []) = 1 := by decide
example : r1.lemSize (R1 [Sum.inl 3, Sum.inr ⟨0, [R1 []]⟩]) = 8 := by decide
   -- R1 + (cons + inl) + (cons + inr + (mk + (cons + R1)))
example : r2.lemSize ⟨7, []⟩ = 1 := by decide

/-! ### (2) the derived size functions rest on no axioms -/
#print axioms tm.lemSize
#print axioms r1.lemSize
#print axioms sbox.lemSize
#print axioms mtree.lemSize

/-! ### (3) a measured wrapper IS the worker at the derived size, definitionally,
    and the kernel computes through it -/
example (t : tm) : tm_sum t = tm_sum_lemFuel (tm.lemSize t) t := rfl
example (t1 t2 : tm) : tm_eq t1 t2 = tm_eq_lemFuel (tm.lemSize t1) t1 t2 := rfl
example (t : mtree) : mcount t = mcount_lemFuel (mtree.lemSize t) t := rfl
example (s : sbox Nat) : sb_count s = sb_count_lemFuel (sbox.lemSize s) s := rfl
example : tm_sum sample_tm = 6 := by decide
example : tm_eq sample_tm sample_tm = true := by decide
example : tm_eq sample_tm (TLeaf 0) = false := by decide
example : tm_eq (TNode [(1, TLeaf 2)] none) (TNode [(1, TLeaf 3)] none) = false := by decide
example : mcount (MNode [MLeaf 1, MNode []]) = 3 := by decide
example : sb_count (SB (1 : Nat) [SB 2 [], SE]) = 2 := by decide

/-! ### (4) the D2 shape: the `Eq0` instance's method is the MEASURED
    equality (fuel-free), and the user class instance too -/
example : Eq0.isEqual sample_tm sample_tm = true := by decide
example : Eq0.isEqual sample_tm (TLeaf 0) = false := by decide
example : Eq0.isInequal sample_tm (TLeaf 0) = true := by decide
example : (Eq0.isEqual : tm → tm → Bool) = tm_eq := rfl
example : sz sample_tm = 6 := by decide

/-! ### (5) measured functions and their consumers are FUEL-FREE (each line
    elaborates only if no `LemFuel` instance is required) -/
example : tm → Nat := tm_sum
example : tm → tm → Bool := tm_eq
example : mtree → Nat := mcount
example : sbox Nat → Nat := sb_count
example : Eq0 tm := inferInstance
example : Sz tm := inferInstance

/-! ### (6) the generated obligations, discharged by the proofs module and
    reused: at EVERY fuel at or above the derived size the worker equals
    the wrapper -/
example (t : tm) (n : Nat) (h : tm.lemSize t ≤ n) : tm_sum_lemFuel n t = tm_sum t :=
  tm_sum_measure_sufficient t n h
example (t1 t2 : tm) (n : Nat) (h : tm.lemSize t1 ≤ n) : tm_eq_lemFuel n t1 t2 = tm_eq t1 t2 :=
  tm_eq_measure_sufficient t1 t2 n h
example : tm_eq_lemFuel 100 sample_tm sample_tm = tm_eq sample_tm sample_tm :=
  tm_eq_measure_sufficient _ _ _ (by decide)
example (t : mtree) (n : Nat) (h : mtree.lemSize t ≤ n) : mcount_lemFuel n t = mcount t :=
  mcount_measure_sufficient t n h
example (s : sbox Nat) (n : Nat) (h : sbox.lemSize s ≤ n) : sb_count_lemFuel n s = sb_count s :=
  sb_count_measure_sufficient s n h

/-! ### (7) the exhaustion lemmas still exist for measured workers -/
example (t : tm) : tm_sum_lemFuel 0 t = fuelExhausted 0 := tm_sum_lemFuel_zero t
example (t1 t2 : tm) : tm_eq_lemFuel 0 t1 t2 = fuelExhausted false := tm_eq_lemFuel_zero t1 t2

end TestLemSizeCheck
