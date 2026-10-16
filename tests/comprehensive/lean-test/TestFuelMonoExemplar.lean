/- Fuel MONOTONICITY, hand-proved exemplar (structural-declare slice,
   2026-09-04; record TODO row 13, pre-merge audit N6 "Route B"). The
   backend generates `f_lemFuel_zero` but NOT monotonicity; this file is
   the precise shape a generated proof would have to produce, proved by
   hand over the GENERATED worker `spin_lemFuel` of test_fuel_param.lem:

     def spin_lemFuel (lemFuel : Nat) (n : Nat) : Nat := match lemFuel with
       | 0 => (999)
       | Nat.succ lemFuel => (if n == 0 then 0 else (spin_lemFuel lemFuel) (n - 1))

   Route B: a COMPLETION PREDICATE `spin_completes : Nat → args → Bool`
   mirroring the worker — 0 ↦ false; n+1 ↦ the body with every recursive
   call `spin_lemFuel n e` replaced by `spin_completes n e` and every
   VALUE the body computes dropped (a body is a function of its
   sub-results, so the taken branch is decided by the same tests). Then,
   by induction on the counter, generalizing the arguments:
     spin_completes_mono : completes n x → completes (n+1) x
     spin_mono           : completes n x → spin_lemFuel (n+1) x = spin_lemFuel n x
   and the corollaries every consumer wants — `spin_stable` (completes at
   n ⇒ the same value at every m ≥ n) and `spin_fuel_irrelevant` (two
   completing fuels agree). Neither "≠ sentinel" nor the opaque payload is
   a sound completion predicate (a genuine result may equal the sentinel
   value; a body may branch on a sub-call's sentinel) — this predicate is.
   Kernel-only tactics, no `native_decide`, no option bump; axioms below. -/
import Test_fuel_param

namespace TestFuelMonoExemplar

/-- the completion predicate: the worker's control skeleton, recursive
    calls replaced by "completes at the decremented counter" -/
def spin_completes : Nat → Nat → Bool
  | 0, _ => false
  | Nat.succ n, x => if x == 0 then true else spin_completes n (x - 1)

theorem spin_completes_mono (n x : Nat) (h : spin_completes n x = true) :
    spin_completes (n + 1) x = true := by
  induction n generalizing x with
  | zero => simp [spin_completes] at h
  | succ n ih =>
    simp only [spin_completes] at h ⊢
    split
    · rfl
    · rename_i hx; rw [if_neg hx] at h; exact ih _ h

/-- the per-function monotonicity theorem, in the shape a generator would
    emit: the SAME case split as the body, one `ih` application per
    recursive call -/
theorem spin_mono (n x : Nat) (h : spin_completes n x = true) :
    spin_lemFuel (n + 1) x = spin_lemFuel n x := by
  induction n generalizing x with
  | zero => simp [spin_completes] at h
  | succ n ih =>
    simp only [spin_completes] at h
    simp only [spin_lemFuel]
    split
    · rfl
    · rename_i hx; rw [if_neg hx] at h; exact ih _ h

/-- completion is upward closed -/
theorem spin_completes_le (n m x : Nat) (hnm : n ≤ m) (h : spin_completes n x = true) :
    spin_completes m x = true := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact spin_completes_mono _ _ ih

/-- completes at n ⇒ the same value at every m ≥ n (the generic corollary;
    its proof is function-independent given `f_mono` and
    `f_completes_mono`) -/
theorem spin_stable (n m x : Nat) (hnm : n ≤ m) (h : spin_completes n x = true) :
    spin_lemFuel m x = spin_lemFuel n x := by
  induction hnm with
  | refl => rfl
  | step hle ih => rw [spin_mono _ _ (spin_completes_le _ _ _ hle h), ih]

/-- the ∀-fuel statement at the wrapper: two completing fuels agree -/
theorem spin_fuel_irrelevant (f g x : Nat)
    (hf : spin_completes f x = true) (hg : spin_completes g x = true) :
    @spin ⟨f⟩ x = @spin ⟨g⟩ x := by
  show spin_lemFuel f x = spin_lemFuel g x
  rcases Nat.le_total f g with h | h
  · rw [spin_stable f g x h hf]
  · rw [spin_stable g f x h hg]

/-- the predicate is decidable and computes: `spin 5` completes at fuel 6, not 5 -/
example : spin_completes 6 5 = true := by decide
example : spin_completes 5 5 = false := by decide

end TestFuelMonoExemplar

#print axioms TestFuelMonoExemplar.spin_stable
#print axioms TestFuelMonoExemplar.spin_fuel_irrelevant
