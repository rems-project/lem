/- Hand-written proofs of the fuel_measure obligations of
   test_fuel_measure.lem (fuel-measure slice, 2026-09-04). The backend
   emits each obligation's STATEMENT into Test_fuel_measure_auxiliary.lean
   as `theorem f_measure_sufficient … := Test_fuel_measure_lemMeasureProofs.f_measure_sufficient …`,
   so this module must provide a theorem of exactly that type for every
   measured function — the auxiliary file (a package root) does not
   build otherwise. This is the per-function obligation the cerberus half
   discharges for each of its measured functions; the proofs below are
   the template.

   Shape of every proof: STABILITY of the worker above the measure,
   `∀ f g, μ x ≤ f → μ x ≤ g → W f x = W g x`, by induction on the data
   generalizing the two fuels — each recursive call's argument has a
   strictly smaller measure (`List.length_cons`), so the induction
   hypothesis applies at the decremented counters. The obligation `W lemFuel x = f x` is the
   instance g := μ x, since `f x = W (μ x) x` by rfl. Kernel-only
   tactics, no `native_decide`, no option bump; `#print axioms` at the
   end. -/
import Test_fuel_measure

namespace Test_fuel_measure_lemMeasureProofs

/-! ### mlen : list recursion, measure `List.length l + 1` -/

theorem mlen_stable (l : List Nat) (f g : Nat) (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    mlen_lemFuel f l = mlen_lemFuel g l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [mlen_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [mlen_lemFuel]
        rw [ih f g (by omega) (by omega)]

theorem mlen_measure_sufficient (l : List Nat) (lemFuel : Nat) (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    mlen_lemFuel lemFuel l = mlen l :=
  mlen_stable l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)

/-! ### mspin : nat recursion by subtraction, measure `n + 1` -/

theorem mspin_stable (n : Nat) (f g : Nat) (hf : n + 1 ≤ f) (hg : n + 1 ≤ g) :
    mspin_lemFuel f n = mspin_lemFuel g n := by
  induction n generalizing f g with
  | zero =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [mspin_lemFuel]
  | succ n ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [mspin_lemFuel, Nat.add_one_sub_one]
        simp only [show ((n + 1 == 0) = false) from by simp]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih f g (by omega) (by omega)

theorem mspin_measure_sufficient (n : Nat) (lemFuel : Nat) (lemMeasureLe : n + 1 ≤ lemFuel) :
    mspin_lemFuel lemFuel n = mspin n :=
  mspin_stable n lemFuel (n + 1) lemMeasureLe (Nat.le_refl _)

/-! ### mrev_acc : the measure on the second parameter, the first an accumulator -/

theorem mrev_acc_stable (l' : List Nat) (acc : List Nat) (f g : Nat)
    (hf : l'.length + 1 ≤ f) (hg : l'.length + 1 ≤ g) :
    mrev_acc_lemFuel f acc l' = mrev_acc_lemFuel g acc l' := by
  induction l' generalizing acc f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [mrev_acc_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [mrev_acc_lemFuel]
        exact ih (x :: acc) f g (by omega) (by omega)

theorem mrev_acc_measure_sufficient (acc : List Nat) (l' : List Nat) (lemFuel : Nat)
    (lemMeasureLe : l'.length + 1 ≤ lemFuel) :
    mrev_acc_lemFuel lemFuel acc l' = mrev_acc acc l' :=
  mrev_acc_stable l' acc lemFuel (l'.length + 1) lemMeasureLe (Nat.le_refl _)

/-! ### mouter : a measured function that passes the AMBIENT on (its worker
    and wrapper take `[LemFuel]`; the callee `aspin 3` starts from the
    full ambient on both sides of the equation) -/

theorem mouter_stable [LemFuel] (l : List Nat) (f g : Nat) (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    mouter_lemFuel f l = mouter_lemFuel g l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [mouter_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [mouter_lemFuel]
        exact ih f g (by omega) (by omega)

theorem mouter_measure_sufficient [LemFuel] (l : List Nat) (lemFuel : Nat) (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    mouter_lemFuel lemFuel l = mouter l :=
  mouter_stable l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)

/-! ### msum_amb : fuel × reader × measure (the reader parameter is a
    leading argument of worker, wrapper and obligation alike) -/

theorem msum_amb_stable (amb : Nat) (l : List Nat) (f g : Nat) (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    msum_amb_lemFuel f amb l = msum_amb_lemFuel g amb l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [msum_amb_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [msum_amb_lemFuel]
        rw [ih f g (by omega) (by omega)]

theorem msum_amb_measure_sufficient (_lemReader_amb : Nat) (l : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    msum_amb_lemFuel lemFuel _lemReader_amb l = msum_amb _lemReader_amb l :=
  msum_amb_stable _lemReader_amb l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)

/-! ### mev / modd : a truly mutual measured block — one joint induction -/

theorem mev_modd_stable (l : List Nat) (f g : Nat) (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    mev_lemFuel f l = mev_lemFuel g l ∧ modd_lemFuel f l = modd_lemFuel g l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [mev_lemFuel, modd_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        have ⟨h1, h2⟩ := ih f g (by omega) (by omega)
        simp only [mev_lemFuel, modd_lemFuel]
        exact ⟨h2, h1⟩

theorem mev_measure_sufficient (l : List Nat) (lemFuel : Nat) (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    mev_lemFuel lemFuel l = mev l :=
  (mev_modd_stable l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)).1

theorem modd_measure_sufficient (l : List Nat) (lemFuel : Nat) (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    modd_lemFuel lemFuel l = modd l :=
  (mev_modd_stable l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)).2

end Test_fuel_measure_lemMeasureProofs

#print axioms Test_fuel_measure_lemMeasureProofs.mlen_measure_sufficient
#print axioms Test_fuel_measure_lemMeasureProofs.mspin_measure_sufficient
#print axioms Test_fuel_measure_lemMeasureProofs.mev_measure_sufficient
