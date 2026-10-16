/- Proofs of the fuel_measure obligations of parity/probes/p_fuel_measure.lem
   (installed by parity/run.sh as P_fuel_measure_lemMeasureProofs.lean;
   the probe's auxiliary module imports it). Same template as
   lean-test/Test_fuel_measure_lemMeasureProofs.lean. -/
import P_fuel_measure

namespace P_fuel_measure_lemMeasureProofs

theorem len_stable (l : List Nat) (f g : Nat) (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    len_lemFuel f l = len_lemFuel g l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g => simp [len_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [len_lemFuel]
        rw [ih f g (by omega) (by omega)]

theorem len_measure_sufficient (l : List Nat) (lemFuel : Nat) (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    len_lemFuel lemFuel l = len l :=
  len_stable l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)

theorem spin_stable (n : Nat) (f g : Nat) (hf : n + 1 ≤ f) (hg : n + 1 ≤ g) :
    spin_lemFuel f n = spin_lemFuel g n := by
  induction n generalizing f g with
  | zero =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g => simp [spin_lemFuel]
  | succ n ih =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g =>
        simp only [spin_lemFuel, Nat.add_one_sub_one]
        simp only [show ((n + 1 == 0) = false) from by simp]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih f g (by omega) (by omega)

theorem spin_measure_sufficient (n : Nat) (lemFuel : Nat) (lemMeasureLe : n + 1 ≤ lemFuel) :
    spin_lemFuel lemFuel n = spin n :=
  spin_stable n lemFuel (n + 1) lemMeasureLe (Nat.le_refl _)

theorem rev_acc_stable (l : List Nat) (acc : List Nat) (f g : Nat)
    (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    rev_acc_lemFuel f acc l = rev_acc_lemFuel g acc l := by
  induction l generalizing acc f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g => simp [rev_acc_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [rev_acc_lemFuel]
        exact ih (x :: acc) f g (by omega) (by omega)

theorem rev_acc_measure_sufficient (acc : List Nat) (l : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    rev_acc_lemFuel lemFuel acc l = rev_acc acc l :=
  rev_acc_stable l acc lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)

end P_fuel_measure_lemMeasureProofs
