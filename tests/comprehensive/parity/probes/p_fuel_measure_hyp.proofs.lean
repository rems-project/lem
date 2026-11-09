/- Proofs of the fuel_measure obligations of parity/probes/p_fuel_measure_hyp.lem
   (installed by parity/run.sh as P_fuel_measure_hyp_lemMeasureProofs.lean;
   the probe's auxiliary module imports it). Same template as
   lean-test/Test_fuel_measure_hyp_lemMeasureProofs.lean: each proof USES
   its `lemHyp` hypothesis. -/
import P_fuel_measure_hyp

namespace P_fuel_measure_hyp_lemMeasureProofs

theorem lemNatDiv_of_pos (n b : Nat) (hb : 0 < b) : lemNatDiv n b = n / b := by
  unfold lemNatDiv
  split
  · rename_i h
    have : b = 0 := by simpa using h
    omega
  · rfl

theorem digits_stable_aux (k : Nat) : ∀ (b n f g : Nat), 2 ≤ b → n ≤ k → n + 1 ≤ f → n + 1 ≤ g →
    digits_lemFuel f b n = digits_lemFuel g b n := by
  induction k with
  | zero =>
    intro b n f g hb hk hf hg
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        have hn : n = 0 := by omega
        subst hn
        simp only [digits_lemFuel]
        rw [lemNatDiv_of_pos 0 b (by omega)]
        simp
  | succ k ih =>
    intro b n f g hb hk hf hg
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [digits_lemFuel]
        rw [lemNatDiv_of_pos n b (by omega)]
        by_cases hq : n / b = 0
        · simp [hq]
        · have hqf : (n / b == 0) = false := by
            cases h : n / b with
            | zero => exact absurd h hq
            | succ m => rfl
          simp only [hqf, Bool.false_eq_true, ↓reduceIte]
          have hn : 0 < n := by
            rcases Nat.eq_zero_or_pos n with h0 | h0
            · subst h0; simp at hq
            · exact h0
          have hlt : n / b < n := Nat.div_lt_self hn (by omega)
          rw [ih b (n / b) f g hb (by omega) (by omega) (by omega)]

theorem digits_measure_sufficient (b : Nat) (n : Nat) (lemHyp : 2 ≤ b) (lemFuel : Nat)
    (lemMeasureLe : n + 1 ≤ lemFuel) :
    digits_lemFuel lemFuel b n = digits b n :=
  digits_stable_aux n b n lemFuel (n + 1) lemHyp (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

theorem steps_stable_aux (k : Nat) : ∀ (a step f g : Nat), 0 < step → a ≤ k → a + 1 ≤ f → a + 1 ≤ g →
    steps_lemFuel f (a, step) = steps_lemFuel g (a, step) := by
  induction k with
  | zero =>
    intro a step f g hs hk hf hg
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        have ha : a = 0 := by omega
        subst ha
        simp [steps_lemFuel]
  | succ k ih =>
    intro a step f g hs hk hf hg
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        show (if a == 0 then 0 else 1 + steps_lemFuel f (a - step, step))
           = (if a == 0 then 0 else 1 + steps_lemFuel g (a - step, step))
        by_cases ha : a = 0
        · simp [ha]
        · have haf : (a == 0) = false := by
            cases h : a with
            | zero => exact absurd h ha
            | succ m => rfl
          simp only [haf, Bool.false_eq_true, ↓reduceIte]
          rw [ih (a - step) step f g hs (by omega) (by omega) (by omega)]

theorem steps_measure_sufficient (p : Nat × Nat) (lemHyp : 0 < p.2) (lemFuel : Nat)
    (lemMeasureLe : p.1 + 1 ≤ lemFuel) :
    steps_lemFuel lemFuel p = steps p := by
  obtain ⟨a, step⟩ := p
  exact steps_stable_aux a a step lemFuel (a + 1) lemHyp (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

end P_fuel_measure_hyp_lemMeasureProofs
