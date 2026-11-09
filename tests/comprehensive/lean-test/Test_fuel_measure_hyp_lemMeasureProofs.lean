/- Hand-written proofs of the fuel_measure obligations of
   test_fuel_measure_hyp.lem (measure-hypothesis slice, 2026-09-05). Each
   obligation carries its `assuming` hypothesis as the binder `lemHyp`
   (before `lemFuel`), and each proof below USES it — without it the
   statement is false (`ndigits 1 n` exhausts at every fuel; a cyclic table
   makes `size_of` exhaust; a zero step makes `down_steps` exhaust), so the
   hypothesis is not decoration. Template: stability of the worker above
   the measure by strong induction on the measured quantity generalizing
   the two fuels, the hypothesis threaded through. Kernel-only tactics, no
   `native_decide`, no option bump; `#print axioms` at the end. -/
import Test_fuel_measure_hyp

namespace Test_fuel_measure_hyp_lemMeasureProofs

/-! ### ndigits : division by the basis, hypothesis `2 ≤ b`, measure `n + 1` -/

theorem lemNatDiv_of_pos (n b : Nat) (hb : 0 < b) : lemNatDiv n b = n / b := by
  unfold lemNatDiv
  split
  · rename_i h
    have : b = 0 := by simpa using h
    omega
  · rfl

theorem ndigits_stable_aux (k : Nat) : ∀ (b n f g : Nat), 2 ≤ b → n ≤ k → n + 1 ≤ f → n + 1 ≤ g →
    ndigits_lemFuel f b n = ndigits_lemFuel g b n := by
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
        simp only [ndigits_lemFuel]
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
        simp only [ndigits_lemFuel]
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

theorem ndigits_measure_sufficient (b : Nat) (n : Nat) (lemHyp : 2 ≤ b) (lemFuel : Nat)
    (lemMeasureLe : n + 1 ≤ lemFuel) :
    ndigits_lemFuel lemFuel b n = ndigits b n :=
  ndigits_stable_aux n b n lemFuel (n + 1) lemHyp (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

/-! ### size_of : lookup-recursion through a ranked table, hypothesis
    `TestFuelMeasureHypImpl.Ranked defs`, measure `i + 1` -/

theorem foldl_add_congr (body : List Nat) (acc : Nat) (F G : Nat → Nat)
    (h : ∀ j, j ∈ body → F j = G j) :
    List.foldl (fun acc j => acc + F j) acc body = List.foldl (fun acc j => acc + G j) acc body := by
  induction body generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl]
    rw [h x (List.mem_cons_self ..)]
    exact ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem size_of_stable_aux (defs : List (List Nat)) (hr : TestFuelMeasureHypImpl.Ranked defs) (k : Nat) :
    ∀ (i f g : Nat), i ≤ k → i + 1 ≤ f → i + 1 ≤ g →
    size_of_lemFuel f defs i = size_of_lemFuel g defs i := by
  induction k with
  | zero =>
    intro i f g hk hf hg
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        have hi : i = 0 := by omega
        subst hi
        simp only [size_of_lemFuel]
        cases hlook : listGetOpt defs 0 with
        | none => rfl
        | some body =>
          simp only
          apply foldl_add_congr
          intro j hj
          have := hr 0 body hlook j hj
          omega
  | succ k ih =>
    intro i f g hk hf hg
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [size_of_lemFuel]
        cases hlook : listGetOpt defs i with
        | none => rfl
        | some body =>
          simp only
          apply foldl_add_congr
          intro j hj
          have hji := hr i body hlook j hj
          exact ih j f g (by omega) (by omega) (by omega)

theorem size_of_measure_sufficient (defs : List (List Nat)) (i : Nat)
    (lemHyp : TestFuelMeasureHypImpl.Ranked defs) (lemFuel : Nat) (lemMeasureLe : i + 1 ≤ lemFuel) :
    size_of_lemFuel lemFuel defs i = size_of defs i :=
  size_of_stable_aux defs lemHyp i i lemFuel (i + 1) (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

/-! ### down_steps : the hypothesis through a projection on a pair
    parameter, hypothesis `0 < p.2`, measure `p.1 + 1` -/

theorem down_steps_stable_aux (k : Nat) : ∀ (a step f g : Nat), 0 < step → a ≤ k → a + 1 ≤ f → a + 1 ≤ g →
    down_steps_lemFuel f (a, step) = down_steps_lemFuel g (a, step) := by
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
        simp [down_steps_lemFuel]
  | succ k ih =>
    intro a step f g hs hk hf hg
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        show (if a == 0 then 0 else 1 + down_steps_lemFuel f (a - step, step))
           = (if a == 0 then 0 else 1 + down_steps_lemFuel g (a - step, step))
        by_cases ha : a = 0
        · simp [ha]
        · have haf : (a == 0) = false := by
            cases h : a with
            | zero => exact absurd h ha
            | succ m => rfl
          simp only [haf, Bool.false_eq_true, ↓reduceIte]
          rw [ih (a - step) step f g hs (by omega) (by omega) (by omega)]

theorem down_steps_measure_sufficient (p : Nat × Nat) (lemHyp : 0 < p.2) (lemFuel : Nat)
    (lemMeasureLe : p.1 + 1 ≤ lemFuel) :
    down_steps_lemFuel lemFuel p = down_steps p := by
  obtain ⟨a, step⟩ := p
  exact down_steps_stable_aux a a step lemFuel (a + 1) lemHyp (Nat.le_refl _) lemMeasureLe (Nat.le_refl _)

end Test_fuel_measure_hyp_lemMeasureProofs

#print axioms Test_fuel_measure_hyp_lemMeasureProofs.ndigits_measure_sufficient
#print axioms Test_fuel_measure_hyp_lemMeasureProofs.size_of_measure_sufficient
#print axioms Test_fuel_measure_hyp_lemMeasureProofs.down_steps_measure_sufficient
