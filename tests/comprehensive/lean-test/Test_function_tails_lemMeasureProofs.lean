/- Hand-written proofs of the fuel_measure obligations of
   test_function_tails.lem (tails-and-pmap-laws slice, 2026-09-05). Same
   template as Test_fuel_measure_lemMeasureProofs.lean: STABILITY of the
   worker above the measure by induction on the data generalizing the two
   fuels — here the data is the HOISTED `function` scrutinee `lemTail`,
   an ordinary explicit argument of worker, wrapper and obligation alike.
   Kernel-only tactics, no `native_decide`, no option bump; `#print axioms`
   at the end. -/
import Test_function_tails

namespace Test_function_tails_lemMeasureProofs

/-! ### tlen : `let rec tlen acc = function …`, measure `List.length lemTail + 1` -/

theorem tlen_stable (l : List Nat) (acc : Nat) (f g : Nat)
    (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    tlen_lemFuel f acc l = tlen_lemFuel g acc l := by
  induction l generalizing acc f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [tlen_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [tlen_lemFuel]
        exact ih (acc + 1) f g (by omega) (by omega)

theorem tlen_measure_sufficient (acc : Nat) (lemTail : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length lemTail + 1 ≤ lemFuel) :
    tlen_lemFuel lemFuel acc lemTail = tlen acc lemTail :=
  tlen_stable lemTail acc lemFuel (List.length lemTail + 1) lemMeasureLe (Nat.le_refl _)

/-! ### tpair : a destructuring parameter before the `function` (the binder
    was hoisted through the compiler's single-arm match on `p`) -/

theorem tpair_stable (l : List Nat) (p : Nat × Nat) (f g : Nat)
    (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    tpair_lemFuel f p l = tpair_lemFuel g p l := by
  induction l generalizing p f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => obtain ⟨a, b⟩ := p; simp [tpair_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        obtain ⟨a, b⟩ := p
        simp only [List.length_cons] at hf hg
        simp only [tpair_lemFuel]
        exact ih (a + x, b + 1) f g (by omega) (by omega)

theorem tpair_measure_sufficient (p : Nat × Nat) (lemTail : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length lemTail + 1 ≤ lemFuel) :
    tpair_lemFuel lemFuel p lemTail = tpair p lemTail :=
  tpair_stable lemTail p lemFuel (List.length lemTail + 1) lemMeasureLe (Nat.le_refl _)

/-! ### tscale : `fun k -> function …` (k and lemTail both hoisted) -/

theorem tscale_stable (l : List Nat) (acc k : Nat) (f g : Nat)
    (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    tscale_lemFuel f acc k l = tscale_lemFuel g acc k l := by
  induction l generalizing acc f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [tscale_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [tscale_lemFuel]
        exact ih (acc + k * x) f g (by omega) (by omega)

theorem tscale_measure_sufficient (acc k : Nat) (lemTail : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length lemTail + 1 ≤ lemFuel) :
    tscale_lemFuel lemFuel acc k lemTail = tscale acc k lemTail :=
  tscale_stable lemTail acc k lemFuel (List.length lemTail + 1) lemMeasureLe (Nat.le_refl _)

/-! ### tev / todd : a truly mutual block, one named-parameter member and one
    `function`-tail member — one joint induction on the shared list -/

theorem tev_todd_stable (l : List Nat) (acc : Nat) (f g : Nat)
    (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    tev_lemFuel f acc l = tev_lemFuel g acc l ∧ todd_lemFuel f acc l = todd_lemFuel g acc l := by
  induction l generalizing acc f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [tev_lemFuel, todd_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [tev_lemFuel, todd_lemFuel]
        exact ⟨(ih (acc + 1) f g (by omega) (by omega)).2, (ih (acc + 2) f g (by omega) (by omega)).1⟩

theorem tev_measure_sufficient (acc : Nat) (l : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    tev_lemFuel lemFuel acc l = tev acc l :=
  (tev_todd_stable l acc lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)).1

theorem todd_measure_sufficient (acc : Nat) (lemTail : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length lemTail + 1 ≤ lemFuel) :
    todd_lemFuel lemFuel acc lemTail = todd acc lemTail :=
  (tev_todd_stable lemTail acc lemFuel (List.length lemTail + 1) lemMeasureLe (Nat.le_refl _)).2

/-! ### tdot : `function` over a PAIR of lists, the measure a projection of
    the hoisted binder (`List.length lemTail.1 + 1`) -/

theorem tdot_stable (l1 l2 : List Nat) (acc : Nat) (f g : Nat)
    (hf : List.length l1 + 1 ≤ f) (hg : List.length l1 + 1 ≤ g) :
    tdot_lemFuel f acc (l1, l2) = tdot_lemFuel g acc (l1, l2) := by
  induction l1 generalizing l2 acc f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => cases l2 <;> simp [tdot_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        cases l2 with
        | nil => simp [tdot_lemFuel]
        | cons y ys =>
          simp only [tdot_lemFuel]
          exact ih ys (acc + x * y) f g (by omega) (by omega)

theorem tdot_measure_sufficient (acc : Nat) (lemTail : List Nat × List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length lemTail.1 + 1 ≤ lemFuel) :
    tdot_lemFuel lemFuel acc lemTail = tdot acc lemTail := by
  obtain ⟨l1, l2⟩ := lemTail
  exact tdot_stable l1 l2 acc lemFuel (List.length l1 + 1) lemMeasureLe (Nat.le_refl _)

/-! ### tuser : a trailing user lambda with no `function` (audit F3, probe
    p13) — `k` hoisted; the measure is on `n` -/

theorem tuser_stable (n k : Nat) (f g : Nat) (hf : n + 1 ≤ f) (hg : n + 1 ≤ g) :
    tuser_lemFuel f n k = tuser_lemFuel g n k := by
  induction n generalizing k f g with
  | zero =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [tuser_lemFuel]
  | succ n ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [tuser_lemFuel, Nat.add_one_sub_one]
        simp only [show ((n + 1 == 0) = false) from by simp]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih (k + 1) f g (by omega) (by omega)

theorem tuser_measure_sufficient (n k : Nat) (lemFuel : Nat) (lemMeasureLe : n + 1 ≤ lemFuel) :
    tuser_lemFuel lemFuel n k = tuser n k :=
  tuser_stable n k lemFuel (n + 1) lemMeasureLe (Nat.le_refl _)

end Test_function_tails_lemMeasureProofs

#print axioms Test_function_tails_lemMeasureProofs.tlen_measure_sufficient
#print axioms Test_function_tails_lemMeasureProofs.tpair_measure_sufficient
#print axioms Test_function_tails_lemMeasureProofs.tscale_measure_sufficient
#print axioms Test_function_tails_lemMeasureProofs.tev_measure_sufficient
#print axioms Test_function_tails_lemMeasureProofs.todd_measure_sufficient
#print axioms Test_function_tails_lemMeasureProofs.tdot_measure_sufficient
#print axioms Test_function_tails_lemMeasureProofs.tuser_measure_sufficient
