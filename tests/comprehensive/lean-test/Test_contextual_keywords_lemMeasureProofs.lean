/- Proof of the fuel_measure obligation of test_contextual_keywords.lem
   (fuel-measure slice, 2026-09-04): the measured `count_list_measured`. -/
import Test_contextual_keywords

namespace Test_contextual_keywords_lemMeasureProofs

theorem count_list_measured_stable (l : List Nat) (f g : Nat)
    (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    count_list_measured_lemFuel f l = count_list_measured_lemFuel g l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g => simp [count_list_measured_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [count_list_measured_lemFuel]
        rw [ih f g (by omega) (by omega)]

theorem count_list_measured_measure_sufficient (l : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    count_list_measured_lemFuel lemFuel l = count_list_measured l :=
  count_list_measured_stable l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)

/-! ### count_list_bounded : a caller-passed bound `k`, hypothesis
    `List.length l ≤ k`, measure `k + 1` (measure-hypothesis slice) -/

theorem count_list_bounded_stable (l : List Nat) (k f g : Nat)
    (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    count_list_bounded_lemFuel f k l = count_list_bounded_lemFuel g k l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g => simp [count_list_bounded_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [count_list_bounded_lemFuel]
        rw [ih f g (by omega) (by omega)]

theorem count_list_bounded_measure_sufficient (k : Nat) (l : List Nat)
    (lemHyp : List.length l ≤ k) (lemFuel : Nat) (lemMeasureLe : k + 1 ≤ lemFuel) :
    count_list_bounded_lemFuel lemFuel k l = count_list_bounded k l :=
  count_list_bounded_stable l k lemFuel (k + 1) (by omega) (by omega)

end Test_contextual_keywords_lemMeasureProofs

#print axioms Test_contextual_keywords_lemMeasureProofs.count_list_measured_measure_sufficient
#print axioms Test_contextual_keywords_lemMeasureProofs.count_list_bounded_measure_sufficient
