/- Hand-written proofs of the fuel_measure obligations of
   test_fuel_mutual_reader.lem (program-data-parameters S1.5, 2026-09-20):
   the measured TRULY-MUTUAL pair rmev/rmodd whose members are
   reader-lifted. The backend emits each obligation's STATEMENT into
   Test_fuel_mutual_reader_auxiliary.lean with the reader binder
   `_lemReader_amb` before the parameters — the same position as the
   single-def msum_amb obligation (Test_fuel_measure_lemMeasureProofs) —
   and this module must provide a theorem of exactly that type.

   Shape (the C2 template, Test_fuel_measure_lemMeasureProofs mev/modd):
   one JOINT stability statement for the pair, by induction on the list
   generalizing the two fuels; the reader value is an inert parameter of
   the recursion (it decides the base case's value, not the structure).
   Kernel-only tactics, no `native_decide`, no option bump. -/
import Test_fuel_mutual_reader

namespace Test_fuel_mutual_reader_lemMeasureProofs

theorem rmev_rmodd_stable (amb : Nat) (l : List Nat) (f g : Nat)
    (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    rmev_lemFuel f amb l = rmev_lemFuel g amb l ∧ rmodd_lemFuel f amb l = rmodd_lemFuel g amb l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [rmev_lemFuel, rmodd_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        have ⟨h1, h2⟩ := ih f g (by omega) (by omega)
        simp only [rmev_lemFuel, rmodd_lemFuel]
        exact ⟨h2, h1⟩

theorem rmev_measure_sufficient (_lemReader_amb : Nat) (l : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    rmev_lemFuel lemFuel _lemReader_amb l = rmev _lemReader_amb l :=
  (rmev_rmodd_stable _lemReader_amb l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)).1

theorem rmodd_measure_sufficient (_lemReader_amb : Nat) (l : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    rmodd_lemFuel lemFuel _lemReader_amb l = rmodd _lemReader_amb l :=
  (rmev_rmodd_stable _lemReader_amb l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)).2

end Test_fuel_mutual_reader_lemMeasureProofs

#print axioms Test_fuel_mutual_reader_lemMeasureProofs.rmev_measure_sufficient
#print axioms Test_fuel_mutual_reader_lemMeasureProofs.rmodd_measure_sufficient
