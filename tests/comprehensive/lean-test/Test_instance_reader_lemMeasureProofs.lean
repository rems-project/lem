/- Hand-written proof of the fuel_measure obligation of
   test_instance_reader.lem (instance-reader slice, 2026-10-05): the
   measured `ilen` reads the instance reader `sw`, so the generated
   obligation (Test_instance_reader_auxiliary.lean) binds
   `[TestInstanceReaderImpl.Sw]` before the parameters, and this theorem
   must have exactly that type. The instance is an inert parameter of the
   recursion (it decides the base value, not the structure). Kernel-only
   tactics, no `native_decide`, no option bump. -/
import Test_instance_reader

namespace Test_instance_reader_lemMeasureProofs

theorem ilen_stable [TestInstanceReaderImpl.Sw] (l : List Nat) (f g : Nat)
    (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    ilen_lemFuel f l = ilen_lemFuel g l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [ilen_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [ilen_lemFuel]
        rw [ih f g (by omega) (by omega)]

theorem ilen_measure_sufficient [TestInstanceReaderImpl.Sw] (l : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    ilen_lemFuel lemFuel l = ilen l :=
  ilen_stable l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)

end Test_instance_reader_lemMeasureProofs

#print axioms Test_instance_reader_lemMeasureProofs.ilen_measure_sufficient
