/- Hand-written kernel pins for fuel x reader x truly-mutual blocks
   (program-data-parameters S1.5, 2026-09-20; see
   test_fuel_mutual_reader.lem and
   doc/lean-backend/2026-09-20_fuel-mutual-reader-record.md). Every def of
   the test is reader-lifted, so nothing is assertable from the .lem; the
   generated shapes are pinned here (signatures, binder names/order, the
   `_zero` lemmas, fuel-parametricity, values where the reader decides the
   result) and re-asserted compiled in TestFuelMutualReaderExec.lean. -/

import Test_fuel_mutual_reader
import Test_fuel_mutual_reader_auxiliary  -- the generated obligations rmev/rmodd_measure_sufficient

/-! ### (1) signatures: [LemFuel]-if-needed, the fuel counter, the reader
    binder, own arguments; wrappers reader-first and point-free -/
example : Nat → Nat → Nat → Nat := rping_lemFuel
example : Nat → Nat → Nat → Nat := rpong_lemFuel
example [LemFuel] : Nat → Nat → Nat := rping
example [LemFuel] : Nat → Nat → Nat := rpong
example [LemFuel] : Nat → Nat → Nat := uses_rping
-- only oping reads amb; opong is lifted all the same (one mutual Val_def, one defined set)
example : Nat → Nat → Nat → Nat := oping_lemFuel
example : Nat → Nat → Nat → Nat := opong_lemFuel
-- the block reaches a fuel'd callee (cdown): its workers take [LemFuel] to pass the ambient on
example [LemFuel] : Nat → Nat → Nat → Nat := fping_lemFuel
example [LemFuel] : Nat → Nat → Nat → Nat := fpong_lemFuel
-- the measured pair: workers with the counter and the reader; wrappers fuel-free, reader-first
example : Nat → Nat → List Nat → Bool := rmev_lemFuel
example : Nat → List Nat → Bool := rmev
example : Nat → List Nat → Bool := rmodd

/-! binder NAMES and order, through named arguments -/
example : rping_lemFuel (lemFuel := 100) (_lemReader_amb := 7) (n := 3) = 0 := by decide
example : rmev (_lemReader_amb := 5) (l := [1, 2]) = false := by decide

/-! fuel-parametricity of the point-free wrappers (`@f ⟨n⟩ = f_lemFuel n`) -/
example (n : Nat) : @rping ⟨n⟩ = rping_lemFuel n := rfl
example (n : Nat) : @opong ⟨n⟩ = opong_lemFuel n := rfl
example (n : Nat) : @fping ⟨n⟩ = @fping_lemFuel ⟨n⟩ n := rfl

/-! ### (2) the exhaustion lemmas carry the reader binder (and [LemFuel]
    when the workers pass the ambient on) -/
example (a n : Nat) : rping_lemFuel 0 a n = 991 := rping_lemFuel_zero a n
example (a n : Nat) : rpong_lemFuel 0 a n = 992 := rpong_lemFuel_zero a n
example (a n : Nat) : opong_lemFuel 0 a n = 982 := opong_lemFuel_zero a n
example (a n : Nat) : @fping_lemFuel ⟨3⟩ 0 a n = 961 := @fping_lemFuel_zero ⟨3⟩ a n
example (a : Nat) (l : List Nat) : rmev_lemFuel 0 a l = false := rmev_lemFuel_zero a l
example (a : Nat) (l : List Nat) : rmodd_lemFuel 0 a l = true := rmodd_lemFuel_zero a l

/-! ### (3) values: the reader decides the result; sibling calls re-inject it -/
example : @rping ⟨100⟩ 7 3 = 0 := by decide     -- 4 hops, rping reaches 7
example : @rping ⟨100⟩ 8 3 = 1 := by decide     -- 5 hops, rpong reaches 8
example : @rpong ⟨100⟩ 7 3 = 1 := by decide
example : @uses_rping ⟨100⟩ 7 3 = 0 := by decide
-- exhaustion inside the block: the sentinel of the member whose counter hits 0
example : @rping ⟨5⟩ 7 3 = 0 := by decide       -- exactly enough
example : @rping ⟨4⟩ 7 3 = 991 := by decide     -- rping at 0
example : @rping ⟨3⟩ 7 3 = 992 := by decide     -- rpong at 0
-- one reading member: the non-reading sibling is lifted too and threads the value
example : @oping ⟨100⟩ 7 4 = 7 := by decide
example : @oping ⟨100⟩ 9 4 = 9 := by decide
example : @oping ⟨100⟩ 7 3 = 1 := by decide
example : @opong ⟨100⟩ 7 3 = 7 := by decide
-- a fuel'd callee reached from a member starts from the FULL ambient (8 ≥ 7 + 1),
-- never from the caller's remaining counter (5 after 3 hops, which would exhaust)
example : @fping ⟨8⟩ 7 2 = 0 := by decide
example : @fping ⟨7⟩ 7 2 = 971 := by decide
example : @fping ⟨100⟩ 7 2 = 0 := by decide

/-! ### (4) the measured pair: fuel-free wrappers; the reader decides the base case -/
example : rmev 0 [1, 2] = true := by decide
example : rmev 5 [1, 2] = false := by decide
example : rmev 5 [1] = true := by decide
example : rmodd 0 [] = false := by decide
example : rmodd 0 [1] = true := by decide
-- below the measure the worker returns a SIBLING's sentinel; at the measure the obligation makes it the wrapper
example : rmev_lemFuel 1 5 [1, 2] = true := by decide
example : rmev_lemFuel 3 5 [1, 2] = rmev 5 [1, 2] := rmev_measure_sufficient 5 [1, 2] 3 (by decide)
example (a : Nat) (l : List Nat) (f : Nat) (h : List.length l + 1 ≤ f) :
    rmodd_lemFuel f a l = rmodd a l := rmodd_measure_sufficient a l f h

/-! axiom census (charter §4: the trio or fewer) -/
#print axioms rping
#print axioms fping
#print axioms rmev
#print axioms rmev_measure_sufficient
