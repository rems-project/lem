/- Kernel pins for the fuel-parameter scheme (fuel-parameter arc,
   2026-09-04; suite lib root). Every fact here is checked by the kernel
   at build time — `rfl`, `decide`, or a small ∀-fuel theorem — with no
   `native_decide`, no axioms beyond Lean's own. A failing pin fails the
   build. The numerals below are TEST-SUITE choices ([USER 2026-09-03]:
   defaults chosen in test suites are fine); none exists
   in LemLib or in the generated code (check_no_fuel_numerals.sh). -/
import Test_fuel_param
import Test_contextual_keywords

namespace TestFuelParamCheck

/-! ### (1) the wrapper IS the worker at the ambient, definitionally -/
example : @spin ⟨100⟩ = spin_lemFuel 100 := rfl
example : @climb ⟨7⟩ = climb_lemFuel 7 := rfl
example (n : Nat) : @loud_spin ⟨0⟩ n = fuelExhausted n := rfl

/-! ### (2) the generated exhaustion lemmas (`<worker>_zero`), reused
    A leaf worker takes no instance; a worker that passes the ambient on
    (outer, mping/mpong) does. -/
example (n : Nat) : spin_lemFuel 0 n = 999 := spin_lemFuel_zero n
example (n : Nat) : loud_spin_lemFuel 0 n = fuelExhausted n := loud_spin_lemFuel_zero n
example (a : Nat) (n : Nat) : climb_lemFuel 0 a n = 998 := climb_lemFuel_zero a n
example (n : Nat) : @outer_lemFuel ⟨3⟩ 0 n = fuelExhausted n := @outer_lemFuel_zero ⟨3⟩ n
example (n : Nat) : @mping_lemFuel ⟨3⟩ 0 n = 995 := @mping_lemFuel_zero ⟨3⟩ n
example (n : Nat) (u : Unit) : wild_spin_lemFuel 0 n u = 997 := wild_spin_lemFuel_zero n u
example (p : Nat × Nat) : tup_spin_lemFuel 0 p = 996 := tup_spin_lemFuel_zero p
-- a point-free tail: the lemma's LHS carries the codomain ascription (fuel-measure slice)
example (n : Nat) : (tail_spin_lemFuel 0 n : Nat → Nat) = (fun x => x) := tail_spin_lemFuel_zero n
example : @tail_spin Nat ⟨3⟩ 2 7 = 7 := by decide

/-! ### (3) sufficient fuel: two different fuels, the same value -/
example : @spin ⟨6⟩ 5 = 0 := by decide
example : @spin ⟨1000⟩ 5 = 0 := by decide
example : @uses_uses_spin ⟨100⟩ 2 = 2 := by decide
example : @uses_uses_spin ⟨5⟩ 2 = 2 := by decide
example : @maps_spin ⟨10⟩ [1, 2, 3] = [0, 0, 0] := by decide
example : @tup_spin ⟨10⟩ (3, 4) = 7 := by decide
example : @wild_spin ⟨10⟩ 3 () = 0 := by decide

/-! ### (4) insufficient fuel: exactly the declared sentinel — nothing else
    (there is no default to fall back on) -/
example : @spin ⟨5⟩ 5 = 999 := by decide
example : @uses_spin ⟨5⟩ 5 = 1000 := by decide

/-! ### (5) a fuel'd callee starts from the FULL ambient: outer 3 needs 4
    counter steps and then spin 3 needs 4 of its own — at ambient 4 both
    complete. (Under "pass the remaining counter" semantics spin would
    receive 0 and this would read 999.) -/
example : @outer ⟨4⟩ 3 = 0 := by decide
example : @mping ⟨3⟩ 2 = 0 := by decide

/-! ### (6) fuel × reader (wrapper: instance, then reader-first) and
    fuel × reader_seed (the seed def is fuel-lifted; its first argument
    seeds the reader) -/
example : @uses_climb ⟨100⟩ 10 3 = 10 := by decide
example : @seeded_climb ⟨100⟩ 10 3 = 10 := by decide
example : @seeded_climb ⟨3⟩ 10 3 = 998 := by decide

/-! ### (7) a value binding is a function of the instance -/
example : @spun_value ⟨100⟩ = 0 := by decide
example : @spun_value ⟨7⟩ = 999 := by decide

/-! ### (8) a fuel_consumer reads the same ambient its callers carry -/
example : @uses_consumer ⟨42⟩ 1 = 43 := by decide

/-! ### (9) an entry point instantiates once (`letI`) -/
example : (letI : LemFuel := ⟨50⟩; uses_spin 7) = 1 := by decide

/-! ### (10) the contextual-keyword test's own fuel declare still works -/
example : @count_down ⟨100⟩ 5 = 0 := by decide

/-! ### (11) the ∀-fuel statement shape: above the depth, the value does
    not depend on the fuel -/
theorem spin_sufficient (n f : Nat) (h : n < f) : spin_lemFuel f n = 0 := by
  induction f generalizing n with
  | zero => omega
  | succ f ih =>
    simp only [spin_lemFuel]
    split
    · rfl
    · rename_i hne
      apply ih
      have hn : n ≠ 0 := fun h0 => hne (by subst h0; decide)
      omega

theorem spin_fuel_irrelevant (f g n : Nat) (hf : n < f) (hg : n < g) :
    @spin ⟨f⟩ n = @spin ⟨g⟩ n := by
  show spin_lemFuel f n = spin_lemFuel g n
  rw [spin_sufficient n f hf, spin_sufficient n g hg]

end TestFuelParamCheck

#print axioms TestFuelParamCheck.spin_fuel_irrelevant

/-! ### an inductive relation with a fuel'd premise takes `[LemFuel]` as an
    inductive parameter (D2-enablers slice): its type, a derivation at an
    explicit instance (the premise `spin m = 0` decided by the kernel at
    that instance), and the constructor's binder shape -/
example : [LemFuel] → Nat → Nat → Prop := @spin_reach
example : @spin_reach ⟨5⟩ 0 1 :=
  @spin_reach.spin_reach_step ⟨5⟩ 0 0 (@spin_reach.spin_reach_refl ⟨5⟩ 0) (by decide)
example : @spin_reach ⟨5⟩ 3 3 := @spin_reach.spin_reach_refl ⟨5⟩ 3
example (n m : Nat) [inst : LemFuel] (h : spin_reach n m) (hs : spin m = 0) : spin_reach n (m + 1) :=
  spin_reach.spin_reach_step n m h hs
