/- Kernel pins for the HYPOTHESIS-carrying fuel measure (measure-hypothesis
   slice, 2026-09-05; suite lib root). Every fact here is checked by the
   kernel at build time — `rfl`, `decide`, or a term — no `native_decide`,
   no axioms beyond Lean's own. A failing pin fails the build. -/
import Test_fuel_measure_hyp
import Test_fuel_measure_hyp_auxiliary

namespace TestFuelMeasureHypCheck

/-! ### (1) the kernel COMPUTES through the wrappers (closed terms inside H) -/
example : ndigits 10 255 = 3 := by decide
example : ndigits 2 255 = 8 := by decide
example : ndigits 16 0 = 1 := rfl
example : uses_ndigits 1000 = 5 := by decide
example : size_of [[], [0], [0, 1], [2, 2]] 3 = 9 := by decide
example : size_of [] 7 = 1 := rfl
example : down_steps (10, 3) = 4 := by decide

/-! ### (2) the wrapper IS the worker at the measure, definitionally — the
    hypothesis is nowhere in the wrapper -/
example (b n : Nat) : ndigits b n = ndigits_lemFuel (n + 1) b n := rfl
example (defs : List (List Nat)) (i : Nat) : size_of defs i = size_of_lemFuel (i + 1) defs i := rfl
example (p : Nat × Nat) : down_steps p = down_steps_lemFuel (p.1 + 1) p := rfl

/-! ### (3) fuel-free, hypothesis-free signatures for the function and its
    consumer (each line elaborates only if no instance and no hypothesis
    is required) -/
example : Nat → Nat → Nat := ndigits
example : Nat → Nat := uses_ndigits
example : List (List Nat) → Nat → Nat := size_of
example : Nat × Nat → Nat := down_steps

/-! ### (4) the generated obligations, discharged by the proofs module and
    applied here WITH their hypotheses: at every fuel at or above the
    measure the worker equals the wrapper, on inputs satisfying H -/
example (b n f : Nat) (hb : 2 ≤ b) (hf : n + 1 ≤ f) : ndigits_lemFuel f b n = ndigits b n :=
  ndigits_measure_sufficient b n hb f hf
example (b n f g : Nat) (hb : 2 ≤ b) (hf : n + 1 ≤ f) (hg : n + 1 ≤ g) :
    ndigits_lemFuel f b n = ndigits_lemFuel g b n := by
  rw [ndigits_measure_sufficient b n hb f hf, ndigits_measure_sufficient b n hb g hg]
example (defs : List (List Nat)) (i f : Nat) (hr : TestFuelMeasureHypImpl.Ranked defs) (hf : i + 1 ≤ f) :
    size_of_lemFuel f defs i = size_of defs i :=
  size_of_measure_sufficient defs i hr f hf
example (p : Nat × Nat) (f : Nat) (hp : 0 < p.2) (hf : p.1 + 1 ≤ f) : down_steps_lemFuel f p = down_steps p :=
  down_steps_measure_sufficient p hp f hf
-- the obligation's binder ORDER is the contract a consumer gate reads:
-- parameters, `lemHyp`, `lemFuel`, `lemMeasureLe`
example : ∀ (b n : Nat), 2 ≤ b → ∀ (lemFuel : Nat), n + 1 ≤ lemFuel → ndigits_lemFuel lemFuel b n = ndigits b n :=
  ndigits_measure_sufficient

/-! ### (5) OUTSIDE the hypothesis the wrapper is still a total, computable
    value — and EXHAUSTS: at basis 1 the recursion never reaches the base
    case (the OCaml target loops forever on this input), so the worker
    bottoms out in the declared sentinel after `measure` frames, and the
    frames above it add to that VALUE (the sentinel is a value in the
    logic — the operational gap the fuel-measure record §2.2 names; in
    production the sentinel is the loud `fuelExhausted`, which panics
    here instead). The obligation says nothing on these inputs. -/
example : ndigits 1 5 = 6 + 999 := by decide            -- 6 frames (measure 5 + 1), then the sentinel
example : down_steps (5, 0) = 6 + 999 := by decide      -- a zero step never reaches 0
example : size_of [[0]] 0 = 1 + 999 := by decide         -- entry 0 refers to itself: a cyclic table

/-! ### (6) the exhaustion lemmas exist unchanged -/
example (b n : Nat) : ndigits_lemFuel 0 b n = 999 := ndigits_lemFuel_zero b n
example (p : Nat × Nat) : down_steps_lemFuel 0 p = 999 := down_steps_lemFuel_zero p

end TestFuelMeasureHypCheck
