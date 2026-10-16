/- The hand-written HYPOTHESIS predicate of test_fuel_measure_hyp.lem (2)
   (measure-hypothesis slice, 2026-09-05), imported by the generated module
   via `declare {lean} extra_import` and named in the declare as
   `TestFuelMeasureHypImpl.Ranked defs`. A table of definitions is RANKED
   when every reference in entry i points to an earlier entry (j < i) — a
   tag environment in declaration order; the size recursion from entry i is
   then at most i + 1 deep. A Prop: it appears only in the obligation's
   `lemHyp` binder and in the consumer's theorems, never in the wrapper. -/
import LemLib

namespace TestFuelMeasureHypImpl

def Ranked (defs : List (List Nat)) : Prop :=
  ∀ i body, listGetOpt defs i = some body → ∀ j, j ∈ body → j < i

end TestFuelMeasureHypImpl
