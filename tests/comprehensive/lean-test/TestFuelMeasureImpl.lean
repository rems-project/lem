/- Hand-written measure functions for test_fuel_measure_tree.lem
   (fuel-measure slice, 2026-09-04): a COMPUTABLE structural size of the
   generated inductive `mtree` (Lean's automatic `sizeOf` has no
   executable code, so it cannot be a wrapper's runtime counter). Mutual
   structural recursion over the nested inductive and its list — the
   shape Lean 4's checker accepts (structural-declare record §6, the D2
   demonstration). The kernel computes through it (`decide`). -/
import Test_fuel_measure_types

namespace TestFuelMeasureImpl

mutual
def treeSize : mtree → Nat
  | .MLeaf _ => 1
  | .MNode ts => 1 + treesSize ts
termination_by structural t => t
def treesSize : List mtree → Nat
  | [] => 1
  | t :: ts => 1 + treeSize t + treesSize ts
termination_by structural ts => ts
end

end TestFuelMeasureImpl
