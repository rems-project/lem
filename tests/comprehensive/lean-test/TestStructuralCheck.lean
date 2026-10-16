/- Kernel pins for `declare {lean} structural val` (structural-declare
   slice, 2026-09-04; suite lib root). Every fact here is checked by the
   kernel at build time — `decide` or `rfl` on CLOSED terms, which is
   exactly what a structural (form (c)) definition promises and a
   well-founded (form (b)) one cannot deliver (the consumer's `join`
   finding: `decide` "did not reduce to isTrue or isFalse" through
   WellFounded.fix). No `native_decide`, no option bump, no axiom beyond
   Lean's own (#print axioms below). -/
import Test_structural

namespace TestStructuralCheck

/-! ### (1) closed-term computation by the kernel: `decide` -/
example : len [1, 2, 3] = 3 := by decide
example : rev_acc [] [1, 2, 3] = [3, 2, 1] := by decide
example : tsum (Node [Leaf 1, Node [Leaf 2, Leaf 3], Leaf 4]) = 10 := by decide
example : zipsum [1, 2, 3] [10, 20] = 33 := by decide
example : skip2 [1, 2, 3, 4, 5] = 9 := by decide
example : sum_with [1, 2, 3] = 6 := by decide

/-! ### (2) and by `rfl` (definitional unfolding — a structural def is
    transparent; the same statement about a `partial def` or a
    WellFounded.fix definition does not typecheck) -/
example : len [1, 2, 3] = 3 := rfl
example : tsum (Node [Leaf 1, Leaf 2]) = 3 := rfl

/-! ### (3) the equation lemmas are the structural unfolding, usable in
    an inductive proof — the ∀-statement shape a consumer writes -/
theorem len_append (a b : List Nat) : len (a ++ b) = len a + len b := by
  induction a with
  | nil => simp [len]
  | cons x xs ih => simp [len, ih]; omega

theorem rev_acc_length (acc l : List Nat) :
    len (rev_acc acc l) = len acc + len l := by
  induction l generalizing acc with
  | nil => simp [rev_acc, len]
  | cons x xs ih => simp only [rev_acc, len]; rw [ih]; simp [len]; omega

/-! ### (4) structural × fuel lifting: the structural def that calls a
    fuel'd def takes the instance and nothing else — its own recursion
    needs no fuel -/
example : @spin_each ⟨10⟩ [1, 2, 3] = 0 := by decide
example : @spin_each ⟨2⟩ [1, 5] = 999 := by decide

end TestStructuralCheck

#print axioms TestStructuralCheck.len_append
#print axioms TestStructuralCheck.rev_acc_length
