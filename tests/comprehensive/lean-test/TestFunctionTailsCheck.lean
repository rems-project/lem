/- Kernel pins for POINT-FREE `function` TAILS (tails-and-pmap-laws slice,
   2026-09-05; suite lib root). The `.lem` definitions are `let rec f acc =
   function …`; the Lean emission hoisted the trailing binder(s) into the
   head as `lemTail` (and a user `fun k ->` as `k`). Every fact here is
   checked by the kernel at build time — `rfl`, `decide`, or a term — no
   `native_decide`, no axioms beyond Lean's own. A failing pin fails the
   build. -/
import Test_function_tails
import Test_function_tails_auxiliary

namespace TestFunctionTailsCheck

/-! ### (1) the kernel COMPUTES through the measured wrappers and the
    structural defs (closed terms) -/
example : tlen 0 [1, 2, 3] = 3 := by decide
example : tlen 0 [1, 2, 3] = 3 := rfl
example : slen 10 [1, 2] = 12 := by decide
example : slen 10 [1, 2] = 12 := rfl
example : tpair (0, 0) [1, 2, 3] = (6, 3) := by decide
example : tscale 0 2 [1, 2, 3] = 12 := by decide
example : tev 0 [1, 2, 3] = 4 := by decide
example : todd 0 [1, 2, 3] = 5 := by decide
example : tdot 0 ([1, 2, 3], [4, 5, 6]) = 32 := by decide
example : tdot 0 ([1, 2], [4]) = 0 := by decide
example : sscale 1 3 [1, 2] = 10 := by decide
example : sscale 1 3 [1, 2] = 10 := rfl

/-! ### (2) the wrapper IS the worker at the measure over the HOISTED
    binder, definitionally -/
example (acc : Nat) (l : List Nat) : tlen acc l = tlen_lemFuel (List.length l + 1) acc l := rfl
example (p : Nat × Nat) (l : List Nat) : tpair p l = tpair_lemFuel (List.length l + 1) p l := rfl
example (acc k : Nat) (l : List Nat) : tscale acc k l = tscale_lemFuel (List.length l + 1) acc k l := rfl
example (acc : Nat) (l : List Nat × List Nat) : tdot acc l = tdot_lemFuel (List.length l.1 + 1) acc l := rfl

/-! ### (3) fuel-free signatures: the hoisted binder is an ordinary explicit
    argument; no `[LemFuel]` (each line elaborates only if no instance is
    required) -/
example : Nat → List Nat → Nat := tlen
example : Nat → List Nat → Nat := slen
example : Nat × Nat → List Nat → Nat × Nat := tpair
example : Nat → Nat → List Nat → Nat := tscale
example : Nat → List Nat → Nat := tev
example : Nat → List Nat → Nat := todd
example : Nat → List Nat × List Nat → Nat := tdot
example : Nat → Nat → List Nat → Nat := sscale

/-! ### (4) the exhaustion lemma: the sentinel — written in lem at the
    head's original, function-typed codomain — applied to the hoisted
    binder; by beta it is the point-free value, and the point-free lemma
    is recovered by funext -/
example (acc : Nat) (l : List Nat) : tlen_lemFuel 0 acc l = acc := tlen_lemFuel_zero acc l
example (acc : Nat) : (tlen_lemFuel 0 acc : List Nat → Nat) = (fun _ => acc) :=
  funext (fun l => tlen_lemFuel_zero acc l)
example (p : Nat × Nat) (l : List Nat) : tpair_lemFuel 0 p l = (0, 0) := tpair_lemFuel_zero p l
example (acc k : Nat) (l : List Nat) : tscale_lemFuel 0 acc k l = acc := tscale_lemFuel_zero acc k l
example (acc : Nat) (l : List Nat × List Nat) : tdot_lemFuel 0 acc l = 0 := tdot_lemFuel_zero acc l

/-! ### (4b) a trailing user lambda with no `function` (audit F3, probe
    p13): `k` is a head binder; the point-free form by funext -/
example : tuser 3 10 = 13 := by decide
example : tuser 3 10 = 13 := rfl
example : Nat → Nat → Nat := tuser
example (n k : Nat) : tuser n k = tuser_lemFuel (n + 1) n k := rfl
example (n k : Nat) : tuser_lemFuel 0 n k = 0 := tuser_lemFuel_zero n k
example (n : Nat) : (tuser_lemFuel 0 n : Nat → Nat) = (fun _ => 0) := funext (fun k => tuser_lemFuel_zero n k)
example (n k m : Nat) (h : n + 1 ≤ m) : tuser_lemFuel m n k = tuser n k := tuser_measure_sufficient n k m h

/-! ### (5) NOT hoisted: an ambient fuel'd point-free tail without a
    measure keeps the fuel-measure slice's shape (codomain-ascribed
    `_zero` lemma, `[LemFuel]` wrapper) -/
example (acc : Nat) : (plain_tail_lemFuel 0 acc : List Nat → Nat) = (fun _ => acc) :=
  plain_tail_lemFuel_zero acc
example : @plain_tail ⟨5⟩ 0 [1, 2, 3] = 3 := by decide
example : @plain_tail ⟨5⟩ 0 [1, 2, 3] = @plain_tail ⟨50⟩ 0 [1, 2, 3] := by decide

/-! ### (6) the structural def's equation lemmas in an inductive proof over
    the hoisted parameter -/
theorem slen_eq (acc : Nat) (l : List Nat) : slen acc l = acc + l.length := by
  induction l generalizing acc with
  | nil => simp [slen]
  | cons x xs ih => simp [slen, ih]; omega

theorem sscale_eq (acc k : Nat) (l : List Nat) : sscale acc k l = acc + k * l.sum := by
  induction l generalizing acc with
  | nil => simp [sscale]
  | cons x xs ih => simp [sscale, ih, Nat.mul_add]; omega

/-! ### (7) the generated obligations, discharged by the proofs module and
    reused: at EVERY fuel at or above the measure the worker equals the
    wrapper -/
example (acc : Nat) (l : List Nat) (n : Nat) (h : List.length l + 1 ≤ n) :
    tlen_lemFuel n acc l = tlen acc l := tlen_measure_sufficient acc l n h
example (acc : Nat) (l : List Nat × List Nat) (n : Nat) (h : List.length l.1 + 1 ≤ n) :
    tdot_lemFuel n acc l = tdot acc l := tdot_measure_sufficient acc l n h
example : tlen_lemFuel 100 0 [1, 2, 3] = tlen 0 [1, 2, 3] := tlen_measure_sufficient _ _ _ (by decide)

end TestFunctionTailsCheck

#print axioms TestFunctionTailsCheck.slen_eq
#print axioms TestFunctionTailsCheck.sscale_eq
