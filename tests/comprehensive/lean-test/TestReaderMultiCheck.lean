/- Hand-written pins for the N-ary reader_seed rule (program-data-
   parameters S0.5, 2026-09-19; see test_reader_multi.lem and
   doc/lean-backend/2026-09-19_nary-reader-seed-record.md). Lifted defs
   cannot be referenced from .lem asserts, so the lifted-path behaviour
   is pinned here (kernel-checked rfl) and re-asserted compiled in
   TestReaderMultiExec.lean.

   Readers are DECLARED gamma, alpha, beta in the .lem; the backend's
   global sorted order is alpha, beta, gamma. alpha and gamma share the
   type Nat, so every value pin below is what makes the order
   observable: TestReaderMultiImpl.combine weighs alpha 1000 and gamma
   10, and the .lem bodies weigh alpha above gamma too. -/

import Test_reader_multi

/- signature pins: lifted defs take the three reader binders (alpha :
   Nat) (beta : String) (gamma : Nat) in that order, then their own
   argument; the binder NAMES are pinned through named arguments -/
example : Nat → String → Nat → Nat → Nat := uses_one
example : Nat → String → Nat → Nat → Nat := uses_two
example : Nat → String → Nat → Nat → Nat := uses_three
example : Nat → String → Nat → Nat → Nat := uses_combine
example : uses_one (_lemReader_alpha := 7) (_lemReader_beta := "ab") (_lemReader_gamma := 9) 3 = 12 := rfl

/- readers THEN the supply binder, then own args (a supply-lifted def in
   the reader cone) -/
example : Nat → String → Nat → Nat → Nat → Nat × Nat := draws_and_reads
example : draws_and_reads (_lemReader_alpha := 7) (_lemReader_beta := "ab")
            (_lemReader_gamma := 9) (_lemSupply_tick := 40) 3 = (7333, 41) := rfl

/- the seed def is NOT lifted: its own three seeds (av bv gv, sorted
   reader order), then x; the supply-lifted seed def puts the supply
   binder first, then the seeds -/
example : Nat → String → Nat → Nat → Nat := seed3
example : seed3 (av := 7) (bv := "ab") (gv := 9) 3 = 8110 := rfl
example : Nat → Nat → String → Nat → Nat → Nat × Nat := seed3_draws
example : seed3_draws (_lemSupply_tick := 40) (av := 7) (bv := "ab") (gv := 9) 3 = (7333, 41) := rfl
example : Nat → Nat := via_seed3

/- value pins through the lifted path: binder order alpha, beta, gamma
   (under the declaration order gamma, alpha, beta these would read
   uses_two 7 "ab" 9 3 = 90 + 7 + 3 = 100, not 82) -/
example : uses_one 7 "ab" 9 3 = 12 := rfl
example : uses_two 7 "ab" 9 3 = 82 := rfl
example : uses_three 7 "ab" 9 3 = 732 := rfl

/- consumer call from a lifted def: the three binders reach the rep's
   leading parameters in order; the alpha/gamma swap is observable -/
example : uses_combine 7 "ab" 9 3 = 7293 := rfl
example : uses_combine 9 "ab" 7 3 = 9273 := rfl
example : uses_combine 7 "ab" 9 3 ≠ uses_combine 9 "ab" 7 3 := by decide

/- N-ary seed pickup: inside seed3 every injection site — the consumer
   call AND the two lifted callees — receives the seed associated with
   ITS reader (av → alpha, bv → beta, gv → gamma); this is the pin that
   FAILS under an alpha/gamma seed swap (10306 ≠ 8110) -/
example : seed3 7 "ab" 9 3 = 8110 := rfl
example : seed3 7 "ab" 9 3 = uses_combine 7 "ab" 9 3 + uses_three 7 "ab" 9 4 + uses_two 7 "ab" 9 5 := rfl
example : seed3 9 "ab" 7 3 = 10306 := rfl
example : seed3 7 "ab" 9 3 ≠ seed3 9 "ab" 7 3 := by decide
example : via_seed3 3 = 8110 := rfl

/- seed × supply: the seeds reach the supply-lifted callee's reader
   binders; the supply threads as usual -/
example : seed3_draws 40 7 "ab" 9 3 = (7333, 41) := rfl
example : seed3_draws 40 7 "ab" 9 3 = draws_and_reads 7 "ab" 9 40 3 := rfl

/- axiom census (charter §4: the trio or fewer — here none: plain defs) -/
#print axioms via_seed3
#print axioms uses_three
