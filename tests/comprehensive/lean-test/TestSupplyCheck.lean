/- Hand-written pins for the supply-lifting feature (effect-retirement
   arc; see test_supply.lem / test_supply_multi.lem). A lifted def
   cannot be referenced from a .lem assert (the fail-closed net rejects
   supply constants outside threaded code at generation time), so the
   draw-sequence and signature pins live here.

   The `example ... := rfl` rows are KERNEL-checked draw-order pins:
   the transform sequences draws in the OCAML TARGET's evaluation order
   (parity-fix F6, 2026-09-03: right-to-left within tuples, argument
   lists, list literals, constructor/record fields, infix operands;
   let/if/match as written), with exact successor numbering —
   supplySplit s = (s, s+1), nothing skipped. Every value below is
   quoted from the compiled OCaml reference run of the same shapes
   (tests/comprehensive/parity/expected/p_supply_shapes.out, the
   two-target pin; e.g. "draw_list 5 = [6; 5] @ 7"). -/

import Test_supply
import Test_supply_multi

/- === signature pins: binder order is [readers] [supply] [args];
   result is the value×supply pair === -/
example : Nat → Unit → (Nat × Nat) × Nat := draw_two
example : Nat → Nat → Unit → Nat × Nat := both        -- reader THEN supply
example : Nat → Nat → Nat → Nat × Nat := seeded       -- supply then seed arg
example : Nat → Nat → List Nat × Nat := @fuel_draws ⟨100⟩    -- wrapper (at a caller fuel): supply then arg
example : Nat → Nat → Unit → (Nat × Nat × Nat) × Nat × Nat := two_streams

/- === draw-sequence pins (kernel-checked, exact numbering) === -/
example : draw_two 100 () = ((100, 101), 102) := rfl
example : draw_list 5 () = ([6, 5], 7) := rfl            -- OCaml: draw_list 5 = [6; 5] @ 7
example : mk_wrap 3 () = (Wrap 4 3, 5) := rfl            -- OCaml: mk_wrap 3 = Wrap 4 3 @ 5
example : mk_srec 7 () = ({ ra := 8, rb := 7 }, 9) := rfl -- OCaml: mk_srec 7 = (8, 7) @ 9
example : read_ra 7 () = (8, 9) := rfl                   -- OCaml: read_ra 7 = 8 @ 9
example : sum_two 10 () = (21, 12) := rfl

/- control forms: only the taken branch consumes -/
example : branchy 50 true = (50, 51) := rfl
example : branchy 50 false = (0, 50) := rfl
example : matchy 20 (some 5) = (25, 21) := rfl
example : matchy 20 none = (20, 21) := rfl

/- short-circuit && / || (audit MAJOR-1, charter O1): right-operand
   draws fire ONLY on the evaluating branch — the short-circuit path
   leaves the supply untouched; the left operand is strict -/
example : sc_and 10 false = (false, 10) := rfl   -- short-circuit: no draw
example : sc_and 7 true = (true, 8) := rfl       -- right draws 7 (= 7)
example : sc_and 10 true = (false, 11) := rfl    -- right draws 10 (≠ 7)
example : sc_or 10 true = (true, 10) := rfl      -- short-circuit: no draw
example : sc_or 7 false = (true, 8) := rfl       -- right draws 7 (= 7)
example : sc_or 10 false = (false, 11) := rfl    -- right draws 10 (≠ 7)
example : sc_both 1 () = (false, 3) := rfl       -- left draws 1 (=1), right draws 2
example : sc_both 5 () = (false, 6) := rfl       -- left draws 5 (≠1): ONE draw only
example : sc_nested 10 true false = (true, 10) := rfl   -- outer || short-circuits
example : sc_nested 10 false false = (false, 10) := rfl -- inner && short-circuits
example : sc_nested 10 false true = (false, 11) := rfl  -- inner right draws 10
example : sc_nested 5 false true = (true, 6) := rfl     -- inner right draws 5 (= 5)
example : sc_imp 10 false = (true, 10) := rfl    -- vacuous antecedent: no draw
example : sc_imp 7 true = (true, 8) := rfl       -- consequent draws 7 (= 7)
example : sc_imp 10 true = (false, 11) := rfl    -- consequent draws 10 (≠ 7)

/- PAREN-SPLIT spine strictness pins (L1 delta audit NOTE-1; the
   registered L2 rider): `((&&) a) (chk 4)` renders through the
   general-head branch (strip_app_exp does not unwrap Paren), so the
   argument threads STRICTLY — the draw fires even when a = false.
   Oracle-faithful: OCaml is strict on exactly this eta-expanded
   shape (the flat form short-circuits on both targets — contrast
   the sc_and pins above). These rows pin the strict behavior so any
   future spine normalization (which would silently change the
   threading class) fails HERE, loudly. -/
example : prefsc_paren 10 false = (false, 11) := rfl -- STRICT: draws despite a = false
example : prefsc_paren 10 true = (false, 11) := rfl  -- draws 10 (≠ 4)
example : prefsc_paren 4 true = (true, 5) := rfl     -- draws 4 (= 4)
example : chk 10 4 = (false, 11) := rfl              -- the drawing argument itself

/- multi-clause source (pattern-compiled to one match) threads -/
example : clausy 20 (some 5) = (25, 21) := rfl
example : clausy 20 none = (20, 21) := rfl

/- threaded calls / transitive lifting -/
example : uses_draw_two 100 7 = (208, 102) := rfl

/- destructuring RHS evaluates once: pair_draw's two draws happen
   exactly once, then c draws the next id (a duplicated RHS would give
   c = 34, not 32) -/
example : pair_draw 30 () = ((31, 30), 32) := rfl           -- OCaml: pair_draw 30 = (31, 30) @ 32
example : destructure_once 30 () = ((31, 30, 32), 33) := rfl -- OCaml: destructure_once 30 = [31; 30; 32] @ 33

/- a draw under a target_rep'd library constructor (F5: `Just` = `some`) -/
example : mk_just 40 () = (some (41, 40), 42) := rfl        -- OCaml: mk_just 40 = Just ((41, 40)) @ 42

/- top-level VALUE bindings that draw are REFUSED (F6 / deviation-4:
   OCaml evaluates them once at module initialisation);
   negative/neg_supply_toplevel_value.lem pins the refusal -/

/- reader × supply composition (reader injected, supply threaded) -/
example : both 9 40 () = (49, 41) := rfl
example : uses_both 9 40 3 = (52, 41) := rfl

/- reader_seed × supply: the seed argument (42) feeds the reader
   injections; the supply threads through the seed def's own binder -/
example : seeded 40 42 3 = (85, 41) := rfl
example : uses_seeded 40 3 = (85, 41) := rfl

/- fuel × supply: the worker threads the supply through the
   decremented self-call; `tick () :: fuel_draws (n - 1)` evaluates the
   recursive call FIRST (OCaml: cons arguments right-to-left), so the
   draws come out descending -/
example : @fuel_draws ⟨100⟩ 60 2 = ([61, 60], 62) := rfl              -- OCaml: fuel_draws 60 = [61; 60] @ 62
example : @uses_fuel_draws ⟨100⟩ 60 2 = ([62, 61, 60], 63) := rfl    -- OCaml: uses_fuel_draws 60 = [62; 61; 60] @ 63
/- the fuel is the caller's ([LemFuel], fuel-parameter arc): the wrapper
   is the worker at the ambient, and the lifted caller carries the same
   instance -/
example : Nat → Nat → List Nat × Nat := @fuel_draws ⟨100⟩
example : @fuel_draws ⟨100⟩ = fuel_draws_lemFuel 100 := rfl
example : @fuel_draws ⟨7⟩ 60 2 = @fuel_draws ⟨100⟩ 60 2 := rfl
/- fuel exhaustion returns the sentinel with the supply UNCONSUMED at
   the exhaustion point (one draw happened before fuel ran out) -/
example : fuel_draws_lemFuel 1 60 2 = ([60], 61) := rfl
/- exhaustion mid-stream at an INSUFFICIENT caller fuel (3) on depth 5
   (a Lean-only observation — the OCaml reference has no fuel): the
   worker exhausts after descending 3 levels, returns the sentinel []
   with the supply unconsumed (60), then the 3 pending conses draw on
   the way back up — 60, 61, 62 — in the OCaml cons order -/
example : @fuel_draws ⟨3⟩ 60 5 = ([62, 61, 60], 63) := rfl

/- === multi-supply ordering (test_supply_multi.lem): binders sorted
   by name (tick before tock); each draw advances only its own
   stream; result states in the same order === -/
example : two_streams 10 100 () = ((10, 100, 11), 12, 101) := rfl
example : uses_two_streams 10 100 () = ((11, 101, 12), 12, 101) := rfl
