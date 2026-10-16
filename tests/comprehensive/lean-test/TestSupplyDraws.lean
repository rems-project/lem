/- Compiled-binary behavioral test for the supply-lifting feature
   (effect-retirement arc; suite phase lean-supply-draws). The
   elaborator pins live in TestSupplyCheck.lean; this binary re-asserts
   the load-bearing draw sequences in COMPILED code — the class of
   evidence the 2026-08-31 backend quality review found missing
   (interpreter/compiler divergences are invisible to elaborator
   asserts). Witnessed here:

   1. draw sequencing: successor numbering in the OCaml target's
      evaluation order (parity-fix F6: right-to-left within one node,
      let chains as written) through let chains, argument hoisting,
      and threaded calls — values quoted from the OCaml reference run
      (tests/comprehensive/parity/expected/p_supply_shapes.out);
   2. single evaluation: a destructuring RHS's draws happen exactly
      once per call (destructure_once's third draw is s+2);
   3. fuel × supply: the worker threads the supply through the
      decremented self-call, and exhaustion returns the supply
      unconsumed at the exhaustion point;
   4. multi-supply: independent streams advance independently, in
      sorted binder order. -/

import Test_supply
import Test_supply_multi

def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    IO.println s!"  ok: {name}"
  else
    IO.println s!"  FAIL: {name}"
  pure ok

def main : IO UInt32 := do
  let r1 ← check "draw_two 100 () = ((100, 101), 102)"
    (draw_two 100 () == ((100, 101), 102))
  let r2 ← check "destructure_once 30 () = ((31, 30, 32), 33) [RHS draws once; OCaml order]"
    (destructure_once 30 () == ((31, 30, 32), 33))
  let r3 ← check "mk_just 40 () = (some (41, 40), 42) / draw_list 5 () = ([6, 5], 7) [rep'd ctor arg; right-to-left]"
    (mk_just 40 () == (some (41, 40), 42) && draw_list 5 () == ([6, 5], 7))
  let r4 ← check "uses_both 9 40 3 = (52, 41) [reader x supply]"
    (uses_both 9 40 3 == (52, 41))
  let r5 ← check "uses_seeded 40 3 = (85, 41) [reader_seed x supply]"
    (uses_seeded 40 3 == (85, 41))
  let r6 ← check "fuel_draws 60 2 at fuel 100 = ([61, 60], 62) [fuel x supply; OCaml cons order]"
    (@fuel_draws ⟨100⟩ 60 2 == ([61, 60], 62))
  let r7 ← check "fuel_draws_lemFuel 1 60 2 = ([60], 61) [exhaustion leaves supply at cut]"
    (fuel_draws_lemFuel 1 60 2 == ([60], 61))
  let r8 ← check "two_streams 10 100 () = ((10, 100, 11), 12, 101) [independent streams]"
    (two_streams 10 100 () == ((10, 100, 11), 12, 101))
  let r9 ← check "sc_and 10 false = (false, 10) / sc_or 10 true = (true, 10) [short-circuit: no draw]"
    (sc_and 10 false == (false, 10) && sc_or 10 true == (true, 10))
  let r10 ← check "sc_and 10 true = (false, 11) / sc_or 10 false = (false, 11) [evaluating branch draws]"
    (sc_and 10 true == (false, 11) && sc_or 10 false == (false, 11))
  let r11 ← check "sc_both 5 () = (false, 6) [left strict, right short-circuited]"
    (sc_both 5 () == (false, 6))
  let r12 ← check "sc_nested 10 false true = (false, 11) / sc_nested 10 false false = (false, 10) [nested]"
    (sc_nested 10 false true == (false, 11) && sc_nested 10 false false == (false, 10))
  if r1 && r2 && r3 && r4 && r5 && r6 && r7 && r8 && r9 && r10 && r11 && r12 then
    IO.println "supply draws: OK"
    return 0
  else
    IO.println "supply draws: FAILED"
    return 1
