/- Compiled-binary pin for the m7 tuple-let single-evaluation fix
   (2026-08-31 backend quality review; see test_tuple_let_once.lem).

   The generated `let (first_draw, second_draw) = tick_pair ()` must
   evaluate its RHS once: the bound values are then exactly (1, 2).
   Under the historical RHS-per-binding duplication the second
   binding's RHS re-evaluates the impure extern call and binds
   (3, 4)'s second component, giving (1, 4). -/

import Test_tuple_let_once

def main : IO UInt32 := do
  let a := first_draw
  let b := second_draw
  IO.println s!"draws: first={a} second={b}"
  if a == 1 && b == 2 then
    IO.println "single-evaluation: OK"
    return 0
  else
    IO.println s!"single-evaluation FAILED: RHS did not run exactly once (got ({a}, {b}), want (1, 2))"
    return 1
