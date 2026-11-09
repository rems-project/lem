/- Compiled-binary behavioral test for the N-ary reader_seed rule
   (program-data-parameters S0.5, 2026-09-19; suite phase
   lean-reader-multi): re-asserts in compiled code that with three
   declared readers (declared gamma, alpha, beta; sorted alpha, beta,
   gamma) the lifted binders are in sorted order, that inside a seed
   def every injection site receives the seed associated with ITS
   reader (through the consumer and through lifted callees), that an
   alpha/gamma swap is observable by value, and that seeding composes
   with supply lifting. -/

import Test_reader_multi

def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    IO.println s!"  ok: {name}"
  else
    IO.println s!"  FAIL: {name}"
  pure ok

def main : IO UInt32 := do
  let r1 ← check "uses_two 7 \"ab\" 9 3 = 82 [lifted binders in sorted order alpha, beta, gamma]"
    (uses_two 7 "ab" 9 3 == 82)
  let r2 ← check "uses_three 7 \"ab\" 9 3 = 732 [all three readers read]"
    (uses_three 7 "ab" 9 3 == 732)
  let r3 ← check "uses_combine 7 \"ab\" 9 3 = 7293 [lifted caller injects three binders into the consumer]"
    (uses_combine 7 "ab" 9 3 == 7293)
  let r4 ← check "uses_combine 9 \"ab\" 7 3 = 9273 [alpha/gamma swap observable by value]"
    (uses_combine 9 "ab" 7 3 == 9273 && uses_combine 9 "ab" 7 3 != uses_combine 7 "ab" 9 3)
  let r5 ← check "via_seed3 3 = 8110 [N-ary seed pickup: consumer + two lifted callees, per reader]"
    (via_seed3 3 == 8110)
  let r6 ← check "seed3 9 \"ab\" 7 3 = 10306 <> 8110 [a seed swap changes the value]"
    (seed3 9 "ab" 7 3 == 10306 && seed3 9 "ab" 7 3 != seed3 7 "ab" 9 3)
  let r7 ← check "draws_and_reads 7 \"ab\" 9 40 3 = (7333, 41) [readers, supply, own args]"
    (draws_and_reads 7 "ab" 9 40 3 == (7333, 41))
  let r8 ← check "seed3_draws 40 7 \"ab\" 9 3 = (7333, 41) [seed x supply: supply, seeds, own args]"
    (seed3_draws 40 7 "ab" 9 3 == (7333, 41))
  if r1 && r2 && r3 && r4 && r5 && r6 && r7 && r8 then
    IO.println "reader_multi: OK"
    return 0
  else
    IO.println "reader_multi: FAILED"
    return 1
