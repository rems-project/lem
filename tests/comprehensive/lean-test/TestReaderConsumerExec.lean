/- Compiled-binary behavioral test for reader_consumer (charter §4.2;
   suite phase lean-reader-consumer): re-asserts in compiled code that
   consumer call sites receive the reader value — through a lifted
   caller, through a bare/HOF partial application, and through the
   reader_seed override (the seed argument, not a binder). -/

import Test_reader_consumer

def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    IO.println s!"  ok: {name}"
  else
    IO.println s!"  FAIL: {name}"
  pure ok

def main : IO UInt32 := do
  let r1 ← check "uses_scaled 9 3 = 903 [lifted caller injects]"
    (uses_scaled 9 3 == 903)
  let r2 ← check "uses_scaled_and_cfg 9 3 = 912 [consumer + direct read]"
    (uses_scaled_and_cfg 9 3 == 912)
  let r3 ← check "maps_scaled 9 [1,2] = [901,902] [HOF partial application]"
    (maps_scaled 9 [1, 2] == [901, 902])
  let r4 ← check "via_seed 3 = 1407 [reader_seed pickup through consumer + lifted callee]"
    (via_seed 3 == 1407)
  if r1 && r2 && r3 && r4 then
    IO.println "reader_consumer: OK"
    return 0
  else
    IO.println "reader_consumer: FAILED"
    return 1
