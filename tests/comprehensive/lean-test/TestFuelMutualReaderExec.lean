/- Compiled-binary behavioural test for fuel x reader x truly-mutual
   blocks (program-data-parameters S1.5, 2026-09-20; suite phase
   lean-fuel-mutual-reader): re-asserts in compiled code that inside a
   fuel'd mutual block the reader value reaches every member (both-read,
   one-read), that sibling hops pass the decremented counter (the sentinel
   of the member hitting 0), that a fuel'd callee reached from a member
   starts from the FULL ambient, and that the measured pair's fuel-free
   wrappers follow the reader. -/

import Test_fuel_mutual_reader

def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    IO.println s!"  ok: {name}"
  else
    IO.println s!"  FAIL: {name}"
  pure ok

def main : IO UInt32 := do
  let r1 ← check "rping 3 at amb 7, fuel 100 = 0 [both members read the reader; 4 hops]" (@rping ⟨100⟩ 7 3 == 0)
  let r2 ← check "rping 3 at amb 8, fuel 100 = 1 [the reader decides which member reaches it]" (@rping ⟨100⟩ 8 3 == 1)
  let r3 ← check "rping 3 at amb 7, fuel 3 = 992 [sibling hop exhausts: rpong's sentinel]" (@rping ⟨3⟩ 7 3 == 992)
  let r4 ← check "rping 3 at amb 7, fuel 4 = 991 [rping's sentinel]" (@rping ⟨4⟩ 7 3 == 991)
  let r5 ← check "uses_rping 3 at amb 7 = 0 [lifted caller injects into the wrapper]" (@uses_rping ⟨100⟩ 7 3 == 0)
  let r6 ← check "opong 3 at amb 7 = 7 [non-reading member lifted, threads the value]" (@opong ⟨100⟩ 7 3 == 7)
  let r7 ← check "oping 4 at amb 9 = 9 / oping 3 at amb 9 = 1" (@oping ⟨100⟩ 9 4 == 9 && @oping ⟨100⟩ 9 3 == 1)
  let r8 ← check "fping 2 at amb 7, fuel 8 = 0 [callee starts from the FULL ambient]" (@fping ⟨8⟩ 7 2 == 0)
  let r9 ← check "fping 2 at amb 7, fuel 7 = 971 [callee exhausts at 7 < 8]" (@fping ⟨7⟩ 7 2 == 971)
  let r10 ← check "rmev 0 [1,2] = true / rmev 5 [1,2] = false / rmev 5 [1] = true [measured pair follows the reader]"
    (rmev 0 [1, 2] == true && rmev 5 [1, 2] == false && rmev 5 [1] == true)
  let r11 ← check "rmev_lemFuel 1 5 [1,2] = true [below the measure: the sibling's sentinel]" (rmev_lemFuel 1 5 [1, 2] == true)
  if r1 && r2 && r3 && r4 && r5 && r6 && r7 && r8 && r9 && r10 && r11 then
    IO.println "fuel mutual reader: OK"
    return 0
  else
    IO.println "fuel mutual reader: FAILED"
    return 1
