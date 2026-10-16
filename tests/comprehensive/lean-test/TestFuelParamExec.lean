/- Compiled-binary behavioural test for the fuel-parameter scheme (suite
   phase lean-fuel-param). Leg 1 (no arguments): two different sufficient
   fuels give identical results; an insufficient fuel gives exactly the
   declared value sentinel; a fuel'd callee starts from the full ambient;
   a fuel_consumer reads the same ambient; `letI` seeds an entry point.
   Leg 2 (`--exhaust`, run by the Makefile under LEAN_ABORT_ON_PANIC=1):
   a fuel'd function with the LOUD sentinel (`fuelExhausted n`) at an
   insufficient fuel PANICS at the program point and the process
   fail-stops — the fuel is passed at RUNTIME (`args.length`) so the
   compiler cannot fold the exhaustion into module initialisation. The
   fuel values are test-suite choices; none is baked anywhere. -/
import Test_fuel_param

def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    IO.println s!"  ok: {name}"
  else
    IO.println s!"  FAIL: {name}"
  pure ok

def main (args : List String) : IO UInt32 := do
  if args.contains "--exhaust" then
    -- leg 2: fuel = args.length (1), depth 10: exhausts, loudly
    let fuel : Nat := args.length
    IO.println s!"loud_spin 10 at fuel {fuel} = {@loud_spin ⟨fuel⟩ 10}"
    IO.println "survived: exhaustion did not abort"
    return 3
  let r1 ← check "spin 5 at fuel 6 = 0" (@spin ⟨6⟩ 5 == 0)
  let r2 ← check "spin 5 at fuel 100000 = 0 [same value at another sufficient fuel]" (@spin ⟨100000⟩ 5 == 0)
  let r3 ← check "spin 5 at fuel 5 = 999 [insufficient: the declared value sentinel]" (@spin ⟨5⟩ 5 == 999)
  let r4 ← check "uses_uses_spin 2 at fuel 100 = 2 [lifted callers]" (@uses_uses_spin ⟨100⟩ 2 == 2)
  let r5 ← check "outer 3 at fuel 4 = 0 [callee starts from the full ambient]" (@outer ⟨4⟩ 3 == 0)
  let r6 ← check "uses_consumer 1 at fuel 42 = 43 [fuel_consumer reads the ambient]" (@uses_consumer ⟨42⟩ 1 == 43)
  let r7 ← check "uses_climb 10 3 at fuel 100 (letI) = 10 [reader x fuel, entry-point seeding]"
    ((letI : LemFuel := ⟨100⟩; uses_climb 10 3) == 10)
  let r8 ← check "seeded_climb 10 3 at fuel 100 = 10 [reader_seed x fuel]" (@seeded_climb ⟨100⟩ 10 3 == 10)
  if r1 && r2 && r3 && r4 && r5 && r6 && r7 && r8 then
    IO.println "fuel param: OK"
    return 0
  else
    IO.println "fuel param: FAILED"
    return 1
