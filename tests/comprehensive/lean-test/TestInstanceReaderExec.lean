/- Compiled pin for instance-implicit readers (instance-reader slice,
   2026-10-05; suite phase lean-instance-reader): the instance supplied at
   the entry point — chosen at RUNTIME from the argument count, so the
   compiler cannot fold it — reaches every lifted definition, through the
   transitive callee, the consumer, the seed def, the fuel'd mutual block
   and the coexistence def (kernel pins: TestInstanceReaderCheck.lean). -/
import Test_instance_reader

open TestInstanceReaderImpl

def check (name : String) (got want : Nat) : IO Bool := do
  if got == want then pure true
  else
    IO.println s!"FAIL: {name}: got {got}, want {want}"
    pure false

/-- every pin under the ambient instances (bound here, supplied by `main`) -/
def runPins [Sw] [LemFuel] (v : Nat) : IO Bool := do
  let oks ← [
      check "get_sw" (get_sw 3) (v + 3),
      check "calls_get_sw" (calls_get_sw 3) ((v + 3) * 2),
      check "uses_scaled_i" (uses_scaled_i 3) (v * 100 + 3),
      check "via_seed" (via_seed 3) (10 + v + 3),
      check "uses_both_c" (uses_both_c 9 3) (100000 + v * 100 + 93),
      check "rping" (rping 3) (if (v - 3) % 2 == 0 then 0 else 1),
      check "mixed" (mixed 2 4) (2000 + v),
      check "ilen" (ilen [1, 2, 3]) (3 + v)
    ].mapM id
  pure (oks.all id)

def main (args : List String) : IO UInt32 := do
  let v := 5 + args.length          -- 5 when run without arguments
  -- the entry point supplies both instances (no instance exists elsewhere)
  if (← @runPins ⟨v⟩ ⟨10⟩ v) then
    IO.println "instance reader: OK"
    pure 0
  else pure 1
