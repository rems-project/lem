import P_fuel
-- Lean driver for p_fuel: `results` is fuel-lifted (`[LemFuel]`); it is
-- evaluated at two different sufficient fuels and both blocks printed —
-- the reference prints its (fuel-free) block twice.
def main : IO Unit := do
  (@results ⟨200⟩).forM IO.println
  (@results ⟨100000⟩).forM IO.println
