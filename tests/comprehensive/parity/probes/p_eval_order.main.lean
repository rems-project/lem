import P_eval_order
-- run_probe is supply-lifted: (supply) (unit) → (value, final supply). Seed 0 to
-- match p_eval_order.ext.ml's first draw = 0.
def main : IO Unit := (run_probe 0 ()).1.forM IO.println
