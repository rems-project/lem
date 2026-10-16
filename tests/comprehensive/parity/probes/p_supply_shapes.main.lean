import P_supply_shapes
-- Lean driver: each shape is supply-lifted (seed) (unit) → (string, final);
-- print exactly the reference driver's line. The fuel'd shapes are
-- fuel-lifted: the driver (a test harness) instantiates the ambient once.
instance : LemFuel := ⟨1000⟩
def shape (name : String) (seed : Nat) (f : Nat → Unit → String × Nat) : IO Unit :=
  let (v, s) := f seed ()
  IO.println s!"{name} {seed} = {v} @ {s}"
def main : IO Unit := do
  shape "draw_two" 100 s_draw_two
  shape "draw_list" 5 s_draw_list
  shape "mk_wrap" 3 s_mk_wrap
  shape "mk_srec" 7 s_mk_srec
  shape "mk_srec_rev" 7 s_mk_srec_rev
  shape "read_ra" 7 s_read_ra
  shape "sum_two" 10 s_sum_two
  shape "branchy_t" 50 s_branchy_t
  shape "branchy_f" 50 s_branchy_f
  shape "matchy_j" 20 s_matchy_j
  shape "matchy_n" 20 s_matchy_n
  shape "sc_and_f" 10 s_sc_and_f
  shape "sc_and_t" 10 s_sc_and_t
  shape "sc_and_t" 7 s_sc_and_t
  shape "sc_or_t" 10 s_sc_or_t
  shape "sc_or_f" 10 s_sc_or_f
  shape "sc_or_f" 7 s_sc_or_f
  shape "sc_both" 1 s_sc_both
  shape "sc_both" 5 s_sc_both
  shape "sc_nested_ft" 10 s_sc_nested_ft
  shape "sc_nested_ff" 10 s_sc_nested_ff
  shape "sc_nested_ft" 5 s_sc_nested_ft
  shape "sc_imp_f" 10 s_sc_imp_f
  shape "sc_imp_t" 7 s_sc_imp_t
  shape "sc_imp_t" 10 s_sc_imp_t
  shape "prefsc_paren_f" 10 s_prefsc_paren_f
  shape "prefsc_paren_t" 10 s_prefsc_paren_t
  shape "prefsc_paren_t" 4 s_prefsc_paren_t
  shape "uses_draw_two" 100 s_uses_draw_two
  shape "pair_draw" 30 s_pair_draw
  shape "destructure_once" 30 s_destructure_once
  shape "mk_just" 40 s_mk_just
  shape "fuel_draws" 60 s_fuel_draws
  shape "uses_fuel_draws" 60 s_uses_fuel_draws
