import Test_unreferenced_binders

/-! Pins for the unreferenced-binder rule (TODO item 54, 2026-11-07;
    doc/lean-backend/2026-11-07_unreferenced-binders-record.md): the
    rendered binder NAMES through Lean's named-argument syntax — a binder
    the rule renamed is `_<name>` here, a referenced or kept one is its
    source name, and either spelled the other way is a build error — and
    the values through the renamed binders, by `rfl`/`decide` (the kernel
    computes through the derived comparisons and the fuel'd worker). -/

-- the def's unreferenced parameter is `_y`; the referenced `x` keeps its name
example : def_params (x := 1) (_y := 2) = 1 := rfl
-- the fuel'd worker keeps `tag` (the sentinel's text names it) and `n`
example : loop_lemFuel (lemFuel := 3) (tag := 9) (n := 2) = 0 := rfl
example : loop_lemFuel 0 9 2 = fuelExhausted 9 := loop_lemFuel_zero 9 2
-- a source name already spelled `_x` is left as it is, unreferenced or referenced (review F1)
example : keep_us (_x := 1) (y := 2) = 2 := rfl
example : use_us (_x := 1) = 2 := rfl
-- the kept names protect the clause head only (review F3): the nested binders are underscored
example : loop_arm_lemFuel (lemFuel := 2) (tag := 9) (o := some 4) = 0 := rfl
example : slen [1, 2, 3] = 3 := by decide
-- values through the renamed binders
example : match_arm (some 5) = 0 := rfl
example : match_arm none = 1 := rfl
example : tuple_arm (1, (2, 3)) = 4 := rfl
example : let_pattern (1, 2) = 1 := rfl
example : as_pattern (1, 2) = (1, 4) := rfl
example : shadowed 1 = 5 := rfl
example : eq_clauses 0 9 = 1 := rfl
example : eq_clauses 4 9 = 4 := rfl
example : ta = 3 := rfl
example : tb = 4 := rfl
-- the derived comparisons compute in the kernel, with and without a clause
example : (NB 1 true == NB 1 true) = true := by decide
example : (NA 1 == NB 1 true) = false := by decide
example : (RNode (RNode RLeaf 1) 2 == RNode (RNode RLeaf 1) 2) = true := by decide
example : (MC (MA_node MA_leaf 3) 4 == MC MA_leaf 4) = false := by decide
example : (ONode (some (ONode none)) == ONode (some (ONode none))) = true := by decide
example : (compare (ONode (some OLeaf)) (ONode none)) = Ordering.gt := by decide
-- the derived sizes: the recursive member and the one that only calls it
example : rec_t.lemSize (RNode (RNode RLeaf 1) 2) = 3 := by decide
example : mC.lemSize (MC (MA_node MA_leaf 3) 4) = 3 := by decide
example : ot.lemSize (ONode (some (ONode none))) = 3 := by decide
