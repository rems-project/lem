/- Hand-written pins for instance-implicit readers (instance-reader
   slice, 2026-10-05; see test_instance_reader.lem). A lifted definition
   cannot be referenced from a .lem assert (no instance there), so the
   lifted behaviour is pinned here: SIGNATURE pins (binder kind and the
   documented order `[LemFuel]`, instance readers in lem-name order,
   `[Inhabited]`, fuel counter, explicit readers, supply, arguments) and
   KERNEL pins (`rfl`) of instance-bound definitions at concrete instances
   (`@f ⟨v⟩ …`, `letI`). No instance is declared anywhere: each pin
   supplies its own. Re-asserted compiled in TestInstanceReaderExec.lean. -/
import Test_instance_reader
import Test_instance_reader_auxiliary

open TestInstanceReaderImpl

/- ---- signature pins: binder kind and order ---- -/
-- (1) simple / (2) transitive lifting
example : [Sw] → Nat → Nat := @get_sw
example : [Sw] → Nat → Nat := @calls_get_sw
-- not lifted
example : Nat → Nat := plain
example : [Sw] → Nat → Nat := @via_bare
example : [Sw] → Nat := @sw_plus_one
example : [Sw] → Nat → Nat := @mc
example : [Sw] → Nat := @sw_a
example : [Sw] → Nat := @sw_b
-- two instance readers: global order by lem name (md before sw)
example : [Md] → [Sw] → Nat → Nat := @both_readers
-- (3) consumers: callers bind the class; the explicit reader stays an
-- explicit leading parameter AFTER the instance binders
example : [Sw] → Nat → Nat := @uses_scaled_i
example : [Sw] → List Nat → List Nat := @maps_scaled_i
example : [LemFuel] → [Sw] → Nat → Nat → Nat := @uses_both_c
-- (4) the seed def binds [Sw] itself; its seed argument is the EXPLICIT
-- reader's only (N counts explicit readers)
example : [Sw] → Nat → Nat → Nat := @seed_entry
example : [Sw] → Nat → Nat := @via_seed
example : Nat → Nat → Nat := seed_plain
example : Nat → Nat := via_seed_plain
-- (5) mutual blocks: every member binds (all-or-none)
example : [Sw] → List Nat → Bool := @iev
example : [Sw] → List Nat → Bool := @iodd
example : [Sw] → Nat → Nat → Nat := @rping_lemFuel
example : [Sw] → Nat → Nat → Nat := @rpong_lemFuel
example : [LemFuel] → [Sw] → Nat → Nat := @rping
example : [LemFuel] → [Sw] → Nat → Nat := @uses_rping
-- (6) coexistence: [LemFuel] [Sw] on the wrapper; the worker: [Sw], the
-- counter, the explicit reader, the argument
example : [Sw] → Nat → Nat → Nat → Nat := @mixed_lemFuel
example : [LemFuel] → [Sw] → Nat → Nat → Nat := @mixed
-- measured: fuel-free wrapper, still [Sw]
example : [Sw] → List Nat → Nat := @ilen
-- supply: the supply binder after the instance binder
example : [Sw] → Nat → Unit → (Nat × Nat) × Nat := @draw_sw
-- the `_zero` lemmas and the measure obligation carry the binder
example [Sw] (n : Nat) : rping_lemFuel 0 n = 991 := rping_lemFuel_zero n
example [Sw] (c n : Nat) : mixed_lemFuel 0 c n = 999 := mixed_lemFuel_zero c n
example [Sw] (l : List Nat) (k : Nat) (h : List.length l + 1 ≤ k) :
    ilen_lemFuel k l = ilen l := ilen_measure_sufficient l k h

/- ---- kernel pins: instance-bound definitions at concrete instances ---- -/
example : @get_sw ⟨5⟩ 3 = 8 := rfl
example : @calls_get_sw ⟨5⟩ 3 = 16 := rfl
example : @calls_get_sw ⟨5⟩ = fun x => (5 + x) * 2 := rfl
example : (letI : Sw := ⟨5⟩; calls_get_sw 3) = 16 := rfl
example : @via_bare ⟨5⟩ 3 = 8 := rfl
example : @sw_plus_one ⟨5⟩ = 6 := rfl
example : @sw_a ⟨5⟩ = 5 := rfl
example : @sw_b ⟨5⟩ = 6 := rfl
example : @mc ⟨5⟩ 0 = 5 := rfl
example : @mc ⟨5⟩ 7 = 7 := rfl
example : @both_readers ⟨true⟩ ⟨5⟩ 3 = 8 := rfl
example : @both_readers ⟨false⟩ ⟨5⟩ 3 = 3 := rfl
example : @uses_scaled_i ⟨5⟩ 3 = 503 := rfl
example : @maps_scaled_i ⟨5⟩ [1, 2] = [501, 502] := rfl
example : @uses_both_c ⟨2⟩ ⟨5⟩ 9 3 = 20593 := rfl
example : @seed_entry ⟨5⟩ 7 3 = 18 := rfl
example : @via_seed ⟨5⟩ 3 = 18 := rfl
example : seed_plain 7 3 = 10 := rfl
example : @iev ⟨0⟩ [1, 2] = true := rfl
example : @iev ⟨1⟩ [1, 2] = false := rfl
example : @iev ⟨0⟩ [1] = false := rfl
example : @rping ⟨10⟩ ⟨7⟩ 3 = 0 := rfl
example : @rping ⟨10⟩ ⟨8⟩ 3 = 1 := rfl
example : @rping_lemFuel ⟨7⟩ 3 3 = 992 := rfl
example : @uses_rping ⟨10⟩ ⟨7⟩ 3 = 0 := rfl
example : @mixed ⟨10⟩ ⟨5⟩ 2 4 = 2005 := rfl
example : @mixed ⟨2⟩ ⟨5⟩ 2 4 = 999 := rfl
example : @ilen ⟨5⟩ [1, 2, 3] = 8 := rfl
example : @draw_sw ⟨5⟩ 10 () = ((10, 5), 11) := rfl

/- ---- quantification: bind the instance in a theorem ---- -/
theorem get_sw_spec [Sw] (x : Nat) : get_sw x = Sw.sw + x := rfl
theorem calls_get_sw_spec [inst : Sw] (x : Nat) : calls_get_sw x = (inst.sw + x) * 2 := rfl
