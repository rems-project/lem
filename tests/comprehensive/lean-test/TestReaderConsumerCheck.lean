/- Hand-written pins for the reader_consumer feature (charter §4.2;
   see test_reader_consumer.lem). Lifted defs cannot be referenced
   from .lem asserts, so the lifted-path behavior is pinned here
   (kernel-checked rfl) and re-asserted compiled in
   TestReaderConsumerExec.lean. -/

import Test_reader_consumer

/- signature pins: lifted callers take the reader binder; the seed def
   takes the seed explicitly and is NOT lifted -/
example : Nat → Nat → Nat := uses_scaled
example : Nat → Nat → Nat := seed_entry
example : Nat → Nat := via_seed

/- consumer call from a lifted def: the binder reaches the rep's
   leading parameter -/
example : uses_scaled 9 3 = 903 := rfl
example : uses_scaled_and_cfg 9 3 = 912 := rfl

/- bare/HOF reference: partial application over the reader binder -/
example : maps_scaled 9 [1, 2] = [901, 902] := rfl

/- reader_seed pickup: inside seed_entry the consumer receives the
   SEED argument (7), including through the lifted callee -/
example : seed_entry 7 3 = 1407 := rfl
example : via_seed 3 = 1407 := rfl
