/- Hand-written classes and consumer implementations for
   test_instance_reader.lem (instance-reader slice, 2026-10-05).

   `declare {lean} reader val sw = instance `TestInstanceReaderImpl.Sw.sw``
   names the PROJECTION of the one-field class `Sw`; every generated
   definition that reads `sw` binds `[Sw]` and reads `Sw.sw`. The
   consumers bind the class themselves (no argument is passed at their
   call sites). No instance is declared here or anywhere in generated
   code: the pins supply them (`@f ⟨v⟩ …`, `letI`). -/
import LemLib

namespace TestInstanceReaderImpl

class Sw where
  sw : Nat

class Md where
  md : Bool

/-- `declare {lean} reader_consumer val scaled_i = instance sw` -/
def scaledI [Sw] (x : Nat) : Nat := Sw.sw * 100 + x

/-- explicit reader (leading argument), instance reader and fuel at once:
    `reader_consumer val both_c`, `reader_consumer val both_c = instance
    sw`, `fuel_consumer val both_c` -/
def bothC [LemFuel] [Sw] (cfg : Nat) (x : Nat) : Nat :=
  LemFuel.fuel * 10000 + Sw.sw * 100 + cfg * 10 + x

end TestInstanceReaderImpl
