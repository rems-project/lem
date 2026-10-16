/- Hand-written implementation for test_fuel_param.lem's fuel consumer
   (`declare {lean} fuel_consumer val consumer_spin`): the ambient fuel
   arrives as the instance-implicit `[LemFuel]` binder — the SAME
   parameter every generated fuel'd function reads — and the
   implementation reads it as `LemFuel.fuel`. This is the seam pattern
   for cerberus's hand-written `CerbMem` consumers (design note §4.2). -/
import LemLib

namespace TestFuelConsumerImpl

/-- reports the ambient it received, so a pin can see which fuel arrived -/
def spinAtFuel [LemFuel] (k : Nat) : Nat := LemFuel.fuel + k

end TestFuelConsumerImpl
