/- Stub Pervasives_extra for testing -/
import LemLib

namespace Pervasives_extra

-- Type class stubs for generated code
class NumAdd (a : Type) extends Add a where

instance : NumAdd Nat where
  add := Nat.add

class SetType (a : Type) where
  setElemCompare : a → a → LemOrdering

instance {a : Type} [SetType a] : BEq a where
  beq x y := match SetType.setElemCompare x y with | .EQ => true | _ => false

-- natLtb, natGtb, setAdd already in LemLib

end Pervasives_extra
