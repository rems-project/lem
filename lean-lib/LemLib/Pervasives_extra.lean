/- Stub Pervasives_extra for the Lean backend.
   In production, this file will be replaced by the version generated
   from pervasives_extra.lem via `make lean-libs`.
   This stub provides the minimal type class definitions needed by
   generated Lean files.

   Note: no namespace wrapper — generated library files are flat, and
   the import already brings definitions into scope. -/
import LemLib

/- Numeric addition class, extending Lean's built-in Add. -/
class NumAdd (a : Type) extends Add a where

instance : NumAdd Nat where
  add := Nat.add

/- Ordered set element class. Provides the comparison function used by
   LemLib's set operations (setMemberBy, setUnionBy, etc.). -/
class SetType (a : Type) where
  setElemCompare : a → a → LemOrdering

export SetType (setElemCompare)

/- Derive BEq from SetType's comparison function. -/
instance {a : Type} [SetType a] : BEq a where
  beq x y := match SetType.setElemCompare x y with | .EQ => true | _ => false
