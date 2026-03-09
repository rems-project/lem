/- Stub Pervasives_extra for the Lean backend.
   This file will be replaced by the version generated from
   pervasives_extra.lem via `make lean-libs`, then restored via
   `git checkout lean-lib/LemLib/Pervasives_extra.lean`. -/
import LemLib
import LemLib.Pervasives

/- Bridge Lem's numeric classes to Lean's operator typeclasses.
   Lem's NumAdd/NumMinus/NumMult classes don't extend Lean's Add/Sub/Mul,
   so we provide these bridges so that `+`, `-`, `*` operators work. -/
instance [Lem_Num.NumAdd α] : Add α where add := Lem_Num.numAdd
instance [Lem_Num.NumMinus α] : Sub α where sub := Lem_Num.numMinus
instance [Lem_Num.NumMult α] : Mul α where mul := Lem_Num.numMult
instance [Lem_Num.NumNegate α] : Neg α where neg := Lem_Num.numNegate

namespace Lem_Pervasives_extra

/- Pervasives_extra definitions go here when generated.
   Currently empty — all needed definitions are in LemLib
   and LemLib.Pervasives. -/

end Lem_Pervasives_extra
