/- Hand-written bridge instances for Lem's numeric typeclasses.
   Lem's NumAdd/NumMinus/NumMult/NumNegate classes don't extend Lean's
   Add/Sub/Mul/Neg, so these bridges let `+`, `-`, `*`, `-x` operators
   work on types with Lem numeric constraints. -/

import LemLib.Num

instance [Lem_Num.NumAdd α] : Add α where add := Lem_Num.numAdd
instance [Lem_Num.NumMinus α] : Sub α where sub := Lem_Num.numMinus
instance [Lem_Num.NumMult α] : Mul α where mul := Lem_Num.numMult
instance [Lem_Num.NumNegate α] : Neg α where neg := Lem_Num.numNegate
