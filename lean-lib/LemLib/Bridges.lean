/- Hand-written bridge instances for Lem's numeric typeclasses.
   Lem's NumAdd/NumMinus/NumMult/NumNegate classes don't extend Lean's
   Add/Sub/Mul/Neg, so these bridges let `+`, `-`, `*`, `-x` operators
   work on types with Lem numeric constraints. -/

import LemLib.Num
import LemLib.Basic_classes

/- SetType/Eq0/Ord0 for Unit — needed by generated code using Set.map with unit results -/
instance : Lem_Basic_classes.SetType Unit where setElemCompare _ _ := .EQ
instance : Lem_Basic_classes.Eq0 Unit where
  isEqual _ _ := true
  isInequal _ _ := false
instance : Lem_Basic_classes.Ord0 Unit where
  compare _ _ := .EQ
  isLess _ _ := false
  isLessEqual _ _ := true
  isGreater _ _ := false
  isGreaterEqual _ _ := true

instance [Lem_Num.NumAdd α] : Add α where add := Lem_Num.numAdd
instance [Lem_Num.NumMinus α] : Sub α where sub := Lem_Num.numMinus
instance [Lem_Num.NumMult α] : Mul α where mul := Lem_Num.numMult
instance [Lem_Num.NumNegate α] : Neg α where neg := Lem_Num.numNegate
