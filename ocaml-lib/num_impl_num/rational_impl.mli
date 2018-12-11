module QI :
  sig
    type t = Num.num
    val of_int : int -> Num.num
    val of_ints : int -> int -> Num.num
    val of_big_int : Big_int.big_int -> Num.num
    val add : Num.num -> Num.num -> Num.num
    val sub : Num.num -> Num.num -> Num.num
    val mul : Num.num -> Num.num -> Num.num
    val div : Num.num -> Num.num -> Num.num
    val neg : Num.num -> Num.num
    val abs : Num.num -> Num.num
    val equal : Num.num -> Num.num -> bool
    val lt : Num.num -> Num.num -> bool
    val gt : Num.num -> Num.num -> bool
    val leq : Num.num -> Num.num -> bool
    val geq : Num.num -> Num.num -> bool
    val min : Num.num -> Num.num -> Num.num
    val max : Num.num -> Num.num -> Num.num
    val floor : Num.num -> Big_int.big_int
    val ceiling : Num.num -> Big_int.big_int
    val num : Num.num -> Big_int.big_int
    val den : Num.num -> Big_int.big_int
  end
