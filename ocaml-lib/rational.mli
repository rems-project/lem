type t = Rational_impl.QI.t
val of_int : int -> t
val of_ints : int -> int -> t
val of_big_int : Big_int_impl.BI.big_int -> t
val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val div : t -> t -> t
val neg : t -> t
val abs : t -> t
val equal : t -> t -> bool
val lt : t -> t -> bool
val gt : t -> t -> bool
val leq : t -> t -> bool
val geq : t -> t -> bool
val min : t -> t -> t
val max : t -> t -> t
val floor : t -> Big_int_impl.BI.big_int
val ceiling : t -> Big_int_impl.BI.big_int
val num : t -> Big_int_impl.BI.big_int
val den : t -> Big_int_impl.BI.big_int
