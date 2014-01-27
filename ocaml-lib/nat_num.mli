type nat = int
type natural = Big_int.big_int

val natural_monus : natural -> natural -> natural
val natural_pred : natural -> natural

val nat_pred  : nat -> nat
val nat_monus : nat -> nat -> nat
val nat_pow   : nat -> nat -> nat
val int_pow   : int -> nat -> int
val int32_pow : Int32.t -> nat -> Int32.t
val int_div   : int -> int -> int
val int32_div : Int32.t -> Int32.t -> Int32.t
val int_mod   : int -> int -> int
val int32_mod : Int32.t -> Int32.t -> Int32.t
