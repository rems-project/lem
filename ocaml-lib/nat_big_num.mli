type num = Big_int_impl.BI.big_int

val zero : num
val succ : num -> num
val pred : num -> num
val pred_nat : num -> num
val negate : num -> num

val add : num -> num -> num
val sub : num -> num -> num
val sub_nat : num -> num -> num
val div : num -> num -> num
val mul : num -> num -> num
val pow_int : num -> int -> num
val pow_int_positive : int -> int -> num


val quomod : num -> num -> num * num
val abs : num -> num
val modulus : num -> num -> num

val min : num -> num -> num
val max : num -> num -> num

val less : num -> num -> bool
val greater : num -> num -> bool
val less_equal : num -> num -> bool
val greater_equal : num -> num -> bool

val compare : num -> num -> int
val equal : num -> num -> bool

val bitwise_or : num -> num -> num
val bitwise_and : num -> num -> num
val bitwise_xor : num -> num -> num
val shift_left : num -> int -> num
val shift_right : num -> int -> num

val extract_num : num -> int -> int -> num

val of_int : int -> num
val of_int32 : Int32.t -> num
val of_int64 : Int64.t -> num

val to_int : num -> int
val to_int32 : num -> Int32.t
val to_int64 : num -> Int64.t

val to_string : num -> string
val of_string : string -> num
val of_string_nat : string -> num
val integerDiv_t : num -> num -> num
val integerRem_t : num -> num -> num
val integerRem_f : num -> num -> num
