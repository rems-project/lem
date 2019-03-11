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
val sqrt : num -> num

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

val to_float : num -> float

val to_string : num -> string
val of_string : string -> num
val of_string_nat : string -> num
val integerDiv_t : num -> num -> num
val integerRem_t : num -> num -> num
val integerRem_f : num -> num -> num

(* pp_num can be used as a printer in the toplevel system:
 * # #use "topfind";;
 * # #require "lem";;
 * # Nat_big_num.of_int 42;;
 * - : Nat_big_num.num = <abstr>
 * # #install_printer Nat_big_num.pp_num;;
 * # Nat_big_num.of_int 42;;
 * - : Nat_big_num.num = 42
 *
 * it can also be used as a printer in ocamldebug:
 * (ocd) load_printer <DESTDIR>/zarith/zarith.cma
 * File <DESTDIR>/zarith/zarith.cma loaded
 * (ocd) load_printer <DESTDIR>/ocaml/nums.cma
 * File <DESTDIR>/ocaml/nums.cma loaded
 * (ocd) load_printer <DESTDIR>/lem_zarith/extract.cma
 * File <DESTDIR>/lem_zarith/extract.cma loaded
 * (ocd) install_printer Nat_big_num.pp_num
 * (ocd) print <expression>
 * $2: Nat_big_num.num = 42
 *
 * where <DESTDIR> is the output of 'ocamlfind printconf destdir'
 *)
 val pp_num    : Format.formatter -> num -> unit
