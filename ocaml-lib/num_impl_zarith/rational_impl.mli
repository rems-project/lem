module QI :
  sig
    type t
    val zero : t
    val one : t
    val minus_one : t
    val inf : t
    val minus_inf : t
    val undef : t
    val of_int : int -> t
    val of_big_int : Big_int_impl.BI.big_int -> t
    val of_int32 : int32 -> t
    val of_int64 : int64 -> t
    val of_nativeint : nativeint -> t
    val of_ints : int -> int -> t
    val of_float : float -> t
    val of_string : string -> t
    val is_real : t -> bool
    val sign : t -> int
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val min : t -> t -> t
    val max : t -> t -> t
    val leq : t -> t -> bool
    val geq : t -> t -> bool
    val lt : t -> t -> bool
    val gt : t -> t -> bool
    val to_int : t -> int
    val to_int32 : t -> int32
    val to_int64 : t -> int64
    val to_nativeint : t -> nativeint
    val to_string : t -> string
    val neg : t -> t
    val abs : t -> t
    val add : t -> t -> t
    val sub : t -> t -> t
    val mul : t -> t -> t
    val inv : t -> t
    val div : t -> t -> t
    val mul_2exp : t -> int -> t
    val div_2exp : t -> int -> t
    val floor : t -> Big_int_impl.BI.big_int
    val ceiling : t -> Big_int_impl.BI.big_int
    val num : t -> Big_int_impl.BI.big_int
    val den : t -> Big_int_impl.BI.big_int
    val print : t -> unit
    val output : out_channel -> t -> unit
    val sprint : unit -> t -> string
    val bprint : Buffer.t -> t -> unit
    val pp_print : Format.formatter -> t -> unit
    val ( ~- ) : t -> t
    val ( ~+ ) : t -> t
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( * ) : t -> t -> t
    val ( / ) : t -> t -> t
    val ( lsl ) : t -> int -> t
    val ( asr ) : t -> int -> t
    val ( ~$ ) : int -> t
    val ( // ) : int -> int -> t
  end
