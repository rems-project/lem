module BI = struct
  include Big_int

  (* div_big_int and mod_big_int are a bit different than Z.div and Z.mod *)
  let div   (_: big_int) (_: big_int) : big_int = failwith "Big_int_impl.div is not implemented"
  let (mod) (_: big_int) (_: big_int) : big_int = failwith "Big_int_impl.(mod) is not implemented"
end
