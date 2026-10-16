let row a b =
  let (q, r) = Divmod.int_dm a b in
  let (q32, r32) = Divmod.int32_dm (Int32.of_int a) (Int32.of_int b) in
  let (q64, r64) = Divmod.int64_dm (Int64.of_int a) (Int64.of_int b) in
  let (qz, rz) = Divmod.integer_dm (Nat_big_num.of_int a) (Nat_big_num.of_int b) in
  Printf.printf "a=%d b=%d | int %d %d | int32 %ld %ld | int64 %Ld %Ld | integer %s %s\n"
    a b q r q32 r32 q64 r64 (Nat_big_num.to_string qz) (Nat_big_num.to_string rz)
let () = row (-7) (-2); row 7 (-2); row (-7) 2; row 7 2; row (-6) (-2);
  let b = -(1 lsl 61) in
  let (q, r) = Divmod.int_dm (-7) b in
  let (q64, r64) = Divmod.int64_dm (-7L) (Int64.of_int b) in
  let (qz, rz) = Divmod.integer_dm (Nat_big_num.of_int (-7)) (Nat_big_num.of_int b) in
  Printf.printf "a=-7 b=-2^61 | int %d %d | int64 %Ld %Ld | integer %s %s\n" q r q64 r64 (Nat_big_num.to_string qz) (Nat_big_num.to_string rz)
