let () =
  Printf.printf "intLsl 1 30:          rep %d  def %d\n" Bitwise.rep_lsl Bitwise.def_lsl;
  Printf.printf "intLor 2^30 0:        rep %d  def %d\n" Bitwise.rep_lor Bitwise.def_lor;
  Printf.printf "natLor 2^40 1:        rep %d  def %d\n" Bitwise.rep_nlor Bitwise.def_nlor
