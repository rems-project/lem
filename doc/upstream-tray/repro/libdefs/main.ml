open Libdefs
let ns s = "{" ^ String.concat "; " (List.map string_of_int (Pset.elements s)) ^ "}"
let rs (R n) = Printf.sprintf "R %d" n
let () =
  let (a, b) = lu1_split () in
  Printf.printf "split 3 {1..5}       = (%s, %s)\n" (ns a) (ns b);
  let (a, m, b) = lu1_splitMember () in
  Printf.printf "splitMember 3 {1..5} = (%s, %b, %s)\n" (ns a) m (ns b);
  Printf.printf "defaultLnot (-6)     = %s\n" (Nat_big_num.to_string (lu2_defaultLnot ()));
  Printf.printf "integerLnot (-6)     = %s\n" (Nat_big_num.to_string (lu2_integerLnot ()));
  Printf.printf "R 1 <= R 2           = %b\n" (lp1_le ());
  Printf.printf "max (R 1) (R 2)      = %s\n" (rs (lp1_max ()));
  Printf.printf "min (R 1) (R 2)      = %s\n" (rs (lp1_min ()));
  Printf.printf "maxByLessEqual (<=) (R 1) (R 2) = %s\n" (rs (lp1_maxBy ()));
  Printf.printf "size (bigunionBy m3 {{1}; {4}})  = %d\n" (lp9_size ());
  Printf.printf "toList (bigunionBy rev {{1; 2}; {3}}) = [%s]\n" (String.concat "; " (List.map string_of_int (lp9_list ())))
