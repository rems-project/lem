(* OCaml reference driver for p_fuel: no fuel exists on this target; the
   block is printed TWICE so the Lean driver's two-fuel output must match
   it byte-for-byte. *)
let () =
  List.iter print_endline P_fuel.results;
  List.iter print_endline P_fuel.results
