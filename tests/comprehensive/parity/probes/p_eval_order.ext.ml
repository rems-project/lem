(* OCaml-side impure counter for p_eval_order (linked as Parity_ext by run.sh):
   the lem `fresh : unit -> nat` (mirrors the retired cerberus
   Symbol.fresh_int native counter: first draw = 0). *)
let counter = ref 0
let fresh () = let v = !counter in incr counter; v
