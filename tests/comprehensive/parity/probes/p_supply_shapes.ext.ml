(* OCaml-side impure counter standing for the lem supply `tick` (linked as
   Parity_ext by run.sh): the reference semantics of a fresh-name counter.
   The driver resets it to each shape's seed and reads the final value. *)
let counter = ref 0
let tick () = let v = !counter in incr counter; v
let reset n = counter := n
let current () = !counter
