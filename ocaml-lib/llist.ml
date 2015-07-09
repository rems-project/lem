(** DPM: ugly version of [map] using "unsafe" OCaml features that doesn't
  * completely blow the stack.  See:
  *   http://cedeela.fr/tail-recursive-map-in-ocaml.html
  * for source (though there is a bug in the handling of "[]" in [recurse]
  * which is fixed below --- Lem's automated assertions and tests picked that
  * up.
  *)
let map f l =
  let rec recurse first prev l =
    match l with
      | []  -> first
      | [x] ->
        let l' = [f x] in
          Obj.set_field (Obj.repr prev) 1 (Obj.repr l'); first
      | x::xs ->
        let cur = [f x] in
          Obj.set_field (Obj.repr prev) 1 (Obj.repr cur);
          recurse first cur xs
  in
    match l with
      | []    -> []
      | x::xs ->
        let first = [f x] in
          recurse first first xs
