let show name f =
  match f () with
  | b -> Printf.printf "%s = %b\n%!" name b
  | exception e -> Printf.printf "%s raises %s\n%!" name (Printexc.to_string e)
let () =
  show "members_same" X1.members_same;
  show "same" X1.same;
  show "refl" X1.refl
