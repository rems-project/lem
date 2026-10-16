let () =
  let n = int_of_string Sys.argv.(1) in
  Printf.printf "List.init n=%d  length=%d\n%!" n (List.length (List.init n (fun _ -> 0)))
