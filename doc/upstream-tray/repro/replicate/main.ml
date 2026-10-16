let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 1000 in
  Printf.printf "replicate n=%d  length=%d\n%!" n (Replicate.rl n)
