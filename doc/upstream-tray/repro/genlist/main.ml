let () =
  List.iter (fun n ->
    let t0 = Sys.time () in
    let len = Genlist.gl n in
    Printf.printf "genlist n=%6d  length=%6d  cpu=%.2fs\n%!" n len (Sys.time () -. t0))
    [5000; 10000; 20000; 40000]
