import P_list_deep
-- One thunk per line, size read at runtime (no closed-term hoisting), so
-- a native stack overflow shows how far we got. args: [n] [start-index]
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300000
  let start := (args[1]? >>= String.toNat?).getD 0
  let fs := [d_length, d_foldl, d_foldr, d_map, d_append, d_zip, d_reverse, d_filter,
             d_concat, d_all, d_take, d_drop, d_splitAt, d_compare, d_eq, d_fromList,
             d_sort, d_sortByOrd, d_concatMap, d_unzip, d_partition, d_lookup, d_show, d_map_fold,
             d_stringFromList, d_string_concat, d_genlist, d_length_int]
  for f in fs.drop start do
    IO.println (f n)
    (← IO.getStdout).flush
