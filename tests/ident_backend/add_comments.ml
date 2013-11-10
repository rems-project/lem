open Str

let space = regexp "[ \t\n,`]"


let counter = ref 0

let do_line o s =
  List.iter 
    (function
       | Text(s) | Delim(s) -> 
           begin
             output_string o "(*";
             output_string o (string_of_int !counter);
             counter := !counter + 1;
             output_string o "*)";
             output_string o s
           end)
    (full_split space s)


let rec do_lines o =
  let s = input_line stdin in
    do_line o s;
    output_string o "\n";
    do_lines o


let _ = 
  let o = open_out "test.lem" in
  try
    do_lines o
  with
    | End_of_file ->
        close_out o
