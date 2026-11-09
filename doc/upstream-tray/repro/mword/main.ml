let run name show f =
  match f () with
  | v -> Printf.printf "%-22s = %s\n%!" name (show v)
  | exception e -> Printf.printf "%-22s raises %s\n%!" name (Printexc.to_string e)
let n = Nat_big_num.to_string and b = string_of_bool and i = string_of_int and s x = "\"" ^ x ^ "\""
open Mword
let () =
  run "om1_uminus_zero" n om1_uminus_zero;
  run "om1_uminus_zero_eq" b om1_uminus_zero_eq;
  run "om1_from_integer" n om1_from_integer;
  run "om1_signed_divide" n om1_signed_divide;
  run "om2_getbit_4_1" b om2_getbit_4_1;
  run "om2_getbit_8_2" b om2_getbit_8_2;
  run "om2_getbit_2_1" b om2_getbit_2_1;
  run "om3_setbit_10" n om3_setbit_10;
  run "om3_setbit_10_len" i om3_setbit_10_len;
  run "om4_bitlist4_len" i om4_bitlist4_len;
  run "om4_bitlist4_bits" i om4_bitlist4_bits;
  run "om4_bitlist11" n om4_bitlist11;
  run "om4_extract_len" i om4_extract_len;
  run "om4_concat_len" i om4_concat_len;
  run "om5_ror0" n om5_ror0;
  run "om5_rol8" n om5_rol8;
  run "om5_rol9" n om5_rol9;
  run "om5_ror9" n om5_ror9;
  run "om5_ror1" n om5_ror1;
  run "om5_asr9" n om5_asr9;
  run "om5_asr3" n om5_asr3;
  run "lp5_hex" s lp5_hex;
  run "lp5_show" s lp5_show
