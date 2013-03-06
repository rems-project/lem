(* Running 'hol < get_constants.sml' makes a file 'constants' with all of HOL's
* defined constants in it.  The Unicode characters need to be removed manually.
* *)

val _ = List.app load ["finite_mapTheory", "listTheory", "pairTheory",
"pred_setTheory", "set_relationTheory", "sortingTheory", "stringTheory",
"integerTheory", "wordsTheory"]

open TextIO

val out = openOut "constants";

val _ =
  List.app
    (fn x => (output (out,x); output (out,"\n")))
    (Parse.known_constants())

val _ = closeOut out

