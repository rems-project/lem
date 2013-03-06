val _ = load "HolDoc";
val _ = load "stringTheory";
val _ = load "res_quanTheory";
val _ = load "finite_mapTheory";
val _ = load "wordsTheory";
val _ = PolyML.shareCommonData PolyML.rootFunction;
fun main () = 
  (List.app use (CommandLine.arguments ()); 
   PolyML.rootFunction ());
val _ = PolyML.export ("hol_preload", main);
