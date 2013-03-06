(**************************************************************************)
(*     ARM/Power Multiprocessor Machine Code Semantics: HOL sources       *)
(*                                                                        *)
(*                                                                        *)
(*  Jade Alglave (2), Anthony Fox (1), Samin Isthiaq (3),                 *)
(*  Magnus Myreen (1), Susmit Sarkar (1), Peter Sewell (1),               *)
(*  Francesco Zappa Nardelli (2)                                          *)
(*                                                                        *)
(*   (1) Computer Laboratory, University of Cambridge                     *)
(*   (2) Moscova project, INRIA Paris-Rocquencourt                        *)
(*   (3) Microsoft Research Cambridge                                     *)
(*                                                                        *)
(*     Copyright 2007-2008                                                *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*                                                                        *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*     products derived from this software without specific prior         *)
(*     written permission.                                                *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,          *)
(*  WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING             *)
(*  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS    *)
(*  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.          *)
(*                                                                        *)
(**************************************************************************)

structure HolDoc :> HolDoc = struct

(*

  Code to automatically generate .imn information for theories at
  export time.  Output is in file <thyname>.imn.

  To get this to work it must be the last module opened (more
  accurately, it must override bossLib and HolKernel, and so must
  follow these two).

*)

val empty_set = Binaryset.empty String.compare
val defns = ref empty_set

open HolKernel Parse boolLib

fun analyse_definition_result result = let
  (* result is a conjunction of possibly universally quantified equations *)
  val (_, tmp) = strip_forall (concl result)
  val cs = strip_conj tmp
  fun head_of_clause t = let
    val (_, body) = strip_forall t
    val (l, _) = dest_eq body
    val (f, _) = strip_comb l
  in
    #Name (dest_thy_const f)
  end
in
  defns := Binaryset.addList (!defns, map head_of_clause cs)  ;
  result
end

val Define = analyse_definition_result o bossLib.Define
fun xDefine s = analyse_definition_result o bossLib.xDefine s


fun get_types () = map #1 (Theory.types "-")

fun get_defined_constants() = Binaryset.listItems (!defns)

fun get_constructors possible_types = let
  open Binaryset
  fun get_cs (tyinfo, acc) =
      List.foldl (fn (c_t, set) => add(set, #1 (dest_const c_t)))
                 acc
                 (TypeBasePure.constructors_of tyinfo)
  fun get_cs_from_name(nm, acc) =
      case TypeBase.read {Thy = current_theory(), Tyop = nm} of
        NONE => acc
      | SOME tyi => get_cs(tyi, acc)
  val result0 = List.foldl get_cs_from_name empty_set possible_types
in
  listItems (difference(result0, addList(empty_set, possible_types)))
end

fun get_field_names possible_types oinfo = let
  val ops0 = Overload.oinfo_ops oinfo
  val recsel = GrammarSpecials.recsel_special
  val ops1 = List.filter (String.isPrefix recsel o #1) ops0
  fun overloads_to_accessor_on_possible_type (s, {actual_ops, ...}) = let
    fun ty_ok ty = mem (#1 (dest_type (#1 (dom_rng ty)))) possible_types
  in
    List.exists (ty_ok o type_of) actual_ops
  end
  val final_ops = List.filter overloads_to_accessor_on_possible_type ops1
in
  map (fn (s,_) => String.extract(s, size recsel, NONE)) final_ops
end

fun write_list listname outstr strlist = let
  fun recurse [] = raise Fail "shouldn't happen"
    | recurse [x] = TextIO.output(outstr, x)
    | recurse (h::t) = (TextIO.output(outstr, h ^ " ");
                        recurse t)
in
  if null strlist then ()
  else
    (TextIO.output(outstr, "(*[ " ^ listname ^
                           "\n(* automatically generated; do not edit *)\n");
     recurse strlist;
     TextIO.output(outstr, "\n]*)\n"))
end


fun export_theory () = let
  val types = get_types ()
  val constructors = get_constructors types
  val defineds = get_defined_constants ()
  val fnames =
      get_field_names types (term_grammar.overload_info (term_grammar()))
  val output_stream = TextIO.openOut (current_theory () ^ ".imn")
in
  write_list "TYPE_LIST" output_stream types;
  write_list "CON_LIST" output_stream constructors;
  write_list "FIELD_LIST" output_stream fnames;
  write_list "AUX_LIST" output_stream defineds;
  TextIO.closeOut output_stream;
  Theory.export_theory()
end;


end (* struct *)
