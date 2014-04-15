(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*          Dominic Mulligan, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            *)
(*          Gabriel Kerneis, University of Cambridge                      *)
(*          Kathy Gray, University of Cambridge                           *)
(*          Peter Boehm, University of Cambridge (while working on Lem)   *)
(*          Peter Sewell, University of Cambridge                         *)
(*          Scott Owens, University of Kent                               *)
(*          Thomas Tuerk, University of Cambridge                         *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2013                               *)
(*  by the UK authors above and Institut National de Recherche en         *)
(*  Informatique et en Automatique (INRIA).                               *)
(*                                                                        *)
(*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   *)
(*  are distributed under the license below.  The former are distributed  *)
(*  under the LGPLv2, as in the LICENSE file.                             *)
(*                                                                        *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(**************************************************************************)



let class_label_to_path (label : string) : Path.t =
  let (ns, n) = begin
  match label with
    | "class_numeral"   -> (["Num"], "Numeral")
    | "class_ord"       -> (["Basic_classes"], "Ord")
    | "class_num_minus" -> (["Num"], "NumMinus")
    | "class_set_type"  -> (["Basic_classes"], "SetType")
    | s -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_general (true,				     
              (Ast.Trans (false, "class_label_to_path", None)),
              ("Unknown label '" ^ s ^ "'"))))
  end in
  Path.mk_path (List.map Name.from_string ns) (Name.from_string n)

let type_label_to_path (label : string) : Path.t =
  let (ns, n) = begin
  match label with
    | "type_natural" -> (["Num"], "natural")
    | s -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_general (true,				     
              (Ast.Trans (false, "type_label_to_path", None)),
              ("Unknown label '" ^ s ^ "'"))))
  end in
  Path.mk_path (List.map Name.from_string ns) (Name.from_string n)


(* TODO: Implement this function in an external file and write a simple parser *)
let constant_label_to_path_name (label : string) : (string list * string) =
match label with
  | "fromNumeral" -> (["Num"], "fromNumeral")
  | "equality" -> (["Basic_classes"], "isEqual")
  | "identity" -> (["Function"], "id")

  | "fail" -> (["Assert_extra"], "fail")
  | "failwith" -> (["Assert_extra"], "failwith")

  | "conjunction" -> (["Bool"], "&&")
  | "implication" -> (["Bool"], "-->")

  | "multiplication" -> (["Num"], "*")
  | "subtraction" -> (["Num"], "-")
  | "less_equal" -> (["Basic_classes"], "<=")

  | "list_concat" -> (["List"], "concat")
  | "list_cons" -> (["List"], "::")
  | "list_exists" -> (["List"], "any")
  | "list_fold_right" -> (["List"], "foldr")
  | "list_forall" -> (["List"], "all")
  | "list_map" -> (["List"], "map")
  | "list_member" -> (["List"], "elem")

  | "maybe_just" -> (["Maybe"], "Just")
  | "maybe_nothing" -> (["Maybe"], "Nothing")

  | "nat_list_to_string" -> (["Pervasives"], "nat_list_to_string")

  | "set_add" -> (["Set"], "insert")
  | "set_cross" -> (["Set"], "cross")
  | "set_exists" -> (["Set"], "any")
  | "set_filter" -> (["Set"], "filter")
  | "set_fold" -> (["Set_helpers"], "fold")
  | "set_forall" -> (["Set"], "all")
  | "set_from_list" -> (["Set"], "fromList")
  | "set_image" -> (["Set"], "map")
  | "set_member" -> (["Set"], "IN")
  | "set_sigma" -> (["Set"], "sigma")

  | "vector_access" -> (["Vector"], "vector_access")
  | "vector_slice" -> (["Vector"], "vector_slice")
  | s -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_general (true,				     
            (Ast.Trans (false, "constant_label_to_path_name", None)),
            ("Unknown label '" ^ s ^ "'"))))
;;

let constant_label_to_path (label : string) : Path.t =
  let (path, head) = constant_label_to_path_name label in
    Path.mk_path (List.map Name.from_string path) (Name.from_string head)
;;




