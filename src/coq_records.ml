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

open Output
open Typed_ast

open Coq_backend_utils

let generate_coq_record_update_notation e =
  let notation_kwd = from_string "Notation" in
  let with_kwd = from_string "\'with\'" in
  let prefix =
    Output.flat [
      notation_kwd; from_string " \"{[ r "; with_kwd; from_string " "
    ]
  in
  let aux all_fields x =
    let ((lskips, l), s4, ty) = x in
    let name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip lskips)) in
    let all_fields = List.filter (fun x -> Pervasives.compare name x <> 0) all_fields in
    let other_fields = concat (kwd "; ")
      (List.map (fun x ->
        Output.flat [
          from_string x; from_string " := " ^ from_string x ^ from_string " r"
        ]
      ) all_fields)
    in
    let focussed_field = from_string name ^ from_string " := e" in
    let body =
      Output.flat [
        from_string "\'"; from_string name; from_string "\' := e ]}\" := "
      ]
    in
    let result =
      Output.flat [
        prefix; body; from_string "("; from_string "{| "; focussed_field;
        from_string "; "; other_fields; from_string " |})."
      ]
    in
      match all_fields with
        | []    -> emp (* DPM: this should have been macro'd away earlier *)
        | x::xs -> result
  in
    match e with
      | Te_record_coq (s3, name, s1, fields, s2) ->
          let all_fields = Seplist.to_list fields in
          let all_fields_names = List.map (fun ((lskips, l), s4, ty) -> Ulib.Text.to_string (Name.to_rope (Name.strip_lskip lskips))) all_fields in
          let field_entries = concat_str "\n" (List.map (aux all_fields_names) all_fields) in
          let terminator =
            if List.length all_fields = 0 then
              emp
            else
              from_string "\n"
          in
            field_entries ^ terminator
      | Te_record (s1, s2, fields, s3) ->
          let all_fields = Seplist.to_list fields in
          let all_fields_names = List.map (fun ((lskips, l), s4, ty) -> Ulib.Text.to_string (Name.to_rope (Name.strip_lskip lskips))) all_fields in
          let field_entries = concat_str "\n" (List.map (aux all_fields_names) all_fields) in
          let terminator =
            if List.length all_fields = 0 then
              emp
            else
              from_string "\n"
          in
            field_entries ^ terminator
      | _                          -> emp
;;
