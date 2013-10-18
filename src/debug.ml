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

open Typed_ast
open Syntactic_tests
open Pcombinators
open Types

let rope_of_string (s : string) : Ulib.Text.t =
  Ulib.Text.of_string s
;;

let string_of_char (c : char) : string =
  String.make 1 c
;;

let parse_tyvar : Tyvar.t parser =
  predicate (fun c ->
    let code = Char.code c in
      code >= 97 && code <= 122) >>= fun r ->
  return (Tyvar.from_rope (rope_of_string (string_of_char r)))
;;

let parse_src_t_aux_wild : src_t_aux parser =
  string_exact "_" >>= fun w ->
  return (Typ_wild no_lskips)
;;

let parse_src_t_aux_tyvar : src_t_aux parser =
  parse_tyvar >>= fun t ->
  return (Typ_var (no_lskips, t))
;;

let parse_nvar : Nvar.t parser =
  predicate (fun c ->
    let code = Char.code c in
      code >= 97 && code <= 122) >>= fun r ->
  return (Nvar.from_rope (rope_of_string (string_of_char r)))
;;

let parse_src_nexp_aux_const : src_nexp_aux parser =
  digits >>= fun ds ->
  return (Nexp_const (no_lskips, ds))
;;

(*
let rec parse_src_nexp_aux : src_nexp_aux parser =
     (parse_nvar >>= fun n -> return (Nexp_var (no_lskips, n)))
  ++ parse_src_nexp_aux_const
  ++ parse_src_nexp_aux_mult
and parse_src_nexp_aux_mult =
  parse_src_nexp_aux >>= fun left ->
  whitespace1 >>= fun _ ->
  string_exact "*" >>= fun _ ->
  whitespace1 >>= fun _ ->
  parse_src_nexp_aux >>= fun right ->
  return (Nexp_mult (left, no_lskips, right))
and parse_src_nexp_aux_add =
  parse_src_nexp_aux >>= fun left ->
  whitespace1 >>= fun _ ->
  string_exact "+" >>= fun _ ->
  whitespace1 >>= fun _ ->
  parse_src_next_aux >>= fun right ->
  return (Nexp_mult (left, no_lskips, right))
and parse_src_nexp_aux_paren =
  string_exact "(" >>= fun _ ->
  whitespace1 >>= fun _ ->
  parse_src_nexp_aux >>= fun n ->
  whitespace1 >>= fun _ ->
  string_exact ")" >>= fun _ ->
  return (Nexp_paren (no_lskips, n, no_lskips))
;;
*)

(*
and src_nexp_aux =
 | Nexp_var of lskips * Nvar.t 
 | Nexp_const of lskips * int
 | Nexp_mult of src_nexp * lskips * src_nexp (* One will always be const *)
 | Nexp_add of src_nexp * lskips * src_nexp 
 | Nexp_paren of lskips * src_nexp * lskips
*)

(*
let _ = parse_and_print "_" parse_src_t_aux_wild (fun x -> "wild parsed")
let _ = parse_and_print "a" parse_src_t_aux_tyvar (fun x -> "tyvar parsed")
*)
