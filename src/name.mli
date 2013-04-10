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

(** source-file and internal short identifiers *)

(* t is the type of plain names, either normal or infix, e.g., x or cmp or ++ *)
type t
val compare : t -> t -> int
val pp : Format.formatter -> t -> unit
val from_rope : Ulib.Text.t -> t
val to_rope : t -> Ulib.Text.t
val to_rope_tex : Output.id_annot -> t -> Ulib.Text.t
val to_string : t -> string
val from_string : string -> t
(*val to_rope_core : Output.id_annot -> Ast.v -> Ulib.Text.t*)
val fresh : Ulib.Text.t -> (t -> bool) -> t
val fresh_list : int -> Ulib.Text.t -> (t -> bool) -> t list
val rename : (Ulib.Text.t -> Ulib.Text.t) -> t -> t
val starts_with_upper_letter : t -> bool
val starts_with_lower_letter : t -> bool
val starts_with_underscore : t -> bool
val capitalize : t -> t
val uncapitalize : t -> t
val remove_underscore : t -> t

(* lskips_t is the type of names with immediately preceding spaces, comments and
* newlines, as well as surrounding `` and (), e.g., (* Foo *) x or (++) or `y` *)
type lskips_t
val lskip_pp : Format.formatter -> lskips_t -> unit
val from_x : Ast.x_l -> lskips_t
val from_ix : Ast.ix_l -> lskips_t
val add_lskip : t -> lskips_t
val strip_lskip : lskips_t -> t
val to_output : (Output.id_annot -> Ulib.Text.t -> Output.t) -> Output.id_annot -> lskips_t -> Output.t
val to_output_quoted : (Output.id_annot -> Ulib.Text.t -> Output.t) -> Output.id_annot -> lskips_t -> Output.t
val add_pre_lskip : Ast.lex_skips -> lskips_t -> lskips_t
val get_lskip : lskips_t -> Ast.lex_skips
val drop_parens : lskips_t -> lskips_t
val add_parens : lskips_t -> lskips_t
val lskip_rename : (Ulib.Text.t -> Ulib.Text.t) -> lskips_t -> lskips_t
val replace_lskip : lskips_t -> Ast.lex_skips -> lskips_t
val get_prec : (Precedence.op -> Precedence.t) -> lskips_t -> Precedence.t
