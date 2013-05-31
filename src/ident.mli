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

(** source-file long identifiers *)

(** t is the type of dot separated lists of names (with preceding lexical
    spacing), e.g. [(*Foo*) M . x] *)
type t

exception No_type of Ast.l * string
val raise_error_string : Ast.l -> string -> 'a
val raise_error : Ast.l -> string -> (Format.formatter -> 'a -> unit) -> 'a -> 'b

(** Pretty print *)
val pp : Format.formatter -> t -> unit

val from_id : Ast.id -> t

(** Return the last name in the ident, e.g., M.Y.x gives x *)
val get_name : t -> Name.lskips_t

(** [mk_ident nsl ns l] generates a new identifiers giving full control. Whitespace is prohibited though and
    only parenthesis might be used in the [Name.lskips_t]. Otherwise, this operation my fails and uses
    the location [l] for the error message. *)
val mk_ident : (Name.lskips_t * Ast.lex_skips) list -> Name.lskips_t -> Ast.l -> t

(** Since [mk_ident] does not allow whitespace and parenthesis are often not needed, 
    [mk_ident_names] provides a simpler interface that uses names. Since it cannot fail, the location is
    not needed. *)
val mk_ident_names : Name.t list -> Name.t -> t

(** [mk_ident_strings] is a version of [mk_ident_names] that uses strings as input. *)
val mk_ident_strings : string list -> string -> t


val to_output : Output.id_annot -> Output.t -> t -> Output.t
val to_output_infix : (Output.id_annot -> Ulib.Text.t -> Output.t) -> Output.id_annot -> Output.t -> t -> Output.t
val get_first_lskip: t -> Ast.lex_skips

(*
val drop_parens : (Precedence.op -> Precedence.t) -> t -> t
val add_parens : (Precedence.op -> Precedence.t) -> t -> t
val starts_with_upper_letter : t -> bool
val starts_with_lower_letter : t -> bool
val capitalize : t -> t
val uncapitalize : t -> t
 *)
val replace_first_lskip : t -> Ast.lex_skips -> t
val to_name_list : t -> Name.t list * Name.t

(** Remove the name from the identifier if it occurs at the first *)
val strip_path : Name.t -> t -> t
