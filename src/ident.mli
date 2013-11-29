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

(** Pretty print *)
val pp : Format.formatter -> t -> unit

(** [to_string i] formats [i] using [pp]. *)
val to_string : t -> string

val from_id : Ast.id -> t
val from_name : Name.lskips_t -> t

(** Return the last name in the ident, e.g., M.Y.x gives x *)
val get_name : t -> Name.lskips_t

(** [mk_ident sk ms n] creates an identifier [n] with module prefix [ms] and leading whitespace [sk]. *)
val mk_ident : Ast.lex_skips -> Name.t list -> Name.t -> t

(** [mk_ident_ast nsl ns l] generates a new identifiers during type-checking. Whitespace is prohibited in all [Name.lskips_t] except the very first one
    and all [Ast.lex_skips] has to be empty. Otherwise, this operation my fails and uses the location [l] for the error message. *)
val mk_ident_ast : (Name.lskips_t * Ast.lex_skips) list -> Name.lskips_t -> Ast.l -> t

(** [mk_ident_strings] is a version of [mk_ident] that uses strings as input and uses empty whitespace. *)
val mk_ident_strings : string list -> string -> t

val to_output_format : (Output.id_annot -> Ulib.Text.t -> Output.t) -> Output.id_annot -> Ulib.Text.t -> t -> Output.t
val to_output : Output.id_annot -> Ulib.Text.t -> t -> Output.t
val get_lskip: t -> Ast.lex_skips

val replace_lskip : t -> Ast.lex_skips -> t
val to_name_list : t -> Name.t list * Name.t

(** [has_empty_path_prefix i] check whether the identifier [i] consists of just a single name without any
    prefix describing its module path *)
val has_empty_path_prefix : t -> bool

(** Remove the name from the identifier if it occurs at the first *)
val strip_path : Name.t -> t -> t

(** [rename i n'] renames the last name component of identifier [i] to [n']. *)
val rename : t -> Name.t -> t 

(** [drop_path i] drops the path of an identier. This means an identifier of the form
    [M1.M2...Mn.name] is converted to [name]. White-space is preserved. *)
val drop_path : t -> t
