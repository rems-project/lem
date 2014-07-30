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

(** generate code for various backends *)

(** The level of extra information to generate *)
val gen_extra_level : int ref

(** Used to suppress the printing of target names in the TeX backend *)
val suppress_target_names : bool ref

(** Used to suppress the printing of open/import statements in the TeX backend *)
val suppress_libraries : bool ref

(** The various backends that generate text from typed asts *)
module Make(C : sig val avoid : Typed_ast.var_avoid_f;; val env : Typed_ast.env;; 
                val dir : string (** the directory the output will be stored. This is important for setting relative paths to import other modules *) end) : sig
  val ident_defs      : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val lem_defs        : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val hol_defs        : Typed_ast.def list * Ast.lex_skips -> (Ulib.Text.t * Ulib.Text.t option)
  val ocaml_defs      : Typed_ast.def list * Ast.lex_skips -> (Ulib.Text.t * Ulib.Text.t option)
  val isa_defs        : Typed_ast.def list * Ast.lex_skips -> (Ulib.Text.t * Ulib.Text.t option)
  val isa_header_defs : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val coq_defs        : Typed_ast.def list * Ast.lex_skips -> (Ulib.Text.t * Ulib.Text.t)
  val tex_defs        : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t
  val tex_inc_defs    : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t * Ulib.Text.t
  val html_defs       : Typed_ast.def list * Ast.lex_skips -> Ulib.Text.t

  (* Some more functions for printing various objects with the identiy backend. This is used for reporting. *)
  val ident_exp   : Typed_ast.exp -> Ulib.Text.t
  val ident_pat   : Typed_ast.pat -> Ulib.Text.t
  val ident_src_t : Types.src_t -> Ulib.Text.t
  val ident_typ   : Types.t -> Ulib.Text.t
  val ident_def   : Typed_ast.def -> Ulib.Text.t
end
