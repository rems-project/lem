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

type t

type t' =
  | Kwd' of string
  | Ident' of Ulib.Text.t
  | Num' of int

type id_annot =  (* kind annotation for latex'd identifiers *)
  | Term_const
  | Term_ctor
  | Term_field 
  | Term_method 
  | Term_var 
  | Term_var_toplevel
  | Term_spec 
  | Type_ctor
  | Type_var
  | Nexpr_var
  | Module_name
  | Class_name
  | Target

val emp : t
val kwd : string -> t
val id : id_annot -> Ulib.Text.t -> t
val num : int -> t
val ws : Ast.lex_skips -> t
val str : Ulib.Text.t -> t
val err : string -> t
val meta : string -> t
val texspace :  t
val (^) : t -> t -> t
val block : bool -> int -> t -> t
val block_h : bool -> int -> t -> t
val block_v : bool -> int -> t -> t
val block_hv : bool -> int -> t -> t
val block_hov : bool -> int -> t -> t
val break_hint : bool -> int -> t
val break_hint_cut : t
val break_hint_space : int -> t
val ensure_newline : t
val flat : t list -> t
val concat : t -> t list -> t
val to_rope : Ulib.Text.t -> (Ast.lex_skip -> Ulib.Text.t) -> (t' -> t' -> bool) -> t -> Ulib.Text.t
val to_rope_option_tex : (Ast.lex_skip -> Ulib.Text.t) -> (t' -> t' -> bool) -> bool -> t -> Ulib.Text.t option
val to_rope_ident : id_annot ->  Ulib.Text.t -> Ulib.Text.t

val tex_escape : Ulib.Text.t -> Ulib.Text.t

val tex_command_escape : Ulib.Text.t -> Ulib.Text.t
val tex_command_label  : Ulib.Text.t -> Ulib.Text.t
val tex_command_name  : Ulib.Text.t -> Ulib.Text.t

val ml_comment_to_rope : Ast.ml_comment -> Ulib.Text.t
