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

(** internal canonical long identifiers *)

(* t is the type of globally unique identifier paths to definitions *)
type t

val compare : t -> t -> int
val pp : Format.formatter -> t -> unit
val from_id : Ident.t -> t
(*
val get_name : t -> Name.t
 *)
val mk_path : Name.t list -> Name.t -> t

(** [mk_path_list names] splits names into [ns @ [n]] and calls
    [mk_path ns n]. It fails, if [names] is empty. *)
val mk_path_list : Name.t list -> t

(** [get_module_path p] returns the module path of path [p]. If
    if is a path of an identifier [m0. ... . mn . f], then [get_module]
    returns the module path [m0. ... . mn]. If the path does not have
    a module prefix, i.e. if it is a single name [f], [None] is returned. *)
val get_module_path : t -> t option

val natpath : t
val listpath : t
val vectorpath : t
val boolpath : t
val bitpath : t
val setpath : t
val stringpath : t
val unitpath : t
val charpath : t
val numeralpath : t
val get_name : t -> Name.t

(** [get_toplevel_name p] gets the outmost name of a path. This is important
    when checking prefixes. For example, the result for path [module.submodule.name] is 
    [module] and for [name] it is [name]. *)
val get_toplevel_name: t -> Name.t

val check_prefix : Name.t -> t -> bool
val to_ident : Ast.lex_skips -> t -> Ident.t
val to_name : t -> Name.t
val to_name_list : t -> Name.t list * Name.t
val to_string : t -> string

(*
val to_rope : (Ast.lex_skips -> Ulib.Text.t) -> Ulib.Text.t -> t -> Ulib.Text.t
val get_lskip: t -> Ast.lex_skips
val add_pre_lskip : Ast.lex_skips -> t -> t
val drop_parens : t -> t
val is_lower : t -> bool
val is_upper : t -> bool
val to_lower : t -> t
val to_upper : t -> t
val prefix_is_lower : t -> bool
val prefix_is_upper : t -> bool
val prefix_to_lower : t -> t
val prefix_to_upper : t -> t
 *)
