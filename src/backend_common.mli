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

(** Functions used by multiple backends *)

open Typed_ast 
open Types

(** [inline_exp_macro target env] does the inlining of target specific constant definitions *)
val inline_exp_macro : Target.non_ident_target -> env -> Macro_expander.macro_context -> exp -> exp option

(** [inline_pat_macro target env] does the inlining of target specific constant definitions *)
val inline_pat_macro : Target.non_ident_target -> env -> _ -> _ -> pat -> pat option

(** [component_to_output c] formats component [c] as an output *)
val component_to_output : Ast.component -> Output.t

(** [get_module_name env targ mod_path mod_name] looks up the name of module [mod_path.mod_name] in environment [env] for
    target [targ].*)
val get_module_name : env -> Target.target -> Name.t list -> Name.t -> Name.t

(** [get_module_open_string l env targ mod_id] looks up how to represent this module in import / open statements. The module might
    well be replaced with a whole list of other modules or nothing. It returns a preceeding skip plus a list of strings. *)
val get_module_open_string : env -> Target.target -> Path.t id -> lskips * string list

(** [format_module_open_string targ s] formats the open string [s] for target [targ]. For HOL the suffix "Theory" is for example
    added. *)
val format_module_open_string : Target.target -> string -> string

module Make(A : sig
  val env : env;; 
  val target : Target.target;;
  val id_format_args : (bool -> Output.id_annot -> Ulib.Text.t -> Output.t) * Output.t
 end) : sig

val open_to_open_target : (Path.t id) list -> (lskips * string) list * lskips

(** [function_application_to_output l exp inf full_exp c_id args] tries to format
    a function application as output. It gets an expression [full_ex] of the from
    [c arg1 ... argn]. The id [c_id] corresponds to constant [c]. The arguments [arg1, ... argn] are 
    handed over as [args]. The description corresponding to [c] is looked up in [A.env]. Depending on
    this description and the backend-specific formats therein, the
    function and its arguments are formated as output.  In the
    simplest case the representation is an identifier ([Ident.t]),
    which is formated using [A.id_format_args] and the information, 
    whether it the whole expression is an infix one [inf]. In more complicated
    cases, formating of expressions is needed, which is done via the
    callback [exp]. In particular if some arguments are not needed by
    the formating of the function application, the function [exp] is
    called on these remaining arguments. The original expression [full_exp] is
    needed, if not enough parameters are present to format the definition correctly. 
    In this case, eta-expansion is applied and the resulting expression formatting via [exp].
    [ascii_alternative] denotes whether an ascii alternative representation for this
    function name is required.
*)
val function_application_to_output : Ast.l -> (exp -> Output.t) -> bool -> exp -> const_descr_ref id -> exp list -> bool -> Output.t list

(** [pattern_application_to_output pat c_id args] tries to
    format a function application in a pattern as output. It does otherwise the same as
    function_application_to_output. However, since there are no infix patterns, the
    parameter [inf] is always set to [false]. 
*)
val pattern_application_to_output : (pat -> Output.t) -> const_descr_ref id -> pat list -> bool -> Output.t list

(** [const_id_to_ident c_id use_ascii] tries to format a constant, constructor or field
    [c_id] as an identifier for target [A.target] using the rules stored
    in environment [A.env]. If the flag [use_ascii] is set, the ascii representation of the
    constant should be used, if there is one. Depending on the formating rules for the
    constant, [const_id_to_ident] might raise an exception. *)
val const_id_to_ident : const_descr_ref id -> bool -> Ident.t 


(** [const_ref_to_name n use_ascii c] tries to format a constant
    [c] for target [A.target] using the rules stored
    in environment [A.env]. If [use_ascii] is set, the ascii-representation is
    returned. [const_ref_to_name] always returns a name [n']. If special formatting
    rules are installed, this name might not be the one used by [function_application_to_output], though.
    The argument [n] is the name used in the original input. It's whitespace is used to
    format [n']. *)
val const_ref_to_name : Name.lskips_t -> bool -> const_descr_ref -> Name.lskips_t

(** [type_path_to_name n p] tries to format a type-path
    [p] for target [A.target] using the rules stored
    in environment [A.env]. It always returns a name [n']. If special formatting
    rules are installed, this name might not be the one used by [function_application_to_output], though.
    The argument [n] is the name used in the original input. It's whitespace is used to
    format [n']. *)
val type_path_to_name : Name.lskips_t -> Path.t -> Name.lskips_t

(** [type_id_to_ident ty_id] tries to format a type
    [ty_id] as an identifier for target [A.target] using the rules stored
    in environment [A.env]. 
*)
val type_id_to_ident : Path.t id -> Ident.t

(** [type_id_to_ident_no_modify ty_id] formats [ty_id] as an identifier.
    In contrast to [type_id_to_ident] neither the target [A.target] nor the rules stored
    in environment [A.env] are used. Instead the type is translated without any
    modifications. This method is intended to be used for backend types, which
    are already formatted.
*)
val type_id_to_ident_no_modify : Path.t id -> Ident.t

val type_app_to_output : (src_t -> Output.t) -> Path.t id -> src_t list -> (src_t list * Output.t)

(** [module_id_to_ident m_id] tries to format a module
    [m_id] as an identifier for target [A.target] using the rules stored
    in environment [A.env]. 
*)
val module_id_to_ident : Path.t id -> Ident.t

end
