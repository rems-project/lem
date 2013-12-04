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
open Target

(** pattern compilation *)

(** {2 Pattern Compilation } *)

type match_props = {is_exhaustive: bool; missing_pats : pat list list; redundant_pats: (int * pat) list; overlapping_pats: ((int * pat) * (int * pat)) list}

(** [check_match_exp env e] checks the pattern match expression [e] in environment [env]. If
    [e] is not a pattern match, [None] is returned. Otherwise, a record of type [match_props] is
    returned that contains information on whether the match is exhaustive, contains redundant parts etc. *)
val check_match_exp : env -> exp -> match_props option

(** [check_pat_list env pl] checks the pattern list [pL] in environment [env]. If
    [pL] is empty or the compilation fails, [None] is returned. Otherwise, a record of type [match_props] is
    returned that contains information on whether the match is exhaustive, contains redundant parts etc. *)
val check_pat_list : env -> pat list -> match_props option

(** [check_match_exp_warn env e] internally calls [check_match_exp env e]. Instead of returning 
    the properties of the match expression, it prints appropriate warning messages, though. *)
val check_match_exp_warn : env -> exp -> unit

(** [check_match_def env d] checks a definition using pattern matching [d] in environment [env]. 
    Definitions of mutually recursive functions can contain multiple top-level pattern matches.
    Therefore, a list is returned. This lists consists of pairs of
    the name of the defined function and it's properties. If the definition does not have a top-level pattern match,
    i.e. if it is not a function definition, the empty list is returned. *)
val check_match_def : env -> def -> (Name.t * match_props) list 

(** [check_match_def_warn env d] checks a definition and prints appropriate warning messages. *)
val check_match_def_warn : env -> def -> unit


type match_check_arg

(** [cleanup_match_exp env add_missing e] tries to cleanup the match-expression [e] by removing
    redunanant rows. Moreover, missing patterns are added at the end, if the argument [add_missing] 
    is set.*)
val cleanup_match_exp : env -> bool -> exp -> exp option

(** [compile_match_exp target_opt pat_OK env e] compiles match-expressions. In contrast to
    [check_match_exp] only case-expressions are checked. Other types of pattern matches
    have to be brought into this form first.

    If the case-expression [e] contains a pattern [p] such that [pat_OK p] does not hold,
    the whole case-expression is processed and transformed into an expression with
    the same semantics that contains only supported patterns. During this compilation, 
    warning messages might be issued. This warning uses [target_opt]. Otherwise, it is not used.*)
val compile_match_exp : target -> match_check_arg -> env -> exp -> exp option

val compile_exp : target -> match_check_arg -> env -> Macro_expander.macro_context -> exp -> exp option

val compile_def : target -> match_check_arg -> env -> Def_trans.def_macro


val is_isabelle_pattern_match : match_check_arg
val is_hol_pattern_match : match_check_arg
val is_coq_pattern_match : match_check_arg
val is_ocaml_pattern_match : match_check_arg
val is_pattern_match_const : bool -> match_check_arg

(** {2 Other pattern functions } *)

(** [checked_number_patterns env p] checks that all number patterns which are part of [p] are
    of type nat or natural. *)
val check_number_patterns : env -> pat -> unit

(** [remove_function env case_f e] replaces the function expression [e] with with [fun x -> match x with ...].
    The function [case_f] is then applied to the new match-expression. *)
val remove_function : env -> (exp -> exp) -> exp -> exp option

(** [remove_fun env case_f e] replaces the fun-expression [e]. If [e] is of the form [fun p0 ... pn -> e'] such that
    not all patterns [pi] are variable patterns, it is replaced with [fun x0 ... xn -> match (x0, ..., xn) with (p0, ..., pn) -> e'].
    The function [case_f] is then applied to the new match-expression. *)
val remove_fun : env -> (exp -> exp) -> exp -> exp option

(** [remove_toplevel_match] tries to introduce matching directly in the function definition by
    eliminating match-expressions in the body. *)
val remove_toplevel_match : target -> match_check_arg -> env -> Def_trans.def_macro

(** [collapse_nested_matches] tries to eliminate nested matches by collapsing them. It is used internally by pattern
    compilation. *)
val collapse_nested_matches : match_check_arg -> env -> exp -> exp option
