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

(** syntax functions for typed_ast *)

open Typed_ast

(** {2 Types} *)

(** The boolean type *)
val bool_ty : Types.t

(** The natural number type *)
val num_ty : Types.t


(** {2 Navigating Environments} *)

(** [lookup_env env path] is used to navigate inside an environment [env]. It opens
    the environment which is reachable via the path [path]. *)
val lookup_env : env -> Name.t list -> env

(** [names_get_const env path n] looks up the constant with name [n] reachable via path [path] in
   the environment [env] *)
val names_get_const : env -> Name.t list -> Name.t -> const_descr

(** [get_const] is a wrapper around [names_get_const] that uses strings instead of names. *)
val get_const : env -> string list -> string -> const_descr

(** [get_const_id env l path n inst] used [get_const env path n] to construct a [const_descr] and
   then wraps it in an id using location [l] and instantiations [inst]. *)
val get_const_id : env -> Ast.l -> string list -> string -> Types.t list -> const_descr id

(** [mk_const_exp] uses [get_const_id] to construct a constant expression. *)
val mk_const_exp : env -> Ast.l -> string list -> string -> Types.t list -> exp

(** {2 Constructing, checking and destructing expressions} *)

(** Destructor for variable expressions *)
val dest_var_exp : exp -> Name.t option

(** [is_var_exp e] checks whether [e] is a variable expression *)
val is_var_exp : exp -> bool

(** Destructor for tuple expressions. Similar to pattern destructors for tuples
    an optional argument to check the number of elements of the tuple. *)
val dest_tup_exp : int option -> exp -> exp list option

(** [is_tup_exp s_opt e] checks whether [e] is a tuple of size [s_opt]. *)
val is_tup_exp : int option -> exp -> bool

(** [is_var_tup_exp e] checks, whether [e] is an expression consisting only of
    variables and tuples. I.e. simple variable expressions, tuples containing
    only variables and tuples containing other variable-tuples are accepted. *)
val is_var_tup_exp : exp -> bool 

(** [mk_tf_exp] creates [true] and [false] expressions. *)
val mk_tf_exp : bool -> exp

(** [dest_tf_exp] destructs [true] and [false] expressions. *)
val dest_tf_exp : exp -> bool option

(** [is_tf_exp v e] checks whether [e] is a [true] or [false] expression. *)
val is_tf_exp : bool -> exp -> bool

(** [dest_num_exp e] destructs a number literal expression. *)
val dest_num_exp : exp -> int option

(** [is_num_exp] checks whether [e] is a number literal expression. *)
val is_num_exp : exp -> bool

(** [mk_num_exp] creates a number literal expression. *)
val mk_num_exp : int -> exp

(** [mk_eq_exp env e1 e2] constructs the expression [e1 = e2]. The environment [env] is needed
    to lookup the equality constant. *)
val mk_eq_exp : env -> exp -> exp -> exp

(** [mk_and_exp env e1 e2] constructs the expression [e1 && e2]. The environment [env] is needed
    to lookup the conjunction constant. *)
val mk_and_exp : env -> exp -> exp -> exp

(** [mk_le_exp env e1 e2] constructs the expression [e1 <= e2]. The environment [env] is needed
    to lookup the less-equal constant. *)
val mk_le_exp : env -> exp -> exp -> exp

(** [mk_add_exp env e1 e2] constructs the expression [e1 + e2]. The environment [env] is needed
    to lookup the add constant. *)
val mk_add_exp : env -> exp -> exp -> exp

(** [mk_sub_exp env e1 e2] constructs the expression [e1 - e2]. The environment [env] is needed
    to lookup the subtraction constant. *)
val mk_sub_exp : env -> exp -> exp -> exp

(** [mk_num_add_exp env n i] constructs the expression [(n + i)]. The environment [env] is needed
    to lookup the add constant. *)
val mk_num_add_exp : env -> Name.t -> int -> exp

(** [mk_num_sub_exp env n i] constructs the expression [(n - i)]. The environment [env] is needed
    to lookup the sub constant. *)
val mk_num_sub_exp : env -> Name.t -> int -> exp

(** [mk_from_list_exp env e] constructs the expression [Set.from_list e]. The environment [env] is needed
    to lookup the from-list constant. *)
val mk_from_list_exp : env -> exp -> exp

(** [mk_cross_exp env e1 e2] constructs the expression [cross e1 e2]. The environment [env] is needed
    to lookup the cross constant. *)
val mk_cross_exp : env -> exp -> exp -> exp

(** [mk_set_sigma_exp env e1 e2] constructs the expression [set_sigma e1 e2]. The environment [env] is needed
    to lookup the sigma constant. *)
val mk_set_sigma_exp : env -> exp -> exp -> exp

(** [mk_set_filter_exp env e_P e_s] constructs the expression [Set.filter e_P e_s]. The environment [env] is needed
    to lookup the constant. *)
val mk_set_filter_exp : env -> exp -> exp -> exp

(** [mk_set_image_exp env e_f e_s] constructs the expression [Set.image e_f e_s]. The environment [env] is needed
    to lookup the constant. *)
val mk_set_image_exp : env -> exp -> exp -> exp

(** [mk_fun_exp [p1, ..., pn] e] constructs the expression [fun p1 ... pn -> e]. *)
val mk_fun_exp : pat list -> exp -> exp

(** [mk_paren_exp e] adds parenthesis around expression [e]. Standard whitespaces are applied. This
    means that whitespace (except comments) are deleted before expression [e]. *)
val mk_paren_exp : exp -> exp

(** [mk_opt_paren_exp e] adds parenthesis around expression [e] if it seems sensible. 
    For parenthesis, variable expressions and tuples, the parenthesis are skipped, though. *)
val mk_opt_paren_exp : exp -> exp

(** [mk_case_exp final l e rows ty] constructs a case (match) expression. In contrast to
    [Typed_ast.mk_case] it uses standard spacing and adds parenthesis. *)
val mk_case_exp : bool -> Ast.l -> exp -> (pat * exp) list -> Types.t -> exp 

(** [mk_let_exp l (n, e1) e2] constructs the expression [let n = e1 in e2] using
    default spacing. *)
val mk_let_exp : Ast.l -> (Name.t * exp) -> exp -> exp

(** [mk_if_exp l c e_t e_f] constructs the expression [if c then e_t else e_f] using
    default spacing. *)
val mk_if_exp : Ast.l -> exp -> exp -> exp -> exp

(** [mk_undefined_exp l m ty] constructs an undefined expression of type [ty] with message [m]. *)
val mk_undefined_exp : Ast.l -> string -> Types.t -> exp

(** [mk_dummy_exp ty] constructs a dummy expression of type [ty]. This is an expression that should
    never be looked at. It is only guaranteed to be an expression of this type. *)
val mk_dummy_exp : Types.t -> exp


(** {2 Miscellaneous} *)

(** [remove_init_ws] should be used with function like [Typed_ast.alter_init_lskips]. It removes
    whitespace expect comments. *)
val remove_init_ws : Ast.lex_skips -> (Ast.lex_skips * Ast.lex_skips)

(** [drop_init_ws] should be used with function like [Typed_ast.alter_init_lskips]. It removes
    whitespace including comments. *)
val drop_init_ws : Ast.lex_skips -> (Ast.lex_skips * Ast.lex_skips)

(** [space_init_ws] should be used with function like [Typed_ast.alter_init_lskips]. It replaces
    whitespace including comments with a single space. *)
val space_init_ws : Ast.lex_skips -> (Ast.lex_skips * Ast.lex_skips)

(** [space_com_init_ws] should be used with function like [Typed_ast.alter_init_lskips]. It replaces
    whitespace except comments with a single space. *)
val space_com_init_ws : Ast.lex_skips -> (Ast.lex_skips * Ast.lex_skips)

(** [strip_paren_typ_exp e] strips parenthesis and type-annotations form expression [e].
    Warning: This might delete white-space! *)
val strip_paren_typ_exp : exp -> exp

(** [is_recursive_def d] checks whether [d] is recursive. Instead of just looking at the type,
    it actually checks, whether a recursive call actually is present. *)
val is_recursive_def : def -> bool

(** [is_trans_loc l] checks whether [l] is of the form [Ast.Trans _] *)
val is_trans_loc : Ast.l -> bool

val is_trans_exp : exp -> bool
val is_trans_def : def -> bool
