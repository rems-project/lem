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
open Types

(** {2 Types} *)

(** The boolean type *)
val bool_ty : Types.t

(** The natural number type *)
val nat_ty : Types.t


(** {2 Navigating Environments} *)

(** [lookup_env_opt env path] is used to navigate inside a environment [env]. It returns
    the local environment which is reachable via the path [path]. If no such environment exists,
    [None] is returned. *)
val lookup_env_opt : env -> Name.t list -> local_env option

(** [lookup_env] is similar to [lookup_env_opt], but reports an internal
    error instead of returning [None], if no environment can be found. *)
val lookup_env : env -> Name.t list -> local_env

(** [env_apply env comp_opt n] looks up the name [n] in the environment [env]. If 
    component [comp] is given, only this type of component is searched. Otherwise,
    it checks whether [n] refers to a type, field, constructor or constant. [env_apply] returns the
    kind of this name, it's full path and the location of the original definition. *)
val env_apply : env -> Ast.component option -> Name.t -> (name_kind * Path.t * Ast.l) option


(** [lookup_mod_descr_opt env path mod_name] is used to navigate inside an environment [env]. It returns
    the module with name [mod_name], which is reachable via the path [path]. If no such environment exists,
    [None] is returned.*)
val lookup_mod_descr_opt : env -> Name.t list -> Name.t -> mod_descr option

(** [lookup_mod_descr env path mod_name] is used to navigate inside an environment [env]. It returns
    the module with name [mod_name], which is reachable via the path [path]. If no such environment exists,
    [Reporting_basic] is used to report an internal error. *)
val lookup_mod_descr : env -> Name.t list -> Name.t -> mod_descr

(** [names_get_const env path n] looks up the constant with name [n] reachable via path [path] in
   the environment [env] *)
val names_get_const : env -> Name.t list -> Name.t -> const_descr_ref * const_descr 

(** [strings_get_const] is a wrapper around [names_get_const] that uses strings instead of names. *)
val strings_get_const : env -> string list -> string -> const_descr_ref * const_descr

(** [get_const env label] is a wrapper around [string_get_const] that maps a label to an actual constant description. *)
val get_const : env -> string -> const_descr_ref * const_descr

(** [const_exists env label] checks, whether the constant with label [label] is available in the environment [env]. If
    it is [get_const env label] succeeds, otherwise it fails. *)
val const_exists : env -> string -> bool

(** [names_get_const_ref env path n] looks up the constant with name [n] reachable via path [path] in
   the environment [env] *)
(* val names_get_const_ref : env -> Name.t list -> Name.t -> const_descr_ref *)

(** [const_descr_to_kind r d] assumes that [d] is the description associated with reference [r]. It
    then determines the kind of constant (field, constructor, constant) depending on the information
    stored in [d]. *)
val const_descr_to_kind : const_descr_ref * const_descr -> name_kind

(** [strings_get_const_id env l path n inst] uses [get_const env path n] to construct a [const_descr] and
   then wraps it in an id using location [l] and instantiations [inst]. *)
val strings_get_const_id : env -> Ast.l -> string list -> string -> Types.t list -> (const_descr_ref id * const_descr)

(** [get_const_id env l label inst] uses [strings_get_const_id] with an indirection to look up a constant for a given label. *)
val get_const_id : env -> Ast.l -> string -> Types.t list -> (const_descr_ref id * const_descr)

(** [strings_mk_const_exp] uses [get_const_id] to construct a constant expression. *)
val strings_mk_const_exp : env -> Ast.l -> string list -> string -> Types.t list -> exp

(** [mk_const_exp] uses [strings_mk_const_exp] with an indirection through a label. *)
val mk_const_exp : env -> Ast.l -> string -> Types.t list -> exp

(** [dest_field_types l env f] looks up the types of the field [f] in environment [env].
    It first gets the description [f_descr] of the field [f] in [env]. It then looks up
    the type of [f]. For fields, this type is always of the form [field_type --> (free_vars) rec_ty_path].
    [dest_field_types] checks that [free_vars] corresponds with the free typevariables of [f_descr]. 
    If the type of [f] is not of the described from, or if [free_vars] does not correspond, 
    the constant did not describe a proper field. In this case, [dest_field_types] fails. Otherwise,
    it returns [(field_type, rec_ty_path, f_descr)]. *)
val dest_field_types : Ast.l -> env -> const_descr_ref -> Types.t * Path.t * const_descr

(** [get_field_type_descr l env f] uses [dest_field_types l env f] to get the base type of the
    field [f]. It then looks up the description of this type in the environment. *)
val get_field_type_descr : Ast.l -> env -> const_descr_ref -> Types.type_descr

(** [get_field_all_fields l env f] uses [get_field_type_descr l env f] to look up the type description of
    the record type of the field [f]. It then returns a list of all the other fields of this record. *)
val get_field_all_fields : Ast.l -> env -> const_descr_ref -> const_descr_ref list

(** [lookup_class_descr l env c_path] looks up the description of type-class [c_path] in environment [env]. 
    If [c_path] is no valid type-class, an exception is raised. *)
val lookup_class_descr : Ast.l -> env -> Path.t -> Types.class_descr

(** [lookup_field_for_class_method l cd method_ref] looks up the field reference corresponding to 
    the method identified by [method_ref] in the description [cd] of a type class.
    If the reference does not point to a method of this type-class, an exception is raised. *)
val lookup_field_for_class_method : Ast.l -> Types.class_descr -> const_descr_ref -> const_descr_ref

(** [lookup_inst_method_for_class_method l i method_ref] looks up the instance method reference corresponding to 
    the method identified by [method_ref] in the instance [i].
    If the reference does not point to a method of this instance, an exception is raised. *)
val lookup_inst_method_for_class_method : Ast.l -> Types.instance -> const_descr_ref -> const_descr_ref

(** Given a class-description [cd] and an argument type [arg], the function [class_descr_get_dict_type cd arg] generates
    the type of the dictionary for the class and argument type. *)
val class_descr_get_dict_type : Types.class_descr -> Types.t -> Types.t

(** Some targets may choose to not use type-classes to implement certain functions. An example is the equality type-class,
    which is implemented using just the build-in equality of HOL, Coq and Isabelle instead of one determined by
    the type-class. If all methods of a type-class are specially treated like this, the type-class does not need to
    be generated at all. This involves not generating the record definition, not generating instances and not 
    using dictionary style passing for the class. The function [class_all_methods_inlined_for_target l env targ class_path] checks,
    wether all methods of [class_path] are inlined for target [targ]. *)
val class_all_methods_inlined_for_target : Ast.l -> env -> Target.target -> Path.t -> bool

(** [update_const_descr l up c env] updates the description of the constant [c] in environment [env] using
    the function [up]. *)
val update_const_descr : Ast.l -> (const_descr -> const_descr) -> const_descr_ref -> env -> env

(** [c_env_store c_env c_d] stores the description [c_d] 
    environment [c_env]. Thereby, a new unique reference is generated and returned
    along with the modified environment. *)
val c_env_store : c_env -> const_descr -> (c_env * const_descr_ref)

(** [c_env_save c_env c_ref_opt c_d] is a combination of [c_env_update] and [c_env_store].
    If [c_ref_opt] is given, [c_env_update] is called, otherwise [c_env_store]. *)
val c_env_save : c_env -> const_descr_ref option -> const_descr -> c_env * const_descr_ref

(** {2 target-representations} *)

(** [const_target_rep_to_loc rep] returns the location, at which [rep] is defined. *)
val const_target_rep_to_loc : const_target_rep -> Ast.l

(** [const_target_rep_allow_override rep] returns whether this representation can be redefined. 
    Only auto-generated target-reps should be redefinable by the user. *)
val const_target_rep_allow_override : const_target_rep -> bool

(** [type_target_rep_to_loc rep] returns the location, at which [rep] is defined. *)
val type_target_rep_to_loc : type_target_rep -> Ast.l

(** [type_target_rep_allow_override rep] returns whether this representation can be redefined. 
    Only auto-generated target-reps should be redefinable by the user. *)
val type_target_rep_allow_override : type_target_rep -> bool

(** [constant_descr_to_name targ cd] looks up the representation for
    target [targ] in the constant description [cd]. It returns a tuple
    [(n_is_shown, n, n_ascii)]. The name [n] is the name of the
    constant for this target, [n_ascii] an optional ascii alternative.
    [n_is_shown] indiciates, whether this name is actually
    printed. Special representations or inline representation might
    have a name, that is not used for the output. *)
val constant_descr_to_name : Target.target -> const_descr -> (bool * Name.t * Name.t option)


(** [const_descr_ref_to_ascii_name env c] tries to find a simple 
    identifier for constant [c]. The exact identifier does not matter, but should somehow
    be familiar to the user. It looks up the constant names, ascii-representations and
    renamings for various backends. If everything fails, it just makes a name up. *) 
val const_descr_ref_to_ascii_name : c_env -> const_descr_ref -> Name.t

(** [type_descr_to_name targ ty td] looks up the representation for target [targ] in the type
    description [td]. Since in constrast to constant-description, type-descriptions don't contain the
    full type-name, but only renamings, the orginal type-name is passed as argument [ty]. It is assumed that
    [td] really belongs to [ty]. *)
val type_descr_to_name : Target.target -> Path.t -> Types.type_descr -> Name.t

(** [const_descr_rename targ n' l' cd] looks up the representation for target [targ] in the constant
    description [cd]. It then updates this description by renaming to the new name [n'] and new location [l']. 
    The updated description is returned along with information of where the constant was last renamed and to which name. *)
val constant_descr_rename : Target.non_ident_target -> Name.t -> Ast.l -> const_descr -> (const_descr * (Ast.l * Name.t) option)

(** [mod_descr_rename targ mod_name n' l' md] updates the representation for target [targ] in the module
    description [md] by renaming to the new name [n'] and new location [l'].
    In case a target representation was already present, a type-check error is raised. *)
val mod_target_rep_rename : Target.non_ident_target -> string -> Name.t -> Ast.l -> mod_target_rep Target.Targetmap.t -> mod_target_rep Target.Targetmap.t

(** [type_descr_rename targ n' l' td] looks up the representation for target [targ] in the type
    description [td]. It then updates this description by renaming to the new name [n'] and new location [l']. 
    The updated description is returned along with information of where the type
    was last renamed and to which name. *)
val type_descr_rename : Target.non_ident_target -> Name.t -> Ast.l -> Types.type_descr -> Types.type_descr * (Ast.l * Name.t) option

(** [type_def_rename_type l d p t n] renames the type with path [p] in the defs [d] to the name [n] for
target [t]. Renaming means that the module structure is kept. Only the name is changed. *)
val type_defs_rename_type: Ast.l -> Types.type_defs -> Path.t -> Target.non_ident_target -> Name.t -> Types.type_defs

(** [const_descr_has_target_rep targ d] checks whether the description [d] contains
    a target-representation for target [targ]. *)
val const_descr_has_target_rep : Target.target -> Typed_ast.const_descr -> bool

(** {2 Constructing, checking and destructing expressions} *)

(** [mk_name_lskips_annot] creates an annoted name *)
val mk_name_lskips_annot : Ast.l -> Name.lskips_t -> Types.t -> name_lskips_annot 

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

(** [is_t_exp v e] checks whether [e] is the [true] expression. *)
val is_t_exp : exp -> bool

(** [is_f_exp v e] checks whether [e] is the [false] expression. *)
val is_f_exp : exp -> bool

(** Destructor for constants expressions *)
val dest_const_exp : exp -> const_descr_ref id option

(** [is_const_exp e] checks whether [e] is a constant expression *)
val is_const_exp : exp -> bool

(** [dest_num_exp e] destructs a number literal expression. *)
val dest_num_exp : exp -> int option

(** [is_num_exp] checks whether [e] is a number literal expression. *)
val is_num_exp : exp -> bool

(** [mk_num_exp] creates a number literal expression. *)
val mk_num_exp : Types.t -> int -> exp

(** [is_empty_backend_exp] checks whether the expression is [``] *)
val is_empty_backend_exp : exp -> bool

(** [mk_eq_exp env e1 e2] constructs the expression [e1 = e2]. The environment [env] is needed
    to lookup the equality constant. *)
val mk_eq_exp : env -> exp -> exp -> exp

(** [mk_and_exp env e1 e2] constructs the expression [e1 && e2]. The environment [env] is needed
    to lookup the conjunction constant. *)
val mk_and_exp : env -> exp -> exp -> exp

(** [mk_and_exps env es] constructs the conjunction of all expressions in es. The environment [env] is needed
    to lookup the conjunction constant. *)
val mk_and_exps : env -> exp list -> exp

(** [dest_and_exps env e] extracts the arguments from a conjunction
    expression [e].  The environment [env] is needed to lookup the
    conjunction constant.

    It is an inverse for [mk_and_exps] when the inner expression are
    not themselves conjunctions. *)
val dest_and_exps : env -> exp -> exp list

(** [mk_le_exp env e1 e2] constructs the expression [e1 <= e2]. The environment [env] is needed
    to lookup the less-equal constant. *)
val mk_le_exp : env -> exp -> exp -> exp

(** [mk_sub_exp env e1 e2] constructs the expression [e1 - e2]. The environment [env] is needed
    to lookup the subtraction constant. *)
val mk_sub_exp : env -> exp -> exp -> exp

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

(** [mk_opt_fun_exp pL e] returns [mk_fun_exp pL e] if [pL] is not empty and [e] otherwise. *)
val mk_opt_fun_exp : pat list -> exp -> exp

(** [mk_app_exp d e1 e2] constructs the expression [e1 e2]. The type definitions [d] are needed
    for typechecking. *)
val mk_app_exp : Ast.l -> Types.type_defs -> exp -> exp -> exp

(** [mk_list_app_exp d f [a1 ... an]] constructs the expression [f a1 ... an] by repeatedly calling [mk_app_exp]. *)
val mk_list_app_exp : Ast.l -> Types.type_defs -> exp -> exp list -> exp

(** [mk_eta_expansion_exp d vars e] for variables [vars = [x1, ..., xn]] tries to build the expression
    [fun x1 ... xn -> (e x1 ... xn)]. The variable names might be changed to ensure that they are distinct to
    each other and all variables already present in [e]. *)
val mk_eta_expansion_exp : Types.type_defs -> Name.t list -> exp -> exp

(** [mk_paren_exp e] adds parenthesis around expression [e]. Standard whitespaces are applied. This
    means that whitespace (except comments) are deleted before expression [e]. *)
val mk_paren_exp : exp -> exp

(** [mk_opt_paren_exp e] adds parenthesis around expression [e] if it seems sensible. 
    For parenthesis, variable expressions and tuples, the parenthesis are skipped, though. *)
val mk_opt_paren_exp : exp -> exp

(** [may_need_paren e] checks, whether [e] might need parenthesis. If returns, whether [mk_opt_paren_exp e]
    would modify the expression. *)
val may_need_paren : exp -> bool

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

(** [dest_app_exp e] tries to destruct an function application expression [e]. *)
val dest_app_exp : exp -> (exp * exp) option

(** [strip_app_exp e] tries to destruct multiple function applications. It returns a pair
    [(base_fun, arg_list)] such that [e] is of the form [base_fun arg_list_1 ... arg_list_n].
    If [e] is not a function application expression, the list [arg_list] is empty. *)
val strip_app_exp : exp -> exp * exp list


(** [dest_infix_exp e] tries to destruct an infix expression [e]. If [e] is of the form
    [l infix_op r] then [Some (l, infix_op, r)] is returned, otherwise [None]. *)
val dest_infix_exp : exp -> (exp * exp * exp) option

(** [is_infix_exp e] checks whether [e] is an infix operation *)
val is_infix_exp : exp -> bool

(** [strip_infix_exp e] is similar to [dest_infix_exp], but returns the result in the same way as
    [strip_app_exp]. If [e] is of the form
    [l infix_op r] then [(infix_op, [l;r])] is returned, otherwise [(e, [])]. *)
val strip_infix_exp : exp -> exp * exp list 

(** [strip_app_infix_exp e] is a combination of [strip_infix_exp] and [strip_app_exp]. 
    The additional boolean result states, whether [e] is an infix operation. 
    If [e] is an infix operation [strip_infix_exp] is called and the additional boolean result
    is [true]. Otherwise [strip_app_exp] is called and the result is set to [false]. *)
val strip_app_infix_exp : exp -> exp * exp list * bool


(** {2 Constructing, checking and destructing definitions} *)

(** [is_type_def_abbrev d] checks whether the definition [d] is a 
    type-abbreviation definition. *)
val is_type_def_abbrev : def -> bool

(** [is_type_def_abbrev d] checks whether the definition [d] is a 
    definition of a record_type. *)
val is_type_def_record : def -> bool


(** {2 Collecting information about uses constants, types, modules ...} *)

(** The type [used_entities] collects lists of used constant references, modules and types of some expression, definition, pattern ... 
   used_entities is using lists, because the order in which entities occur might be important for renaming.
   However, these lists should not contain duplicates. *)
type used_entities = { 
   used_consts : const_descr_ref list; 
   used_consts_set : Cdset.t;
   used_types : Path.t list; 
   used_types_set : Pset.t;
   used_modules : Path.t list; 
   used_modules_set : Pset.t;
   used_tnvars : TNset.t }

(** An empty collection of entities *)
val empty_used_entities : used_entities

val add_exp_entities : used_entities -> exp -> used_entities

(** [add_def_aux_entities targ only_new ue def] adds all the modules, types, constants ... used by definition [def] for target 
    [targ] to [ue]. If the flag [only_new] is set, only the newly defined are added. 
    Notice, that the identity backend won't throw parts of modules away. Therefore the result for the identiy backend
    is the union of the results for all other backends. *)
val add_def_aux_entities : Target.target -> bool -> used_entities -> Typed_ast.def_aux -> used_entities

(** [add_def_entities] is called [add_def_aux_entities] after extracting the appropriate [def_aux]. *)
val add_def_entities : Target.target -> bool -> used_entities -> Typed_ast.def -> used_entities

(** [get_checked_module_entities targ only_new ml] gets all the modules, types, constants ... used by modules [ml] for target 
    [targ]. If the flag [only_new] is set, only the newly defined are returned. 
    Notice, that the identity backend won't throw parts of modules away. Therefore the result for the identiy backend
    is the union of the results for all other backends. *)
val get_checked_modules_entities : Target.target -> bool -> checked_module list -> used_entities


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

(** [is_recursive_def d] checks whether [d] is recursive. It returns a pair of booleans [(is_syntactic_rec, is_real_rec)].
    The flag [is_syntactic_rec] states, whether the definition was made using the [rec]-keyword. The flag [is_real_rec] states,
    whether the function actually appears inside its own definition. *)
val is_recursive_def : def_aux -> bool * bool

(** [try_termination_proof targ c_env d] calls [is_recursive_def d]. It further checks, whether a termination proof for target [targ] should be tried by
    checking the termination settings of all involved constants. It returns a triple [(is_syntactic_rec, is_real_rec, try_auto_termination)]. *)
val try_termination_proof : Target.target -> c_env -> def_aux -> bool * bool * bool

(** [is_pp_loc l] checks whether [l] is of the form [Ast.Trans (true, _, _)]. This means
    that the entity marked with [l] should be formated using a pretty printer that calculates whitespaces new instead
    of using the ones provided by the user.  *)
val is_pp_loc : Ast.l -> bool

val is_pp_exp : exp -> bool
val is_pp_def : def -> bool

(** [val_def_get_name d] tries to extract the name of the defined function. *)
val val_def_get_name : val_def -> Name.lskips_t option 

(** [val_def_get_class_constraints_no_target_rep env targ vd] collects the class constraints of all top-level function definitions
    in [vd], which don't have a target-specific representation for target [targ]. Warning: contraints may appear multiple times in the resulting list *)
val val_def_get_class_constraints_no_target_rep : env -> Target.target -> val_def -> (Path.t * Types.tnvar) list

(** [val_def_get_class_constraints env vd] collects the class constraints of all top-level function definitions
    in [vd]. Warning: contraints may appear multiple times in the resulting list *)
val val_def_get_class_constraints : env -> val_def -> (Path.t * Types.tnvar) list

(** [val_def_get_free_tnvars env vd] returns the set of all free type-variables used by [vd]. *)
val val_def_get_free_tnvars : env -> val_def -> Types.TNset.t

(** [env_tag_to_string tag] formats [tag] as a string. This functions should only be used
    for human-readable output in e.g. error-messages. *)
val env_tag_to_string : env_tag -> string


(** [constr_family_to_id l env ty cf] tries to instantiate the constructor family [cf] to be used
    on a match statement where the matched type is [ty]. If it succeeeds the properly instantiated 
    construtor ids + the instantiated case split function is returned. However, returning the case-split
    function is a bit complicated. It depends on the return type of match expression as well. Moreover, it
    might not be there at all, if the targets build-in pattern matching should be used to construct one.
    Therefore, an optional function from a type (the return type) to an id is returned for the case-split function. *)
val constr_family_to_id : Ast.l -> env -> Types.t -> constr_family_descr -> ((const_descr_ref id) list * (t -> (const_descr_ref id)) option) option

(** [check_constr_family] is similar to [constr_family_to_id]. It does not return the instantiations though, but 
    produces a nicely formatted error, in case no such instantiations could be found. *)
val check_constr_family : Ast.l -> env -> Types.t -> constr_family_descr -> unit

(** [check_for_inline_cycles targ env] checks whether any constant in [env] would be inlined (possible over several steps) onto
    itself. If this happens, an exception is thrown. *)
val check_for_inline_cycles : Target.target -> c_env -> unit
