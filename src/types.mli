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

val report_default_instance_invocation : bool ref

type tnvar =
  | Ty of Tyvar.t
  | Nv of Nvar.t

val pp_tnvar: Format.formatter -> tnvar -> unit
val tnvar_to_rope: tnvar -> Ulib.Text.t
val tnvar_compare: tnvar -> tnvar -> int

module TNvar : sig
  type t = tnvar
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module Pfmap : Finite_map.Fmap with type k = Path.t
module Pset: Set.S with type elt = Path.t
module TNfmap : Finite_map.Fmap with type k = TNvar.t
module TNset : sig
  include Set.S with type elt = TNvar.t
  val pp : Format.formatter -> t -> unit
end

type t_uvar
type n_uvar
type t = { mutable t : t_aux }
and t_aux =
  | Tvar of Tyvar.t
  | Tfn of t * t
  | Ttup of t list
  | Tapp of t list * Path.t
  | Tbackend of t list * Path.t (* a backend type that should be preserved litterally *)
  | Tne of nexp
  | Tuvar of t_uvar
and nexp = { mutable nexp : nexp_aux }
and nexp_aux =
  | Nvar of Nvar.t
  | Nconst of int
  | Nadd of nexp * nexp
  | Nmult of nexp * nexp
  | Nneg of nexp (* Unary minus for representing new vector sizes after vector slicing *)
  | Nuvar of n_uvar

(* Constraints for nexps, plus the location which added the constraint, each nexp is either <= 0 = 0 or >= 0 *)
type range =
  | LtEq of Ast.l * nexp
  | Eq of Ast.l * nexp
  | GtEq of Ast.l * nexp

val range_with : range -> nexp -> range
val range_of_n : range -> nexp
val mk_gt_than : Ast.l -> nexp -> nexp -> range
val mk_eq_to   : Ast.l -> nexp -> nexp -> range


(** Structural comparison of types, without expanding type abbreviations.
    Probably better not to use. Consider using [compare_expand] instead. *)
val compare : t -> t -> int


val multi_fun : t list -> t -> t
val type_subst : t TNfmap.t -> t -> t
val nexp_subst : t TNfmap.t -> nexp -> nexp
val free_vars : t -> TNset.t
val is_var_type : t -> bool

(** is the type ok to be used in an non-default type-class instantiation? *)
val is_instance_type : t -> bool

val tnvar_to_name : tnvar -> Name.t
val tnvar_to_type : tnvar -> t
val tnvar_split : tnvar list -> (tnvar list * tnvar list)

(** A reference to a constant description. These constant description references
    are used by [typed_ast]. This module also contains the appropriate mapping
    functionality to constant descriptions. However, the references need to
    be defined here, because types need information about associated constants.
    Record types need a list of all their field constants. Moreover, every type
    can contain a list of constructor descriptions. *)
type const_descr_ref 

(** [string_of_const_descr_ref] formats a reference in a human readable form.
    No other guarentees are given. This function should only be used for debugging 
    and reporting internal errors. Its implementation can change at any point to 
    something completely different and should not be relied on. *)
val string_of_const_descr_ref : const_descr_ref -> string

module Cdmap : Finite_map.Fmap with type k = const_descr_ref
module Cdset : Set.S with type elt = const_descr_ref

(** [cdmap] is a type for maps of const_descr_ref. In contrast to finite maps
    represented by module [Cdmap], the keys might be autogenerated. *)
type 'a cdmap

(** Constructs an empty cdmap *)
val cdmap_empty : unit -> 'a cdmap

(** [cdmap_lookup m r] looks up the reference [r] in map [m] *)
val cdmap_lookup : 'a cdmap -> const_descr_ref -> 'a option

(** [cdmap_update m r v] updates map [m] at reference [r] with value [v]. *)
val cdmap_update : 'a cdmap -> const_descr_ref -> 'a -> 'a cdmap

(** [cdmap_insert m v] inserts value [v] into [m]. A fresh (not occurring in [m]) reference
    is generated for [v] and returned together with the modifed map. *)
val cdmap_insert : 'a cdmap -> 'a -> ('a cdmap * const_descr_ref)

(** [cdmap_domain m] returns the list of all const description references in the map *)
val cdmap_domain : 'a cdmap -> const_descr_ref list

(** [nil_const_descr_ref] is a nil reference, i.e. a reference that will never be bound
    by any cdmap. *)
val nil_const_descr_ref : const_descr_ref

(** [is_nil_const_descr_ref r] checks whether [r] is the nil reference. *)
val is_nil_const_descr_ref : const_descr_ref -> bool

type ('a,'b) annot = { term : 'a; locn : Ast.l; typ : t; rest : 'b }
val annot_to_typ : ('a,'b) annot -> t

type ident_option =
  | Id_none of Ast.lex_skips
  | Id_some of Ident.t


(** Represents a usage of an 'a (usually in constr_descr, field_descr,
    const_descr) *)
type 'a id = 
    { 
      id_path : ident_option; 
      (** The identifier as written at the usage point.  None if it is generated
          internally, and therefore has no original source *)

      id_locn : Ast.l;
      (** The location of the usage point *)

      descr : 'a; 
      (** A description of the binding that the usage refers to *)

      instantiation : t list;
      (** The usage site instantiation of the type parameters of the definition *)
    }


(* The AST.  Ast.lex_skips appear in the types wherever concrete syntactic elements
 * would appear (e.g., a keyword), and represent the comments and whitespace
 * that preceded that concrete element.  They do not represent the element
 * itself *)
and src_t = (src_t_aux,unit) annot

and src_t_aux = 
 | Typ_wild of Ast.lex_skips
 | Typ_var of Ast.lex_skips * Tyvar.t
 | Typ_len of src_nexp
 | Typ_fn of src_t * Ast.lex_skips * src_t
 | Typ_tup of (src_t, Ast.lex_skips) Seplist.t
 | Typ_app of Path.t id * src_t list
 | Typ_backend of Path.t id * src_t list (** a backend type that should be used literally *)
 | Typ_paren of Ast.lex_skips * src_t * Ast.lex_skips

and src_nexp = { nterm : src_nexp_aux; nloc : Ast.l; nt : nexp } (*(src_nexp_aux,unit) annot*)

and src_nexp_aux =
 | Nexp_var of Ast.lex_skips * Nvar.t 
 | Nexp_const of Ast.lex_skips * int
 | Nexp_mult of src_nexp * Ast.lex_skips * src_nexp (* One will always be const *)
 | Nexp_add of src_nexp * Ast.lex_skips * src_nexp 
 | Nexp_paren of Ast.lex_skips * src_nexp * Ast.lex_skips

val src_t_to_t : src_t -> t
val src_type_subst : src_t TNfmap.t -> src_t -> src_t

val id_alter_init_lskips : (Ast.lex_skips -> Ast.lex_skips * Ast.lex_skips) -> 'a id -> 'a id * Ast.lex_skips
val typ_alter_init_lskips : (Ast.lex_skips -> Ast.lex_skips * Ast.lex_skips) -> src_t -> src_t * Ast.lex_skips 
val nexp_alter_init_lskips : (Ast.lex_skips -> Ast.lex_skips * Ast.lex_skips) -> src_nexp -> src_nexp * Ast.lex_skips

type constr_family_descr = { 
   constr_list : const_descr_ref list; 
   constr_exhaustive : bool;
   constr_case_fun : const_descr_ref option;
   constr_default : bool;
   constr_targets : Target.Targetset.t;
}

(** the target representation of a type *)
type type_target_rep =
  | TYR_simple of Ast.l *  bool * Ident.t
  | TYR_subst of Ast.l *  bool * tnvar list * src_t 

(** a type description  **)
type type_descr = { 
  type_tparams : tnvar list;
  (** a list of type and length parameters *)

  type_abbrev : t option;
  (** if it is an abbreviation, the type it abbreviates *)

  type_varname_regexp : (string * Str.regexp) option;
  (** an optional regular expression that variable names that have the
   * type must match, stored in literal and pre-compiled form *)

  type_fields : (const_descr_ref list) option;
  (** if it is a record type, the list of fields *)

  type_constr : constr_family_descr list;
  (** the constructors of this type *)
  
  type_rename : (Ast.l * Name.t) Target.Targetmap.t;
  (** target representation of the type *)

  type_target_rep : type_target_rep Target.Targetmap.t;
  (** target representation of the type *)
}

type class_descr = { 
  class_tparam : tnvar; (** the type paremeter of the type class *)
  class_record : Path.t; (** for dictionary style passing a corresponding record is defined, this is its path *)
  class_methods : (const_descr_ref * const_descr_ref) list; 
   (** The methods of the class. For each method there is a corresponding record field. Therefore, methods are represented by pairs
       (method_ref, field_ref). Details like the names and types can be looked up in the environment. *)
  class_rename : (Ast.l * Name.t) Target.Targetmap.t;
  class_target_rep : type_target_rep Target.Targetmap.t;
  class_is_inline : bool
}

type tc_def = 
  | Tc_type of type_descr
  | Tc_class of class_descr

type type_defs = tc_def Pfmap.t

(** [type_defs_update_tc_type l d p up] updates the description of type [p] in [d] using the function [up].
    If there is no type [p] in [d] or if [up] returns [None], an exception is raised. *)
val type_defs_update_tc_type : Ast.l -> type_defs -> Path.t -> (type_descr -> type_descr option) -> type_defs

(** [type_defs_update_tc_class l d p up] updates the description of type [p] in [d] using the function [up].
    If there is no type [p] in [d] or if [up] returns [None], an exception is raised. *)
val type_defs_update_tc_class : Ast.l -> type_defs -> Path.t -> (class_descr -> class_descr option) -> type_defs

(** [type_defs_update_fields l d p fl] updates the fields of type [p] in [d]. *)
val type_defs_update_fields : Ast.l -> type_defs -> Path.t -> const_descr_ref list -> type_defs

val type_defs_add_constr_family : Ast.l -> type_defs -> Path.t -> constr_family_descr -> type_defs

(** [type_defs_get_constr_families l d targ t c] gets all constructor family descriptions for type [t] 
    for target [targ] in type environment [d], which contain the constant [c]. *)
val type_defs_get_constr_families : Ast.l -> type_defs -> Target.target -> t -> const_descr_ref -> constr_family_descr list

(** [type_defs_lookup_typ l d t] looks up the description of type [t] in defs [d]. *)
val type_defs_lookup_typ : Ast.l -> type_defs -> t -> type_descr option

(** [type_defs_lookup l d p] looks up the description of type with path [p] in defs [d]. *)
val type_defs_lookup : Ast.l -> type_defs -> Path.t -> type_descr

(** [type_defs_update d p td] updates the description of type with path [p] in defs [d] with [td]. *)
val type_defs_update : type_defs -> Path.t -> type_descr -> type_defs

(** Generates a type abbreviation *)
val mk_tc_type_abbrev : tnvar list -> t -> tc_def

(** [mk_tc_type vars reg_exp_opt] generates a simple description of a type,
    which uses the type arguments [vars] and the [reg_exp_opt] for restricting
    the names of variables of this type. *)
val mk_tc_type : tnvar list -> string option -> tc_def

(** [match_types t_pat t] tries to match type [t_pat] against type [t].
    If it succeeds, it returns a substitution [sub] that applied to [t_pat] returns [t]. 
    This function is rather simple. It does not use type synonyms or other fancy features. *)
val match_types : t -> t -> (t TNfmap.t) option

(** an instance of a type class *)
type instance = {
  inst_l : Ast.l; (** The location, the instance was declared *)
  inst_is_default : bool; (** Is it a fallback / default instance or a real one ? *)
  inst_binding : Path.t; (** The path of the instance *)
  inst_class : Path.t; (** The type class, that is instantiated *)
  inst_type : t; (** The type, the type-class is instantiated with *)
  inst_tyvars : tnvar list; (** The free type variables of this instance *)
  inst_constraints : (Path.t * tnvar) list; (** Type class constraints on the free type variables of the instance *)
  inst_methods : (const_descr_ref * const_descr_ref) list; (** The methods of this instance. Since each instance method corresponds to one
    class method it instantiates, the methods are given as a list of pairs [(class_method_ref, instance_method_ref)]. *)
  inst_dict : const_descr_ref (** a dictionary for the instance *)
}


(* A type for contraints collected during type checking. TNset contains the variables the term ranges over, the second are remaining class constraints, and the third remaining length constraints *)
type typ_constraints = Tconstraints of TNset.t * (Path.t * tnvar) list * range list

val head_norm : type_defs -> t -> t

(** [dest_fn_type d_opt t] tries to destruct a function type
    [t]. Before the destruction, [head_norm d t] is applied, if
    [d_opt] is of the form [Some d]. If the result is a function type,
    [t1 --> t2], the [Some (t1, t2)] is returned. Otherwise the result
    is [None]. *)
val dest_fn_type : type_defs option -> t -> (t * t) option

(** [strip_fn_type d t] tries to destruct a function type [t] by applying [dest_fn] repeatedly. *)
val strip_fn_type : type_defs option -> t -> (t list * t)

(** [check_equal d t1 t2] checks whether [t1] and [t2] are equal in type environment [d]. 
    It expands the type to perform this check. Therefore, it is more reliable than [compare t1 t2 = 0],
    which only performs a structural check, but does not unfold type definitions. *)
val check_equal : type_defs -> t -> t -> bool

(** [assert_equal l m d t1 t2] performs the same check as [check_equal d t1 t2]. However, while 
    check_equal returns wether the types are equal, [assert_equal] raises a type-exception 
    in case they are not. [l] and [m] are used for printing this exception. *)
val assert_equal : Ast.l -> string -> type_defs -> t -> t -> unit

(** [compare_expand d t1 t2] is similar [check_equal d t1 t2]. Instead of just checking for equality,
    it compare the values though. During this comparison, type abbrivations are unfolded. Therefore,
    it is in general preferable to the very similar method [compare], which perform comparisons without
    unfolding. *)
val compare_expand : type_defs -> t -> t -> int


(** A reference to an instance. *)
type instance_ref 

(** [string_of_instance_ref] formats a reference in a human readable form.
    No other guarentees are given. This function should only be used for debugging 
    and reporting internal errors. Its implementation can change at any point to 
    something completely different and should not be relied on. *)
val string_of_instance_ref : instance_ref -> string

(** an instance environment carries information about all defined instances *)
type i_env 

(** an empty instance environment *)
val empty_i_env : i_env 

(** [i_env_add i_env i] adds an additional instance [i] to the instance environment.
    It returns the modified environment as well as the reference of the added instance. *)
val i_env_add : i_env -> instance -> (i_env * instance_ref)

(** [i_env_lookup l i_env ref] looks up the reference in environment [i_env].
    If this reference is not present, an exception is raised. *)
val i_env_lookup : Ast.l -> i_env -> instance_ref -> instance

(** [get_matching_instance type_env (class, ty) i_env] searches for an
    instantiation of type class [class] instantianted with type [ty]
    in the type invironment [i_env]. The type environment [type_env]
    is necessary to match [ty] against other instantiations of
    [class].  An instance can itself have free type variables. If a
    matching instance is found, it is returned to together with the
    substition, which needs to be applied to the free type variables
    of the instance in order to match type [t] excactly.  The
    typevariables of an instances might have attached type
    constraints. It is not (!) checked, that the found substitution
    satisfies these constraints. However, they are taken into account
    to rule out impossible instances, if there are multiple options. 
*)
val get_matching_instance : type_defs -> (Path.t * t) -> i_env -> (instance * t TNfmap.t) option

(* Convert a list of nexp into a binary sumation *)
val nexp_from_list : nexp list -> nexp

module type Global_defs = sig
  val d : type_defs 
  val i : i_env
end 

module Constraint (T : Global_defs) : sig
  val new_type : unit -> t
  val new_nexp : unit -> nexp
  val equate_types : Ast.l -> string -> t -> t -> unit
  val in_range : Ast.l -> nexp -> nexp -> unit
  val add_constraint : Path.t -> t -> unit
  val add_length_constraint : range -> unit
  val add_tyvar : Tyvar.t -> unit 
  val add_nvar : Nvar.t -> unit
  val inst_leftover_uvars : Ast.l -> typ_constraints
  val check_numeric_constraint_implication : Ast.l -> range -> range list -> unit
end

val pp_type : Format.formatter -> t -> unit
val pp_nexp : Format.formatter -> nexp -> unit
val pp_range : Format.formatter -> range -> unit
val pp_class_constraint : Format.formatter -> Path.t * tnvar -> unit
val pp_instance : Format.formatter -> instance -> unit
val pp_typschm : Format.formatter -> tnvar list -> (Path.t * tnvar) list -> t -> unit

(*
val pp_instance_defs: Format.formatter -> i_env -> unit
*)

val t_to_string : t -> string

(** [print_debug_typ_raw s [ty0, ..., tn]] prints a debug message [s t0, ..., tn]
    using [Reporting_basic.print_debug]. *)
val print_debug_typ_raw : string -> t list -> unit

(* converts the type into the default name of auto-generated variables of this type *)
val t_to_var_name : t -> Name.t
