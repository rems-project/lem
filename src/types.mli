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


(* Structural comparison of types, without expanding type abbreviations.
 * Probably better not to use *)
val compare : t -> t -> int

val multi_fun : t list -> t -> t
val type_subst : t TNfmap.t -> t -> t
val nexp_subst : t TNfmap.t -> nexp -> nexp
val free_vars : t -> TNset.t

val tnvar_to_name : tnvar -> Name.t
val tnvar_to_type : tnvar -> t
val tnvar_split : tnvar list -> (tnvar list * tnvar list)

(** A reference to a constant description. These constant description references
    are used by [typed_ast]. This module also contains the appropriate mapping
    functionality to constant descriptions. However, the references need to
    be defined here, because types need information about associated constants.
    Record types need a list of all their field constants. Moreover, every type
    can contain a list of constructor descriptions. *)
type const_descr_ref = int

type constr_family_descr = { 
   constr_list : const_descr_ref list; 
   (** a list of all the constructors *)

   constr_case_fun : const_descr_ref option 
   (** the case split function for this constructor list, [None] means that pattern matching is used. *)
}

(** the target representation of a type *)
type type_target_rep =
  | TR_rename of Name.t (** Rename the type to the given name. This means keeping the module structure unchanged and just modifying the name *)
  | TR_new_ident of Ident.t (** Replace the type identifier with the given one. Module prefixes are thrown away and replaced *)

(** a type description  **)
type type_descr = { 
  type_tparams : tnvar list;
  (** a list of type and length parameters *)

  type_abbrev : t option;
  (** if it is an abbreviation, the type it abbreviates *)

  type_varname_regexp : string option;
  (** an optional regular expression that variable names that have the type must match *)

  type_fields : (const_descr_ref list) option;
  (** if it is a record type, the list of fields *)

  type_constr : constr_family_descr list;
  (** the constructors of this type *)
  
  type_target_rep : type_target_rep Target.Targetmap.t
  (** target representation of the type *)
}

type tc_def = 
  | Tc_type of type_descr
  | Tc_class of tnvar * (Name.t * t) list
    (** The class' type parameter, and the names and types of the methods *)

type type_defs = tc_def Pfmap.t

(** [type_defs_update_fields l d p fl] updates the fields of type [p] in [d]. *)
val type_defs_update_fields : Ast.l -> type_defs -> Path.t -> const_descr_ref list -> type_defs

val type_defs_add_constr_family : Ast.l -> type_defs -> Path.t -> constr_family_descr -> type_defs

(** [type_defs_get_constr_families l d t c] gets all constructor family descriptions for type [t] in
    type environment [d], which contain the constant [c]. *)
val type_defs_get_constr_families : Ast.l -> type_defs -> t -> const_descr_ref -> constr_family_descr list

(** [type_def_rename_type l d p t n] renames the type with path [p] in the defs [d] to the name [n] for
target [t]. Renaming means that the module structure is kept. Only the name is changed. *)
val type_defs_rename_type: Ast.l -> type_defs -> Path.t -> Target.target -> Name.t -> type_defs

(** [type_def_new_ident_type l d p t i] changes the representation of the type with path [p] in the defs [d] to the identifier [i] for
target [t]. This means that the whole module structure is lost and replace by the identifier. *)
val type_defs_new_ident_type: Ast.l -> type_defs -> Path.t -> Target.target -> Ident.t -> type_defs

(** [type_defs_lookup_typ l d t] looks up the description of type [t] in defs [d]. *)
val type_defs_lookup_typ : Ast.l -> type_defs -> t -> type_descr option

(** [type_defs_lookup l d p] looks up the description of type with path [p] in defs [d]. *)
val type_defs_lookup : Ast.l -> type_defs -> Path.t -> type_descr

(** Generates a type abbreviation *)
val mk_tc_type_abbrev : tnvar list -> t -> tc_def

(** Generates a type *)
val mk_tc_type : tnvar list -> string option -> tc_def

(* The last Name.t list is to the module enclosing the instance declaration *)
type instance = tnvar list * (Path.t * tnvar) list * t * Name.t list

(* A type for contraints collected during type checking. TNset contains the variables the term ranges over, the second are remaining class constraints, and the third remaining length constraints *)
type typ_constraints = Tconstraints of TNset.t * (Path.t * tnvar) list * range list

val head_norm : type_defs -> t -> t

(** [dest_fn_type d t] tries to destruct a function type [t]. Before the destruction, [head_norm d t] is applied. If
    the result is a function type, [t1 --> t2], the [Some (t1, t2)] is returned. Otherwise the result is [None]. *)
val dest_fn_type : type_defs -> t -> (t * t) option

(** [strip_fn_type d t] tries to destruct a function type [t] by applying [dest_fn] repeatedly. *)
val strip_fn_type : type_defs -> t -> (t list * t)


val assert_equal : Ast.l -> string -> type_defs -> t -> t -> unit

(* Gets the instance for the given class and type.  Returns None if there is
 * none.  The returned Name list is to the module enclosing the instance
 * declaration.  The returned map is the instantiation of the instances type
 * variables.  The returned list is the set of instances that the found instance
 * relies on. *)
val get_matching_instance : type_defs -> (Path.t * t) -> instance list Pfmap.t -> 
          (Name.t list * t TNfmap.t * (Path.t * t) list) option

(* Convert a list of nexp into a binary sumation *)
val nexp_from_list : nexp list -> nexp

module type Global_defs = sig
  val d : type_defs 
  val i : (instance list) Pfmap.t 
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
val pp_instance_defs: Format.formatter -> (instance list) Pfmap.t -> unit

val t_to_string : t -> string

(* converts the type into the default name of auto-generated variables of this type *)
val t_to_var_name : t -> Name.t
