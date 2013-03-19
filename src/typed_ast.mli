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

(* Sets of Names *)
module NameSet : Set.S with type elt = Name.t and type t = Set.Make(Name).t

(* Name keyed finite maps *)
module Nfmap : Finite_map.Fmap with type k = Name.t

val nfmap_domain : 'a Nfmap.t -> NameSet.t

type name_l = Name.lskips_t * Ast.l

(* Whitespace, comments, and newlines *)
type lskips = Ast.lex_skips

type 'a lskips_seplist = ('a, lskips) Seplist.t

(* The empty lskip *)
val no_lskips : lskips

(* A space lskip *)
val space : lskips

(* Get only the comments (and a trailing space) *)
val lskips_only_comments : lskips list -> lskips

val ast_target_compare : Ast.target -> Ast.target -> int

type target = 
  | Target_hol
  | Target_ocaml
  | Target_isa
  | Target_coq
  | Target_tex
  | Target_html

val ast_target_to_target : Ast.target -> target
val target_to_ast_target : target -> Ast.target
val target_compare : target -> target -> int

(* target keyed finite maps *)
module Targetmap : Finite_map.Fmap with type k = target
module Targetset : Set.S with type elt = target

(* The set of all the possible targets *)
val all_targets : Targetset.t

val target_to_string : target -> string
val target_opt_to_string : target option -> string
val target_to_output : Output.id_annot -> Ast.target -> Output.t
val target_to_mname : target -> Name.t

(* What kind of top-level definition a particular constant is *)
type env_tag = 
  (* A class method *)
  | K_method

  (* A method instance *)
  | K_instance

  (* A val specification that has no definitions *)
  | K_val

  (* A let definition with no target specific definitions or val spec *)
  | K_let

  (* A definition that also has a val specification.  There is a target-specific
   * definition for each target in the set, and the bool is true if there is a
   * target non-specific definition *)
  | K_target of bool * Targetset.t

type ('a,'b) annot = { term : 'a; locn : Ast.l; typ : Types.t; rest : 'b }
val annot_to_typ : ('a,'b) annot -> Types.t

(* Represents a (data) constructor *)
type constr_descr = 
  { 
    (* The path to the constructor's definition *)
    constr_binding : Path.t; 
    
    (* Its type parameters *)
    constr_tparams : Types.tnvar list; 
    
    (* The types of the constructor's arguments (can refer to the above type
     * parameters) *)
    constr_args : Types.t list; 
    
    (* The type constructor that the constructors value has.  Implicitly
    * parameterized by the above type parameters *)
    constr_tconstr : Path.t;
    
    (* The names of the other (data) constructors of the same type *)
    constr_names : NameSet.t; 

    (* The location for the first occurrence of the definition of this constructor *)
    constr_l : Ast.l;
  }

(* Represents a field *)
type field_descr = 
    {
      (* The path to the field's definition *)
      field_binding : Path.t;

      (* Its type parameters *)
      field_tparams : Types.tnvar list;

      (* The type constructor of the record that the field belongs to.
      * Implicitly parameterized by the above type parameters *)
      field_tconstr : Path.t;

      (* The type of the field (can refer to the above type parameters) *)
      field_arg : Types.t;

      (* The names of the other fields of the same record type *)
      field_names : Name.t list;

      (* The location for the first occurrence of the definition of this field *)
      field_l : Ast.l;
    }

(* Maps a type name to the unique path representing that type and 
   the first location this type is defined and any regular expression 
   identifiers of this type should respect
*)
type p_env = (Path.t * Ast.l) Nfmap.t

type ident_option =
  | Id_none of Ast.lex_skips
  | Id_some of Ident.t


(* Represents a usage of an 'a (usually in constr_descr, field_descr,
 * const_descr) *)
type 'a id = 
    { 
      (* The identifier as written at the usage point.  None if it is generated
       * internally, and therefore has no original source *)
      id_path : ident_option; 

      (* The location of the usage point *)
      id_locn : Ast.l;

      (* A description of the binding that the usage refers to *)
      descr : 'a; 

      (* The usage site instantiation of the type parameters of the definition *)
      instantiation : Types.t list;
    }


(* The AST.  lskips appear in the types wherever concrete syntactic elements
 * would appear (e.g., a keyword), and represent the comments and whitespace
 * that preceded that concrete element.  They do not represent the element
 * itself *)

and src_t = (src_t_aux,unit) annot

and src_t_aux = 
 | Typ_wild of lskips
 | Typ_var of lskips * Tyvar.t
 | Typ_len of src_nexp
 | Typ_fn of src_t * lskips * src_t
 | Typ_tup of src_t lskips_seplist
 | Typ_app of Path.t id * src_t list
 | Typ_paren of lskips * src_t * lskips

and src_nexp =  { nterm : src_nexp_aux; nloc : Ast.l; nt : Types.nexp } 

and src_nexp_aux =
 | Nexp_var of lskips * Nvar.t 
 | Nexp_const of lskips * int
 | Nexp_mult of src_nexp * lskips * src_nexp (* One will always be const *)
 | Nexp_add of src_nexp * lskips * src_nexp 
 | Nexp_paren of lskips * src_nexp * lskips

type lit = (lit_aux,unit) annot

and lit_aux =
  | L_true of lskips
  | L_false of lskips
  | L_zero of lskips (* This is a bit, not a num *)
  | L_one of lskips  (* see above *)
  | L_num of lskips * int
  | L_string of lskips * string
  | L_unit of lskips * lskips
  | L_vector of lskips * string * string  (* For vectors of bits, specified with hex or binary, first string is either 0b or 0x, second is the binary or hex number as a string *)
  | L_undefined of lskips * string (** A special undefined value that explicitly states that nothing is known about it. This is useful for expressing underspecified functions. It has been introduced to easier support pattern compilation of non-exhaustive patterns. *)

type pat = (pat_aux,pat_annot) annot
and pat_annot = { pvars : Types.t Nfmap.t }

and pat_aux = 
  | P_wild of lskips
  | P_as of lskips * pat * lskips * name_l * lskips
  | P_typ of lskips * pat * lskips * src_t * lskips
  | P_var of Name.lskips_t
  | P_constr of constr_descr id * pat list
  | P_record of lskips * (field_descr id * lskips * pat) lskips_seplist * lskips
  | P_vector of lskips * pat lskips_seplist * lskips
  | P_vectorC of lskips * pat list * lskips
  | P_tup of lskips * pat lskips_seplist * lskips
  | P_list of lskips * pat lskips_seplist * lskips
  | P_paren of lskips * pat * lskips
  | P_cons of pat * lskips * pat
  | P_num_add of name_l * lskips * lskips * int
  | P_lit of lit
  (* A type-annotated pattern variable.  This is redundant with the combination
  * of the P_typ and P_var cases above, but useful as a macro target. *)
  | P_var_annot of Name.lskips_t * src_t

(* The description of a top-level definition *)
and const_descr = 
  { 
    (* The path to the definition *)
    const_binding : Path.t;

    (* Its type parameters.  Must have length 1 for class methods. *)
    const_tparams : Types.tnvar list;

    (* Its class constraints (must refer to above type parameters).  Must have
     * length 1 for class methods *)
    const_class : (Path.t * Types.tnvar) list;

    (* Its type *)
    const_type : Types.t; 

    (* What kind of definition it is. *)
    env_tag : env_tag;

    (* The location for the first occurrence of a definition/specification of
     * this constant *)
    spec_l : Ast.l;

    (* Target-specific substitutions to use for this constant *)
    substitutions : ((Name.t,unit) annot list * exp) Targetmap.t; 
  }

and val_descr = 
  | Constr of constr_descr
  | Val of const_descr

and v_env = val_descr Nfmap.t

and f_env = field_descr Nfmap.t
and m_env = mod_descr Nfmap.t
and env = { m_env : m_env; p_env : p_env; f_env : f_env; v_env : v_env; }

and mod_descr = { mod_binding : Path.t; mod_env : env; }

and exp
and exp_subst =
  | Sub of exp
  | Sub_rename of Name.t

and exp_aux = private
  | Var of Name.lskips_t
  | Nvar_e of lskips * Nvar.t
  | Constant of const_descr id
  | Constructor of constr_descr id
  | Tup_constructor of constr_descr id * lskips * exp lskips_seplist * lskips
  | Fun of lskips * pat list * lskips * exp
  | Function of lskips * (pat * lskips * exp * Ast.l) lskips_seplist * lskips
  | App of exp * exp
  (* The middle exp must be a Var, Constant, or Constructor *) 
  | Infix of exp * exp * exp
  | Record of lskips * fexp lskips_seplist * lskips
  | Record_coq of name_l * lskips * fexp lskips_seplist * lskips
  | Recup of lskips * exp * lskips * fexp lskips_seplist * lskips
  | Field of exp * lskips * field_descr id
  | Vector of lskips * exp lskips_seplist * lskips
  | VectorSub of exp * lskips * src_nexp * lskips * src_nexp * lskips
  | VectorAcc of exp * lskips * src_nexp * lskips
  | Case of bool * lskips * exp * lskips * (pat * lskips * exp * Ast.l) lskips_seplist * lskips
  | Typed of lskips * exp * lskips * src_t * lskips
  | Let of lskips * letbind * lskips * exp
  | Tup of lskips * exp lskips_seplist * lskips
  | List of lskips * exp lskips_seplist * lskips
  | Paren of lskips * exp * lskips
  | Begin of lskips * exp * lskips
  | If of lskips * exp * lskips * exp * lskips * exp
  | Lit of lit
  | Set of lskips * exp lskips_seplist * lskips
  | Setcomp of lskips * exp * lskips * exp * lskips * NameSet.t
  (* true for list comprehensions, false for set comprehensions *)
  | Comp_binding of bool * lskips * exp * lskips * lskips * quant_binding list * lskips * exp * lskips
  | Quant of Ast.q * quant_binding list * lskips * exp


and fexp = field_descr id * lskips * exp * Ast.l

and name_lskips_annot = (Name.lskips_t,unit) annot

and quant_binding = 
  | Qb_var of name_lskips_annot
  (* true for list quantifiers, false for set quantifiers *)
  | Qb_restr of bool * lskips * pat * lskips * exp * lskips

and funcl_aux = name_lskips_annot * pat list * (lskips * src_t) option * lskips * exp

and letbind = letbind_aux * Ast.l

and letbind_aux =
  | Let_val of pat * (lskips * src_t) option * lskips * exp
  | Let_fun of funcl_aux
  
type tyvar = lskips * Ulib.Text.t * Ast.l
type nvar = lskips * Ulib.Text.t * Ast.l

type tnvar = 
  | Tn_A of tyvar
  | Tn_N of nvar

type texp = 
  | Te_opaque
  | Te_abbrev of lskips * src_t
  | Te_record of lskips * lskips * (name_l * lskips * src_t) lskips_seplist * lskips
  | Te_record_coq of lskips * name_l * lskips * (name_l * lskips * src_t) lskips_seplist * lskips
  | Te_variant of lskips * (name_l * lskips * src_t lskips_seplist) lskips_seplist
  | Te_variant_coq of lskips * (name_l * lskips * src_t lskips_seplist * name_l * tnvar list) lskips_seplist

type constraints = 
  | Cs_list of (Ident.t * tnvar) lskips_seplist * lskips

type constraint_prefix =
  | Cp_forall of lskips * tnvar list * lskips * constraints option

type typschm = constraint_prefix option * src_t

type instschm = constraint_prefix option * lskips * Ident.t * src_t * lskips

type val_spec = lskips * name_l * lskips * typschm

type class_val_spec = lskips * name_l * lskips * src_t

type targets_opt = (lskips * Ast.target lskips_seplist * lskips) option

val in_targets_opt : Ast.target option -> targets_opt -> bool

type val_def = 
  | Let_def of lskips * targets_opt * letbind
  | Rec_def of lskips * lskips * targets_opt * funcl_aux lskips_seplist
  | Let_inline of lskips * lskips * targets_opt * name_lskips_annot * name_lskips_annot list * lskips * exp

(* Semantic information about an instance that is used for the dictionary
 * passing transformations *)
type inst_sem_info =
  { 
    (* An environment that contains const bindings for all of the methods *)
    inst_env : v_env;
    (* A module name for the instance *)
    inst_name : Name.t;
    (* The class instantiated *)
    inst_class : Path.t;
    (* The type variables that the instantiation is parameterised over *)
    inst_tyvars : Types.tnvar list;
    (* The class constraints that the instance depends on *)
    inst_constraints : (Path.t * Types.tnvar) list;
    (* The instantiated class' method names and their types *)
    inst_methods : (Name.t * Types.t) list; }

type name_sect = Name_restrict of (lskips * name_l * lskips * lskips * string * lskips)

type def = (def_aux * lskips option) * Ast.l

and def_aux =
  | Type_def of lskips * (name_l * tnvar list * texp * name_sect option) lskips_seplist
  (* The TNset contains the type length variables that the definition is parameterized
   * over, and the list contains the class constraints on those variables *)
  | Val_def of val_def * Types.TNset.t * (Path.t * Types.tnvar) list 
  | Lemma of lskips * Ast.lemma_typ * targets_opt * (name_l * lskips) option * exp
  | Ident_rename of lskips * targets_opt * Path.t * Ident.t * lskips * name_l
  | Module of lskips * name_l * lskips * lskips * def list * lskips
  | Rename of lskips * name_l * lskips * mod_descr id
  | Open of lskips * mod_descr id
  | Indreln of lskips * targets_opt * 
               (Name.lskips_t option * lskips * name_lskips_annot list * lskips * exp option * lskips * name_lskips_annot * exp list) lskips_seplist
  | Val_spec of val_spec
  | Class of lskips * lskips * name_l * tnvar * lskips * class_val_spec list * lskips
  | Instance of lskips * instschm * val_def list * lskips * inst_sem_info

  (* Does not appear in the source, used to comment out definitions for certain
  * backends *)
  | Comment of def

val tnvar_to_types_tnvar : tnvar -> Types.tnvar * Ast.l

val empty_env : env

val exp_to_locn : exp -> Ast.l
val exp_to_typ : exp -> Types.t

(* append_lskips adds new whitespace/newline/comments to the front of an
 * expression (before any existing whitespace/newline/comments in front of the
 * expression) *)
val append_lskips : lskips -> exp -> exp 
val pat_append_lskips : lskips -> pat -> pat

(* alter_init_lskips finds all of the whitespace/newline/comments preceding an
 * expression and passes it to the supplied function in a single invocation.
 * The preceding whitespace/newline/comments are replaced with the fst of the
 * function's result, and the snd of the function's result is returned from
 * alter_init_lskips *)
val typ_alter_init_lskips : (lskips -> lskips * lskips) -> src_t -> src_t * lskips 
val nexp_alter_init_lskips : (lskips -> lskips * lskips) -> src_nexp -> src_nexp * lskips
val pat_alter_init_lskips : (lskips -> lskips * lskips) -> pat -> pat * lskips
val alter_init_lskips : (lskips -> lskips * lskips) -> exp -> exp * lskips
val def_alter_init_lskips : (lskips -> lskips * lskips) -> def -> def * lskips

val unsat_constraint_err : Ast.l -> (Path.t * Types.tnvar) list -> unit
val pp_const_descr : Format.formatter -> const_descr -> unit
val pp_field_descr : Format.formatter -> field_descr -> unit
val pp_env : Format.formatter -> env -> unit
val pp_instances : Format.formatter -> Types.instance list Types.Pfmap.t -> unit

type checked_module =
    { filename : string;
      module_name : string;
      predecessor_modules : string list;
      untyped_ast : Ast.defs * Ast.lex_skips;
      typed_ast : def list * Ast.lex_skips; }

(** [var_avoid_f] is a type of a tuple [(avoid_ty_vars, name_ok, do_rename)]. 
    The flag [avoid_ty_vars] states, whether clashes with type variables should be avoided.
    The [name_ok n] checks whether the name [n] is OK. 
    If it is not OK, the function [do_rename n_text check] renames [n].
    As input it takes the text of [n], a function [check] that checks whether the new
    name clashes with any names to be avoided or existing variable names in the context. *)
type var_avoid_f = bool * (Name.t -> bool) * (Ulib.Text.t -> (Name.t -> bool) -> Name.t)

module type Exp_context = sig
  (* Whether the constructor functions should do type checking too *)
  val check : Types.type_defs option
    (* Avoiding certain names for local variables.  Given a name and a set of
     * names that must be avoided, choose a new name if necessary *)
  val avoid : var_avoid_f option

end

module Exps_in_context(C : Exp_context) : sig
  val exp_subst : (Types.t Types.TNfmap.t * exp_subst Nfmap.t) -> exp -> exp
  val push_subst : (Types.t Types.TNfmap.t * exp_subst Nfmap.t) -> pat list -> exp -> pat list * exp
  val exp_to_term : exp -> exp_aux
  val exp_to_free : exp -> Types.t Nfmap.t
  val type_eq : Ast.l -> string -> Types.t -> Types.t -> unit
  val mk_lnum : Ast.l -> lskips -> int -> Types.t option -> lit
  val mk_lbool : Ast.l -> lskips -> bool -> Types.t option -> lit
  val mk_lbit : Ast.l -> lskips -> int -> Types.t option -> lit
  val mk_lundef : Ast.l -> lskips -> string -> Types.t -> lit
  val mk_lstring : Ast.l -> lskips -> string -> Types.t option -> lit
  val mk_twild : Ast.l -> lskips -> Types.t -> src_t
  val mk_tvar : Ast.l -> lskips -> Tyvar.t -> Types.t -> src_t
  val mk_tfn : Ast.l -> src_t -> lskips -> src_t -> Types.t option -> src_t
  val mk_ttup : Ast.l -> src_t lskips_seplist -> Types.t option -> src_t
  val mk_tapp : Ast.l -> Path.t id -> src_t list -> Types.t option -> src_t
  val mk_tparen : Ast.l -> lskips -> src_t -> lskips -> Types.t option -> src_t

  val mk_pwild : Ast.l -> lskips -> Types.t -> pat
  val mk_pas : Ast.l -> lskips -> pat -> lskips -> name_l -> lskips -> Types.t option -> pat
  val mk_ptyp : Ast.l -> lskips -> pat -> lskips -> src_t -> lskips -> Types.t option -> pat
  val mk_pvar : Ast.l -> Name.lskips_t -> Types.t -> pat
  val mk_pconstr : Ast.l -> constr_descr id -> pat list -> Types.t option -> pat
  val mk_precord : Ast.l -> lskips -> (field_descr id * lskips * pat) lskips_seplist -> lskips -> Types.t option -> pat
  val mk_ptup : Ast.l -> lskips -> pat lskips_seplist -> lskips -> Types.t option -> pat
  val mk_plist : Ast.l -> lskips -> pat lskips_seplist -> lskips -> Types.t -> pat
  val mk_pvector : Ast.l -> lskips -> pat lskips_seplist -> lskips -> Types.t -> pat
  val mk_pvectorc : Ast.l -> lskips -> pat list -> lskips -> Types.t -> pat
  val mk_pparen : Ast.l -> lskips -> pat -> lskips -> Types.t option -> pat
  val mk_pcons : Ast.l -> pat -> lskips -> pat -> Types.t option -> pat
  val mk_pnum_add : Ast.l -> name_l -> lskips -> lskips -> int -> Types.t option -> pat
  val mk_plit : Ast.l -> lit -> Types.t option -> pat 
  val mk_pvar_annot : Ast.l -> Name.lskips_t -> src_t -> Types.t option -> pat 

  val mk_var : Ast.l -> Name.lskips_t -> Types.t -> exp
  val mk_nvar_e : Ast.l -> lskips -> Nvar.t -> Types.t -> exp
  val mk_const : Ast.l -> const_descr id -> Types.t option -> exp
  val mk_constr : Ast.l -> constr_descr id -> Types.t option -> exp
  val mk_tup_ctor : Ast.l -> constr_descr id -> lskips -> exp lskips_seplist -> lskips -> Types.t option -> exp
  val mk_fun : Ast.l -> lskips -> pat list -> lskips -> exp -> Types.t option -> exp
  val mk_function : Ast.l -> lskips -> (pat * lskips * exp * Ast.l) lskips_seplist -> lskips -> Types.t option -> exp
  val mk_app : Ast.l -> exp -> exp -> Types.t option -> exp
  val mk_infix : Ast.l -> exp -> exp -> exp -> Types.t option -> exp
  val mk_record : Ast.l -> lskips -> (field_descr id * lskips * exp * Ast.l) lskips_seplist-> lskips -> Types.t option -> exp
  val mk_record_coq : Ast.l -> lskips -> (field_descr id * lskips * exp * Ast.l) lskips_seplist-> lskips -> Types.t option -> exp
  val mk_recup : Ast.l -> lskips -> exp -> lskips -> (field_descr id * lskips * exp * Ast.l) lskips_seplist -> lskips -> Types.t option -> exp
  val mk_field : Ast.l -> exp -> lskips -> field_descr id -> Types.t option -> exp
  val mk_case : bool -> Ast.l -> lskips -> exp -> lskips -> (pat * lskips * exp * Ast.l) lskips_seplist -> lskips -> Types.t option -> exp
  val mk_typed : Ast.l -> lskips -> exp -> lskips -> src_t -> lskips -> Types.t option -> exp
  val mk_let_val : Ast.l -> pat -> (lskips * src_t) option -> lskips -> exp -> letbind
  val mk_let_fun : Ast.l -> name_lskips_annot -> pat list -> (lskips * src_t) option -> lskips -> exp -> letbind
  val mk_let : Ast.l -> lskips -> letbind -> lskips -> exp -> Types.t option -> exp
  val mk_tup : Ast.l -> lskips -> exp lskips_seplist -> lskips -> Types.t option -> exp
  val mk_list : Ast.l -> lskips -> exp lskips_seplist -> lskips -> Types.t -> exp
  val mk_vector : Ast.l -> lskips -> exp lskips_seplist -> lskips -> Types.t -> exp
  val mk_vaccess : Ast.l -> exp -> lskips -> src_nexp -> lskips -> Types.t -> exp
  val mk_vaccessr : Ast.l -> exp -> lskips -> src_nexp -> lskips ->src_nexp -> lskips -> Types.t -> exp
  val mk_paren : Ast.l -> lskips -> exp -> lskips -> Types.t option -> exp
  val mk_begin : Ast.l -> lskips -> exp -> lskips -> Types.t option -> exp
  val mk_if : Ast.l -> lskips -> exp -> lskips -> exp -> lskips -> exp -> Types.t option -> exp
  val mk_lit : Ast.l -> lit -> Types.t option -> exp
  val mk_set : Ast.l -> lskips -> exp lskips_seplist -> lskips -> Types.t -> exp
  val mk_setcomp : Ast.l -> lskips -> exp -> lskips -> exp -> lskips -> NameSet.t -> Types.t option -> exp
  val mk_comp_binding : Ast.l -> bool -> lskips -> exp -> lskips -> lskips -> quant_binding list -> lskips -> exp -> lskips -> Types.t option -> exp
  val mk_quant : Ast.l -> Ast.q -> quant_binding list -> lskips -> exp -> Types.t option -> exp
  val t_to_src_t : Types.t -> src_t
  val pat_subst : Types.t Types.TNfmap.t * Name.t Nfmap.t -> pat -> pat
  val delimit_exp : (Precedence.op -> Precedence.t) -> Precedence.context -> exp -> exp
  val exp_to_prec : (Precedence.op -> Precedence.t) -> exp -> Precedence.t
end

val env_union : env -> env -> env
val delimit_pat : Precedence.pat_context -> pat -> pat
val get_new_constants_types : target option -> checked_module list -> Ast.l Nfmap.t * Ast.l Nfmap.t

exception Renaming_error of Ast.l * string
val get_renames_of_defs : target option -> (Path.t * ( Ast.l * Path.t)) list -> def list -> (Path.t * ( Ast.l * Path.t)) list

type name_kind =
  | Nk_typeconstr
  | Nk_const
  | Nk_constr
  | Nk_field
  | Nk_module
  | Nk_class

(** [env_apply env n] looks up the name [n] in the environment [env], regardless of whether [n] is a
   name of a type, field, constructor or constant and returns the
   type of this name, it's full path and the location of the original definition *)
val env_apply : env -> Name.t -> (name_kind * Path.t * Ast.l) option


(** Mutually recursive function definitions may contain multiple clauses for the
    same function. These can however appear interleaved with clauses for other functions. 
    [funcl_aux_seplist_group seplist] sorts the clauses according to the function names and
    states, whether any resorting was necessary. Moreover, the initial lskip is returned, if present. *)
val funcl_aux_seplist_group : funcl_aux lskips_seplist -> (bool * lskips option * (Name.t * funcl_aux lskips_seplist) list)

val class_path_to_dict_name : Path.t -> Types.tnvar -> Name.t
val class_path_to_dict_type : Path.t -> Types.t -> Types.t

val names_get_field : env -> Name.t list -> field_descr
val resolve_ident_path : 'a id -> Path.t -> Ident.t
val ident_get_first_lskip : 'a id -> Ast.lex_skips
val ident_replace_first_lskip : ident_option -> Ast.lex_skips -> ident_option
