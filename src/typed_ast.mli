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

open Types

(** Sets of Names *)
module NameSet : Set.S with type elt = Name.t and type t = Set.Make(Name).t

(** Name keyed finite maps *)
module Nfmap : Finite_map.Fmap with type k = Name.t

val nfmap_domain : 'a Nfmap.t -> NameSet.t

type name_l = Name.lskips_t * Ast.l

(** Whitespace, comments, and newlines *)
type lskips = Ast.lex_skips

type 'a lskips_seplist = ('a, lskips) Seplist.t

(** The empty lskip *)
val no_lskips : lskips

(** A space lskip *)
val space : lskips

(** Get only the comments (and a trailing space) *)
val lskips_only_comments : lskips list -> lskips

(** Get the first lskip of the list and only comments from the rest *)
val lskips_only_comments_first : lskips list -> lskips


(** [env_tag] is used by [const_descr] to describe the type of constant. Constants can be defined in multiple ways:
    the most common way is via a [let]-statement. Record-type definitions introduce fields-accessor 
    functions and variant types introduce constructors. There are methods, instances and relations as well.
    A [let] definition can be made via a [val] definition and multiple, target specific lets. *)
type env_tag = 
  | K_let      (** A let definition, the most common case. Convers val as well, details see above. *)
  | K_field    (** A field *)
  | K_constr   (** A type constructor *)
  | K_relation (** A relation *)
  | K_method   (** A class method *)
  | K_instance (** A method instance *)

(** Maps a type name to the unique path representing that type and 
    the first location this type is defined
*)
type p_env = (Path.t * Ast.l) Nfmap.t

type lit = (lit_aux,unit) Types.annot

and lit_aux =
  | L_true of lskips
  | L_false of lskips
  | L_zero of lskips (** This is a bit, not a num *)
  | L_one of lskips  (** see above *)
  | L_numeral of lskips * int * string option (** A numeral literal, it has fixed type "numeral" and is used in patterns and after translating L_num to it. *)
  | L_num of lskips * int * string option (** A number literal. This is like a numeral one wrapped with the "from_numeral" function *)
  | L_char of lskips * char * string option (** A char literal. It contains the parsed char as well as the original input string (if available). *)
  | L_string of lskips * string * string option (** A string literal. It contains the parsed string as well as the original input string (if available). *)
  | L_unit of lskips * lskips
  | L_vector of lskips * string * string  (** For vectors of bits, specified with hex or binary, first string is either 0b or 0x, second is the binary or hex number as a string *)
  | L_undefined of lskips * string (** A special undefined value that explicitly states that nothing is known about it. This is useful for expressing underspecified functions. It has been introduced to easier support pattern compilation of non-exhaustive patterns. *)

type const_descr_ref = Types.const_descr_ref

type name_kind =
  | Nk_typeconstr of Path.t
  | Nk_const of const_descr_ref
  | Nk_constr of const_descr_ref
  | Nk_field of const_descr_ref
  | Nk_module of Path.t
  | Nk_class of Path.t

type pat = (pat_aux,pat_annot) Types.annot
and pat_annot = { pvars : Types.t Nfmap.t }

and pat_aux = 
  | P_wild of lskips
  | P_as of lskips * pat * lskips * name_l * lskips
  | P_typ of lskips * pat * lskips * src_t * lskips
  | P_var of Name.lskips_t
  | P_const of const_descr_ref id * pat list
  | P_backend of lskips * Ident.t * Types.t * pat list
  | P_record of lskips * (const_descr_ref id * lskips * pat) lskips_seplist * lskips
  | P_vector of lskips * pat lskips_seplist * lskips
  | P_vectorC of lskips * pat list * lskips
  | P_tup of lskips * pat lskips_seplist * lskips
  | P_list of lskips * pat lskips_seplist * lskips
  | P_paren of lskips * pat * lskips
  | P_cons of pat * lskips * pat
  | P_num_add of name_l * lskips * lskips * int
  | P_lit of lit
  | P_var_annot of Name.lskips_t * src_t
    (** A type-annotated pattern variable.  This is redundant with the combination
        of the P_typ and P_var cases above, but useful as a macro target. *)

and cr_special_fun (** an indirection for target-representation output functions, the mapping is done in [Backend_common.cr_special_fun_to_fun] *) =
  | CR_special_uncurry of int (** [CR_special_uncurry n] formats a function with [n] arguments curried, i.e. turn the arguments into a tupled argument, surrounded by parenthesis and separated by "," *)
  | CR_special_rep of string list * exp list (** [CR_special_rep sr args] encodes a user given special representation. replace the arguments in the expression list and then interleave the results with sr *)

and const_target_rep =
  | CR_inline of Ast.l * bool * name_lskips_annot list * exp
    (** [CR_inline (loc, allow_override, vars, e)] means inlining the constant with the expression [e] and
        replacing the variable [vars] inside [e] with the arguments of the constant. The flag [allow_override] signals whether
        the declaration might be safely overriden. Automatically generated target-representations (e.g. for ocaml constructors) should
        be changeable by the user, whereas multiple user-defined ones should cause a type error. *)
  | CR_infix of Ast.l * bool * Ast.fixity_decl * Ident.t
    (** [CR_infix (loc, allow_override, fixity, i)] declares infix notation for the constant with the giving identifier. *)
  | CR_undefined of Ast.l * bool 
    (** [CR_undefined (loc, allow_override)] declares undefined constant. *)
  | CR_simple of Ast.l * bool * name_lskips_annot list * exp
    (** [CR_simple (loc, allow_override, vars, e)] is similar to [CR_inline]. Instead of inlining during macro expansion and therefore allowing
        further processing afterwards, [CR_simple] performs the inlining only during printing in the backend. *)
  | CR_special of Ast.l * bool * cr_special_fun * name_lskips_annot list
    (** [CR_special (loc, allow_override, to_out, vars)] describes special formating of this 
        constant. The (renamed) constant (including path prefix) and all arguments are transformed to
        output. [to_out] represents a function that is then given the formatted name and the appropriate number of these
        outputs. The expected arguments are described by [vars]. If there are more arguments than variables,
        they are appended. If there are less, for expressions local functions are introduced. For patterns,
        an exception is thrown. Since values of [const_target_rep] need to be written out to file via [output_value] in order to cache libraries,
        it cannot be a function of type [Output.t list -> Output.t list] directly. Instead, the type [cr_special_fun] is used
        as an indirection.*)

and (** rel_io represents whether an argument of an inductive relation is considerred as an input or an output *)
  rel_io = Rel_mode_in | Rel_mode_out 
and rel_mode = rel_io list
and (** rel_output_type specifies the type of the result *)
  rel_output_type = 
  | Out_list 
  (** Return a list of possible outputs *)
  | Out_pure 
  (** Return one possible output or fail if no such output exists *)
  | Out_option
  (** Return one possible output or None if no such output exists *)
  | Out_unique
  (** Return the output if it is unique or None otherwise *)

and (** rel_info represents information about functions and types genereated from this relation 0*)
  rel_info = {
  ri_witness : (Path.t * const_descr_ref Nfmap.t) option;
  (** Contains the path of the witness type and a mapping from rules to constructors.
      [None] if no witness type has been generated *)

  ri_check : const_descr_ref option;
  (** A reference to the witness checking function or [None] if it is not generated *)

  ri_fns : ((rel_mode * bool * rel_output_type) * const_descr_ref) list;
  (** A list of functions generated from the relation together with their modes *)
}

(** The description of a top-level definition *)
and const_descr = 
  { const_binding : Path.t;
    (** The path to the definition *)

    const_tparams : Types.tnvar list;
    (** Its type parameters.  Must have length 1 for class methods. *)

    const_class : (Path.t * Types.tnvar) list;
    (** Its class constraints (must refer to above type parameters).  Must have
        length 1 for class methods *)

    const_no_class : const_descr_ref Target.Targetmap.t;
    (** If the constant has constraints, i.e. const_class is not empty, we need another constant without
        constraints for dictionary passing. This field stores the reference to this constant, if one such constant
        has aready been generated. *)

    const_ranges : Types.range list;
    (** Its length constraints (must refer to above type parameters). Can be equality or GtEq inequalities *)

    const_type : Types.t; 
    (** Its type *)

    relation_info: rel_info option;
    (** If the constant is a relation, it might contain additional information about this relation.
        However, it might be [None] for some relations as well. *)

    env_tag : env_tag;
    (** What kind of definition it is. *)

    const_targets : Target.Targetset.t;
    (** The set of targets the constant is defined for. *)

    spec_l : Ast.l;
    (** The location for the first occurrence of a definition/specification of
        this constant. *)
    
    target_rename : (Ast.l * Name.t) Target.Targetmap.t;
    (** Target-specific renames of for this constant. *)

    target_ascii_rep : (Ast.l * Name.t) Target.Targetmap.t;
    (** Optional ASCII representation for this constant. *)

    target_rep : const_target_rep Target.Targetmap.t; 
    (** Target-specific representation of for this constant *)

    compile_message : string Target.Targetmap.t;
    (** An optional warning message that should be printed, if the constant is used *)

    termination_setting: Ast.termination_setting Target.Targetmap.t;
    (** Can termination be proved automatically by various backends? *)
  }

and v_env = const_descr_ref Nfmap.t
and f_env = const_descr_ref Nfmap.t
and m_env = Path.t Nfmap.t
and e_env = mod_descr Types.Pfmap.t
and c_env 
and 
  (** [local_env] represents local_environments, i.e. essentially maps from names to the entities they represent *)
  local_env = { 
    m_env : m_env; (** module map *)
    p_env : p_env; (** type map *)
    f_env : f_env; (** field map *)
    v_env : v_env  (** constructor and constant map *)
}
and env = { 
    local_env : local_env;   (** the current local environment *)
    c_env : c_env;           (** global map from constant references to the constant descriptions *)
    t_env : Types.type_defs; (** global type-information *)
    i_env : Types.i_env;     (** global instances information *)
    e_env : e_env;           (** global map from module paths to the module descriptions *)
 }

and mod_target_rep =
  | MR_rename of Ast.l * Name.t (** Rename the module *)

and mod_descr = { mod_binding     : Path.t; (** The full path of this module *)
                  mod_env         : local_env;  (** The local environment of the module *)
                  mod_target_rep  : mod_target_rep Target.Targetmap.t; (** how to represent the module for different backends *)
		  mod_filename   : string option; (** the filename the module is defined in (if it is a top-level module) *)
                  mod_in_output   : bool; (** is this module written to a file (true) or an existing file used (false) ? *) 
}

and exp
and exp_subst =
  | Sub of exp
  | Sub_rename of Name.t

and exp_aux = private
  | Var of Name.lskips_t
  | Backend of lskips * Ident.t (** An identifier that should be used literally by a backend. The identifier does not contain whitespace. Initial whitespace is represented explicitly. *)
  | Nvar_e of lskips * Nvar.t
  | Constant of const_descr_ref id
  | Fun of lskips * pat list * lskips * exp
  | Function of lskips * (pat * lskips * exp * Ast.l) lskips_seplist * lskips
  | App of exp * exp
  | Infix of exp * exp * exp (** The middle exp must be a Var, Constant, or Constructor *) 
  | Record of lskips * fexp lskips_seplist * lskips
  | Recup of lskips * exp * lskips * fexp lskips_seplist * lskips
  | Field of exp * lskips * const_descr_ref id
  | Vector of lskips * exp lskips_seplist * lskips
  | VectorSub of exp * lskips * src_nexp * lskips * src_nexp * lskips
  | VectorAcc of exp * lskips * src_nexp * lskips
  | Case of bool * lskips * exp * lskips * (pat * lskips * exp * Ast.l) lskips_seplist * lskips
    (** The boolean flag as first argument is used to prevent pattern compilation from looping in
        rare cases. If set to [true], no pattern compilation is tried. The default value is [false]. *)
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
  | Comp_binding of bool * lskips * exp * lskips * lskips * quant_binding list * lskips * exp * lskips
    (** [true] for list comprehensions, [false] for set comprehensions *)
  | Quant of Ast.q * quant_binding list * lskips * exp
  | Do of lskips * Path.t id * do_line list * lskips * exp * lskips * (Types.t * bind_tyargs_order)
    (** The last argument is the type of the value in the monad *)

and do_line = Do_line of (pat * lskips * exp * lskips)

and (** A bind constant of a monad M has type [M 'a -> ('a -> M 'b) -> M 'b].
        Here, I call ['a] the input type and ['b] the output type. Depending on
        how the bind constant is defined in detail its free type variable list
        (stored in constant-description record, field const_tparams) might be either
        of the form [['a, 'b]] or [['b, 'a]]. This type is used to distinguish the
        two possibilities. *)
     bind_tyargs_order = 
   | BTO_input_output (** [['a, 'b]] *)
   | BTO_output_input (** [['b, 'a]] *)

and fexp = const_descr_ref id * lskips * exp * Ast.l

and name_lskips_annot = (Name.lskips_t,unit) annot

and quant_binding = 
  | Qb_var of name_lskips_annot
  | Qb_restr of bool * lskips * pat * lskips * exp * lskips
    (** true for list quantifiers, false for set quantifiers *)

and funcl_aux = name_lskips_annot * const_descr_ref * pat list * (lskips * src_t) option * lskips * exp

and letbind = letbind_aux * Ast.l

and letbind_aux =
  | Let_val of pat * (lskips * src_t) option * lskips * exp
    (** [Let_val (p, ty_opt, sk, e)] describes binding the pattern [p] to exp [e] in a local
        let statement, i.e. a statement like [let p = e in ...] *)
  | Let_fun of name_lskips_annot * pat list * (lskips * src_t) option * lskips * exp
    (** [Let_fun (n, ps, ty_opt, sk, e)] describes defining a local function [f] with arguments [ps] locally.
        It repre0sents a statement like [let n ps = e in ...]. Notice that the arguments of [Let_fun] are
        similar to [funcl_aux]. However, funcl_aux has a constant-references, as it is used in top-level definitions,
        whereas [Let_fun] is used only for local functions. *)

val pat_to_bound_names : pat -> NameSet.t

type tyvar = lskips * Ulib.Text.t * Ast.l
type nvar = lskips * Ulib.Text.t * Ast.l

type tnvar = 
  | Tn_A of tyvar
  | Tn_N of nvar

(** Type exepressions for defining types *)
type texp = 
  | Te_opaque (** introduce just a new type name without definition *)
  | Te_abbrev of lskips * src_t (** a type abbreviation with the type Te_abbrev *)
  | Te_record of lskips * lskips * (name_l * const_descr_ref * lskips * src_t) lskips_seplist * lskips
    (** [Te_record (_, _, field_list, _)] defines a record type. The fields and their types
         are stored in [field_list]. The entries of [field_list] consist of the name of the field,
         the reference to it's constant description and the type of the field as well as white-spaces.*)
  | Te_variant of lskips * (name_l * const_descr_ref * lskips * src_t lskips_seplist) lskips_seplist
    (** [Te_variant (_, _, constr_list, _)] defines a variant type. The constructors and their types
         are stored in [constr_list]. The entries of [constr_list] consist of the name of the constructor,
         the reference to it's constant description and the type of it's arguments as well as white-spaces.*)

type range = 
  | GtEq of Ast.l * src_nexp * lskips * src_nexp
  | Eq of Ast.l * src_nexp * lskips * src_nexp

type constraints = 
  | Cs_list of (Ident.t * tnvar) lskips_seplist * lskips option * range lskips_seplist * lskips

type constraint_prefix =
  | Cp_forall of lskips * tnvar list * lskips * constraints option

type typschm = constraint_prefix option * src_t

(** Instance Scheme, constraint prefix, sk, class-ident as printed, resolved class-path the id points to, instantiation type, sk *) 
type instschm = constraint_prefix option * lskips * Ident.t * Path.t * src_t * lskips

(** [cr_special_fun_uses_name f] checks, whether [f] uses it's first argument,
    i.e. whether it uses the formatted name of the constant. This information
    is important to determine, whether the constant needs to be renamed. *)
val cr_special_fun_uses_name : cr_special_fun -> bool


(** targets_opt is represents a set of targets *)
type targets_opt = 
   Targets_opt_none (** represents the universal set, i.e. all targets *)
 | Targets_opt_concrete of lskips * Ast.target lskips_seplist * lskips
     (** (in source `\{ t1; ...; tn \}`) is the set of all targets in the list `tl` *)
 | Targets_opt_neg_concrete of lskips * Ast.target lskips_seplist * lskips
     (** (in source ~`\{ t1; ...; tn \}`) is the set of all targets {b not} in the list `tl` *)
 | Targets_opt_non_exec of lskips
     (** (in source `non_exec`) is the set of all targets that can handle non-executable definitions *)


(** [in_targets_opt targ targets_opt] checks whether the target `targ` is in the set of targets represented by
    `targets_opt`. If [targ] is the a human readable target, [true] is returned. *)
val in_targets_opt : Target.target -> targets_opt -> bool

(** [in_target_set targ targetset] checks whether the target `targ` is in the set of targets 
    [targetset]. It is intended for checking whether to output certain parts of the TAST. 
    Therefore, [in_target_set] returns true for all human readable targets and only checks for others. *)
val in_target_set : Target.target -> Target.Targetset.t -> bool 

(** [target_opt_to_list targets_opt] returns a distinct list of all the targets in the option. *)
val targets_opt_to_list : targets_opt -> Target.non_ident_target list

type val_spec = lskips * name_l * const_descr_ref * Ast.ascii_opt * lskips * typschm

type class_val_spec = lskips * targets_opt * name_l * const_descr_ref * Ast.ascii_opt * lskips * src_t

(** [fun_def_rec_flag] is used to encode, whether a [Fun_def] is recursive. The recursive one carries some whitespace for
    printing after the rec-keyword. *)
type fun_def_rec_flag =
  | FR_non_rec
  | FR_rec of lskips

type val_def = 
  | Let_def of lskips * targets_opt * (pat * (Name.t * const_descr_ref) list * (lskips * src_t) option * lskips * exp)
  | Fun_def of lskips * fun_def_rec_flag * targets_opt * funcl_aux lskips_seplist
    (** [Fun_def (sk1, rec_flag, topt, clauses)] encodes a function definition, which might consist of multiple clauses. *)
  | Let_inline of lskips * lskips * targets_opt * name_lskips_annot * const_descr_ref * name_lskips_annot list * lskips * exp

type name_sect = Name_restrict of (lskips * name_l * lskips * lskips * string * lskips)

type indreln_rule_quant_name = 
  | QName of name_lskips_annot
  | Name_typ of lskips * name_lskips_annot * lskips * src_t * lskips

(**
   A rule of the form [Rule(clause_name_opt, sk1, sk2, bound_vars, sk3, left_hand_side_opt, sk4, rel_name, c, args)] encodes
   a clause [clause_name: forall bound_vars. (left_hand_side ==> rel_name args)]. [c] is the reference of the relation [rel_name]. *)
type indreln_rule_aux = Rule of Name.lskips_t * lskips * lskips * indreln_rule_quant_name list * lskips * exp option * lskips * name_lskips_annot * const_descr_ref * exp list

type indreln_rule = indreln_rule_aux * Ast.l


(** Name of the witness type to be generated *)
type indreln_witness = Indreln_witness of lskips * lskips * Name.lskips_t * lskips

(** Name and mode of a function to be generated from an inductive relation *)
type indreln_indfn = Indreln_fn of Name.lskips_t * lskips * src_t * lskips option

(** Type annotation for the relation and information on what to generate from it.
    [RName(sk1, rel_name, rel_name_ref, sk2, rel_type, witness_opt, check_opt, indfns opt, sk3)] *)
type indreln_name = RName of lskips* Name.lskips_t * const_descr_ref * lskips * typschm * 
                             (indreln_witness option) * ((lskips*Name.lskips_t*lskips) option) * 
                             (indreln_indfn list) option * lskips

type target_rep_rhs =  (** right hand side of a target representation declaration *)
   Target_rep_rhs_infix of lskips * Ast.fixity_decl * lskips * Ident.t (** Declaration of an infix constant *)
 | Target_rep_rhs_term_replacement of exp (** the standard term replacement, replace with the exp for the given backend *)
 | Target_rep_rhs_type_replacement of src_t (** the standard term replacement, replace with the type for the given backend *)
 | Target_rep_rhs_special of lskips * lskips * string * exp list (** fancy represenation of terms *)
 | Target_rep_rhs_undefined (** undefined, don't throw a problem during typeching, but during output *)

type declare_def =  (** Declarations *)
 | Decl_compile_message of lskips * targets_opt * lskips * const_descr_ref id * lskips * lskips * string 
   (** [Decl_compile_message_decl (sk1, targs, sk2, c, sk3, sk4, message)], declares printing waring message
       [message], if constant [c] is used for one of the targets in [targs] *)
 | Decl_target_rep_term of lskips * Ast.target * lskips * Ast.component * const_descr_ref id * name_lskips_annot list * lskips * target_rep_rhs
   (** [Decl_target_rep_term (sk1, targ, sk2, comp, c, args, sk3, rhs)] declares a target-representation for target [targ] and
       constant [c] with arguments [args]. Since fields and constant live in different namespaces, [comp] is used to declare
       whether a field or a constant is meant. The [rhs] constains details about the representation. *)
 | Decl_target_rep_type of lskips * Ast.target * lskips * lskips * Path.t id * tnvar list * lskips * src_t
   (** [Decl_target_rep_type (sk1, targ, sk2, sk3, id, args, sk4, rhs)] declares a target-representation. for target [targ] and
       type [id] with arguments [args]. *)

 | Decl_ascii_rep             of lskips * targets_opt * lskips * Ast.component * name_kind id * lskips * lskips * Name.t
 | Decl_rename                of lskips * targets_opt * lskips * Ast.component * name_kind id * lskips * Name.lskips_t
 | Decl_rename_current_module of lskips * targets_opt * lskips * lskips * lskips * Name.lskips_t 
 | Decl_termination_argument  of lskips * targets_opt * lskips * const_descr_ref id * lskips * Ast.termination_setting
 | Decl_pattern_match_decl    of lskips * targets_opt * lskips * Ast.exhaustivity_setting * Path.t id * tnvar list * lskips * lskips * (const_descr_ref id)  lskips_seplist * lskips * (const_descr_ref id) option

type def_aux =
  | Type_def of lskips * (name_l * tnvar list * Path.t * texp * name_sect option) lskips_seplist
    (** [Type_def (sk, sl)] defines one or more types. The entries of [sl] are the type definitions.
        They contain a name of the type, the full path of the defined type, the free type variables, the main type definiton and 
        restrictions on variable names of this type *)
  | Val_def of val_def 
    (** The list contains the class constraints on those variables *)
  | Lemma of lskips * Ast.lemma_typ * targets_opt * name_l * lskips * exp 
  | Module of lskips * name_l * Path.t * lskips * lskips * def list * lskips
  | Rename of lskips * name_l * Path.t * lskips * Path.t id
    (** Renaming an already defined module *)
  | OpenImport of Ast.open_import * (Path.t id) list
    (** open and/or import modules *)
  | OpenImportTarget of Ast.open_import * targets_opt * (lskips * string) list
    (** open and/or import modules only for specific targets *)
  | Indreln of lskips * targets_opt * indreln_name lskips_seplist * indreln_rule lskips_seplist
    (** Inductive relations *)
  | Val_spec of val_spec
  | Class of Ast.class_decl * lskips * name_l * tnvar * Path.t * lskips * class_val_spec list * lskips
  | Instance of Ast.instance_decl * Types.instance_ref * instschm * val_def list * lskips
    (** [Instance (default?, instance_scheme, methods, sk2)] *)
  | Comment of def
    (** Does not appear in the source, used to comment out definitions for certain backends *)
  | Declaration of declare_def 
    (** Declarations that change the behaviour of lem, but have no semantic meaning *)

(** A definition consists of a the real definition represented as a [def_aux], followed by some white-space.
    There is also the location of the definition and the local-environment present after the definition has been processed. *)
and def = (def_aux * lskips option) * Ast.l * local_env

val tnvar_to_types_tnvar : tnvar -> Types.tnvar * Ast.l

val empty_local_env : local_env
val empty_env : env

(** [e_env_lookup l e_env p] looks up the module with path [p] in
    environment [e_env] and returns the corresponding description. If this
    lookup fails, a fatal error is thrown using location [l] for the error message. *)
val e_env_lookup : Ast.l -> e_env -> Path.t -> mod_descr

(** [c_env_lookup l c_env c_ref] looks up the constant reference [c_ref] in
    environment [c_env] and returns the corresponding description. If this
    lookup fails, a fatal error is thrown using location [l] for the error message. *)
val c_env_lookup : Ast.l -> c_env -> const_descr_ref -> const_descr

(** [c_env_store_raw c_env c_d] stores the description [c_d] 
    environment [c_env]. Thereby, a new unique reference is generated and returned
    along with the modified environment. It stores the real [c_d] passed. The function
    [c_env_store] preprocesses [c_d] to add common features like for example 
    capitalizing constructors for the Ocaml backend. *)
val c_env_store_raw : c_env -> const_descr -> (c_env * const_descr_ref)

(** [c_env_update c_env c_ref c_d] updates the description of constant [c_ref] with 
    [c_d] in environment [c_env]. *)
val c_env_update : c_env -> const_descr_ref -> const_descr -> c_env

(** [env_c_env_update env c_ref c_d] updates the description of constant [c_ref] with 
    [c_d] in environment [env]. *)
val env_c_env_update : env -> const_descr_ref -> const_descr -> env

(** [c_env_all_consts c_env] returns the constants defined in [c_env] *)
val c_env_all_consts : c_env -> const_descr_ref list

val exp_to_locn : exp -> Ast.l
val exp_to_typ : exp -> Types.t

(** append_lskips adds new whitespace/newline/comments to the front of an
    expression (before any existing whitespace/newline/comments in front of the
    expression) *)
val append_lskips : lskips -> exp -> exp 
val pat_append_lskips : lskips -> pat -> pat

(** [alter_init_lskips] finds all of the whitespace/newline/comments preceding an
    expression and passes it to the supplied function in a single invocation.
    The preceding whitespace/newline/comments are replaced with the fst of the
    function's result, and the snd of the function's result is returned from
    alter_init_lskips *)
val alter_init_lskips : (lskips -> lskips * lskips) -> exp -> exp * lskips
val pat_alter_init_lskips : (lskips -> lskips * lskips) -> pat -> pat * lskips
val def_aux_alter_init_lskips : (lskips -> lskips * lskips) -> def_aux -> def_aux * lskips
val def_alter_init_lskips : (lskips -> lskips * lskips) -> def -> def * lskips
val oi_alter_init_lskips : (lskips -> lskips * lskips) -> Ast.open_import -> Ast.open_import * lskips 

val pp_const_descr : Format.formatter -> const_descr -> unit
val pp_env : Format.formatter -> env -> unit
val pp_local_env : Format.formatter -> local_env -> unit
val pp_c_env : Format.formatter -> c_env -> unit
val pp_instances : Format.formatter -> Types.instance list Types.Pfmap.t -> unit

type imported_modules =
  | IM_paths of Path.t list
  | IM_targets of targets_opt * string list

type checked_module =
    { filename : string; 
      module_path : Path.t;
      imported_modules : imported_modules list; 
      imported_modules_rec : imported_modules list;
      untyped_ast : Ast.defs * Ast.lex_skips;
      typed_ast : def list * Ast.lex_skips; 
      generate_output : bool}

(** [var_avoid_f] is a type of a tuple [(avoid_ty_vars, name_ok, do_rename)]. 
    The flag [avoid_ty_vars] states, whether clashes with type variables should be avoided.
    The [name_ok n] checks whether the name [n] is OK. 
    If it is not OK, the function [do_rename n_text check] renames [n].
    As input it takes the text of [n], a function [check] that checks whether the new
    name clashes with any names to be avoided or existing variable names in the context. *)
type var_avoid_f = bool * (Name.t -> bool) * (Ulib.Text.t -> (Name.t -> bool) -> Name.t)

module type Exp_context = sig
  (** The environment the expressions are considered in *)
  val env_opt : env option

  (** Avoiding certain names for local variables.  Given a name and a set of
      names that must be avoided, choose a new name if necessary *)
  val avoid : var_avoid_f option

end

module Exps_in_context(C : Exp_context) : sig
  val exp_subst : (Types.t Types.TNfmap.t * exp_subst Nfmap.t) -> exp -> exp
  val push_subst : (Types.t Types.TNfmap.t * exp_subst Nfmap.t) -> pat list -> exp -> pat list * exp
  val exp_to_term : exp -> exp_aux
  val exp_to_free : exp -> Types.t Nfmap.t
  val type_eq : Ast.l -> string -> Types.t -> Types.t -> unit
  val mk_lnumeral : Ast.l -> lskips -> int -> string option -> Types.t option -> lit
  val mk_lnum : Ast.l -> lskips -> int -> string option -> Types.t -> lit 
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
  val mk_pconst : Ast.l -> const_descr_ref id -> pat list -> Types.t option -> pat
  val mk_pbackend : Ast.l -> lskips -> Ident.t -> Types.t -> pat list -> Types.t option -> pat
  val mk_precord : Ast.l -> lskips -> (const_descr_ref id * lskips * pat) lskips_seplist -> lskips -> Types.t option -> pat
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
  val mk_backend : Ast.l -> lskips -> Ident.t -> Types.t -> exp
  val mk_const : Ast.l -> const_descr_ref id -> Types.t option -> exp
  val mk_fun : Ast.l -> lskips -> pat list -> lskips -> exp -> Types.t option -> exp
  val mk_function : Ast.l -> lskips -> (pat * lskips * exp * Ast.l) lskips_seplist -> lskips -> Types.t option -> exp
  val mk_app : Ast.l -> exp -> exp -> Types.t option -> exp
  val mk_infix : Ast.l -> exp -> exp -> exp -> Types.t option -> exp
  val mk_record : Ast.l -> lskips -> (const_descr_ref id * lskips * exp * Ast.l) lskips_seplist-> lskips -> Types.t option -> exp
(*  val mk_record_coq : Ast.l -> lskips -> (const_descr_ref id * lskips * exp * Ast.l) lskips_seplist-> lskips -> Types.t option -> exp*)
  val mk_recup : Ast.l -> lskips -> exp -> lskips -> (const_descr_ref id * lskips * exp * Ast.l) lskips_seplist -> lskips -> Types.t option -> exp
  val mk_field : Ast.l -> exp -> lskips -> const_descr_ref id -> Types.t option -> exp
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
  val mk_do : Ast.l -> lskips -> Path.t id -> do_line list -> lskips -> exp -> lskips -> (Types.t * bind_tyargs_order) -> Types.t option -> exp
  val t_to_src_t : Types.t -> src_t
  val pat_subst : Types.t Types.TNfmap.t * Name.t Nfmap.t -> pat -> pat
end

val local_env_union : local_env -> local_env -> local_env

(** Mutually recursive function definitions may contain multiple clauses for the
    same function. These can however appear interleaved with clauses for other functions. 
    [funcl_aux_seplist_group seplist] sorts the clauses according to the function names and
    states, whether any resorting was necessary. Moreover, the initial lskip is returned, if present. *)
val funcl_aux_seplist_group : funcl_aux lskips_seplist -> (bool * lskips option * (Name.t * funcl_aux lskips_seplist) list)

(** [class_path_to_dict_name cp tv] creates a name for the class [cp]
    with type argument [tv].  This name is used during dictionary
    passing. If a function has a type constraint that type-variable
    [tv] is of type-class [cp], the function call
    [class_path_to_dict_name cp tv] is used to generate the name of a
    new argument. This argument is a dictionary that is used to eliminate the use
    of type classes.

    This design is very fragile and should probably be changed in the future!
    [class_path_to_dict_name] needs to generate names that globally do not clash with
    anything else, including names generated by [class_path_to_dict_name] itself. The
    generated name is independently used by both definition macros adding the 
    argument to the definition and expression macros that use the added argument.
    The name used in both places has to coincide! Therefore, the name cannot be modified 
    depending on the context. Renaming to avoid clashes with other arguments /
    local variables is not possible. *)
val class_path_to_dict_name : Path.t -> Types.tnvar -> Name.t


val ident_get_lskip : 'a id -> Ast.lex_skips
val ident_replace_lskip : ident_option -> Ast.lex_skips -> ident_option
val oi_get_lskip : Ast.open_import -> Ast.lex_skips
