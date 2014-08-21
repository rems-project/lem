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
open Target
module NameSet = Set.Make(Name)
module Nfmap = Finite_map.Fmap_map(Name)
type name_l = Name.lskips_t * Ast.l
type lskips = Ast.lex_skips

let nfmap_domain (m : 'a Nfmap.t) :NameSet.t = Nfmap.domain m
let r = Ulib.Text.of_latin1

let no_lskips = None
let space = Some([Ast.Ws(r" ")])

let lskips_only_comments_first coms = 
  match coms with
    | [] -> None
    | c::cs -> begin
        match List.fold_right Ast.combine_lex_skips cs None with
         | None -> c
         | Some(l) ->
             Ast.combine_lex_skips c 
               (Some(List.filter (function | Ast.Com _ -> true | _ -> false) l))
      end

let lskips_only_comments coms = 
  match List.fold_right Ast.combine_lex_skips coms None with
    | None -> space
    | Some(l) ->
        Some(List.filter (function | Ast.Com _ -> true | _ -> false) l @[Ast.Ws(r" ")])

type 'a lskips_seplist = ('a, lskips) Seplist.t

type env_tag = 
  | K_let
  | K_field
  | K_constr
  | K_relation
  | K_method
  | K_instance

type const_descr_ref = Types.const_descr_ref

type name_kind =
  | Nk_typeconstr of Path.t
  | Nk_const of const_descr_ref
  | Nk_constr of const_descr_ref
  | Nk_field of const_descr_ref
  | Nk_module of Path.t
  | Nk_class of Path.t

type p_env = (Path.t * Ast.l) Nfmap.t

type lit = (lit_aux,unit) annot

and lit_aux =
  | L_true of lskips
  | L_false of lskips
  | L_zero of lskips
  | L_one of lskips
  | L_numeral of lskips * int * string option 
  | L_num of lskips * int * string option
  | L_char of lskips * char * string option
  | L_string of lskips * string * string option
  | L_unit of lskips * lskips
  | L_vector of lskips * string * string
  | L_undefined of lskips * string

type pat = (pat_aux,pat_annot) annot
and pat_annot = { pvars : free_env }

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

and cr_special_fun =
  | CR_special_uncurry of int
  | CR_special_rep of string list * exp list

and const_target_rep =
  | CR_inline of Ast.l * bool * name_lskips_annot list * exp
  | CR_infix of Ast.l * bool * Ast.fixity_decl * Ident.t
  | CR_undefined of Ast.l * bool 
  | CR_simple of Ast.l * bool * name_lskips_annot list * exp
  | CR_special of Ast.l * bool * cr_special_fun * name_lskips_annot list

and rel_io = Rel_mode_in | Rel_mode_out
and rel_mode = rel_io list
and rel_output_type = Out_list | Out_pure | Out_option | Out_unique
and rel_info = {
  ri_witness : (Path.t * const_descr_ref Nfmap.t) option;
  ri_check : const_descr_ref option;
  ri_fns : ((rel_mode * bool * rel_output_type) * const_descr_ref) list
}

and const_descr = { const_binding : Path.t;
                    const_tparams : Types.tnvar list;
                    const_class : (Path.t * Types.tnvar) list;
                    const_no_class : const_descr_ref Targetmap.t;
                    const_ranges : Types.range list;
                    const_type : t; 
		    relation_info: rel_info option;
                    env_tag : env_tag;
                    const_targets : Targetset.t;
                    spec_l : Ast.l;
                    target_rename : (Ast.l * Name.t) Targetmap.t;
                    target_ascii_rep : (Ast.l * Name.t) Targetmap.t;
                    target_rep : const_target_rep Targetmap.t;
                    compile_message : string Target.Targetmap.t;
                    termination_setting: Ast.termination_setting Targetmap.t}

and v_env = const_descr_ref Nfmap.t
and f_env = const_descr_ref Nfmap.t
and m_env = Path.t Nfmap.t
and c_env = const_descr cdmap
and e_env = mod_descr Pfmap.t

and local_env = { m_env : m_env; p_env : p_env; f_env : f_env; v_env : v_env}
and env = { local_env : local_env; c_env : c_env; t_env : Types.type_defs; i_env : Types.i_env; e_env : e_env}

(* free_env represents the free variables in expression, with their types *)
and free_env = t Nfmap.t

and mod_target_rep =
  | MR_rename of Ast.l * Name.t

and mod_descr = { mod_binding    : Path.t;
                  mod_env        : local_env; 
                  mod_target_rep : mod_target_rep Targetmap.t;
		  mod_filename   : string option;
                  mod_in_output  : bool }

and exp = (exp_aux,exp_annot) annot
(* We keep typ with the subst applied, and term and free without, we also only
* keep subst bindings (for the exp subst) that are free in the unapplied free
* map *)
and exp_annot = 
  { free  : free_env;
    bound : NameSet.t;
    subst : t TNfmap.t * exp_subst Nfmap.t; }
and exp_subst = 
  | Sub of exp
  | Sub_rename of Name.t

and exp_aux =
  | Var of Name.lskips_t
  | Backend of lskips * Ident.t
  | Nvar_e of lskips * Nvar.t
  | Constant of const_descr_ref id
  | Fun of lskips * pat list * lskips * exp
  | Function of lskips * (pat * lskips * exp * Ast.l) lskips_seplist * lskips
  | App of exp * exp
  (* The middle exp must be a Var, Constant, or Constructor *) 
  | Infix of exp * exp * exp
  | Record of lskips * fexp lskips_seplist * lskips
  | Recup of lskips * exp * lskips * fexp lskips_seplist * lskips
  | Field of exp * lskips * const_descr_ref id
  | Vector of lskips * exp lskips_seplist * lskips
  (* | VectorC of lskips * exp * lskips * exp *)
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
  | Do of lskips * Path.t id * do_line list * lskips * exp * lskips * (Types.t * bind_tyargs_order)

and do_line = Do_line of (pat * lskips * exp * lskips)

and bind_tyargs_order = 
   | BTO_input_output (** [['a, 'b]] *)
   | BTO_output_input (** [['b, 'a]] *)

and fexp = const_descr_ref id * lskips * exp * Ast.l

and name_lskips_annot = (Name.lskips_t,unit) annot

and quant_binding =
  | Qb_var of name_lskips_annot
  (* true for list quantifiers, false for set quantifiers *)
  | Qb_restr of bool * lskips * pat * lskips * exp * lskips

and funcl_aux = name_lskips_annot * const_descr_ref * pat list * (lskips * src_t) option * lskips * exp

and letbind = letbind_aux * Ast.l

and letbind_aux = 
  | Let_val of pat * (lskips * src_t) option * lskips * exp
  | Let_fun of name_lskips_annot * pat list * (lskips * src_t) option * lskips * exp

let cr_special_fun_uses_name = function
  | (CR_special_uncurry _) -> true
  | (CR_special_rep _) -> false

let big_union sets =
  List.fold_right NameSet.union sets NameSet.empty

let rec pat_to_bound_names pat =
  match pat.term with
    | P_wild _ -> NameSet.empty
    | P_as (_, pat, _, _, _) -> pat_to_bound_names pat
    | P_typ (_, pat, _, _, _) -> pat_to_bound_names pat
    | P_var name -> NameSet.add (Name.strip_lskip name) NameSet.empty
    | P_const (_, pats) -> big_union (List.map pat_to_bound_names pats)
    | P_backend (_, _, _, pats) -> big_union (List.map pat_to_bound_names pats)
    | P_record (_, pats, _) ->
      let pats = Seplist.to_list pats in
      let sets = List.map (fun (_, _, p) ->
          pat_to_bound_names p
        ) pats
      in
        big_union sets
    | P_vector (_, pats, _) ->
      let pats = Seplist.to_list pats in
      let sets = List.map pat_to_bound_names pats in
        big_union sets
    | P_vectorC (_, pats, _) -> big_union (List.map pat_to_bound_names pats)
    | P_tup (_, pats, _) ->
      let pats = Seplist.to_list pats in
        big_union (List.map pat_to_bound_names pats)
    | P_list (_, pats, _) ->
      let pats = Seplist.to_list pats in
        big_union (List.map pat_to_bound_names pats)
    | P_paren (_, pat, _) -> pat_to_bound_names pat
    | P_cons (patl, _, patr) ->
      NameSet.union (pat_to_bound_names patl) (pat_to_bound_names patr)
    | P_num_add (name_l, _, _, _) -> NameSet.empty
    | P_lit _ -> NameSet.empty
    | P_var_annot (name, _) -> NameSet.add (Name.strip_lskip name) NameSet.empty


type tyvar = lskips * Ulib.Text.t * Ast.l
type nvar = lskips * Ulib.Text.t * Ast.l

type tnvar = 
  | Tn_A of tyvar
  | Tn_N of nvar

type texp = 
  | Te_opaque
  | Te_abbrev of lskips * src_t
  | Te_record of lskips * lskips * (name_l * const_descr_ref * lskips * src_t) lskips_seplist * lskips
  | Te_variant of lskips * (name_l * const_descr_ref * lskips * src_t lskips_seplist) lskips_seplist

type range = 
  | GtEq of Ast.l * src_nexp * lskips * src_nexp
  | Eq of Ast.l * src_nexp * lskips * src_nexp

type constraints = 
  | Cs_list of (Ident.t * tnvar) lskips_seplist * lskips option * range lskips_seplist * lskips

type constraint_prefix =
  | Cp_forall of lskips * tnvar list * lskips * constraints option

type typschm = constraint_prefix option * src_t

type instschm = constraint_prefix option * lskips * Ident.t * Path.t * src_t * lskips

type targets_opt = 
   Targets_opt_none
 | Targets_opt_concrete of lskips * Ast.target lskips_seplist * lskips
 | Targets_opt_neg_concrete of lskips * Ast.target lskips_seplist * lskips
 | Targets_opt_non_exec of lskips

let in_targets_opt_raw (targ : Target.target) (targets_opt : targets_opt) : bool = match targ with
    Target_ident   -> true
  | Target_no_ident t -> (match targets_opt with 
        Targets_opt_none -> true
      | Targets_opt_concrete (_, targets, _) -> 
          Seplist.exists (fun t' -> ast_target_compare (target_to_ast_target t) t' = 0) targets
      | Targets_opt_neg_concrete (_, targets, _) -> 
          not (Seplist.exists (fun t' -> ast_target_compare (target_to_ast_target t) t' = 0) targets)
      | Targets_opt_non_exec _ ->
          not (List.exists (fun t' -> target_compare t t' = 0) Target.all_targets_only_exec_list))

let in_targets_opt (targ : Target.target) (targets_opt : targets_opt) : bool = 
   if is_human_target targ then true else in_targets_opt_raw targ targets_opt

let targets_opt_to_list (targets_opt : targets_opt) : Target.non_ident_target list =
   List.filter (fun t -> in_targets_opt_raw (Target_no_ident t) targets_opt) Target.all_targets_list
                         
let in_target_set (targ : Target.target) (targetset : Target.Targetset.t) : bool = 
  match dest_human_target targ with
    | None   -> true
    | Some t -> Target.Targetset.mem t targetset 


type val_spec       = lskips *               name_l * const_descr_ref * Ast.ascii_opt * lskips * typschm
type class_val_spec = lskips * targets_opt * name_l * const_descr_ref * Ast.ascii_opt * lskips * src_t

type fun_def_rec_flag =
  | FR_non_rec
  | FR_rec of lskips

type val_def = 
  | Let_def of lskips * targets_opt * (pat * (Name.t * const_descr_ref) list * (lskips * src_t) option * lskips * exp)
  | Fun_def of lskips * fun_def_rec_flag * targets_opt * funcl_aux lskips_seplist
  | Let_inline of lskips * lskips * targets_opt * name_lskips_annot * const_descr_ref * name_lskips_annot list * lskips * exp

type name_sect = Name_restrict of (lskips * name_l * lskips * lskips * string * lskips)

type indreln_rule_quant_name = 
  | QName of name_lskips_annot
  | Name_typ of lskips * name_lskips_annot * lskips * src_t * lskips

type indreln_rule_aux = Rule of Name.lskips_t * lskips * lskips * indreln_rule_quant_name list * lskips * exp option * lskips * name_lskips_annot * const_descr_ref * exp list
type indreln_rule = indreln_rule_aux * Ast.l

type indreln_witness = Indreln_witness of lskips * lskips * Name.lskips_t * lskips
type indreln_indfn = Indreln_fn of Name.lskips_t * lskips * src_t * lskips option
type indreln_name = RName of lskips* Name.lskips_t * const_descr_ref * lskips * typschm * (indreln_witness option) * ((lskips*Name.lskips_t*lskips) option) * (indreln_indfn list) option * lskips

type 
target_rep_rhs =  (* right hand side of a target representation declaration *)
   Target_rep_rhs_infix of lskips * Ast.fixity_decl * lskips * Ident.t
 | Target_rep_rhs_term_replacement of exp
 | Target_rep_rhs_type_replacement of src_t
 | Target_rep_rhs_special of lskips * lskips * string * exp list
 | Target_rep_rhs_undefined  


type declare_def =  (* declarations *)
 | Decl_compile_message       of lskips * targets_opt * lskips * const_descr_ref id * lskips * lskips * string 
 | Decl_target_rep_term       of lskips * Ast.target  * lskips * Ast.component * const_descr_ref id * name_lskips_annot list * lskips * target_rep_rhs
 | Decl_target_rep_type       of lskips * Ast.target  * lskips * lskips * Path.t id * tnvar list * lskips * src_t
 | Decl_ascii_rep             of lskips * targets_opt * lskips * Ast.component * name_kind id * lskips * lskips * Name.t
 | Decl_rename                of lskips * targets_opt * lskips * Ast.component * name_kind id * lskips * Name.lskips_t
 | Decl_rename_current_module of lskips * targets_opt * lskips * lskips * lskips * Name.lskips_t 
 | Decl_termination_argument  of lskips * targets_opt * lskips * const_descr_ref id * lskips * Ast.termination_setting
 | Decl_pattern_match_decl    of lskips * targets_opt * lskips * Ast.exhaustivity_setting * Path.t id * tnvar list * lskips * lskips * (const_descr_ref id) lskips_seplist * lskips * (const_descr_ref id) option
(*
 | Decl_set_flag              of lskips * lskips * Name.lskips_t * lskips * Name.lskips_t
*)

type def = (def_aux * lskips option) * Ast.l * local_env
and def_aux =
  | Type_def of lskips * (name_l * tnvar list * Path.t * texp * name_sect option) lskips_seplist
  | Val_def of val_def 
  | Lemma of lskips * Ast.lemma_typ * targets_opt * name_l * lskips * exp 
  | Module of lskips * name_l * Path.t * lskips * lskips * def list * lskips
  | Rename of lskips * name_l * Path.t * lskips * Path.t id
  | OpenImport of Ast.open_import * (Path.t id) list
  | OpenImportTarget of Ast.open_import * targets_opt * (lskips * string) list
  | Indreln of lskips * targets_opt * indreln_name lskips_seplist * indreln_rule lskips_seplist
  | Val_spec of val_spec
  | Class of Ast.class_decl * lskips * name_l * tnvar * Path.t * lskips * class_val_spec list * lskips
  (* The v_env, name and Path/tyvar list are for converting the instance into a module. *)
  | Instance of Ast.instance_decl * Types.instance_ref * instschm * val_def list * lskips 
  | Comment of def
  | Declaration of declare_def


let tnvar_to_types_tnvar tnvar = 
  match tnvar with
    | Tn_A(sk, tv, l) -> (Ty(Tyvar.from_rope tv),l)
    | Tn_N(sk, nv, l) -> (Nv(Nvar.from_rope nv),l)

let empty_local_env = { m_env = Nfmap.empty;
                        p_env = Nfmap.empty;
                        f_env = Nfmap.empty; 
                        v_env = Nfmap.empty; }

let empty_env = { local_env = empty_local_env;
                  c_env = cdmap_empty();
                  t_env = Pfmap.empty;
                  i_env = Types.empty_i_env;
                  e_env = Pfmap.empty }


let c_env_lookup l m c = 
         match cdmap_lookup m c with
           | None -> 
             let m = Format.sprintf "constant-description reference %s not present in environment" (string_of_const_descr_ref c) in
             raise (Reporting_basic.err_type l m)
           | Some(cd) -> cd

let e_env_lookup l m p = 
         match Pfmap.apply m p with
           | None -> 
             let m = Format.sprintf "module-description for module %s not present in environment" (Path.to_string p) in
             raise (Reporting_basic.err_type l m)
           | Some(md) -> md

let c_env_update = cdmap_update 

let env_c_env_update env c_id c_d =
  { env with c_env = c_env_update env.c_env c_id c_d }

let c_env_store_raw = cdmap_insert

let c_env_all_consts = cdmap_domain



(* Applies lskips_f to the leftmost lskips in p, replacing it with lskips_f's
 * first result and returning lskips_f's second result *)
let lit_alter_init_lskips (lskips_f : lskips -> lskips * lskips) (l : lit) : lit * lskips = 
  let res t s = ({ l with term = t }, s) in
    match l.term with
      | L_true(s) -> 
          let (s_new,s_ret) = lskips_f s in
            res (L_true(s_new)) s_ret
      | L_false(s) ->
          let (s_new,s_ret) = lskips_f s in
            res (L_false(s_new)) s_ret
      | L_undefined(s,n) -> 
          let (s_new,s_ret) = lskips_f s in
            res (L_undefined(s_new,n)) s_ret
      | L_zero(s) ->
          let (s_new,s_ret) = lskips_f s in
            res (L_zero(s_new)) s_ret
      | L_one(s) ->
          let (s_new,s_ret) = lskips_f s in
            res (L_one(s_new)) s_ret
      | L_num(s,n,org) ->
          let (s_new,s_ret) = lskips_f s in
            res (L_num(s_new,n,org)) s_ret
      | L_numeral(s,n,org) ->
          let (s_new,s_ret) = lskips_f s in
            res (L_numeral(s_new,n,org)) s_ret
      | L_char(s,c, input_c) ->
          let (s_new,s_ret) = lskips_f s in
            res (L_char(s_new,c,input_c)) s_ret
      | L_string(s,n,input_s) ->
          let (s_new,s_ret) = lskips_f s in
            res (L_string(s_new,n,input_s)) s_ret
      | L_vector(s,n,m) ->
          let (s_new,s_ret) = lskips_f s in
            res (L_vector(s_new,n,m)) s_ret
      | L_unit(s1,s2) ->
          let (s_new,s_ret) = lskips_f s1 in
            res (L_unit(s_new,s2)) s_ret

let rec pat_alter_init_lskips (lskips_f : lskips -> lskips * lskips) (p : pat) : pat * lskips =
  let res t s = ({ p with term = t }, s) in
    match p.term with
      | P_wild(s) -> 
          let (s_new, s_ret) = lskips_f s in
            res (P_wild(s_new))s_ret
      | P_as(s1,p,s2,nl,s3) -> 
          let (s_new, s_ret) = lskips_f s1 in
            res (P_as(s_new,p, s2, nl,s3)) s_ret
      | P_typ(s1,p,s2,t,s3) -> 
          let (s_new, s_ret) = lskips_f s1 in
            res (P_typ(s_new, p, s2, t, s3)) s_ret
      | P_var(n) -> 
          let (s_new, s_ret) = lskips_f (Name.get_lskip n) in
            res (P_var(Name.replace_lskip n s_new)) s_ret
      | P_const(c,ps) -> 
          let (id_new, s_ret) = id_alter_init_lskips lskips_f c in
            res (P_const(id_new,ps)) s_ret
      | P_backend(sk,i,ty,ps) -> 
          let (s_new, s_ret) = lskips_f sk in
            res (P_backend(s_new, i, ty, ps)) s_ret
      | P_record(s1,fieldpats,s2) -> 
          let (s_new, s_ret) = lskips_f s1 in
            res (P_record(s_new, fieldpats, s2)) s_ret
      | P_vector(s1,vectorpats,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (P_vector(s_new,vectorpats,s2)) s_ret
      | P_vectorC(s1, vectorpats,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (P_vectorC(s_new,vectorpats,s2)) s_ret
      | P_tup(s1,ps,s2) -> 
          let (s_new, s_ret) = lskips_f s1 in
            res (P_tup(s_new, ps, s2)) s_ret
      | P_list(s1,ps,s2) -> 
          let (s_new, s_ret) = lskips_f s1 in
            res (P_list(s_new, ps, s2)) s_ret
      | P_paren(s1,ps,s2) -> 
          let (s_new, s_ret) = lskips_f s1 in
            res (P_paren(s_new, ps, s2)) s_ret
      | P_cons(p1,s,p2) -> 
          let (p_new, s_ret) = pat_alter_init_lskips lskips_f p1 in
            res (P_cons(p_new, s, p2)) s_ret
      | P_num_add((n,l),s1,s2,i) ->
          let (s_new, s_ret) = lskips_f (Name.get_lskip n) in
            res (P_num_add((Name.replace_lskip n s_new, l), s1, s2, i)) s_ret
      | P_lit(l) ->
          let (l_new, s_ret) = lit_alter_init_lskips lskips_f l in
            res (P_lit(l_new)) s_ret
      | P_var_annot(n,t) -> 
          let (s_new, s_ret) = lskips_f (Name.get_lskip n) in
            res (P_var_annot(Name.replace_lskip n s_new,t)) s_ret


let pat_append_lskips lskips (p : pat) : pat =
  let (p, _) = pat_alter_init_lskips (fun s -> (Ast.combine_lex_skips lskips s, None)) p in
    p

let rec alter_init_lskips (lskips_f : lskips -> lskips * lskips) (e : exp) : exp * lskips = 
  let res t s = ({ e with term = t }, s) in
    match e.term with
      | Var(n) ->
          let (s_new, s_ret) = lskips_f (Name.get_lskip n) in
            res (Var(Name.replace_lskip n s_new)) s_ret
      | Backend(sk, i) ->
          let (s_new, s_ret) = lskips_f sk in
            res (Backend(s_new, i)) s_ret
      | Nvar_e(s,n) ->
          let (s_new, s_ret) = lskips_f s in
            res (Nvar_e(s_new,n)) s_ret 
      | Constant(c) ->
          let (id_new, s_ret) = id_alter_init_lskips lskips_f c in
            res (Constant(id_new)) s_ret
      | Fun(s1,ps,s2,e) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Fun(s_new,ps,s2,e)) s_ret
      | Function(s1,pes,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Function(s_new, pes,s2)) s_ret
      | App(e1,e2) -> begin
          match e1.term with
            | Backend (sk, i) when (Ident.to_string i = "") ->
                let e1' = { e with term = Backend (None, i) } in
                let lskips_f' sk2 = lskips_f (Ast.combine_lex_skips sk sk2) in
                let (e_new, s_ret) = alter_init_lskips lskips_f' e2 in
                   res (App(e1', e_new)) s_ret
            | _ -> let (e_new, s_ret) = alter_init_lskips lskips_f e1 in
                   res (App(e_new, e2)) s_ret
        end
      | Infix(e1,e2,e3) ->
          let (e_new, s_ret) = alter_init_lskips lskips_f e1 in
            res (Infix(e_new, e2, e3)) s_ret
      | Record(s1,fieldexps,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Record(s_new, fieldexps,s2)) s_ret
      | Recup(s1,e,s2,fieldexps,s3) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Recup(s_new, e, s2, fieldexps,s3)) s_ret
      | Field(e,s,fd) ->
          let (e_new, s_ret) = alter_init_lskips lskips_f e in
            res (Field(e_new, s, fd)) s_ret
      | Vector(s1, vconsts,s2) ->
          let (s_new,s_ret) = lskips_f s1 in
            res (Vector(s_new,vconsts,s2)) s_ret
            (* TODO: Cut
      | VectorC(s1,v1,s2,v2) ->
          let (s_new,s_ret) = lskips_f s1 in
            res (VectorC(s_new,v1,s2,v2)) s_ret 
            *)
      | VectorSub(v,s1,n1,s2,n2,s3) ->
          let (v_new, s_ret) = alter_init_lskips lskips_f v in
            res (VectorSub(v_new,s1,n1,s2,n2,s3)) s_ret
      | VectorAcc(v,s1,n,s2) ->
          let (v_new, s_ret) = alter_init_lskips lskips_f v in
            res (VectorAcc(v_new,s1,n,s2)) s_ret
      | Case(c,s1,e,s2,patexps,s3) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Case(c,s_new,e,s2,patexps,s3)) s_ret
      | Typed(s1,e,s2,src_t,s3) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Typed(s_new,e,s2,src_t,s3)) s_ret
      | Let(s1,letbinds,s2,e) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Let(s_new,letbinds,s2,e)) s_ret
      | Tup(s1,es,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Tup(s_new, es, s2)) s_ret
      | List(s1,es,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (List(s_new,es,s2)) s_ret
      | Paren(s1,e,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Paren(s_new,e,s2)) s_ret
      | Begin(s1,e,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Begin(s_new,e,s2)) s_ret
      | If(s1,e1,s2,e2,s3,e3) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (If(s_new,e1,s2,e2,s3,e3)) s_ret
      | Lit(l) ->
          let (l_new, s_ret) = lit_alter_init_lskips lskips_f l in
            res (Lit(l_new)) s_ret
      | Set(s1,es,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Set(s_new,es,s2)) s_ret
      | Setcomp(s1,e1,s2,e2,s3,bindings) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Setcomp(s_new, e1, s2, e2, s3,bindings)) s_ret
      | Comp_binding(is_lst,s1,e1,s2,s5,qbs,s3,e2,s4) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Comp_binding(is_lst,s_new, e1, s2, s5, qbs, s3, e2, s4)) s_ret
      | Quant(Ast.Q_forall(s1),ns,s2,e) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Quant(Ast.Q_forall(s_new), ns, s2, e)) s_ret
      | Quant(Ast.Q_exists(s1),ns,s2,e) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Quant(Ast.Q_exists(s_new), ns, s2, e)) s_ret
      | Do(s1,mid,do_lines,sk2,e,sk3,t) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Do(s_new,mid,do_lines,sk2,e,sk3,t)) s_ret

let append_lskips lskips (p : exp) : exp =
  let (e, _) = alter_init_lskips (fun s -> (Ast.combine_lex_skips lskips s, None)) p in
    e

let oi_alter_init_lskips lskips_f (oi : Ast.open_import) : (Ast.open_import * lskips) = 
  match oi with
    | Ast.OI_open sk ->
        let (s_new, s_ret) = lskips_f sk in
        (Ast.OI_open s_new, s_ret)
    | Ast.OI_import sk ->
        let (s_new, s_ret) = lskips_f sk in
        (Ast.OI_import s_new, s_ret)
    | Ast.OI_open_import (sk, sk') ->
        let (s_new, s_ret) = lskips_f sk in
        (Ast.OI_open_import (s_new, sk'), s_ret)
    | Ast.OI_include sk ->
        let (s_new, s_ret) = lskips_f sk in
        (Ast.OI_include s_new, s_ret)
    | Ast.OI_include_import (sk, sk') ->
        let (s_new, s_ret) = lskips_f sk in
        (Ast.OI_include_import (s_new, sk'), s_ret)

let rec def_aux_alter_init_lskips (lskips_f : lskips -> lskips * lskips) d : def_aux * lskips = 
  let res x y = (x,y) in
    match d with
      | Type_def(sk, tds) ->
          let (s_new, s_ret) = lskips_f sk in
            res (Type_def(s_new,tds)) s_ret
      | Val_def(Let_def(sk, topt, lb)) -> 
          let (s_new, s_ret) = lskips_f sk in
            res (Val_def(Let_def(s_new,topt,lb))) s_ret
      | Val_def(Fun_def(sk1, sk2, topt, funs)) -> 
          let (s_new, s_ret) = lskips_f sk1 in
            res (Val_def(Fun_def(s_new, sk2, topt, funs))) s_ret
      | Val_def(Let_inline(sk1,sk2,targ,n,c,ns,sk4,e)) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Val_def(Let_inline(s_new,sk2,targ,n,c,ns,sk4,e))) s_ret
      | Lemma(sk1, lty, targ, n, sk2, e) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Lemma(s_new, lty, targ, n,sk2, e)) s_ret
      | Module(sk1, n, mod_bind, sk2, sk3, ds, sk4) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Module(s_new, n, mod_bind, sk2, sk3, ds, sk4)) s_ret
      | Rename(sk1, n, mod_bind, sk2, m) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Rename(s_new, n, mod_bind, sk2, m)) s_ret
      | OpenImport(oi,m) -> begin     
          let (oi', s_ret) = oi_alter_init_lskips lskips_f oi in
          res (OpenImport(oi',m)) s_ret
        end
      | OpenImportTarget(oi,targets,m) -> begin     
          let (oi', s_ret) = oi_alter_init_lskips lskips_f oi in
          res (OpenImportTarget(oi',targets,m)) s_ret
        end
      | Indreln(sk,topt,names,rules) ->
          let (s_new, s_ret) = lskips_f sk in
            res (Indreln(s_new,topt,names,rules)) s_ret
      | Val_spec(sk1,n,n_ref,ao,sk2,ts) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Val_spec(s_new,n,n_ref,ao,sk2,ts)) s_ret
      | Class(Ast.Class_decl sk1,sk2,n,tvar,class_ty,sk3,body,sk4) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Class(Ast.Class_decl s_new,sk2,n,tvar,class_ty,sk3,body,sk4)) s_ret
      | Class(Ast.Class_inline_decl (sk1, sk1'),sk2,n,tvar,class_ty,sk3,body,sk4) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Class(Ast.Class_inline_decl (s_new,sk1'),sk2,n,tvar,class_ty,sk3,body,sk4)) s_ret
      | Instance(Ast.Inst_decl sk1,i_ref,is,ds,sk2) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Instance(Ast.Inst_decl s_new,i_ref,is,ds,sk2)) s_ret
      | Instance(Ast.Inst_default sk1,i_ref,is,ds,sk2) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Instance(Ast.Inst_default s_new,i_ref,is,ds,sk2)) s_ret
      | Comment(d) ->
          let (d',s_ret) = def_alter_init_lskips lskips_f d in
            res (Comment(d')) s_ret
      | Declaration d -> begin     
          let (d', s_ret) = match d with
            | Decl_compile_message (sk1, targs, sk2, id, sk3, sk4, msg) ->
                let (sk1', s_ret) = lskips_f sk1 in
                (Decl_compile_message (sk1', targs, sk2, id, sk3, sk4, msg), s_ret)
            | Decl_target_rep_term (sk1, targ, sk2, comp, id, args, sk3, rhs) ->
                let (sk1', s_ret) = lskips_f sk1 in
                (Decl_target_rep_term (sk1', targ, sk2, comp, id, args, sk3, rhs), s_ret)
            | Decl_target_rep_type (sk1, targ, sk2, sk3, id, args, sk4, rhs) ->
                let (sk1', s_ret) = lskips_f sk1 in
                (Decl_target_rep_type (sk1', targ, sk2, sk3, id, args, sk4, rhs), s_ret)
            | Decl_ascii_rep (sk1, targs, sk2, comp, id, sk3, sk4, n) ->
                let (sk1', s_ret) = lskips_f sk1 in
                (Decl_ascii_rep (sk1', targs, sk2, comp, id, sk3, sk4, n), s_ret)
            | Decl_rename (sk1, targs, sk2, comp, id, sk3, n) ->
                let (sk1', s_ret) = lskips_f sk1 in
                (Decl_rename (sk1', targs, sk2, comp, id, sk3, n), s_ret)
            | Decl_rename_current_module (sk1, targs, sk2, sk3, sk4, n) ->
                let (sk1', s_ret) = lskips_f sk1 in
                (Decl_rename_current_module (sk1', targs, sk2, sk3, sk4, n), s_ret)
            | Decl_termination_argument (sk1, targs, sk2, id, sk3, ts) ->
                let (sk1', s_ret) = lskips_f sk1 in
                (Decl_termination_argument (sk1', targs, sk2, id, sk3, ts), s_ret)
            | Decl_pattern_match_decl (sk1, targs, sk2, ex_set, p_id, args, sk3, sk4, constr_ids, sk5, elim_id_opt) ->
                let (sk1', s_ret) = lskips_f sk1 in
                (Decl_pattern_match_decl (sk1', targs, sk2, ex_set, p_id, args, sk3, sk4, constr_ids, sk5, elim_id_opt), s_ret)
          in
          res (Declaration d') s_ret
        end
and def_alter_init_lskips (lskips_f : lskips -> lskips * lskips) (((d,s),l,lenv) : def) : def * lskips = 
  let (d', y) = def_aux_alter_init_lskips lskips_f d in
  (((d',s),l,lenv),y)

let exp_to_locn e = e.locn
let exp_to_typ e = e.typ

let remove_binders (binders : NameSet.t) (vsubst : exp_subst Nfmap.t) 
      : exp_subst Nfmap.t = 
  if Nfmap.is_empty vsubst then
    vsubst
  else
    NameSet.fold (fun pvar sub -> Nfmap.remove sub pvar) binders vsubst

let empty_sub = (TNfmap.empty, Nfmap.empty)

open Pp
open Format

let pp_env_tag ppf tag = 
  match tag with
    | K_method -> Format.fprintf ppf "method"
    | K_field -> Format.fprintf ppf "field"
    | K_constr -> Format.fprintf ppf "constr"
    | K_instance -> Format.fprintf ppf "instance"
    | K_let -> Format.fprintf ppf "let"
    | K_relation -> Format.fprintf ppf "relation"

let pp_const_descr ppf c =
  fprintf ppf "@[<2>forall@ (@[%a@]).@ @[%a@]@ @[%a@]@ =>@ %a@]@ (%a)@ %a"
    (lst ",@," TNvar.pp) c.const_tparams
    (lst "@ " pp_class_constraint) c.const_class
    (lst "@ " pp_range) c.const_ranges
    pp_type c.const_type
    Path.pp c.const_binding
    pp_env_tag c.env_tag

let pp_const_ref ppf c =
  fprintf ppf "%s" (string_of_const_descr_ref c)

let pp_c_env ppf m =
  fprintf ppf "cdmap"

let rec pp_local_env ppf env =
  pp_open_box ppf 0;
  let empty_m = Nfmap.is_empty env.m_env in
  let empty_v = Nfmap.is_empty env.v_env in
  let empty_p = Nfmap.is_empty env.p_env in
  let empty_f = Nfmap.is_empty env.f_env in
  (Nfmap.pp_map Name.pp Path.pp) ppf env.m_env;
    if not empty_m && not empty_v then
      fprintf ppf "@\n";
  (Nfmap.pp_map Name.pp pp_const_ref) ppf env.v_env; 
    if not empty_v && not empty_p then
      fprintf ppf "@\n";
    (Nfmap.pp_map Name.pp (fun ppf (p, _) -> Path.pp ppf p)) ppf env.p_env;
    if not empty_p && not empty_f then
      fprintf ppf "@\n";
    (Nfmap.pp_map Name.pp pp_const_ref) ppf env.f_env; 
  pp_close_box ppf ()

and pp_env ppf env =
  pp_open_box ppf 0;
(*  let empty_m = Nfmap.is_empty env.m_env in
  let empty_v = Nfmap.is_empty env.v_env in
  let empty_p = Nfmap.is_empty env.p_env in
  let empty_f = Nfmap.is_empty env.f_env in
    (Nfmap.pp_map Name.pp pp_mod_descr) ppf env.m_env;
    if not empty_m && not empty_v then
      fprintf ppf "@\n";
(*    (Nfmap.pp_map Name.pp pp_const_descr) ppf env.v_env; *)
    if not empty_v && not empty_p then
      fprintf ppf "@\n";
    (Nfmap.pp_map Name.pp (fun ppf (p, _) -> Path.pp ppf p)) ppf env.p_env;
    if not empty_p && not empty_f then
      fprintf ppf "@\n";
(*    (Nfmap.pp_map Name.pp pp_field_descr) ppf env.f_env; *)
*)
    pp_close_box ppf ()

and pp_mod_descr ppf (md : mod_descr) = 
  pp_local_env ppf md.mod_env

let pp_instances = Pfmap.pp_map Path.pp (lst "@\n" pp_instance)

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
      generate_output : bool }

type var_avoid_f = bool * (Name.t -> bool) * (Ulib.Text.t -> (Name.t -> bool) -> Name.t)

module type Exp_context = sig
  val env_opt : env option
  val avoid : var_avoid_f option
end

module Exps_in_context(D : Exp_context) = struct
  
  let check = D.env_opt <> None

  let empty_free_env = Nfmap.empty

  let sing_free_env k v = Nfmap.from_list [(k,v)]

  let type_eq l m t1 t2 =
    match D.env_opt with
      | None -> ()
      | Some(env) ->
          assert_equal l m env.t_env t1 t2

  let check_typ l (m : string) (t_given : t option) (t_built_f : type_defs -> t option) : t =
    let t_build_d_opt = Util.option_bind (fun env -> Util.option_map (fun t -> (t, env.t_env)) (t_built_f env.t_env)) D.env_opt in
    match (t_given,t_build_d_opt) with
      | (None,None) -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_type (l, "check_typ case (None, None) " ^ m)))
      | (Some(t),None) -> t
      | (None,Some(t, _)) -> t
      | (Some(t1),Some(t2, d)) -> 
          assert_equal l m d t1 t2;
          t1

  let merge_free_env for_pat l (envs : free_env list) : free_env = 
    List.fold_left
      (fun e_res e ->
         Nfmap.merge
           (fun k v1 v2 ->
              match (v1,v2) with
                | (None,_) -> v2
                | (_,None) -> v1
                | (Some(v),Some(v')) ->
                    if for_pat then
                      raise (Reporting_basic.err_type l ("Duplicate variable in a pattern: " ^
                                        Pp.pp_to_string (fun ppf -> Name.pp ppf k)))
                    else
                      begin
                        try
                          type_eq l "merge_free_env" v v'
                        with
                          | Reporting_basic.Fatal_error (Reporting_basic.Err_type (l,s)) ->
                              raise (Reporting_basic.err_type l (s ^ "\n in merging: " ^ Pp.pp_to_string (fun ppf -> Name.pp ppf k)))
                      end;
                    v1)
           e_res
           e)
      empty_free_env
      envs

  let bind_free_env l pat_env exp_env =
    Nfmap.fold
      (fun e_res k v ->
         match Nfmap.apply e_res k with
           | None -> e_res
           | Some(v') -> 
               begin
                 try
                   type_eq l "bind_free_env" v v'
                 with
                   | Reporting_basic.Fatal_error (Reporting_basic.Err_type (l,s)) ->
                       raise (Reporting_basic.err_type l (s ^ "\nin binding " ^ Pp.pp_to_string (fun ppf -> Name.pp ppf k)))
               end;
               Nfmap.remove e_res k)
      exp_env
      pat_env

  let mk_pwild l s t : pat =
    { term = P_wild(s);
      locn = l;
      typ = t;
      rest = { pvars = empty_free_env; }; }

  let mk_pas l s1 p s2 nl s3 t =
    let t = check_typ l "mk_pas" t (fun d -> Some p.typ) in
      { term = P_as(s1,p,s2,nl,s3);
        locn = l;
        typ = t;
        rest = 
          { pvars = 
              merge_free_env true l
                [sing_free_env (Name.strip_lskip (fst nl)) t; 
                 p.rest.pvars]; }; }

  let mk_ptyp l s1 p s2 t1 s3 t =
    let t = check_typ l "mk_ptyp" t (fun d -> Some p.typ) in
      type_eq l "mk_ptyp" p.typ t1.typ;
      { term = P_typ(s1,p,s2,t1,s3);
        locn = l;
        typ = t;
        rest = { pvars = p.rest.pvars; }; }

  let mk_pvar l n t : pat =
    { term = P_var(n);
      locn = l;
      typ = t;
      rest = { pvars = sing_free_env (Name.strip_lskip n) t; }; }

  let mk_pconst l c ps t =
    (* only perform checks, if environment is provided *)
    let c_base_ty_opt = Util.option_map (fun env -> begin
      let d = c_env_lookup l env.c_env c.descr in
      let subst = TNfmap.from_list2 d.const_tparams c.instantiation in
      let new_c_ty = type_subst subst d.const_type in
      let (c_tyL, c_base_ty) = Types.strip_fn_type (Some env.t_env) new_c_ty in
      let _ = if check then
    (** TODO: perhaps add check for right no of args again 
    if List.length ps <> List.length c.descr.constr_args
    then raise (Ident.No_type(l, "wrong number of arguments for constructor")); *)
      begin
          List.iter2
            (fun t p -> type_eq l "mk_pconst" t p.typ)
            c_tyL
            ps
      end in
      c_base_ty
    end) D.env_opt in
    let t = 
      check_typ l "mk_pconst" t (fun d -> c_base_ty_opt)
    in
    { term = P_const(c,ps);
      locn = l;
      typ = t;
      rest = { pvars = merge_free_env true l (List.map (fun p -> p.rest.pvars) ps); }; }

  let mk_pbackend l sk i ty ps t =
    (* only perform checks, if environment is provided *)
    let c_base_ty_opt = Util.option_map (fun env -> begin
      let new_c_ty = ty in
      let (c_tyL, c_base_ty) = Types.strip_fn_type (Some env.t_env) new_c_ty in
      let _ = if check then
    (** TODO: perhaps add check for right no of args again 
    if List.length ps <> List.length c.descr.constr_args
    then raise (Ident.No_type(l, "wrong number of arguments for constructor")); *)
      begin
          List.iter2
            (fun t p -> type_eq l "mk_pconst" t p.typ)
            c_tyL
            ps
      end in
      c_base_ty
    end) D.env_opt in
    let t = 
      check_typ l "mk_pconst" t (fun d -> c_base_ty_opt)
    in
    { term = P_backend(sk,i,ty,ps);
      locn = l;
      typ = t;
      rest = { pvars = merge_free_env true l (List.map (fun p -> p.rest.pvars) ps); }; }

  let mk_precord l s1 fps s2 t =
    let f_rec_ty_opt = Util.option_bind (fun env -> begin
      let (f,_,p) = Seplist.hd fps in
      let d = c_env_lookup l env.c_env f.descr in
      let subst = TNfmap.from_list2 d.const_tparams f.instantiation in
      let new_f_ty = type_subst subst d.const_type in
      Util.option_map (fun (t, _) -> t) (Types.dest_fn_type (Some env.t_env) new_f_ty)
    end) D.env_opt in
    let t = 
      check_typ l "mk_precord" t (fun d -> f_rec_ty_opt)
    (* TODO: Add more checks *)
    in
      { term = P_record(s1,fps,s2);
        locn = l;
        typ = t;
        rest = 
          { pvars = 
              merge_free_env true l 
                (Seplist.to_list_map (fun (_,_,p) -> p.rest.pvars) fps); }; }


  let mk_ptup l s1 ps s2 t =
    let t = 
      check_typ l "mk_ptup" t
        (fun d -> Some { t = Ttup(Seplist.to_list_map (fun p -> p.typ) ps) } )
    in
      { term = P_tup(s1,ps,s2);
        locn = l;
        typ = t;
        rest = 
          { pvars = 
              merge_free_env true l (Seplist.to_list_map (fun p -> p.rest.pvars) ps); }; }

  let mk_plist l s1 ps s2 t =
    if check then
      Seplist.iter 
        (fun p -> type_eq l "mk_plist" { t = Tapp([p.typ], Path.listpath) } t) 
        ps;
    { term = P_list(s1,ps,s2);
      locn = l;
      typ = t;
      rest = 
        { pvars = 
            merge_free_env true l (Seplist.to_list_map (fun p -> p.rest.pvars) ps); }; }

  let mk_pvector l s1 ps s2 t =
    if check then
       type_eq l "mk_pvector" { t= Tapp([((Seplist.hd ps).typ);{t=Tne({nexp=Nconst(Seplist.length ps)})} ], Path.vectorpath) } t;
    (* TODO KG need to check here that the types are all the same *)
    { term = P_vector(s1,ps,s2);
       locn = l;
       typ = t;
       rest = {pvars = merge_free_env true l (Seplist.to_list_map (fun p -> p.rest.pvars) ps); }; }

  let mk_pvectorc l s1 ps s2 t =
    (* TODO KG add check *)
     { term = P_vectorC(s1,ps,s2);
       locn = l;
       typ = t;
       rest = {pvars = merge_free_env true l (List.map (fun p -> p.rest.pvars) ps); }; }
   
  let mk_pparen l s1 p s2 t =
    let t = check_typ l "mk_pparen" t (fun d -> Some p.typ) in
      { term = P_paren(s1,p,s2);
        locn = l;
        typ = t; 
        rest = { pvars = p.rest.pvars; }; }

  let mk_pcons l p1 s p2 t =
    let t = check_typ l "mk_pcons" t (fun d -> Some p2.typ) in
      type_eq l "mk_pcons" p2.typ { t = Tapp([p1.typ], Path.listpath) };
      { term = P_cons(p1,s,p2);
        locn = l;
        typ = t; 
        rest = { pvars = merge_free_env true l [p1.rest.pvars; p2.rest.pvars]; }; }

  let mk_pnum_add l xl s1 s2 i t =
    let t = check_typ l "mk_pnum_add" t (fun d -> Some { t = Tapp([], Path.natpath) }) in
      { term = P_num_add(xl,s1,s2,i);
        locn = l;
        typ = t; 
        rest = { pvars = sing_free_env (Name.strip_lskip (fst xl)) t; }; }

  let mk_plit l li t = 
    let t = check_typ l "mk_plit" t (fun d -> Some li.typ) in
    { term = P_lit(li);
      locn = l;
      typ = t; 
      rest = { pvars = empty_free_env; }; }

  let mk_pvar_annot l n src_t t : pat =
    let t = check_typ l "mk_pvar_annot" t (fun d -> Some src_t.typ) in
      { term = P_var_annot(n,src_t);
        locn = l;
        typ = t;
        rest = { pvars = sing_free_env (Name.strip_lskip n) t; }; }

  let rec pat_subst ((tsubst,rename) as sub) p =
    let l = p.locn in
    let new_typ = type_subst tsubst p.typ in
    match p.term with
      | P_var(n) ->
          let n' = begin
            match Nfmap.apply rename (Name.strip_lskip n) with
              | None -> n
              | Some(n') -> (Name.lskip_rename (fun _ -> Name.to_rope n') n)
          end in
          mk_pvar l n' new_typ
      | P_as(s1,p,s2,(n,l),s3) -> 
          let n' = 
            match Nfmap.apply rename (Name.strip_lskip n) with
              | None -> n
              | Some(n') ->
                  Name.lskip_rename (fun _ -> Name.to_rope n') n
          in
            mk_pas l s1 (pat_subst sub p) s2 (n',l) s3 (Some new_typ)
      | P_typ(s1,p,s2,src_t,s3) -> 
          mk_ptyp l s1 (pat_subst sub p) s2 src_t s3 (Some new_typ)
      | P_const(c,ps) -> 
          let c =
            { c with instantiation = 
                List.map (type_subst tsubst) c.instantiation }
          in
            mk_pconst l c (List.map (pat_subst sub) ps) (Some new_typ)
      | P_backend(sk,i,ty,ps) -> 
          mk_pbackend l sk i (type_subst tsubst ty) (List.map (pat_subst sub) ps) (Some new_typ)
      | P_record(s1,fieldpats,s2) ->
          mk_precord l
            s1 
            (Seplist.map 
               (fun (fid,s1,p) -> 
                  let fid = 
                    { fid with instantiation = 
                        List.map (type_subst tsubst) fid.instantiation }
                  in
                    (fid, s1,pat_subst sub p))
               fieldpats)
            s2
            (Some new_typ)
      | P_vector(s1,vpats,s2) ->
          mk_pvector l s1 (Seplist.map (pat_subst sub) vpats) s2 new_typ
      | P_vectorC(s1,vpats,s2) ->
          mk_pvectorc l s1 (List.map (pat_subst sub) vpats) s2 new_typ
      | P_tup(s1,ps,s2) -> 
          mk_ptup l s1 (Seplist.map (pat_subst sub) ps) s2 (Some new_typ)
      | P_list(s1,ps,s2) -> 
          mk_plist l s1 (Seplist.map (pat_subst sub) ps) s2 new_typ
      | P_paren(s1,p,s2) -> 
          mk_pparen l s1 (pat_subst sub p) s2 (Some new_typ)
      | P_cons(p1,s,p2) -> 
          mk_pcons l (pat_subst sub p1) s (pat_subst sub p2) (Some new_typ)
      | P_num_add((n,l'),s1,s2,i) -> 
          begin
            match Nfmap.apply rename (Name.strip_lskip n) with
              | None -> p
              | Some(n') ->
                   mk_pnum_add l  
                      ((Name.lskip_rename (fun _ -> Name.to_rope n') n), l')
                      s1 s2 i (Some new_typ)
          end
      | (P_lit _ | P_wild _) ->
          {p with typ = new_typ}
      | P_var_annot(n,t) ->
          let n' = begin
            match Nfmap.apply rename (Name.strip_lskip n) with
              | None -> n
              | Some(n') -> (Name.lskip_rename (fun _ -> Name.to_rope n') n)
          end in 
          (* todo: preserve type-annotation *)
          mk_pvar l n' new_typ


  let cut_subst sub free =
    Nfmap.fold
      (fun res_sub n e ->
         if Nfmap.in_dom n free then
           Nfmap.insert res_sub (n,e)
         else
           res_sub)
      Nfmap.empty
      sub

  (* TODO: Pushing a subst with freevars through a binder and type substs in
   * src_ts *)
  let rec exp_subst (tsubst,(vsubst:exp_subst Nfmap.t)) e : exp =
    let (existing_tsubst, existing_vsubst) = e.rest.subst in
    let new_tsubst = 
      if TNfmap.is_empty tsubst then
        existing_tsubst
      else
        TNfmap.map (fun n t -> type_subst tsubst t) existing_tsubst
    in
    let new_vsubst = 
      if TNfmap.is_empty tsubst && Nfmap.is_empty vsubst then
        existing_vsubst
      else
        Nfmap.map (fun n exp ->
                     match exp with
                       | Sub(exp) ->
                           Sub(exp_subst (tsubst, vsubst) exp)
                       | Sub_rename(n) ->
                           match Nfmap.apply vsubst n with
                             | None -> Sub_rename(n)
                             | Some(e) -> e)
          existing_vsubst 
    in
      { term = e.term;
        locn = e.locn;
        typ = type_subst tsubst e.typ;
        rest =
          { free = e.rest.free;
            bound = e.rest.bound;
            subst = (TNfmap.union tsubst new_tsubst, 
                     Nfmap.union (cut_subst vsubst e.rest.free) new_vsubst); }; }


   let rec exp_to_free e = 
    let (tsubst,vsubst) = e.rest.subst in
    let free' = 
      if TNfmap.is_empty tsubst then
        e.rest.free
      else
        Nfmap.map (fun _ t -> type_subst tsubst t) e.rest.free
    in
      if Nfmap.is_empty vsubst then
        free'
      else
        Nfmap.fold
          (fun fr n t ->
             match Nfmap.apply vsubst n with
               | None -> 
                   merge_free_env false Ast.Unknown [fr; sing_free_env n t]
               | Some(Sub(e)) ->
                   merge_free_env false Ast.Unknown [fr; exp_to_free e]
               | Some(Sub_rename(n')) ->
                   merge_free_env false Ast.Unknown 
                     [fr; sing_free_env n' t])
          Nfmap.empty
          free'

  let exp_to_free_tyvars e =
    let ty = exp_to_typ e in
    let tv_set = free_vars ty in
    let nset = TNset.fold (fun tv s -> NameSet.add (Types.tnvar_to_name tv) s) tv_set NameSet.empty in
    nset

  let pat_to_free_tyvars (p : pat) =
    let ty = annot_to_typ p in
    let tv_set = free_vars ty in
    let nset = TNset.fold (fun tv s -> NameSet.add (Types.tnvar_to_name tv) s) tv_set NameSet.empty in
    nset

  let subst_freevars subst = 
    Nfmap.fold
      (fun fv n esub ->
         match esub with
           | Sub(exp) -> NameSet.union (Nfmap.domain (exp_to_free exp)) fv
           | Sub_rename(n) -> NameSet.add n fv)
      NameSet.empty
      subst
  (* Rename the binders that conflict with avoid or the free variables of the
   * substitution.  When choosing the new name, don't rename to names in
   * would_capture.  Return the renamings, and the substitution modified for
   * use under the bingers *)
  let get_renames binders vsubst would_capture free_typevar = 
    (* First, remove the substitutions that are hidden by the binders we're
     * pushing it under *)
    let vsubst = remove_binders binders vsubst in
    let (avoid_ty, avoid_f) =
      match D.avoid with
        | None -> (false, (fun x -> false))
        | Some((ty,f1,_)) -> (ty, (fun x -> not (f1 x)))
    in
    (* Binders need renaming if they occur free in the substitution, or if
     * their name must be avoided *)
    let needs_rename = 
      NameSet.fold
        (fun n needs_rename ->
           if NameSet.mem n (subst_freevars vsubst) || avoid_f n || (avoid_ty && NameSet.mem n free_typevar) then
             n::needs_rename
           else
             needs_rename)
        binders
        []
    in
    let rename_f =
      match D.avoid with
        | None -> Name.fresh
        | Some((_,_,f2)) -> f2
    in
    (* Uses new_bindings to make sure we don't accidentally choose the name
     * renaming twice, new_bindings contains all old binders to start with
     * in order to avoid renaming to a value that is not in needs_renaming *)
    let (renames,_) = 
      List.fold_right
        (fun n (subst,new_bindings) -> 
           let b = 
             rename_f (Name.to_rope n)
               (fun n -> 
                  not (NameSet.mem n new_bindings) && 
                  not (NameSet.mem n would_capture) &&
                  not (avoid_ty && NameSet.mem n free_typevar))
           in
             (Nfmap.insert subst (n, b), NameSet.add b new_bindings))
        needs_rename
        (Nfmap.empty,binders)
    in
    let new_vsubst =
      Nfmap.union (Nfmap.map (fun _ n -> Sub_rename(n)) renames) vsubst 
    in
      (renames,new_vsubst)

  let push_pat_exp_bind_list f_aux not_to_choose' (tsubst,vsubst) pes es =
    let not_to_choose = 
      List.fold_left
        (fun s e -> NameSet.union (Nfmap.domain (exp_to_free e)) s)
        not_to_choose'
        es
    in
    let not_to_choose_ty = 
      List.fold_left
        (fun s e -> NameSet.union (exp_to_free_tyvars e) s)
        NameSet.empty
        es
    in
    let (new_pes,new_vsubst) =
      f_aux not_to_choose not_to_choose_ty (tsubst,vsubst) pes
    in
      (new_pes, List.map (exp_subst (tsubst,new_vsubst)) es)

  let rec push_subst (tsubst,vsubst) ps e =
    let binders =
      List.fold_left
        (fun binders p ->
          NameSet.union (Nfmap.domain p.rest.pvars) binders)
        NameSet.empty
        ps
    in
    let binder_tyvars =
      List.fold_left
        (fun binder_tyvars p -> NameSet.union (pat_to_free_tyvars p) binder_tyvars)
        NameSet.empty
        ps
    in
    let (renames,new_vsubst) = 
      get_renames binders vsubst (Nfmap.domain (exp_to_free e)) (NameSet.union (exp_to_free_tyvars e) binder_tyvars)
    in
    let bound =
      NameSet.fold (fun e set ->
        match Nfmap.apply renames e with
          | None -> NameSet.add e set
          | Some n -> NameSet.add n set) binders NameSet.empty
    in
    let (renames,new_vsubst) = 
      get_renames binders vsubst (NameSet.union (Nfmap.domain (exp_to_free e)) bound) (NameSet.union (exp_to_free_tyvars e) binder_tyvars)
    in
      (List.map (pat_subst (tsubst,renames)) ps,
       exp_subst (tsubst,new_vsubst) e)

  and push_subst1 (tsubst,vsubst) p e =
    match push_subst (tsubst,vsubst) [p] e with
      | ([p'],e') -> (p',e')
      | _ -> assert false

  and push_subst_name subst n e =
    match push_subst1 subst (mk_pvar Ast.Unknown n.term n.typ) e with
      | ({ term = P_var(n'); typ = t; locn = l }, e) ->
          ({ n with term = n'; typ = t; locn = l; }, e)
      | _ -> assert false

  and push_quant_binds_subst_aux not_to_choose not_to_choose_ty (tsubst, vsubst) = function
    | [] -> ([], vsubst)
    | Qb_var(n)::qbs ->
        let binders = NameSet.singleton (Name.strip_lskip n.term) in
        let (renames, new_vsubst) = 
          get_renames binders vsubst not_to_choose not_to_choose_ty
        in
        let n' = 
          match pat_subst (tsubst,renames) (mk_pvar Ast.Unknown n.term n.typ) with
            | { term = P_var(n'); typ = t; locn = l } ->
                { n with term = n'; typ = t; locn = l; }
            | _ -> assert false
        in
        let (qbs, s) =
          push_quant_binds_subst_aux 
            (NameSet.add (Name.strip_lskip n'.term) not_to_choose) 
            not_to_choose_ty
            (tsubst, new_vsubst)
            qbs
        in
          (Qb_var(n')::qbs, s)
    | Qb_restr(lst,s1,p,s2,e,s3)::qbs ->
        let binders = Nfmap.domain p.rest.pvars in
        let (renames,new_vsubst) = 
          get_renames binders vsubst not_to_choose not_to_choose_ty
        in
        let p' = pat_subst (tsubst,renames) p in
        let e' = exp_subst (tsubst,vsubst) e in
        let (qbs, s) =
          push_quant_binds_subst_aux 
            (NameSet.union (Nfmap.domain p'.rest.pvars) not_to_choose) 
            not_to_choose_ty
            (tsubst, new_vsubst)
            qbs
        in
          (Qb_restr(lst,s1,p',s2,e',s3)::qbs, s)

  and push_quant_binds_subst (tsubst,vsubst) qbs es =
    let not_to_choose' =
      List.fold_left
        (fun s qb ->
           match qb with
             | Qb_var(n) -> NameSet.add (Name.strip_lskip n.term) s
             | Qb_restr(_,_,p,_,e,_) ->
                 NameSet.union 
                   (Nfmap.domain p.rest.pvars)
                   (NameSet.union (Nfmap.domain (exp_to_free e)) s))
        NameSet.empty
        qbs
    in
    push_pat_exp_bind_list push_quant_binds_subst_aux not_to_choose' (tsubst,vsubst) qbs es

  and push_quant_binds_subst1 subst qbs e =
    match push_quant_binds_subst subst qbs [e] with
      | (qbs,[e]) -> (qbs,e)
      | _ -> assert false

  and push_quant_binds_subst2 subst qbs e1 e2 =
    match push_quant_binds_subst subst qbs [e1;e2] with
      | (qbs,[e1;e2]) -> (qbs,e1,e2)
      | _ -> assert false

  (* This is very similar to push_quant_binds_subst_aux, but OCaml doesn't 
   * give us a very good way to abstract *)
  and push_do_lines_subst_aux not_to_choose not_to_choose_ty (tsubst, vsubst) = function
    | [] -> ([], vsubst)
    | Do_line(p,s1,e,s2)::do_lines ->
        let binders = Nfmap.domain p.rest.pvars in
        let (renames,new_vsubst) = 
          get_renames binders vsubst not_to_choose not_to_choose_ty
        in
        let p' = pat_subst (tsubst,renames) p in
        let e' = exp_subst (tsubst,vsubst) e in
        let (do_lines, s) =
          push_do_lines_subst_aux 
            (NameSet.union (Nfmap.domain p'.rest.pvars) not_to_choose) 
            not_to_choose_ty
            (tsubst, new_vsubst)
            do_lines
        in
          (Do_line(p',s1,e',s2)::do_lines, s)

  and push_do_lines_subst (tsubst,vsubst) do_lines e =
    let not_to_choose' =
      List.fold_left
        (fun s line ->
           match line with
             | Do_line(p,_,e,_) ->
                 NameSet.union 
                   (Nfmap.domain p.rest.pvars)
                   (NameSet.union (Nfmap.domain (exp_to_free e)) s))
        NameSet.empty
        do_lines
    in
      push_pat_exp_bind_list push_do_lines_subst_aux not_to_choose' (tsubst,vsubst) do_lines [e]

  and exp_to_term e = 
    let (tsubst, vsubst) = e.rest.subst in
    let subst = (tsubst,vsubst) in
    let id_subst i = 
      { i with instantiation = List.map (type_subst tsubst) i.instantiation }
    in
      match e.term with
        | Var(n) -> 
            begin
              match Nfmap.apply vsubst (Name.strip_lskip n) with
                | None -> Var(n)
                | Some(Sub_rename(n')) ->
                    Var(Name.lskip_rename (fun _ -> Name.to_rope n') n)
                | Some(Sub(e')) -> 
                    exp_to_term (append_lskips (Name.get_lskip n) e')
            end
        | Backend (s,i) -> Backend (s,i)
        | Nvar_e(s,v) -> Nvar_e(s,v)
        | Constant(c) -> 
            Constant(id_subst c)
        | Fun(s1,ps,s2,e) ->
            let (ps,e) = push_subst subst ps e in
              Fun(s1,ps,s2,e)
        | Function(s1,pes,s2) ->
            Function(s1,
                     Seplist.map
                       (fun (p,s3,e,l) -> 
                          let (p,e) = 
                            push_subst1 subst p e 
                          in
                            (p,s3,e,l))
                       pes,
                     s2)
        | App(e1,e2) ->
            App(exp_subst subst e1, exp_subst subst e2)
        | Infix(e1,e2,e3) ->
            Infix(exp_subst subst e1, exp_subst subst e2, exp_subst subst e3)
        | Record(s1,fieldexps,s2) ->
            Record(s1, 
                   Seplist.map 
                     (fun (fd,s3,e,l) -> (id_subst fd,s3,exp_subst subst e, l)) 
                     fieldexps, 
                   s2)
        | Recup(s1,e,s2,fieldexps,s3) ->
            Recup(s1,
                  exp_subst subst e, 
                  s2,
                  Seplist.map 
                    (fun (fd,s3,e,l) -> (id_subst fd,s3,exp_subst subst e, l)) 
                    fieldexps,
                  s3)         
        | Field(e,s,fd) ->
            Field(exp_subst subst e, s, id_subst fd)
        | Vector(s1,es,s2) ->
            Vector(s1, Seplist.map (exp_subst subst) es, s2)
            (* TODO: Cut
        | VectorC(s1,exp1,s2,exp2) ->
            VectorC(s1, (exp_subst subst) exp1, s2, (exp_subst subst) exp2) 
*)
        | VectorSub(exp,s1,n1,s2,n2,s3) ->
            VectorSub((exp_subst subst) exp, s1, n1, s2, n2,s3)
        | VectorAcc(exp,s1,nexp,s2) ->
            VectorAcc((exp_subst subst) exp,s1, nexp, s2)
        | Case(c,s1,e,s2,patexps,s3) ->
            Case(c,s1,
                 exp_subst subst e,
                 s2,
                 Seplist.map
                   (fun (p,s4,e,l) -> 
                      let (p,e) = push_subst1 subst p e in
                        (p,s4,e,l))
                   patexps,
                 s3)
        | Typed(s1,e,s2,src_t,s3) ->
            Typed(s1, exp_subst subst e, s2, src_t, s3)
        | Let(s1,(Let_val(p,topt,s,e'),l),s2,e) ->
            let (p,e) = push_subst1 subst p e in
              Let(s1,(Let_val(p,topt,s,exp_subst subst e'),l), s2, e)
        | Let(s1,(Let_fun(n,ps,topt,s,e'),l),s2,e) ->
            let (ps,e') = push_subst subst ps e' in
            let (n,e) = push_subst_name subst n e in
              Let(s1,(Let_fun (n,ps,topt,s,e'), l),s2,e)
        | Tup(s1,es,s2) ->
            Tup(s1, Seplist.map (exp_subst subst) es, s2)
        | List(s1,es,s2) ->
            List(s1, Seplist.map (exp_subst subst) es, s2)
        | Paren(s1,e,s2) ->
            Paren(s1,exp_subst subst e,s2)
        | Begin(s1,e,s2) ->
            Begin(s1,exp_subst subst e,s2)
        | If(s1,e1,s2,e2,s3,e3) ->
            If(s1, exp_subst subst e1, 
               s2, exp_subst subst e2, 
               s3, exp_subst subst e3)
        | Lit(l) ->
            Lit(l)
        | Set(s1,es,s2) ->
            Set(s1, Seplist.map (exp_subst subst) es, s2)
        | Setcomp(s1,e1,s2,e2,s3,bindings) ->
            let new_vsubst =
              NameSet.fold
                (fun n sub -> Nfmap.remove sub n)
                bindings
                vsubst 
            in
            let new_subst = (tsubst, new_vsubst) in
              Setcomp(s1,exp_subst new_subst e1, s2, exp_subst new_subst e2, s3,bindings)
        | Comp_binding(is_lst,s1,e1,s2,s5,qbs,s3,e2,s4) ->
            let (new_qbs,e1,e2) = 
              push_quant_binds_subst2 subst qbs e1 e2 
            in
              Comp_binding(is_lst,s1, e1, s2, s5, new_qbs, s3, e2, s4)
        | Quant(q,qbs,s,e) ->
            let (new_qbs,e) = push_quant_binds_subst1 subst qbs e in
              Quant(q,new_qbs,s,e)
        | Do(s1,mid,do_lines,s2,e,s3,t) ->
            let (new_do_lines,e) = push_do_lines_subst subst do_lines e in
              Do(s1,mid,new_do_lines,s2, List.hd e, s3,t)

  and exp_to_binders (e : exp) : NameSet.t =
  	match exp_to_term e with
  		| Let (_, (letbind, _), _, exp) ->
  		  let letbind_vars =
  				match letbind with
  					| Let_val (pat, _, _, exp) ->
  					    let pat_vars = Nfmap.domain pat.rest.pvars in
  					    let exp_bind = exp_to_binders exp in
  					    	NameSet.union pat_vars exp_bind
  			  	| Let_fun (_, pats, _, _, exp) ->
  			  	    let pat_vars = List.fold_right NameSet.union (List.map (fun p -> Nfmap.domain p.rest.pvars) pats) NameSet.empty in
  			  	    let exp_bind = exp_to_binders exp in
  			  	    	NameSet.union pat_vars exp_bind
  	    in
  	      NameSet.union letbind_vars (exp_to_binders exp)
  	  | Tup (_, exps, _) ->
  	    let lexps = Seplist.to_list exps in
  	      List.fold_right NameSet.union (List.map exp_to_binders lexps) NameSet.empty
  	  | Fun (_, pats, _, exp) ->
  	      let pat_vars = List.fold_right NameSet.union (List.map (fun p -> Nfmap.domain p.rest.pvars) pats) NameSet.empty in
  	      let exp_bind = exp_to_binders exp in
  	        NameSet.union pat_vars exp_bind
  	  | App (left, right) ->
  	      NameSet.union (exp_to_binders left) (exp_to_binders right)
  	  | Infix (left, centre, right) ->
  	      NameSet.union (exp_to_binders left) (NameSet.union (exp_to_binders centre) (exp_to_binders right))
  	  | Paren (_, exp, _) -> exp_to_binders exp
  	  | Typed (_, exp, _, _, _) -> exp_to_binders exp
  	  | Begin (_, exp, _) -> exp_to_binders exp
  	  | If (_, cond, _, t, _, f) ->
  	      NameSet.union (exp_to_binders cond) (NameSet.union (exp_to_binders t) (exp_to_binders f))
  	  | List (_, exps, _) ->
  	      let lexps = Seplist.to_list exps in
  	        List.fold_right NameSet.union (List.map exp_to_binders lexps) NameSet.empty
  	  | Set (_, exps, _) ->
  	      let lexps = Seplist.to_list exps in
  	        List.fold_right NameSet.union (List.map exp_to_binders lexps) NameSet.empty
  	  | Setcomp (_, exp0, _, exp1, _, name_set) ->
  	      NameSet.union name_set (NameSet.union (exp_to_binders exp0) (exp_to_binders exp1))
  	  | Var _ -> NameSet.empty
  	  | Backend _ -> NameSet.empty
  	  | Nvar_e _ -> NameSet.empty
  	  | Constant _ -> NameSet.empty
  	  | Function (_, pat_exps, _) ->
  	      let lpat_exps = Seplist.to_list pat_exps in
  	      let binds = List.map (fun (pat, _, exp, _) -> NameSet.union (Nfmap.domain pat.rest.pvars) (exp_to_binders exp)) lpat_exps in
  	        List.fold_right NameSet.union binds NameSet.empty
  	  | Lit _ -> NameSet.empty
  	  | Field (exp, _, _) -> exp_to_binders exp
  	  | Vector (_, exps, _) ->
  	      let lexps = Seplist.to_list exps in
  	        List.fold_right NameSet.union (List.map exp_to_binders lexps) NameSet.empty
  	  | VectorSub (exp, _, _, _, _, _) -> exp_to_binders exp
  	  | VectorAcc (exp, _, _, _) -> exp_to_binders exp
  	  | Quant (_, quants, _, exp) ->
  	      let quant_binding_to_binder binding =
  	        match binding with
  	          | Qb_var name_lskips_annot ->
  	              NameSet.singleton (Name.strip_lskip (name_lskips_annot.term))
              | Qb_restr (_, _, pat, _, exp, _) ->
                  NameSet.union (Nfmap.domain pat.rest.pvars) (exp_to_binders exp)
          in
          let qbind = List.fold_right NameSet.union (List.map quant_binding_to_binder quants) NameSet.empty in
            NameSet.union qbind (exp_to_binders exp)
  	  | Record (_, fexps, _) ->
  	      let fexp_to_binder (_, _, exp, _) = exp_to_binders exp in
  	      let lfexps = Seplist.to_list fexps in
  	        List.fold_right NameSet.union (List.map fexp_to_binder lfexps) NameSet.empty
  	  | Recup (_, exp, _, fexps, _) ->
  	    	let fexp_to_binder (_, _, exp, _) = exp_to_binders exp in
  	      let lfexps = Seplist.to_list fexps in
  	      let binds = List.fold_right NameSet.union (List.map fexp_to_binder lfexps) NameSet.empty in
  	        NameSet.union binds (exp_to_binders exp)
  	  | Case (_, _, cond, _, pat_exps, _) ->
  	      let lpat_exps = Seplist.to_list pat_exps in
  	      let bind      = List.fold_right NameSet.union (List.map (fun (pat, _, exp, _) -> NameSet.union (Nfmap.domain pat.rest.pvars) (exp_to_binders exp)) lpat_exps) NameSet.empty in
  	        NameSet.union bind (exp_to_binders cond)
  	  | Comp_binding (_, _, exp0, _, _, quants, _, exp1, _) ->
  	    	let quant_binding_to_binder binding =
  	        match binding with
  	          | Qb_var name_lskips_annot ->
  	              NameSet.singleton (Name.strip_lskip (name_lskips_annot.term))
              | Qb_restr (_, _, pat, _, exp, _) ->
                  NameSet.union (Nfmap.domain pat.rest.pvars) (exp_to_binders exp)
          in
          let qbind = List.fold_right NameSet.union (List.map quant_binding_to_binder quants) NameSet.empty in
            NameSet.union (exp_to_binders exp0) (NameSet.union (exp_to_binders exp1) qbind)
  	  | Do (_, _, lines, _, exp, _, _) ->
  	      let do_line_to_binders line =
  	        match line with
    	        | Do_line (pat, _, exp, _) ->
    	            NameSet.union (Nfmap.domain pat.rest.pvars) (exp_to_binders exp)
    	    in
    	    let bind = List.fold_right NameSet.union (List.map do_line_to_binders lines) NameSet.empty in
    	      NameSet.union bind (exp_to_binders exp)
  ;;

  let mk_lnumeral l s i org_input t = 
    let t = check_typ l "mk_lnumeral" t (fun d -> Some { t = Tapp([],Path.numeralpath) }) in
    { term = L_numeral(s,i,org_input);
      locn = l;
      typ = t;
      rest = (); }

  let mk_lnum l s i org_input t = 
    { term = L_num(s,i,org_input);
      locn = l;
      typ = t;
      rest = (); }

  let mk_lbool l s b t = 
    let t = check_typ l "mk_lbool" t (fun d -> Some { t = Tapp([],Path.boolpath) }) in
    { term = if b then L_true(s) else L_false(s);
      locn = l;
      typ = t;
      rest = (); }

  let mk_lbit l s b t =
    let t = check_typ l "mk_lbit" t (fun d -> Some { t = Tapp([],Path.bitpath) }) in
    { term = if (b=0) then L_zero(s) else L_one(s);
      locn = l;
      typ = t;
      rest = (); }

  let mk_lundef l s x t = 
    { term = L_undefined(s,x);
      locn = l;
      typ = t;
      rest = (); }

  let mk_lstring l s c t = 
    let t = check_typ l "mk_lstring" t (fun d -> Some { t = Tapp([],Path.stringpath) }) in
    { term = L_string(s,c,None);
      locn = l;
      typ = t;
      rest = (); }

  let mk_twild l s t =
    { term = Typ_wild(s);
      locn = l;
      typ = t;
      rest = (); }

  let mk_tvar l s tv t =
    { term = Typ_var(s,tv);
      locn = l;
      typ = t;
      rest = (); }

  let mk_tfn l t1 s t2 t =
    let t = check_typ l "mk_tfn" t (fun d -> Some { t = Tfn(t1.typ, t2.typ) }) in
    { term = Typ_fn(t1,s,t2);
      locn = l;
      typ = t;
      rest = (); }

  let mk_ttup l ts t =
    let t = 
      check_typ l "mk_ttup" t 
        (fun d -> Some { t = Ttup(Seplist.to_list_map (fun x -> x.typ) ts) }) 
    in
    { term = Typ_tup(ts);
      locn = l;
      typ = t;
      rest = (); }

  let mk_tapp l p ts t =
    let t =
      check_typ l "mk_tapp" t 
        (fun d -> Some { t = Tapp(List.map (fun x -> x.typ) ts, p.descr) })
    in
    { term = Typ_app(p,ts);
      locn = l;
      typ = t;
      rest = (); }

  let mk_tparen l s1 t1 s2 t =
    let t = check_typ l "mk_tparen" t (fun d -> Some t1.typ) in
    { term = Typ_paren(s1,t1,s2);
      locn = l;
      typ = t;
      rest = (); }

  let mk_var l n t : exp =
    { term = Var(n);
      locn = l;
      typ = t;
      rest =
        { free  = sing_free_env (Name.strip_lskip n) t;
          bound = NameSet.empty;
          subst = empty_sub; } }

  let mk_backend l sk i t : exp =
    { term = Backend(sk, i);
      locn = l;
      typ = t;
      rest =
        { free = empty_free_env;
          bound = NameSet.empty;
          subst = empty_sub; } }


  let mk_nvar_e l s n t : exp =
    { term = Nvar_e(s,n);
      locn = l;
      typ = t;
      rest =
        { free = empty_free_env; 
          bound = NameSet.empty;
          subst = empty_sub; }; }

  let mk_const l c t : exp =
    let new_c_ty_opt = Util.option_map (fun env -> begin
      let d = c_env_lookup l env.c_env c.descr in
      let subst = TNfmap.from_list2 d.const_tparams c.instantiation in
      let new_c_ty = type_subst subst d.const_type in
      new_c_ty
    end) D.env_opt in
    let t = 
      check_typ l "mk_const" t 
        (fun d -> new_c_ty_opt)
    in 
      { term = Constant(c);
        locn = l;
        typ = t;
        rest = { free = empty_free_env;
                 bound = NameSet.empty;
                 subst = empty_sub; }; }

  let mk_fun l s1 ps s2 e t : exp  =
    let t = 
      check_typ l "mk_fun" t (fun d -> Some (multi_fun (List.map (fun p -> p.typ) ps) e.typ))
    in
    let bound' = NameSet.union (big_union (List.map pat_to_bound_names ps)) e.rest.bound in
    let p_free = merge_free_env true l (List.map (fun p -> p.rest.pvars) ps) in
      { term = Fun(s1,ps,s2,e);
        locn = l;
        typ = t;
        rest = 
          { free = bind_free_env l p_free (exp_to_free e);
            bound = bound';
            subst = empty_sub; }; }

  let mk_function l s1 pes s2 t =
    let t = 
      check_typ l "mk_function" t
        (fun d -> 
           let (p,_,e,_) = Seplist.hd pes in
             Some { t = Tfn(p.typ,e.typ) })
    in
      let bound' =
        let pes  = Seplist.to_list pes in
        let sets = List.map (fun (pat, _, exp, _) ->
          NameSet.union (pat_to_bound_names pat) exp.rest.bound) pes
        in
          big_union sets
      in
      if check then
        Seplist.iter 
          (fun (p,_,e,_) -> type_eq l "mk_function" t { t = Tfn(p.typ,e.typ) })
          pes;
      { term = Function(s1,pes,s2);
        locn = l;
        typ = t;
        rest = 
          { free = 
              merge_free_env false l 
                (Seplist.to_list_map 
                   (fun (p,_,e,_) -> bind_free_env l p.rest.pvars (exp_to_free e)) 
                   pes);
            bound = bound';
            subst = empty_sub; }; }

  let mk_app l e1 e2 t =
    let t = 
      check_typ l "mk_app" t
        (fun d -> 
           match (head_norm d e1.typ).t with
             | Tfn(t1,t2) ->
                 type_eq l "mk_app" t1 e2.typ;
                 Some t2
             | _ -> 
                 raise (Reporting_basic.err_type l "non-function in application"))
    in
      { term = App(e1,e2);
        locn = l;
        typ = t; 
        rest = 
          { free = merge_free_env false l [exp_to_free e1;exp_to_free e2];
            bound = NameSet.union e1.rest.bound e2.rest.bound;
            subst = empty_sub; }; }

  let mk_infix l e1 e2 e3 t =
    let t' = 
      check_typ l "mk_infix" t
        (fun d -> Some (
           match (head_norm d e2.typ).t with
             | Tfn(t1,t2) ->
                 begin
                   match (head_norm d t2).t with
                     | Tfn(t3,t4) ->
                         type_eq l "mk_infix" t1 e1.typ;
                         type_eq l "mk_infix" t3 e3.typ;
                         t4
                     | _ -> 
                         raise (Reporting_basic.err_type l "non-function in infix application")
                 end
             | _ ->
                 raise (Reporting_basic.err_type l "non-function in infix application")))
    in
      match exp_to_term e2 with
        | Var _ | Constant _ -> 
            { term = Infix(e1,e2,e3);
              locn = l;
              typ = t'; 
              rest =
                { free = merge_free_env false l [exp_to_free e1; exp_to_free e2; exp_to_free e3];
                  bound = NameSet.union e1.rest.bound (NameSet.union e2.rest.bound e3.rest.bound);
                  subst = empty_sub; }; }
        | _ -> 
            mk_app l (mk_app l e2 e1 (Some({ t = Tfn(e3.typ,t') }))) e3 t


  let mk_record l s1 fes s2 t =
    let f_rec_ty_opt = Util.option_map (fun env -> begin
      let (f,_,_,_) = Seplist.hd fes in
      let d = c_env_lookup l env.c_env f.descr in
      let subst = TNfmap.from_list2 d.const_tparams f.instantiation in
      let new_f_ty = type_subst subst d.const_type in
      let (f_rec_ty, _) = Util.option_get_exn (Reporting_basic.err_general true l "not of field type")
                             (Types.dest_fn_type (Some env.t_env) new_f_ty) in
      let _ = if check then (* TODO: add typecheck code *) () in
      f_rec_ty
    end) D.env_opt in
    let t = check_typ l "mk_record" t (fun d -> f_rec_ty_opt ) in
    let bound' =
      let fes  = Seplist.to_list fes in
      let sets = List.map (fun (cdr, _, exp, _) ->
          exp.rest.bound
        ) fes
      in
        big_union sets
    in
    { term = Record(s1,fes,s2);
      locn = l;
      typ = t;
      rest = 
        { free = 
          merge_free_env false l 
            (Seplist.to_list_map (fun (_,_,e,_) -> exp_to_free e) fes);
          bound = bound';
          subst = empty_sub; }; }

  let mk_recup l s1 e s2 fes s3 t =
    let t = check_typ l "mk_recup" t (fun d -> Some e.typ) in
      if check then
        (* TODO: add typecheck code *)
        ();
      let bound' =
        let fes  = Seplist.to_list fes in
        let sets = List.map (fun (cdr, _, exp, _) ->
            exp.rest.bound
          ) fes
      in
        NameSet.union e.rest.bound (big_union sets)
    in
      { term = Recup(s1,e,s2,fes,s3);
        locn = l;
        typ = t; 
        rest = 
          { free = 
              merge_free_env false l 
                (exp_to_free e :: Seplist.to_list_map (fun (_,_,e,_) -> exp_to_free e) fes);
            bound = bound';
            subst = empty_sub; }; }

  let mk_field l e s f t =
    let f_arg_ty_opt = Util.option_map (fun env -> begin
      let d = c_env_lookup l env.c_env f.descr in
      let subst = TNfmap.from_list2 d.const_tparams f.instantiation in
      let new_f_ty = type_subst subst d.const_type in
      let (f_rec_ty, f_arg_ty) = Util.option_get_exn (Reporting_basic.err_general true l "not of field type")
                             (Types.dest_fn_type (Some env.t_env) new_f_ty) in
      let _ = type_eq l "mk_field" e.typ f_rec_ty in
      f_arg_ty
    end) D.env_opt in
    let t = check_typ l "mk_field" t (fun d -> f_arg_ty_opt)
    in
      { term = Field(e,s,f);
        locn = l;
        typ = t; 
        rest =
          { free = exp_to_free e;
            bound = e.rest.bound;
            subst = empty_sub; }; }

  let mk_vector l s1 es s2 t =
    let t =
      check_typ l "mk_vector" t 
        (fun d ->
           let len = Seplist.length es in Some
                     { t = Tapp([List.hd (Seplist.to_list_map (fun e -> e.typ) es); {t = Tne({nexp = Nconst(len)})}],
                                Path.vectorpath) })
    (* TODO KG determine if the types should be checked here to all be the same *)
    in
      {term = Vector(s1,es,s2);
       locn = l;
       typ = t;
       rest = 
          {free = merge_free_env false l (Seplist.to_list_map exp_to_free es);
           bound = big_union (List.map (fun x -> x.rest.bound) (Seplist.to_list es));
           subst = empty_sub;}; }
                        
  let mk_vectoracc l e s1 n s2 t =
    let t = 
       check_typ l "mk_vectoracc" t (fun d -> Some (
                        match e.typ.t with | Tapp( [n1;t1], _ ) -> t1 (* TODO KG Need a better check that this is a vector *)
                                           | _ -> assert false))
    in
      {term = VectorAcc(e,s1,n,s2);
       locn = l;
       typ = t;
       rest = 
         { free = exp_to_free e;
           bound = e.rest.bound;
           subst = empty_sub; }; }

  let mk_vectoraccr l e s1 n1 s2 n2 s3 t =
     (* TODO KG Add a check *)
     { term = VectorSub(e,s1,n1,s2,n2,s3);
       locn = l;
       typ = t;
       rest = 
         { free = exp_to_free e;
           bound = e.rest.bound;
           subst = empty_sub; }; }

  let mk_case c l s1 e s2 pats s3 t =
    let t = 
      check_typ l "mk_case" t
        (fun d ->
           match Seplist.hd pats with
             | (_,_,e,_) -> Some e.typ)
    in
      let bound' =
        let pats = Seplist.to_list pats in
        let sets = List.map (fun (p, _, e, _) ->
            let ps = pat_to_bound_names p in
            let es = e.rest.bound in
              NameSet.union ps es
          ) pats
        in
          big_union sets
      in
      if check then
        Seplist.iter
          (fun (p,_,e',_) ->
             type_eq l "mk_case" p.typ e.typ;
             type_eq l "mk_case" e'.typ t)
          pats;
      { term = Case(c,s1,e,s2,pats,s3);
        locn = l;
        typ = t; 
        rest =
          { free =
              merge_free_env false l 
                (exp_to_free e ::
                 (Seplist.to_list_map 
                    (fun (p,_,e,_) -> bind_free_env l p.rest.pvars (exp_to_free e)) 
                    pats));
            bound = bound';
            subst = empty_sub; }; }

  let mk_typed l s1 e s2 src_t s3 t =
    let t = check_typ l "mk_typed" t (fun d -> Some e.typ) in
      type_eq l "mk_typed" e.typ src_t.typ;
      { term = Typed(s1,e,s2,src_t,s3);
        locn = l;
        typ = t; 
        rest =
          { free = exp_to_free e;
            bound = e.rest.bound;
            subst = empty_sub; }; }

  let mk_let_val l p topt s e =
    type_eq l "mk_let_var" p.typ e.typ;
    begin
      match topt with
        | Some((_,t)) -> type_eq l "mk_let_var" p.typ t.typ
        | _ -> ()
    end;
    (Let_val(p,topt,s,e),l)

  let mk_let_fun l n ps topt s e =
    type_eq l "mk_let_fun" n.typ (multi_fun (List.map (fun p -> p.typ) ps) e.typ);
    begin
      match topt with
        | Some((_,t)) -> type_eq l "mk_let_fun" e.typ t.typ
        | _ -> ()
    end;
    (Let_fun(n,ps,topt,s,e),l)

  let mk_let l s1 lb s2 e t =
    let t = check_typ l "mk_let" t (fun d -> Some e.typ) in
    let bound' =
      let es = e.rest.bound in
      let lb =
        let (lb_aux, _) = lb in
          match lb_aux with
            | Let_val (p, _, _, e) ->
                NameSet.union (pat_to_bound_names p) e.rest.bound
            | Let_fun (_, ps, _, _, e) ->
                NameSet.union (big_union (List.map pat_to_bound_names ps)) e.rest.bound
      in
        NameSet.union (NameSet.union lb es) e.rest.bound
    in
      { term = Let(s1,lb,s2,e);
        locn = l;
        typ = t;
        rest =
          { free = 
              begin
                match lb with
                  | (Let_val(p,_,_,e'),_) ->
                      merge_free_env false l
                        [bind_free_env l p.rest.pvars (exp_to_free e); 
                         exp_to_free e']
                  | (Let_fun(n,ps,_,_,e'),_) ->
                      merge_free_env false l
                        [bind_free_env l
                           (merge_free_env true l (List.map (fun p -> p.rest.pvars) ps))
                           (exp_to_free e');
                         bind_free_env l
                           (sing_free_env (Name.strip_lskip n.term) n.typ)
                           (exp_to_free e)]
              end;
            bound = bound';
            subst = empty_sub; }; }

  let mk_tup l s1 es s2 t =
    let t = 
      check_typ l "mk_tup" t 
        (fun d -> Some { t = Ttup(Seplist.to_list_map (fun e -> e.typ) es) } )
    in
    let bound' =
      let es   = Seplist.to_list es in
      let sets = List.map (fun x -> x.rest.bound) es in
        big_union sets
    in
      { term = Tup(s1,es,s2);
        locn = l;
        typ = t; 
        rest =
          { free =
              merge_free_env false l (Seplist.to_list_map exp_to_free es);
            bound = bound';
            subst = empty_sub; }; }

  let mk_list l s1 es s2 t =
    let bound' =
      let es   = Seplist.to_list es in
      let sets = List.map (fun x -> x.rest.bound) es in
        big_union sets
    in
    if check then
      Seplist.iter 
        (fun e -> type_eq l "mk_list" { t = Tapp([e.typ], Path.listpath) } t) 
        es;
    { term = List(s1,es,s2);
      locn = l;
      typ = t;
      rest = 
        { free = merge_free_env false l (Seplist.to_list_map exp_to_free es);
          bound = bound';
          subst = empty_sub; }; }

  let mk_vector l s1 es s2 t =
    let tlen = {t = Tne({nexp = Nconst(Seplist.length es)}) } in
    let bound' =
      let es   = Seplist.to_list es in
      let sets = List.map (fun x -> x.rest.bound) es in
        big_union sets
    in
    if check then
     Seplist.iter
       (fun e -> type_eq l "mk_vector" { t = Tapp([e.typ;tlen],Path.vectorpath) } t)
       es;
    { term = Vector(s1,es,s2);
      locn = l;
      typ = t;
      rest = 
        { free = merge_free_env false l (Seplist.to_list_map exp_to_free es);
          bound = bound';
          subst = empty_sub; }; }

   let mk_vaccess l e s1 n s2 t = 
     (* TODO KG Add type here, need a means of calling nexp_within or some such here *)
     { term = VectorAcc(e,s1,n,s2);
       locn = l;
       typ = t;
       rest =
        { free = exp_to_free e;
          bound = e.rest.bound;
          subst = empty_sub; }; }       

  let mk_vaccessr l e s1 n1 s2 n2 s3 t =
     (* TODO KG add check here, see above *)
     { term = VectorSub(e,s1,n1,s2,n2,s3);
       locn = l;
       typ = t;
       rest = 
         { free = exp_to_free e;
           bound = e.rest.bound;
           subst = empty_sub } }

  let mk_paren l s1 e s2 t =
    let t = check_typ l "mk_paren" t (fun d -> Some e.typ) in
      { term = Paren(s1,e,s2);
        locn = l;
        typ = t; 
        rest = 
          { free = exp_to_free e;
            bound = e.rest.bound; 
            subst = empty_sub; }; }

  let mk_begin l s1 e s2 t =
    let t = check_typ l "mk_begin" t (fun d -> Some e.typ) in
      { term = Begin(s1,e,s2);
        locn = l;
        typ = t;
        rest = 
          { free = exp_to_free e;
            bound = e.rest.bound;
            subst = empty_sub; }; }

  let mk_if l s1 e1 s2 e2 s3 e3 t =
    let t = check_typ l "mk_if" t (fun d -> Some e3.typ) in
      type_eq l "mk_if" e1.typ { t = Tapp([], Path.boolpath) };
      type_eq l "mk_if" e2.typ e3.typ;
      { term = If(s1,e1,s2,e2,s3,e3);
        locn = l;
        typ = t; 
        rest =
          { free = merge_free_env false l 
                     [exp_to_free e1; exp_to_free e2; exp_to_free e3];
            bound = NameSet.union (NameSet.union e1.rest.bound e2.rest.bound) e3.rest.bound;
            subst = empty_sub; }; }

  let mk_lit l li t =
    let t = check_typ l "mk_lit" t (fun d -> Some li.typ) in
      { term = Lit(li);
        locn = l;
        typ = t; 
        rest =
          { free = empty_free_env;
            bound = NameSet.empty;
            subst = empty_sub; }; }

  let mk_set l s1 es s2 t =
    let bound' =
      let es   = Seplist.to_list es in
      let sets = List.map (fun x -> x.rest.bound) es in
        big_union sets
    in
    if check then
      Seplist.iter 
        (fun e -> type_eq l "mk_set" { t = Tapp([e.typ], Path.setpath) } t) 
        es;
    { term = Set(s1,es,s2);
      locn = l;
      typ = t;
      rest =
        { free = merge_free_env false l (Seplist.to_list_map exp_to_free es);
          bound = bound';
          subst = empty_sub; }; }

  let mk_setcomp l s1 e1 s2 e2 s3 ns t =
    let t = check_typ l "mk_setcomp" t (fun d -> Some { t = Tapp([e1.typ], Path.setpath) }) in
    let env = merge_free_env false l [exp_to_free e1; exp_to_free e2] in
      type_eq l "mk_setcomp" e2.typ { t = Tapp([], Path.boolpath) };
      { term = Setcomp(s1,e1,s2,e2,s3,ns);
        locn = l;
        typ = t;
        rest = 
          { free = NameSet.fold (fun k e -> Nfmap.remove e k) ns env;
            bound = NameSet.union (NameSet.union e1.rest.bound e2.rest.bound) ns;
            subst = empty_sub; }; }

  let pp_fvs = Nfmap.pp_map Name.pp Types.pp_type

  (* Compute the free variables for an expression with a binding structure of
   * pattern/expression pairs followed by an expression, where each pattern
   * binds in subsequent expressions and in the final expression *)
  let pat_exp_list_freevars l allow_duplicates (pes : (pat * exp option) list) exp =
    let (bindings,frees) =
      List.fold_left
        (fun (bindings,frees) (p,e) ->
           let new_bindings =
             Nfmap.merge 
               (fun k v1 v2 ->
                  match (v1,v2) with
                    | (None,_) -> v2
                    | (_,None) -> v1
                    | (Some(v),Some(v')) ->
                        if allow_duplicates then
                          Some(v')
                        else
                          raise (Reporting_basic.err_type l ("Duplicate variable in a pattern: " ^
                                                   Pp.pp_to_string (fun ppf -> Name.pp ppf k))))
               bindings
               p.rest.pvars
           in
             match e with
               | None ->
                   (new_bindings, frees)
               | Some(e) ->
                   (new_bindings, merge_free_env false l [frees; bind_free_env l bindings (exp_to_free e)]))
        (Nfmap.empty, Nfmap.empty)
        pes
    in
      merge_free_env false l [frees; bind_free_env l bindings (exp_to_free exp)]

  let check_qbs l = function
    | Qb_var(n) -> ()
    | Qb_restr(is_lst,s1,p,s2,e,s3) ->
        type_eq l "check_qbs" e.typ 
          { t = Tapp([p.typ], if is_lst then Path.listpath else Path.setpath) }

  let qbs_bindings l qbs = 
    merge_free_env true l
      (List.map
         (function
            | Qb_var(n) -> 
                sing_free_env (Name.strip_lskip n.term) n.typ
            | Qb_restr(_,_,p,_,_,_) ->
                p.rest.pvars)
         qbs)

  let qbs_envs l qbs =
    List.map 
      (function
         | Qb_var(n) -> empty_free_env
         | Qb_restr(_,_,_,_,e,_) -> exp_to_free e)
      qbs

  let mk_comp_binding l is_lst s1 e1 s2 s3 qbs s4 e2 s5 t =
    let bound' =
      let qbs = List.map (fun q ->
        match q with
          | Qb_var name_lskips ->
              let name_lskips = name_lskips.term in
                NameSet.add (Name.strip_lskip name_lskips) NameSet.empty
          | Qb_restr (_, _, pat, _, exp, _) ->
              NameSet.union (pat_to_bound_names pat) exp.rest.bound
        ) qbs
      in
        NameSet.union (NameSet.union e1.rest.bound e2.rest.bound) (big_union qbs)
    in
    let t = 
      check_typ l "mk_comp_binding" t
        (fun d ->  Some
           { t = Tapp([e1.typ], if is_lst then Path.listpath else Path.setpath) })
    in
      type_eq l "mk_comp_binding" e2.typ { t = Tapp([], Path.boolpath) };
      if check then
        List.iter (check_qbs l) qbs;
      if check && is_lst then
        List.iter (function | Qb_var _ -> assert false | _ -> ()) qbs;
      { term = Comp_binding(is_lst,s1,e1,s2,s3,qbs,s4,e2,s5);
        locn = l;
        typ = t; 
        rest =
          { free = 
              (* TODO: Check that we're returning the right free variables, and
               * consider using pat_exp_list_freevars *)
              merge_free_env false l
                (bind_free_env l
                   (qbs_bindings l qbs) 
                   (merge_free_env false l [exp_to_free e1; exp_to_free e2]) ::
                 qbs_envs l qbs);
            bound = bound';
            subst = empty_sub; }; }

  let mk_quant l q qbs s e t =
    let bound' =
      let qbs = List.map (fun q ->
        match q with
          | Qb_var name_lskips ->
              let name_lskips = name_lskips.term in
                NameSet.add (Name.strip_lskip name_lskips) NameSet.empty
          | Qb_restr (_, _, pat, _, exp, _) ->
              NameSet.union (pat_to_bound_names pat) exp.rest.bound) qbs
      in
        NameSet.union e.rest.bound (big_union qbs)
    in
    let t = check_typ l "mk_quant" t (fun d -> Some e.typ) in
      List.iter (check_qbs l) qbs;
      type_eq l "mk_quant" e.typ { t = Tapp([],Path.boolpath) };
      { term = Quant(q,qbs,s,e);
        locn = l;
        typ = t; 
        rest =
          { free = 
              merge_free_env false l
                (bind_free_env l (qbs_bindings l qbs) (exp_to_free e) ::
                 qbs_envs l qbs);
            bound = bound';
            subst = empty_sub; }; }

  let do_lns_bindings l do_lns = 
    merge_free_env false l
      (List.map (function | Do_line(p,_,_,_) -> p.rest.pvars) do_lns)

  let do_lns_envs l do_lns =
    List.map (function | Do_line(_,_,e,_) -> exp_to_free e) do_lns

  let mk_do l s1 mid do_lns s2 e s3 ret_t t =
    let bound' =
      let do_lns = List.map (fun d ->
          match d with
            | Do_line (p, _, e, _) ->
                NameSet.union (pat_to_bound_names p) e.rest.bound
        ) do_lns
      in
        NameSet.union e.rest.bound (big_union do_lns)
    in
    (* TODO: actually do the check *)
    let t = check_typ l "mk_do" t (fun d -> Some e.typ ) in
      { term = Do(s1,mid,do_lns,s2,e,s3,ret_t);
        locn = l;
        typ = t;
        rest =
          { free = pat_exp_list_freevars l true 
                     (List.map (function | Do_line(p,_,e,_) -> (p,Some e)) do_lns)
                     e;
            bound = bound';
            subst = empty_sub }}


  type src_t_context = 
    | TC_app
    | TC_tup
    | TC_fn_left
    | TC_fn_right

  let delimit_typ ctxt t = 
    match t.term with
      | Typ_wild _ | Typ_var _ | Typ_paren _ | Typ_len _ -> t (*TODO Check that parens aren't needed *)
      | Typ_fn _ ->
          if ctxt = TC_fn_right then
            t
          else 
            mk_tparen Ast.Unknown None t None (Some(t.typ))
      | Typ_tup _ ->
          if ctxt = TC_app || ctxt = TC_tup then
            mk_tparen Ast.Unknown None t None (Some(t.typ))
          else
            t
      | (Typ_app _ | Typ_backend _) ->
          if ctxt = TC_app then
            mk_tparen Ast.Unknown None t None (Some(t.typ))
          else 
            t

  (* To print internal types, we define functions to convert internal types to
   * src types *)

  (* TODO KG figure out the delimit part of this and add Tlen *)
  let rec t_to_src_t (texp : Types.t) : src_t =
    match texp.t with
      | Tvar(n) -> 
          mk_tvar Ast.Unknown None n texp
      | Tfn(te1,te2) -> 
          mk_tfn Ast.Unknown 
            (delimit_typ TC_fn_left (t_to_src_t te1))
            space 
            (delimit_typ TC_fn_right (t_to_src_t te2))
            (Some(texp))
      | Ttup(tys) -> 
          let ts = 
            Seplist.from_list 
              (List.map (fun x -> (delimit_typ TC_tup (t_to_src_t x), None)) tys)
          in
            mk_ttup Ast.Unknown ts (Some(texp))
      | Tapp(tys,p) -> 
          let pid = 
            { id_path = Id_none None;
              id_locn = Ast.Unknown; 
              descr = p; 
              instantiation = [] } 
          in
          let ts = 
            List.map (fun x -> delimit_typ TC_app (t_to_src_t x)) tys
          in
            mk_tapp Ast.Unknown pid ts (Some(texp))
      | _ -> mk_twild Ast.Unknown None texp

end

let local_env_union e1 e2 =
  { m_env = Nfmap.union e1.m_env e2.m_env;
    p_env = Nfmap.union e1.p_env e2.p_env;
    v_env = Nfmap.union e1.v_env e2.v_env; 
    f_env = Nfmap.union e1.f_env e2.f_env; }


let funcl_aux_seplist_group (sl : funcl_aux lskips_seplist) = begin
  let (first_s, pL) = Seplist.to_pair_list None sl in
  let add_fun_name ((((nsa, _, _, _, _, _) : funcl_aux), _) as x) =
    let n = Name.strip_lskip (nsa.term) in (n, x) in
  let npL = List.map add_fun_name pL in
  let np_comp (n1, _) (n2, _) = Name.compare n1 n2 in
  let rec is_sorted l = match l with [] -> true | [x] -> true | x1 :: x2 :: xs -> (np_comp x1 x2 <= 0) && is_sorted (x2 :: xs) in
  let (was_resorted, snpL) = let ok = is_sorted npL in if ok then (false, npL) else (true, List.stable_sort np_comp npL) in

  let grouped = begin
    let rec aux acc l = match (acc, l) with
      | (_, []) -> List.rev (List.map (fun (n, l) -> (n, Seplist.from_list (List.rev l))) acc)
      | ([], (n, x) :: l') -> aux [(n, [x])] l'
      | (((cn, xs) :: acc'), (n, x) :: l') ->
          if (Name.compare cn n = 0) then
            aux ((cn, x::xs) :: acc') l'
          else 
            aux ((n, [x]) :: (cn, xs) :: acc') l'
    in aux [] snpL
  end in
  (was_resorted, first_s, grouped)
end
  
let class_path_to_dict_name c tv =
  let (pnames,n) = Path.to_name_list c in
    Name.from_rope (Ulib.Text.concat (r"_") 
                     (r"dict" ::
                       (* TODO KG & SO Should the tv distinguish ty vs nv *)
                       (List.map Name.to_rope pnames @ [Name.to_rope n; Types.tnvar_to_rope tv])))

let ident_get_lskip id =
  match id.id_path with
    | Id_none sk -> sk
    | Id_some i -> Ident.get_lskip i

let ident_replace_lskip id sk =
  match id with
    | Id_none _ -> Id_none sk
    | Id_some i -> Id_some (Ident.replace_lskip i sk)

let oi_get_lskip oi =
  let (_, sk) = oi_alter_init_lskips (fun sk -> (sk, sk)) oi in
  sk
