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
module P = Precedence
module NameSet = Set.Make(Name)
module Nfmap = Finite_map.Fmap_map(Name)
type name_l = Name.lskips_t * Ast.l
type lskips = Ast.lex_skips

let nfmap_domain (m : 'a Nfmap.t) :NameSet.t = Nfmap.domain m
let r = Ulib.Text.of_latin1

let no_lskips = None
let space = Some([Ast.Ws(r" ")])

let lskips_only_comments coms = 
  match List.fold_right Ast.combine_lex_skips coms None with
    | None -> space
    | Some(l) ->
        Some(List.filter (function | Ast.Com _ -> true | _ -> false) l @[Ast.Ws(r" ")])

type 'a lskips_seplist = ('a, lskips) Seplist.t

let ast_target_compare x y = match (x,y) with
  | (Ast.Target_hol _, Ast.Target_hol _) -> 0
  | (Ast.Target_hol _, _) -> 1
  | (_, Ast.Target_hol _) -> -1
  | (Ast.Target_ocaml _, Ast.Target_ocaml _) -> 0
  | (Ast.Target_ocaml _, _) -> 1
  | (_, Ast.Target_ocaml _) -> -1
  | (Ast.Target_isa _, Ast.Target_isa _) -> 0
  | (Ast.Target_isa _, _) -> 1
  | (_, Ast.Target_isa _) -> -1 
  | (Ast.Target_coq _, Ast.Target_coq _) -> 0
  | (Ast.Target_coq _, _) -> 1
  | (_, Ast.Target_coq _) -> -1 
  | (Ast.Target_tex _, Ast.Target_tex _) -> 0
  | (Ast.Target_tex _, _) -> 1
  | (_, Ast.Target_tex _) -> -1 
  | (Ast.Target_html _, Ast.Target_html _) -> 0

type target = 
  | Target_hol
  | Target_ocaml
  | Target_isa
  | Target_coq
  | Target_tex
  | Target_html

let ast_target_to_target t = match t with
  | Ast.Target_hol   _ -> Target_hol 
  | Ast.Target_ocaml _ -> Target_ocaml 
  | Ast.Target_isa   _ -> Target_isa
  | Ast.Target_coq   _ -> Target_coq
  | Ast.Target_tex   _ -> Target_tex
  | Ast.Target_html  _ -> Target_html

let target_to_ast_target t = match t with
  | Target_hol   -> Ast.Target_hol None
  | Target_ocaml -> Ast.Target_ocaml None
  | Target_isa   -> Ast.Target_isa None
  | Target_coq   -> Ast.Target_coq None
  | Target_tex   -> Ast.Target_tex None
  | Target_html  -> Ast.Target_html None

let target_compare = Pervasives.compare

module Targetmap = Finite_map.Fmap_map(
struct 
  type t = target
  let compare = target_compare
end)

module Targetset = Set.Make(
struct 
  type t = target
  let compare = target_compare
end)

let all_targets = 
  List.fold_right Targetset.add 
    [Target_hol; Target_ocaml; Target_isa; Target_coq; Target_tex; Target_html] 
    Targetset.empty

let target_to_string = function
  | Target_hol -> "hol"
  | Target_ocaml -> "ocaml"
  | Target_isa -> "isabelle"
  | Target_coq -> "coq"
  | Target_tex -> "tex"
  | Target_html -> "html"

let target_opt_to_string = function
  | None -> "ident"
  | Some t -> target_to_string t

let target_to_output a t = 
  let open Output in
    match t with
      | Ast.Target_hol(s) -> ws s ^ id a (r"hol")
      | Ast.Target_ocaml(s) -> ws s ^ id a (r"ocaml")
      | Ast.Target_isa(s) -> ws s ^ id a (r"isabelle")
      | Ast.Target_coq(s) -> ws s ^ id a (r"coq")
      | Ast.Target_tex(s) -> ws s ^ id a (r"tex")
      | Ast.Target_html(s) -> ws s ^ id a (r"html")

let target_to_mname = function
  | Target_hol -> Name.from_rope (r"Hol")
  | Target_ocaml -> Name.from_rope (r"Ocaml")
  | Target_isa -> Name.from_rope (r"Isabelle")
  | Target_coq -> Name.from_rope (r"Coq")
  | Target_tex -> Name.from_rope (r"Tex")
  | Target_html -> Name.from_rope (r"Html")


type env_tag = 
  | K_method
  | K_instance
  | K_val
  | K_let
  | K_target of bool * Targetset.t

type ('a,'b) annot = { term : 'a; locn : Ast.l; typ : t; rest : 'b }

let annot_to_typ a = a.typ

type constr_descr = { constr_binding : Path.t; 
                      constr_tparams : Types.tnvar list; 
                      constr_args : t list; 
                      constr_tconstr : Path.t;
                      constr_names : NameSet.t; 
                      constr_l : Ast.l;}

type field_descr = { field_binding : Path.t;
                     field_tparams : Types.tnvar list;
                     field_tconstr : Path.t;
                     field_arg : t;
                     field_names : Name.t list; 
                     field_l : Ast.l; }

type p_env = (Path.t * Ast.l) Nfmap.t

type ident_option =
  | Id_none of Ast.lex_skips
  | Id_some of Ident.t

type 'a id = { id_path : ident_option;
               id_locn : Ast.l;
               descr : 'a; 
               instantiation : t list; }

and src_t = (src_t_aux,unit) annot

and src_t_aux = 
 | Typ_wild of lskips
 | Typ_var of lskips * Tyvar.t
 | Typ_len of src_nexp
 | Typ_fn of src_t * lskips * src_t
 | Typ_tup of src_t lskips_seplist
 | Typ_app of Path.t id * src_t list
 | Typ_paren of lskips * src_t * lskips

and src_nexp = { nterm : src_nexp_aux; nloc : Ast.l; nt : Types.nexp } (*(src_nexp_aux,unit) annot*)

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
  | L_zero of lskips
  | L_one of lskips
  | L_num of lskips * int
  | L_string of lskips * string
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
  | P_var_annot of Name.lskips_t * src_t


and const_descr = { const_binding : Path.t;
                    const_tparams : Types.tnvar list;
                    const_class : (Path.t * Types.tnvar) list;
                    const_ranges : Types.range list;
                    const_type : t; 
                    env_tag : env_tag;
                    spec_l : Ast.l;
                    substitutions : ((Name.t,unit) annot list * exp) Targetmap.t }

and val_descr = 
  | Constr of constr_descr
  | Val of const_descr

and v_env = val_descr Nfmap.t
and f_env = field_descr Nfmap.t
and m_env = mod_descr Nfmap.t
and r_info = {
  rel_witness : (Path.t * constr_descr Nfmap.t) option;
  rel_check : Path.t option;
}
and r_env = r_info Nfmap.t
and env = { m_env : m_env; p_env : p_env; f_env : f_env; v_env : v_env;
            r_env : r_env }

(* free_env represents the free variables in expression, with their types *)
and free_env = t Nfmap.t

and mod_descr = { mod_binding : Path.t;
                  mod_env : env; }

and exp = (exp_aux,exp_annot) annot
(* We keep typ with the subst applied, and term and free without, we also only
* keep subst bindings (for the exp subst) that are free in the unapplied free
* map *)
and exp_annot = 
  { free : free_env; 
    subst : t TNfmap.t * exp_subst Nfmap.t; }
and exp_subst = 
  | Sub of exp
  | Sub_rename of Name.t

and exp_aux =
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
  | Do of lskips * mod_descr id * do_line list * lskips * exp * lskips * (Types.t * int)

and do_line = Do_line of (pat * lskips * exp * lskips)

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

type range = 
  | GtEq of Ast.l * src_nexp * lskips * src_nexp
  | Eq of Ast.l * src_nexp * lskips * src_nexp

type constraints = 
  | Cs_list of (Ident.t * tnvar) lskips_seplist * lskips option * range lskips_seplist * lskips

type constraint_prefix =
  | Cp_forall of lskips * tnvar list * lskips * constraints option

type rename_tag = | RT_field | RT_constr | RT_fun | RT_type

type typschm = constraint_prefix option * src_t

type instschm = constraint_prefix option * lskips * Ident.t * src_t * lskips

type val_spec = lskips * name_l * lskips * typschm

type class_val_spec = lskips * name_l * lskips * src_t

type targets_opt = (lskips * Ast.target lskips_seplist * lskips) option

let in_targets_opt t_opt targets_opt = match t_opt with
    None   -> true
  | Some t -> (match targets_opt with 
                 None -> true
               | Some (_, targets, _) -> Seplist.exists (fun t' -> ast_target_compare t t' = 0) targets)

type val_def = 
  | Let_def of lskips * targets_opt * letbind
  | Rec_def of lskips * lskips * targets_opt * funcl_aux lskips_seplist
  | Let_inline of lskips * lskips * targets_opt * name_lskips_annot * name_lskips_annot list * lskips * exp

type inst_sem_info =
  { inst_env : v_env;
    inst_name : Name.t;
    inst_class : Path.t;
    inst_tyvars : Types.tnvar list;
    inst_constraints : (Path.t * Types.tnvar) list;
    inst_methods : (Name.t * Types.t) list; }

type name_sect = Name_restrict of (lskips * name_l * lskips * lskips * string * lskips)

type def = (def_aux * lskips option) * Ast.l

and def_aux =
  | Type_def of lskips * (name_l * tnvar list * texp * name_sect option) lskips_seplist
  | Val_def of val_def * TNset.t * (Path.t * Types.tnvar) list 
  | Lemma of lskips * Ast.lemma_typ * targets_opt * (name_l * lskips) option * lskips * exp * lskips
  | Ident_rename of lskips * targets_opt * Path.t * Ident.t * lskips * name_l
  | Module of lskips * name_l * lskips * lskips * def list * lskips
  | Rename of lskips * name_l * lskips * mod_descr id
  | Open of lskips * mod_descr id
  | Indreln of lskips * targets_opt * 
               (Name.lskips_t option * lskips * name_lskips_annot list * lskips * exp option * lskips * name_lskips_annot * exp list) lskips_seplist
  | Val_spec of val_spec
  | Class of lskips * lskips * name_l * tnvar * lskips * class_val_spec list * lskips
  (* The v_env, name and Path/tyvar list are for converting the instance into a module. *)
  | Instance of lskips * instschm * val_def list * lskips * inst_sem_info
  | Comment of def

let tnvar_to_types_tnvar tnvar = 
  match tnvar with
    | Tn_A(sk, tv, l) -> (Ty(Tyvar.from_rope tv),l)
    | Tn_N(sk, nv, l) -> (Nv(Nvar.from_rope nv),l)

let empty_env = { m_env = Nfmap.empty;
                  p_env = Nfmap.empty;
                  f_env = Nfmap.empty;
                  r_env = Nfmap.empty;
                  v_env = Nfmap.empty; }

(* Applies lskips_f to the leftmost lskips in p, replacing it with lskips_f's
 * first result and returning lskips_f's second result *)

let rec nexp_alter_init_lskips(lskips_f : lskips -> lskips * lskips) (n: src_nexp) : src_nexp * lskips =
  let res n' s = ({ n with nterm = n'}, s) in
    match n.nterm with
      | Nexp_var(s, nv) ->
          let (s_new,s_ret) = lskips_f s in
            res (Nexp_var(s_new,nv)) s_ret
      | Nexp_const(s, i) ->
          let (s_new,s_ret) = lskips_f s in
            res (Nexp_const(s_new,i)) s_ret
      | Nexp_mult(n1, s, n2) ->
          let (n1_new,s_ret) = nexp_alter_init_lskips lskips_f n1 in
            res (Nexp_mult(n1_new,s,n2)) s_ret
      | Nexp_add(n1, s, n2) ->
          let (n1_new,s_ret) = nexp_alter_init_lskips lskips_f n1 in
            res (Nexp_add(n1_new,s,n2)) s_ret
      | Nexp_paren(s1, n, s2) ->
         let (s_new,s_ret) = lskips_f s1 in
            res (Nexp_paren(s_new,n,s2)) s_ret

let id_alter_init_lskips lskips_f (id : 'a id) : 'a id * lskips =
  match id.id_path with
    | Id_some(id_path) ->
        let (s_new, s_ret) = lskips_f (Ident.get_first_lskip id_path) in
          ({id with id_path = Id_some (Ident.replace_first_lskip id_path s_new)}, s_ret)
    | Id_none(sk) ->
        let (s_new, s_ret) = lskips_f sk in
          ({id with id_path = Id_none s_new}, s_ret)

let rec typ_alter_init_lskips (lskips_f : lskips -> lskips * lskips) (t : src_t) : src_t * lskips = 
  let res t' s = ({ t with term = t'}, s) in
    match t.term with
      | Typ_wild(s) ->
          let (s_new,s_ret) = lskips_f s in
            res (Typ_wild(s_new)) s_ret
      | Typ_var(s,tv) ->
          let (s_new,s_ret) = lskips_f s in
            res (Typ_var(s_new,tv)) s_ret
      | Typ_len(nexp) -> 
          let (nexp_new,s_ret) = nexp_alter_init_lskips lskips_f nexp in
             res (Typ_len(nexp_new)) s_ret
      | Typ_fn(t1,s,t2) ->
          let (t_new, s_ret) = typ_alter_init_lskips lskips_f t1 in
            res (Typ_fn(t_new, s, t2)) s_ret
      | Typ_tup(ts) ->
          let t = Seplist.hd ts in
          let ts' = Seplist.tl ts in
          let (t_new, s_ret) = typ_alter_init_lskips lskips_f t in
            res (Typ_tup(Seplist.cons_entry t_new ts')) s_ret
      | Typ_app(id,ts) ->
          let (id_new,s_ret) = id_alter_init_lskips lskips_f id in
            res (Typ_app(id_new,ts)) s_ret 
      | Typ_paren(s1,t,s2) ->
          let (s_new,s_ret) = lskips_f s1 in
            res (Typ_paren(s_new,t,s2)) s_ret

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
      | L_num(s,n) ->
          let (s_new,s_ret) = lskips_f s in
            res (L_num(s_new,n)) s_ret
      | L_string(s,n) ->
          let (s_new,s_ret) = lskips_f s in
            res (L_string(s_new,n)) s_ret
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
      | P_constr(c,ps) -> 
          let (id_new, s_ret) = id_alter_init_lskips lskips_f c in
            res (P_constr(c,ps)) s_ret
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
      | Nvar_e(s,n) ->
          let (s_new, s_ret) = lskips_f s in
            res (Nvar_e(s_new,n)) s_ret 
      | Constant(c) ->
          let (id_new, s_ret) = id_alter_init_lskips lskips_f c in
            res (Constant(c)) s_ret
      | Constructor(c) ->
          let (id_new, s_ret) = id_alter_init_lskips lskips_f c in
            res (Constructor(id_new)) s_ret
      | Tup_constructor(c,s1,es,s2) -> 
          let (s_new, s_ret) = id_alter_init_lskips lskips_f c in
            res (Tup_constructor(c,s1,es,s2)) s_ret
      | Fun(s1,ps,s2,e) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Fun(s_new,ps,s2,e)) s_ret
      | Function(s1,pes,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Function(s_new, pes,s2)) s_ret
      | App(e1,e2) ->
          let (e_new, s_ret) = alter_init_lskips lskips_f e1 in
            res (App(e_new, e2)) s_ret
      | Infix(e1,e2,e3) ->
          let (e_new, s_ret) = alter_init_lskips lskips_f e1 in
            res (Infix(e_new, e2, e3)) s_ret
      | Record(s1,fieldexps,s2) ->
          let (s_new, s_ret) = lskips_f s1 in
            res (Record(s_new, fieldexps,s2)) s_ret
      | Record_coq((n,l),s1,fieldexps,s2) ->
          let (s_new, s_ret) = lskips_f (Name.get_lskip n) in
            res (Record_coq((Name.replace_lskip n s_new, l),s1,fieldexps,s2)) s_ret
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

let rec def_alter_init_lskips (lskips_f : lskips -> lskips * lskips) (((d,s),l) : def) : def * lskips = 
  let res x y = (((x,s),l),y) in
    match d with
      | Type_def(sk, tds) ->
          let (s_new, s_ret) = lskips_f sk in
            res (Type_def(s_new,tds)) s_ret
      | Val_def(Let_def(sk, topt, lb),tnvs, class_constraints) -> 
          let (s_new, s_ret) = lskips_f sk in
            res (Val_def(Let_def(s_new,topt,lb),tnvs, class_constraints)) s_ret
      | Val_def(Rec_def(sk1, sk2, topt, funs),tnvs, class_constraints) -> 
          let (s_new, s_ret) = lskips_f sk1 in
            res (Val_def(Rec_def(s_new, sk2, topt, funs),tnvs, class_constraints)) s_ret
      | Val_def(Let_inline(sk1,sk2,targ,n,ns,sk4,e), tnvs, class_constraints) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Val_def(Let_inline(s_new,sk2,targ,n,ns,sk4,e), tnvs, class_constraints)) s_ret
      | Lemma(sk1, lty, targ, n_opt, sk2, e, sk3) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Lemma(s_new, lty, targ, n_opt,sk2, e, sk3)) s_ret
      | Module(sk1, n, sk2, sk3, ds, sk4) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Module(s_new, n, sk2, sk3, ds, sk4)) s_ret
      | Rename(sk1, n, sk2, m) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Rename(s_new, n, sk2, m)) s_ret
      | Ident_rename (sk1,topt,p,i,sk2,nl) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Ident_rename (s_new,topt,p,i,sk2,nl)) s_ret
      | Open(sk,m) ->
          let (s_new, s_ret) = lskips_f sk in
            res (Open(s_new,m)) s_ret
      | Indreln(sk,topt,rules) ->
          let (s_new, s_ret) = lskips_f sk in
            res (Indreln(s_new,topt,rules)) s_ret
      | Val_spec(sk1,n,sk2,ts) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Val_spec(s_new,n,sk2,ts)) s_ret
      | Class(sk1,sk2,n,tvar,sk3,body,sk4) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Class(s_new,sk2,n,tvar,sk3,body,sk4)) s_ret
      | Instance(sk1,is,ds,sk2,sem_info) ->
          let (s_new, s_ret) = lskips_f sk1 in
            res (Instance(s_new,is,ds,sk2,sem_info)) s_ret
      | Comment(d) ->
          let (d',s_ret) = def_alter_init_lskips lskips_f d in
            res (Comment(d')) s_ret

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

let pp_constr_descr ppf c =
  fprintf ppf "@[<2>forall@ (@[%a@]).@ %a@]"
    (lst ",@," TNvar.pp) c.constr_tparams
    pp_type (multi_fun 
               c.constr_args 
               { t = Tapp(List.map
                          (fun tv -> match tv with | Ty(tv) -> { t = Tvar(tv) }
                                                   | Nv(nv) -> { t = Tne( {nexp = Nvar(nv)}) }) 
                          c.constr_tparams, 
                          c.constr_tconstr) })

let unsat_constraint_err l = function
  | [] -> ()
  | cs ->
      let t1 = 
        Pp.pp_to_string 
          (fun ppf -> 
             (Pp.lst "@\nand@\n" pp_class_constraint) ppf cs)
      in
        raise (Ident.No_type(l, "unsatisfied type class constraints:\n" ^ t1))

let pp_env_tag ppf tag = 
  match tag with
    | K_method -> Format.fprintf ppf "method"
    | K_instance -> Format.fprintf ppf "instance"
    | K_val -> Format.fprintf ppf "val"
    | K_let -> Format.fprintf ppf "let"
    | K_target(exists_general, targets) -> 
        Format.fprintf ppf "target(%b,%s)"
        exists_general "???"

let pp_const_descr ppf c =
  fprintf ppf "@[<2>forall@ (@[%a@]).@ @[%a@]@ @[%a@]@ =>@ %a@]@ (%a)@ %a"
    (lst ",@," TNvar.pp) c.const_tparams
    (lst "@ " pp_class_constraint) c.const_class
    (lst "@ " pp_range) c.const_ranges
    pp_type c.const_type
    Path.pp c.const_binding
    pp_env_tag c.env_tag

let pp_field_descr ppf f =
  fprintf ppf "@[<2>forall@ (@[%a@]).@ %a@]"
    (lst ",@," TNvar.pp) f.field_tparams
    pp_type ({t = Tfn({ t = Tapp(List.map 
                                 (fun tv -> match tv with | Ty(tv) -> { t = Tvar(tv) }
                                                          | Nv(nv) -> { t = Tne( {nexp = Nvar(nv)}) }) 
                                 f.field_tparams, f.field_tconstr) },
                      f.field_arg) })
let pp_val_descr ppf = function
  | Constr(c) -> pp_constr_descr ppf c
  | Val(c) -> pp_const_descr ppf c

let rec pp_env ppf env =
  pp_open_box ppf 0;
  let empty_m = Nfmap.is_empty env.m_env in
  let empty_v = Nfmap.is_empty env.v_env in
  let empty_p = Nfmap.is_empty env.p_env in
  let empty_f = Nfmap.is_empty env.f_env in
    (Nfmap.pp_map Name.pp pp_mod_descr) ppf env.m_env;
    if not empty_m && not empty_v then
      fprintf ppf "@\n";
    (Nfmap.pp_map Name.pp pp_val_descr) ppf env.v_env;
    if not empty_v && not empty_p then
      fprintf ppf "@\n";
    (Nfmap.pp_map Name.pp (fun ppf (p, _) -> Path.pp ppf p)) ppf env.p_env;
    if not empty_p && not empty_f then
      fprintf ppf "@\n";
    (Nfmap.pp_map Name.pp pp_field_descr) ppf env.f_env;
    pp_close_box ppf ()
and pp_mod_descr ppf md = 
  pp_env ppf md.mod_env

let pp_instances = Pfmap.pp_map Path.pp (lst "@\n" pp_instance)

type checked_module =
    { filename : string;
      module_name : string;
      predecessor_modules : string list;
      untyped_ast : Ast.defs * Ast.lex_skips;
      typed_ast : def list * Ast.lex_skips; }

type var_avoid_f = bool * (Name.t -> bool) * (Ulib.Text.t -> (Name.t -> bool) -> Name.t)

module type Exp_context = sig
  val check : type_defs option
  val avoid : var_avoid_f option
end

module Exps_in_context(D : Exp_context) = struct
  
  let check = D.check <> None

  let empty_free_env = Nfmap.empty

  let sing_free_env k v = Nfmap.from_list [(k,v)]

  let type_eq l m t1 t2 =
    match D.check with
      | None -> ()
      | Some(d) ->
          assert_equal l m d t1 t2

  let check_typ l (m : string) (t_given : t option) (t_built : type_defs -> t) : t =
    match (t_given,D.check) with
      | (None,None) -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_type (l, "check_typ case (None, None) " ^ m)))
      | (Some(t),None) -> t
      | (None,Some(d)) -> t_built d 
      | (Some(t),Some(d)) -> 
          assert_equal l m d t (t_built d);
          t

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
                      raise (Ident.No_type(l, "Duplicate variable in a pattern: " ^
                                        Pp.pp_to_string (fun ppf -> Name.pp ppf k)))
                    else
                      begin
                        try
                          type_eq l "merge_free_env" v v'
                        with
                          | Ident.No_type(l,s) ->
                              raise (Ident.No_type(l,s ^ "\n in merging: " ^ Pp.pp_to_string (fun ppf -> Name.pp ppf k)))
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
                   | Ident.No_type(l,s) ->
                       raise (Ident.No_type(l,s ^ "\nin binding " ^ Pp.pp_to_string (fun ppf -> Name.pp ppf k)))
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
    let t = check_typ l "mk_pas" t (fun d -> p.typ) in
      { term = P_as(s1,p,s2,nl,s3);
        locn = l;
        typ = t;
        rest = 
          { pvars = 
              merge_free_env true l
                [sing_free_env (Name.strip_lskip (fst nl)) t; 
                 p.rest.pvars]; }; }

  let mk_ptyp l s1 p s2 t1 s3 t =
    let t = check_typ l "mk_ptyp" t (fun d -> p.typ) in
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

  let mk_pconstr l c ps t =
    let t = 
      check_typ l "mk_pconstr" t 
        (fun d -> { t = Tapp(c.instantiation, c.descr.constr_tconstr) })
    in
    if List.length ps <> List.length c.descr.constr_args
    then raise (Ident.No_type(l, "wrong number of arguments for constructor"));
    if check then
      begin
        let subst = TNfmap.from_list2 c.descr.constr_tparams c.instantiation in
          List.iter2
            (fun t p -> type_eq l "mk_pconstr" (type_subst subst t) p.typ)
            c.descr.constr_args
            ps
      end;
    { term = P_constr(c,ps);
      locn = l;
      typ = t;
      rest = { pvars = merge_free_env true l (List.map (fun p -> p.rest.pvars) ps); }; }

  let mk_precord l s1 fps s2 t =
    let t = 
      check_typ l "mk_precord" t 
        (fun d ->
           let (f,_,p) = Seplist.hd fps in
             { t = Tapp(f.instantiation, f.descr.field_tconstr) })
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
        (fun d -> { t = Ttup(Seplist.to_list_map (fun p -> p.typ) ps) } )
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
    let t = check_typ l "mk_pparen" t (fun d -> p.typ) in
      { term = P_paren(s1,p,s2);
        locn = l;
        typ = t; 
        rest = { pvars = p.rest.pvars; }; }

  let mk_pcons l p1 s p2 t =
    let t = check_typ l "mk_pcons" t (fun d -> p2.typ) in
      type_eq l "mk_pcons" p2.typ { t = Tapp([p1.typ], Path.listpath) };
      { term = P_cons(p1,s,p2);
        locn = l;
        typ = t; 
        rest = { pvars = merge_free_env true l [p1.rest.pvars; p2.rest.pvars]; }; }

  let mk_pnum_add l xl s1 s2 i t =
    let t = check_typ l "mk_pnum_add" t (fun d -> { t = Tapp([], Path.numpath) }) in
      { term = P_num_add(xl,s1,s2,i);
        locn = l;
        typ = t; 
        rest = { pvars = sing_free_env (Name.strip_lskip (fst xl)) t; }; }

  let mk_plit l li t = 
    let t = check_typ l "mk_plit" t (fun d -> li.typ) in
    { term = P_lit(li);
      locn = l;
      typ = t; 
      rest = { pvars = empty_free_env; }; }

  let mk_pvar_annot l n src_t t : pat =
    let t = check_typ l "mk_pvar_annot" t (fun d -> src_t.typ) in
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
      | P_constr(c,ps) -> 
          let c =
            { c with instantiation = 
                List.map (type_subst tsubst) c.instantiation }
          in
            mk_pconstr l c (List.map (pat_subst sub) ps) (Some new_typ)
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

  let push_subst (tsubst,vsubst) ps e =
    let binders =
      List.fold_left
        (fun binders p -> NameSet.union (Nfmap.domain p.rest.pvars) binders)
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
      (List.map (pat_subst (tsubst,renames)) ps,
       exp_subst (tsubst,new_vsubst) e)

 let push_subst1 (tsubst,vsubst) p e =
    match push_subst (tsubst,vsubst) [p] e with
      | ([p'],e') -> (p',e')
      | _ -> assert false

  let push_subst_name subst n e =
    match push_subst1 subst (mk_pvar Ast.Unknown n.term n.typ) e with
      | ({ term = P_var(n'); typ = t; locn = l }, e) ->
          ({ n with term = n'; typ = t; locn = l; }, e)
      | _ -> assert false

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


  let rec push_quant_binds_subst_aux not_to_choose not_to_choose_ty (tsubst, vsubst) = function
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

  let push_quant_binds_subst (tsubst,vsubst) qbs es =
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

  let push_quant_binds_subst1 subst qbs e =
    match push_quant_binds_subst subst qbs [e] with
      | (qbs,[e]) -> (qbs,e)
      | _ -> assert false

  let push_quant_binds_subst2 subst qbs e1 e2 =
    match push_quant_binds_subst subst qbs [e1;e2] with
      | (qbs,[e1;e2]) -> (qbs,e1,e2)
      | _ -> assert false

  (* This is very similar to push_quant_binds_subst_aux, but OCaml doesn't 
   * give us a very good way to abstract *)
  let rec push_do_lines_subst_aux not_to_choose not_to_choose_ty (tsubst, vsubst) = function
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

  let push_do_lines_subst (tsubst,vsubst) do_lines e =
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

  let rec exp_to_term e = 
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
        | Nvar_e(s,v) -> Nvar_e(s,v)
        | Constant(c) -> 
            Constant(id_subst c)
        | Constructor(c) -> 
            Constructor(id_subst c)
        | Tup_constructor(c,s1,es,s2) ->
            Tup_constructor(id_subst c,s1,Seplist.map (exp_subst subst) es,s2)
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
        | Record_coq(n,s1,fieldexps,s2) ->
            Record_coq(n,s1, 
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


  (*
  let val_descr_eq l id vd1 vd2 = 
    if check then
      match (vd1,vd2) with
        | (Constr(c1), Constr(c2)) when Path.compare c1.constr_binding c2.constr_binding = 0 ->
            ()
        | (Val(c1), Val(c2)) when Path.compare c1.const_binding c2.const_binding = 0 ->
            ()
        | (Fld(f1), Fld(f2)) when Path.compare f1.field_binding f2.field_binding = 0 ->
            ()
        | _ ->
            raise (Ident.No_type(l,"Incompatible assumptions over " ^ 
                             Pp.pp_to_string (fun ppf -> Path.pp ppf id) ^
                             "\n" ^
                             Pp.pp_to_string (fun ppf -> pp_val_descr ppf vd1) ^
                             "\n" ^
                             Pp.pp_to_string (fun ppf -> pp_val_descr ppf vd2)))

  let merge_p_env l envs =
    List.fold_left
      (fun e_res (e,_) ->
         Pfmap.merge
           (fun k v1 v2 ->
              match (v1,v2) with
                | (None,_) -> v2
                | (_,None) -> v1
                | (Some(v),Some(v')) ->
                    val_descr_eq l k v v';
                    v1)
           e
           e_res)
      Pfmap.empty
      envs
   *)

  let mk_lnum l s i t = 
    let t = check_typ l "mk_lnum" t (fun d -> { t = Tapp([],Path.numpath) }) in
    { term = L_num(s,i);
      locn = l;
      typ = t;
      rest = (); }

  let mk_lbool l s b t = 
    let t = check_typ l "mk_lbool" t (fun d -> { t = Tapp([],Path.boolpath) }) in
    { term = if b then L_true(s) else L_false(s);
      locn = l;
      typ = t;
      rest = (); }

  let mk_lbit l s b t =
    let t = check_typ l "mk_lbit" t (fun d -> { t = Tapp([],Path.bitpath) }) in
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
    let t = check_typ l "mk_lstring" t (fun d -> { t = Tapp([],Path.stringpath) }) in
    { term = L_string(s,c);
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
    let t = check_typ l "mk_tfn" t (fun d -> { t = Tfn(t1.typ, t2.typ) }) in
    { term = Typ_fn(t1,s,t2);
      locn = l;
      typ = t;
      rest = (); }

  let mk_ttup l ts t =
    let t = 
      check_typ l "mk_ttup" t 
        (fun d -> { t = Ttup(Seplist.to_list_map (fun x -> x.typ) ts) }) 
    in
    { term = Typ_tup(ts);
      locn = l;
      typ = t;
      rest = (); }

  let mk_tapp l p ts t =
    let t =
      check_typ l "mk_tapp" t 
        (fun d -> 
           { t = Tapp(List.map (fun x -> x.typ) ts, p.descr) })
    in
    { term = Typ_app(p,ts);
      locn = l;
      typ = t;
      rest = (); }

  let mk_tparen l s1 t1 s2 t =
    let t = check_typ l "mk_tparen" t (fun d -> t1.typ) in
    { term = Typ_paren(s1,t1,s2);
      locn = l;
      typ = t;
      rest = (); }

  let mk_var l n t : exp =
    { term = Var(n);
      locn = l;
      typ = t;
      rest =
        { free = sing_free_env (Name.strip_lskip n) t;
          subst = empty_sub; } }

  let mk_nvar_e l s n t : exp =
    { term = Nvar_e(s,n);
      locn = l;
      typ = t;
      rest =
        { free = empty_free_env; 
          subst = empty_sub; }; }

  let mk_const l c t : exp =
    let t = 
      check_typ l "mk_const" t 
        (fun d -> 
           type_subst 
             (TNfmap.from_list2 c.descr.const_tparams c.instantiation) 
             c.descr.const_type)
    in 
      { term = Constant(c);
        locn = l;
        typ = t;
        rest = { free = empty_free_env;
                 subst = empty_sub; }; }

  let mk_constr l c t : exp =
    let t =
      check_typ l "mk_constr" t
        (fun d -> 
           let subst = 
             TNfmap.from_list2 c.descr.constr_tparams c.instantiation
           in
             multi_fun 
               (List.map (type_subst subst) c.descr.constr_args)
               { t = Tapp(c.instantiation, c.descr.constr_tconstr) })
    in
      { term = Constructor(c);
        locn = l;
        typ = t;
        rest = { free = empty_free_env;
                 subst = empty_sub; }; }

  let mk_tup_ctor l c s1 es s2 t =
    let t = 
      check_typ l "mk_tup_ctor" t 
        (fun d -> { t = Tapp(c.instantiation, c.descr.constr_tconstr) })
    in
      if check then
        begin
          let subst = TNfmap.from_list2 c.descr.constr_tparams c.instantiation in
            List.iter2
              (fun t e -> type_eq l "mk_tup_ctor" (type_subst subst t) e.typ)
              c.descr.constr_args
              (Seplist.to_list es);
        end;
      { term = Tup_constructor(c,s1,es,s2);
        locn = l;
        typ = t; 
        rest =
          { free = 
              merge_free_env false l (Seplist.to_list_map exp_to_free es);
            subst = empty_sub; }; }

  let mk_fun l s1 ps s2 e t : exp  =
    let t = 
      check_typ l "mk_fun" t (fun d -> multi_fun (List.map (fun p -> p.typ) ps) e.typ)
    in
    let p_free = merge_free_env true l (List.map (fun p -> p.rest.pvars) ps) in
      { term = Fun(s1,ps,s2,e);
        locn = l;
        typ = t;
        rest = 
          { free = bind_free_env l p_free (exp_to_free e);
            subst = empty_sub; }; }

  let mk_function l s1 pes s2 t =
    let t = 
      check_typ l "mk_function" t
        (fun d -> 
           let (p,_,e,_) = Seplist.hd pes in
             { t = Tfn(p.typ,e.typ) })
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
            subst = empty_sub; }; }

  let mk_app l e1 e2 t =
    let t = 
      check_typ l "mk_app" t
        (fun d -> 
           match (head_norm d e1.typ).t with
             | Tfn(t1,t2) ->
                 type_eq l "mk_app" t1 e2.typ;
                 t2
             | _ -> 
                 raise (Ident.No_type(l, "non-function in application")))
    in
      { term = App(e1,e2);
        locn = l;
        typ = t; 
        rest = 
          { free = merge_free_env false l [exp_to_free e1;exp_to_free e2];
            subst = empty_sub; }; }

  let mk_infix l e1 e2 e3 t =
    let t' = 
      check_typ l "mk_infix" t
        (fun d ->
           match (head_norm d e2.typ).t with
             | Tfn(t1,t2) ->
                 begin
                   match (head_norm d t2).t with
                     | Tfn(t3,t4) ->
                         type_eq l "mk_infix" t1 e1.typ;
                         type_eq l "mk_infix" t3 e3.typ;
                         t4
                     | _ -> 
                         raise (Ident.No_type(l, "non-function in infix application"))
                 end
             | _ ->
                 raise (Ident.No_type(l, "non-function in infix application")))
    in
      match exp_to_term e2 with
        | Var _ | Constant _ | Constructor _ -> 
            { term = Infix(e1,e2,e3);
              locn = l;
              typ = t'; 
              rest =
                { free = merge_free_env false l [exp_to_free e1; exp_to_free e2; exp_to_free e3];
                  subst = empty_sub; }; }
        | _ -> 
            mk_app l (mk_app l e2 e1 (Some({ t = Tfn(e3.typ,t') }))) e3 t


  let mk_record l s1 fes s2 t =
    let t = 
      check_typ l "mk_record" t
        (fun d -> 
          let (f,_,e,_) = Seplist.hd fes in
          { t = Tapp(f.instantiation, f.descr.field_tconstr) })
    in
    if check then
      (* TODO: add typecheck code *)
      ();
    { term = Record(s1,fes,s2);
      locn = l;
      typ = t;
      rest = 
        { free = 
          merge_free_env false l 
            (Seplist.to_list_map (fun (_,_,e,_) -> exp_to_free e) fes);
          subst = empty_sub; }; }

  let mk_record_coq l s1 fes s2 t =
    let strip_file_name s =
      let rec split sep str =
        try
          let i = String.index str sep in
            String.sub str 0 i :: split sep (String.sub str (1 + i) (String.length str - (i + 1)))
        with Not_found -> [str]
      in
      let splitted = split '.' s in
        match splitted with
          | []    -> assert false
          | x::xs -> List.hd (List.rev splitted)
    in
    let t = 
      check_typ l "mk_record_coq" t
        (fun d -> 
          let (f,_,e,_) = Seplist.hd fes in
          { t = Tapp(f.instantiation, f.descr.field_tconstr) })
    in
    (* FZ WORKING HERE, discuss with Scott and Peter how to do this properly *)
    (* TODO: fix the Record_coq type accordingly *)
    let s = 
      Format.flush_str_formatter (Types.pp_type Format.str_formatter t) in
    (* DPM: ugly, ugly, ugly!  We should record both the name of the record
            type and the name of the function needed to build an inhabitant of
            that record type somehow.
    *)
    let stripped = strip_file_name s in
    let s = "Build_" ^ stripped in
    { term = Record_coq((Name.add_lskip (Name.from_rope (Ulib.Text.of_string s)),l),s1,fes,s2);
      locn = l;
      typ = t;
      rest = 
        { free = 
          merge_free_env false l 
            (Seplist.to_list_map (fun (_,_,e,_) -> exp_to_free e) fes);
          subst = empty_sub; }; }

  let mk_recup l s1 e s2 fes s3 t =
    let t = check_typ l "mk_recup" t (fun d -> e.typ) in
      if check then
        (* TODO: add typecheck code *)
        ();
      { term = Recup(s1,e,s2,fes,s3);
        locn = l;
        typ = t; 
        rest = 
          { free = 
              merge_free_env false l 
                (exp_to_free e :: Seplist.to_list_map (fun (_,_,e,_) -> exp_to_free e) fes);
            subst = empty_sub; }; }

  let mk_field l e s f t =
    let t = 
      check_typ l "mk_field" t
        (fun d ->
           let subst = 
             TNfmap.from_list2 f.descr.field_tparams f.instantiation
           in
             type_eq l "mk_field" e.typ
               { t = Tapp(f.instantiation, f.descr.field_tconstr) };
             type_subst subst f.descr.field_arg)
    in
      { term = Field(e,s,f);
        locn = l;
        typ = t; 
        rest =
          { free = exp_to_free e;
            subst = empty_sub; }; }

  let mk_vector l s1 es s2 t =
    let t =
      check_typ l "mk_vector" t 
        (fun d ->
           let len = Seplist.length es in
                     { t = Tapp([List.hd (Seplist.to_list_map (fun e -> e.typ) es); {t = Tne({nexp = Nconst(len)})}],
                                Path.vectorpath) })
    (* TODO KG determine if the types should be checked here to all be the same *)
    in
      {term = Vector(s1,es,s2);
       locn = l;
       typ = t;
       rest = 
          {free = merge_free_env false l (Seplist.to_list_map exp_to_free es);
           subst = empty_sub;}; }
                        
  let mk_vectoracc l e s1 n s2 t =
    let t = 
       check_typ l "mk_vectoracc" t (fun d -> 
                        match e.typ.t with | Tapp( [n1;t1], _ ) -> t1 (* TODO KG Need a better check that this is a vector *)
                                           | _ -> assert false)
    in
      {term = VectorAcc(e,s1,n,s2);
       locn = l;
       typ = t;
       rest = 
         { free = exp_to_free e;
           subst = empty_sub; }; }

  let mk_vectoraccr l e s1 n1 s2 n2 s3 t =
     (* TODO KG Add a check *)
     { term = VectorSub(e,s1,n1,s2,n2,s3);
       locn = l;
       typ = t;
       rest = 
         { free = exp_to_free e;
           subst = empty_sub; }; }

  let mk_case c l s1 e s2 pats s3 t =
    let t = 
      check_typ l "mk_case" t
        (fun d ->
           match Seplist.hd pats with
             | (_,_,e,_) -> e.typ)
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
            subst = empty_sub; }; }

  let mk_typed l s1 e s2 src_t s3 t =
    let t = check_typ l "mk_typed" t (fun d -> e.typ) in
      type_eq l "mk_typed" e.typ src_t.typ;
      { term = Typed(s1,e,s2,src_t,s3);
        locn = l;
        typ = t; 
        rest =
          { free = exp_to_free e;
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
    let t = check_typ l "mk_let" t (fun d -> e.typ) in
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
            subst = empty_sub; }; }

  let mk_tup l s1 es s2 t =
    let t = 
      check_typ l "mk_tup" t 
        (fun d -> { t = Ttup(Seplist.to_list_map (fun e -> e.typ) es) } )
    in
      { term = Tup(s1,es,s2);
        locn = l;
        typ = t; 
        rest =
          { free =
              merge_free_env false l (Seplist.to_list_map exp_to_free es);
            subst = empty_sub; }; }

  let mk_list l s1 es s2 t =
    if check then
      Seplist.iter 
        (fun e -> type_eq l "mk_list" { t = Tapp([e.typ], Path.listpath) } t) 
        es;
    { term = List(s1,es,s2);
      locn = l;
      typ = t;
      rest = 
        { free = merge_free_env false l (Seplist.to_list_map exp_to_free es);
          subst = empty_sub; }; }

  let mk_vector l s1 es s2 t =
    let tlen = {t = Tne({nexp = Nconst(Seplist.length es)}) } in 
    if check then
     Seplist.iter
       (fun e -> type_eq l "mk_vector" { t = Tapp([e.typ;tlen],Path.vectorpath) } t)
       es;
    { term = Vector(s1,es,s2);
      locn = l;
      typ = t;
      rest = 
        { free = merge_free_env false l (Seplist.to_list_map exp_to_free es);
          subst = empty_sub; }; }

   let mk_vaccess l e s1 n s2 t = 
     (* TODO KG Add type here, need a means of calling nexp_within or some such here *)
     { term = VectorAcc(e,s1,n,s2);
       locn = l;
       typ = t;
       rest =
        { free = exp_to_free e;
          subst = empty_sub; }; }       

  let mk_vaccessr l e s1 n1 s2 n2 s3 t =
     (* TODO KG add check here, see above *)
     { term = VectorSub(e,s1,n1,s2,n2,s3);
       locn = l;
       typ = t;
       rest = 
         { free = exp_to_free e;
           subst = empty_sub } }

  let mk_paren l s1 e s2 t =
    let t = check_typ l "mk_paren" t (fun d -> e.typ) in
      { term = Paren(s1,e,s2);
        locn = l;
        typ = t; 
        rest = 
          { free = exp_to_free e; 
            subst = empty_sub; }; }

  let mk_begin l s1 e s2 t =
    let t = check_typ l "mk_begin" t (fun d -> e.typ) in
      { term = Begin(s1,e,s2);
        locn = l;
        typ = t;
        rest = 
          { free = exp_to_free e;
            subst = empty_sub; }; }

  let mk_if l s1 e1 s2 e2 s3 e3 t =
    let t = check_typ l "mk_if" t (fun d -> e3.typ) in
      type_eq l "mk_if" e1.typ { t = Tapp([], Path.boolpath) };
      type_eq l "mk_if" e2.typ e3.typ;
      { term = If(s1,e1,s2,e2,s3,e3);
        locn = l;
        typ = t; 
        rest =
          { free = merge_free_env false l 
                     [exp_to_free e1; exp_to_free e2; exp_to_free e3];
            subst = empty_sub; }; }

  let mk_lit l li t =
    let t = check_typ l "mk_lit" t (fun d -> li.typ) in
      { term = Lit(li);
        locn = l;
        typ = t; 
        rest =
          { free = empty_free_env;
            subst = empty_sub; }; }

  let mk_set l s1 es s2 t =
    if check then
      Seplist.iter 
        (fun e -> type_eq l "mk_set" { t = Tapp([e.typ], Path.setpath) } t) 
        es;
    { term = Set(s1,es,s2);
      locn = l;
      typ = t;
      rest =
        { free = merge_free_env false l (Seplist.to_list_map exp_to_free es);
          subst = empty_sub; }; }

  let mk_setcomp l s1 e1 s2 e2 s3 ns t =
    let t = check_typ l "mk_setcomp" t (fun d -> { t = Tapp([e1.typ], Path.setpath) }) in
    let env = merge_free_env false l [exp_to_free e1; exp_to_free e2] in
      type_eq l "mk_setcomp" e2.typ { t = Tapp([], Path.boolpath) };
      { term = Setcomp(s1,e1,s2,e2,s3,ns);
        locn = l;
        typ = t;
        rest = 
          { free = NameSet.fold (fun k e -> Nfmap.remove e k) ns env;
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
                          raise (Ident.No_type(l, "Duplicate variable in a pattern: " ^
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
    let t = 
      check_typ l "mk_comp_binding" t
        (fun d -> 
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
            subst = empty_sub; }; }

  let mk_quant l q qbs s e t =
    let t = check_typ l "mk_quant" t (fun d -> e.typ) in
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
            subst = empty_sub; }; }

  let do_lns_bindings l do_lns = 
    merge_free_env false l
      (List.map (function | Do_line(p,_,_,_) -> p.rest.pvars) do_lns)

  let do_lns_envs l do_lns =
    List.map (function | Do_line(_,_,e,_) -> exp_to_free e) do_lns

  let mk_do l s1 mid do_lns s2 e s3 ret_t t =
    (* TODO: actually do the check *)
    let t = check_typ l "mk_do" t (fun d -> e.typ ) in
      { term = Do(s1,mid,do_lns,s2,e,s3,ret_t);
        locn = l;
        typ = t;
        rest =
          { free = pat_exp_list_freevars l true 
                     (List.map (function | Do_line(p,_,e,_) -> (p,Some e)) do_lns)
                     e;
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
      | Typ_app _ ->
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
            None 
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

let exp_to_prec get_prec (exp : exp) : P.t = 
  match exp_to_term exp with
    | Var(n) -> Name.get_prec get_prec n
    | Constant(c) -> 
        (match c.id_path with
          | Id_none _ -> assert false
          | Id_some p -> Ident.get_prec get_prec p)
    | Constructor(c) | Tup_constructor(c,_,_,_) -> 
        (match c.id_path with
          | Id_none _ -> assert false
          | Id_some p -> Ident.get_prec get_prec p)
    | _ -> assert false

let delimit_exp get_prec (c : P.context) (e : exp) : exp =
  let k = match exp_to_term e with
    | Tup_constructor _ | App _ -> P.App
    | Infix(_,e2,_) -> P.Infix(exp_to_prec get_prec e2)
    | Fun _ | Let _ | If _ | Quant _ -> P.Let
    | _ -> P.Atomic
  in
    if P.needs_parens c k then
      begin
        let (e, lskips) = alter_init_lskips (fun s -> (no_lskips, s)) e in
        let e' =
          { e with rest = { free = e.rest.free; 
                            subst = (TNfmap.empty,Nfmap.empty); }; }
        in
          { e with term = Paren(lskips,e',no_lskips); }
      end
    else
      e

end

let env_union e1 e2 =
  { m_env = Nfmap.union e1.m_env e2.m_env;
    p_env = Nfmap.union e1.p_env e2.p_env;
    v_env = Nfmap.union e1.v_env e2.v_env; 
    r_env = Nfmap.union e1.r_env e2.r_env;
    f_env = Nfmap.union e1.f_env e2.f_env }

let delimit_pat (c : P.pat_context) (p : pat) : pat =
  let k = match p.term with
    | P_wild _ | P_var _ | P_constr(_,[]) | P_lit _ | P_typ _ | P_record _
    | P_tup _ | P_list _ | P_paren _ | P_var_annot _ | P_vector _ | P_vectorC _ ->
        P.Patomic
    | P_as _ -> P.Pas
    | P_cons _ -> P.Pcons
    | P_constr _ -> P.Papp
    | P_num_add _ -> P.Pas
  in
    if P.pat_needs_parens c k then
      begin
        let (p_new, lskips) = pat_alter_init_lskips (fun s -> (no_lskips, s)) p in
          { term = P_paren(lskips,p_new,no_lskips); 
            locn = p.locn; typ = p.typ; rest = p.rest; }
      end
    else
      p

(* Lookup a name in an environment and report what type of name it is *)

type name_kind =
  | Nk_typeconstr
  | Nk_const
  | Nk_constr
  | Nk_field
  | Nk_module
  | Nk_class
 
let env_apply env n =
  match Nfmap.apply env.p_env n with
      Some (p, l) -> Some (Nk_typeconstr, p, l)
    | None ->
  match Nfmap.apply env.f_env n with
      Some d -> Some (Nk_field, d.field_binding, d.field_l)
    | None ->
  match Nfmap.apply env.v_env n with
      Some (Constr d) -> Some (Nk_constr, d.constr_binding, d.constr_l)
    | Some (Val d) -> Some (Nk_const, d.const_binding, d.spec_l)
    | None -> None

(* get all the newly defined constants names of a module *)

let add_new_constants_types_of_funcl_aux l (const_map, type_map) (n, _, _, _, _) =
   (Nfmap.insert const_map (Name.strip_lskip n.term, l), type_map)

let add_new_constants_types_of_letbind (const_map, type_map) (lb, l) =
   match lb with
     | Let_val _ -> (const_map, type_map)
     | Let_fun faux -> add_new_constants_types_of_funcl_aux l (const_map, type_map) faux

let add_new_constants_types_of_def targ (const_map, type_map) ((aux, _), l_base) =
    match aux with
      | Type_def(s1, tds) ->   
        begin
          let add_td (const_map, type_map) x =
            match x with
            | ((n,l),_,Te_abbrev(_,_),_) ->
                (const_map, Nfmap.insert type_map (Name.strip_lskip n, l))
            | ((n,l),_,Te_record(_, _, fields, _),_) -> 
              let type_map' = Nfmap.insert type_map (Name.strip_lskip n, l) in
              let field_name_list = List.map (fun ((n, l), _, _) -> (Name.strip_lskip n, l)) (Seplist.to_list fields) in
              let const_map' = List.fold_left Nfmap.insert const_map field_name_list in
                (const_map', type_map')
            | ((n,l),_,Te_record_coq(_, _, _, fields, _),_) ->
              let type_map' = Nfmap.insert type_map (Name.strip_lskip n, l) in
              let field_name_list = List.map (fun ((n, l), _, _) -> (Name.strip_lskip n, l)) (Seplist.to_list fields) in
              let const_map' = List.fold_left Nfmap.insert const_map field_name_list in
                (const_map', type_map')
            | ((n,l),_,Te_variant(_, constrs),_) -> 
              let type_map' = Nfmap.insert type_map (Name.strip_lskip n, l) in
              let constr_name_list = List.map (fun ((n, l), _, _) -> (Name.strip_lskip n, l)) (Seplist.to_list constrs) in
              let const_map' = List.fold_left Nfmap.insert const_map constr_name_list in
                (const_map', type_map')
            | ((n,l),_,Te_variant_coq(_, constrs),_) ->
              let type_map' = Nfmap.insert type_map (Name.strip_lskip n, l) in
              let constr_name_list = List.map (fun ((n, l), _, _, _, _) -> (Name.strip_lskip n, l)) (Seplist.to_list constrs) in
              let const_map' = List.fold_left Nfmap.insert const_map constr_name_list in
                (const_map', type_map')
            | _ -> (const_map, type_map)
          in
            List.fold_left add_td (const_map, type_map) (Seplist.to_list tds) 
        end
      | Val_spec(_,(n, l),_,_) -> 
        (Nfmap.insert const_map (Name.strip_lskip n, l), type_map)

      | Val_def(Let_def(_, topt, lb),_,_) -> if not (in_targets_opt targ topt) then (const_map, type_map) else add_new_constants_types_of_letbind (const_map, type_map) lb

      | Val_def(Rec_def(_, _, topt, funs),_,_) -> if not (in_targets_opt targ topt) then (const_map, type_map) else
           List.fold_left (add_new_constants_types_of_funcl_aux l_base) (const_map, type_map) (Seplist.to_list funs)

      | Val_def(Let_inline(sk1,sk2,targ,n,ns,sk4,e), tnvs,_) -> (const_map, type_map)

      | _  -> (const_map, type_map)



let get_new_constants_types targ checked_module_list =
  let ast_target_opt = Util.option_map target_to_ast_target targ in
  let add_def_list s dl = List.fold_left (add_new_constants_types_of_def ast_target_opt) s dl in
  let add_fun s cm = add_def_list s (fst (cm.typed_ast)) in
  let result = List.fold_left add_fun (Nfmap.empty, Nfmap.empty) checked_module_list in
  result

exception Renaming_error of Ast.l * string

let add_renames_of_def targ resL ((aux, _), _) =
    match aux with
      | Ident_rename(_, topt, p, _, _, (n_new, l)) -> 
          if not (in_targets_opt targ topt) then resL else 
            let already_renamed = try (match List.assoc p resL with (l', _) -> Some l') with Not_found -> None in
            (match already_renamed with
              | Some l' -> (
                   raise (Renaming_error (l, ("Identifier '"^(Name.to_string (Path.get_name p))^ "' has already been renamed at "^ (Reporting_basic.loc_to_string true l) ^ "!")))
                )
              | None -> (p, (l, let (nl, _) = Path.to_name_list p in Path.mk_path nl (Name.strip_lskip n_new))) :: resL)
      | _  -> resL

let get_renames_of_defs targ org_ren def_list =
  let ast_target_opt = Util.option_map target_to_ast_target targ in
  List.fold_left (add_renames_of_def ast_target_opt) org_ren def_list

let funcl_aux_seplist_group (sl : funcl_aux lskips_seplist) = begin
  let (first_s, pL) = Seplist.to_pair_list None sl in
  let add_fun_name ((((nsa, _, _, _, _) : funcl_aux), _) as x) =
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

let class_path_to_dict_type c arg =
  let (mods,n) = Path.to_name_list c in
  let n = Name.rename (fun x -> Ulib.Text.(^^^) x (r"_class")) n in
    { Types.t = Types.Tapp([arg], Path.mk_path mods n) }

let rec names_get_field env path =
  match path with
    | [] -> assert false
    | [n] ->
        begin
          match Nfmap.apply env.f_env n with
            | Some(x) -> x
            | _ ->
              Format.printf "%a@ IN@\n%a@\n" Name.pp n pp_env env;
              assert false
        end
    | n::p ->
        begin
          match Nfmap.apply env.m_env n with
            | Some(x) ->
                names_get_field x.mod_env p
            | None -> 
                Format.printf "%a@ IN@\n%a@\n" Name.pp n pp_env env;
                assert false
        end

let rec fix_mod_path mp =
  match mp with 
    | [] -> []
    | (n::mn) ->
        if Name.compare n (target_to_mname Target_hol) = 0 ||
           Name.compare n (target_to_mname Target_isa) = 0 ||
           Name.compare n (target_to_mname Target_coq) = 0 ||
           Name.compare n (target_to_mname Target_ocaml) = 0 then
          fix_mod_path mn
        else
          n::mn

(* TODO: This needs to be much more sophisticated *)
let resolve_ident_path id path : Ident.t =
  let id = 
    match id.id_path with 
      | Id_none sk -> 
          let (mod_names, name) = Path.to_name_list path in
          let mod_names' = List.map (fun mn -> (Name.add_lskip mn, None)) (fix_mod_path mod_names) in
          let mod_names' = [] in
            Ident.replace_first_lskip (Ident.mk_ident mod_names' (Name.add_lskip name) id.id_locn) sk
      | Id_some id -> id
  in
  (* TODO: A hack dealing with the option type *)
  let (mods,n) = Ident.to_name_list id in
    if 0 = Path.compare (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"option")))
                        (Path.mk_path mods n) then
      Ident.mk_ident [] (Name.replace_lskip (Name.add_lskip n) (Ident.get_first_lskip id)) Ast.Unknown
    else if 0 = Path.compare (Path.mk_path [Name.from_rope (r"Pervasives")] (Name.from_rope (r"sum")))
                        (Path.mk_path mods n) then
      Ident.mk_ident [] (Name.replace_lskip (Name.add_lskip n) (Ident.get_first_lskip id)) Ast.Unknown
    else
      id


let ident_get_first_lskip id =
  match id.id_path with
    | Id_none sk -> sk
    | Id_some i -> Ident.get_first_lskip i

let ident_replace_first_lskip id sk =
  match id with
    | Id_none _ -> Id_none sk
    | Id_some i -> Id_some (Ident.replace_first_lskip i sk)
