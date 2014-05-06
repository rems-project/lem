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
open Types
module C = Exps_in_context(struct let env_opt = None let avoid = None end)

let rec is_var_wild_pat (p : pat) : bool =
  match p.term with
    | P_wild _ | P_var _ | P_var_annot _ -> true
    | P_typ(_,p,_,_,_) | P_paren(_,p,_) -> 
        is_var_wild_pat p
    | _ -> false

let rec dest_ext_var_pat (p : pat) : Name.t option =
  match p.term with
    | P_var ns -> Some (Name.strip_lskip ns)
    | P_var_annot (ns, _) -> Some (Name.strip_lskip ns)
    | P_typ(_,p,_,_,_) | P_paren(_,p,_) -> 
        dest_ext_var_pat p
    | _ -> None

let is_ext_var_pat (p : pat) : bool = not (dest_ext_var_pat p = None)

let dest_var_pat p =
  match p.term with
    | P_var ns -> Some (Name.strip_lskip ns)
    | _ -> None

let is_var_pat (p : pat) : bool =
  match p.term with
    | P_var _ -> true
    | _ -> false

let rec pat_to_ext_name (p:pat) : name_lskips_annot option = 
  match p.term with
    | P_var n -> Some { term = n; typ= p.typ; locn = p.locn; rest = (); }
    | P_var_annot (n, _) -> Some { term = n; typ= p.typ; locn = p.locn; rest = (); }
    | P_typ(_,p,_,_,_) | P_paren(_,p,_) -> pat_to_ext_name p
    | _ -> None

(** Is it a wildcard pattern? Nothing else including typed vars accepted. 
    @param p Something *)
let rec is_wild_pat (p : pat) : bool =
  match p.term with
    | P_wild _ -> true
    | _ -> false

let rec dest_tup_pat (lo : int option) (p : pat) : pat list option =
  match p.term with
    | P_tup (_, sl, _) -> 
      begin
        let l = Seplist.to_list sl in
        match lo with None -> Some l
                    | Some len -> if List.length l = len then Some l else None
      end
    | _ -> None

let is_tup_pat lo p = not (dest_tup_pat lo p = None)

let mk_tup_pat = function [p] -> p | pL ->
  let l = Ast.Trans (true, "mk_tup_pat", None) in
  let ty = { Types.t = Types.Ttup(List.map annot_to_typ pL) } in
  let ps = Seplist.from_list (List.map (fun p -> (p, None)) pL) in
  let p = C.mk_ptup l None ps None (Some ty) 
in p


let rec dest_tf_pat (p :pat) : bool option =
  match p.term with
  | P_lit l -> (
    match l.term with
      L_true _ -> Some true
    | L_false _ -> Some false
    | _ -> None)
  | _ -> None

let is_tf_pat p = not (dest_tf_pat p = None)
let is_t_pat p = (dest_tf_pat p = Some true)
let is_f_pat p = (dest_tf_pat p = Some false)

let mk_tf_pat b =
  let l = Ast.Trans (false, "mk_tf_pat", None) in
  let bool_ty = { Types.t = Types.Tapp ([], Path.boolpath) } in
  let lit = C.mk_lbool l None b (Some bool_ty) in
  let exp = C.mk_plit l lit (Some bool_ty) 
in exp

let mk_paren_pat =
  let l = Ast.Trans (false, "mk_paren_pat", None) in
  fun p ->
     let (p', ws) = pat_alter_init_lskips Typed_ast_syntax.remove_init_ws p in
     C.mk_pparen l ws p' None (Some (annot_to_typ p))

let mk_opt_paren_pat (p :pat) : pat =
  let needs_parens =
    match p.term with
      | P_wild _ -> false
      | P_var _  -> false
      | P_paren _ -> false
      | P_tup _ -> false
      | P_lit _ -> false
      | P_const (_, pL) -> not (pL = [])
      | P_backend (_, _, _, pL) -> not (pL = [])
      | _ -> true
  in 
  if (needs_parens) then 
    mk_paren_pat p 
  else p


let rec dest_num_pat (p :pat) : int option =
  match p.term with
  | P_lit l -> (
    match l.term with
      L_num (_, n,_) -> Some n
    | _ -> None)
  | P_paren (_, p, _) -> dest_num_pat p
  | P_typ(_,p,_,_,_) -> dest_num_pat p
  | _ -> None

let is_num_pat p = not (dest_num_pat p = None)

let mk_num_pat num_ty i = 
  let l = Ast.Trans (false, "mk_num_pat", None) in
  let lit = C.mk_lnum l None i None num_ty in
  C.mk_plit l lit (Some num_ty)

let rec dest_num_add_pat (p :pat) : (Name.t * int) option =
  match p.term with
  | P_num_add ((n, _), _, _, i) -> Some (Name.strip_lskip n, i)
  | P_paren (_, p, _) -> dest_num_add_pat p
  | P_typ(_,p,_,_,_) -> dest_num_add_pat p
  | _ -> None

let is_num_add_pat p = 
  not (dest_num_add_pat p = None)

let mk_num_add_pat num_ty n i = 
  let l = Ast.Trans (false, "mk_num_add_pat", None) in
  mk_paren_pat (C.mk_pnum_add l (Name.add_lskip n,l) space space i (Some num_ty))

let num_ty_pat_cases f_v f_i f_a f_w f_else p =
  Util.option_cases (dest_ext_var_pat p) f_v (fun () ->
                 Util.option_cases (dest_num_pat p) f_i (fun () ->
                   Util.option_cases (dest_num_add_pat p) (fun (n,i) -> 
                       if i = 0 then f_v n else f_a n i)
                     (fun () -> if is_wild_pat p then f_w else f_else p)))

let rec dest_string_pat (p :pat) : string option =
  match p.term with
  | P_lit l -> (
    match l.term with
      L_string (_, s, _) -> Some s
    | _ -> None)
  | _ -> None

let is_string_pat p = not (dest_string_pat p = None)

let rec dest_cons_pat (p :pat) : (pat * pat) option =
  match p.term with
  | P_cons (p1, _, p2) -> Some (p1, p2)
  | _ -> None

let is_cons_pat p = not (dest_cons_pat p = None)

let rec dest_list_pat (lo : int option) (p : pat) : pat list option =
  match p.term with
  | P_list (_, ps, _) ->
      let l = Seplist.to_list ps in
      (match lo with None -> Some l
        | Some len -> if List.length l = len then Some l else None)
  | _ -> None

let is_list_pat (lo : int option) p = not (dest_list_pat lo p = None)


let rec dest_const_pat (p : pat) : (const_descr_ref id * pat list) option =
  match p.term with
  | P_const (descr, pL) -> Some (descr, pL)
  | _ -> None

let is_const_pat p = not (dest_const_pat p = None)


let rec dest_record_pat (p : pat) : (const_descr_ref id * pat) list option =
  match p.term with
    | P_record (_, sl, _) -> 
     begin
        let l = Seplist.to_list sl in
        let l' = List.map (fun (i, _, p) -> (i, p)) l in
        if (l' = []) then None else Some l'
      end
    | _ -> None

let is_record_pat p = not (dest_record_pat p = None)


(* Patterns that are most basic and should be supported by any backend *)
let direct_subpats (p : pat) : pat list =
  match p.term with
    | (P_lit _ | P_wild _ | P_var _ | P_var_annot _) -> []
    | P_num_add (_, _, _, _) -> []
    | P_typ (_,p,_,_,_) -> [p] 
    | P_paren(_,p,_) -> [p]
    | P_const(_,ps) -> ps
    | P_backend(_,_,_,ps) -> ps
    | P_as (_, p, _, _, _) -> [p]
    | P_cons(p1,_,p2) -> [p1;p2]
    | P_tup(_,ps,_) -> Seplist.to_list ps
    | P_list(_,ps,_) -> Seplist.to_list ps
    | P_record (_, pfl, _) -> List.map (fun (_, _, p) -> p) (Seplist.to_list pfl)
    | P_vector (_, ps, _) -> Seplist.to_list ps
    | P_vectorC (_, ps, _) -> ps

let rec subpats (p : pat) : pat list =
  let spL = List.map subpats (direct_subpats p) in
  p :: (List.flatten spL)

let rec exists_subpat (cf : pat -> bool) (p : pat) : bool = 
  cf p || List.exists (exists_subpat cf) (direct_subpats p)

let rec for_all_subpat (cf : pat -> bool) (p : pat) : bool = 
  cf p && List.for_all (for_all_subpat cf) (direct_subpats p)

let rec is_var_tup_pat p : bool = match p.term with
    | (P_wild _ | P_as _ | P_const _ | P_backend _ | P_record _ | P_list _ | P_cons _  | P_lit _) -> false
    | P_paren(_,p,_) -> is_var_tup_pat p
    | P_var _ | P_var_annot _ -> true
    | P_typ(_,p,_,_,_) -> is_var_tup_pat p
    | P_tup(_,ps,_) -> Seplist.for_all is_var_tup_pat ps
    | P_vector _ | P_vectorC _ -> false
    | P_num_add _ -> false

let rec is_var_wild_tup_pat p : bool = match p.term with
    | P_wild _ -> true
    | P_paren(_,p,_) -> is_var_wild_tup_pat p
    | P_var _ | P_var_annot _ -> true
    | P_typ(_,p,_,_,_) -> is_var_wild_tup_pat p
    | P_tup(_,ps,_) -> Seplist.for_all is_var_wild_tup_pat ps
    | _ -> false

let split_var_annot_pat p = match p.term with
  | P_var_annot (n, src_t) -> C.mk_ptyp (p.locn) None (C.mk_pvar (p.locn) n (annot_to_typ p)) None src_t None (Some (annot_to_typ p))
  | _ -> p

let rec single_pat_exhaustive (p : pat) : bool = 
  match p.term with
    | P_wild _ | P_var _ | P_var_annot _ -> true
    | P_tup(_,ps,_) ->
        Seplist.for_all single_pat_exhaustive ps
    | P_const(c,ps) ->
        (* TODO *) false (*
        NameSet.cardinal c.descr.constr_names = 1 &&
        List.for_all single_pat_exhaustive ps *)
    | P_backend _ -> false
    | P_record(_,fes,_) ->
        Seplist.for_all
          (fun (_,_,p) -> single_pat_exhaustive p)
          fes
    | P_num_add (_, _, _, n) -> (n = 0)
    | P_lit _ | P_list _ | P_cons _ | P_vector _ | P_vectorC _ ->
        false
    | P_as(_,p,_,_,_) | P_typ(_,p,_,_,_) | P_paren(_,p,_) -> 
        single_pat_exhaustive p

let rec pat_vars_src p = match p.term with
  | P_wild _ -> []
  | P_as(_,p,_,(n,_),_) ->
      { term = n; typ = p.typ; locn = p.locn; rest = (); } :: pat_vars_src p
  | P_typ(_,p,_,_,_) ->
      pat_vars_src p
  | P_var(n) | P_var_annot(n,_) ->
      [{ term = n; typ = p.typ; locn = p.locn; rest = (); }]
  | P_const(_,ps) ->
      List.concat (List.map pat_vars_src ps)
  | P_record(_,fieldpats,_) ->
      List.concat (Seplist.to_list_map (fun (_,_,p) -> pat_vars_src p) fieldpats)
  | P_tup(_,ps,_) ->
      List.concat (Seplist.to_list_map pat_vars_src ps)
  | P_list(_,ps,_) ->
      List.concat (Seplist.to_list_map pat_vars_src ps)
  | P_paren(_,p,_) ->
      pat_vars_src p
  | P_cons(p1,_,p2) ->
      (pat_vars_src p1) @ (pat_vars_src p2)
  | P_num_add((n, _),_,_, _) ->
      [{ term = n; typ = p.typ; locn = p.locn; rest = (); }]
  | P_lit _ -> []
  | _ -> raise (Reporting_basic.err_todo true p.locn "Unimplemented pattern in pat_vars_src")


let rec pat_extract_lskips p = 
  let sk_flatten sks = List.fold_right Ast.combine_lex_skips sks None in
  match p.term with
  | P_wild s -> s
  | P_as(s1,p,s2,(n,_),s3) -> 
      sk_flatten [s1; pat_extract_lskips p; s2; Name.get_lskip n; s3]
  | P_typ(s1,p,s2,_,s3) -> (* TODO extract from src_t as well *)
      sk_flatten [s1; pat_extract_lskips p; s2; s3]
  | P_var(n) ->Name.get_lskip n
  | P_var_annot(n,_) -> (* TODO extract from src_t as well *)
     Name.get_lskip n
  | P_const(_,ps) ->
     sk_flatten (List.map pat_extract_lskips ps)
  | P_record(s1,fieldpats,s2) ->
     let ws = Seplist.to_sep_list (fun (_, s, p) -> Ast.combine_lex_skips s (pat_extract_lskips p)) (fun s -> s) fieldpats in
     sk_flatten (s1 :: ws @ [s2])
  | P_tup(s1,ps,s2) ->
     let ws = Seplist.to_sep_list pat_extract_lskips (fun s -> s) ps in
     sk_flatten (s1 :: ws @ [s2])
  | P_list(s1,ps,s2) ->
     let ws = Seplist.to_sep_list pat_extract_lskips (fun s -> s) ps in
     sk_flatten (s1 :: ws @ [s2])
  | P_paren(s1,p,s2) ->
      sk_flatten [s1; pat_extract_lskips p; s2]
  | P_cons(p1,s,p2) ->
      sk_flatten [pat_extract_lskips p1; s; pat_extract_lskips p2]
  | P_num_add((n, _),s1,s2,_) ->
      sk_flatten [Name.get_lskip n; s1; s2]
  | P_lit _ -> (* TODO *) None
  | _ -> (*TODO*) None



exception Pat_to_exp_unsupported of Ast.l * string
let rec pat_to_exp env p = 
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  let l_unk = Ast.Trans(true, "pat_to_exp", Some p.locn) in
  match p.term with
    | P_wild(lskips) -> 
        raise (Pat_to_exp_unsupported(p.locn, "_ pattern"))
    | P_as(_,p,_,(n,_),_) ->
        raise (Pat_to_exp_unsupported(p.locn, "as pattern"))
    | P_typ(lskips1,p,lskips2,t,lskips3) ->
        C.mk_typed p.locn lskips1 (pat_to_exp env p) lskips2 t lskips3 None
    | P_var(n) ->
        C.mk_var p.locn n p.typ
    | P_const(c,ps) ->
        List.fold_left
          (fun e p -> C.mk_app l_unk e (pat_to_exp env p) None)
          (C.mk_const p.locn c None)
          ps
    | P_backend(sk,i,ty,ps) ->
        List.fold_left
          (fun e p -> C.mk_app l_unk e (pat_to_exp env p) None)
          (C.mk_backend p.locn sk i ty)
          ps
    | P_record(_,fieldpats,_) ->
        raise (Pat_to_exp_unsupported(p.locn, "record pattern"))
    | P_tup(lskips1,ps,lskips2) ->
        C.mk_tup p.locn lskips1 (Seplist.map (pat_to_exp env) ps) lskips2 None
    | P_list(lskips1,ps,lskips2) ->
        C.mk_list p.locn lskips1 (Seplist.map (pat_to_exp env) ps) lskips2 p.typ
    | P_vector(lskips1,ps,lskips2) ->
        C.mk_vector p.locn lskips1 (Seplist.map (pat_to_exp env) ps) lskips2 p.typ
    | P_vectorC(lskips1,ps,lskips2) ->
        raise (Pat_to_exp_unsupported(p.locn, "vector concat pattern")) (* NOTE Would it be good enough to expand this into n calls to Vector.vconcat *)
    | P_paren(lskips1,p,lskips2) ->
        C.mk_paren p.locn lskips1 (pat_to_exp env p) lskips2 None
    | P_cons(p1,lskips,p2) ->
        let cons = Typed_ast_syntax.mk_const_exp env l_unk "list_cons" [p1.typ] in
          C.mk_infix p.locn (pat_to_exp env p1) (append_lskips lskips cons) (pat_to_exp env p2) None
    | P_lit(l) ->
        C.mk_lit p.locn l None
    | P_num_add _ -> 
        raise (Pat_to_exp_unsupported(p.locn, "add_const pattern"))
    | P_var_annot(n,t) ->
        C.mk_typed p.locn None (C.mk_var p.locn n p.typ) None t None None



let is_constructor l env (targ: Target.target) (c : const_descr_ref) =
  let cd = c_env_lookup l env.c_env c in
  let (_, base_ty) = strip_fn_type (Some env.t_env) cd.const_type in
  (List.length (type_defs_get_constr_families l env.t_env targ base_ty c) > 0)

let is_buildin_constructor l env (targ: Target.target) (c : const_descr_ref) =
  let cd = c_env_lookup l env.c_env c in
  let (_, base_ty) = strip_fn_type (Some env.t_env) cd.const_type in
  List.exists (fun cf -> cf.constr_case_fun = None) (type_defs_get_constr_families l env.t_env targ base_ty c);;

let is_not_buildin_constructor l env (targ: Target.target) (c : const_descr_ref) =
  let cd = c_env_lookup l env.c_env c in
  let (_, base_ty) = strip_fn_type (Some env.t_env) cd.const_type in
  List.exists (fun cf -> not (cf.constr_case_fun = None)) (type_defs_get_constr_families l env.t_env targ base_ty c);;
