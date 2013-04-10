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

(** try to fix problems from target's different precedence *)

(* Traversing expressions to resolve any target parsing problems that will arise
 * from infix and missing parentheses *)
open Typed_ast

module M = Macro_expander.Expander(struct let avoid = None let check = None end)
module C = Exps_in_context(struct let avoid = None let check = None end)
module P = Precedence

let id_fix_parens_for_prefix f get_prec id =
  let p = resolve_ident_path id (f id.descr) in
  let add_or_drop = 
    if P.is_infix (Ident.get_prec get_prec p) then
      Ident.add_parens
    else
      Ident.drop_parens
  in
    { id with id_path = Id_some (add_or_drop get_prec p) }

let name_fix_parens_for_prefix get_prec n =
  if P.is_infix (Name.get_prec get_prec n) then
    Name.add_parens n
  else
    Name.drop_parens n

let fix_pat_parens get_prec p =
  match p.term with
    | P_constr(c,ps) ->
        let id = resolve_ident_path c c.descr.constr_binding in
        let path = 
          if P.is_infix (Ident.get_prec get_prec id) then
            Ident.add_parens get_prec id
          else
            Ident.drop_parens get_prec id
        in
          { p with term = P_constr({c with id_path = Id_some path}, ps) }
    | P_var(n) ->
        let n = 
          if P.is_infix (Name.get_prec get_prec n) then
            Name.add_parens n
          else
            Name.drop_parens n
        in
          { p with term = P_var(n) }
    | P_var_annot(n,t) ->
        let n = 
          if P.is_infix (Name.get_prec get_prec n) then
            Name.add_parens n
          else
            Name.drop_parens n
        in
          { p with term = P_var_annot(n,t) }
    | _ -> assert false

let rec fix_pat get_prec p = 
  let old_t = Some(p.typ) in
  let old_l = p.locn in
  let trans = fix_pat get_prec in
    match p.term with
      | P_as(sk1,p,s,nl,sk2) -> 
          C.mk_pas old_l sk1 (delimit_pat P.Pas_left (trans p)) s nl sk2 old_t
      | P_typ(s1,p,s2,t,s3) -> 
          C.mk_ptyp old_l s1 (trans p) s2 t s3 old_t
      | P_constr(c,ps) -> 
          fix_pat_parens get_prec
            (C.mk_pconstr old_l 
               c 
               (List.map 
                  (fun p -> delimit_pat P.Plist (trans p)) 
                  ps)
               old_t)
      | P_record(s1,fieldpats,s2) ->
          C.mk_precord old_l
            s1 
            (Seplist.map 
               (fun (fid,s1,p) -> (fid,s1,trans p))
               fieldpats)
            s2
            old_t
      | P_tup(s1,ps,s2) -> 
          C.mk_ptup old_l s1 (Seplist.map trans ps) s2 old_t
      | P_list(s1,ps,s2) -> 
          C.mk_plist old_l s1 (Seplist.map trans ps) s2 p.typ
      | P_vector(s1,ps,s2) ->
          C.mk_pvector old_l s1 (Seplist.map trans ps) s2 p.typ
      | P_vectorC(s1,ps,s2) ->
          C.mk_pvectorc old_l s1 (List.map trans ps) s2 p.typ
      | P_paren(s1,p,s2) -> 
          C.mk_pparen old_l s1 (trans p) s2 old_t
      | P_cons(p1,s,p2) -> 
          C.mk_pcons old_l
            (delimit_pat P.Pcons_left (trans p1)) 
            s 
            (delimit_pat P.Pcons_right (trans p2))
            old_t
      | (P_var _ | P_var_annot _) -> 
          fix_pat_parens get_prec p
      | (P_lit _ | P_wild _ | P_num_add _) ->
          p


let rec fix_exp get_prec e = 
  let trans = fix_exp get_prec in 
  let transp = fix_pat get_prec in
  let old_t = Some(exp_to_typ e) in
  let old_l = exp_to_locn e in
    match (C.exp_to_term e) with
      | Tup_constructor(c,s1,es,s2) ->
          C.mk_tup_ctor old_l 
            (id_fix_parens_for_prefix (fun x -> x.constr_binding) get_prec c) 
            s1 (Seplist.map trans es) s2 old_t
      | Fun(s1,ps,s2,e) ->
          C.mk_fun old_l 
            s1 (List.map (fun p -> delimit_pat P.Plist (transp p)) ps) 
            s2 (trans e)
            old_t
      | Function(s1,pes,s2) ->
          C.mk_function old_l
            s1 (Seplist.map 
                  (fun (p,s1,e,l) -> (transp p,s1,trans e,l))
                  pes)
            s2
            old_t
      | App(e1,e2) ->
          C.mk_app old_l
            (C.delimit_exp get_prec P.App_left (skip_apps get_prec e1))
            (C.delimit_exp get_prec P.App_right (trans e2))
            old_t
      | Infix(e1,e2,e3) ->
          let trans_e2 = trans e2 in
          let e2_term = C.exp_to_term trans_e2 in
          let stay_infix =
            match e2_term with
              | Var _ | Constant _ | Constructor _ ->
                  P.is_infix (C.exp_to_prec get_prec e2)
              | _ -> false
          in
            if stay_infix then
              begin
                let e2' =
                  match e2_term with
                    | Var(n) ->
                        C.mk_var (exp_to_locn trans_e2)
                          (Name.drop_parens n) 
                          (exp_to_typ trans_e2)
                    | Constant(c) ->
                        C.mk_const (exp_to_locn trans_e2)
                          { c with id_path = 
                              Id_some (Ident.drop_parens get_prec (resolve_ident_path c c.descr.const_binding)) }
                          (Some(exp_to_typ trans_e2))
                    | Constructor(c) ->
                        C.mk_constr (exp_to_locn trans_e2)
                          { c with id_path = 
                              Id_some (Ident.drop_parens get_prec (resolve_ident_path c c.descr.constr_binding)) }
                          (Some(exp_to_typ trans_e2))
                    | _ -> assert false
                in
                  C.mk_infix old_l 
                    (C.delimit_exp get_prec
                       (P.Infix_left(C.exp_to_prec get_prec e2)) 
                       (trans e1))
                    e2'
                    (C.delimit_exp get_prec 
                       (P.Infix_right(C.exp_to_prec get_prec e2)) 
                       (trans e3))
                    old_t
              end
            else
              (* Move the Whitespace preceding the first subexpression to
               * precede the operator, to keep it in front of the whole
               *expression *)
              let (e1',sk) = alter_init_lskips (fun x -> (None,x)) e1 in
              let trans_e2' = append_lskips sk trans_e2 in
                C.mk_app old_l 
                  (C.mk_app old_l 
                     (C.delimit_exp get_prec P.App_left trans_e2')
                     (C.delimit_exp get_prec P.App_right (trans e1'))
                     (Some({ Types.t = Types.Tfn(exp_to_typ e3,exp_to_typ e) })))
                  (C.delimit_exp get_prec P.App_right (trans e3))
                  old_t

      | Record(s1,fieldexps,s2) ->
          C.mk_record old_l
            s1
            (Seplist.map 
               (fun (fid,s1,e,l) -> (fid,s1,C.delimit_exp get_prec P.App_right (trans e),l))
               fieldexps)
            s2
            old_t
      | Record_coq(n,s1,fieldexps,s2) ->
          C.mk_record_coq old_l
            s1
            (Seplist.map 
               (fun (fid,s1,e,l) -> (fid,s1,trans e,l))
               fieldexps)
            s2
            old_t
      | Recup(s1,e,s2,fieldexps,s3) ->
          C.mk_recup old_l
            s1 (trans e) s2
            (Seplist.map 
               (fun (fid,s1,e,l) -> (fid,s1,trans e,l))
               fieldexps)
            s3
            old_t
      | Field(e,s,fid) ->
          C.mk_field old_l 
            (C.delimit_exp get_prec P.Field (trans e)) s fid
            old_t
      | Case(c,s1,e,s2,patexps,s3) ->
          C.mk_case c old_l
            s1 (trans e) s2
            (Seplist.map
               (fun (p,s1,e,l) -> (transp p,s1,trans e,l))
               patexps)
            s3
            old_t
      | Typed(s1,e,s2,t,s3) ->
          C.mk_typed old_l 
            s1 (trans e) s2 t s3
            old_t
      | Let(s1,letbind,s2,e) ->
          C.mk_let old_l
            s1 (fix_letbind get_prec letbind) s2 (trans e)
            old_t
      | Tup(s1,es,s2) ->
          C.mk_tup old_l
            s1 (Seplist.map (fun e -> C.delimit_exp get_prec P.App_left (trans e)) es) s2
            old_t
      | List(s1,es,s2) ->
          C.mk_list old_l
            s1 (Seplist.map (fun e -> C.delimit_exp get_prec P.App_left (trans e)) es) s2
            (exp_to_typ e)
      | Vector(s1,es,s2) ->
          C.mk_vector old_l
            s1 (Seplist.map (fun e -> C.delimit_exp get_prec P.App_left (trans e)) es) s2
            (exp_to_typ e)
      | VectorAcc(e,s1,n,s2) ->
          C.mk_vaccess old_l (trans e) s1 n s2 
            (exp_to_typ e)
      | VectorSub(e,s1,n1,s2,n2,s3) ->
         C.mk_vaccessr old_l (trans e) s1 n1 s2 n2 s3
            (exp_to_typ e)
      | Paren(s1,e,s2) ->
          C.mk_paren old_l
            s1 (trans e) s2
            old_t
      | Begin(s1,e,s2) ->
          C.mk_begin old_l
            s1 (trans e) s2
            old_t
      | If(s1,e1,s2,e2,s3,e3) ->
          C.mk_if old_l
            s1 (trans e1) s2 (trans e2) s3 (trans e3)
            old_t
      | Set(s1,es,s2) ->
          C.mk_set old_l
            s1 (Seplist.map trans es) s2
            (exp_to_typ e)
      | Setcomp(s1,e1,s2,e2,s3,b) ->
          C.mk_setcomp old_l
            s1 (trans e1) s2 (trans e2) s3 b
            old_t
      | Comp_binding(is_lst,s1,e1,s2,s3,qbs,s4,e2,s5) ->
          C.mk_comp_binding old_l
            is_lst s1 (trans e1) s2 s3 qbs s4 (trans e2) s5
            old_t
      | Quant(q,qbs,s,e) ->
          C.mk_quant old_l
            q
            (List.map
               (function
                  | Qb_var(n) -> Qb_var(n)
                  | Qb_restr(is_lst,s1,n,s2,e,s3) ->
                      Qb_restr(is_lst,s1,n,s2,trans e,s3))
               qbs)
            s
            (trans e)
            old_t
      | Constructor(c) ->
          C.mk_constr old_l (id_fix_parens_for_prefix (fun x -> x.constr_binding) get_prec c) old_t
      | Constant(c) ->
          C.mk_const old_l (id_fix_parens_for_prefix (fun x -> x.const_binding) get_prec c) old_t
      | Var(n) ->
          C.mk_var old_l (name_fix_parens_for_prefix get_prec n) (exp_to_typ e) 
      | Lit _  | Nvar_e _ ->
          e

and skip_apps get_prec e = match (C.exp_to_term e) with
  | App(e1,e2) ->
      C.mk_app (exp_to_locn e)
        (C.delimit_exp get_prec P.App_left (skip_apps get_prec e1))
        (C.delimit_exp get_prec P.App_right (fix_exp get_prec e2))
        (Some(exp_to_typ e))
  | _ -> fix_exp get_prec e

and fix_letbind get_prec (lb,l) = match lb with
  | Let_val(p,topt,s,e) ->
      C.mk_let_val l
        (fix_pat get_prec p) topt s (fix_exp get_prec e)
  | Let_fun(n,ps,t,s1,e) -> 
      C.mk_let_fun l
        n (List.map (fun p -> delimit_pat P.Plist (fix_pat get_prec p)) ps) t s1 
        (fix_exp get_prec e)

let rec fix_infix_and_parens get_prec defs =
  let fix_val_def = function
    | Let_def(s1,targets,lb) ->
        Let_def(s1, targets,fix_letbind get_prec lb)
    | Rec_def(s1,s2,targets,clauses) ->
        Rec_def(s1,
                s2,
                targets,
                Seplist.map
                  (fun (nl,ps,topt,s3,e) -> 
                     (nl, List.map (fun p -> fix_pat get_prec p) ps,
                      topt,s3,fix_exp get_prec e))
                  clauses)
    | let_inline -> let_inline
  in
  let rec fix_def = function
    | Val_def(d,tnvs,class_constraints) -> Val_def(fix_val_def d,tnvs,class_constraints)
    | Lemma(sk,lty,targets,n_opt,sk2,e,sk3) -> Lemma(sk,lty,targets,n_opt,sk2,fix_exp get_prec e,sk3)
    | Indreln(s1,targets,c) ->
        Indreln(s1,
                targets,
                Seplist.map
                  (fun (name_opt,s1,ns,s2,e_opt,s3,n,es) ->
                     (name_opt,s1,ns,s2,
                      Util.option_map (fix_exp get_prec) e_opt, s3, n, 
                      List.map (fix_exp get_prec) es))
                  c)
    | Module(sk1, nl, sk2, sk3, ds, sk4) ->
        Module(sk1, nl, sk2, sk3, List.map (fun ((d,s),l) -> ((fix_def d,s),l)) ds, sk4)
    | Instance(sk1,is,vdefs,sk2,sem_info) ->
        Instance(sk1, is, List.map fix_val_def vdefs, sk2, sem_info)
    | def -> def
  in
    match defs with
      | [] -> []
      | ((def,s),l)::defs ->
          ((fix_def def,s),l)::fix_infix_and_parens get_prec defs

