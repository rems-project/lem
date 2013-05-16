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

(* Traversing expressions to resolve any target problems that will arise from
 * its binding and module structure and namespaces being different from Lem's *)

open Typed_ast

module M = Macro_expander.Expander(struct let avoid = None let env_opt = None end)
module C = Exps_in_context(struct let avoid = None let env_opt = None end)
module P = Precedence

(* TODO: This needs to be much more complex to be really right *)
let id_fix_binding target id =
  match id.id_path with
    | Id_none _ -> id
    | Id_some p -> 
        { id with id_path = Id_some (Ident.strip_path target p) }

let rec fix_src_t target t =
  match t.term with
    | Typ_wild _ | Typ_var _ -> t
    | Typ_fn(t1,sk,t2) -> 
        { t with term = Typ_fn(fix_src_t target t1, sk, fix_src_t target t2) }
    | Typ_tup(ts) -> 
        { t with term = Typ_tup(Seplist.map (fix_src_t target) ts) }
    | Typ_app(id,ts) ->
        { t with term = 
            Typ_app(id_fix_binding target id, List.map (fix_src_t target) ts) }
    | Typ_len(n) -> t
    | Typ_paren(sk1,t',sk2) -> 
        { t with term = Typ_paren(sk1, fix_src_t target t', sk2) }


let rec fix_pat target p = 
  let old_t = Some(p.typ) in
  let old_l = p.locn in
  let trans = fix_pat target in
    match p.term with
      | P_as(sk1,p,s,nl,sk2) -> 
          C.mk_pas old_l sk1 (trans p) s nl sk2 old_t
      | P_typ(s1,p,s2,t,s3) -> 
          C.mk_ptyp old_l s1 (trans p) s2 (fix_src_t target t) s3 old_t
      | P_const(c,ps) -> 
          C.mk_pconst old_l (id_fix_binding target c) (List.map trans ps) old_t
      | P_record(s1,fieldpats,s2) ->
          C.mk_precord old_l
            s1 
            (Seplist.map 
               (fun (fid,s1,p) -> (id_fix_binding target fid,s1,trans p))
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
          C.mk_pcons old_l (trans p1) s (trans p2) old_t
      | P_num_add _ -> p
      | P_var _ | P_var_annot _ | P_lit _ | P_wild _ ->
          p


let rec fix_exp target e = 
  let trans = fix_exp target in 
  let transp = fix_pat target in
  let old_t = Some(exp_to_typ e) in
  let old_l = exp_to_locn e in
    match (C.exp_to_term e) with
      | Fun(s1,ps,s2,e) ->
          C.mk_fun old_l s1 (List.map transp ps) s2 (trans e) old_t
      | Function(s1,pes,s2) ->
          C.mk_function old_l
            s1 (Seplist.map 
                  (fun (p,s1,e,l) -> (transp p,s1,trans e,l))
                  pes)
            s2
            old_t
      | App(e1,e2) ->
          C.mk_app old_l (trans e1) (trans e2) old_t
      | Infix(e1,e2,e3) ->
          C.mk_infix old_l (trans e1) (trans e2) (trans e3) old_t
      | Record(s1,fieldexps,s2) ->
          C.mk_record old_l
            s1
            (Seplist.map 
               (fun (fid,s1,e,l) -> (id_fix_binding target fid,s1,trans e,l))
               fieldexps)
            s2
            old_t
(*      | Record_coq(n,s1,fieldexps,s2) ->
          C.mk_record_coq old_l
            s1
            (Seplist.map 
               (fun (fid,s1,e,l) -> (id_fix_binding target fid,s1,trans e,l))
               fieldexps)
            s2
            old_t*)
      | Recup(s1,e,s2,fieldexps,s3) ->
          C.mk_recup old_l
            s1 (trans e) s2
            (Seplist.map 
               (fun (fid,s1,e,l) -> (id_fix_binding target fid,s1,trans e,l))
               fieldexps)
            s3
            old_t
      | Field(e,s,fid) ->
          C.mk_field old_l (trans e) s (id_fix_binding target fid) old_t
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
            s1 (trans e) s2 (fix_src_t target t) s3
            old_t
      | Let(s1,letbind,s2,e) ->
          C.mk_let old_l
            s1 (fix_letbind target letbind) s2 (trans e)
            old_t
      | Tup(s1,es,s2) ->
          C.mk_tup old_l
            s1 (Seplist.map trans es) s2
            old_t
      | List(s1,es,s2) ->
          C.mk_list old_l
            s1 (Seplist.map trans es) s2
            (exp_to_typ e)
      | Vector(s1,es,s2) ->
         C.mk_vector old_l s1 (Seplist.map trans es) s2 (exp_to_typ e)
      | VectorAcc(e,s1,n,s2) ->
         C.mk_vaccess old_l (trans e) s1 n s2 (exp_to_typ e)
      | VectorSub(e,s1,n1,s2,n2,s3) ->
         C.mk_vaccessr old_l (trans e) s1 n1 s2 n2 s3 (exp_to_typ e)
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
      (* TODO: Why is qbs ignored *)
      | Comp_binding(is_lst,s1,e1,s2,s3,qbs,s4,e2,s5) ->
          C.mk_comp_binding old_l
            is_lst s1 (trans e1) s2 s3 qbs s4 (trans e2) s5
            old_t
      (* TODO: Why is lns ignored *)
      | Do(s1,mid,lns,s2,e,s3,ret_t) ->
          C.mk_do old_l s1 mid lns s2 (trans e) s3 ret_t old_t
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
      | Constant(c) ->
          C.mk_const old_l (id_fix_binding target c) old_t
      | Var _ | Lit _  | Nvar_e _ ->
          e

and fix_letbind target (lb,l) = match lb with
  | Let_val(p,topt,s,e) ->
      C.mk_let_val l
        (fix_pat target p) topt s (fix_exp target e)
  | Let_fun(n,ps,t,s1,e) -> 
      C.mk_let_fun l
        n (List.map (fix_pat target) ps) t s1 
        (fix_exp target e)

let rec fix_binding target defs =
  let fix_val_def = function
    | Let_def(s1,targets,lb) ->
        Let_def(s1, targets,fix_letbind target lb)
    | Rec_def(s1,s2,targets,clauses) ->
        Rec_def(s1,
                s2,
                targets,
                Seplist.map
                  (fun (nl,ps,topt,s3,e) -> 
                     (nl, List.map (fun p -> fix_pat target p) ps,
                      topt,s3,fix_exp target e))
                  clauses)
    | let_inline -> let_inline
  in
  let rec fix_def = function
    | Val_def(d,tnvs,class_constraints) -> Val_def(fix_val_def d,tnvs,class_constraints)
    | Lemma(sk,lty,targets,n_opt,sk2,e,sk3) -> Lemma(sk,lty,targets,n_opt,sk2,fix_exp target e,sk3)
    | Indreln(s1,targets,c) ->
        Indreln(s1,
                targets,
                Seplist.map
                  (fun (name_opt,s1,ns,s2,e_opt,s3,n,es) ->
                     (name_opt,s1,ns,s2,Util.option_map (fix_exp target) e_opt, s3, n, 
                      List.map (fix_exp target) es))
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
          ((fix_def def,s),l)::fix_binding target defs

