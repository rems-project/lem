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

type level = 
  | Top_level
  | Nested

type pat_pos = 
  | Bind
  | Param

type pat_position = level * pat_pos

let rec list_to_mac = function
  | [] -> (fun e -> None)
  | m1::ms ->
      let ms_f = list_to_mac ms in
        (fun e ->
           match m1 e with
             | None -> ms_f e
             | Some(e) -> Some(e))

let rec list_to_bool_mac = function
  | [] -> (fun b e -> None)
  | m1::ms ->
      let ms_f = list_to_bool_mac ms in
        (fun b e ->
           match m1 b e with
             | None -> ms_f b e
             | Some(e) -> Some(e))


module Expander(C : Exp_context) = struct

(* Using the checks here adds significant overhead *)
module C = Exps_in_context(C)

let expand_annot_typ typ_r (a : ('a,'b) annot) = 
  let typ' = typ_r a.typ in { a with typ = typ' }

let rec expand_pat pat_pos p (typ_r, src_typ_r, r) : pat = 
  let trans p = expand_pat pat_pos p (typ_r, src_typ_r, r) in 
  let new_t = typ_r p.typ in
  let old_l = p.locn in
    match r pat_pos p with
      | Some(p') -> trans p'
      | None ->
          match p.term with
            | P_as(s1,p,s2,nl,s3) -> 
                C.mk_pas old_l s1 (trans p) s2 nl s3 (Some new_t)
            | P_typ(s1,p,s2,t,s3) -> 
                C.mk_ptyp old_l s1 (trans p) s2 t s3 (Some new_t)
            | P_constr(c,ps) -> 
                C.mk_pconstr old_l 
                  c 
                  (List.map (fun p -> (trans p)) ps)
                  (Some new_t)
            | P_record(s1,fieldpats,s2) ->
                C.mk_precord old_l
                  s1 
                  (Seplist.map 
                     (fun (fid,s1,p) -> (fid,s1,trans p))
                     fieldpats)
                  s2
                  (Some new_t)
            | P_tup(s1,ps,s2) -> 
                C.mk_ptup old_l s1 (Seplist.map trans ps) s2 (Some new_t)
            | P_list(s1,ps,s2) -> 
                C.mk_plist old_l s1 (Seplist.map trans ps) s2 new_t
            | P_vector(s1,ps,s2) ->
                C.mk_pvector old_l s1 (Seplist.map trans ps) s2 new_t
            | P_vectorC(s1,ps,s2) ->
                C.mk_pvectorc old_l s1 (List.map trans ps) s2 new_t
            | P_paren(s1,p,s2) -> 
                C.mk_pparen old_l s1 (trans p) s2 (Some new_t)
            | P_cons(p1,s,p2) -> 
                C.mk_pcons old_l (trans p1) s (trans p2) (Some new_t)
            | P_var _ ->
                { p with typ = new_t }
            | P_var_annot (n, ty) ->
                { p with typ = new_t; term = P_var_annot (n, src_typ_r ty) }
            | P_num_add _ -> 
                { p with typ = new_t }
            | (P_lit _ | P_wild _) ->
                { p with typ = new_t }


let rec expand_exp ((r,typ_r,src_typ_r,pat_r):((exp -> exp option) * (Types.t -> Types.t) * (src_t -> src_t) * (pat_position -> pat -> pat option))) (e : exp) : exp = 
  let trans = expand_exp (r,typ_r,src_typ_r,pat_r) in 
  let transp b p = expand_pat (Nested, b) p (typ_r, src_typ_r, pat_r) in
  let new_t = typ_r (exp_to_typ e) in
  let old_l = exp_to_locn e in
    match r e with
      | Some(e') -> 
          begin
            C.type_eq old_l "expand_exp" (exp_to_typ e) (exp_to_typ e');
            trans e'
          end
      | None ->
          begin
            match (C.exp_to_term e) with
              | Tup_constructor(c,s1,es,s2) ->
                  C.mk_tup_ctor old_l 
                    c 
                    s1 (Seplist.map trans es) s2 (Some new_t)
              | Fun(s1,ps,s2,e) ->
                  C.mk_fun old_l 
                    s1 (List.map (fun p -> transp Param p) ps) 
                    s2 (trans e)
                    (Some new_t)
              | Function(s1,pes,s2) ->
                  C.mk_function old_l
                    s1 (Seplist.map 
                          (fun (p,s1,e,l) -> (transp Param p,s1,trans e,l))
                          pes)
                    s2
                    (Some new_t)
              | App(e1,e2) ->
                  C.mk_app old_l
                    (skip_apps (r,typ_r,src_typ_r,pat_r) e1)
                    (trans e2)
                    (Some new_t)
              | Infix(e1,e2,e3) ->
                  C.mk_infix old_l (trans e1) (trans e2) (trans e3) (Some new_t)
              | Record(s1,fieldexps,s2) ->
                  C.mk_record old_l
                    s1
                    (Seplist.map 
                       (fun (fid,s1,e,l) -> (fid,s1,trans e,l))
                       fieldexps)
                    s2
                    (Some new_t)
              | Record_coq(n,s1,fieldexps,s2) ->
                  C.mk_record_coq old_l
                    s1
                    (Seplist.map 
                       (fun (fid,s1,e,l) -> (fid,s1,trans e,l))
                       fieldexps)
                    s2
                    (Some new_t)
              | Recup(s1,e,s2,fieldexps,s3) ->
                  C.mk_recup old_l
                    s1 (trans e) s2
                    (Seplist.map 
                       (fun (fid,s1,e,l) -> (fid,s1,trans e,l))
                       fieldexps)
                    s3
                    (Some new_t)
              | Field(e,s,fid) ->
                  C.mk_field old_l 
                    (trans e) s fid
                    (Some new_t)
              | Case(c,s1,e,s2,patexps,s3) ->
                  C.mk_case false old_l
                    s1 (trans e) s2
                    (Seplist.map
                       (fun (p,s1,e,l) -> (transp Bind p,s1,trans e,l))
                       patexps)
                    s3
                    (Some new_t)
              | Typed(s1,e,s2,t,s3) ->
                  C.mk_typed old_l 
                    s1 (trans e) s2 t s3
                    (Some new_t)
              | Let(s1,letbind,s2,e) ->
                  C.mk_let old_l
                    s1 (expand_letbind (Nested,Bind) (r,typ_r,src_typ_r,pat_r) letbind) s2 (trans e)
                    (Some new_t)
              | Tup(s1,es,s2) ->
                  C.mk_tup old_l
                    s1 (Seplist.map trans es) s2
                    (Some new_t)
              | List(s1,es,s2) ->
                  C.mk_list old_l
                    s1 (Seplist.map trans es) s2
                    new_t
              | Vector(s1,es,s2) ->
                  C.mk_vector old_l
                    s1 (Seplist.map trans es) s2
                    new_t
              | VectorAcc(e1,s1,n,s2) ->
                 C.mk_vaccess old_l (trans e1) s1 n s2 new_t
              | VectorSub(e,s1,n1,s2,n2,s3) ->
                 C.mk_vaccessr old_l (trans e) s1 n1 s2 n2 s3 new_t
              | Paren(s1,e,s2) ->
                  C.mk_paren old_l
                    s1 (trans e) s2
                    (Some new_t)
              | Begin(s1,e,s2) ->
                  C.mk_begin old_l
                    s1 (trans e) s2
                    (Some new_t)
              | If(s1,e1,s2,e2,s3,e3) ->
                  C.mk_if old_l
                    s1 (trans e1) s2 (trans e2) s3 (trans e3)
                    (Some new_t)
              | Set(s1,es,s2) ->
                  C.mk_set old_l
                    s1 (Seplist.map trans es) s2
                    new_t
              | Setcomp(s1,e1,s2,e2,s3,b) ->
                  C.mk_setcomp old_l
                    s1 (trans e1) s2 (trans e2) s3 b
                    (Some new_t)
              | Comp_binding(is_lst,s1,e1,s2,s3,qbs,s4,e2,s5) ->
                  C.mk_comp_binding old_l
                    is_lst s1 (trans e1) s2 s3 qbs s4 (trans e2) s5
                    (Some new_t)
              | Quant(q,qbs,s,e) ->
                  C.mk_quant old_l
                    q
                    (List.map
                       (function
                          | Qb_var(n) -> Qb_var(n)
                          | Qb_restr(is_lst,s1,n,s2,e,s3) ->
                              Qb_restr(is_lst,s1,transp Bind n,s2,trans e,s3))
                       qbs)
                    s
                    (trans e)
                    (Some new_t)
              | Constructor(c) ->
                  C.mk_constr old_l c (Some new_t)
              | Constant(c) ->
                  C.mk_const old_l c (Some new_t)
              | Var(n) ->
                  C.mk_var old_l n new_t
              | Nvar_e(s,n) -> C.mk_nvar_e old_l s n new_t
              | Lit li  ->
                  C.mk_lit old_l  {li with Typed_ast.typ = new_t} (Some new_t)
          end

and skip_apps (r,typ_r,src_typ_r,pat_r) e = match (C.exp_to_term e) with
  | App(e1,e2) ->
      C.mk_app (exp_to_locn e)
        (skip_apps (r,typ_r,src_typ_r,pat_r) e1)
        (expand_exp (r,typ_r,src_typ_r,pat_r) e2)
        (Some(typ_r (exp_to_typ e)))
  | _ -> expand_exp (r,typ_r,src_typ_r,pat_r) e

and expand_letbind (level,_) (r,typ_r,src_typ_r,pat_r) (lb,l) = match lb with
  | Let_val(p,topt,s,e) ->
      let topt' = Util.option_map (fun (s, ty) -> (s, src_typ_r ty)) topt in
      C.mk_let_val l
        (expand_pat (level,Bind) p (typ_r, src_typ_r, pat_r)) topt' s (expand_exp (r,typ_r, src_typ_r, pat_r) e)
  | Let_fun(n,ps,t,s1,e) -> 
      C.mk_let_fun l
        (expand_annot_typ typ_r n)
        (List.map (fun p -> expand_pat (level,Param) p (typ_r, src_typ_r, pat_r)) ps) t s1 
        (expand_exp (r,typ_r,src_typ_r,pat_r) e)

let rec expand_defs defs ((r,typ_r,src_typ_r,pat_r):((exp -> exp option) * (Types.t -> Types.t) * (src_t -> src_t) * (pat_position -> pat -> pat option))) =
  let expand_val_def = function
    | Let_def(s1,targets,lb) ->
        Let_def(s1, targets, expand_letbind (Top_level,Bind) (r, typ_r, src_typ_r, pat_r) lb)
    | Rec_def(s1,s2,targets,clauses) ->
        Rec_def(s1,
                s2,
                targets,
                Seplist.map
                  (fun (nl,ps,topt,s3,e) -> 
                     (nl,
                      List.map 
                        (fun p -> expand_pat (Top_level,Param) p (typ_r, src_typ_r, pat_r))
                        ps,
                      topt,s3,expand_exp (r,typ_r,src_typ_r,pat_r) e))
                  clauses)
    | let_inline -> let_inline
  in
  let rec expand_def = function
    | Val_def(d,tnvs,class_constraints) -> Val_def(expand_val_def d,tnvs,class_constraints)
    | Lemma(sk,lty,n_opt,e) -> Lemma(sk,lty,n_opt, expand_exp (r,typ_r,src_typ_r,pat_r) e)
    | Indreln(s1,targets,c) ->
        Indreln(s1,
                targets,
                Seplist.map
                  (fun (name_opt,s1,ns,s2,e_opt,s3,n,es) ->
                     (name_opt,
                      s1,
                      List.map (expand_annot_typ typ_r) ns,
                      s2,
                      Util.option_map (expand_exp (r,typ_r,src_typ_r,pat_r)) e_opt, s3, 
                      expand_annot_typ typ_r n, 
                      List.map (expand_exp (r,typ_r,src_typ_r,pat_r)) es))
                  c)
    | Module(sk1, nl, sk2, sk3, ds, sk4) ->
        Module(sk1, nl, sk2, sk3, List.map (fun ((d,s),l) -> ((expand_def d,s),l)) ds, sk4)
    | Instance(sk1,is,vdefs,sk2,sem_info) ->
        Instance(sk1, is, List.map expand_val_def vdefs, sk2, sem_info)
    | def -> def
  in
    match defs with
      | [] -> []
      | ((def,s),l)::defs ->
          ((expand_def def,s),l)::expand_defs defs (r,typ_r,src_typ_r,pat_r)
end
