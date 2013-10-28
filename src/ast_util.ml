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

open Ast
module NameSet = Set.Make(Name)

let emp = NameSet.empty

let xl_to_name x =
  Name.strip_lskip (Name.from_x x)

let id_vars not_shadowed = function
  | Id([],xl,_) -> 
      let n = xl_to_name xl in
        if not_shadowed n then
          NameSet.singleton n
        else 
          emp
  | Id((xl,_)::_,_,_) -> 
      let n = xl_to_name xl in
        if not_shadowed n then
          NameSet.singleton n
        else 
          emp

let rec pat_vars not_shadowed (Pat_l(p,l)) =
  let pv = pat_vars not_shadowed in
  let psv = pats_vars not_shadowed in
    match p with
      | P_wild _ -> emp
      | P_as(_,p,_,xl,_) ->
          NameSet.add (xl_to_name xl) (pv p)
      | P_typ(_,p,_,_,_) ->
          pv p
      | P_app(id, []) ->
          id_vars not_shadowed id
      | P_app(id,ps) ->
          psv ps
      | P_record(_,fieldpats,_,_,_) ->
          psv (List.map (fun (Fpat(_,_,p,_),_) -> p) fieldpats)
      | P_tup(_,ps,_) ->
          psv (List.map fst ps)
      | P_list(_,ps,_,_,_) | P_vector(_,ps,_,_,_) ->
          psv (List.map fst ps)
      | P_paren(_,p,_) ->
          pv p
      | P_num_add(xl,_,_,_) ->
          NameSet.add (xl_to_name xl) emp
      | P_cons(p1,_,p2) ->
          NameSet.union (pv p1) (pv p2)
      | P_lit _ -> emp
      | P_vectorC(_,ps,_) ->
          psv ps

and pats_vars not_shadowed ps =
  List.fold_right (fun p r -> NameSet.union (pat_vars not_shadowed p) r) ps emp

let rec setcomp_bindings not_shadowed (Expr_l(e,l)) =
  let scb = setcomp_bindings not_shadowed in
  let scb_list = setcomp_bindings_list not_shadowed in
    match e with
      | Ident(id) -> id_vars not_shadowed id
      | Backend _ -> NameSet.empty
      | Fun(_,Patsexp(ps,_,e,_)) ->
          NameSet.diff 
            (scb e)
            (pats_vars not_shadowed ps)
      | Function(_,_,_,pes,_) ->
          List.fold_right
            (fun (Patexp(p,_,e,_),_) s ->
               NameSet.union (NameSet.diff (scb e) (pat_vars not_shadowed p)) s)
            pes
            emp
      | App(e1,e2) ->
          NameSet.union (scb e1) (scb e2)
      | Infix(e1,SymX_l((_,op),_),e2) ->
          let s = NameSet.union (scb e1) (scb e2) in
          let n = Name.from_rope op in
            if not_shadowed n then
              NameSet.add n s
            else 
              s
      | Record(_,(Fexps(fexpr_terms,_,_,_)),_) ->
          scb_list (List.map (fun (Fexp(_,_,e,_),_) -> e) fexpr_terms)
      | Recup(_,e,_,(Fexps(fexpr_terms,_,_,_)),_) ->
          NameSet.union
            (scb e)
            (scb_list (List.map (fun (Fexp(_,_,e,_),_) -> e) fexpr_terms))
      | Field(e,_,_) ->
          scb e
      | Case(_,e,_,_,_,patexprs,_,_) ->
          List.fold_right 
            (fun (Patexp(p,_,e,_),_) s -> NameSet.union (NameSet.diff (scb e) (pat_vars not_shadowed p)) s) 
            patexprs 
            (scb e)
      | Typed(_,e,_,_,_) ->
          scb e
      | Let(_,Letbind(lb,_),_,e) ->
          let (fv,binds) = letbind_freevars not_shadowed lb in
            NameSet.union fv (NameSet.diff (scb e) binds)
      | Tup(_,es,_) ->
          scb_list (List.map fst es)
      | Elist(_,es,_,_,_) | Vector(_,es,_,_,_) ->
          scb_list (List.map fst es)
      | VAccess(e,_,_,_) | VAccessR(e,_,_,_,_,_) ->
          scb e
      | Paren(_,e,_) ->
          scb e
      | Begin(_,e,_) ->
          scb e
      | If(_,e1,_,e2,_,e3) ->
          NameSet.union (scb e1) (NameSet.union (scb e2) (scb e3))
      | Cons(e1,_,e2) ->
          NameSet.union (scb e1) (scb e2)
      | Lit _ | Nvar _ ->
          emp
      | Set(_,es,_,_,_) ->
          scb_list (List.map fst es)
      | Setcomp(_,e1,_,e2,_) ->
          emp
      | Setcomp_binding(_,e1,_,_,qbs,_,e2,_) ->
          setcomp_bindings_qbs not_shadowed qbs (NameSet.union (scb e1) (scb e2))
      | Quant(q,qbs,_,e) ->
          setcomp_bindings_qbs not_shadowed qbs (scb e)
      | Listcomp(_,e1,_,_,qbs,_,e2,_) ->
          setcomp_bindings_qbs not_shadowed qbs (NameSet.union (scb e1) (scb e2))
      | Do(_,_,lns,_,e,_) ->
          setcomp_bindings_lns not_shadowed lns (scb e) 

and setcomp_bindings_lns not_shadowed =
  List.fold_right
    (fun line s ->
       match line with
         | (p,_,e,_) ->
             NameSet.union (setcomp_bindings not_shadowed e) (NameSet.diff s (pat_vars not_shadowed p)))

and setcomp_bindings_qbs not_shadowed =
  List.fold_right
    (fun qb s ->
       match qb with
         | Qb_var(xl) ->
             NameSet.remove (xl_to_name xl) s
         | Qb_restr(_,p,_,e,_) | Qb_list_restr(_,p,_,e,_) ->
             NameSet.union (setcomp_bindings not_shadowed e) (NameSet.diff s (pat_vars not_shadowed p)))

and setcomp_bindings_list not_shadowed es =
  List.fold_right (fun e r -> NameSet.union (setcomp_bindings not_shadowed e) r) es emp

and letbind_freevars not_shadowed = function
  | Let_val(p,_,_,e) -> (setcomp_bindings not_shadowed e, pat_vars not_shadowed p)
  | Let_fun(Funcl(xl,ps,_,_,e)) ->
      (NameSet.diff (setcomp_bindings not_shadowed e) (pats_vars not_shadowed ps),
       NameSet.singleton (xl_to_name xl))


let get_imported_modules_of_def_aux l = function
  | Open_import ((OI_import _ | OI_open_import _ | OI_include_import _), ids) ->
      List.map (fun id -> (Path.from_id (Ident.from_id id), l)) ids
  | _ -> [] 
  
let get_imported_modules (Defs ds, _) =
  List.flatten (List.map (fun (Def_l (d, l), _, _) -> get_imported_modules_of_def_aux l d) ds)
