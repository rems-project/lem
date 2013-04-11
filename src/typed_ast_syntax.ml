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

let r = Ulib.Text.of_latin1
let space = Some [Ast.Ws (r" ")]
let new_line = Some [Ast.Ws (r"\n")]

module C = Exps_in_context(struct let check = None let avoid = None end)

let bool_ty = { Types.t = Types.Tapp ([], Path.boolpath) }
let num_ty  = { Types.t = Types.Tapp ([], Path.numpath)  }

let rec dest_var_exp (e :exp) : Name.t option =
  match C.exp_to_term e with
    Var n -> Some (Name.strip_lskip n)
  | Typed (_, e', _, _, _) -> dest_var_exp e'
  | Paren (_, e', _) -> dest_var_exp e'
  | _ -> None

let is_var_exp e = not (dest_var_exp e = None)

let rec dest_tup_exp (lo : int option) (e :exp) : exp list option =
  match C.exp_to_term e with
  | Tup (_, sl, _) -> begin
      let l = Seplist.to_list sl in
      match lo with None -> Some l
        | Some len -> if List.length l = len then Some l else None
    end
  | _ -> None

let is_tup_exp lo e = not (dest_tup_exp lo e = None)

let rec is_var_tup_exp e = is_var_exp e ||
  (match dest_tup_exp None e with None -> false | Some eL ->
     List.for_all is_var_tup_exp eL)

let mk_tf_exp b =
  let l = Ast.Trans ("mk_tf_exp", None) in
  let lit = C.mk_lbool l None b (Some bool_ty) in
  let exp = C.mk_lit l lit (Some bool_ty) 
in exp

let dest_tf_exp e =
  match C.exp_to_term e with
      Lit l -> (match l.term with L_true _ -> Some true | L_false _ -> Some false | _ -> None)
    | _ -> None

let is_tf_exp b e = (dest_tf_exp e = Some b)

let dest_num_exp e =
  match C.exp_to_term e with
      Lit l -> (match l.term with L_num (_,i) -> Some i | _ -> None)
    | _ -> None

let is_num_exp e = not (dest_tf_exp e = None)

let mk_num_exp i = 
  let l = Ast.Trans ("mk_num_exp", None) in
  let lit = C.mk_lnum l None i (Some num_ty) in
  C.mk_lit l lit (Some num_ty)

let rec replace_init_ws nws ws =
  let rec aux rws ws =
    match ws with 
      | None -> (nws, rws)
      | Some [] -> (nws, rws)
      | Some (Ast.Com _ :: _) -> (Ast.combine_lex_skips nws ws, rws)
      | Some (x :: l) -> aux (Ast.combine_lex_skips rws (Some [x])) (Some l)
  in aux None ws

let remove_init_ws ws =
  replace_init_ws None ws

let space_com_init_ws ws =
  replace_init_ws space ws

let drop_init_ws ws = (None, ws)
let space_init_ws ws = (space, ws)

let mk_paren_exp e =
     let (e', ws) = alter_init_lskips remove_init_ws e in
     C.mk_paren (exp_to_locn e) ws e' None (Some (exp_to_typ e))

let mk_opt_paren_exp (e :exp) : exp =
  match C.exp_to_term e with
    | Var _ -> e
    | Constant _ -> e
    | Constructor _ -> e
    | Tup _ -> e
    | Paren _ -> e
    | Lit _ -> e
    | _ -> mk_paren_exp e


let mk_case_exp final (l:Ast.l) (in_e : exp) (rows : (pat * exp) list) (ty : Types.t) : exp =
  let loc = Ast.Trans ("mk_case_exp", Some l) in
  let rows_sep_list = Seplist.from_list (List.map (fun (p,e) -> ((pat_append_lskips space p, space, fst (alter_init_lskips space_init_ws e), loc), space)) rows) in
  C.mk_case final loc None in_e space rows_sep_list space (Some ty)

let mk_case_exp_new_line final (l:Ast.l) (in_e : exp) (rows : (pat * exp) list) (ty : Types.t) : exp =
  let loc = Ast.Trans ("mk_case_exp", Some l) in
  let case_space = Some [Ast.Ws (r"\n  ")] in
  let rows_sep_list = Seplist.from_list (List.map (fun (p,e) -> ((pat_append_lskips space p, space, fst (alter_init_lskips space_init_ws e), loc), case_space)) rows) in
  C.mk_case final loc new_line in_e space rows_sep_list new_line (Some ty)

let mk_let_exp (l:Ast.l) ((n: Name.t), (e1:exp)) (e2:exp) : exp =
  let loc = Ast.Trans ("mk_let_exp", Some l) in

  let (e1'', _) = alter_init_lskips remove_init_ws e1 in
  let e1' = append_lskips space e1'' in
  let (e2', _) = alter_init_lskips remove_init_ws e2 in
  let let_val = C.mk_let_val loc (C.mk_pvar loc (Name.add_lskip n) (exp_to_typ e1)) None space e1' in
  let let_exp = C.mk_let loc None let_val space e2' (Some (exp_to_typ e2))
  in let_exp

let mk_if_exp loc e_c e_t e_f =
  C.mk_if loc space (mk_opt_paren_exp e_c) space (mk_opt_paren_exp e_t) space (mk_opt_paren_exp e_f) (Some (exp_to_typ e_t)) 

let mk_undefined_exp l m ty = begin
   let lit = C.mk_lundef l space m ty in
   let exp = C.mk_lit l lit (Some ty) in
   exp end

(* Sometimes dummy expressions are needed during checking the properties
   of a match expression. Undef is a simple way to create those.
   These dummy-expressions are just be used internally and should never
   appear in the output. Any expression of the right type as a result would
   be fine.  *)
let mk_dummy_exp ty = mk_undefined_exp Ast.Unknown "Dummy expression" ty

let rec lookup_env e mp = match mp with
  | [] -> e
  | n::nl ->
      match Nfmap.apply e.m_env n with
        | None -> (
            let nL = NameSet.elements (nfmap_domain e.m_env) in
            let sL = List.map (fun n -> ("'" ^ (Name.to_string n) ^ "'")) nL in
            let s = String.concat ", " sL in
            (raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal (Ast.Unknown, 
                  "lookup_env failed to find '" ^ (Name.to_string n) ^"' in [" ^ s ^"]")))))
        | Some(e) -> lookup_env e.mod_env nl

let names_get_const env mp n =
  let env' = lookup_env env mp in
  match Nfmap.apply env'.v_env n with
      | Some(Val d) -> d
      | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(Ast.Unknown, "names_get_const env did not contain constant!")))

let get_const env mp n =
  names_get_const env (List.map (fun n -> (Name.from_rope (r n))) mp) (Name.from_rope (r n))


let names_mk_ident l i loc =
  Ident.mk_ident (List.map (fun r -> (Name.add_lskip r, None)) l)
    (Name.add_lskip i)
    loc

let mk_ident l i loc =
  names_mk_ident (List.map (fun n -> Name.from_rope (r n)) l) (Name.from_rope (r i)) loc

let get_const_id env l mp n inst =
{ id_path = Id_some (mk_ident mp n l);
  id_locn = l;
  descr = (get_const env mp n);
  instantiation = inst }

let mk_const_exp env l mp n inst =
  let c = (get_const_id env l mp n inst) in
  let t = Types.type_subst 
             (Types.TNfmap.from_list2 c.descr.const_tparams c.instantiation) 
             c.descr.const_type in
  C.mk_const l c (Some t)

let mk_eq_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans ("mk_eq", None) in
  let ty = exp_to_typ e1 in  

  let ty_0 = { Types.t = Types.Tfn (ty, bool_ty) } in
  let ty_1 = { Types.t = Types.Tfn (ty, ty_0) } in

  let eq_id = { id_path = Id_some (Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r "="))) l);
                id_locn = l;
                descr = (get_const env ["Ocaml"; "Pervasives"] "=");
                instantiation = [ty] } in

  let eq_exp = C.mk_const l eq_id (Some ty_1) in
  let res = C.mk_infix l e1 eq_exp e2 (Some bool_ty) in
  res

let mk_and_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans ("mk_and_exp", None) in
  let ty_0 = { Types.t = Types.Tfn (bool_ty, bool_ty) } in
  let ty_1 = { Types.t = Types.Tfn (bool_ty, ty_0) } in

  let and_id = { id_path = Id_some (Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r "&&"))) l);
                id_locn = l;
                descr = get_const env ["Pervasives"] "&&";
                instantiation = [] } in

  let and_exp = C.mk_const l and_id (Some ty_1) in
  let res = C.mk_infix l e1 and_exp e2 (Some bool_ty) in
  res

let mk_le_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans ("mk_le_exp", None) in
  let ty_0 = { Types.t = Types.Tfn (num_ty, bool_ty) } in
  let ty_1 = { Types.t = Types.Tfn (num_ty, ty_0) } in

  let le_id = { id_path = Id_some (Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r "<="))) l);
                id_locn = l;
                descr = get_const env ["Pervasives"] "<=";
                instantiation = [] } in

  let le_exp = C.mk_const l le_id (Some ty_1) in
  let res = C.mk_infix l e1 le_exp e2 (Some bool_ty) in
  res

let mk_add_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans ("matrix_compile_mk_add", None) in
  let ty_0 = { Types.t = Types.Tfn (num_ty, num_ty) } in
  let ty_1 = { Types.t = Types.Tfn (num_ty, ty_0) } in

  let add_id = { id_path = Id_some (Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r "+"))) l);
                id_locn = l;
                descr = get_const env ["Pervasives"] "+";
                instantiation = [] } in

  let add_exp = C.mk_const l add_id (Some ty_1) in
  let res = C.mk_infix l e1 add_exp e2 (Some num_ty) in
  res

let mk_sub_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans ("matrix_compile_mk_sub", None) in
  let ty_0 = { Types.t = Types.Tfn (num_ty, num_ty) } in
  let ty_1 = { Types.t = Types.Tfn (num_ty, ty_0) } in

  let sub_id = { id_path = Id_some (Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r "-"))) l);
                id_locn = l;
                descr = get_const env ["Pervasives"] "-";
                instantiation = [] } in

  let sub_exp = C.mk_const l sub_id (Some ty_1) in
  let res = C.mk_infix l e1 sub_exp e2 (Some num_ty) in
  res

let mk_num_add_exp env n i = 
  let l = Ast.Trans ("mk_num_add_exp", None) in
  let e1 = C.mk_var l (Name.add_lskip n) num_ty in
  let e2 = mk_num_exp i in
  let ee = mk_add_exp env e1 e2 in
  mk_opt_paren_exp ee

let mk_num_sub_exp env n i = 
  let l = Ast.Trans ("mk_num_sub_exp", None) in
  let e1 = C.mk_var l  (Name.add_lskip n) num_ty in
  let e2 = mk_num_exp i in
  let ee = mk_sub_exp env e1 e2 in
  mk_opt_paren_exp ee


let mk_from_list_exp env (e : exp) : exp =
  let l = Ast.Trans ("mk_from_list_exp", None) in

  let list_ty = exp_to_typ e in
  let base_ty = match list_ty.Types.t with
          | Types.Tapp([t],_) -> t
          | _ -> raise (Reporting_basic.err_unreachable true l "e not of list-type") in
  let set_ty = { Types.t = Types.Tapp([base_ty],Path.setpath) } in
  
  let from_list_exp = mk_const_exp env l ["Set"] "from_list" [base_ty] in
  let res = C.mk_app l from_list_exp e (Some set_ty) in
  res

let mk_cross_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans ("mk_cross_exp", None) in

  let get_set_type e = match (exp_to_typ e).Types.t with
       | Types.Tapp([t],_) -> t
       | _ -> raise (Reporting_basic.err_unreachable true l "e not of set-type") in

  let e1_ty = get_set_type e1 in
  let e2_ty = get_set_type e2 in
  let pair_ty = { Types.t = Types.Ttup [e1_ty; e2_ty] } in
  let cross_ty = { Types.t = Types.Tapp([pair_ty],Path.setpath) } in
  let aux_ty = { Types.t = Types.Tfn (exp_to_typ e2, cross_ty) } in
  
  let cross_exp = mk_const_exp env l ["Set"] "cross" [e1_ty; e2_ty] in
  let res0 = C.mk_app l cross_exp e1 (Some aux_ty) in
  let res = C.mk_app l res0 e2 (Some cross_ty) in
  res

let mk_set_sigma_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans ("mk_set_sigma_exp", None) in

  let (e1_ty, e2_ty) = match (exp_to_typ e2).Types.t with
       | Types.Tfn(e1_ty, {Types.t = Types.Tapp([e2_ty],_)}) -> (e1_ty, e2_ty)
       | _ -> raise (Reporting_basic.err_unreachable true l "e2 not of type 'a -> set 'b") in

  let pair_ty = { Types.t = Types.Ttup [e1_ty; e2_ty] } in
  let sigma_ty = { Types.t = Types.Tapp([pair_ty],Path.setpath) } in
  let aux_ty = { Types.t = Types.Tfn (exp_to_typ e2, sigma_ty) } in
  
  let union_exp = mk_const_exp env l ["Set"] "set_sigma" [e1_ty; e2_ty] in
  let res0 = C.mk_app l union_exp e1 (Some aux_ty) in
  let res = C.mk_app l res0 e2 (Some sigma_ty) in
  res

let mk_set_filter_exp env (e_P : exp) (e_s : exp) : exp =
  let l = Ast.Trans ("mk_filter_exp", None) in

  let set_ty = match (exp_to_typ e_P).Types.t with
       | Types.Tfn (ty_a, _) -> ty_a
       | _ -> raise (Reporting_basic.err_unreachable true l "e_P not of predicate-type") in
 
  let res_ty = { Types.t = Types.Tapp([set_ty],Path.setpath) } in
  let aux_ty = { Types.t = Types.Tfn (exp_to_typ e_s, res_ty) } in

  let filter_exp = mk_const_exp env l ["Set"] "filter" [set_ty] in
  let res0 = C.mk_app l filter_exp e_P (Some aux_ty) in
  let res = C.mk_app l res0 e_s (Some res_ty) in
  res


let mk_set_image_exp env (e_f : exp) (e_s : exp) : exp =
  let l = Ast.Trans ("mk_image_exp", None) in

  let (ty_a, ty_b) = match (exp_to_typ e_f).Types.t with
       | Types.Tfn (ty_a, ty_b) -> (ty_a, ty_b)
       | _ -> raise (Reporting_basic.err_unreachable true l "e_f not of function-type") in
 
  let res_ty = { Types.t = Types.Tapp([ty_b],Path.setpath) } in
  let aux_ty = { Types.t = Types.Tfn (exp_to_typ e_s, res_ty) } in

  let image_exp = mk_const_exp env l ["Set"] "image" [ty_a; ty_b] in
  let res0 = C.mk_app l image_exp e_f (Some aux_ty) in
  let res = C.mk_app l res0 e_s (Some res_ty) in
  res

let mk_fun_exp (pL : pat list) (e_s : exp) : exp =
  let l = Ast.Trans ("mk_fun_exp", None) in
  let pL' = List.map (fun p -> fst (pat_alter_init_lskips space_com_init_ws p)) pL in
  let res_ty = Types.multi_fun (List.map (fun p -> p.typ) pL) (exp_to_typ e_s) in
  let res = C.mk_fun l space pL' space (mk_opt_paren_exp e_s) (Some res_ty) in
  res

let rec strip_paren_typ_exp (e :exp) : exp =
  match C.exp_to_term e with
    | Paren (s1, e', s2) -> strip_paren_typ_exp e'
    | Typed (s1, e', s2, src_t, s3) -> strip_paren_typ_exp e'
    | _ -> e

let is_recursive_def (((d, _), _) : def) =  
 match d with
  |  Val_def ((Rec_def (_, _, _, sl)), tnvs,class_constraints) -> begin 
       let (_, pL) = Seplist.to_pair_list None sl in

       (* get the names of all newly defined functions *)
       let get_fun_name s ((((nsa, _, _, _, _) : funcl_aux), _)) =
         let n = Name.strip_lskip (nsa.term) in NameSet.add n s in
       let names = List.fold_left get_fun_name NameSet.empty pL in

       (* get the variables used on the rhs / 
          WARNING: in the future this might need changing to all constants, 
                   when the representation of recursive calls changes *)
       let get_rhs_names s ((((_, _, _, _, e) : funcl_aux), _)) =
         NameSet.union (nfmap_domain (C.exp_to_free e)) s in
       let rhs_names = List.fold_left get_rhs_names NameSet.empty pL in

       let is_rec = not (NameSet.is_empty (NameSet.inter names rhs_names)) in
       is_rec
     end
  |  _ -> false


let val_def_get_name d : Name.t option = match d with
  | Val_def (Rec_def (_, _, _, clauses),_,_) -> 
    begin
      match Seplist.to_list clauses with
         | [] -> None
         | (n, _, _, _, _)::_ -> Some (Name.strip_lskip n.term)
    end
  | Val_def (Let_def (_, _,(bind, _)),_,_)->
    begin
    match bind with
      | Let_val(p,_,_,_) ->
        begin
          match p.term with 
            | P_var ns -> Some (Name.strip_lskip ns)
            | _ -> None
        end
      | Let_fun(n, _, _, _, _) ->
          Some (Name.strip_lskip n.term)
    end
  | _ -> None

let is_trans_loc = function
    Ast.Trans _ -> true
  | _ -> false

let is_trans_exp e =
  is_trans_loc (exp_to_locn e)

let is_trans_def (((_, _), l) : def) =  is_trans_loc l

