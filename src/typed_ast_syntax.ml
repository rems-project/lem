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



(* -------------------------------------------------------------------------- *)
(* Auxiliary stuff                                                            *)
(* -------------------------------------------------------------------------- *)

let r = Ulib.Text.of_latin1
let space = Some [Ast.Ws (r" ")]
let new_line = Some [Ast.Ws (r"\n")]

module C = Exps_in_context(struct let env_opt = None let avoid = None end)

let bool_ty = { Types.t = Types.Tapp ([], Path.boolpath) }
let num_ty  = { Types.t = Types.Tapp ([], Path.numpath)  }

let mk_name_lskips_annot l n ty : name_lskips_annot = 
  { term = n;
    locn = l;
    typ = ty;
    rest = (); }

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


(* -------------------------------------------------------------------------- *)
(* navigating environments                                                    *)
(* -------------------------------------------------------------------------- *)

let lookup_env_step (m_env : m_env) (n : Name.t) : mod_descr =
   match Nfmap.apply m_env n with
    | None -> (
        let nL = NameSet.elements (nfmap_domain m_env) in
        let sL = List.map (fun n -> ("'" ^ (Name.to_string n) ^ "'")) nL in
        let s = String.concat ", " sL in
        (raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal (Ast.Unknown, 
              "lookup_env failed to find '" ^ (Name.to_string n) ^"' in [" ^ s ^"]")))))
    | Some(e) -> e


let rec lookup_env (e : local_env) (mp : Name.t list) : local_env = match mp with
  | [] -> e
  | n::nl ->
      let m_d = lookup_env_step e.m_env n in
      lookup_env m_d.mod_env nl

let rec lookup_env_opt (e : local_env) (mp : Name.t list) : local_env option = match mp with
  | [] -> Some e
  | n::nl ->
      Util.option_bind (fun m_d -> lookup_env_opt m_d.mod_env nl) (Nfmap.apply e.m_env n)

let rec lookup_mod_descr (e : local_env) (mp : Name.t list) (n : Name.t) : mod_descr = 
  let e' = lookup_env e mp in lookup_env_step e'.m_env n

let rec lookup_mod_descr_opt (e : local_env) (mp : Name.t list) (n : Name.t) : mod_descr option = 
  Util.option_bind (fun e -> Nfmap.apply e.m_env n) (lookup_env_opt e mp)

let names_get_const (env : env) mp n =
  let l = Ast.Trans ("names_get_const", None) in
  let local_env = lookup_env env.local_env mp in
  let c_ref = match Nfmap.apply local_env.v_env n with
      | Some(d) -> d
      | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "names_get_const: env did not contain constant!"))) in
  let c_d = c_env_lookup l env.c_env c_ref in
  (c_ref, c_d)

let get_const (env : env) mp n =
  names_get_const env (List.map (fun n -> (Name.from_rope (r n))) mp) (Name.from_rope (r n))

let rec names_get_field env mp n =
  let l = Ast.Trans ("names_get_field", None) in
  let local_env = lookup_env env.local_env mp in
  let c_ref = match Nfmap.apply local_env.f_env n with
      | Some(d) -> d
      | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "names_get_field: env did not contain constant!"))) in
  let c_d = c_env_lookup l env.c_env c_ref in
  (c_ref, c_d)

let get_field (env : env) mp n =
  names_get_field env (List.map (fun n -> (Name.from_rope (r n))) mp) (Name.from_rope (r n))

let dest_field_types l env (f : const_descr_ref) =
  let l = Ast.Trans("dest_field_types", Some l) in 
  let f_d = c_env_lookup l env.c_env f in
  let full_type = f_d.const_type in
  match Types.dest_fn_type (Some env.t_env) full_type with
    | Some ({ Types.t = Types.Tapp (t_b_args, t_b_c) }, t_arg) when t_b_args = List.map Types.tnvar_to_type (f_d.const_tparams) -> 
         (t_arg, t_b_c, f_d)
    | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "not a field type")))

let get_field_type_descr l env (f : const_descr_ref) =
  let l = Ast.Trans("get_field_type_descr", Some l) in 
  let (f_field_arg, f_tconstr, f_d) = dest_field_types l env f in
  match Types.Pfmap.apply env.t_env f_tconstr with
    | Some(Types.Tc_type(td)) -> td
    | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "not a field type")))

let get_field_all_fields l env (f : const_descr_ref) : const_descr_ref list =
  let l = Ast.Trans("get_field_all_fields", Some l) in 
  let td = get_field_type_descr l env f in
  match td.Types.type_fields with
    | Some(fl) -> fl
    | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "not a field type")))

let update_const_descr l up c env =
  let l = Ast.Trans("update_const_descr", Some l) in 
  let cd = c_env_lookup l env.c_env c in
  let new_cd = up cd in
  let new_c_env = c_env_update env.c_env c new_cd in
  {env with c_env = new_c_env}

let constant_descr_to_name (targ : Target.target option) (cd : const_descr) : (bool * Name.t) = 
  match Target.Targetmap.apply_opt cd.target_rep targ with
    | Some (CR_rename (l, _, n)) -> (true, n)
    | Some (CR_new_ident (_, _, i)) -> (true, Name.strip_lskip (Ident.get_name i))
    | Some (CR_inline _) -> (false, Path.get_name cd.const_binding)
    | Some (CR_special (_, _, b, n, _, _)) -> (b, n)
    | None -> (true, Path.get_name cd.const_binding)

let type_descr_to_name (targ : Target.target option) (p : Path.t) (td : type_descr) : Name.t = 
  match Target.Targetmap.apply_opt td.Types.type_target_rep targ with
     | None -> Path.get_name p 
     | Some (Types.TR_new_ident (_, _, i)) -> Name.strip_lskip (Ident.get_name i)
     | Some (Types.TR_rename (_, _, n)) -> n


let constant_descr_rename  (targ : Target.target option) (n':Name.t) (l' : Ast.l) (cd : const_descr) : (const_descr * (Ast.l * Name.t) option) option = 
  let rep = Target.Targetmap.apply_opt cd.target_rep targ in
  let rep_info_opt = match rep with
    | Some (CR_rename (l, true, n)) -> Some (CR_rename (l', true, n'), Some (l, n))
    | Some (CR_new_ident (l, true, i)) -> Some (CR_new_ident (l', true, Ident.rename i n'), Some (l, Name.strip_lskip (Ident.get_name i)))
    | Some (CR_special (l, true, sn, n, outf, nl)) -> Some (CR_special (l', true, sn, n', outf, nl) , Some (l, n))
    | None -> Some (CR_rename (l', true, n'), None)
    | _ -> None
  in
  let save_env (cr, d) = begin
    let tr = Target.Targetmap.insert_opt (cd.target_rep) (targ, cr) in
    ({cd with target_rep = tr}, d)
  end in
  Util.option_map save_env rep_info_opt

let type_descr_rename  (targ : Target.target option) (n':Name.t) (l' : Ast.l) (td : type_descr) : (type_descr * (Ast.l * Name.t) option) option = 
  let rep = Target.Targetmap.apply_opt td.type_target_rep targ in
  let rep_info_opt = match rep with
    | Some (TR_rename (l, true, n)) -> Some (TR_rename (l', true, n'), Some (l, n))
    | Some (TR_new_ident (l, true, i)) -> Some (TR_new_ident (l', true, Ident.rename i n'), Some (l, Name.strip_lskip (Ident.get_name i)))
    | None -> Some (TR_rename (l', true, n'), None)
    | _ -> None
  in
  let save_env (tr, d) = begin
    let targ_rep = Target.Targetmap.insert_opt (td.type_target_rep) (targ, tr) in
    ({td with type_target_rep = targ_rep}, d)
  end in
  Util.option_map save_env rep_info_opt

let type_descr_set_ident  (targ : Target.target option) (i:Ident.t) (l' : Ast.l) (td : type_descr) : type_descr option = 
  let rep = Target.Targetmap.apply_opt td.type_target_rep targ in
  let rep_info_opt = match rep with
    | (Some (TR_rename (_, true, _)) | Some (TR_new_ident (_, true, _)) | None) -> 
         Some (TR_new_ident (l', true, i))
    | _ -> None
  in
  let save_env tr = begin
    let targ_rep = Target.Targetmap.insert_opt (td.type_target_rep) (targ, tr) in
    ({td with type_target_rep = targ_rep})
  end in
  Util.option_map save_env rep_info_opt

let type_defs_rename_type l (d : type_defs) (p : Path.t) (t: Target.target) (n : Name.t) : type_defs =
  let l' = Ast.Trans ("type_defs_rename_type", Some l) in
  let up td = begin
    let res_opt = type_descr_rename (Some t) n l td in
    Util.option_map (fun (td, _) -> td) res_opt
  end in
  Types.type_defs_update_tc_type l' d p up

let type_defs_new_ident_type l (d : type_defs) (p : Path.t) (t: Target.target) (i : Ident.t) : type_defs =
  let l' = Ast.Trans ("type_defs_target_type", Some l) in
  let up td = type_descr_set_ident (Some t) i l td in
  Types.type_defs_update_tc_type l' d p up

let const_descr_to_kind (r, d) =
  match d.env_tag with
    | K_field -> Nk_field r
    | K_constr -> Nk_constr r
    | _ -> Nk_const r

let env_apply (env : env) n =
  match Nfmap.apply env.local_env.p_env n with
      Some (p, l) -> Some (Nk_typeconstr p, p, l)
    | None ->
  match Nfmap.apply env.local_env.f_env n with    
      Some r -> 
        let d = c_env_lookup (Ast.Trans ("env_apply", None)) env.c_env r in
        Some (Nk_field r, d.const_binding, d.spec_l)
    | None ->
  match Nfmap.apply env.local_env.v_env n with
      Some r -> 
        let d = c_env_lookup (Ast.Trans ("env_apply", None)) env.c_env r in
        Some (const_descr_to_kind (r, d), d.const_binding, d.spec_l)
    | None -> 
  match Nfmap.apply env.local_env.m_env n with
      Some mod_descr -> 
        let p = mod_descr.mod_binding in
        Some (Nk_module p, p, Ast.Unknown)
    | None -> None;;
    

let set_target_const_rep env path name target rep =
  begin
    let (c_ref, cd) = get_const env path name in
    let new_tr = Target.Targetmap.insert cd.target_rep (target, rep) in
    let new_c_env = c_env_update env.c_env c_ref {cd with target_rep = new_tr} in
    {env with c_env = new_c_env}
  end

let get_const_id (env : env) l mp n inst =
let (c_ref, c_d) = get_const env mp n in
({ id_path = Id_some (Ident.mk_ident_strings mp n);
  id_locn = l;
  descr = c_ref;
  instantiation = inst },
 c_d)



(* -------------------------------------------------------------------------- *)
(* fixing initial representations                                             *)
(* -------------------------------------------------------------------------- *)

let fix_const_descr_ocaml_constr c_d = c_d
  
let fix_const_descr c_d =
  let c_d = fix_const_descr_ocaml_constr c_d in
  c_d

let c_env_store c_env c_d = c_env_store_raw c_env (fix_const_descr c_d)

let c_env_save c_env c_id_opt c_d =
  match c_id_opt with 
    | None -> c_env_store c_env c_d
    | Some c_id -> (c_env_update c_env c_id c_d, c_id)

(* -------------------------------------------------------------------------- *)
(* destruct / check / make expression                                         *)
(* -------------------------------------------------------------------------- *)

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

let mk_paren_exp e =
     let (e', ws) = alter_init_lskips remove_init_ws e in
     C.mk_paren (exp_to_locn e) ws e' None (Some (exp_to_typ e))

let mk_opt_paren_exp (e :exp) : exp =
  match C.exp_to_term e with
    | Var _ -> e
    | Constant _ -> e
    | Tup _ -> e
    | Paren _ -> e
    | Lit _ -> e
    | _ -> mk_paren_exp e


let dest_const_exp (e : exp) : const_descr_ref id option =
  match C.exp_to_term e with
     | Constant c -> Some c
     | _ -> None
  ;;

let is_const_exp e = not (dest_const_exp e = None)


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

let mk_const_exp (env : env) l mp n inst =
  let (c, c_d) = (get_const_id env l mp n inst) in
  let t = Types.type_subst 
             (Types.TNfmap.from_list2 c_d.const_tparams c.instantiation) 
             c_d.const_type in
  C.mk_const l c (Some t)

let mk_eq_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans ("mk_eq", None) in
  let ty = exp_to_typ e1 in  

  let ty_0 = { Types.t = Types.Tfn (ty, bool_ty) } in
  let ty_1 = { Types.t = Types.Tfn (ty, ty_0) } in

  let eq_id = { id_path = Id_some (Ident.mk_ident [] (Name.add_lskip (Name.from_rope (r "="))) l);
                id_locn = l;
                descr = fst (get_const env ["Ocaml"; "Pervasives"] "=");
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
                descr = fst (get_const env ["Pervasives"] "&&");
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
                descr = fst (get_const env ["Pervasives"] "<=");
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
                descr = fst (get_const env ["Pervasives"] "+");
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
                descr = fst (get_const env ["Pervasives"] "-");
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

let mk_opt_fun_exp pL e_s =
  if (Util.list_longer 0 pL) then mk_fun_exp pL e_s else e_s

let mk_app_exp d e1 e2 =
  let l = Ast.Trans ("mk_app_exp", None) in
  let b_ty = match Types.dest_fn_type (Some d) (exp_to_typ e1) with
               | None -> raise (Ident.No_type(l, "non-function in application"))
               | Some (_, b_ty) -> b_ty
  in
  C.mk_app l e1 e2 (Some b_ty)

let rec mk_list_app_exp d f aL =
  match aL with 
    | [] -> f
    | a :: aL' -> mk_list_app_exp d (mk_app_exp d f a) aL'

let rec strip_paren_typ_exp (e :exp) : exp =
  match C.exp_to_term e with
    | Paren (s1, e', s2) -> strip_paren_typ_exp e'
    | Typed (s1, e', s2, src_t, s3) -> strip_paren_typ_exp e'
    | _ -> e


let dest_app_exp (e :exp) : (exp * exp) option =
  match C.exp_to_term e with
    | App (e1, e2) -> Some (e1, e2)
    | _ -> None

let strip_app_exp (e : exp) : exp * exp list = 
  let rec aux acc e =
    match dest_app_exp e with
      | None -> (e, acc)
      | Some (e1, e2) -> aux (e2 :: acc) e1
  in
  aux [] e


let dest_infix_exp (e :exp) : (exp * exp * exp) option =
  match C.exp_to_term e with
    | Infix (l, c, r) -> Some (l, c, r)
    | _ -> None

let is_infix_exp e =
  match C.exp_to_term e with
    | Infix _ -> true
    | _ -> false

let strip_infix_exp (e : exp) : exp * exp list = 
  match dest_infix_exp e with 
    | None -> (e, [])
    | Some (l, c, r) -> (c, [l;r])


let strip_app_infix_exp (e : exp) : exp * exp list * bool =
  if (is_infix_exp e) then
    let (e, args) = strip_infix_exp e in
    (e, args, true)
  else
    let (e, args) = strip_app_exp e in
    (e, args, false)

  
(* -------------------------------------------------------------------------- *)
(* checking properties and extracting specific informations                   *)
(* -------------------------------------------------------------------------- *)

let val_def_get_name d : Name.t option = match d with
  | Val_def (Fun_def (_, _, _, clauses),_,_) -> 
    begin
      match Seplist.to_list clauses with
         | [] -> None
         | (n, _, _, _, _, _)::_ -> Some (Name.strip_lskip n.term)
    end
  | Val_def (Let_def (_, _, (p,_,_,_,_)),_,_) -> 
      (match p.term with
         | P_var ns -> Some (Name.strip_lskip ns)
         | _ -> None)
  | _ -> None

let is_trans_loc = function
    Ast.Trans _ -> true
  | _ -> false

let is_trans_exp e =
  is_trans_loc (exp_to_locn e)

let is_trans_def (((_, _), l) : def) =  is_trans_loc l


let is_type_def_abbrev ((d, _), _) = 
  match d with
    | Type_def (_, l) -> begin
        Seplist.length l = 1 &&
        match Seplist.hd l with
          | (_,_,_,Te_abbrev _,_) -> true
          | _ -> false
      end
    | _ -> false

let is_type_def_record  ((d, _), _) = 
  match d with
    | Type_def (_, l) -> begin
        Seplist.length l = 1 &&
        match Seplist.hd l with
          | (_,_,_,Te_record _,_) -> true
          | _ -> false
      end
    | _ -> false




(* -------------------------------------------------------------------------- *)
(* Lookup the functions / types / modules used in some context                *)
(* -------------------------------------------------------------------------- *)

(* the used constant references, modules and types of some expression, definition, pattern ... 
   used_entities is using lists, because the order in which entities occur might be important for renaming.
   However, each list contains only distinct elements
*)
type used_entities = { used_consts : const_descr_ref list; used_types : Path.t list; used_modules : Path.t list }

let reverse_used_entities ue =
  { used_consts  = List.rev ue.used_consts; 
    used_types   = List.rev ue.used_types;
    used_modules = List.rev ue.used_modules }

let empty_used_entities = { used_consts = []; used_types = []; used_modules = [] }

let used_entities_add_const ue c =
  if (List.mem c ue.used_consts) then ue else
  {ue with used_consts = c :: ue.used_consts}

let used_entities_add_type ue p =
  if (List.mem p ue.used_types) then ue else
  {ue with used_types = p :: ue.used_types}

let used_entities_add_module ue p =
  if (List.mem p ue.used_modules) then ue else
  {ue with used_modules = p :: ue.used_modules}


let rec add_type_entities (ue : used_entities) (t : Types.t) : used_entities =
  match t.t with
    | Tvar _ -> ue
    | Tfn(t1,t2) -> add_type_entities (add_type_entities ue t1) t2
    | Ttup(ts) -> 
        List.fold_left add_type_entities ue ts
    | Tapp(ts,p) ->
        List.fold_left add_type_entities (used_entities_add_type ue p) ts
    | Tne _ -> ue
    | Tuvar _ -> ue

let rec add_src_t_entities (ue : used_entities) (t : Typed_ast.src_t) : used_entities =
  match t.term with
    | Typ_wild _ -> ue
    | Typ_var _ -> ue
    | Typ_len _ -> ue
    | Typ_fn (t1, _, t2) -> add_src_t_entities (add_src_t_entities ue t1) t2
    | Typ_tup sp -> Seplist.fold_left (fun t ue -> add_src_t_entities ue t) ue sp
    | Typ_app (id, args) -> List.fold_left add_src_t_entities (used_entities_add_type ue id.descr) args
    | Typ_paren (_, t, _) -> add_src_t_entities ue t

let rec add_pat_entities (ue : used_entities) (p : pat) : used_entities =
  let ue = add_type_entities ue (annot_to_typ p) in
  match p.term with
    | P_wild _ -> ue
    | P_as(_,p,_,_,_) -> add_pat_entities ue p
    | P_typ(_,p,_,t,_) -> 
        add_pat_entities (add_src_t_entities ue t) p
    | P_var _ -> ue
    | P_const(c,ps) -> 
        let ue = used_entities_add_const ue c.descr in
        List.fold_left add_pat_entities ue ps
    | P_record(_,fieldpats,_) -> Seplist.fold_left (fun (id, _, p) ue -> 
         add_pat_entities (used_entities_add_const ue id.descr)  p) ue fieldpats
    | P_vector(_,vectorpats,_) -> Seplist.fold_left (fun p ue -> add_pat_entities ue p) ue vectorpats
    | P_vectorC(_, vectorpats,_) -> List.fold_left add_pat_entities ue vectorpats
    | P_tup(_,ps,_) -> 
        Seplist.fold_left (fun p ue -> add_pat_entities ue p) ue ps
    | P_list(_,ps,_) -> 
        Seplist.fold_left (fun p ue -> add_pat_entities ue p) ue ps
    | P_paren(_,p,_) -> add_pat_entities ue p
    | P_cons(p1,_,p2) -> 
       add_pat_entities (add_pat_entities ue p1) p2
    | P_num_add _ -> ue
    | P_lit _ -> ue
    | P_var_annot(_,t) -> add_src_t_entities ue t

let rec add_letbind_entities (ue : used_entities) (lb : letbind) : used_entities = 
  match lb with
    | ( Let_val (p, ty_opt, _, e), _) ->
      let ue = add_pat_entities ue p in
      let ue = Util.option_default_map ty_opt ue (fun (_, src_ty) -> add_src_t_entities ue src_ty) in
      let ue = add_exp_entities ue e in
      ue
    | ( Let_fun (_, ps, ty_opt, _, e), _) ->
      let ue = List.fold_left add_pat_entities ue ps in
      let ue = Util.option_default_map ty_opt ue (fun (_, src_ty) -> add_src_t_entities ue src_ty) in
      let ue = add_exp_entities ue e in
      ue

and add_quant_binding_entities (ue : used_entities) (qb : quant_binding) : used_entities = 
  match qb with
    | Qb_var _ -> ue
    | Qb_restr (_, _, p, _, e, _) ->
      let ue = add_pat_entities ue p in
      let ue = add_exp_entities ue e in
      ue

and add_do_lines_entities (ue : used_entities) (dl : do_line) : used_entities = 
  match dl with
    | Do_line (p, _, e, _) ->
      let ue = add_pat_entities ue p in
      let ue = add_exp_entities ue e in
      ue

and add_exp_entities (ue : used_entities) (e : exp) : used_entities = 
  let ue = add_type_entities ue (exp_to_typ e) in
  match C.exp_to_term e with
    | Var(n) -> ue
    | Nvar_e _ -> ue
    | Constant(c) -> used_entities_add_const ue c.descr
    | Fun(_,ps,_,e) ->        
         add_exp_entities (List.fold_left add_pat_entities ue ps) e
    | Function(_,pes,_) ->
         Seplist.fold_left (fun (p, _, e,_) ue -> add_exp_entities (add_pat_entities ue p) e) ue pes
    | App(e1,e2) -> add_exp_entities (add_exp_entities ue e1) e2
    | Infix(e1,e2,e3) -> add_exp_entities (add_exp_entities (add_exp_entities ue e1) e2) e3
    | Record(_,fieldexps,_) -> Seplist.fold_left (fun (id, _, e, _) ue -> add_exp_entities (used_entities_add_const ue id.descr) e) ue fieldexps
    | Recup(_, e,_,fieldexps,_) ->
        let ue = add_exp_entities ue e in
        Seplist.fold_left (fun (id, _, e, _) ue -> add_exp_entities (used_entities_add_const ue id.descr) e) ue fieldexps
    | Field(e,_,fd) -> add_exp_entities (used_entities_add_const ue fd.descr) e
    | Vector(_,es,_) -> Seplist.fold_left (fun e ue -> add_exp_entities ue e) ue es
    | VectorSub(e,_,_,_,_,_) -> add_exp_entities ue e
    | VectorAcc(e,_,_,_) -> add_exp_entities ue e
    | Case(_,_,e,_,patexps,_) ->
      let ue = add_exp_entities ue e in
      Seplist.fold_left (fun (p, _, e, _) ue -> add_exp_entities (add_pat_entities ue p) e) ue patexps
    | Typed(_,e,_,src_t,_) ->
      add_exp_entities (add_src_t_entities ue src_t) e
    | Let(_,lb,_,e) ->
      let ue = add_letbind_entities ue lb in
      add_exp_entities ue e
    | Tup(_,es,_) -> Seplist.fold_left (fun e ue -> add_exp_entities ue e) ue es
    | List(_,es,_) -> Seplist.fold_left (fun e ue -> add_exp_entities ue e) ue es
    | Paren(_,e,_) -> add_exp_entities ue e
    | Begin(_,e,_) -> add_exp_entities ue e
    | If(_,e1,_,e2,_,e3) ->
      let ue = add_exp_entities ue e1 in
      let ue = add_exp_entities ue e2 in
      let ue = add_exp_entities ue e3 in
      ue
    | Lit _ -> ue
    | Set(_,es,_) -> Seplist.fold_left (fun e ue -> add_exp_entities ue e) ue es
    | Setcomp(_,e1,_,e2,_,_) ->
      let ue = add_exp_entities ue e1 in
      let ue = add_exp_entities ue e2 in
      ue
    | Comp_binding(_,_,e1,_,_,qbs,_,e2,_) ->
      let ue = add_exp_entities ue e1 in
      let ue = List.fold_left add_quant_binding_entities ue qbs in
      let ue = add_exp_entities ue e2 in
      ue
   | Quant(_,qbs,_,e) ->
      let ue = List.fold_left add_quant_binding_entities ue qbs in
      let ue = add_exp_entities ue e in
      ue
   | Do(_,mid,do_lines,_,e,_,_) ->
      let ue = used_entities_add_module ue mid.descr.mod_binding in
      let ue = List.fold_left add_do_lines_entities ue do_lines in
      let ue = add_exp_entities ue e in
      ue

and add_texp_entities (ue : used_entities) = function
  | Te_opaque -> ue
  | Te_abbrev (_, src_t) -> add_src_t_entities ue src_t
  | Te_record (_, _, sl, _) ->
       Seplist.fold_left (fun (_, c, _, src_t) ue -> add_src_t_entities (used_entities_add_const ue c) src_t) ue sl
  | Te_variant (_, constr_sl) ->
       Seplist.fold_left (fun (_, c, _, src_t_sl) ue -> begin
         let ue = used_entities_add_const ue c in
         let ue = Seplist.fold_left (fun src_t ue -> add_src_t_entities ue src_t) ue src_t_sl in
         ue
       end) ue constr_sl

and add_funcl_aux_entities (ue : used_entities) ((_, c, ps, src_t_opt, _, e):funcl_aux) = begin
  let ue = used_entities_add_const ue c in
  let ue = List.fold_left add_pat_entities ue ps in
  let ue = match src_t_opt with 
    | Some (_, src_t) -> add_src_t_entities ue src_t 
    | _ -> ue 
  in
  let ue = add_exp_entities ue e in
  ue
end

and add_def_entities (t_opt : Target.target option) (ue : used_entities) (((d, _), _) : def) : used_entities = 
  match d with
      | Type_def(sk, tds) ->
         Seplist.fold_left (fun (_, _, type_path, texp, _) ue -> begin
           let ue = used_entities_add_type ue type_path in
           let ue = add_texp_entities ue texp in
           ue
         end) ue tds
      | Val_def(Let_def(_, targs, (p, nm, src_t_opt, _, e)), _, _) -> 
         if (not (in_targets_opt t_opt targs)) then ue else begin
           let ue = add_pat_entities ue p in
           let ue = List.fold_left (fun ue  (_, c) -> used_entities_add_const ue c) ue nm in
           let ue = match src_t_opt with 
             | Some (_, src_t) -> add_src_t_entities ue src_t 
             | _ -> ue 
           in
           let ue = add_exp_entities ue e in
           ue
         end
      | (Val_def(Fun_def(_, _, targs, funs),_,_)) -> 
         if (in_targets_opt t_opt targs) then 
           Seplist.fold_left (fun clause ue -> add_funcl_aux_entities ue clause) ue funs 
         else ue
      | Val_def(Let_inline(_,_,targs,_,c,_,_,e), tnvs, class_constraints) ->
         if (in_targets_opt t_opt targs) then begin
           let ue = used_entities_add_const ue c in
           let ue = add_exp_entities ue e in
           ue
         end else ue
      | Lemma(_, _, targs, _, _, e, _) ->
          if (in_targets_opt t_opt targs) then add_exp_entities ue e else ue
      | Module(_, _, mod_path, _, _, ds, _) -> begin
          let ue = used_entities_add_module ue mod_path in
          let ue = List.fold_left (add_def_entities t_opt) ue ds in
          ue
        end
      | Rename(_, _, mod_path, _, m) -> begin
          let ue = used_entities_add_module ue mod_path in
          let ue = used_entities_add_module ue m.descr.mod_binding in
          ue
        end
      | Ident_rename (_,_,_,_,_,_) ->
          (* TODO: replace Ident_rename with something more general *) ue
      | Open(_,m) -> used_entities_add_module ue m.descr.mod_binding
      | Indreln(_,targ,rules) -> begin
          let add_rule (_,_,_,_,e_opt,_,_,n_ref,es) ue = begin
             let ue = match e_opt with None -> ue | Some e -> add_exp_entities ue e in
             let ue = used_entities_add_const ue n_ref in
             let ue = List.fold_left add_exp_entities ue es in
             ue
          end in
          Seplist.fold_left add_rule ue rules
        end
      | Val_spec(_,_,n_ref,_,(_, src_t)) ->begin
          let ue = used_entities_add_const ue n_ref in
          let ue = add_src_t_entities ue src_t in
          ue
        end
      | Class(_,_,n,tvar,_,_,body,_) -> (* TODO: classes broken, needs fixing in typechecking and AST *) ue
      | Instance(_,_,_,_,_) -> (* TODO: broken, needs fixing in typechecking and AST *) ue
      | Comment _ -> ue


let add_checked_module_entities (t_opt : Target.target option) (ue : used_entities) (m : checked_module): used_entities = 
  let (dl, _) = m.typed_ast in 
  List.fold_left (add_def_entities t_opt) ue dl

let get_checked_modules_entities (t_opt : Target.target option) (ml : checked_module list) : used_entities =
  reverse_used_entities (List.fold_left (add_checked_module_entities t_opt) empty_used_entities ml)


(* check whether a definition is recursive using entities *)
let is_recursive_def (((d, _), _) : def) =  
 match d with
  |  Val_def ((Fun_def (_, Some _, _, sl)), tnvs,class_constraints) -> begin 
       let (_, pL) = Seplist.to_pair_list None sl in

       (* get the names of all newly defined functions *)
       let add_fun_ref s ((((_, c, _, _, _, _) : funcl_aux), _)) = if (List.mem c s) then s else c::s in
       let all_consts = List.fold_left add_fun_ref [] pL in

       let get_rhs_entities ue ((((_, _, _, _, _, e) : funcl_aux), _)) = add_exp_entities ue e in
       let rhs_ue = List.fold_left get_rhs_entities empty_used_entities pL in

       let is_real_rec = List.exists (fun c -> List.mem c rhs_ue.used_consts) all_consts in
       (true, is_real_rec)
     end
  |  _ -> (false, false)
