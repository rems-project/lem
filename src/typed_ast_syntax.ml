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
let nat_ty  = { Types.t = Types.Tapp ([], Path.natpath)  }

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


let env_tag_to_string = function
    | K_field    -> "field"
    | K_constr   -> "constructor"
    | K_instance -> "instance of a class method"
    | K_method   -> "class method"
    | K_let      -> "top-level variable binding"
    | K_relation -> "relation"


let is_pp_loc = function
    Ast.Trans (b, _, _) -> b
  | _ -> false

let is_pp_exp e =
  is_pp_loc (exp_to_locn e)

let is_pp_def (((_, _), l, _) : def) =  is_pp_loc l


(* -------------------------------------------------------------------------- *)
(* navigating environments                                                    *)
(* -------------------------------------------------------------------------- *)

let lookup_env_opt_aux (e_env : e_env) (e : local_env) (mp : Name.t list) : (local_env * mod_descr option) option = 
  let rec aux (env : local_env) (last_descr : mod_descr option) mp =
     match mp with
      | [] -> Some (env, last_descr)
      | n::nl ->
         let p_opt = Nfmap.apply env.m_env n in
         let md_opt = Util.option_bind (Pfmap.apply e_env) p_opt in
         Util.option_bind (fun md -> aux md.mod_env (Some md) nl) md_opt
  in
  aux e None mp

let lookup_env_opt (e : env) (mp : Name.t list) : local_env option = 
  Util.option_map fst (lookup_env_opt_aux e.e_env e.local_env mp)

let rec lookup_env (e : env) (mp : Name.t list) : local_env = 
match lookup_env_opt e mp with
  | Some env -> env
  | None ->
        let mod_p = Path.mk_path_list mp in
        raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal (Ast.Unknown, 
              "lookup_env failed to find module '" ^ (Path.to_string mod_p) ^"'")))

let rec lookup_mod_descr_opt (e : env) (mp : Name.t list) (n : Name.t) : mod_descr option = 
  Util.option_bind snd (lookup_env_opt_aux e.e_env e.local_env (mp @ [n]))

let lookup_mod_descr (e : env) (mp : Name.t list) (n : Name.t) : mod_descr = 
  match lookup_mod_descr_opt e mp n with
    | Some md -> md
    | None ->
        let mod_p = Path.mk_path mp n in
        raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal (Ast.Unknown, 
              "lookup_mod_descr failed to find module '" ^ (Path.to_string mod_p) ^"'")))


let names_get_const_ref (env : env) mp n : const_descr_ref = 
  let l = Ast.Trans(false, "names_get_const_ref", None) in
  let local_env_opt = lookup_env_opt env mp in
  let res_opt = Util.option_bind (fun local_env -> Nfmap.apply local_env.v_env n) local_env_opt in
  match res_opt with 
    | Some d -> d
    | None ->
      let const_ident = Ident.mk_ident None mp n in
        raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "environment does not contain constant '" ^
               Ident.to_string const_ident ^ "'")))

let names_get_const (env : env) mp n =
  let c_ref = names_get_const_ref env mp n in
  let c_d = c_env_lookup Ast.Unknown env.c_env c_ref in
  (c_ref, c_d)

let strings_get_const (env : env) mp n =
  names_get_const env (List.map (fun n -> (Name.from_rope (r n))) mp) (Name.from_rope (r n))

let get_const env label =
  let (mp, n) = External_constants.constant_label_to_path_name label in
  strings_get_const env mp n

let const_exists env label =
  let (mp, n) = External_constants.constant_label_to_path_name label in
  let local_env_opt = lookup_env_opt env (List.map Name.from_string mp) in
  let res_opt = Util.option_bind (fun local_env -> Nfmap.apply local_env.v_env (Name.from_string n)) local_env_opt in
  match res_opt with
    | None -> false
    | Some _ -> true

let dest_field_types l env (f : const_descr_ref) =
  let l = Ast.Trans(false, "dest_field_types", Some l) in 
  let f_d = c_env_lookup l env.c_env f in
  let full_type = f_d.const_type in
  match Types.dest_fn_type (Some env.t_env) full_type with
    | Some ({ Types.t = Types.Tapp (t_b_args, t_b_c) }, t_arg) when t_b_args = List.map Types.tnvar_to_type (f_d.const_tparams) -> 
         (t_arg, t_b_c, f_d)
    | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "not a field type")))

let get_field_type_descr l env (f : const_descr_ref) =
  let l = Ast.Trans(false, "get_field_type_descr", Some l) in 
  let (f_field_arg, f_tconstr, f_d) = dest_field_types l env f in
  match Types.Pfmap.apply env.t_env f_tconstr with
    | Some(Types.Tc_type(td)) -> td
    | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "not a field type")))

let get_field_all_fields l env (f : const_descr_ref) : const_descr_ref list =
  let l = Ast.Trans(false, "get_field_all_fields", Some l) in 
  let td = get_field_type_descr l env f in
  match td.Types.type_fields with
    | Some(fl) -> fl
    | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "not a field type")))

let lookup_class_descr l env (class_path : Path.t) =
  let l = Ast.Trans(false, "get_class_descr", Some l) in 
  match Types.Pfmap.apply env.t_env class_path with
    | Some(Types.Tc_class(cd)) -> cd
    | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "not a type class")))

let lookup_field_for_class_method l cd method_ref = 
  try 
     List.assoc method_ref cd.Types.class_methods
  with Not_found -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "method-ref not present in class!")))

let lookup_inst_method_for_class_method l id method_ref = 
  try 
     List.assoc method_ref id.Types.inst_methods
  with Not_found -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(l, "method-ref not present in class!")))


let class_descr_get_dict_type cd arg =
    { Types.t = Types.Tapp([arg], cd.class_record) }

let class_all_methods_inlined_for_target l env target (class_path : Path.t) =
  let l = Ast.Trans(false, "class_all_methods_inlined_for_target", Some l) in 
  let class_d = lookup_class_descr l env class_path in
  let method_refs = List.map fst class_d.class_methods in

  let method_is_inlined c = begin
    let cd = c_env_lookup l env.c_env c in
    not (in_target_set target cd.const_targets) ||
    (match (Target.Targetmap.apply_target cd.target_rep target) with
      | Some (CR_inline _) -> true
      | _ -> false)
  end in

  List.for_all method_is_inlined method_refs


let update_const_descr l up c env =
  let l = Ast.Trans(false, "update_const_descr", Some l) in 
  let cd = c_env_lookup l env.c_env c in
  let new_cd = up cd in
  let new_c_env = c_env_update env.c_env c new_cd in
  {env with c_env = new_c_env}

let constant_descr_to_name (targ : Target.target) (cd : const_descr) : (bool * Name.t * Name.t option) = 
  let name_renamed = match Target.Targetmap.apply_target cd.target_rename targ with
    | Some (_, n) -> n
    | None -> Path.get_name cd.const_binding
  in

  let name_ascii = 
     match Target.Targetmap.apply_target cd.target_ascii_rep targ with
       | Some (_, n) -> Some n
       | None -> None
  in

  let is_shown = match Target.Targetmap.apply_target cd.target_rep targ with
    | Some (CR_inline _) -> false
    | Some (CR_special (_, _, special_fun, _)) -> cr_special_fun_uses_name special_fun
    | Some (CR_simple _) -> false
    | Some (CR_infix _) -> false
    | Some (CR_undefined _) -> false
    | None -> true
  in
  (is_shown, name_renamed, name_ascii)

let const_descr_ref_to_ascii_name_counter = ref 0
let const_descr_ref_to_ascii_name c_env c : Name.t =
begin
  let l = Ast.Trans (false, "const_ref_to_name", None) in
  let c_descr = c_env_lookup l c_env c in

  let name_ok n = Util.is_simple_ident_string (Name.to_string n) in

  let name0 = Path.get_name c_descr.const_binding in
  if (name_ok name0) then name0 else 
  begin
    let check_target targ = begin
       let (_, n_no_ascii, n_ascii_opt) = constant_descr_to_name (Target.Target_no_ident targ) c_descr in
       if name_ok n_no_ascii then Some n_no_ascii else
       Util.option_bind (fun n -> if name_ok n then Some n else None) n_ascii_opt
    end in
    match Util.option_first check_target Target.all_targets_list with
      | None -> (* really could not find anything, so make something up *) 
                (const_descr_ref_to_ascii_name_counter := !const_descr_ref_to_ascii_name_counter + 1;
                 Name.from_string ("please_define_ascii_alternative" ^ 
                   (string_of_int !const_descr_ref_to_ascii_name_counter)))
      | Some n -> n
  end
end

let type_descr_to_name (targ : Target.target) (p : Path.t) (td : type_descr) : Name.t = 
  match Target.Targetmap.apply_target td.Types.type_rename targ with
     | None -> Path.get_name p        
     | Some (_, n) -> n


let constant_descr_rename  (targ : Target.non_ident_target) (n':Name.t) (l' : Ast.l) (cd : const_descr) : (const_descr * (Ast.l * Name.t) option) = 
  let old_info = Target.Targetmap.apply_target cd.target_rename (Target.Target_no_ident targ) in
  let tr = Target.Targetmap.insert (cd.target_rename) (targ, (l', n')) in
  ({cd with target_rename = tr}, old_info)

let mod_target_rep_rename  (targ : Target.non_ident_target) mod_string (n':Name.t) (l' : Ast.l) (tr : mod_target_rep Target.Targetmap.t) : mod_target_rep Target.Targetmap.t = 
  let _ = match (Target.Targetmap.apply_target tr (Target.Target_no_ident targ)) with
    | (Some (MR_rename (l, _))) ->
      begin
        let loc_s = Reporting_basic.loc_to_string true l in
        let msg = Format.sprintf 
           "a %s target representation for module '%s' has already been given at\n    %s" 
           (Target.non_ident_target_to_string targ) mod_string loc_s in
        raise (Reporting_basic.err_type l' msg)
      end
    | None -> ()
  in
  let new_name = Util.option_default n' (Name.capitalize n') in
  let new_info = MR_rename (l', new_name) in
  let tr' = Target.Targetmap.insert tr (targ, new_info) in
  tr'


let type_descr_rename  (targ : Target.non_ident_target) (n':Name.t) (l' : Ast.l) (td : type_descr) : type_descr * (Ast.l * Name.t) option = 
  let old_rep = Target.Targetmap.apply td.type_rename targ in
  let tr = Target.Targetmap.insert td.type_rename (targ, (l', n')) in
  ({td with type_rename = tr}, old_rep)

let type_defs_rename_type l (d : type_defs) (p : Path.t) (t: Target.non_ident_target) (n : Name.t) : type_defs =
  let l' = Ast.Trans (false, "type_defs_rename_type", Some l) in
  let up td = begin
    let (res, _) = type_descr_rename t n l td in
    Some res
  end in
  Types.type_defs_update_tc_type l' d p up

let const_target_rep_to_loc= function
  | CR_inline (l, _, _, _) -> l
  | CR_infix (l, _, _, _) -> l
  | CR_simple (l, _, _, _) -> l
  | CR_special (l, _, _, _) -> l
  | CR_undefined (l, _) -> l

let const_target_rep_allow_override = function
  | CR_inline (_, f, _, _) -> f
  | CR_infix (_, f, _, _) -> f
  | CR_simple (_, f, _, _) -> f
  | CR_special (_, f, _, _) -> f
  | CR_undefined (_, f) -> f

let type_target_rep_to_loc= function
  | TYR_simple (l, _, _) -> l
  | TYR_subst (l, _, _, _) -> l

let type_target_rep_allow_override = function
  | TYR_simple (_, b, _) -> b
  | TYR_subst (_, b, _, _) -> b


let const_descr_has_target_rep targ cd =
  match targ with
    | Target.Target_ident -> false
    | Target.Target_no_ident t -> Target.Targetmap.in_dom t cd.target_rep


let const_descr_to_kind (r, d) =
  match d.env_tag with
    | K_field -> Nk_field r
    | K_constr -> Nk_constr r
    | _ -> Nk_const r

let env_apply_aux (env : env) n comp =
  let case_fun map f =
    Util.option_map f (Nfmap.apply map n)
  in
  match comp with
    | Ast.Component_module _ ->
        case_fun env.local_env.m_env (fun mod_path ->
          (Nk_module mod_path, mod_path, Ast.Unknown))
    | Ast.Component_function _ ->
        case_fun env.local_env.v_env (fun r ->
        let d = c_env_lookup (Ast.Trans (false, "env_apply", None)) env.c_env r in
        (const_descr_to_kind (r, d), d.const_binding, d.spec_l))
    | Ast.Component_type _ -> 
        case_fun env.local_env.p_env (fun (p, l) -> (Nk_typeconstr p, p, l))
    | Ast.Component_field _ ->
        case_fun env.local_env.f_env (fun r ->
        let d = c_env_lookup (Ast.Trans (false, "env_apply", None)) env.c_env r in
        (const_descr_to_kind (r, d), d.const_binding, d.spec_l))

let env_apply (env : env) comp_opt n =
  let aux = env_apply_aux env n in
  match comp_opt with
    | Some comp -> aux comp
    | None -> Util.option_first aux [Ast.Component_function None; Ast.Component_field None; Ast.Component_type None; Ast.Component_module None]


let strings_get_const_id (env : env) l mp n inst =
let (c_ref, c_d) = strings_get_const env mp n in
({ id_path = Id_none None;
   id_locn = l;
   descr = c_ref;
   instantiation = inst },
 c_d)

let get_const_id env l label inst =
  let (mp, n) = External_constants.constant_label_to_path_name label in
  strings_get_const_id env l mp n inst


(* -------------------------------------------------------------------------- *)
(* fixing initial representations                                             *)
(* -------------------------------------------------------------------------- *)

let fix_const_descr_ocaml_constr c_d = 
  let is_constr = match c_d.env_tag with
    | K_constr -> true
    | _ -> false
  in if not is_constr then c_d else begin
    (* get the argument types *)
    let (arg_tyL, _) = Types.strip_fn_type None c_d.const_type in
    let vars = List.map (fun ty ->
      { term = Name.add_lskip (t_to_var_name ty);
        locn = Ast.Unknown;
        typ = ty;
        rest = (); }) arg_tyL in

    let rep = CR_special (c_d.spec_l, true, CR_special_uncurry (List.length arg_tyL), vars) in
    let new_tr = Target.Targetmap.insert c_d.target_rep (Target.Target_ocaml, rep) in
    
    { c_d with target_rep = new_tr }
  end

  
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
  let l = Ast.Trans (false, "mk_tf_exp", None) in
  let lit = C.mk_lbool l None b (Some bool_ty) in
  let exp = C.mk_lit l lit (Some bool_ty) 
in exp

let dest_tf_exp e =
  match C.exp_to_term e with
      Lit l -> (match l.term with L_true _ -> Some true | L_false _ -> Some false | _ -> None)
    | _ -> None

let is_tf_exp b e = (dest_tf_exp e = Some b)

let is_t_exp e =
  is_tf_exp true e

let is_f_exp e =
  is_tf_exp false e

let dest_num_exp e =
  match C.exp_to_term e with
      Lit l -> (match l.term with L_num (_,i,_) -> Some i | _ -> None)
    | _ -> None

let is_num_exp e = not (dest_tf_exp e = None)

let mk_num_exp num_ty i = 
  let l = Ast.Trans (false, "mk_num_exp", None) in
  let lit = C.mk_lnum l None i None num_ty in
  C.mk_lit l lit (Some num_ty)

let mk_paren_exp e =
     let (e', ws) = alter_init_lskips remove_init_ws e in
     C.mk_paren (exp_to_locn e) ws e' None (Some (exp_to_typ e))


let is_empty_backend_exp e =
  match C.exp_to_term e with
   | Backend(_,i) -> (Ident.to_string i = "") 
   | _ -> false


let rec mk_opt_paren_exp (e :exp) : exp = 
  match C.exp_to_term e with
    | Var _ -> e
    | Constant _ -> e
    | Backend _ -> e
    | Tup _ -> e
    | Paren _ -> e
    | Lit _ -> e
    | App (e1, e2) -> 
      if is_empty_backend_exp e1 then
        C.mk_app (exp_to_locn e) e1 (mk_opt_paren_exp e2) (Some (exp_to_typ e)) 
      else
        mk_paren_exp e
    | _ -> mk_paren_exp e 


let rec may_need_paren (e :exp) : bool = 
  match C.exp_to_term e with
    | Var _ -> false
    | Constant _ -> false
    | Backend _ -> false
    | Tup _ -> false
    | Paren _ -> false
    | Lit _ -> false
    | App (e1, e2) -> (not (is_empty_backend_exp e1)) || may_need_paren e2
    | _ -> true

let dest_const_exp (e : exp) : const_descr_ref id option =
  match C.exp_to_term e with
     | Constant c -> Some c
     | _ -> None
  ;;

let is_const_exp e = not (dest_const_exp e = None)


let mk_case_exp final (l:Ast.l) (in_e : exp) (rows : (pat * exp) list) (ty : Types.t) : exp =
  let loc = Ast.Trans (true, "mk_case_exp", Some l) in
  let rows_sep_list = Seplist.from_list (List.map (fun (p,e) -> ((pat_append_lskips space p, space, fst (alter_init_lskips space_init_ws e), loc), space)) rows) in
  C.mk_case final loc None in_e space rows_sep_list space (Some ty)

let mk_case_exp_new_line final (l:Ast.l) (in_e : exp) (rows : (pat * exp) list) (ty : Types.t) : exp =
  let loc = Ast.Trans (true, "mk_case_exp", Some l) in
  let case_space = Some [Ast.Ws (r"\n  ")] in
  let rows_sep_list = Seplist.from_list (List.map (fun (p,e) -> ((pat_append_lskips space p, space, fst (alter_init_lskips space_init_ws e), loc), case_space)) rows) in
  C.mk_case final loc new_line in_e space rows_sep_list new_line (Some ty)

let mk_let_exp (l:Ast.l) ((n: Name.t), (e1:exp)) (e2:exp) : exp =
  let loc = Ast.Trans (true, "mk_let_exp", Some l) in

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

let strings_mk_const_exp (env : env) l mp n inst =
  let (c, c_d) = (strings_get_const_id env l mp n inst) in
  let t = Types.type_subst 
             (Types.TNfmap.from_list2 c_d.const_tparams c.instantiation) 
             c_d.const_type in
  C.mk_const l c (Some t)

let mk_const_exp (env : env) l label inst =
  let (mp, n) = External_constants.constant_label_to_path_name label in
  strings_mk_const_exp env l mp n inst

let mk_eq_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans (true, "mk_eq", None) in
  let ty = exp_to_typ e1 in  

  let ty_0 = { Types.t = Types.Tfn (ty, bool_ty) } in
  let ty_1 = { Types.t = Types.Tfn (ty, ty_0) } in

  let (eq_id, _) = get_const_id env l "equality" [ty] in
  let eq_exp = C.mk_const l eq_id (Some ty_1) in
  let res = C.mk_infix l e1 eq_exp e2 (Some bool_ty) in
  res

let mk_and_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans (true, "mk_and_exp", None) in
  let ty_0 = { Types.t = Types.Tfn (bool_ty, bool_ty) } in
  let ty_1 = { Types.t = Types.Tfn (bool_ty, ty_0) } in

  let (and_id, _) = get_const_id env l "conjunction" [] in
  let and_exp = C.mk_const l and_id (Some ty_1) in
  let res = C.mk_infix l e1 and_exp e2 (Some bool_ty) in
  res

let rec mk_and_exps env el : exp =
  match el with
    | [] -> mk_tf_exp true
    | [e] -> e
    | e1 :: e2 :: es ->
      mk_and_exp env e1 (mk_and_exps env (e2 :: es))

let is_and_exp (env : env) (e : exp) =
  match C.exp_to_term e with
    | Constant c -> c.descr = fst (get_const env "conjunction")
    | _ -> false

(* Splits on infix (&&) : ((a && b) && (c && d)) && true -> [a;b;c;d] *)
let rec dest_and_exps (env : env) (e : exp) : exp list =
  match C.exp_to_term e with
    | Infix(e1, op, e2) when is_and_exp env op ->
      dest_and_exps env e1 @ dest_and_exps env e2
    | Paren(_,e,_) -> dest_and_exps env e
    | Typed(_,e,_,_,_) -> dest_and_exps env e
    | _ when is_t_exp e -> []
    | _ -> [e]

let mk_le_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans (true, "mk_le_exp", None) in  
  let num_ty = exp_to_typ e1 in
  let ty_0 = { Types.t = Types.Tfn (num_ty, bool_ty) } in
  let ty_1 = { Types.t = Types.Tfn (num_ty, ty_0) } in

  let (le_id, _) = get_const_id env l "less_equal" [num_ty] in

  let le_exp = C.mk_const l le_id (Some ty_1) in
  let res = C.mk_infix l e1 le_exp e2 (Some bool_ty) in
  res

let mk_sub_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans (true, "matrix_compile_mk_sub", None) in
  let num_ty = exp_to_typ e1 in
  let ty_0 = { Types.t = Types.Tfn (num_ty, num_ty) } in
  let ty_1 = { Types.t = Types.Tfn (num_ty, ty_0) } in

  let (sub_id, _) = get_const_id env l "subtraction" [num_ty] in
  let sub_exp = C.mk_const l sub_id (Some ty_1) in
  let res = C.mk_infix l e1 sub_exp e2 (Some num_ty) in
  res

let mk_from_list_exp env (e : exp) : exp =
  let l = Ast.Trans (true, "mk_from_list_exp", None) in

  let list_ty = exp_to_typ e in
  let base_ty = match list_ty.Types.t with
          | Types.Tapp([t],_) -> t
          | _ -> raise (Reporting_basic.err_unreachable l "e not of list-type") in
  let set_ty = { Types.t = Types.Tapp([base_ty],Path.setpath) } in
  
  let from_list_exp = mk_const_exp env l "set_from_list" [base_ty] in
  let res = C.mk_app l from_list_exp e (Some set_ty) in
  res

let mk_cross_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans (true, "mk_cross_exp", None) in

  let get_set_type e = match (exp_to_typ e).Types.t with
       | Types.Tapp([t],_) -> t
       | _ -> raise (Reporting_basic.err_unreachable l "e not of set-type") in

  let e1_ty = get_set_type e1 in
  let e2_ty = get_set_type e2 in
  let pair_ty = { Types.t = Types.Ttup [e1_ty; e2_ty] } in
  let cross_ty = { Types.t = Types.Tapp([pair_ty],Path.setpath) } in
  let aux_ty = { Types.t = Types.Tfn (exp_to_typ e2, cross_ty) } in
  
  let cross_exp = mk_const_exp env l "set_cross" [e1_ty; e2_ty] in
  let res0 = C.mk_app l cross_exp e1 (Some aux_ty) in
  let res = C.mk_app l res0 e2 (Some cross_ty) in
  res

let mk_set_sigma_exp env (e1 : exp) (e2 : exp) : exp =
  let l = Ast.Trans (true, "mk_set_sigma_exp", None) in

  let (e1_ty, e2_ty) = match (exp_to_typ e2).Types.t with
       | Types.Tfn(e1_ty, {Types.t = Types.Tapp([e2_ty],_)}) -> (e1_ty, e2_ty)
       | _ -> raise (Reporting_basic.err_unreachable l "e2 not of type 'a -> set 'b") in

  let pair_ty = { Types.t = Types.Ttup [e1_ty; e2_ty] } in
  let sigma_ty = { Types.t = Types.Tapp([pair_ty],Path.setpath) } in
  let aux_ty = { Types.t = Types.Tfn (exp_to_typ e2, sigma_ty) } in
  
  let union_exp = mk_const_exp env l "set_sigma" [e1_ty; e2_ty] in
  let res0 = C.mk_app l union_exp e1 (Some aux_ty) in
  let res = C.mk_app l res0 e2 (Some sigma_ty) in
  res

let mk_set_filter_exp env (e_P : exp) (e_s : exp) : exp =
  let l = Ast.Trans (true, "mk_filter_exp", None) in

  let set_ty = match (exp_to_typ e_P).Types.t with
       | Types.Tfn (ty_a, _) -> ty_a
       | _ -> raise (Reporting_basic.err_unreachable l "e_P not of predicate-type") in
 
  let res_ty = { Types.t = Types.Tapp([set_ty],Path.setpath) } in
  let aux_ty = { Types.t = Types.Tfn (exp_to_typ e_s, res_ty) } in

  let filter_exp = mk_const_exp env l "set_filter" [set_ty] in
  let res0 = C.mk_app l filter_exp e_P (Some aux_ty) in
  let res = C.mk_app l res0 e_s (Some res_ty) in
  res


let mk_set_image_exp env (e_f : exp) (e_s : exp) : exp =
  let l = Ast.Trans (true, "mk_image_exp", None) in

  let (ty_a, ty_b) = match (exp_to_typ e_f).Types.t with
       | Types.Tfn (ty_a, ty_b) -> (ty_a, ty_b)
       | _ -> raise (Reporting_basic.err_unreachable l "e_f not of function-type") in
 
  let res_ty = { Types.t = Types.Tapp([ty_b],Path.setpath) } in
  let aux_ty = { Types.t = Types.Tfn (exp_to_typ e_s, res_ty) } in

  let image_exp = mk_const_exp env l "set_image" [ty_a; ty_b] in
  let res0 = C.mk_app l image_exp e_f (Some aux_ty) in
  let res = C.mk_app l res0 e_s (Some res_ty) in
  res

let mk_fun_exp (pL : pat list) (e_s : exp) : exp =
  let l = Ast.Trans (true, "mk_fun_exp", None) in
  let pL' = List.map (fun p -> fst (pat_alter_init_lskips space_com_init_ws p)) pL in
  let res_ty = Types.multi_fun (List.map (fun p -> p.typ) pL) (exp_to_typ e_s) in
  let res = C.mk_fun l space pL' space (mk_opt_paren_exp e_s) (Some res_ty) in
  res

let mk_opt_fun_exp pL e_s =
  if (Util.list_longer 0 pL) then mk_fun_exp pL e_s else e_s

let mk_app_exp l d e1 e2 =
  let l = Ast.Trans (true, "mk_app_exp", Some l) in
  let b_ty = match Types.dest_fn_type (Some d) (exp_to_typ e1) with
               | None -> raise (Reporting_basic.err_type l "non-function in application")
               | Some (_, b_ty) -> b_ty
  in
  C.mk_app l e1 e2 (Some b_ty)

let rec mk_list_app_exp l d f aL =
  match aL with 
    | [] -> f
    | a :: aL' -> mk_list_app_exp l d (mk_app_exp l d f a) aL'

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

let val_def_get_name d : Name.lskips_t option = match d with
  | (Fun_def (_, _, _, clauses)) -> 
    begin
      match Seplist.to_list clauses with
         | [] -> None
         | (n, _, _, _, _, _)::_ -> Some n.term
    end
  | (Let_def (_, _, (p,_,_,_,_))) -> 
      (match p.term with
         | P_var ns -> Some ns
         | _ -> None)
  | _ -> None


let val_def_get_const_descr_refs = function
  | Let_def(_, _, (_, nm, _, _, _)) -> 
      List.map snd nm
  | Let_inline(_,_,_,_,c,_,_,_) -> [c]
  | Fun_def(_, _, _, funs) -> 
     Seplist.to_list_map (fun ((_, c, _, _, _, _):funcl_aux) -> c) funs

let val_def_get_class_constraints_no_target_rep env targ d = begin
  let l_unk = Ast.Trans (true, "val_def_get_class_constraints", None) in
  let cs = val_def_get_const_descr_refs d in
  let cds = List.map (c_env_lookup l_unk env.c_env) cs in
  List.flatten (List.map (fun cd -> 
       match Target.Targetmap.apply_target cd.target_rep targ with
         | None -> cd.const_class | Some _ -> []) cds)
end

let val_def_get_class_constraints env d = begin
  let l_unk = Ast.Trans (true, "val_def_get_class_constraints", None) in
  let cs = val_def_get_const_descr_refs d in
  let cds = List.map (c_env_lookup l_unk env.c_env) cs in
  List.flatten (List.map (fun cd -> cd.const_class) cds)
end

let val_def_get_free_tnvars env d = begin
  let l_unk = Ast.Trans (true, "val_def_get_free_tnvars", None) in
  let cs = val_def_get_const_descr_refs d in
  let cds = List.map (c_env_lookup l_unk env.c_env) cs in
  let tnvars = List.flatten (List.map (fun cd -> cd.const_tparams) cds) in
  List.fold_left (fun s x -> TNset.add x s) TNset.empty tnvars
end

let is_type_def_abbrev (((d, _), _, _):def) = 
  match d with
    | Type_def (_, l) -> begin
        Seplist.length l = 1 &&
        match Seplist.hd l with
          | (_,_,_,Te_abbrev _,_) -> true
          | _ -> false
      end
    | _ -> false

let is_type_def_record  (((d, _), _, _):def) = 
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
type used_entities = { 
   used_consts : const_descr_ref list; 
   used_consts_set : Cdset.t;
   used_types : Path.t list; 
   used_types_set : Pset.t;
   used_modules : Path.t list; 
   used_modules_set : Pset.t;
   used_tnvars : TNset.t }

let reverse_used_entities ue =
  { used_consts  = List.rev ue.used_consts; 
    used_consts_set = ue.used_consts_set;
    used_types   = List.rev ue.used_types;
    used_types_set = ue.used_types_set;
    used_modules = List.rev ue.used_modules;
    used_modules_set = ue.used_modules_set;
    used_tnvars  = ue.used_tnvars }

let empty_used_entities = { 
    used_consts = []; 
    used_consts_set = Cdset.empty;
    used_types = []; 
    used_types_set = Pset.empty;
    used_modules = []; 
    used_modules_set = Pset.empty;
    used_tnvars = TNset.empty }

let used_entities_add_const ue c =
  if (Cdset.mem c ue.used_consts_set) then ue else
  {ue with used_consts = c :: ue.used_consts;
           used_consts_set = Cdset.add c ue.used_consts_set}

let used_entities_add_type ue p =
  if (Pset.mem p ue.used_types_set) then ue else
  {ue with used_types = p :: ue.used_types;
           used_types_set = Pset.add p ue.used_types_set}

let used_entities_add_module ue p =
  if (Pset.mem p ue.used_modules_set) then ue else
  {ue with used_modules = p :: ue.used_modules;
           used_modules_set = Pset.add p ue.used_modules_set}

let used_entities_add_tnvars ue tnvars =
  {ue with used_tnvars = TNset.union tnvars ue.used_tnvars}


let rec add_type_entities_aux (ue : used_entities) (t : Types.t) : used_entities =
  match t.t with
    | Tvar _ -> ue
    | Tfn(t1,t2) -> add_type_entities_aux (add_type_entities_aux ue t1) t2
    | Ttup(ts) -> 
        List.fold_left add_type_entities_aux ue ts
    | Tapp(ts,p) ->
        List.fold_left add_type_entities_aux (used_entities_add_type ue p) ts
    | Tbackend(ts,_) ->
        List.fold_left add_type_entities_aux ue ts
    | Tne _ -> ue
    | Tuvar _ -> ue

let add_type_entities (ue : used_entities) (t : Types.t) : used_entities =
  let ue = used_entities_add_tnvars ue (Types.free_vars t) in
  add_type_entities_aux ue t

let rec add_src_t_entities (ue : used_entities) (t : Types.src_t) : used_entities =
  match t.term with
    | Typ_wild _ -> ue
    | Typ_var _ -> ue
    | Typ_len _ -> ue
    | Typ_fn (t1, _, t2) -> add_src_t_entities (add_src_t_entities ue t1) t2
    | Typ_tup sp -> Seplist.fold_left (fun t ue -> add_src_t_entities ue t) ue sp
    | Typ_app (id, args) -> List.fold_left add_src_t_entities (used_entities_add_type ue id.descr) args
    | Typ_backend (_, args) -> List.fold_left add_src_t_entities ue args
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
    | P_backend(_,_,_,ps) -> 
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
    | Backend _ -> ue
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
      let ue = used_entities_add_module ue mid.descr in
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

and add_funcl_aux_entities (ue : used_entities) only_new ((_, c, ps, src_t_opt, _, e):funcl_aux) = begin
  let ue = used_entities_add_const ue c in
  if only_new then ue else begin
    let ue = List.fold_left add_pat_entities ue ps in
    let ue = match src_t_opt with 
      | Some (_, src_t) -> add_src_t_entities ue src_t 
      | _ -> ue 
    in
    let ue = add_exp_entities ue e in
    ue
  end
end

and add_def_aux_entities (t_opt : Target.target) (only_new : bool) (ue : used_entities) (d : def_aux) : used_entities = 
  match d with
      | Type_def(sk, tds) ->
         Seplist.fold_left (fun (_, _, type_path, texp, _) ue -> begin
           let ue = used_entities_add_type ue type_path in
           let ue = if only_new then ue else add_texp_entities ue texp in
           ue
         end) ue tds
      | Val_def(Let_def(_, targs, (p, nm, src_t_opt, _, e))) -> 
         if (not (in_targets_opt t_opt targs)) then ue else begin
           let ue = List.fold_left (fun ue  (_, c) -> used_entities_add_const ue c) ue nm in
           if only_new then ue else begin
             let ue = add_pat_entities ue p in
             let ue = match src_t_opt with 
               | Some (_, src_t) -> add_src_t_entities ue src_t 
               | _ -> ue 
             in
             let ue = add_exp_entities ue e in
             ue
           end
         end
      | (Val_def(Fun_def(_, _, targs, funs))) -> 
         if (in_targets_opt t_opt targs) then 
           Seplist.fold_left (fun clause ue -> add_funcl_aux_entities ue only_new clause) ue funs 
         else ue
      | Val_def(Let_inline(_,_,targs,_,c,_,_,e)) ->
         if (in_targets_opt t_opt targs) && not only_new then begin
           let ue = used_entities_add_const ue c in
           let ue = add_exp_entities ue e in
           ue
         end else ue
      | Lemma(_, _, targs, _, _, e) ->
          if (in_targets_opt t_opt targs) && (not only_new) then add_exp_entities ue e else ue
      | Module(_, _, mod_path, _, _, ds, _) -> begin
          let ue = used_entities_add_module ue mod_path in
          let ue = List.fold_left (add_def_entities t_opt only_new) ue ds in
          ue
        end
      | Rename(_, _, mod_path, _, m) -> begin
          let ue = used_entities_add_module ue mod_path in
          let ue = if only_new then ue else used_entities_add_module ue m.descr in
          ue
        end
      | OpenImport(_,ms) -> if only_new then ue else List.fold_left (fun ue m -> used_entities_add_module ue m.descr) ue ms
      | OpenImportTarget _ -> ue
      | Indreln(_,targ,names,rules) -> begin
          let add_rule (Rule (_,_,_,_,_,e_opt,_,_,n_ref,es),_) ue = begin
             let ue = used_entities_add_const ue n_ref in
             if only_new then ue else begin
               let ue = match e_opt with None -> ue | Some e -> add_exp_entities ue e in
               let ue = List.fold_left add_exp_entities ue es in
               ue
             end
          end in
          (* TODO: consider what to do about names *)
          Seplist.fold_left add_rule ue rules
        end
      | Val_spec(_,_,n_ref,_,_,(_, src_t)) ->begin
          let ue = used_entities_add_const ue n_ref in
          let ue = if only_new then ue else add_src_t_entities ue src_t in
          ue
        end
      | Class(_,_,n,tvar,_,_,body,_) -> (* TODO: classes broken, needs fixing in typechecking and AST *) ue
      | Instance(_,_,_,_,_) -> (* TODO: broken, needs fixing in typechecking and AST *) ue
      | Declaration(_) -> ue
      | Comment _ -> ue

and add_def_entities (t_opt : Target.target) (only_new : bool) (ue : used_entities) (((d, _), _, _) : def) : used_entities = 
  add_def_aux_entities t_opt only_new ue d


let add_checked_module_entities (t_opt : Target.target) only_new (ue : used_entities) (m : checked_module): used_entities = 
  let (dl, _) = m.typed_ast in 
  List.fold_left (add_def_entities t_opt only_new) ue dl

let get_checked_modules_entities (t_opt : Target.target) only_new (ml : checked_module list) : used_entities =
  reverse_used_entities (List.fold_left (add_checked_module_entities t_opt only_new) empty_used_entities ml)


(* check whether a definition is recursive using entities *)
let is_recursive_def (d:def_aux) =  
 match d with
  |  Val_def ((Fun_def (_, FR_rec _, _, sl))) -> begin 
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

(* check whether a definition is recursive using entities *)
let try_termination_proof targ c_env (d:def_aux) =  
 let l_unk = Ast.Trans (true, "try_termination_proof", None) in
 match d with
  |  Val_def ((Fun_def (_, FR_rec _, _, sl))) -> begin 
       let (is_rec, is_real_rec) = is_recursive_def d in
       let try_term = if (not is_real_rec) then true else begin
         let (_, pL) = Seplist.to_pair_list None sl in

         (* get the names of all newly defined functions *)
         let add_fun_ref s ((((_, c, _, _, _, _) : funcl_aux), _)) = if (List.mem c s) then s else c::s in
         let all_consts = List.fold_left add_fun_ref [] pL in

         let check_terminate c = begin
           let cd = c_env_lookup l_unk c_env c in
           match Target.Targetmap.apply_target cd.termination_setting targ with
             | None -> false
             | Some (Ast.Termination_setting_manual _) -> false
             | Some (Ast.Termination_setting_automatic _) -> true
         end in
          
         List.for_all check_terminate all_consts
       end in
       (is_rec, is_real_rec, try_term)
     end
  |  _ -> (false, false, true)


let mk_eta_expansion_exp t_env (vars : Name.t list) (e : exp) : exp =
begin
  let l = Ast.Trans (true, "mk_eta_expansion", Some (exp_to_locn e)) in

  (* make the variable names distinct from any already used names and from each other *)
  let fv_map = C.exp_to_free e in
  let vars' = Name.fresh_list (fun n -> not (Nfmap.in_dom n fv_map)) vars in
  
  (* get types *)
  let (arg_tyL, _) = strip_fn_type (Some t_env) (exp_to_typ e) in
  let (var_types, _) = Util.split_after (List.length vars') arg_tyL in

  (* get the typed list of variables*)
  let typed_vars = List.combine vars' var_types in

  (* make application *)
  let mk_var_app (e : exp) ((n: Name.t), (ty : Types.t)) = begin
    let var = C.mk_var l (Name.add_lskip n) ty in
    let ty = match (dest_fn_type (Some t_env) (exp_to_typ e)) with
      | Some (_, ty) -> ty
      | None -> raise (Reporting_basic.err_unreachable l "fun type already checked above")
    in
    C.mk_app l e var (Some ty) 
  end in
  let e' = List.fold_left mk_var_app e typed_vars in

  (* make fun *)
  let e'' = C.mk_fun l None (List.map (fun (n, ty) -> C.mk_pvar l (Name.add_lskip n) ty) typed_vars) None e' (Some (exp_to_typ e)) in

  e''
end

exception Constr_family_to_id_exn of string;;
let constr_family_to_id_aux l env (inst_type : t) (cf : constr_family_descr) : ((const_descr_ref id) list * (t -> (const_descr_ref id)) option) =
  (* check the constructors *)
  let check_constr c = begin
    let cd = c_env_lookup l env.c_env c in
    let c_string = Path.to_string cd.const_binding in
    let (t_args, t_base) = strip_fn_type (Some env.t_env) cd.const_type in
    let _ = if (TNset.subset (free_vars cd.const_type) (free_vars t_base)) then () else raise 
       (Constr_family_to_id_exn ("function " ^ c_string ^ " has type-variables not appearing in result type")) in
    let subst = Util.option_get_exn (Constr_family_to_id_exn ("function "^ c_string ^" has wrong result type")) (match_types t_base inst_type) in
    let inst = List.map (fun v -> Util.option_get_exn 
        (Constr_family_to_id_exn ("problem with " ^ c_string)) (TNfmap.apply subst v)) cd.const_tparams in

    let c_id = 
      { id_path = Id_none None;
        id_locn = l;
        descr = c;
        instantiation = inst } in
    let t_args' = List.map (type_subst subst) t_args in
    (c_id, t_args')   
  end in

  let constr_resl = List.map check_constr cf.constr_list in

  let bf = match cf.constr_case_fun with
    | None -> None
    | Some case_c -> begin
        let case_cd = c_env_lookup l env.c_env case_c in
        let case_string = Path.to_string case_cd.const_binding in
        let (t_args, ret_ty) = strip_fn_type (Some env.t_env) case_cd.const_type in
        let ret_ty_var = match ret_ty.t with
          | Tvar v -> Ty v
          | _ -> raise (Constr_family_to_id_exn ("return type of " ^ case_string ^ " is too special"))
        in

        let constr_args_list = if not cf.constr_exhaustive then (List.map snd constr_resl) @ [[]] else (List.map snd constr_resl) in
        let _ = if List.length constr_args_list + 1 = List.length t_args then () else 
           raise (Constr_family_to_id_exn ("number of given constructors and number of arguments of " ^ case_string ^ " don't match")) in

        let subst = (* get the substitution for the arguments as well as the return type variable *) begin
           match t_args with
             | [] -> raise (Reporting_basic.err_unreachable l "checked length before")
             | ty :: _ -> 
                 let _ = if (TNset.mem ret_ty_var (free_vars ty)) then raise 
                 (Constr_family_to_id_exn ("return type of " ^ case_string ^ " is too special")) in
                 Util.option_get_exn (Constr_family_to_id_exn ("type of first argument of " ^ case_string ^ " does not match pattern type")) 
                     (match_types ty inst_type)
        end in


        (* check that the argument type conincite with the types of the constructors *)
        let exn = Constr_family_to_id_exn ("type of arguments of " ^ case_string ^ " does not coincide with types of constructors") in
        let _ = List.iter2 (fun targ constr_args ->
          begin
            let (targ_args, targ_base) = strip_fn_type (Some env.t_env) targ in
            let _ = if (Types.check_equal env.t_env targ_base ret_ty) then () else raise exn in
            let _ = if (List.length targ_args = List.length constr_args) then () else raise exn in
            let _ = List.iter2 (fun targ_arg constr_arg ->
               if (Types.check_equal env.t_env (type_subst subst targ_arg) constr_arg) then () else raise exn
            ) targ_args constr_args in
            ()
          end) (List.tl t_args) constr_args_list
        in
        Some (fun ret_ty_inst -> begin
          let subst' = TNfmap.insert subst (ret_ty_var, ret_ty_inst) in
          let inst = List.map (fun v -> Util.option_get_exn (Constr_family_to_id_exn "") (TNfmap.apply subst' v)) case_cd.const_tparams in
          { id_path = Id_none None;
            id_locn = l;
            descr = case_c;
            instantiation = inst }           
        end)
    end
  in
  (List.map fst constr_resl, bf)


let constr_family_to_id l env (inst_type : t) (cf : constr_family_descr) : ((const_descr_ref id) list * (t -> (const_descr_ref id)) option) option =
try
   Some (constr_family_to_id_aux l env inst_type cf)
with Constr_family_to_id_exn _ -> None


let check_constr_family l env inst_type cf =
  try
    let _ = constr_family_to_id_aux l env inst_type cf in
    ()
  with Constr_family_to_id_exn s -> 
     raise (Reporting_basic.err_type l ("invalid constructor family: " ^ s))


let check_for_inline_cycles (targ : Target.target) (c_env : c_env) : unit = begin
  let l = Ast.Trans (false, "check_for_inline_cycles", None) in
  let report_error c = begin
    let cd = c_env_lookup l c_env c in
    let tr = match Target.Targetmap.apply_target cd.target_rep targ with
      | Some tr ->tr 
      | None -> raise (Reporting_basic.err_unreachable Ast.Unknown "since the target_rep is cyclic, it must exist")
    in
    let tr_l = const_target_rep_to_loc tr in
    raise (Reporting_basic.Fatal_error (Reporting_basic.Err_cyclic_inline (tr_l, Target.target_to_string targ, Path.to_string cd.const_binding)))
  end in


  let get_used_consts_exp (e : exp) : const_descr_ref list =
    let ue = add_exp_entities empty_used_entities e in
    ue.used_consts
  in

  let get_directly_used_consts (c : const_descr_ref) : const_descr_ref list  =
    let cd = c_env_lookup l c_env c in
    match Target.Targetmap.apply_target cd.target_rep targ with
    | Some (CR_inline (_, _, _, e)) -> get_used_consts_exp e
    | Some (CR_special (_, _, _, _)) -> []
    | Some (CR_simple (_,_,_,e)) -> get_used_consts_exp e
    | Some (CR_infix _) -> []
    | Some (CR_undefined _) -> []
    | None -> []
  in

  let rec check_for_inline_cycle_aux c_before c =
  begin
    if (List.mem c c_before) then report_error c else
    begin
      let sc = get_directly_used_consts c in
      let c_before' = c :: c_before in
      List.iter (check_for_inline_cycle_aux c_before') sc
    end
  end in

  let _ = List.iter (check_for_inline_cycle_aux []) (c_env_all_consts c_env) in
  ()
end


