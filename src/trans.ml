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
open Typed_ast_syntax
open Pattern_syntax
open Target
open Types
open Util
exception Trans_error of Ast.l * string

let r = Ulib.Text.of_latin1

type 'a macro = Macro_expander.macro_context -> 'a -> 'a option
type pat_macro = Macro_expander.pat_position -> pat macro

module Macros(E : sig val env : env end) = struct

module I = struct let d = E.env.t_env let i = E.env.i_env end
module C = Exps_in_context(struct let env_opt = Some E.env;; let avoid = None end)
module T = Types.Constraint(I)

let d = I.d
let inst = I.i
open E

(* Macros *)

let remove_singleton_record_updates _ e =
    match C.exp_to_term e with
      | Recup(s1, exp, s2, fields, s3) ->
        begin
            match Seplist.to_list fields with
              | [x] ->
                  let l = exp_to_locn e in
                  let td_opt = Types.type_defs_lookup_typ l E.env.t_env (exp_to_typ e) in
                  let field_count = match td_opt with 
                    | None -> 0 (* should not happen, since type occours in AST *)
                    | Some td -> begin 
                        match td.Types.type_fields with
                          | None -> 0 (* should not happen, since type is a record type *)
                          | Some fl -> List.length fl
                      end in
                  if field_count = 1 then
                    Some (C.mk_record l s1 fields s3 (Some (exp_to_typ e)))
                  else
                    None
              | _   -> None
        end
      | _ -> None
;;

let remove_multiple_record_updates _ e =
  let l_unk = Ast.Trans(true, "remove_multiple_record_updates", Some (exp_to_locn e)) in
    match C.exp_to_term e with
      | Recup(s1, e, s2, fields, s3) ->
        begin
            match List.rev (Seplist.to_list fields) with
              | [] -> None
              | [x] -> None
              | x::xs ->
                let singleton e =
                  Seplist.from_pair_list None [(e, Typed_ast.no_lskips)] None
                in
                let recup =
                  C.mk_recup l_unk s1 e s2 (singleton x) s3 None
                in
                let recups =
                  List.fold_left (fun recup -> fun x ->
                    C.mk_recup l_unk s2 recup s2 (singleton x) s2 None
                  ) recup xs
                in
                  Some recups
        end
      | _ -> None
;;


let sort_record_fields _ e =
  let l_unk = Ast.Trans(true, "sort_record_fields", Some (exp_to_locn e)) in
    match C.exp_to_term e with
      | Record(s1,fields,s2) -> if Seplist.length fields < 2 then None else
        begin
          let all_fields_opt = Util.option_bind (fun td -> td.Types.type_fields) (Types.type_defs_lookup_typ l_unk E.env.t_env (exp_to_typ e)) in
          let all_fields = Util.option_get_exn (Reporting_basic.err_unreachable l_unk "type of record is no record-type") all_fields_opt in
          let (hd_sep_opt, fieldsL) = Seplist.to_pair_list None fields in
          let find_field_fun r ((field_descr_id, _, _, _),s) = (r = field_descr_id.descr) in
          let rec find_field n b = function
                | [] -> raise Not_found
                | x::xs ->
                      (if find_field_fun n x then (x, b, xs) else
      		      let (y, b', ys) = find_field n true xs in (y, b', x::ys)) in
          let (changed, _, resultL) = try List.fold_left (fun (changed, fieldL, resultL) n -> 
               let (y, changed', ys) = find_field n changed fieldL in (changed', ys, y::resultL)) 
               (false, fieldsL, []) all_fields
            with Not_found -> (false, fieldsL, fieldsL) 
          in if (not changed) then None else begin
            let fields' = Seplist.from_pair_list hd_sep_opt (List.rev resultL) None in
            let res = C.mk_record l_unk s1 fields' s2 (Some (exp_to_typ e)) in
            let _ = Reporting.report_warning E.env (Reporting.Warn_record_resorted (exp_to_locn e, e)) in
            Some (res) end
        end 
      | _ -> None
;;

let remove_failwith_matches _ e =
  let l_unk = Ast.Trans(true, "remove_failwith_matches", Some (exp_to_locn e)) in
    match C.exp_to_term e with
      | Case (flag, skips, scrutinee, skips', pat_skips_exp_loc_seplist, skips'') ->
        let (fail_ref, _)      = get_const E.env "fail" in
        let (fail_with_ref, _) = get_const E.env "failwith" in
        let exp_contains_fail_or_failwith loc exp =
          match C.exp_to_term (fst (strip_app_exp exp)) with
            | Constant const_descr_ref_id ->
                (const_descr_ref_id.descr = fail_ref) || (const_descr_ref_id.descr = fail_with_ref)
            | _ -> false
        in
        let filter =
          Seplist.filter (fun (pat, skips, exp, loc) ->
            not (exp_contains_fail_or_failwith loc exp)
          ) pat_skips_exp_loc_seplist
        in
        if filter = pat_skips_exp_loc_seplist then
          None
        else
          let res = C.mk_case flag l_unk skips scrutinee skips' filter skips'' None in
            Some res
      | _ -> None
;;

(* Turn function | pat1 -> exp1 ... | patn -> expn end into
 * fun x -> match x with | pat1 -> exp1 ... | patn -> expn end *)
let remove_function _ e = Patterns.remove_function E.env (fun e -> e) e

(* Remove patterns from (fun ps -> ...), except for variable and 
 * (optionally) tuple patterns *)
(* Patterns.remove_fun is very similar, but introduces case-expressions *)
let remove_fun_pats keep_tup _ e = 
  let l_unk = Ast.Trans(true, "remove_fun_pats", Some (exp_to_locn e)) in
  let rec keep p = if keep_tup then Pattern_syntax.is_var_tup_pat p else Pattern_syntax.is_ext_var_pat p in
  let rec group acc = function
    | [] -> 
        if acc = [] then
          []
        else
          [(true,List.rev acc)]
    | p::ps -> 
        if keep p then
          group (p::acc) ps
        else if acc = [] then 
          (false,[p])::group [] ps 
        else 
          (true,List.rev acc)::(false,[p])::group [] ps
  in
    match C.exp_to_term e with
      | Fun(s1,ps,s2,e') ->
          let pss = group [] ps in
            begin
              match pss with
                | [(true,_)] -> None
                | _ ->
                    let e =
                      List.fold_right
                        (fun ps res_e ->
                           match ps with
                             | (true,ps) ->
                                 C.mk_fun l_unk space ps space res_e None
                             | (false,[p]) ->
                                 C.mk_function l_unk 
                                   space 
                                   (Seplist.from_list [((p,space,res_e,l_unk),no_lskips)])
                                   no_lskips
                                   None
                             | _ -> assert false)
                        pss
                        e'
                    in
                      match (C.exp_to_term e) with
                        | Fun(_,ps,_,e') ->
                            Some(C.mk_fun (exp_to_locn e) s1 ps s2 e'
                                   (Some(exp_to_typ e)))
                        | Function(_,x,_) ->
                            Some(C.mk_function (exp_to_locn e) 
                                   (Ast.combine_lex_skips s1 s2) x no_lskips
                                   (Some(exp_to_typ e)))
                        | _ -> assert false
            end
      | _ -> None
;;

let remove_unit_pats _ _ p =
  let l_unk = Ast.Trans(true, "remove_unit_pats", Some p.locn) in
  match p.term with
    | P_lit({ term = L_unit(s1, s2)}) ->
        Some(C.mk_pwild l_unk s1 { Types.t = Types.Tapp([], Path.unitpath) } )
     | _ -> None

(* Turn comprehensions into nested folds, fails on unrestricted quantifications *)
let remove_comprehension for_lst _ e = 
  let l_unk n = Ast.Trans(true, "remove_comprehension " ^ string_of_int n, Some (exp_to_locn e)) in
  match C.exp_to_term e with
  | Comp_binding(is_lst,s1,e1,s2,s3,qbs,s4,e2,s5) when is_lst = for_lst ->
      let (acc_name,param_name) = 
        let avoid = 
          List.fold_right
            (fun qb s ->
               match qb with 
                 | Qb_var(n) ->
                     raise (Trans_error(l_unk 0, "cannot generate code for unrestricted set comprehension"))
                 | Qb_restr(_,_,_,_,e,_) ->
                     Nfmap.union (C.exp_to_free e) s)
            qbs
            (Nfmap.union (C.exp_to_free e1) (C.exp_to_free e2))
        in
        match
          List.map (fun n -> Name.add_pre_lskip space (Name.add_lskip n))
            (Name.fresh_num_list 2 (r"x") (fun n -> not (Nfmap.in_dom n avoid)))
        with
          | [x;y] -> (x,y)
          | _ -> assert false
      in
      let acc_var = C.mk_var (l_unk 1) acc_name (exp_to_typ e) in
      let acc_pat = C.mk_pvar (l_unk 2) acc_name (exp_to_typ e) in
      let result_type = 
        { Types.t = 
            Types.Tapp([(exp_to_typ e1)], 
                       if is_lst then Path.listpath else Path.setpath) }
      in
      let list_fold_const t =
        append_lskips space
          (mk_const_exp env (l_unk 4) "list_fold_right" [t; result_type])
      in
      let set_fold_const t =
        append_lskips space
          (mk_const_exp env (l_unk 5) "set_fold" [t; result_type])
      in
      let f = 
        if is_lst then
          let add_const = (mk_const_exp env (l_unk 8) "list_cons" [exp_to_typ e1]) in
            C.mk_infix (l_unk 9) e1 add_const acc_var None
        else
          let add_const = mk_const_exp env (l_unk 11) "set_add" [exp_to_typ e1] in
          let f_app1 = 
            C.mk_app (l_unk 12) add_const e1 None
          in
            C.mk_app (l_unk 13) f_app1 acc_var None
      in
      let rec helper = function
        | [] -> C.mk_if (l_unk 14) space e2 space f space acc_var None
        | Qb_var(n)::_ -> assert false
        | Qb_restr(is_lst,s1',p,s2',e,s3')::qbs ->
            let param_var = C.mk_var (l_unk 15) param_name p.typ in
            let param_pat = C.mk_pvar (l_unk 16) param_name p.typ in
            let res = helper qbs in
            let s = lskips_only_comments [s1';s2';s3'] in
            let arg_fun = 
              if Pattern_syntax.single_pat_exhaustive p then
                C.mk_fun (l_unk 17) s [p; acc_pat] space res None
              else
                C.mk_fun (l_unk 18) s [param_pat; acc_pat] space
                  (C.mk_case false (l_unk 19) space param_var space
                     (Seplist.from_list
                        [((p, space, res, l_unk 20), space);
                         ((C.mk_pwild (l_unk 21) space p.typ, space, acc_var, 
                           (l_unk 22)), space)])
                     None
                     None)
                  None
            in
            let (arg1, arg2, arg3) = if is_lst then (arg_fun, acc_var, e) else (arg_fun, e, acc_var) in
            let app1 = 
              C.mk_app (l_unk 23) 
                (if is_lst then
                   list_fold_const p.typ 
                 else 
                   set_fold_const p.typ) 
                arg1 
                None
            in
            let app2 = C.mk_app (l_unk 24) app1 arg2 None in
              C.mk_app (l_unk 25) app2 arg3 None
      in
      let t = 
        { Types.t = 
            Types.Tapp([exp_to_typ e1], if for_lst then Path.listpath else Path.setpath) }
      in
      let empexp = 
        (if for_lst then C.mk_list else C.mk_set) 
          (l_unk 26) space (Seplist.from_list []) None t in
      let letexp = 
        C.mk_let (exp_to_locn e) 
          s1 
          (C.mk_let_val (l_unk 27) acc_pat None space empexp) 
          (lskips_only_comments [s2;s3;s4;s5])
          (helper qbs)
          None
      in
        Some(letexp)
  | _ -> 
      None

let rec var_tup_pat_eq_exp p e =
  match dest_var_pat p with
    | Some n -> (match dest_var_exp e with None -> false | Some n' -> Name.compare n n' = 0)
    | None -> 
      begin
        match dest_tup_pat None p with 
          | None -> false
          | Some pL -> 
	    begin
              match dest_tup_exp None e with 
                | None -> false
                | Some eL -> 
		    (List.length pL = List.length eL) &&
		    List.for_all2 var_tup_pat_eq_exp pL eL
	    end
      end

(* Replaces set comprehension by introducing set_image and set_filter. Perhaps
   cross is added as well. *)
let remove_set_comprehension_image_filter allow_sigma _ e = 
  let l_unk = Ast.Trans(true, "remove_set_comprehension_image_filter", Some (exp_to_locn e)) in
  match C.exp_to_term e with
  | Comp_binding(false,s1,e1,s2,s3,qbs,s4,e2,s5) ->
      let all_quant_vars = List.fold_left (fun acc -> function Qb_var _ -> acc | Qb_restr (_, _, p, _, _, _) -> 
                              NameSet.union (nfmap_domain p.rest.pvars) acc) NameSet.empty qbs in
      let ok = List.for_all (function Qb_var _ -> false | Qb_restr (_, _, p, _, e, _) -> is_var_tup_pat p) qbs in
      let need_sigma = List.exists (function Qb_var _ -> false | Qb_restr (_, _, p, _, e, _) -> not (
                   NameSet.is_empty (NameSet.inter all_quant_vars (nfmap_domain (C.exp_to_free e))))) qbs in
      if not (ok && ((not need_sigma) || allow_sigma)) then None else
      begin
        (* filter the quantifiers that need to be in a cross-product and ones that need to go to the expression *)
        let all_vars = NameSet.union (nfmap_domain (C.exp_to_free e1)) all_quant_vars in
        let (qbs_set_p, qbs_set_e, qbs_cond) = List.fold_right (fun qb (s_p, s_e, c) -> (
           match qb with 
              Qb_var _ -> raise (Reporting_basic.err_unreachable l_unk "previosly checked")
            | Qb_restr (is_lst, sk1, p, sk2, e, sk3) -> begin
                let can_move = NameSet.is_empty (NameSet.inter all_vars (nfmap_domain p.rest.pvars)) in
                if can_move then (s_p, s_e, qb::c) else (
                  let e' = if is_lst then mk_from_list_exp env e else e in
                  (p::s_p, e'::s_e, c))
              end
             )) qbs ([], [], []) in

        let ok2 = (match qbs_set_p with [] -> false | _ -> true) in
        if not ok2 then None else
        begin
          (* new condition *)
          let e2' = if List.length qbs_cond = 0 then e2 else 
                      C.mk_quant l_unk (Ast.Q_exists None) qbs_cond space e2 (Some bool_ty) in
          (* cross or big_union set *)
          let p = mk_tup_pat qbs_set_p in
          let mk_exp env s (p, s') = if need_sigma then mk_set_sigma_exp env s' (mk_fun_exp [p] s) else mk_cross_exp env s' s in
          let s = List.fold_left (mk_exp env) (List.hd (List.rev qbs_set_e)) (List.tl (List.rev (List.combine qbs_set_p qbs_set_e))) in

          let res0 = mk_set_filter_exp env (mk_fun_exp [p] e2') s in
          let res1 = if (var_tup_pat_eq_exp p e1) then res0 else
                       mk_set_image_exp env (mk_fun_exp [p] e1) res0 in
          Some res1
        end
      end
  | _ -> 
      None

(* Replaces Setcomp with Comp_binding. *)
let remove_setcomp _ e = 
  let l_unk = Ast.Trans(true, "remove_setcomp", Some (exp_to_locn e)) in
  match C.exp_to_term e with
   | Setcomp(s1,e1,s2,e2,s3,bindings) -> begin
       let e1_free_map = C.exp_to_free e1 in
       let qb_name (n : Name.t) = begin
         match Nfmap.apply e1_free_map n with
            | None -> None
            | Some ty -> Some (Qb_var{ term = Name.add_lskip n; locn = l_unk; typ = ty; rest = (); })
       end in 
       match Util.map_all qb_name (NameSet.elements bindings) with
         | None -> None
         | Some qbs -> Some (C.mk_comp_binding l_unk false s1 e1 s2 space qbs space e2 s3 (Some (exp_to_typ e)))
     end
  | _ -> None

let remove_sets context e = 
  let l_unk = Ast.Trans(true, "remove_sets", Some (exp_to_locn e)) in
  match C.exp_to_term e with
  | Set(s1,es,s2) ->
      begin
        match (Types.head_norm d (exp_to_typ e)).Types.t with
          | Types.Tapp([t],_) ->
              let lst = 
                C.mk_list (exp_to_locn e) 
                  space es s2 { Types.t = Types.Tapp([t],Path.listpath) }
              in
              let from_list = mk_const_exp env l_unk "set_from_list" [t] in
              let app = C.mk_app l_unk from_list lst None in
                Some(app)
          | _ -> 
              assert false
      end
  | Setcomp _ ->
      raise (Trans_error(l_unk, "cannot generate code for unrestricted set comprehension"))
  | _ -> remove_comprehension false context e

(* Turn list comprehensions into nested folds *)
let remove_list_comprehension e = remove_comprehension true e
let remove_set_comprehension e = remove_comprehension false e

let get_quant_lskips = function
  | Ast.Q_forall(s) -> s
  | Ast.Q_exists(s) -> s
;;

let strip_quant_lskips = function
  | Ast.Q_forall(s) -> Ast.Q_forall(space)
  | Ast.Q_exists(s) -> Ast.Q_exists(space)
;;

let get_quant_impl (env : Typed_ast.env) is_lst t : Ast.q -> exp = 
  let l_unk = Ast.Trans(true, "get_quant_impl", None) in
  let module C = Exps_in_context (struct let env_opt = Some env;; let avoid = None end) in
  let f label s =
    let d = fst (get_const env label) in
      append_lskips s
        (C.mk_const l_unk 
          { id_path = Id_none None;
             id_locn = l_unk;
             descr = d;
             instantiation = [t] }
           None)
  in
    function
      | Ast.Q_forall(s) ->
          if is_lst then
            f "list_forall" s
          else
            f "set_forall" s
      | Ast.Q_exists(s) ->
          if is_lst then
            f "list_exists" s
          else
            f "set_exists" s
;;

(* Turn quantifiers into iteration, fails on unrestricted quantifications *)
let remove_quant context e = 
  let l_unk = Ast.Trans(true, "remove_quant", Some (exp_to_locn e)) in
  match C.exp_to_term e with
  | Quant(q,[],s,e) ->
      Some(append_lskips s e)
  | Quant(q,qb::qbs,s1,e') ->
      begin
        match qb with
          | Qb_var(n) ->
              raise (Trans_error(l_unk, "cannot generate code for unrestricted quantifier"))
          | Qb_restr(is_lst,s2,p,s3,e_restr,s4) ->
              let q_impl = get_quant_impl E.env is_lst p.typ q in
              let f = 
                C.mk_fun l_unk
                  (lskips_only_comments [s2;s3;s4])
                  [pat_append_lskips space p] 
                  space
                  (C.mk_quant l_unk (strip_quant_lskips q) qbs s1 e' None)
                  None
              in
              let app1 = C.mk_app l_unk q_impl f None in
                Some(C.mk_app (exp_to_locn e) app1 e_restr None)
      end
  | _ -> None
;;

let remove_quant_coq context e = 
  if context = Macro_expander.Ctxt_theorem then
    None
  else
    let l_unk = Ast.Trans(true, "remove_quant_coq", Some (exp_to_locn e)) in
    match C.exp_to_term e with
    | Quant(q,[],s,e) ->
        Some(append_lskips s e)
    | Quant(q,qb::qbs,s1,e') ->
        begin
          match qb with
            | Qb_var(n) ->
                raise (Trans_error(l_unk, "cannot generate code for unrestricted quantifier"))
            | Qb_restr(is_lst,s2,p,s3,e_restr,s4) ->
                let q_impl = get_quant_impl E.env is_lst p.typ q in
                let f = 
                  C.mk_fun l_unk
                    (lskips_only_comments [s2;s3;s4])
                    [pat_append_lskips space p] 
                    space
                    (C.mk_quant l_unk (strip_quant_lskips q) qbs s1 e' None)
                    None
                in
                let app1 = C.mk_app l_unk q_impl f None in
                  Some(C.mk_app (exp_to_locn e) app1 e_restr None)
        end
    | _ -> None
;;


(* Turn forall (x MEM L). P x into forall (x IN Set.from_list L). P x *)
let list_quant_to_set_quant _ e = 
  let l_unk = Ast.Trans(true, "list_quant_to_set_quant", Some (exp_to_locn e)) in
  match C.exp_to_term e with
  | Quant(q,qbs,s1,e') ->
      let qbs =
        Util.map_changed
          (fun e -> match e with
             | Qb_restr(is_lst,s2,p,s3,e,s4) when is_lst->
                 let lst_to_set = 
                   append_lskips space
                     (mk_const_exp env l_unk "set_from_list" [p.typ])
                 in
                 let app = C.mk_app l_unk lst_to_set e None in
                   Some(Qb_restr(false,s2,p,s3,app,s4))
             | _ -> None)
          qbs
      in
        begin
          match qbs with
            | None -> None
            | Some(qbs) -> Some(C.mk_quant (exp_to_locn e) q qbs s1 e' None)
        end
  | _ -> None


(* Turn restricted quantification into unrestricted quantification:
 * { f x | forall (p IN e) | P x } goes to
 * { f x | FV(p) | forall FV(p). p IN e /\ P x } 

 * In order to do this the pattern p is converted into an expression.
 * This is likely to fail for more complex patterns. In these cases, pattern 
 * compilation is needed. 
 *)
let remove_set_restr_quant _ e = 
  let l_unk = Ast.Trans(true, "remove_set_restr_quant", Some (exp_to_locn e)) in
  let qb_OK = (function | Qb_var _ -> true | Qb_restr _ -> false) in
  try (
  match C.exp_to_term e with
  | Comp_binding(false,s1,e1,s2,s3,qbs,s4,e2,s5) ->
      if List.for_all qb_OK qbs then
        None
      else
        let and_const = mk_const_exp env l_unk "conjunction" [] in
        let in_const t = mk_const_exp env l_unk "set_member" [t] in
        let mem_const t = mk_const_exp env l_unk "list_member" [t] in
        let pred_exp =
          List.fold_right 
            (fun qb res_e ->
               match qb with
                 | Qb_var(n) -> res_e
                 | Qb_restr(is_lst, s1', p, s2', e', s3') ->
                     let e =
                       C.mk_paren l_unk 
                         s1'
                         (C.mk_infix l_unk
                            (pat_to_exp env p)
                            (append_lskips s2' (if is_lst then mem_const p.typ else in_const p.typ))
                            e'
                            None)
                         s3'
                         None
                     in
                       C.mk_infix l_unk
                         e
                         (append_lskips space and_const)
                         res_e
                         None)
            qbs
            e2
        in
        let new_qbs = 
          List.concat
            (List.map 
               (function
                  | Qb_var(n) -> [Qb_var(n)]
                  | Qb_restr(_,_,p,_,_,_) -> List.map (fun v -> Qb_var(v)) (Pattern_syntax.pat_vars_src p))
               qbs)
        in
          Some(C.mk_comp_binding l_unk
                 false s1 e1 s2 s3 new_qbs s4 pred_exp s5 None)
  | _ -> None)
  with Pat_to_exp_unsupported (l, m) -> 
    (Reporting.report_warning env (Reporting.Warn_general (true, exp_to_locn e, m^" in restricted set comprehension")); None) (* it can still be handled by pattern compilation *)


(* Moves quantification to the condition part of the 
   set comprehension, if it does not concern any variables in the pattern
 * { f x | forall (p IN e) xx yy | P x } goes to 
 * { f x | forall xx yy | exists (p IN e). P x } 
 * if x notin FV p.
 *)
let cleanup_set_quant _ e = 
  let l_unk = Ast.Trans(true, "cleanup_set_restr_quant", Some (exp_to_locn e)) in
  match C.exp_to_term e with
  | Comp_binding(false,s1,e1,s2,s3,qbs,s4,e2,s5) ->
      let used_vars = List.fold_left (fun acc -> function 
             Qb_var nsa -> acc
           | Qb_restr (_, _, _, _, e, _) -> NameSet.union (nfmap_domain (C.exp_to_free e)) acc)
         (nfmap_domain (C.exp_to_free e1)) qbs in

      let can_move = function 
          Qb_var nsa -> not (NameSet.mem (Name.strip_lskip nsa.term) used_vars)
	| Qb_restr (_, _, p, _, e, _) ->
            NameSet.is_empty (NameSet.inter used_vars (nfmap_domain p.rest.pvars)) 
      in
      let (qbs_move, qbs_keep) = List.partition can_move qbs in
      if List.length qbs_move = 0 then
        None
      else
        let e2' = C.mk_quant l_unk (Ast.Q_exists None) qbs_move  space e2 (Some bool_ty) in 
        let res = C.mk_comp_binding l_unk false s1 e1 s2 s3 qbs_keep s4 e2' s5 (Some (exp_to_typ e)) in
          Some res
  | _ -> None

(* Turn unrestricted comb-bindings into set_comb
 * { f x | x | P x y1 ... yn } goes to
 * { f x | P x y1 ... yn } 
 *)
let remove_set_comp_binding _ e = 
  let l_unk = Ast.Trans(true, "remove_comp_binding", Some (exp_to_locn e)) in
  let qb_OK = (function | Qb_var _ -> true | Qb_restr _ -> false) in
  match C.exp_to_term e with
  | Comp_binding(false,s1,e1,s2,s3,qbs,s4,e2,s5) ->
      if not (List.for_all qb_OK qbs) then None
      else begin
        let e_vars = nfmap_domain (C.exp_to_free e1) in
        let b_vars = begin 
          let bound_vars = List.map (function Qb_var v -> Name.strip_lskip (v.term) | _ -> 
               raise (Reporting_basic.err_unreachable l_unk "Unreachable because of qb_OK check")) qbs in
          let module NameSetE = Util.ExtraSet(NameSet) in
          let bvs = NameSetE.from_list bound_vars in
          bvs
        end in
        if not (NameSet.equal e_vars b_vars) then
          None
        else begin
          let s234 = (Ast.combine_lex_skips s2 (Ast.combine_lex_skips s3 s4)) in
          let res = C.mk_setcomp l_unk s1 e1 s234 e2 s5 e_vars (Some (exp_to_typ e)) in
          Some res
        end
      end 
  | _ -> None


(* Turn restricted quantification into unrestricted quantification.
 * forall (p IN e). P x  goes to
 * forall FV(p). p IN e --> P x 
 * patterns, for which pat_OK returns true are kept 
 *)
let remove_restr_quant pat_OK _ e = 
  let l_unk = Ast.Trans(true, "remove_restr_quant", Some (exp_to_locn e)) in
  let qb_OK = (function | Qb_var _ -> true | Qb_restr(_,_,p,_,_,_) -> pat_OK p) in
  try (match C.exp_to_term e with
  | Quant(q,qbs,s,e) ->
      if List.for_all qb_OK qbs then
        None
      else
        let imp_const = mk_const_exp env l_unk "implication" [] in
        let and_const = mk_const_exp env l_unk "conjunction" [] in
        let comb_const = match q with Ast.Q_forall _ -> imp_const | Ast.Q_exists _ -> and_const in
        let in_const t = mk_const_exp env l_unk "set_member" [t] in
        let mem_const t = mk_const_exp env l_unk "list_member" [t] in
        let pred_exp =
          List.fold_right 
            (fun qb res_e ->
               match qb with
                 | Qb_var(n) -> res_e
                 | Qb_restr(is_lst, s1', p, s2', e', s3') ->
                     if Pattern_syntax.is_var_wild_pat p then res_e else begin
                       let e =
                         C.mk_paren l_unk 
                           s1'
                           (C.mk_infix l_unk
                              (pat_to_exp env p)
                              (append_lskips s2' (if is_lst then mem_const p.typ else in_const p.typ))
                              e'
                              None)
                           s3'
                           None
                       in
                         C.mk_infix l_unk
                           e
                           (append_lskips space comb_const)
                           res_e
                           None
                    end)
            qbs
            e
        in
        let new_qbs = 
          List.concat
            (List.map 
               (fun qb -> match qb with
                  | Qb_var(n) -> [Qb_var(n)]
                  | Qb_restr(_,_,p,_,_,_) -> (if pat_OK p then [qb] else (List.map (fun v -> Qb_var(v)) (Pattern_syntax.pat_vars_src p))))
               qbs)
        in
          Some(C.mk_quant (exp_to_locn e) q new_qbs s pred_exp None)
  | _ -> None)
  with Pat_to_exp_unsupported (l, m) -> 
    (Reporting.report_warning env (Reporting.Warn_general (true, exp_to_locn e, m^" in restricted set comprehension")); None) (* it can still be handled by pattern compilation *)


let tnfmap_apply m k =
  match Types.TNfmap.apply m k with
    | None -> assert false
    | Some x -> x

let remove_num_lit _ e =
  let l = Ast.Trans(false, "remove_num_lit", Some (exp_to_locn e)) in
  match C.exp_to_term e with
    | Lit lit -> begin
        match lit.term with 
          | L_num (sk, i, org_i) -> begin
              let (fromNumeral_id, _) = get_const_id env l "fromNumeral" [exp_to_typ e] in
              let numeral_ty  = { Types.t = Types.Tapp ([], Path.numeralpath)  } in
              let ty_0 = { Types.t = Types.Tfn (numeral_ty, exp_to_typ e) } in

              let exp0 = C.mk_const l fromNumeral_id (Some ty_0) in
              let lit1 = C.mk_lnumeral l sk i org_i (Some numeral_ty) in
              let exp1 = C.mk_lit l lit1 (Some numeral_ty) in
              let exp2 = C.mk_app l exp0 exp1 (Some (exp_to_typ e)) in
              Some exp2
            end
          | _ -> None
      end
    | _ -> None




(* remove a class-method and replace it either with the instance method or add a dictionary style passing argument *)
let remove_method (target : Target.target) try_dict _ e =
  let l_unk = Ast.Trans(true, "remove_method", Some (exp_to_locn e)) in
  match C.exp_to_term e with
    | Constant(c) ->
        begin
          let c_descr = c_env_lookup l_unk env.c_env c.descr in
          match c_descr.env_tag with
            | K_method ->
                begin 
                  match (c_descr.const_class, c.instantiation) with
                    | ([(c_path,tparam)],[targ]) -> 
                        begin
                          match Types.get_matching_instance d (c_path, targ) inst with
                            | Some (instance, subst) ->
                                (* There is an instance for this method at this type, so
                                 * we directly call the instance *)
                                begin
                                  let new_const_ref = lookup_inst_method_for_class_method l_unk instance c.descr in
                                  let new_const_descr = c_env_lookup l_unk env.c_env new_const_ref in
                                  let id = 
                                    { id_path = Id_none (Typed_ast.ident_get_lskip c);
                                      id_locn = c.id_locn;
                                      descr = new_const_ref;
                                      instantiation = List.map (tnfmap_apply subst) new_const_descr.const_tparams; }
                                  in
                                  let new_e = C.mk_const l_unk id None in Some(new_e)
                                end
                            | None -> 
                                let is_inlined = match Targetmap.apply_target c_descr.target_rep target with
                                  | Some (CR_inline _) -> true
                                  | _ -> false
                                in
                                if is_inlined || (not try_dict) then None else (
                                let tv = 
                                  match targ.Types.t with
                                    | Types.Tvar tv -> Types.Ty tv
                                    | Types.Tne { Types.nexp = Types.Nvar v } -> Types.Nv v
                                    | _ -> 
                                      (* there is no instance, yet typechecking did not detect an
                                         unsatisfiable type-class constraint. This means that the
                                         constraint is on a type-variable. *)
                                      raise (Reporting_basic.err_unreachable l_unk "because there was no instance")
                                in
                                let cd = lookup_class_descr l_unk env c_path in
                                let n = class_path_to_dict_name c_path tv in
                                let n_sk = Name.add_pre_lskip (ident_get_lskip c) (Name.add_lskip n) in
                                let t = class_descr_get_dict_type cd targ in
                                let dict = C.mk_var l_unk n_sk t in

                                let field = 
                                  { id_path = Id_none None;
                                    id_locn = c.id_locn;
                                    descr = lookup_field_for_class_method l_unk cd c.descr;
                                    instantiation = [targ] }
                                in
                                let new_e = 
                                  C.mk_field l_unk dict None field (Some (exp_to_typ e))
                                in
                                    Some(new_e))
                        end
                    | _ -> assert false
                end
            | _ -> None
        end
    | _ -> None


let remove_method_pat _ _ p =
  let l_unk = Ast.Trans(true, "remove_method_pat", Some (p.locn)) in
  match p.term with
    | P_const(c, ps) ->
        begin
          let c_descr = c_env_lookup l_unk env.c_env c.descr in
          match c_descr.env_tag with
            | K_method ->
                begin 
                  match (c_descr.const_class, c.instantiation) with
                    | ([(c_path,tparam)],[targ]) -> 
                        begin
                          match Types.get_matching_instance d (c_path, targ) inst with
                            | Some (instance, subst) ->
                                (* There is an instance for this method at this type, so
                                 * we directly call the instance *)
                                begin
                                  let new_const_ref = lookup_inst_method_for_class_method l_unk instance c.descr in
                                  let new_const_descr = c_env_lookup l_unk env.c_env new_const_ref in
                                  let id = 
                                    { id_path = Id_none (Typed_ast.ident_get_lskip c);
                                      id_locn = c.id_locn;
                                      descr = new_const_ref;
                                      instantiation = List.map (tnfmap_apply subst) new_const_descr.const_tparams; }
                                  in
                                  let new_e = C.mk_pconst l_unk id ps None in Some(new_e)
                                end
                            | None -> None (* no instance, so don't do a thing. Perhaps something else
                                              takes care of this constant *)
                        end
                    | _ -> assert false
                end
            | _ -> None
        end
    | _ -> None


(* remove class constraints from constants by adding explicit dictionary arguments. *)

let remove_class_const_aux l_unk targ mk_exp c =
  let c_descr = c_env_lookup l_unk env.c_env c.descr in
  if const_descr_has_target_rep targ c_descr then (* if the constant is represented specially, don't touch it *) None else
  let const_constraints = List.filter (fun (c, _) -> not (class_all_methods_inlined_for_target l_unk env targ c)) c_descr.const_class in

  match (const_constraints, Targetmap.apply_target c_descr.const_no_class targ) with
      | (([], _) | (_, None)) ->                 
          (* if there are no class constraints, there is nothing to do *)
          None
      | (_, Some c_ref') ->
          let subst = Types.TNfmap.from_list2 c_descr.const_tparams c.instantiation in
          let class_constraint_to_arg (c_path, tv) =
	    begin
              let t_inst = tnfmap_apply subst tv in
              match Types.get_matching_instance d (c_path, t_inst) inst with
                | Some(inst, subst) -> 
                  begin
                     (* if there is a matching instance, we know which dictionary to attach*)                                 
                     let dict_const_descr = c_env_lookup l_unk env.c_env inst.inst_dict in
                       C.mk_const l_unk
                         { id_path = Id_none None;
                           id_locn = l_unk;
                           descr = inst.inst_dict;
                           instantiation = List.map (tnfmap_apply subst) dict_const_descr.const_tparams }
                         None
                  end
                | None ->
                    (* it's not bound, so the constraint is propagating. Use the argument as a free var therefore *)
                    let tv = 
                      match t_inst.Types.t with
                        | Tvar tv -> Ty tv
                        | Tne { nexp = Nvar v } -> Nv v
                        | _ -> raise (Reporting_basic.err_unreachable l_unk "because there was no instance")
                    in
                    let cd = lookup_class_descr l_unk env c_path in
                    let t = class_descr_get_dict_type cd t_inst in
                        C.mk_var l_unk (Name.add_lskip (class_path_to_dict_name c_path tv)) t
            end
          in
          let args = List.map class_constraint_to_arg const_constraints in          
          let new_e = 
            List.fold_left
              (fun e arg -> C.mk_app l_unk e arg None)
              (mk_exp {c with descr = c_ref'})
              args
          in
            Some(new_e)
     

let remove_class_const targ _ e =
  let l_unk = Ast.Trans(true, "remove_class_const", Some (exp_to_locn e)) in
  match C.exp_to_term e with
    | Constant(c) ->
        remove_class_const_aux l_unk targ (fun c' -> (C.mk_const l_unk c' None)) c
    | Field(e,sk,fd) ->
        remove_class_const_aux l_unk targ (fun fd' -> (C.mk_field l_unk e sk fd' None)) fd
    | _ -> None


(*Convert nexpressions to expressions *)
let nexp_to_exp n =
   let l_unk = Ast.Trans (true, "nexp_to_exp", None) in
   let num_type = nat_ty in
   let bin_op_type = { Types.t = Types.Tfn(num_type,num_type) } in
   let rec to_exp n =
      match n.Types.nexp with
      | Types.Nvar(n) -> C.mk_nvar_e l_unk Typed_ast.no_lskips n num_type
      | Types.Nconst(i) -> let lit =  C.mk_lnum l_unk Typed_ast.no_lskips i None num_type in
                           C.mk_lit l_unk lit (Some num_type)
      | Types.Nadd(n1,n2) -> 
               let (plus_const_id, _) = get_const_id env l_unk "addition" [] in
               let plus = C.mk_const l_unk plus_const_id (Some bin_op_type) in
               C.mk_infix l_unk (to_exp n1) plus (to_exp n2) (Some num_type)
      | Types.Nmult(n1,n2) ->
               let (mult_const_id, _) = get_const_id env l_unk "multiplication" [] in
               let mult = C.mk_const l_unk mult_const_id (Some bin_op_type) in
               C.mk_infix l_unk (to_exp n1) mult (to_exp n2) (Some num_type)
      | _ -> assert false
    in to_exp n

let rec remove_tne ts =
  match ts with 
    | [] -> [],[]
    | ({Types.t = Types.Tne _} as n) :: ts -> let (tns,oths) = remove_tne ts in
                                              (n::tns,oths)
    | t :: ts -> let (tns,oths) = remove_tne ts in
                 (tns,t::oths)

(*add numeric parameter for nexp type parameter in function calls with constants*)
let add_nexp_param_in_const _ e =
  let l_unk = Ast.Trans(true, "add_nexp_param_in_const", Some (exp_to_locn e)) in
  match C.exp_to_term e with
    | Constant(c) ->
        begin
          let c_descr = c_env_lookup l_unk env.c_env c.descr in
          match c_descr.env_tag with
            | K_method -> None 
            | K_let ->
                if c_descr.const_tparams = [] then None
                else    
                  let (nvars,tvars) = Types.tnvar_split c_descr.const_tparams in
                  if nvars = [] then None
                  else
                    let (c_path1,c_path2) = Path.to_name_list c_descr.const_binding in
                    let (new_c_ref, new_c_descr) = names_get_const env c_path1 c_path2 in
                    (* This causes the add_nexp_param_in_const to terminate as the def_trans will update nvar types in the descr,
                       and the add_nexp updates the local descr. This only works when the macro is run after the def_trans for nvars
                       and before other macros have updated the local descr.
                    *)
                    if c.descr = new_c_ref then None
                    else 
                      let (args,instances) = remove_tne c.instantiation in
                      let args = List.map (fun t -> match t.Types.t with | Types.Tne(n) -> nexp_to_exp n | _ -> assert false) args in
                      let new_id = {c with descr = new_c_ref } in
                      (*let _ = Format.printf "%a@ =@ %a@\n" Types.pp_type (exp_to_typ (C.mk_const l_unk new_id None)) Types.pp_type (exp_to_typ e) in*)
                      let new_e = 
                        List.fold_left
                          (fun e arg -> C.mk_app l_unk e arg None)
                          (C.mk_const l_unk new_id None)
                           args in
                        Some(new_e)
            | _ -> None
        end
    | _ -> None

(*Replace vector access with an appropriate external library call, ocaml specific at the moment*)
let remove_vector_access _ e =
  let l_unk = Ast.Trans(true, "remove_vector_acc", Some (exp_to_locn e)) in
  match C.exp_to_term e with
    | VectorAcc(v, sk1, i, sk2) -> 
      let vlength = match (exp_to_typ v).Types.t with | Types.Tapp([n;a],_) -> n | _ -> assert false in
      let num_type = nat_ty in
      let acc_typ1 = { Types.t = Types.Tfn(exp_to_typ v,exp_to_typ e) } in
      let acc_typ = { Types.t = Types.Tfn(num_type, acc_typ1) } in
      let (f_id, _) = get_const_id env l_unk "vector_access" [(exp_to_typ e); {Types.t = Types.Tne(i.nt)}; vlength ] in
      let f = C.mk_const l_unk f_id (Some acc_typ) in
      let app1 = C.mk_app l_unk f (nexp_to_exp i.nt) (Some acc_typ1) in
      Some(C.mk_app l_unk app1 v (Some (exp_to_typ e)))
    | _ -> None

(*Replace vector sub with an appropriate external library call, ocaml specific at the moment*)
let remove_vector_sub _ e =
  let l_unk = Ast.Trans(true, "remove_vector_sub", Some (exp_to_locn e)) in
  match C.exp_to_term e with
    | VectorSub(v, sk1, i1, sk2, i2, sk3) -> 
      let (vlength1,a) = match (exp_to_typ v).Types.t with | Types.Tapp([n;a],_) -> (n,a) | _ -> assert false in
      let vlength2 = match (exp_to_typ e).Types.t with | Types.Tapp([n;a],_) -> n | _ -> assert false in
      let num_type = nat_ty in
      let acc_typ1 = { Types.t = Types.Tfn(exp_to_typ v,exp_to_typ e) } in
      let acc_typ2 = { Types.t = Types.Tfn(num_type, acc_typ1) } in
      let acc_typ3 = { Types.t = Types.Tfn(num_type, acc_typ2) } in
      let (f_id, _) = get_const_id env l_unk "vector_slice" [a; { Types.t = Types.Tne(i1.nt)}; {Types.t = Types.Tne(i2.nt)}; vlength1; vlength2] in 
      let f = C.mk_const l_unk f_id (Some acc_typ3) in
      let app1 = C.mk_app l_unk f (nexp_to_exp i1.nt) (Some acc_typ2) in
      let app2 = C.mk_app l_unk app1 (nexp_to_exp i2.nt) (Some acc_typ1) in
      Some(C.mk_app l_unk app2 v (Some (exp_to_typ e)))
    | _ -> None


(* Add type annotations to pattern variables whose type contains a type variable
 * (only add for arguments to top-level functions) *)
let rec coq_type_annot_pat_vars (level,pos) _ p = 
  let l_unk = Ast.Trans(true, "coq_type_annot_pat_vars", Some p.locn) in
  match p.term with
    | P_var(n) when level = Macro_expander.Top_level && 
                    pos = Macro_expander.Param && 
                    not (Types.TNset.is_empty (Types.free_vars p.typ)) ->
        Some(C.mk_pvar_annot l_unk n (C.t_to_src_t p.typ) (Some(p.typ)))
    | _ -> None

let bind_id l = function
  | Id_none(sk) ->
      Id_some(Ident.mk_ident_strings [] "bind")
  | Id_some(id) ->
      let (n1,n2) = Ident.to_name_list id in
        Id_some (Ident.mk_ident None (n1 @ [n2]) (Name.from_rope (r "bind")))


let bind_const l (m : Path.t id) i =
  let (n1,n2) = Path.to_name_list m.descr in
  let (descr, _) = names_get_const E.env (n1@[n2]) (Name.from_rope (r"bind")) in
    C.mk_const l { id_path = bind_id l m.id_path; id_locn = l; descr = descr; instantiation = i } None

(* TODO: do something sensible with the spacing *)
let remove_do _ e =
  let l_unk = Ast.Trans(true, "remove_do", Some (exp_to_locn e)) in
    match C.exp_to_term e with
      | Do(sk1, m, [], sk2, e, sk3,t) ->
          Some e
      | Do(sk1, m, Do_line(p',sk1',e',sk2')::lns, sk2, exp, sk3, (t, direction)) ->
          let e1 = e' in
          let tyargs = match direction with
                         | BTO_input_output -> [p'.typ; t]
                         | BTO_output_input -> [t; p'.typ]
          in
          let e2 = bind_const l_unk m tyargs in
          let e3 = 
            C.mk_fun l_unk None [p'] sk1' (C.mk_do (exp_to_locn e) sk1 m lns sk2 exp sk3 (t, direction) (Some (exp_to_typ e))) 
              (Some { Types.t = Types.Tfn(p'.typ,exp_to_typ e)})
          in
            Some (C.mk_infix l_unk e1 e2 e3 (Some (exp_to_typ e)))
      | _ -> None

end

