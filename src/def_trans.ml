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
open Target
open Types
type def_macro = Name.t list -> env -> def -> (env * def list) option

let r = Ulib.Text.of_latin1
let space = Some [Ast.Ws (r" ")]
let new_line = Some [Ast.Ws (r"\n")]


let rec list_to_mac = function
  | [] -> (fun p e d -> None)
  | m1::ms ->
        (fun p e d ->
           match m1 p e d with
             | None -> let ms_f = list_to_mac ms in ms_f p e d
             | Some((e,d)) -> Some((e,d)))

let rec process_defs path (trans : def_macro) mod_name (env : env) defs = 
  let (sub_env : mod_descr) = 
    match Nfmap.apply env.local_env.m_env mod_name with
      | None -> assert false
      | Some(x) -> x
  in
  let rec p env defs =
    match defs with
      | [] -> (env,[])
      | def::defs ->
          begin
            match trans (mod_name::path) env def with
              | Some((env',def')) ->
                 p env' (def'@defs)
              | None -> ( 
                  let (env',def') = 
                    match def with
                      | ((Module(sk1,(n,l'),mod_bind,sk2,sk3,ds,sk4),s),l,lenv) ->
                          let (env',ds') = 
                            process_defs (mod_name::path) trans (Name.strip_lskip n) env ds 
                          in
                            (env',((Module(sk1,(n,l'),mod_bind,sk2,sk3,ds',sk4),s),l,lenv))
                      | _ -> (env,def)
                  in
                  let (env'', defs') = p env' defs in
                    (env'', def'::defs'))
          end
  in
  let (env',defs') = p {env with local_env = sub_env.mod_env} defs in
  let m_env' = Nfmap.insert env.local_env.m_env (mod_name, {sub_env with mod_env = env'.local_env}) in
  let local_env' = {env.local_env with m_env = m_env'} in
    ({ env' with local_env = local_env' },
     defs')



module C = Exps_in_context (struct let avoid = None let env_opt = None end)

let comment_def ((((d, s), l, lenv):def) as def) : def =
  ((Comment (def), s), Ast.Trans(false,"comment_def", Some l), lenv)

let remove_vals _ env (((d,_),_,_) as def) =
  match d with
    | Val_spec _ ->
        Some (env, [comment_def def])
    | _ -> None

let remove_indrelns _ env (((d,_),_,_) as def) =
  match d with
    | Indreln _ ->
        Some (env, [comment_def def])
    | _ -> None

let remove_opens _ env (((d,_),_,_) as def) =
  match d with
    | Open _ ->
        Some (env, [comment_def def])
    | _ -> None

let remove_classes _ env (((d,_),_,_) as def) =
  match d with
    | Class _ ->
        Some(env, [comment_def def])
    | _ -> None

let remove_indrelns_true_lhs _ env ((d,s),l,lenv) =
  let l_unk = Ast.Trans (true, "remove_indrelns_true_lhs", Some l) in
  match d with
    | Indreln (s', targ, names, sl) ->
        let remove_true (Rule (name_opt,s0, s1, qnames, s2, e_opt, s3, rname, c, es),l) =
            (match e_opt with None -> None | Some e -> (if Typed_ast_syntax.is_tf_exp true e then 
                Some (Rule(name_opt, s0,s1, qnames, s2, None, s3, rname, c, es),l) else None))
        in
        (match Seplist.map_changed remove_true sl with
             None -> None
           | Some sl' -> 
             let def = (((Indreln (s', targ, names, sl'), s), l_unk,lenv):def) in 
             Some(env, [def]))
    | _ -> None

(* For Coq, add return types to function definitions that have type variables *)
let generate_srt_t_opt src_opt e =
  match src_opt with 
    | Some _ -> None
    | None ->  
        if Types.TNset.is_empty (Types.free_vars (exp_to_typ e)) then
          None
        else
          Some (None,C.t_to_src_t (exp_to_typ e))
             
let type_annotate_definitions _ env ((d,s),l,lenv) =
  match d with
    | Val_def(Let_def(sk1,topt,(p, name_map, src_t_opt, sk2, e)),tnvs,class_constraints) -> begin
        match generate_srt_t_opt src_t_opt e with
          | None -> None
          | Some t -> Some (env,
               [((Val_def(Let_def(sk1, topt,(p, name_map, Some t, sk2, e)), tnvs, class_constraints), s), l, lenv)])
      end
    | Val_def(Fun_def(sk1,sk2,topt,funs),tnvs,class_constraints) -> begin
        let fix_funcl_aux (n, n_c, pL, src_t_opt, sk, e) = begin
          let src_t_opt' = generate_srt_t_opt src_t_opt e 
          in match src_t_opt' with 
            | None -> None 
            | _ -> Some (n, n_c, pL, src_t_opt', sk, e)
        end in
        let funs'_opt = Seplist.map_changed fix_funcl_aux funs in
        match funs'_opt with 
          | None -> None
          | Some funs' -> Some (env,
               [((Val_def(Fun_def(sk1,sk2,topt,funs'), tnvs, class_constraints), s), l, lenv)])
      end
    | _ -> None


(* Turn a class definition into a record one for dictionary passing.
   The type definition of the record and the definition of its fields has 
   already been done during type-checking. *)
let class_to_record mod_path env ((d,s),l,lenv) =
    let l_unk = Ast.Trans(true, "class_to_record", Some l) in 
    match d with
      | Class(sk1,sk2,(n,l),tnvar,class_path,sk3,specs,sk4) ->
          (* lookup class-description *)
          let cd = lookup_class_descr l_unk env class_path in

          (* turn the methods specs into pairs of sk + field spec *)
          let process_method_spec (sk1, (method_name, l), method_ref, sk2, src_t) =
          begin
            let field_ref = lookup_field_for_class_method l cd method_ref in
            let fd = c_env_lookup l env.c_env field_ref in
            let field_name = Name.add_pre_lskip sk1 (Name.add_lskip (Path.get_name fd.const_binding)) in
              
	    ((field_name, l), field_ref, sk2, src_t)
          end in   
          let fields = Seplist.from_list_default None (List.map process_method_spec specs) in
          let (sk_fields, fields) = Seplist.drop_first_sep fields in

          let rec_path = cd.class_record in
          let rec_name = Name.add_pre_lskip sk2 (Name.add_lskip (Path.get_name rec_path)) in
          let rec_def = 
            Type_def (sk1, 
                      Seplist.from_list_default None [((rec_name, l), [tnvar], rec_path, Te_record(None, sk3, fields, sk4), None)])
          in
            Some (env, [((rec_def, s), l, lenv)])
      | _ -> None


(* turns an instance declaration into a module containing all the field declarations
   and a dictionary at the end *)
let instance_to_module (global_env : env) mod_path (env : env) ((d,s),l,lenv) =
  let l_unk n = Ast.Trans(true, "instance_to_module" ^ string_of_int n , Some l) in
  match d with
      | Instance(sk1, (prefix, sk2, id, class_path, t, sk3), vdefs, sk4) ->
          (* lookup instance and class description *)
          let id_opt = get_matching_instance env.t_env (class_path, t.typ) env.i_env in 
          let id = match id_opt with
                     | Some (id, subst) -> id
                     | None -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal (l, "instance has not been added properly to the environment during typechecking.")))
          in      
          let cd = lookup_class_descr (l_unk 0) env id.inst_class in

          let (inst_path, inst_name) = Path.to_name_list id.inst_binding in

          (* now generate the definition of the record dict *)
          let dict = begin
            let mk_field_entry (class_method_ref, inst_method_ref) =
              begin
                let field_ref = lookup_field_for_class_method l cd class_method_ref in
                let field_id = { id_path = Id_none None;
                                 id_locn = l_unk 1;
                                 descr = field_ref;
                                 instantiation = [t.typ]; } in

                let inst_method_d = c_env_lookup l env.c_env inst_method_ref in
                let inst_method_id = { id_path = Id_none None;
                                       id_locn = l_unk 3;
                                       descr = inst_method_ref;
                                       instantiation = List.map Types.tnvar_to_type inst_method_d.const_tparams; } in
                let inst_method_const = C.mk_const (l_unk 2) inst_method_id (Some inst_method_d.const_type) in

                ((field_id, None, inst_method_const, (l_unk 4)),
                 None)
              end in
            let fields = List.map mk_field_entry id.inst_methods in
            let dict_type = class_descr_get_dict_type cd t.typ in
            let dict_d = c_env_lookup (l_unk 7) env.c_env id.inst_dict in
            let dict_body = C.mk_record (l_unk 5) None (Seplist.from_list fields) None (Some dict_type)
            in
            let dict_name =
              { term = Name.add_lskip (Path.get_name dict_d.const_binding);
                typ = dict_type;
                locn = l_unk 6;
                rest = ();
              }
            in
            let dict' = ((dict_name, id.inst_dict, [], None, None, dict_body):funcl_aux) in
            let dict = Fun_def(new_line,FR_non_rec,None,Seplist.cons_entry dict' Seplist.empty) in
            dict
          end in

          (* environment inside the module *)
          let lenv' = local_env_union lenv (lookup_mod_descr lenv [] inst_name).mod_env in

          (* finally, we get the module *)
          let tnvars_set = List.fold_right TNset.add id.inst_tyvars TNset.empty in
          let m = 
            Module(sk1, (Name.add_lskip inst_name, l_unk 9), 
                   id.inst_binding, sk2, None, 
                   List.map (fun d -> ((Val_def(d,tnvars_set,id.inst_constraints),None), l_unk 10, lenv')) 
                            (vdefs @ [dict]), 
                   sk4)
          in
            Some((env,[((m,s),l,lenv)]))
      | _ ->
          None

(* for dictionary passing turn class constriants into additional arguments *) 
let class_constraint_to_parameter : def_macro = fun mod_path env ((d,s),l,lenv) ->
  let l_unk = Ast.Trans(true, "class_constraint_to_parameter", Some l) in
  (* TODO : avoid shouldn't be None *)
    match d with
      | Val_def(_, tnvs, []) -> None
      | Val_def(lb,tnvs,class_constraints) ->
          let new_pats =
            List.map
              (fun (c,tnv) ->
                 let n = Typed_ast.class_path_to_dict_name c tnv in
                 let cd = lookup_class_descr l_unk env c in
                 let dict_type = class_descr_get_dict_type cd (Types.tnvar_to_type tnv) in
                   C.mk_pvar l_unk (Name.add_lskip n) dict_type) 
              class_constraints
          in
          let build_fun sk1 fr targs clauses =
            (* update the constant description *)
            let (clauses', c_env') = Seplist.map_acc_left (fun ((n, c, ps, topt, sk2, e):funcl_aux) c_env -> 
              begin
              let c_d = c_env_lookup l_unk c_env c  in
	      let (c', t', c_env') = 
                match c_d.const_no_class with
		  | Some c' -> 
                      let c_d' = c_env_lookup l_unk c_env c' in
                      (c', c_d'.const_type, c_env)
		  | None -> 
                    begin            
                      let t' = Types.multi_fun (List.map (fun x -> x.typ) new_pats) c_d.const_type in

                      let c_d' = ({ c_d with const_class = []; const_type = t' }) in
                      let (c_env', c') = c_env_store_raw c_env c_d' in 

                      let c_d_new = { c_d with const_no_class = Some c' } in
                      let c_env' = c_env_update c_env' c c_d_new in 

                      (c',t', c_env')
                   end
              in
              let n'' = { n with typ = t' } in
              let (clause':funcl_aux) = (n'',c',new_pats@ps,topt,sk2,e) in
              (clause', c_env') end)
            env.c_env clauses in

            Some({ env with c_env = c_env'},
                 [((Val_def(Fun_def(sk1,fr,targs,clauses'),tnvs,[]),s),l,lenv)])
          in
          begin
            match lb with
              | Let_def(_,_,_) -> 
                  raise (Reporting_basic.err_unreachable true l "Fancy, top level pattern maching should not have a class constraint. Typechecking should have complained.")

              | Fun_def(sk,fr,topt,clauses) -> build_fun sk fr topt clauses

              | Let_inline _ -> 
                  raise (Reporting_basic.err_unreachable true l "Inline functions should not have a class constraint. Typechecking should have complained.")

         end
      | _ -> None

let nvar_to_parameter : def_macro = fun mod_path env ((d,s),l,_) ->
  let l_unk = Ast.Trans(true, "nvar_to_parameter", Some l) in
    match d with
      | Val_def(lb, tnvs, class_constraints) ->
        if (Types.TNset.is_empty tnvs) then None
        else
        let (nvars, tvars) = Types.tnvar_split (Types.TNset.elements tnvs) in
        if ([] = nvars) then None
        else
        let new_pats = List.map (fun n -> C.mk_pvar l_unk (Name.add_lskip (Types.tnvar_to_name n))
                                                          { Types.t = Types.Tapp([],Path.numpath) })
                                nvars in

        let tnvs' = List.fold_left (fun s t -> Types.TNset.add t s) Types.TNset.empty tvars in

        let build_funcl_aux ((sk1, c, ps, topt, sk2, e):funcl_aux) : (env * funcl_aux) = 
        begin
            let c_d = c_env_lookup l_unk env.c_env c in 
            let t' = Types.multi_fun (List.map (fun x -> x.typ) new_pats) c_d.const_type in
            let c_new_d = ({ c_d with const_type = t' } ) in
            let env' = env_c_env_update env c c_new_d in
            (env', ((sk1,c,new_pats@ps,topt,sk2,e):funcl_aux))
        end in
            begin
              match lb with 
              | Let_def(_,_,_) -> None
              | Fun_def(sk1,_,topt,funs) ->
                  raise (Reporting_basic.err_todo true l "Recursive function with nvars")
              | Let_inline _ ->
                  assert false
            end
      | _ -> None


let get_name def l = match def with

  (*TODO : Check the name section, no just within the clauses*)
  | Indreln(_,_,_,clauses) -> (match Seplist.to_list clauses with 
    | [] ->  
        raise (Reporting_basic.err_todo false l "Error while pruning target definitions: empty Indreln clauses in get_name [debug]")
        
    | ((Rule(_,_,_,_,_,_,_,name,_,_),_)::cs) -> Name.strip_lskip name.term
    )
  
  | Val_def(Fun_def(_,_,_,clauses),ntvs,_) -> (match Seplist.to_list clauses with

    (* in a Rec_def, the constant names of all clauses should be the same, so we
     * check only the first TODO: check! *)
    
    | [] ->  
        raise (Reporting_basic.err_todo false l "Error while pruning target definitions: empty Rec_def clauses in get_name [debug]")

    | ((name,_,_,_,_,_)::cs) -> Name.strip_lskip name.term     
    )

  | Val_def(Let_def(_,_,(p,_,_,_,_)),tnvs,_) -> begin
      match Pattern_syntax.pat_to_ext_name p with
        | Some nls -> Name.strip_lskip nls.term 
        | None -> raise (Reporting_basic.err_todo false l "Error while pruning target definitions: unmatched Let_val case in get_name [debug]")
    end
  | Val_def(Let_inline(_,_,_,name,_,_,_,_), _,_) -> Name.strip_lskip name.term
  | _ -> 
    raise (Reporting_basic.err_todo false l "Error while pruning target definitions: unmatched top-level case in get_name [debug]")


let target_supports_lemma_type target lty =
  match (target, lty) with
    | (Target.Target_ocaml, Ast.Lemma_theorem _) -> false
    | (Target.Target_ocaml, Ast.Lemma_lemma _) -> false
    | (_, _) -> true

let prune_target_bindings target (defs : def list) : def list =

  (* given a list constant name and a list of definition, rem_dups removes all
   * duplicate definitions (i.e. with the same name) from the list *)
  let rec rem_dups name = function 
    | [] -> []
    | ((def,s),l, lenv)::defs -> 
        (match def with 
      | (Val_def _ | Indreln _) -> 
          if (Name.compare name (get_name def l) = 0) then
            rem_dups name defs
          else 
            ((def,s),l,lenv) :: rem_dups name defs
      | d -> ((d,s),l,lenv) :: rem_dups name defs
    )
  in

  (* def_walker walks over a list of definitions, checks for each def if it is a 
   * target specific one, in which case it invokes rem_dups with both, the
   * already checked defs and the remaining defs *)
  let rec def_walker (target : Target.non_ident_target) acc =  function
    | [] -> List.rev acc

    | ((def,s),l,lenv)::defs -> begin
      match def with
        | (Val_def(Let_def(_,topt,_),_,_) |
          Val_def(Fun_def(_,_,topt,_),_,_) |
          Indreln(_,topt,_,_) ) as d -> 
          if Typed_ast.in_targets_opt (Target_no_ident target) topt then 
              let name = get_name d l in
              let acc' = rem_dups name acc in  
              let defs' = rem_dups name defs in
            def_walker target (((def,s),l,lenv) :: acc') defs' 
          else
            def_walker target acc defs
      
       | Lemma(_,lty,targets,_,_,_,_) as d ->
         let targ_OK = Typed_ast.in_targets_opt (Target_no_ident target) targets in
         if (target_supports_lemma_type target lty && targ_OK) then
            def_walker target (((d,s),l,lenv) :: acc) defs
         else
            def_walker target acc defs
       | d -> def_walker target (((d,s),l,lenv) :: acc) defs
     end

  in def_walker target [] defs


