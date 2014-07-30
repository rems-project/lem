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

let ident_force_pattern_compile = ref false
let ident_force_dictionary_passing = ref false
let hol_remove_matches = ref false
let prover_remove_failwith = ref false

open Typed_ast
open Typed_ast_syntax
open Target

module T = Trans.Macros
module M = Def_trans

type which_macro =
  | Def_macros of (env -> Def_trans.def_macro list)
  | Exp_macros of (env -> (Macro_expander.macro_context -> exp -> exp option) list)
  | Pat_macros of (env -> (Macro_expander.pat_position -> Macro_expander.macro_context -> pat -> pat option) list)

type trans =
    { 
      (* Which macros to run, in the given order so that updates to the
       * environment by definition macros can be properly accounted for. *)
      macros : which_macro list;

      (* Perform the extra translations after the above, left-to-right *)
      extra : (Path.t -> env -> def list -> def list) list
    }

(* The macros needed to implement the dictionary passing translations to remove type classes *)
let dictionary_macros targ = 
  [
   Def_macros (fun env -> [M.class_to_record targ]);
   Def_macros (fun env -> [M.instance_to_dict false targ]);
   Def_macros (fun env -> [M.class_constraint_to_parameter targ]);  
   Exp_macros (fun env -> let module T = T(struct let env = env end) in [T.remove_method targ true]);
   Pat_macros (fun env -> let module T = T(struct let env = env end) in [T.remove_method_pat]);
   Exp_macros (fun env -> let module T = T(struct let env = env end) in [T.remove_class_const targ])
  ]

let coq_typeclass_resolution_macros targ =
  [
    Exp_macros (fun env -> let module T = T(struct let env = env end) in [T.remove_method targ false]);
    Pat_macros (fun env -> let module T = T(struct let env = env end) in [T.remove_method_pat])
  ]

(* The macros needed to change number type variables (e.g., ''a) into function parameters *)
let nvar_macros =
  [Def_macros (fun env -> [M.nvar_to_parameter]);
   Exp_macros (fun env -> let module T = T(struct let env = env end) in [T.add_nexp_param_in_const])
  ]

let indreln_macros = 
  [
    Def_macros (fun env ->   
      let module Ctxt = struct let avoid = None let env_opt = Some(env) end in
      let module Conv = Convert_relations.Converter(Ctxt) in
      [ Conv.gen_witness_type_macro env;
        Conv.gen_witness_check_macro env;
        Conv.gen_fns_macro env;]); 
  ]

let ident () =
  { (* for debugging pattern compilation *)
    macros = (if !ident_force_dictionary_passing then dictionary_macros Target_ident else []) @ [ Def_macros (fun env -> if !ident_force_pattern_compile then [Patterns.compile_def Target_ident (Patterns.is_pattern_match_const false) env] else []);
               Exp_macros (fun env -> if !ident_force_pattern_compile then [(Patterns.compile_exp Target_ident (Patterns.is_pattern_match_const false) env)] else [])];
    extra = []; }

let lem () = 
  { macros = [Exp_macros (fun env -> [Backend_common.inline_exp_macro Target_lem env]);
              Pat_macros (fun env -> [Backend_common.inline_pat_macro Target_lem env])];
    extra = []; }


let tex =
  { macros = [];
    extra = []; }

let hol =
  { macros = indreln_macros @
             dictionary_macros (Target_no_ident Target_hol) @ 
             nvar_macros @
             [Def_macros (fun env -> ([  M.remove_vals;
                                        M.remove_classes; 
                                        M.remove_opens;
					M.remove_module_renames;
                                        M.remove_types_with_target_rep (Target_no_ident Target_hol);
                                        M.defs_with_target_rep_to_lemma env (Target_no_ident Target_hol);
                                        Patterns.compile_def (Target_no_ident Target_hol) Patterns.is_hol_pattern_match env] @
                                        (if (!hol_remove_matches) then 
                                          [Patterns.remove_toplevel_match (Target_no_ident Target_hol) Patterns.is_hol_pattern_match env]
                                        else [])));
              Pat_macros (fun env -> [Backend_common.inline_pat_macro Target_hol env]);
              Exp_macros (fun env ->
                            let module T = T(struct let env = env end) in
                              (if !prover_remove_failwith then
                                [T.remove_failwith_matches]
                               else
                                []) @
                              [T.remove_list_comprehension;
                               T.list_quant_to_set_quant;
                    	       T.remove_setcomp;
                               T.remove_num_lit;
                               T.remove_set_restr_quant;
                               T.remove_restr_quant Pattern_syntax.is_var_tup_pat;
                               Backend_common.inline_exp_macro Target_hol env;
                               Patterns.compile_exp (Target_no_ident Target_hol) Patterns.is_hol_pattern_match env]);
              Pat_macros (fun env ->
                            let module T = T(struct let env = env end) in
                              [])
             ];
    extra = [(* (fun n -> Rename_top_level.rename_nested_module [n]);  
             (fun n -> Rename_top_level.rename_defs_target (Some Target_hol) consts fixed_renames [n]);*)
             Rename_top_level.flatten_modules]; }



let ocaml =
  { macros = indreln_macros @ 
             dictionary_macros (Target_no_ident Target_ocaml) @
             nvar_macros @
             [Def_macros (fun env ->  
                            [M.remove_vals; 
                             M.remove_import;
                             M.remove_indrelns;
                             M.remove_types_with_target_rep (Target_no_ident Target_ocaml);
                             M.defs_with_target_rep_to_lemma env (Target_no_ident Target_ocaml);
                             Patterns.compile_def (Target_no_ident Target_ocaml) Patterns.is_ocaml_pattern_match env]);
              Pat_macros (fun env -> [Backend_common.inline_pat_macro Target_ocaml env]);
              Exp_macros (fun env ->
                            let module T = T(struct let env = env end) in
                              [(* TODO: figure out what it does and perhaps add it again    T.hack; *)
                               (* TODO: add again or implement otherwise                    T.tup_ctor (fun e -> e) Seplist.empty; *)
                               Backend_common.inline_exp_macro Target_ocaml env;
                               T.remove_sets;
                               T.remove_num_lit;
                               T.remove_list_comprehension;
                               T.remove_quant;
                               T.remove_vector_access;
                               T.remove_vector_sub;
                               T.remove_do;
                               Patterns.compile_exp (Target_no_ident Target_ocaml) Patterns.is_ocaml_pattern_match env])
             ];
    extra = [(* (fun n -> Rename_top_level.rename_defs_target (Some Target_ocaml) consts fixed_renames [n]) *)]; 
  }

let isa  =
  { macros =
     indreln_macros @
     dictionary_macros (Target_no_ident Target_isa) @
     [Exp_macros (fun env ->
        let module T = T(struct let env = env end) in
          if !prover_remove_failwith then
            [T.remove_failwith_matches]
          else
            []);
      Def_macros (fun env ->
                    [M.remove_vals;
                     M.remove_opens;
                     M.remove_indrelns_true_lhs;
                     M.remove_types_with_target_rep (Target_no_ident Target_isa);
                     M.defs_with_target_rep_to_lemma env (Target_no_ident Target_isa);
                     Patterns.compile_def (Target_no_ident Target_isa) Patterns.is_isabelle_pattern_match env;
                     Patterns.remove_toplevel_match (Target_no_ident Target_isa) Patterns.is_isabelle_pattern_match env;] );
      Pat_macros (fun env -> [Backend_common.inline_pat_macro Target_isa env]);
      Exp_macros (fun env ->
                    let module T = T(struct let env = env end) in
                      [T.list_quant_to_set_quant;
                       T.remove_list_comprehension;
                       T.cleanup_set_quant;
                       T.remove_set_comprehension_image_filter true;
                       T.remove_num_lit;
                       T.remove_set_restr_quant;
                       T.remove_restr_quant Pattern_syntax.is_var_wild_tup_pat;
                       T.remove_set_comp_binding;
                       Backend_common.inline_exp_macro Target_isa env;
                       T.sort_record_fields;
                       Patterns.compile_exp (Target_no_ident Target_isa) Patterns.is_isabelle_pattern_match env]);
      Pat_macros (fun env ->
                    let module T = T(struct let env = env end) in
                      [T.remove_unit_pats])
     ];
    extra = [Rename_top_level.flatten_modules; 
             (* (fun n -> Rename_top_level.rename_nested_module [n]);             
             (fun n -> Rename_top_level.rename_defs_target (Some Target_isa) consts fixed_renames [n])*)];
  }

let coq =
  { macros = indreln_macros @
      coq_typeclass_resolution_macros (Target_no_ident Target_coq) @
      [Def_macros (fun env -> 
                    [M.type_annotate_definitions;
                     M.comment_out_inline_instances_and_classes (Target_no_ident Target_coq);
                     M.remove_import_include;
                     M.remove_types_with_target_rep (Target_no_ident Target_coq);
                     M.defs_with_target_rep_to_lemma env (Target_no_ident Target_coq);
                     Patterns.compile_def (Target_no_ident Target_coq) Patterns.is_coq_pattern_match env
                    ]); 
       Pat_macros (fun env -> [Backend_common.inline_pat_macro Target_coq env]);
       Exp_macros (fun env -> 
                     let module T = T(struct let env = env end) in
                      (if !prover_remove_failwith then
                       [T.remove_failwith_matches]
                      else
                       []) @
                       [T.remove_singleton_record_updates;
                        T.remove_multiple_record_updates;
                        T.remove_list_comprehension;
                        T.remove_num_lit;
                        T.remove_set_comprehension;
                        T.remove_quant_coq;
                        Backend_common.inline_exp_macro Target_coq env;
                        T.remove_do;
                        Patterns.compile_exp (Target_no_ident Target_coq) Patterns.is_coq_pattern_match env]);
       Pat_macros (fun env ->
                     let module T = T(struct let env = env end) in
                       [T.coq_type_annot_pat_vars])
      ];
    (* TODO: coq_get_prec *)
    extra = [(* fun n -> Rename_top_level.rename_defs_target (Some Target_coq) consts fixed_renames [n]) *)]; 
    }

let default_avoid_f ty_avoid (cL : (Name.t -> Name.t option) list) consts = 
  let is_good n = not (NameSet.mem n consts) && List.for_all (fun c -> c n = None) cL in
    (ty_avoid, is_good, 
     (fun n check -> 
        let old_n : Name.t = Name.from_rope n in
        let apply_fun (n : Name.t) = Util.option_first (fun c -> c n) cL in
        let new_n : Name.t = Util.option_repeat apply_fun old_n in
        let n' = Name.to_rope new_n in
        Name.fresh n' (fun n -> check n && is_good n)))

let ocaml_avoid_f consts = default_avoid_f false [Name.uncapitalize] consts

let underscore_avoid_f consts = 
  default_avoid_f false [Name.remove_underscore] consts

let underscore_both_avoid_f consts = 
  default_avoid_f false [Name.remove_underscore; Name.remove_underscore_suffix] consts



let add_used_entities_to_avoid_names env targ ue ns =
begin
  let l = Ast.Trans (false, "add_used_entities_to_avoid_names", None) in

  let avoid_consts =  match targ with
                        | Target_ident -> false
                        | Target_no_ident Target_lem -> false
                        | Target_no_ident Target_hol -> false 
                        | _ -> true
  in
  let avoid_types = match targ with
                      | Target_ident -> false
                      | Target_no_ident Target_lem -> false
                      | Target_no_ident Target_isa -> false
                      | Target_no_ident Target_hol -> false
                      | _ -> true in
  let avoid_modules = false in

  let add_avoid_const ns r = begin
    let c_d = c_env_lookup l env.c_env r in
    let (n_is_shown, n, n_ascii_opt) = constant_descr_to_name targ c_d in
    if n_is_shown then 
      NameSet.add n (Util.option_default_map n_ascii_opt ns (fun n_ascii -> NameSet.add n_ascii ns))
    else ns
  end in
  let ns = if not avoid_consts then ns else List.fold_left add_avoid_const ns ue.used_consts in

  let add_avoid_type ns t = begin
    let td = Types.type_defs_lookup l env.t_env t in
    let n = type_descr_to_name targ t td in
    NameSet.add n ns 
  end in
  let ns = if not avoid_types then ns else List.fold_left add_avoid_type ns ue.used_types in
  
  (* TODO: add avoid modules *)
  let ns = if not avoid_modules then ns else ns in
  ns
end

let get_avoid_f targ : NameSet.t -> var_avoid_f = 
  match targ with
    | Target_no_ident Target_ocaml -> ocaml_avoid_f 
    | Target_no_ident Target_isa -> underscore_both_avoid_f
    | Target_no_ident Target_hol -> underscore_avoid_f 
    | Target_no_ident Target_coq -> default_avoid_f true [] 
    | _ -> default_avoid_f false [] 

let rename_def_params_aux targ consts =
  let module Ctxt = Exps_in_context(struct 
                                      let env_opt = None
                                      (* TODO *)
                                      let avoid = Some(get_avoid_f targ consts)
                                    end) 
  in
    fun ((d,lex_skips),l,lenv) ->
      let d = 
        match d with
          | Val_def(Fun_def(s1,s2_opt,topt,clauses)) ->
              let clauses = 
                Seplist.map
                  (fun (n,c,ps,topt,s,e) ->
                     let (ps,e) =
                       Ctxt.push_subst (Types.TNfmap.empty, Nfmap.empty) ps e
                     in
                       (n,c,ps,topt,s,e))
                  clauses
              in
                Val_def(Fun_def(s1,s2_opt,topt,clauses))
          | Indreln(s1,topt,names,clauses) ->
              let clauses =
                Seplist.map
                  (fun (Rule(name,s0,s1,ns,s2,e,s3,n,c,es),l) ->
                  	let (_, name_avoid, _) = get_avoid_f targ consts in
                  	let ns = List.map (fun n ->
                  		match n with
                  	    | QName name_lskips_annot ->
                  	    		let new_name = Name.lskip_rename (fun t -> Name.to_rope (Name.fresh t name_avoid)) name_lskips_annot.Types.term in
                  	    		let subst = Nfmap.insert Nfmap.empty (Name.strip_lskip name_lskips_annot.Types.term, Sub_rename (Name.strip_lskip new_name)) in
                  	    		let name_lskips_annot = { name_lskips_annot with Types.term = new_name } in
                  	    			QName name_lskips_annot, subst
                        | Name_typ (skips, name_lskips_annot, skips', src_t, skips'') ->
                        	  let new_name = Name.lskip_rename (fun t -> Name.to_rope (Name.fresh t name_avoid)) name_lskips_annot.Types.term in
                  	    		let subst = Nfmap.insert Nfmap.empty (Name.strip_lskip name_lskips_annot.Types.term, Sub_rename (Name.strip_lskip new_name)) in
                  	    		let name_lskips_annot = { name_lskips_annot with Types.term = new_name } in
                        		Name_typ (skips, name_lskips_annot, skips', src_t, skips''), subst
                  	) ns in
                  	let substs = Nfmap.big_union (List.map snd ns) in
                  	let e   =
                  		match e with
                  			| None   -> None
                  			| Some e ->
                  			    Some (Ctxt.exp_subst (Types.TNfmap.empty, substs) e)
                    in
                  	let es  = List.map (Ctxt.exp_subst (Types.TNfmap.empty, substs)) es in
                  	let ns  = List.map fst ns in
                     (* TODO: rename ns to avoid conflicts *)
                     (Rule(name,s0,s1,ns,s2,e,s3,n,c,es),l))
                  clauses
              in
                Indreln(s1,topt,names,clauses)      
          | d -> d
      in
        ((d,lex_skips),l,lenv)

let rename_def_params targ consts =
    let rdp = rename_def_params_aux targ consts in
    List.map (fun (m:Typed_ast.checked_module) ->
       {m with Typed_ast.typed_ast = (let (defs, end_lex_skips) = m.Typed_ast.typed_ast in (List.map rdp defs, end_lex_skips))})

let trans (targ : Target.target) params env (m : checked_module) =
  let (defs, end_lex_skips) = m.typed_ast in

  (* TODO: Macros are only applied in the order they are given. Fix this! As a workaround, just apply all
           macros several times. *)

  let (module_path, module_name) = Path.to_name_list m.module_path in
  let rev_module_path = List.rev module_path in

  (* TODO: Move this to a definition macro, and remove the targ argument *)
  let defs = if (Target.is_human_target targ) then defs else
    match targ with 
      | Target_ident -> defs
      | Target_no_ident t -> Def_trans.prune_target_bindings t defs 
  in

  let rec achieve_fixpoint env defs =
    let (env',defs') = 
      List.fold_left 
        (fun (env,defs) mac ->
           match mac with
             | Def_macros dtrans ->
                 Def_trans.process_defs 
                   rev_module_path
                   (Def_trans.list_to_mac (dtrans env))
                   module_name
                   env
                   defs
             | Exp_macros etrans ->
                 let module Ctxt = struct let avoid = None let env_opt = Some(env) end in
                 let module M = Macro_expander.Expander(Ctxt) in
                 let defs =
                   M.expand_defs defs
                     (Macro_expander.list_to_mac (etrans env),
                      (fun ty -> ty),
                      (fun ty -> ty),
                      Macro_expander.list_to_bool_mac [])
                 in
                   (env,defs)
             | Pat_macros ptrans ->
                 let module Ctxt = struct let avoid = None let env_opt = Some(env) end in
                 let module M = Macro_expander.Expander(Ctxt) in
                 let defs =
                   M.expand_defs defs
                     (Macro_expander.list_to_mac [],
                      (fun ty -> ty),
                      (fun ty -> ty),
                      Macro_expander.list_to_bool_mac (ptrans env))
                 in
                   (env,defs))
        (env, defs) params.macros
    in
      if env' = env && defs = defs' then
        (env, defs)
      else
        achieve_fixpoint env' defs'
  in
  let (env, defs) = achieve_fixpoint env (List.rev defs) in
  let defs =
    List.fold_left
      (fun defs e -> e m.module_path env defs)
      defs
      params.extra
  in
  let defs = if (is_human_target targ) then defs else Target_syntax.fix_infix_and_parens env targ defs in 
    (* Note: this is the environment from the macro translations, ignoring the
     * extra translations *)
    (env,
     { m with typed_ast = (List.rev defs, end_lex_skips) })

let get_transformation targ =
  let tr = match targ with
    | Target_no_ident Target_hol   -> hol
    | Target_no_ident Target_ocaml -> ocaml
    | Target_no_ident Target_coq   -> coq
    | Target_no_ident Target_isa   -> isa
    | Target_no_ident Target_tex   -> tex
    | Target_no_ident Target_lem   -> lem ()
    | Target_no_ident Target_html  -> ident ()
    | Target_ident                 -> ident ()
  in
    trans targ tr


