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

module Make(C : sig include Types.Global_defs end) = 
struct

  open Typed_ast

  module T = Trans.Macros(struct let d = C.d let i = C.i end)
  module M = Def_trans.Macros

  type which_macro =
    | Def_macros of (env -> Def_trans.def_macro list)
    | Exp_macros of (env -> (exp -> exp option) list)
    | Pat_macros of (env -> (Macro_expander.pat_position -> pat -> pat option) list)

  type trans =
      { 
        (* Which macdos to run, in the given order so that updates to the
         * environment by definition macros can be properly accounted for. *)
        macros : which_macro list;

        (* A description of operator precedences *)
        get_prec : Precedence.op -> Precedence.t; 

        (* Perform the extra translations after the above, left-to-right *)
        extra : (Name.t -> env -> def list -> def list) list
      }

  (* The macros needed to implement the dictionary passing translations to remove type classes *)
  let dictionary_macros = 
    [
     Def_macros (fun env -> let module M = M(struct let env = env end) in [M.class_to_module]);
     Def_macros (fun env -> let module M = M(struct let env = env end) in [M.instance_to_module env]);
     Def_macros (fun env -> let module M = M(struct let env = env end) in [M.class_constraint_to_parameter]);
     Exp_macros (fun env -> let module T = T(struct let env = env end) in [T.remove_method]);
     Exp_macros (fun env -> let module T = T(struct let env = env end) in [T.remove_class_const])
    ]

  (* The macros needed to change number type variables (e.g., ''a) into function parameters *)
  let nvar_macros =
    [(* TODO add again: Def_macros (fun _ -> [Def_trans.nvar_to_parameter]); *)
     Exp_macros (fun env -> let module T = T(struct let env = env end) in [T.add_nexp_param_in_const])
    ]

  let ident =
    { (* for debugging pattern compilation *)
      macros = [ Def_macros (fun env -> if !ident_force_pattern_compile then [Patterns.compile_def None (Patterns.is_pattern_match_const false) env] else []);
                 Exp_macros (fun env -> if !ident_force_pattern_compile then [Patterns.compile_exp None (Patterns.is_pattern_match_const false) C.d env] else []) ];
      get_prec = Precedence.get_prec; 
      extra = []; }

  let tex =
    { macros = [];
      get_prec = Precedence.get_prec;
      extra = []; }

  let hol consts fixed_renames =
    { macros = dictionary_macros @ 
               nvar_macros @
               [Def_macros (fun env -> let module M = M(struct let env = env end) in [
                                          M.remove_vals;
                                          M.remove_classes; 
                                          M.remove_opens;
                                          Patterns.compile_def (Some Target_hol) Patterns.is_hol_pattern_match env;
                                          (*M.flatten_modules*)]);
                Exp_macros (fun env ->
                              let module T = T(struct let env = env end) in
                                [T.remove_list_comprehension;
                                 T.list_quant_to_set_quant;
				 T.remove_setcomp;
                                 T.remove_set_restr_quant;
                                 T.remove_restr_quant Pattern_syntax.is_var_tup_pat;
                                 (* TODO: T.do_substitutions Target_hol; *)
                                 Patterns.compile_exp (Some Target_hol) Patterns.is_hol_pattern_match C.d env]);
                Pat_macros (fun env ->
                              let module T = T(struct let env = env end) in
                                [(*TODO: T.peanoize_num_pats_hol *)])
               ];
      get_prec = Precedence.get_prec_hol;
      extra = [(* TODO: (fun n -> 
                Rename_top_level.rename_nested_module [n]); 
               (fun n -> Rename_top_level.rename_defs_target (Some Target_hol) consts fixed_renames [n]);
               Rename_top_level.flatten_modules*)]; }

  let ocaml consts fixed_renames =
    { macros = dictionary_macros @
               nvar_macros @
               [Def_macros (fun env -> let module M = M(struct let env = env end) in 
                              [M.remove_vals; 
                               M.remove_indrelns;
                               Patterns.compile_def (Some Target_ocaml) Patterns.is_ocaml_pattern_match env]);
                Exp_macros (fun env ->
                              let module T = T(struct let env = env end) in
                                [(* TODO: figure out what it does and perhaps add it again    T.hack; *)
                                 (* TODO: add again or implement otherwise                    T.tup_ctor (fun e -> e) Seplist.empty; *)
                                 (* TODO: add again                                           T.do_substitutions Target_ocaml; *)
                                 T.remove_sets;
                                 T.remove_list_comprehension;
                                 T.remove_quant;
                                 T.remove_vector_access;
                                 T.remove_vector_sub;
                                 T.remove_do;
                                 Patterns.compile_exp (Some Target_ocaml) Patterns.is_ocaml_pattern_match C.d env])
               ];
      get_prec = Precedence.get_prec_ocaml;
      extra = [(*TODO: add again   (fun n -> Rename_top_level.rename_defs_target (Some Target_ocaml) consts fixed_renames [n]) *)]; 
    }

  let isa consts fixed_renames =
    { macros =
       [Def_macros (fun env -> let module M = M(struct let env = env end) in 
                      [M.remove_vals;
                       M.remove_opens;
                       M.remove_indrelns_true_lhs;
                       Patterns.compile_def (Some Target_isa) Patterns.is_isabelle_pattern_match env;
                       (*Def_trans.flatten_modules*)] );
        Exp_macros (fun env ->
                      let module T = T(struct let env = env end) in
                        [T.list_quant_to_set_quant;
                         T.remove_list_comprehension;
                         T.cleanup_set_quant;
                         T.remove_set_comprehension_image_filter true;
                         T.remove_set_restr_quant;
                         T.remove_restr_quant Pattern_syntax.is_var_wild_tup_pat;
                         T.remove_set_comp_binding;
                         (* TODO: add again T.do_substitutions Target_isa;*)
                         (* TODO: add again T.sort_record_fields;  *)
                         T.string_lits_isa;
                         Patterns.compile_exp (Some Target_isa) Patterns.is_isabelle_pattern_match C.d env]);
        Pat_macros (fun env ->
                      let module T = T(struct let env = env end) in
                        [(* TODO: add again    T.peanoize_num_pats_isa; *) T.remove_unit_pats])
       ];
      get_prec = Precedence.get_prec_isa;
      extra = [(* TODO: add again (fun n -> Rename_top_level.rename_nested_module [n]);
               Rename_top_level.flatten_modules; 
               (fun n -> Rename_top_level.rename_defs_target (Some Target_isa) consts fixed_renames [n]) *)];
    }

  let coq consts fixed_renames =
    { macros =
        [Def_macros (fun env -> let module M = M(struct let env = env end) in 
                      [M.type_annotate_definitions;
                       M.push_patterns_in_function_definitions_in;
                       Patterns.compile_def (Some Target_coq) Patterns.is_coq_pattern_match env
                      ]); 
         Exp_macros (fun env -> 
                       let module T = T(struct let env = env end) in
                         [(* TODO: add again T.remove_singleton_record_updates;
                          T.remove_multiple_record_updates;*)
                          T.remove_list_comprehension;
                          T.remove_set_comprehension;
                          T.remove_quant;
                          (* TODO: add again      T.do_substitutions Target_coq; *)
                          Patterns.compile_exp (Some Target_coq) Patterns.is_coq_pattern_match C.d env]);
         Pat_macros (fun env ->
                       let module T = T(struct let env = env end) in
                         [T.coq_type_annot_pat_vars])
        ];
      (* TODO: coq_get_prec *)
      get_prec = Precedence.get_prec;
      extra = [(* TODO: add again  (fun n -> Rename_top_level.rename_defs_target (Some Target_coq) consts fixed_renames [n]) *)]; 
      }

  let nameset_union_map s m =
    Nfmap.fold (fun s k _ -> NameSet.add k s) s m

  let extend_consts_consts targ consts modules = 
      let (new_consts, new_types) = Typed_ast.get_new_constants_types targ modules in
      nameset_union_map consts new_consts


  let extend_consts_full targ consts modules = 
      let (new_consts, new_types) = Typed_ast.get_new_constants_types targ modules in
      nameset_union_map (nameset_union_map consts new_types) new_consts

  let extend_consts targ consts =
    match targ with
      | Some(Target_isa) -> extend_consts_full targ consts
      | _ -> fun _ -> consts

  let default_avoid_f ty_avoid (cL : (Name.t -> Name.t option) list) consts = 
    let is_good n = not (NameSet.mem n consts) && List.for_all (fun c -> c n = None) cL
    in
      (ty_avoid, is_good, 
       (fun n check -> 
          let old_n : Name.t = Name.from_rope n in
          let new_n_opt : Name.t option = Util.option_first (fun c -> c old_n) cL in
          let n' = Util.option_default n (Util.option_map Name.to_rope new_n_opt) in
          Name.fresh n' (fun n -> check n && is_good n)))

  let ocaml_avoid_f consts = 
    let upper_fun n = if Name.starts_with_upper_letter n then Some (Name.uncapitalize n) else None
    in default_avoid_f false [upper_fun] consts

  let underscore_avoid_f consts = 
    let us_fun n = if Name.starts_with_underscore n then Some (Name.remove_underscore n) else None
    in default_avoid_f false [us_fun] consts

  let get_avoid_f targ : (NameSet.t -> var_avoid_f) = 
    match targ with
      | Some(Target_ocaml) -> ocaml_avoid_f
      | Some(Target_isa) -> underscore_avoid_f
      | Some(Target_hol) -> underscore_avoid_f
      | Some(Target_coq) -> default_avoid_f true []
      | _ -> default_avoid_f false []

  let rename_def_params_aux targ consts =
    let module Ctxt = Exps_in_context(struct 
                                        let env_opt = None
                                        (* TODO *)
                                        let avoid = Some(get_avoid_f targ consts)
                                      end) 
    in
      fun ((d,lex_skips),l) ->
        let d = 
          match d with
            | Val_def(Rec_def(s1,s2,topt,clauses),tnvs,class_constraints) ->
                let clauses = 
                  Seplist.map
                    (fun (n,ps,topt,s,e) ->
                       let (ps,e) =
                         Ctxt.push_subst (Types.TNfmap.empty, Nfmap.empty) ps e
                       in
                         (n,ps,topt,s,e))
                    clauses
                in
                  Val_def(Rec_def(s1,s2,topt,clauses),tnvs,class_constraints)
            | Val_def(Let_def(s1,topt,(Let_fun(n,ps,t,s2,e),l)),tnvs,class_constraints) ->
                let (ps, e) = 
                  Ctxt.push_subst (Types.TNfmap.empty, Nfmap.empty) ps e
                in
                  Val_def(Let_def(s1,topt,(Let_fun(n,ps,t,s2,e),l)),tnvs,class_constraints)
            | Indreln(s1,topt,clauses) ->
                let clauses =
                  Seplist.map
                    (fun (name_opt,s1,ns,s2,e,s3,n,es) ->
                       (* TODO: rename to avoid conflicts *)
                       (name_opt,s1,ns,s2,e,s3,n,es))
                    clauses
                in
                  Indreln(s1,topt,clauses)      
            | d -> d
        in
          ((d,lex_skips),l)

  let rename_def_params targ consts =
      let rdp = rename_def_params_aux targ consts in
      List.map (fun (m:Typed_ast.checked_module) -> 
         {m with Typed_ast.typed_ast = (let (defs, end_lex_skips) = m.Typed_ast.typed_ast in (List.map rdp defs, end_lex_skips))})

  let trans targ ttarg params env m =
    let module Ctxt = struct let avoid = None let env_opt = Some(env) end in
    let module M = Macro_expander.Expander(Ctxt) in
    let (defs, end_lex_skips) = m.typed_ast in
    let module_name = Name.from_rope (Ulib.Text.of_latin1 m.module_name) in
    (* TODO: Move this to a definition macro, and remove the targ argument *)
    let defs =
      match targ with 
        | None -> defs 
        | Some(targ) -> let module M2 = Def_trans.Macros(struct let env = env end) in M2.prune_target_bindings targ defs 
    in
    let (env,defs) = 
      List.fold_left 
        (fun (env,defs) mac ->
           match mac with
             | Def_macros dtrans ->
                 Def_trans.process_defs 
                   []
                   (Def_trans.list_to_mac (dtrans env))
                   module_name
                   env
                   defs
             | Exp_macros etrans ->
                 let defs =
                   M.expand_defs defs
                     (Macro_expander.list_to_mac (etrans env),
                      (fun ty -> ty),
                      (fun ty -> ty),
                      Macro_expander.list_to_bool_mac [])
                 in
                   (env,defs)
             | Pat_macros ptrans ->
                 let defs =
                   M.expand_defs defs
                     (Macro_expander.list_to_mac [],
                      (fun ty -> ty),
                      (fun ty -> ty),
                      Macro_expander.list_to_bool_mac (ptrans env))
                 in
                   (env,defs))
        (env,List.rev defs)
        params.macros
    in
    let defs =
      List.fold_left
        (fun defs e -> e (Name.from_rope (Ulib.Text.of_latin1 m.module_name)) env defs)
        defs
        params.extra
    in
    let defs = 
      match ttarg with
        | None -> defs
        | Some(ttarg) ->
            Target_binding.fix_binding (target_to_mname ttarg) defs 
    in
    let defs = Target_syntax.fix_infix_and_parens env params.get_prec defs in
      (* Note: this is the environment from the macro translations, ignoring the
       * extra translations *)
      (env,
       { m with typed_ast = (List.rev defs, end_lex_skips) })

  let get_fixed_renames targ : (Typed_ast.name_kind * Path.t * Path.t) list =
    let r = Ulib.Text.of_latin1 in
    let mk_string_path ns n = Path.mk_path (List.map (fun s -> Name.from_rope (r s)) ns) (Name.from_rope (r n)) in
    match targ with
      | Some(Target_isa) -> [
           (Typed_ast.Nk_typeconstr, 
            Path.numpath,
            mk_string_path [] "nat");

           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Hol"; "Integer"] "int",
            mk_string_path [] "int");

           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Coq"; "Hol"; "Integer"] "int",
            mk_string_path [] "int");

           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Int"] "int",
            mk_string_path [] "int");

           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Isabelle"; "Pervasives"] "int",
            mk_string_path [] "int");

           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Pmap"] "map",
            mk_string_path ["Map"] "map");
           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Coq"; "Hol"; "Finite_map"] "fmap",
            mk_string_path ["Map"] "map");
           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Hol"; "Finite_map"] "fmap",
            mk_string_path ["Map"] "map");
           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Coq"; "Map"] "fmap",
            mk_string_path ["Map"] "fmap");
          ]
      | Some(Target_hol) -> [
           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Pmap"] "map",
            mk_string_path [] "fmap");
           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Coq"; "Hol"; "Finite_map"] "fmap",
            mk_string_path [] "fmap");
           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Hol"; "Finite_map"] "fmap",
            mk_string_path [] "fmap");
           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Coq"; "Hol"] "fmap",
            mk_string_path [] "fmap");
          ]
      | Some(Target_coq) -> [
           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Pmap"] "map",
            mk_string_path [] "fmap");
           (Typed_ast.Nk_typeconstr, 
            mk_string_path ["Coq"; "Hol"; "Integer"] "int",
            mk_string_path [] "int");
        ]
      | _ -> []

  let get_transformation targ consts =
    let fixed_renames = get_fixed_renames targ in
    match targ with
      | Some(Target_hol) -> 
          (trans (Some(Ast.Target_hol(None))) targ (hol consts fixed_renames),
           get_avoid_f targ)
      | Some(Target_ocaml) -> 
          (* TODO *)
          (trans (Some(Ast.Target_ocaml(None))) targ (ocaml consts fixed_renames),
           get_avoid_f targ)
      | Some(Target_coq) -> 
          (trans (Some(Ast.Target_coq(None))) targ (coq consts fixed_renames),
           get_avoid_f targ)
      | Some(Target_isa) -> 
          (trans (Some(Ast.Target_isa(None))) targ (isa consts fixed_renames),
           get_avoid_f targ)
      | Some(Target_tex) -> 
          (trans (Some(Ast.Target_tex(None))) targ tex,
           get_avoid_f targ)
      | Some(Target_html) -> 
          (trans None targ ident,
           get_avoid_f targ)
      | None -> 
          (trans None targ ident,
           get_avoid_f targ)

end
