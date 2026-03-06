(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*  Lean 4 backend                                                        *)
(*                                                                        *)
(**************************************************************************)

open Backend_common
open Output
open Typed_ast
open Typed_ast_syntax
open Target
open Types

let r = Ulib.Text.of_latin1

let print_and_fail l s =
  raise (Reporting_basic.err_general true l s)
;;

let wrap_lean_comment x = Ulib.Text.(^^^) (Ulib.Text.(^^^) (r"/- ") x) (r" -/")

let rec lean_comment_to_rope =
  function
    | Ast.Chars r -> r
    | Ast.Comment coms -> wrap_lean_comment (Ulib.Text.concat (r"") (List.map lean_comment_to_rope coms))

let lex_skip =
  function
    | Ast.Com r -> lean_comment_to_rope r
    | Ast.Ws r -> r
    | Ast.Nl -> r"\n"
;;

let delim_regexp = Str.regexp "^\\([][`;,(){}]\\|;;\\)$"
;;

let symbolic_regexp = Str.regexp "^[-!$%&*+./:<=>?@^|~]+$"
;;

let is_delim s = Str.string_match delim_regexp s 0
;;

let is_symbolic s = Str.string_match symbolic_regexp s 0
;;

let is_abbreviation l =
  let length = Seplist.length l in
  let abbreviation =
    match Seplist.hd l with
      | (_, _, _, Te_abbrev _, _) -> true
      | _ -> false
  in
    length = 1 && abbreviation
;;

let is_record l =
  let length = Seplist.length l in
  let record =
    match Seplist.hd l with
      | (_, _, _, Te_record _, _) -> true
      | _ -> false
  in
    length = 1 && record
;;

let need_space x y =
  let f x =
    match x with
      | Kwd'(s) ->
        if is_delim s then
          (true,false)
        else if is_symbolic s then
          (false,true)
        else
          (false,false)
      | Ident'(r) ->
        (false, is_symbolic @@ Ulib.Text.to_string r)
      | Num' _ ->
        (false,false)
  in
    let (d1,s1) = f x in
    let (d2,s2) = f y in
      not d1 && not d2 && s1 = s2
;;

let from_string x = meta x
let sep x s = ws s ^ x
let path_sep = r"."

let tyvar (_, tv, _) = id Type_var (Ulib.Text.(^^^) (r"") tv)
let concat_str s = concat (from_string s)

let lskips_t_to_output name =
  let stripped = Name.strip_lskip name in
  let rope = Name.to_rope stripped in
    Output.id Term_var rope
;;

let in_target targets = Typed_ast.in_targets_opt (Target.Target_no_ident Target.Target_lean) targets;;

let lean_infix_op a x =
  Output.flat [
    from_string "(fun x y => x "; id a x; from_string " y)"
  ]
;;

let lean_format_op use_infix a x =
  if use_infix then
    lean_infix_op a x
  else
    id a x

let none = Ident.mk_ident_strings [] "none";;
let some = Ident.mk_ident_strings [] "some";;

let fresh_name_counter = ref 0
;;

let generate_fresh_name = fun () ->
  let old  = !fresh_name_counter in
  let _    = fresh_name_counter := old + 1 in
  let post = string_of_int old in
    Stdlib.(^) "x" post
;;

type variable
  = Tyvar of Output.t
  | Nvar of Output.t
;;

module LeanBackendAux (A : sig val avoid : var_avoid_f option;; val env : env;; val dir : string;; val ascii_rep_set : Types.Cdset.t end) =
  struct

    module B = Backend_common.Make (
      struct
        let env = A.env
        let target = Target_no_ident Target_lean
        let id_format_args = (lean_format_op, path_sep)
        let dir = A.dir
      end);;

    module C = Exps_in_context (
      struct
        let env_opt = Some A.env
        let avoid = A.avoid
      end)
    ;;

let use_ascii_rep_for_const (cd : const_descr_ref) : bool =
  Types.Cdset.mem cd A.ascii_rep_set
;;

let field_ident_to_output fd ascii_alternative =
  let ident = B.const_id_to_ident fd ascii_alternative in
  let name = Ident.get_name ident in
  let stripped = Name.strip_lskip name in
    from_string (Name.to_string stripped)
;;

let typ_ident_to_output (p : Path.t id) = B.type_id_to_output p

    let rec def_extra (inside_instance: bool) (callback: def list -> Output.t) (inside_module: bool) (m: def_aux) =
      match m with
        | Lemma (skips, lemma_typ, targets, (name, _), skips', e) ->
          if in_target targets then
            let name = Name.to_output Term_var name
            in
              Output.flat [
                ws skips; from_string "theorem"; name; ws skips'; from_string " : ";
                from_string "("; exp inside_instance e; from_string " : Prop) ";
                from_string ":= by sorry"
              ]
          else
            from_string "/- removed lemma intended for another backend -/"
        | _ -> emp
    and def (inside_instance: bool) (callback : def list -> Output.t) (inside_module : bool) (m : def_aux) =
      match m with
      | Type_def (skips, def) ->
          let funcl = if is_abbreviation def then
              type_def_abbreviation
            else if is_record def then
              type_def_record
            else
              type_def inside_module
          in
            Output.flat [
              ws skips; funcl def
            ]
      | Val_def (def) ->
          let class_constraints = val_def_get_class_constraints A.env def in
          let tv_set = val_def_get_free_tnvars A.env def in
          val_def false None (snd (Typed_ast_syntax.is_recursive_def m)) def tv_set class_constraints
      | Module (skips, (name, l), mod_binding, skips', skips'', defs, skips''') ->
        let name = lskips_t_to_output name in
        let body = callback defs in
          Output.flat [
            ws skips; from_string "namespace "; name; ws skips'; ws skips'';
            body; from_string "\nend "; name; ws skips'''
          ]
      | Rename (skips, name, mod_binding, skips', mod_descr) -> emp
      | OpenImport (oi, ms) ->
          let (ms', sk) = B.open_to_open_target ms in
          if (ms' = []) then
             ws (oi_get_lskip oi)
          else (
            let d' = OpenImportTarget(oi, Targets_opt_none, ms') in
            def inside_instance callback inside_module d' ^ ws sk
          )
      | OpenImportTarget(oi, _, []) -> ws (oi_get_lskip oi)
      | OpenImportTarget (Ast.OI_open skips, targets, mod_descrs) ->
          ws skips ^
          let handle_mod (sk, md) = begin
            Output.flat [
              from_string "import"; ws sk; from_string md; from_string "\n"
            ; from_string "open"; ws sk; from_string md; from_string "\n"
            ]
          end in
          if (not (in_target targets)) then emp else Output.flat (List.map handle_mod mod_descrs)
      | OpenImportTarget _ -> emp
      | Indreln (skips, targets, names, cs) ->
          if in_target targets then
            let c = Seplist.to_list cs in
              clauses inside_instance c
          else
            let cs = Seplist.to_list cs in
              Output.flat [
                ws skips; clauses inside_instance cs
              ]
      | Val_spec val_spec -> from_string "\n/- removed value specification -/\n"
      | Class (Ast.Class_inline_decl (skips, _), _, _, _, _,_, _, _) -> ws skips
      | Class (Ast.Class_decl skips, skips', (name, l), tv, p, skips'', body, skips''') ->
          let name = Name.to_output Term_var name in
          let tv =
            begin
              match tv with
                | Typed_ast.Tn_A (_, tyvar, _) ->
                    from_string @@ Ulib.Text.to_string tyvar
                | Typed_ast.Tn_N (_, nvar, l) ->
                    from_string "NOT_SUPPORTED"
            end
          in
          let body_entries =
            List.map (fun (skips, targets_opt, (name, l), const_descr_ref, ascii_rep_opt, skips', src_t) ->
              let name' = B.const_ref_to_name name true const_descr_ref in
              let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name')) in
                Output.flat [
                  ws skips; from_string name_str; from_string " :"; ws skips'; pat_typ src_t
                ]
            ) body
          in
          let body_out = Output.concat (from_string "\n") body_entries in
          Output.flat [
            ws skips; from_string "class"; ws skips'; name; from_string " ("; tv; from_string " : Type) where"
          ; ws skips''; from_string "\n"; body_out
          ; ws skips'''
          ]
      | Instance (Ast.Inst_default skips, i_ref, inst, vals, skips') -> emp
      | Instance (Ast.Inst_decl skips, i_ref, inst, vals, skips') ->
        let l_unk = Ast.Unknown in
          let prefix =
            match inst with
              | (constraint_prefix_opt, skips, ident, path, src_t, skips') ->
                let tyvars, c =
                  begin
                  match constraint_prefix_opt with
                    | None -> emp, emp
                    | Some c ->
                      begin
                      match c with
                        | Cp_forall (skips, tnvar_list, skips', constraints_opt) ->
                            let tnvars =
                              Output.concat (from_string " ") (List.map (fun t ->
                                match t with
                                  | Typed_ast.Tn_A (_, var, _) ->
                                      from_string @@ Ulib.Text.to_string var
                                  | _ ->
                                    raise (Reporting_basic.err_general true l_unk "nexps not supported in instance declarations")
                              ) tnvar_list)
                            in
                            let cs =
                              begin
                              match constraints_opt with
                                | None -> emp
                                | Some cs ->
                                  match cs with
                                    | Cs_list (ident_var_seplist, skips_opt, range_seplist, skips') ->
                                      let ident_var_list = Seplist.to_list ident_var_seplist in
                                      let ident_var_list =
                                        Output.concat (from_string " ") (List.map (fun (id, var) ->
                                          let var =
                                            match var with
                                              | Typed_ast.Tn_A (_, var, _) ->
                                                  from_string @@ Ulib.Text.to_string var
                                              | _ ->
                                                raise (Reporting_basic.err_general true l_unk "nexps not supported in instance declarations")
                                          in
                                          let ident = Name.to_output Term_var (Ident.get_name id) in
                                            Output.flat [
                                              from_string "["; ident; from_string " "; var; from_string "]"
                                            ]) ident_var_list)
                                      in
                                        ident_var_list
                              end
                            in
                              tnvars, cs
                      end
                  end
                in
                let id = Name.to_output Term_var (Ident.get_name ident) in
                let tyvars_typeset =
                  if tyvars = emp then
                    emp
                  else
                    Output.flat [
                      from_string "("; tyvars; from_string " : Type)"
                    ]
                in
                  Output.flat [
                    ws skips; tyvars_typeset; from_string " "; c; from_string " : "; id
                  ; pat_typ src_t
                  ]
          in
          let body =
            Output.concat (from_string "\n") (List.map (fun d -> val_def true (Some i_ref) false d Types.TNset.empty []) vals)
          in
            Output.flat [
              ws skips; from_string "instance"; prefix; from_string " where";
              from_string "\n"; body;
              ws skips'
            ]
      | Comment c ->
        let ((def_aux, skips_opt), l, lenv) = c in
        let skips = match skips_opt with None -> from_string "\n" | Some s -> ws s in
          Output.flat [
            skips; from_string "/- "; def inside_instance callback inside_module def_aux; from_string " -/"
          ]
      | _ -> emp
    and val_def inside_instance i_ref_opt is_recursive def tv_set class_constraints =
      begin
        let constraints =
          let body =
            Output.concat (from_string " ") (List.map (fun (path, tnvar) ->
              let name = Path.get_name path in
              let name = from_string (Ulib.Text.to_string (Name.to_rope name)) in
              let var =
                match tnvar with
                  | Types.Ty var -> from_string @@ Ulib.Text.to_string @@ Types.tnvar_to_rope tnvar
                  | _ ->
                      raise (Reporting_basic.err_general true Ast.Unknown "nexps not supported in type class constraints")
              in
                Output.flat [
                  from_string "["; name; from_string " "; var; from_string "]"
                ]
            ) class_constraints)
          in
          if List.length class_constraints = 0 then
            emp
          else
            body
        in
        match def with
          | Let_def (skips, targets, (p, name_map, topt, sk, e)) ->
              if in_target targets then
                let bind = (Let_val (p, topt, sk, e), Ast.Unknown) in
                let body = let_body inside_instance i_ref_opt true tv_set bind in
                let defn, ending =
                  if inside_instance then
                    emp, emp
                  else
                    from_string "def", emp
                  in
                    Output.flat [
                      ws skips; defn; constraints; body; ending
                    ]
              else
                ws skips ^ from_string "/- removed value definition intended for another target -/"
          | Fun_def (skips, rec_flag, targets, funcl_skips_seplist) ->
              if in_target targets then
                let skips' = match rec_flag with FR_non_rec -> None | FR_rec sk -> sk in
                let header, ending =
                  if is_recursive then
                    if inside_instance then
                      ws (match skips' with Some s -> Some s | None -> None), emp
                    else
                      Output.flat [
                        from_string "def"
                      ], emp
                  else
                    if inside_instance then
                      emp, emp
                    else
                      from_string "def", emp
                in
                let funcls = Seplist.to_list funcl_skips_seplist in
                let bodies = List.map (funcl inside_instance i_ref_opt constraints tv_set) funcls in
                let formed = concat_str "\n" bodies in
                  Output.flat [
                    ws skips; header; formed; ending
                  ]
              else
                from_string "\n/- removed recursive definition intended for another target -/"
          | _ -> from_string "\n/- removed top-level value definition -/"
      end
    and clauses (inside_instance: bool) clause_list =
      let gather_names clause_list =
        let rec gather_names_aux buffer clauses =
          match clauses with
            | []    -> buffer
            | (Rule(_,_, _, _, _, _, _, name_lskips_annot, _, _),_)::xs ->
              let name = name_lskips_annot.term in
              let name = Name.strip_lskip name in
              if List.mem name buffer then
                gather_names_aux buffer xs
              else
                gather_names_aux (name::buffer) xs
        in
          gather_names_aux [] clause_list
      in
      let gathered = gather_names clause_list in
      let compare_clauses_by_name name (Rule(_,_, _, _, _, _, _, name', _, _),_) =
        let name' = name'.term in
        let name' = Name.strip_lskip name' in
          Stdlib.compare name name' = 0
      in
      let indrelns =
        List.map (fun name ->
          let name_string = Name.to_string name in
          let bodies = List.filter (compare_clauses_by_name name) clause_list in
          let index_types =
            match bodies with
              | [] -> [from_string "Prop"]
              | (Rule(_,_, _, _, _, _, _, _, _, exp_list),_)::xs ->
                  List.map (fun t ->
                    Output.flat [
                      from_string "("; indreln_typ @@ C.t_to_src_t (Typed_ast.exp_to_typ t); from_string ")"
                    ]
                  ) exp_list
          in
          let bodies =
            List.map (fun (Rule(name_lskips_t, skips0, skips, name_lskips_annot_list, skips', exp_opt, skips'', name_lskips_annot, c, exp_list),_) ->
              let constructor_name = from_string (Name.to_string (Name.strip_lskip name_lskips_t)) in
              let antecedent =
                match exp_opt with
                  | None -> emp
                  | Some e ->
                    match dest_and_exps A.env e with
                    | [] -> emp
                    | ants ->
                      flat [
                        concat_str " → "
                          (List.map (fun e ->
                               flat [ from_string "(";
                                      exp inside_instance e;
                                      from_string " : Prop)" ]) ants);
                        from_string " → "
                      ]
              in
              let bound_variables =
                concat_str " " @@ List.map (fun b ->
                  match b with
                    | QName n -> from_string (Name.to_string (Name.strip_lskip n.term))
                    | _ -> assert false
                ) name_lskips_annot_list
              in
              let binder, binder_sep =
                match name_lskips_annot_list with
                  | [] -> emp, emp
                  | x::xs -> from_string "∀ ", from_string ", "
              in
              let indices = concat_str " " @@ List.map (exp inside_instance) exp_list in
              let index_free_vars = List.map (fun t -> Types.free_vars (Typed_ast.exp_to_typ t)) exp_list in
              let index_free_vars = List.fold_right Types.TNset.union index_free_vars Types.TNset.empty in
              let index_free_vars_typeset = concat_str " " @@ List.map (fun v -> from_string (Name.to_string (Types.tnvar_to_name v))) (Types.TNset.elements index_free_vars) in
              let relation_name = from_string (Name.to_string name) in
                Output.flat [
                  from_string "  | "; constructor_name; from_string " : ";
                  binder; bound_variables; binder_sep; antecedent;
                  relation_name; from_string " "; index_free_vars_typeset; from_string " "; indices
                ], index_free_vars
            ) bodies
          in
          let free_vars = List.map (fun (x, y) -> y) bodies in
          let free_vars = Types.TNset.elements @@ List.fold_right Types.TNset.union free_vars Types.TNset.empty in
          let free_vars_typeset =
            concat_str " " @@ List.map (fun v ->
              Output.flat [
                from_string "("; from_string (Name.to_string (Types.tnvar_to_name v)); from_string " : Type)"
              ]) free_vars
          in
          let index_types =
            Output.flat [
              concat_str " → " index_types; from_string " → Prop"
            ]
          in
          let bodies = concat_str "\n" @@ List.map (fun (x, y) -> x) bodies in
          Output.flat [
            from_string name_string; from_string " "; free_vars_typeset; from_string " : "; index_types; from_string " where\n";
            bodies
          ]
        ) gathered
      in
        Output.flat [
          from_string "\ninductive "; concat_str "\n" indrelns
        ]
    and let_body inside_instance i_ref_opt top_level tv_set ((lb, _):letbind) =
      match lb with
        | Let_val (p, topt, skips, e) ->
            let p = def_pattern p in
            let tv_set_sep, tv_set =
              if Types.TNset.cardinal tv_set = 0 then
                let typ = Typed_ast.exp_to_typ e in
                let tv_set = Types.free_vars typ in
                  if Types.TNset.cardinal tv_set = 0 then
                    emp, tv_set
                  else
                    from_string " ", tv_set
              else
                from_string " ", tv_set
            in
            let tv_set = let_type_variables top_level tv_set in
            let topt =
              match topt with
                | None        -> emp
                | Some (s, t) ->
                    Output.flat [
                      ws s; from_string " :"; pat_typ t
                    ]
            in
            let e = exp inside_instance e in
              Output.flat [
                p; tv_set_sep; tv_set; topt; ws skips; from_string " :="; e
              ]
        | Let_fun (n, pats, typ_opt, skips, e) ->
          funcl_aux inside_instance i_ref_opt emp tv_set (n.term, pats, typ_opt, skips, e)
    and funcl_aux inside_instance i_ref_opt constraints tv_set (n, pats, typ_opt, skips, e) =
      let name_skips = Name.get_lskip n in
      let name = from_string (Name.to_string (Name.strip_lskip n)) in
      let pat_skips =
        match pats with
          | [] -> emp
          | _  -> from_string " "
      in
      let constraints_sep =
        if constraints = emp then
          emp
        else
          from_string " "
      in
      let tv_set_sep, tv_set =
        if inside_instance then
          emp, emp
        else
          if Types.TNset.cardinal tv_set = 0 then
            let typ = Typed_ast.exp_to_typ e in
            let tv_set = Types.free_vars typ in
              if Types.TNset.cardinal tv_set = 0 then
                emp, let_type_variables true tv_set
              else
                from_string " ", let_type_variables true tv_set
          else
            from_string " ", let_type_variables true tv_set
      in
      let typ_opt =
        match typ_opt with
          | None -> emp
          | Some (s, t) ->
              Output.flat [
                ws s; from_string " : "; pat_typ t
              ]
      in
        Output.flat [
          ws name_skips; from_string " "; name; tv_set_sep; tv_set; constraints_sep; constraints; pat_skips;
          fun_pattern_list inside_instance pats; ws skips; typ_opt; from_string " := "; exp inside_instance e
        ]
    and funcl inside_instance i_ref_opt constraints tv_set ({term = n}, c, pats, typ_opt, skips, e) =
      let n =
        if inside_instance then
          match i_ref_opt with
            | None -> B.const_ref_to_name n true c
            | Some i_ref ->
              begin
                let instance = Types.i_env_lookup Ast.Unknown A.env.i_env i_ref in
                let filtered = List.filter (fun x -> snd x = c) instance.inst_methods in
                  match filtered with
                    | x::xs -> B.const_ref_to_name n true (fst x)
                    | _   -> assert false
              end
        else
          B.const_ref_to_name n true c
      in
        funcl_aux inside_instance i_ref_opt constraints tv_set (n, pats, typ_opt, skips, e)
    and let_type_variables top_level tv_set =
      if Types.TNset.is_empty tv_set || not top_level then
        emp
      else
      let tyvars =
        List.map (fun tv -> match tv with
          | Types.Ty tv -> id Type_var (Tyvar.to_rope tv)
          | Types.Nv nv -> id Type_var (Nvar.to_rope nv))
        (Types.TNset.elements tv_set)
      in
        if List.length tyvars = 0 || not top_level then
          emp
        else
          (from_string "{") ^ (concat_str " " tyvars) ^ (from_string " : Type}")
    and lean_function_application_to_output inside_instance l id args = B.function_application_to_output l (exp inside_instance) id args
    and exp inside_instance e =
      let is_user_exp = Typed_ast_syntax.is_pp_exp e in
        match C.exp_to_term e with
          | Var v ->
              Name.to_output Term_var v
          | Backend (sk, i) ->
              ws sk ^
              Ident.to_output (Term_const (false, true)) path_sep i
          | Lit l -> literal l
          | Do (skips, mod_descr_id, do_line_list, skips', e, skips'', type_int) -> assert false
          | App (e1, e2) ->
              let trans e = block (Typed_ast_syntax.is_pp_exp e) 0 (exp inside_instance e) in
              let sep = (break_hint_space 2) in
              let oL = begin
              let (e0, args) = strip_app_exp e in
                match C.exp_to_term e0 with
                  | Constant cd ->
                    B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd.descr)
                  | _ ->
                    List.map trans (e0 :: args)
              end in
              let o = Output.concat sep oL in
              block is_user_exp 0 o
          | Paren (skips, e, skips') ->
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; ws skips'; from_string ")";
              ]
          | Typed (skips, e, skips', t, skips'') ->
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; from_string " :"; ws skips'; pat_typ t; ws skips''; from_string ")";
              ]
          | Tup (skips, es, skips') ->
              let tups = flat @@ Seplist.to_sep_list (exp inside_instance) (sep (from_string ",")) es in
                Output.flat [
                  ws skips; from_string "("; tups; from_string ")"; ws skips'
                ]
          | List (skips, es, skips') ->
              let lists = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> from_string " ")) (exp inside_instance) (sep @@ from_string ",") es in
                Output.flat [
                  ws skips; from_string "["; lists; from_string "]"; ws skips'
                ]
          | Let (skips, bind, skips', e) ->
              let body = let_body inside_instance None false Types.TNset.empty bind in
                Output.flat [
                  ws skips; from_string "let"; body; ws skips'; from_string "\n"; exp inside_instance e
                ]
          | Constant const ->
            Output.concat emp (B.function_application_to_output (exp_to_locn e) (exp inside_instance) false e const [] (use_ascii_rep_for_const const.descr))
          | Fun (skips, ps, skips', e) ->
              let ps = fun_pattern_list inside_instance ps in
                block_hov (Typed_ast_syntax.is_pp_exp e) 2 (
                  Output.flat [
                    ws skips; from_string "fun"; ps; ws skips'; from_string "=>"; break_hint_space 0; exp inside_instance e
                  ])
          | Function _ ->
              print_and_fail (Typed_ast.exp_to_locn e) "illegal function in extraction, should have been previously macro'd away"
          | Set (skips, es, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (exp inside_instance) (sep @@ from_string ", ") es in
            let skips =
              if skips = Typed_ast.no_lskips then
                from_string " "
              else
                ws skips
            in
              block is_user_exp 0 (
                if Seplist.is_empty es then
                  Output.flat [
                    skips; from_string "∅"
                  ]
                else
                  Output.flat [
                    skips; from_string "{"; body; ws skips'; from_string "}"
                  ])
          | Begin (skips, e, skips') ->
              Output.flat [
                ws skips; from_string "/- begin block -/"; exp inside_instance e; ws skips';
                from_string "/- end block -/"
              ]
          | Record (skips, fields, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (field_update inside_instance) (sep @@ from_string ",") fields in
              Output.flat [
                ws skips; from_string "{ "; body; ws skips'; from_string " }"
              ]
          | Field (e, skips, fd) ->
            let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
              Output.flat [
                exp inside_instance e; from_string "."; ws skips; name
              ]
          | Recup (skips, e, skips', fields, skips'') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (field_update inside_instance) (sep @@ from_string ",") fields in
            let skips'' =
              if skips'' = Typed_ast.no_lskips then
                from_string " "
              else
                ws skips''
            in
              Output.flat [
                 ws skips; from_string "{ "; exp inside_instance e; ws skips'; from_string " with "; body; skips''; from_string " }"
              ]
          | Case (_, skips, e, skips', cases, skips'') ->
            let body = flat @@ Seplist.to_sep_list_last Seplist.Optional (case_line inside_instance) (sep (break_hint_space 2)) cases in
              block is_user_exp 0 (
                Output.flat [
                  ws skips; from_string "match "; exp inside_instance e; from_string " with"; ws skips';
                  break_hint_space 4; body; ws skips''
                ])
          | Infix (l, c, r) ->
              let trans e = block (Typed_ast_syntax.is_pp_exp e) 0 (exp inside_instance e) in
              let sep = (break_hint_space 0) in
              begin
                match C.exp_to_term c with
                  | Constant cd ->
                    begin
                      let pieces = B.function_application_to_output (exp_to_locn e) trans true e cd [l; r] (use_ascii_rep_for_const cd.descr) in
                      let output = Output.concat sep pieces in
                        block is_user_exp 0 output
                    end
                  | _           ->
                    begin
                      let mapped = List.map trans [l; c; r] in
                      let output = Output.concat sep mapped in
                        block is_user_exp 0 output
                    end
              end
          | If (skips, test, skips', t, skips'', f) ->
              block is_user_exp 0 (Output.flat [
                ws skips; break_hint_cut; from_string "if";
                block (Typed_ast_syntax.is_pp_exp test) 0 (exp inside_instance test);
                ws skips'; from_string "then"; break_hint_space 2;
                block (Typed_ast_syntax.is_pp_exp t) 0 (exp inside_instance t);
                ws skips''; break_hint_space 0; from_string "else"; break_hint_space 2;
                block (Typed_ast_syntax.is_pp_exp f) 0 (exp inside_instance f)
              ])
          | Quant (quant, quant_binding_list, skips, e) ->
            let quant =
              match quant with
                | Ast.Q_forall _ -> from_string "∀"
                | Ast.Q_exists _ -> from_string "∃"
            in
            let bindings =
              Output.concat (from_string " ") (
                List.map (fun quant_binding ->
                  match quant_binding with
                    | Typed_ast.Qb_var name_lskips_annot ->
                      let name = name_lskips_annot.term in
                      let skip = Name.get_lskip name in
                      let name = Name.strip_lskip name in
                      let name = Ulib.Text.to_string (Name.to_rope name) in
                        Output.flat [
                          ws skip; from_string name
                        ]
                    | Typed_ast.Qb_restr (bool, skips, pat, skips', e, skips'') ->
                      let pat_out = fun_pattern pat in
                        Output.flat [
                          ws skips; pat_out; ws skips'; from_string " : ";
                          exp inside_instance e; ws skips''
                        ]
                ) quant_binding_list)
            in
              Output.flat [
                quant; from_string " "; bindings; from_string ","; ws skips;
                exp inside_instance e
              ]
          | Comp_binding (_, _, _, _, _, _, _, _, _) -> from_string "/- comp binding -/"
          | Setcomp (_, _, _, _, _, _) -> from_string "/- setcomp -/"
          | Nvar_e (skips, nvar) ->
            let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r "") (Nvar.to_rope nvar) in
              Output.flat [
                ws skips; nvar
              ]
          | VectorAcc (e, skips, nexp, skips') ->
              Output.flat [
                from_string "Vector.get "; exp inside_instance e; ws skips; src_nexp nexp; ws skips'
              ]
          | VectorSub (e, skips, nexp, skips', nexp', skips'') ->
              Output.flat [
                from_string "Vector.slice "; exp inside_instance e; ws skips; src_nexp nexp;
                ws skips'; src_nexp nexp'; ws skips'
              ]
          | Vector (skips, es, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (exp inside_instance) (sep @@ from_string ", ") es in
            let skips =
              if skips = Typed_ast.no_lskips then
                from_string " "
              else
                ws skips
            in
              block is_user_exp 0 (
                if Seplist.is_empty es then
                  Output.flat [
                    skips; from_string "#v[]"
                  ]
                else
                  Output.flat [
                    skips; from_string "#v["; body; ws skips'; from_string "]"
                  ])
    and src_nexp n =
      match n.nterm with
        | Nexp_var (skips, nvar) ->
          let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r"") (Nvar.to_rope nvar) in
            Output.flat [
              ws skips; nvar
            ]
        | Nexp_const (skips, i) ->
            Output.flat [
              ws skips; from_string (Z.to_string i)
            ]
        | Nexp_mult (nexp, skips, nexp') ->
            Output.flat [
              src_nexp nexp; ws skips; from_string "*"; src_nexp nexp'
            ]
        | Nexp_add (nexp, skips, nexp') ->
            Output.flat [
              src_nexp nexp; ws skips; from_string "+"; src_nexp nexp'
            ]
        | Nexp_paren (skips, nexp, skips') ->
            Output.flat [
              ws skips; from_string "("; src_nexp nexp; ws skips'; from_string ")"
            ]
    and case_line inside_instance (p, skips, e, _) =
        Output.flat [
          from_string "| "; def_pattern p; ws skips; from_string "=>"; break_hint_space 2; exp inside_instance e
        ]
    and field_update inside_instance (fd, skips, e, _) =
      let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
        Output.flat [
          name; ws skips; from_string " := "; exp inside_instance e
        ]
    and literal l =
      match l.term with
        | L_true skips -> ws skips ^ from_string "true"
        | L_false skips -> ws skips ^ from_string "false"
        | L_num (skips, n, _) -> ws skips ^ num n
        | L_string (skips, s, _) ->
            let escaped = Str.global_replace (Str.regexp "\"") "\\\"" s in
            ws skips ^ str (Ulib.Text.of_string escaped)
        | L_unit (skips, skips') -> ws skips ^ from_string "()" ^ ws skips'
        | L_zero s ->
          Output.flat [
            ws s; from_string "false"
          ]
        | L_one s ->
          Output.flat [
            ws s; from_string "true"
          ]
        | L_char (s, c, _) ->
          let c = from_string (Printf.sprintf "'%s'" (Char.escaped c)) in
          Output.flat [
            ws s; c
          ]
        | L_numeral (skips, i, _) ->
          let i = from_string @@ Z.to_string i in
            Output.flat [
              ws skips; i
            ]
        | L_vector (s, v, v') -> assert false
        | L_undefined (skips, explanation) ->
          let typ = l.typ in
          let src_t = C.t_to_src_t typ in
            Output.flat [
              ws skips; default_value src_t;
              from_string " /- "; from_string explanation; from_string " -/"
            ]
    and fun_pattern_list inside_instance ps =
      let f =
        if inside_instance then
          def_pattern
        else
          fun_pattern
      in
        Output.flat [
          from_string " "; (concat_str " " @@ List.map f ps)
        ]
    and fun_pattern p =
      match p.term with
        | P_wild skips ->
          let skips =
            if skips = Typed_ast.no_lskips then
              from_string " "
            else
              ws skips
          in
          let t = C.t_to_src_t p.typ in
            Output.flat [
              from_string "("; skips; from_string "_ : "; pat_typ t; from_string ")"
            ]
        | P_var v ->
          let name = lskips_t_to_output v in
          let t = C.t_to_src_t p.typ in
            Output.flat [
              from_string "("; name; from_string " : "; pat_typ t; from_string ")"
            ]
        | P_lit l -> literal l
        | P_as (skips, p, skips', (n, l), skips'') ->
          let name = Name.to_output Term_var n in
            Output.flat [
              ws skips; from_string "("; fun_pattern p; from_string ")"; ws skips'; name; ws skips''
            ]
        | P_typ (skips, p, skips', t, skips'') ->
            Output.flat [
              ws skips; from_string "("; def_pattern p; ws skips'; from_string " :";
              ws skips''; pat_typ t; from_string ")"
            ]
        | P_tup (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list fun_pattern (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "("; body; ws skips'; from_string ")"
            ]
        | P_record (_, fields, _) ->
            print_and_fail p.locn "illegal record pattern in code extraction, should have been compiled away"
        | P_cons (p1, skips, p2) ->
            Output.flat [
              def_pattern p1; ws skips; from_string " :: "; def_pattern p2
            ]
        | P_var_annot (n, t) ->
            let name = Name.to_output Term_var n in
              Output.flat [
                from_string "("; name; from_string " : "; pat_typ t; from_string ")"
              ]
        | P_list (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional fun_pattern (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_paren (skips, p, skips') ->
            Output.flat [
              ws skips; from_string "("; fun_pattern p; ws skips'; from_string ")"
            ]
        | P_const(cd, ps) ->
            (* Lean 4: prefix constructor patterns with . for dot notation *)
            let sk = Typed_ast.ident_get_lskip cd in
            let cd_no_sk = {cd with id_path = Typed_ast.ident_replace_lskip cd.id_path Typed_ast.no_lskips} in
            let oL = B.pattern_application_to_output p.locn fun_pattern cd_no_sk ps (use_ascii_rep_for_const cd.descr) in
            Output.flat [ws sk; from_string "."; concat emp oL]
        | P_backend(sk, i, _, ps) ->
            ws sk ^
            from_string "." ^
            Ident.to_output (Term_const (false, true)) path_sep (Ident.replace_lskip i Typed_ast.no_lskips) ^
            concat texspace (List.map fun_pattern ps)
        | P_num_add ((name, l), skips, skips', k) ->
            let name = lskips_t_to_output name in
              Output.flat [
                ws skips; from_string "("; name; from_string " + "; from_string (Z.to_string k); from_string ")"
              ]
        | _ -> from_string "/- pattern not supported -/"
    and def_pattern p =
      match p.term with
        | P_wild skips ->
          let skips =
            if skips = Typed_ast.no_lskips then
              from_string " "
            else
              ws skips
          in
            Output.flat [
              skips; from_string "_"
            ]
        | P_var v -> Name.to_output Term_var v
        | P_lit l -> literal l
        | P_as (skips, p, skips', (n, l), skips'') ->
          let name = Name.to_output Term_var n in
            Output.flat [
              ws skips; from_string "("; def_pattern p; ws skips'; from_string ")"; ws skips'; name
            ]
        | P_typ (skips, p, _, t, skips') ->
            Output.flat [
              ws skips; from_string "("; def_pattern p; from_string " : "; pat_typ t; from_string ")"; ws skips'
            ]
        | P_tup (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list def_pattern (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "("; body; from_string ")"; ws skips'
            ]
        | P_record (_, fields, _) ->
            print_and_fail p.locn "illegal record pattern in code extraction, should have been compiled away"
        | P_cons (p1, skips, p2) ->
            Output.flat [
              def_pattern p1; ws skips; from_string " :: "; def_pattern p2
            ]
        | P_var_annot (n, t) ->
            Name.to_output Term_var n
        | P_list (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional def_pattern (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_paren (skips, p, skips') ->
            Output.flat [
              from_string "("; ws skips; def_pattern p; ws skips'; from_string ")"
            ]
        | P_const(cd, ps) ->
            (* Lean 4: prefix constructor patterns with . for dot notation *)
            let sk = Typed_ast.ident_get_lskip cd in
            let cd_no_sk = {cd with id_path = Typed_ast.ident_replace_lskip cd.id_path Typed_ast.no_lskips} in
            let oL = B.pattern_application_to_output p.locn def_pattern cd_no_sk ps (use_ascii_rep_for_const cd.descr) in
            Output.flat [ws sk; from_string "."; concat emp oL]
        | P_backend(sk, i, _, ps) ->
            ws sk ^
            from_string "." ^
            Ident.to_output (Term_const (false, true)) path_sep (Ident.replace_lskip i Typed_ast.no_lskips) ^
            concat texspace (List.map def_pattern ps)
        | P_num_add ((name, l), skips, skips', k) ->
            let name = lskips_t_to_output name in
              Output.flat [
                ws skips; from_string "("; name; from_string " + "; from_string (Z.to_string k); from_string ")"
              ]
        | _ -> from_string "/- pattern not supported -/"
    and type_def_abbreviation def =
      match Seplist.hd def with
        | ((n, _), tyvars, path, Te_abbrev (skips, t),_) ->
            let n = B.type_path_to_name n path in
            let name = Name.to_output (Type_ctor (false, false)) n in
            let tyvars' = type_def_type_variables tyvars in
            let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
            let body = pat_typ t in
              Output.flat [
                from_string "abbrev"; name; tyvar_sep; tyvars';
                ws skips; from_string " := "; body; from_string "\n";
              ]
        | _ -> from_string "/- Internal Lem error, please report. -/"
    and type_def_record def =
      match Seplist.hd def with
        | (n, tyvars, path, (Te_record (skips, skips', fields, skips'')),_) ->
            let (n', _) = n in
            let n' = B.type_path_to_name n' path in
            let name = Name.to_output (Type_ctor (false, false)) n' in
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) field (sep @@ from_string "\n") fields in
            let tyvars' = type_def_type_variables tyvars in
            let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
              Output.flat [
                from_string "structure"; name; tyvar_sep; tyvars';
                ws skips; from_string " where"; ws skips';
                from_string "\n"; body; ws skips''; from_string "\n";
              ]
        | _ -> from_string "/- Internal Lem error, please report. -/"
    and type_def inside_module defs =
      let body = flat @@ Seplist.to_sep_list type_def' (sep @@ from_string "\n") defs in
        Output.flat [
          from_string "inductive"; body; from_string "\n";
        ]
    and type_def' ((n0, l), ty_vars, t_path, ty, _) =
      let n = B.type_path_to_name n0 t_path in
      let name = Name.to_output (Type_ctor (false, false)) n in
      let ty_vars =
        List.map (
          function
            | Typed_ast.Tn_A (_, tyvar, _) -> Tyvar (from_string @@ Ulib.Text.to_string tyvar)
            | Typed_ast.Tn_N (_, nvar, _) -> Nvar (from_string @@ Ulib.Text.to_string nvar)
          ) ty_vars
      in
        match ty with
          | Te_opaque ->
              Output.flat [
                inductive ty_vars n; from_string " where"
              ]
          | _ ->
            Output.flat [
              inductive ty_vars n; tyexp name ty_vars ty
            ]
    and inductive ty_vars name =
      let ty_var_sep = if List.length ty_vars = 0 then emp else from_string " " in
      let ty_vars = inductive_type_variables ty_vars in
      let name = Name.to_output (Type_ctor (false, false)) name in
        Output.flat [
          from_string " "; name; ty_var_sep; ty_vars
        ]
    and inductive_type_variables vars =
      let mapped = List.map (fun v ->
          match v with
            | Tyvar x ->
              Output.flat [
                from_string "("; x; from_string " : Type)"
              ]
            | Nvar x ->
              Output.flat [
                from_string "("; x; from_string " : Nat)"
              ]) vars
      in
        concat_str " " mapped
    and tyexp name ty_vars =
      function
        | Te_opaque -> emp
        | Te_abbrev (skips, t) -> ws skips ^ from_string " := " ^ pat_typ t
        | Te_record (skips, _, fields, skips') -> ws skips ^ from_string " where\n" ^ tyexp_record fields ^ ws skips'
        | Te_variant (skips, ctors) ->
          let body = flat @@ Seplist.to_sep_list_first Seplist.Optional (constructor name ty_vars) (sep @@ from_string "\n") ctors in
            Output.flat [
              from_string " where"; ws skips; from_string "\n"; body
            ]
    and constructor ind_name (ty_vars : variable list) ((name0, _), c_ref, skips, args) =
      let ctor_name = B.const_ref_to_name name0 false c_ref in
      let ctor_name = Name.to_output (Type_ctor (false, false)) ctor_name in
      let body = flat @@ Seplist.to_sep_list pat_typ (sep @@ from_string " → ") args in
      let ty_vars_typeset =
        concat_str " " @@ List.map (fun v ->
          match v with
            | Tyvar out -> out
            | Nvar out -> out
        ) ty_vars
      in
      let tail =
        Output.flat [
          from_string " → "; ind_name; from_string " "; ty_vars_typeset
        ]
      in
        if Seplist.length args = 0 then
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; ind_name
          ; from_string " "; ty_vars_typeset
          ]
        else
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; body; tail
          ]
    and tyexp_record fields =
      let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) field (sep @@ from_string "\n") fields in
        body
    and pat_typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) ->
            Output.flat [
              ws skips; id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v)
            ]
        | Typ_fn (t1, skips, t2) ->
            if skips = Typed_ast.no_lskips then
              pat_typ t1 ^ from_string " → " ^ ws skips ^ pat_typ t2
            else
              pat_typ t1 ^ from_string " →" ^ ws skips ^ pat_typ t2
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list pat_typ (sep @@ from_string " ×") ts in
              from_string "(" ^ body ^ from_string ")"
        | Typ_app (p, ts) ->
            let (ts, head) = B.type_app_to_output pat_typ p ts in
            let ts = concat_str " " @@ List.map pat_typ ts in
              Output.flat [
                head; from_string " "; ts
              ]
        | Typ_paren(skips, t, skips') ->
            ws skips ^ from_string "(" ^ pat_typ t ^ ws skips' ^ from_string ")"
        | Typ_with_sort(t,_) -> pat_typ t
        | Typ_len nexp -> src_nexp nexp
        | Typ_backend (p, ts) ->
          let i = Path.to_ident (ident_get_lskip p) p.descr in
          let i = Ident.to_output (Type_ctor (false, true)) path_sep i in
          let ts = concat emp @@ List.map pat_typ ts in
            Output.flat [
              i; from_string " "; ts
            ]
    and typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) -> id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v)
        | Typ_fn (t1, skips, t2) -> typ t1 ^ ws skips ^ kwd "→" ^ typ t2
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list typ (sep @@ from_string " ×") ts in
              from_string "(" ^ body ^ from_string ")"
        | Typ_app (p, ts) ->
           typ_ident_to_output p
        | Typ_paren (skips, t, skips') ->
            ws skips ^ from_string "(" ^ typ t ^ from_string ")" ^ ws skips'
        | Typ_with_sort (t, sort) -> typ t
        | Typ_len nexp -> src_nexp nexp
        | _ -> assert false
    and type_def_type_variables tvs =
      match tvs with
        | [] -> emp
        | [Typed_ast.Tn_A tv] -> from_string "(" ^ tyvar tv ^ from_string " : Type)"
        | tvs ->
          let mapped = List.map (fun t ->
            match t with
              | Typed_ast.Tn_A (_, tv, _) ->
                let tv = from_string @@ Ulib.Text.to_string tv in
                  Output.flat [
                    from_string "("; tv; from_string " : Type)"
                  ]
              | Typed_ast.Tn_N nv ->
                  Output.flat [
                    from_string "("; from_string "nv : Nat)"
                  ]) tvs
          in
            Output.flat [
              from_string " "; concat_str " " mapped
            ]
    and indreln_typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) -> id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v)
        | Typ_fn (t1, skips, t2) ->
          begin
            match t2.term with
              | Typ_app (p, []) ->
                if p.descr = Path.boolpath then
                  indreln_typ t1 ^ ws skips ^ from_string " → " ^ from_string "Prop"
                else
                  indreln_typ t1 ^ ws skips ^ from_string " → " ^ indreln_typ t2
              | _ ->
                indreln_typ t1 ^ ws skips ^ from_string " → " ^ indreln_typ t2
          end
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list indreln_typ (sep @@ from_string " ×") ts in
              from_string "(" ^ body ^ from_string ")"
        | Typ_app (p, ts) ->
          let args = concat_str " " @@ List.map indreln_typ ts in
          let args_space = if List.length ts = 1 then from_string " " else emp in
            Output.flat [
              typ_ident_to_output p; args_space; args
            ]
        | Typ_paren(skips, t, skips') ->
            ws skips ^ from_string "(" ^ indreln_typ t ^ from_string ")" ^ ws skips'
        | Typ_with_sort(t, _) -> indreln_typ t
        | Typ_len nexp -> src_nexp nexp
        | _ -> assert false
    and field ((n, _), f_ref, skips, t) =
      Output.flat [
          from_string "  ";
          Name.to_output Term_field (B.const_ref_to_name n false f_ref);
          ws skips; from_string " :"; pat_typ t
      ]
    and default_value (s : src_t) : Output.t =
      match s.term with
        | Typ_wild _ -> from_string "sorry /- DAEMON -/"
        | Typ_var _ -> from_string "sorry /- DAEMON -/"
        | Typ_len _ -> from_string "0"
        | Typ_tup seplist ->
            let src_ts = Seplist.to_list seplist in
            let mapped = List.map default_value src_ts in
              Output.flat [
                from_string "("; concat_str ", " mapped; from_string ")"
              ]
        | Typ_app (path, src_ts) ->
            if List.length src_ts = 0 then
              from_string "default"
            else
              from_string "default"
        | Typ_paren (_, src_t, _)
        | Typ_with_sort (src_t, _) -> default_value src_t
        | Typ_fn (dom, _, rng) ->
            let v = generate_fresh_name () in
              Output.flat [
                from_string "(fun ("; from_string v; from_string " : "; pat_typ dom;
                from_string ") => "; default_value rng; from_string ")"
              ]
        | _ -> assert false
      ;;
end
;;


module CdsetE = Util.ExtraSet(Types.Cdset)

module LeanBackend (A : sig val avoid : var_avoid_f option;; val env : env;; val dir : string end) =
  struct

    let rec defs inside_instance inside_module (ds : def list) =
        List.fold_right (fun (((d, s), l, lenv):def) y ->
          let ue = add_def_entities (Target_no_ident Target_lean) true empty_used_entities ((d,s),l,lenv) in
          let callback = defs false true in
          let module C = LeanBackendAux (
            struct
              let avoid = A.avoid;;
              let env = {A.env with local_env = lenv};;
              let ascii_rep_set = CdsetE.from_list ue.used_consts;;
              let dir = A.dir;;
            end)
          in
          let (before_out, d') = Backend_common.def_add_location_comment ((d,s),l,lenv) in
          before_out ^
          match s with
            | None   -> C.def inside_instance callback inside_module d' ^ y
            | Some s -> C.def inside_instance callback inside_module d' ^ ws s ^ y
        ) ds emp
    and defs_extra inside_instance inside_module (ds: def list) =
        List.fold_right (fun (((d, s), l, lenv):def) y ->
          let ue = add_def_entities (Target_no_ident Target_lean) true empty_used_entities ((d,s),l,lenv) in
          let module C = LeanBackendAux (
            struct
              let avoid = A.avoid;;
              let env = {A.env with local_env = lenv};;
              let ascii_rep_set = CdsetE.from_list ue.used_consts;;
              let dir = A.dir;;
            end)
          in
          let callback = defs false true in
          match s with
            | None   -> C.def_extra inside_instance callback inside_module d ^ y
            | Some s -> C.def_extra inside_instance callback inside_module d ^ ws s ^ y
        ) ds emp
    ;;

    let lean_defs ((ds : def list), end_lex_skips) =
      let lean_defs = defs false false ds in
      let lean_defs_extra = defs_extra false false ds in
        ((to_rope (r"\"") lex_skip need_space @@ lean_defs ^ ws end_lex_skips),
          to_rope (r"\"") lex_skip need_space @@ lean_defs_extra ^ ws end_lex_skips)
    ;;
  end
