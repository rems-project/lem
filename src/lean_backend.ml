(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*  Lean 4 backend                                                        *)
(*                                                                        *)
(*  Translates Lem definitions into Lean 4 syntax. Uses the shared        *)
(*  Backend_common infrastructure for identifier resolution and target    *)
(*  representation handling.                                               *)
(*                                                                        *)
(*  Key design decisions:                                                  *)
(*  - Block formatting is disabled (Lean 4 is whitespace-sensitive)       *)
(*  - UTF-8 output uses Meta_utf8 to avoid double-encoding (×, →, etc.)  *)
(*  - Constructors are brought into scope via 'open TypeName' after each  *)
(*    inductive definition, instead of dot-notation                       *)
(*  - Class methods are brought into scope via 'open ClassName'           *)
(*  - Mutual inductives with heterogeneous parameter counts use indexed   *)
(*    types (parameters become indices with Type 1 universe)              *)
(*  - Target-specific class methods ({hol}, {coq}, etc.) are filtered     *)
(*    from both class and instance definitions                            *)
(*  - BEq is derived for types without function-typed constructor args    *)
(*  - Inhabited instances use sorry for mutual recursive types            *)
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

let lean_string_escape s =
  let buf = Buffer.create (String.length s) in
  String.iter (fun c -> match c with
    | '\\' -> Buffer.add_string buf "\\\\"
    | '"' -> Buffer.add_string buf "\\\""
    | '\n' -> Buffer.add_string buf "\\n"
    | '\t' -> Buffer.add_string buf "\\t"
    | '\000' -> Buffer.add_string buf "\\0"
    | '\r' -> Buffer.add_string buf "\\r"
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf
;;

(* Collects type namespace names that need 'open' in the auxiliary file *)
let lean_auxiliary_opens : string list ref = ref []
(* Tracks current namespace nesting for qualified open names *)
let lean_namespace_stack : string list ref = ref []

let lean_qualified_name name_str =
  match !lean_namespace_stack with
    | [] -> name_str
    | ns -> String.concat "." (List.rev ns @ [name_str])

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

let from_string x = meta_utf8 x
let sep x s = ws s ^ x
let path_sep = r"."

(* Lean 4 is whitespace-sensitive, so disable auto-formatting blocks
   which can break indentation of match alternatives *)
let block _ _ t = t
let block_hov _ _ t = t

let flatten_newlines = Output.flatten_newlines

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


let fresh_name_counter = ref 0

let generate_fresh_name () =
  let n = !fresh_name_counter in
  fresh_name_counter := n + 1;
  Stdlib.(^) "x" (string_of_int n)

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
            let name_out = Name.to_output Term_var name in
            let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
            match lemma_typ with
            | Ast.Lemma_assert _ ->
              Output.flat [
                ws skips;
                from_string "#eval do\n";
                from_string ("  if ("); exp inside_instance e; from_string (" : Bool)\n");
                from_string (String.concat "" ["  then IO.println \"PASS: "; lean_string_escape name_str; "\"\n"]);
                from_string (String.concat "" ["  else throw (IO.userError \"FAIL: "; lean_string_escape name_str; "\")"])
              ]
            | Ast.Lemma_lemma _ | Ast.Lemma_theorem _ ->
              Output.flat [
                ws skips; from_string "theorem "; name_out; ws skips'; from_string " : ";
                from_string "("; exp inside_instance e; from_string " : Prop) ";
                from_string ":= by decide"
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
          let defaults =
            if Seplist.length def > 1 then
              generate_default_values_mutual def
            else
              generate_default_values def
          in
            Output.flat [
              ws skips; funcl def;
              defaults;
            ]
      | Val_def (def) ->
          let class_constraints = val_def_get_class_constraints A.env def in
          let tv_set = val_def_get_free_tnvars A.env def in
          val_def false None (snd (Typed_ast_syntax.is_recursive_def m)) def tv_set class_constraints
      | Module (skips, (name, l), mod_binding, skips', skips'', defs, skips''') ->
        let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
        lean_namespace_stack := name_str :: !lean_namespace_stack;
        let name = lskips_t_to_output name in
        let body = callback defs in
        lean_namespace_stack := (match !lean_namespace_stack with _ :: tl -> tl | [] -> []);
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
          let strip_lemlib_prefix s =
            let prefix = "LemLib." in
            let plen = String.length prefix in
            if String.length s >= plen && String.sub s 0 plen = prefix then
              String.sub s plen (String.length s - plen)
            else s
          in
          let handle_mod (sk, md) = begin
            let open_name = strip_lemlib_prefix md in
            Output.flat [
              from_string "import"; ws sk; from_string md; from_string "\n"
            ; from_string "open"; ws sk; from_string open_name; from_string "\n"
            ]
          end in
          if (not (in_target targets)) then emp else Output.flat (List.map handle_mod mod_descrs)
      | OpenImportTarget _ -> emp
      | Indreln (skips, targets, names, cs) ->
          if in_target targets then
            let c = Seplist.to_list cs in
              clauses inside_instance c
          else
            ws skips ^ from_string "\n/- removed inductive relation intended for another target -/"
      | Val_spec val_spec -> from_string "\n/- removed value specification -/\n"
      | Class (Ast.Class_inline_decl (skips, _), _, _, _, _,_, _, _) -> ws skips
      | Class (Ast.Class_decl skips, skips', (name, l), tv, p, skips'', body, skips''') ->
          let name_str = Name.to_string (B.class_path_to_name p) in
          lean_auxiliary_opens := lean_qualified_name name_str :: !lean_auxiliary_opens;
          let name = from_string name_str in
          let tv_kind =
            match tv with
              | Typed_ast.Tn_A _ -> "Type"
              | Typed_ast.Tn_N _ -> "Nat"
          in
          let tv =
            begin
              match tv with
                | Typed_ast.Tn_A (_, tyvar, _) ->
                    from_string @@ Ulib.Text.to_string tyvar
                | Typed_ast.Tn_N (_, nvar, _) ->
                    from_string @@ Ulib.Text.to_string nvar
            end
          in
          let body_entries =
            List.filter_map (fun (skips, targets_opt, (name, l), const_descr_ref, ascii_rep_opt, skips', src_t) ->
              if in_target targets_opt then
                let name' = B.const_ref_to_name name true const_descr_ref in
                let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name')) in
                  Some (Output.flat [
                    ws skips; from_string name_str; from_string " :"; ws skips'; pat_typ src_t
                  ])
              else
                None
            ) body
          in
          let body_out = Output.concat (from_string "\n") body_entries in
          Output.flat [
            ws skips; from_string "class"; ws skips'; name; from_string " ("; tv; from_string " : "; from_string tv_kind; from_string ") where"
          ; ws skips''; from_string "\n"; body_out
          ; ws skips'''; from_string "\nopen "; name; from_string "\n"
          ]
      | Instance (Ast.Inst_default skips, i_ref, inst, vals, skips') -> emp
      | Instance (Ast.Inst_decl skips, i_ref, inst, vals, skips') ->
        (* Filter out instance methods whose corresponding class methods
           are not visible for the Lean target *)
        let instance_info = Types.i_env_lookup Ast.Unknown A.env.i_env i_ref in
        let class_method_visible (inst_cd_ref : Types.const_descr_ref) : bool =
          let found = List.filter (fun (_, inst_ref) -> inst_ref = inst_cd_ref) instance_info.inst_methods in
          match found with
          | (class_ref, _) :: _ ->
            let class_cd = c_env_lookup Ast.Unknown A.env.c_env class_ref in
            Typed_ast.in_target_set (Target.Target_no_ident Target.Target_lean) class_cd.const_targets
          | [] -> true
        in
        let val_is_visible (d : Typed_ast.val_def) : bool =
          match d with
          | Let_def (_, _, (_, name_map, _, _, _)) ->
            List.for_all (fun (_, cd_ref) -> class_method_visible cd_ref) name_map
          | Fun_def (_, _, _, funcl_sep) ->
            Seplist.for_all (fun ({term = _}, c, _, _, _, _) -> class_method_visible c) funcl_sep
          | _ -> true
        in
        let vals = List.filter val_is_visible vals in
        let l_unk = Ast.Unknown in
          let prefix =
            match inst with
              | (constraint_prefix_opt, skips, ident, path, src_t, skips') ->
                let tnvar_list_opt, tyvars, c =
                  begin
                  match constraint_prefix_opt with
                    | None -> None, emp, emp
                    | Some c ->
                      begin
                      match c with
                        | Cp_forall (skips, tnvar_list, skips', constraints_opt) ->
                            let tnvars =
                              Output.concat (from_string " ") (List.map (fun t ->
                                match t with
                                  | Typed_ast.Tn_A (_, var, _) ->
                                      from_string @@ Ulib.Text.to_string var
                                  | Typed_ast.Tn_N (_, var, _) ->
                                      from_string @@ Ulib.Text.to_string var
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
                                              | Typed_ast.Tn_N (_, var, _) ->
                                                  from_string @@ Ulib.Text.to_string var
                                          in
                                          let (ns, n) = Ident.to_name_list id in
                                          let class_name = B.class_path_to_name (Path.mk_path ns n) in
                                          let ident = from_string (Name.to_string class_name) in
                                            Output.flat [
                                              from_string "["; ident; from_string " "; var; from_string "]"
                                            ]) ident_var_list)
                                      in
                                        ident_var_list
                              end
                            in
                              Some tnvar_list, tnvars, cs
                      end
                  end
                in
                let id = from_string (Name.to_string (B.class_path_to_name path)) in
                let tyvars_typeset =
                  if tyvars = emp then
                    emp
                  else
                    match tnvar_list_opt with
                    | Some tnvar_list ->
                      let has_nvar = List.exists (fun t ->
                        match t with Typed_ast.Tn_N _ -> true | _ -> false) tnvar_list in
                      if has_nvar then
                        Output.concat (from_string " ") (List.map (fun t ->
                          match t with
                            | Typed_ast.Tn_A (_, var, _) ->
                              Output.flat [from_string "("; from_string @@ Ulib.Text.to_string var; from_string " : Type)"]
                            | Typed_ast.Tn_N (_, var, _) ->
                              Output.flat [from_string "("; from_string @@ Ulib.Text.to_string var; from_string " : Nat)"]
                        ) tnvar_list)
                      else
                        Output.flat [
                          from_string "("; tyvars; from_string " : Type)"
                        ]
                    | None ->
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
              let name = from_string (Name.to_string (B.class_path_to_name path)) in
              let var = from_string @@ Ulib.Text.to_string @@ Types.tnvar_to_rope tnvar
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
                let funcls = Seplist.to_list funcl_skips_seplist in
                (* Group clauses by function name *)
                let get_name ({term = n}, _, _, _, _, _) = Name.to_string (Name.strip_lskip n) in
                let groups =
                  let order = ref [] in
                  let tbl = Hashtbl.create 8 in
                  List.iter (fun fcl ->
                    let key = get_name fcl in
                    (if not (Hashtbl.mem tbl key) then
                      order := key :: !order);
                    let existing = try Hashtbl.find tbl key with Not_found -> [] in
                    Hashtbl.replace tbl key (existing @ [fcl])
                  ) funcls;
                  List.map (fun key -> Hashtbl.find tbl key) (List.rev !order)
                in
                let num_functions = List.length groups in
                let is_truly_mutual = num_functions > 1 in
                let def_keyword =
                  if is_recursive then
                    if inside_instance then emp
                    else from_string "partial def"
                  else
                    if inside_instance then emp
                    else from_string "def"
                in
                let render_group group =
                  match group with
                  | [] -> emp
                  | [single_clause] ->
                    (* Single clause: render as before *)
                    funcl inside_instance i_ref_opt constraints tv_set single_clause
                  | first_clause :: rest_clauses ->
                    (* Multi-clause: use Lean 4 equation compiler syntax *)
                    let ({term = n}, c, pats, typ_opt, _skips, _e) = first_clause in
                    let name_skips = Name.get_lskip n in
                    let name = from_string (Name.to_string (Name.strip_lskip n)) in
                    (* Get the full type from the const_descr *)
                    let cd = c_env_lookup Ast.Unknown A.env.c_env c in
                    let full_type = pat_typ (C.t_to_src_t cd.const_type) in
                    let tv_set_out =
                      if inside_instance then emp
                      else
                        let tv = Types.free_vars cd.const_type in
                        if Types.TNset.cardinal tv = 0 then emp
                        else Output.flat [from_string " "; let_type_variables true tv]
                    in
                    let constraints_sep =
                      if constraints = emp then emp else from_string " "
                    in
                    (* Render each clause as | pat1, pat2, ... => body *)
                    let render_equation ({term = _}, _, pats, _, skips, e) =
                      let pat_out = concat_str ", " (List.map def_pattern pats) in
                      Output.flat [
                        from_string "\n  | "; pat_out; from_string " =>"; ws skips; from_string " "; exp inside_instance e
                      ]
                    in
                    let equations = Output.flat (List.map render_equation (first_clause :: rest_clauses)) in
                    Output.flat [
                      ws name_skips; from_string " "; name; tv_set_out; constraints_sep; constraints;
                      from_string " : "; full_type; equations
                    ]
                in
                let bodies = List.map render_group groups in
                let rec_skips =
                  if is_recursive && not inside_instance then
                    ws (match skips' with Some s -> Some s | None -> None)
                  else emp
                in
                if is_truly_mutual then
                  Output.flat [
                    ws skips; from_string "mutual\n"; rec_skips;
                    concat_str "\n" (List.map (fun b -> Output.flat [def_keyword; b]) bodies);
                    from_string "\nend"
                  ]
                else
                  Output.flat [
                    ws skips; rec_skips; def_keyword; Output.flat bodies
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
                                      from_string ")" ]) ants);
                        from_string " → "
                      ]
              in
              let bound_variables =
                concat_str " " @@ List.map (fun b ->
                  match b with
                    | QName n -> from_string (Name.to_string (Name.strip_lskip n.term))
                    | _ -> raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected binding form in indreln quantifier")
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
                    | _ -> raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: instance method not found for class method")
              end
        else
          B.const_ref_to_name n true c
      in
        funcl_aux inside_instance i_ref_opt constraints tv_set (n, pats, typ_opt, skips, e)
    and let_type_variables top_level tv_set =
      if Types.TNset.is_empty tv_set || not top_level then
        emp
      else
      let bindings =
        List.map (fun tv -> match tv with
          | Types.Ty tv ->
            Output.flat [from_string "{"; id Type_var (Tyvar.to_rope tv); from_string " : Type}"]
          | Types.Nv nv ->
            Output.flat [from_string "{"; id Type_var (Nvar.to_rope nv); from_string " : Nat}"])
        (Types.TNset.elements tv_set)
      in
        if List.length bindings = 0 || not top_level then
          emp
        else
          from_string " " ^ concat_str " " bindings
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
          | Do (skips, _mod_descr_id, do_line_list, _skips', e, _skips'', _type_int) ->
              let lines = List.map (fun (Do_line (p, _s1, body, _s2)) ->
                let (body', _) = Typed_ast.alter_init_lskips (fun sk -> (Typed_ast.no_lskips, sk)) body in
                Output.flat [
                  from_string "    let "; fun_pattern p; from_string " ← "; exp inside_instance body'; from_string "\n"
                ]
              ) do_line_list in
              let (e', _) = Typed_ast.alter_init_lskips (fun sk -> (Typed_ast.no_lskips, sk)) e in
              Output.flat [
                ws skips; from_string "(do\n";
                concat emp lines;
                from_string "    "; exp inside_instance e'; from_string "\n";
                from_string "  )"
              ]
          | App (e1, e2) ->
              let trans e = exp inside_instance e in
              let sep = from_string " " in
              let oL = begin
              let (e0, args) = strip_app_exp e in
                match C.exp_to_term e0 with
                  | Constant cd ->
                    B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd.descr)
                  | _ ->
                    List.map trans (e0 :: args)
              end in
              Output.concat sep oL
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
                  ws skips; from_string "let "; body; ws skips'; from_string "\n"; exp inside_instance e
                ]
          | Constant const ->
              Output.concat emp (B.function_application_to_output (exp_to_locn e) (exp inside_instance) false e const [] (use_ascii_rep_for_const const.descr))
          | Fun (skips, ps, skips', e) ->
              let ps = fun_pattern_list inside_instance ps in
                block_hov (Typed_ast_syntax.is_pp_exp e) 2 (
                  Output.flat [
                    ws skips; from_string "fun"; ps; ws skips'; from_string "=> "; exp inside_instance e
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
                    skips; from_string "(setEmpty)"
                  ]
                else
                  Output.flat [
                    skips; from_string "(setFromList ["; body; from_string "])"; ws skips'
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
            let case_sep _ = from_string " " in
            let has_vec = Seplist.exists (fun (p, _, _, _) -> pat_has_vector p) cases in
            let body = flat @@ Seplist.to_sep_list_last Seplist.Optional (case_line inside_instance) case_sep cases in
            let match_suffix = if has_vec then from_string ".toList" else emp in
                Output.flat [
                  ws skips; from_string "match "; exp inside_instance e; match_suffix; from_string " with "; body; ws skips''
                ]
          | Infix (l, c, r) ->
              let trans e = exp inside_instance e in
              let sep = from_string " " in
              begin
                match C.exp_to_term c with
                  | Constant cd ->
                    begin
                      let pieces = B.function_application_to_output (exp_to_locn e) trans true e cd [l; r] (use_ascii_rep_for_const cd.descr) in
                      Output.concat sep pieces
                    end
                  | _           ->
                    begin
                      let mapped = List.map trans [l; c; r] in
                      Output.concat sep mapped
                    end
              end
          | If (skips, test, skips', t, skips'', f) ->
              Output.flat [
                ws skips; from_string "if";
                from_string " "; exp inside_instance test;
                ws skips'; from_string "then"; from_string " ";
                exp inside_instance t;
                ws skips''; from_string " else "; exp inside_instance f
              ]
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
                quant; from_string " "; bindings; from_string ", ("; ws skips;
                exp inside_instance e; from_string " : Prop)"
              ]
          | Comp_binding _ -> from_string "/- comp binding -/"
          | Setcomp _ -> from_string "/- set comprehension -/"
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
                ws skips'; src_nexp nexp'; ws skips''
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
    and pat_has_vector (p : pat) : bool =
      match p.term with
        | P_vector _ | P_vectorC _ -> true
        | P_paren (_, p, _) | P_typ (_, p, _, _, _) | P_as (_, p, _, _, _) -> pat_has_vector p
        | P_tup (_, ps, _) | P_list (_, ps, _) -> Seplist.exists pat_has_vector ps
        | P_cons (p1, _, p2) -> pat_has_vector p1 || pat_has_vector p2
        | P_const (_, ps) -> List.exists pat_has_vector ps
        | _ -> false
    and case_line inside_instance (p, skips, e, _) =
        flatten_newlines (Output.flat [
          from_string "| "; def_pattern p; from_string " => "; exp inside_instance e
        ])
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
            let escaped = lean_string_escape s in
            ws skips ^ from_string (String.concat "" ["\""; escaped; "\""])
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
        | L_vector (s, prefix, bits) ->
            Output.flat [
              ws s; from_string (String.concat "" [prefix; bits])
            ]
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
              ws skips; name; from_string "@("; fun_pattern p; from_string ")"; ws skips''
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
              from_string "("; def_pattern p1; ws skips; from_string " :: "; def_pattern p2; from_string ")"
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
        | P_vector (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional fun_pattern (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_vectorC _ ->
            raise (Reporting_basic.err_general true p.locn
              "Lean backend: vector concatenation patterns are not supported")
        | P_paren (skips, p, skips') ->
            Output.flat [
              ws skips; from_string "("; fun_pattern p; ws skips'; from_string ")"
            ]
        | P_const(cd, ps) ->
            let oL = B.pattern_application_to_output p.locn fun_pattern cd ps (use_ascii_rep_for_const cd.descr) in
            concat (from_string " ") oL
        | P_backend(sk, i, _, ps) ->
            ws sk ^
            Ident.to_output (Term_const (false, true)) path_sep (Ident.replace_lskip i Typed_ast.no_lskips) ^
            concat (from_string " ") (List.map fun_pattern ps)
        | P_num_add ((name, l), skips, skips', k) ->
            let name = lskips_t_to_output name in
              Output.flat [
                ws skips; from_string "("; name; from_string " + "; from_string (Z.to_string k); from_string ")"
              ]
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
              ws skips; name; from_string "@("; def_pattern p; from_string ")"; ws skips''
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
        | P_vector (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional def_pattern (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_vectorC _ ->
            raise (Reporting_basic.err_general true p.locn
              "Lean backend: vector concatenation patterns are not supported")
        | P_paren (skips, p, skips') ->
            Output.flat [
              from_string "("; ws skips; def_pattern p; ws skips'; from_string ")"
            ]
        | P_const(cd, ps) ->
            let oL = B.pattern_application_to_output p.locn def_pattern cd ps (use_ascii_rep_for_const cd.descr) in
            concat (from_string " ") oL
        | P_backend(sk, i, _, ps) ->
            ws sk ^
            Ident.to_output (Term_const (false, true)) path_sep (Ident.replace_lskip i Typed_ast.no_lskips) ^
            concat (from_string " ") (List.map def_pattern ps)
        | P_num_add ((name, l), skips, skips', k) ->
            let name = lskips_t_to_output name in
              Output.flat [
                ws skips; from_string "("; name; from_string " + "; from_string (Z.to_string k); from_string ")"
              ]
    and src_t_has_fn (t : src_t) : bool =
      match t.term with
        | Typ_fn _ -> true
        | Typ_tup ts -> Seplist.exists src_t_has_fn ts
        | Typ_app (_, ts) -> List.exists src_t_has_fn ts
        | Typ_paren (_, t, _) -> src_t_has_fn t
        | Typ_with_sort (t, _) -> src_t_has_fn t
        | _ -> false
    and texp_can_derive_beq (t : texp) : bool =
      match t with
        | Te_variant (_, ctors) ->
          not (Seplist.exists (fun (_, _, _, args) ->
            Seplist.exists src_t_has_fn args
          ) ctors)
        | Te_record (_, _, fields, _) ->
          not (Seplist.exists (fun (_, _, _, src_t) -> src_t_has_fn src_t) fields)
        | _ -> false
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
        | _ -> raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected type definition form")
    and type_def_record def =
      match Seplist.hd def with
        | (n, tyvars, path, (Te_record (skips, skips', fields, skips'')),_) ->
            let (n', _) = n in
            let n' = B.type_path_to_name n' path in
            let name = Name.to_output (Type_ctor (false, false)) n' in
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) field (sep @@ from_string "\n") fields in
            let tyvars' = type_def_type_variables tyvars in
            let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
            let deriving =
              if texp_can_derive_beq (Te_record (skips, skips', fields, skips'')) then
                from_string "\n  deriving BEq"
              else emp
            in
              Output.flat [
                from_string "structure"; name; tyvar_sep; tyvars';
                ws skips; from_string " where"; ws skips';
                from_string "\n"; body; ws skips''; deriving; from_string "\n";
              ]
        | _ -> raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected type definition form")
    and type_def inside_module defs =
      (* Collect type names for "open" declarations *)
      let type_names = Seplist.to_list_map (fun ((n0, _), _, t_path, _, _) ->
        let n = B.type_path_to_name n0 t_path in
        Name.to_string (Name.strip_lskip n)
      ) defs in
      (* Also register these for the auxiliary file (with namespace qualification) *)
      lean_auxiliary_opens := !lean_auxiliary_opens @ List.map lean_qualified_name type_names;
      let open_decls = flat (List.map (fun name_str ->
        from_string (String.concat "" ["\nopen "; name_str])
      ) type_names) in
      let n = Seplist.length defs in
      if n > 1 then
        (* Check if all types in mutual block have the same number of type params *)
        let param_counts = Seplist.to_list_map (fun (_, ty_vars, _, _, _) ->
          List.length ty_vars
        ) defs in
        let all_same = match param_counts with
          | [] -> true
          | x :: xs -> List.for_all (fun y -> y = x) xs
        in
        if all_same then
          let body = flat @@ Seplist.to_sep_list (type_def_variant false) (sep @@ from_string "\ninductive") defs in
          Output.flat [ from_string "mutual\ninductive"; body; from_string "\nend"; open_decls; from_string "\n" ]
        else
          (* Heterogeneous params: use indices instead of params for Lean 4 compatibility *)
          let body = flat @@ Seplist.to_sep_list type_def_indexed (sep @@ from_string "\ninductive") defs in
          Output.flat [ from_string "mutual\ninductive"; body; from_string "\nend"; open_decls; from_string "\n" ]
      else
        let body = flat @@ Seplist.to_sep_list (type_def_variant true) (sep @@ from_string "\n") defs in
        Output.flat [ from_string "inductive"; body; open_decls; from_string "\n" ]
    and type_def_variant emit_deriving ((n0, l), ty_vars, t_path, ty, _) =
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
              inductive ty_vars n; tyexp emit_deriving name ty_vars ty
            ]
    and type_def_indexed ((n0, l), ty_vars, t_path, ty, _) =
      (* Emit type with indices instead of parameters, for heterogeneous mutual blocks.
         Parameters become indices: inductive v : (a : Type) → (b : Type) → Type 1 where *)
      let n = B.type_path_to_name n0 t_path in
      let name = Name.to_output (Type_ctor (false, false)) n in
      let ty_vars_list =
        List.map (
          function
            | Typed_ast.Tn_A (_, tyvar, _) -> Tyvar (from_string @@ Ulib.Text.to_string tyvar)
            | Typed_ast.Tn_N (_, nvar, _) -> Nvar (from_string @@ Ulib.Text.to_string nvar)
          ) ty_vars
      in
      let indices =
        if List.length ty_vars_list = 0 then emp
        else
          let mapped = List.map (fun v ->
            match v with
              | Tyvar x -> Output.flat [ from_string "("; x; from_string " : Type) → " ]
              | Nvar x -> Output.flat [ from_string "("; x; from_string " : Nat) → " ]
          ) ty_vars_list in
          concat emp mapped
      in
      let universe = if List.length ty_vars_list > 0 then from_string "Type 1" else from_string "Type" in
      let ty_vars_names =
        concat_str " " @@ List.map (fun v ->
          match v with
            | Tyvar out -> out
            | Nvar out -> out
        ) ty_vars_list
      in
      let ty_vars_names_space = if List.length ty_vars_list = 0 then emp else from_string " " in
      match ty with
        | Te_variant (skips, ctors) ->
          let body = flat @@ Seplist.to_sep_list_first Seplist.Optional
            (constructor_indexed name ty_vars_list ty_vars_names ty_vars_names_space) (sep @@ from_string "\n") ctors in
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where";
            ws skips; from_string "\n"; body
          ]
        | Te_opaque ->
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where"
          ]
        | _ ->
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where"
          ]
    and constructor_indexed ind_name (ty_vars : variable list) ty_vars_names ty_vars_names_space ((name0, _), c_ref, skips, args) =
      let ctor_name = B.const_ref_to_name name0 false c_ref in
      let ctor_name = Name.to_output (Type_ctor (false, false)) ctor_name in
      let body = flat @@ Seplist.to_sep_list pat_typ (sep @@ from_string " → ") args in
      (* For indexed inductives, constructors must bind all type variables implicitly *)
      let implicit_bindings =
        if List.length ty_vars = 0 then emp
        else
          let mapped = List.map (fun v ->
            match v with
              | Tyvar x -> Output.flat [ from_string "{"; x; from_string " : Type} → " ]
              | Nvar x -> Output.flat [ from_string "{"; x; from_string " : Nat} → " ]
          ) ty_vars in
          concat emp mapped
      in
      let tail =
        Output.flat [
          from_string " → "; ind_name; ty_vars_names_space; ty_vars_names
        ]
      in
        if Seplist.length args = 0 then
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; implicit_bindings; ind_name
          ; ty_vars_names_space; ty_vars_names
          ]
        else
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; implicit_bindings; body; tail
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
    and tyexp emit_deriving name ty_vars =
      function
        | Te_opaque -> emp
        | Te_abbrev (skips, t) -> ws skips ^ from_string " := " ^ pat_typ t
        | Te_record (skips, _, fields, skips') -> ws skips ^ from_string " where\n" ^ tyexp_record fields ^ ws skips'
        | Te_variant (skips, ctors) ->
          let body = flat @@ Seplist.to_sep_list_first Seplist.Optional (constructor name ty_vars) (sep @@ from_string "\n") ctors in
          let deriving =
            if emit_deriving && texp_can_derive_beq (Te_variant (skips, ctors)) then
              from_string "\n  deriving BEq"
            else emp
          in
            Output.flat [
              from_string " where"; ws skips; from_string "\n"; body; deriving
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
            if Path.compare p.descr Path.unitpath = 0 then
              let sk = Typed_ast.ident_get_lskip p in
              Output.flat [ ws sk; from_string "Unit" ]
            else
            let (ts_list, head) = B.type_app_to_output pat_typ p ts in
            let ts_out = concat_str " " @@ List.map pat_typ ts_list in
            let space = if ts_list = [] then emp else from_string " " in
              Output.flat [
                head; space; ts_out
              ]
        | Typ_paren(skips, t, skips') ->
            ws skips ^ from_string "(" ^ pat_typ t ^ ws skips' ^ from_string ")"
        | Typ_with_sort(t,_) -> raise (Reporting_basic.err_general true t.locn "Lean backend: target sort annotations are not supported")
        | Typ_len nexp -> src_nexp nexp
        | Typ_backend (p, ts) ->
          let i = Path.to_ident (ident_get_lskip p) p.descr in
          let i = Ident.to_output (Type_ctor (false, true)) path_sep i in
          let ts_out = List.map pat_typ ts in
          let space = if ts_out = [] then emp else from_string " " in
            Output.flat [
              i; space; concat emp ts_out
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
            if Path.compare p.descr Path.unitpath = 0 then
              let sk = Typed_ast.ident_get_lskip p in
              Output.flat [ ws sk; from_string "Unit" ]
            else
              let args = concat_str " " @@ List.map typ ts in
              let args_space = if ts <> [] then from_string " " else emp in
              Output.flat [ typ_ident_to_output p; args_space; args ]
        | Typ_paren (skips, t, skips') ->
            ws skips ^ from_string "(" ^ typ t ^ from_string ")" ^ ws skips'
        | Typ_with_sort (t, sort) -> raise (Reporting_basic.err_general true t.locn "Lean backend: target sort annotations are not supported")
        | Typ_len nexp -> src_nexp nexp
        | Typ_backend (p, ts) ->
          let i = Path.to_ident (ident_get_lskip p) p.descr in
          let i = Ident.to_output (Type_ctor (false, true)) path_sep i in
          let ts_out = List.map typ ts in
          let space = if ts_out = [] then emp else from_string " " in
            Output.flat [
              i; space; concat emp ts_out
            ]
        | _ -> raise (Reporting_basic.err_general true t.locn "Lean backend: unexpected type form in typ")
    and type_def_type_variables tvs =
      match tvs with
        | [] -> emp
        | [Typed_ast.Tn_A tv] -> from_string "(" ^ tyvar tv ^ from_string " : Type)"
        | tvs ->
          let mapped = List.map (fun t ->
            match t with
              | Typed_ast.Tn_A (_, tv_name, _) ->
                let tv_out = from_string @@ Ulib.Text.to_string tv_name in
                  Output.flat [
                    from_string "("; tv_out; from_string " : Type)"
                  ]
              | Typed_ast.Tn_N (_, nv_name, _) ->
                let nv_out = from_string @@ Ulib.Text.to_string nv_name in
                  Output.flat [
                    from_string "("; nv_out; from_string " : Nat)"
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
          let args_space = if ts <> [] then from_string " " else emp in
            Output.flat [
              typ_ident_to_output p; args_space; args
            ]
        | Typ_paren(skips, t, skips') ->
            ws skips ^ from_string "(" ^ indreln_typ t ^ from_string ")" ^ ws skips'
        | Typ_with_sort(t, _) -> indreln_typ t
        | Typ_len nexp -> src_nexp nexp
        | Typ_backend (p, ts) ->
          let i = Path.to_ident (ident_get_lskip p) p.descr in
          let i = Ident.to_output (Type_ctor (false, true)) path_sep i in
          let ts_out = List.map indreln_typ ts in
          let space = if ts_out = [] then emp else from_string " " in
            Output.flat [
              i; space; concat emp ts_out
            ]
        | _ -> raise (Reporting_basic.err_general true t.locn "Lean backend: unexpected type form in indreln_typ")
    and field ((n, _), f_ref, skips, t) =
      Output.flat [
          from_string "  ";
          Name.to_output Term_field (B.const_ref_to_name n false f_ref);
          ws skips; from_string " :"; pat_typ t
      ]
    and default_type_variables tvs =
      match tvs with
        | [] -> emp
        | [Typed_ast.Tn_A tv] ->
            Output.flat [
              from_string " {"; tyvar tv; from_string " : Type}";
              from_string " [Inhabited "; tyvar tv; from_string "]"
            ]
        | tvs ->
          let mapped = List.map (fun t ->
            match t with
              | Typed_ast.Tn_A (_, tv_name, _) ->
                let tv_out = from_string @@ Ulib.Text.to_string tv_name in
                  Output.flat [
                    from_string " {"; tv_out; from_string " : Type}";
                    from_string " [Inhabited "; tv_out; from_string "]"
                  ]
              | Typed_ast.Tn_N (_, nv_name, _) ->
                let nv_out = from_string @@ Ulib.Text.to_string nv_name in
                  Output.flat [
                    from_string " {"; nv_out; from_string " : Nat}"
                  ]) tvs
          in
            concat emp mapped
    (* Check if a source type references any of the given paths (mutual type detection) *)
    and src_t_references_paths mutual_paths (s : src_t) : bool =
      match s.term with
        | Typ_wild _ | Typ_var _ | Typ_len _ -> false
        | Typ_tup seplist ->
            List.exists (src_t_references_paths mutual_paths) (Seplist.to_list seplist)
        | Typ_app (p, ts) ->
            List.exists (fun mp -> Path.compare mp p.descr = 0) mutual_paths ||
            List.exists (src_t_references_paths mutual_paths) ts
        | Typ_paren (_, inner, _) | Typ_with_sort (inner, _) ->
            src_t_references_paths mutual_paths inner
        | Typ_fn (dom, _, rng) ->
            src_t_references_paths mutual_paths dom || src_t_references_paths mutual_paths rng
        | Typ_backend (_, ts) ->
            List.exists (src_t_references_paths mutual_paths) ts
        | _ -> true
    (* Default value for a source type in Inhabited instance context.
       Uses [default] for type variables since [Inhabited] constraints are in scope. *)
    and default_value_inhabited (s : src_t) : Output.t =
      match s.term with
        | Typ_wild _ -> from_string "default"
        | Typ_var _ -> from_string "default"
        | Typ_len _ -> from_string "0"
        | Typ_tup seplist ->
            let src_ts = Seplist.to_list seplist in
            let mapped = List.map default_value_inhabited src_ts in
              Output.flat [
                from_string "("; concat_str ", " mapped; from_string ")"
              ]
        | Typ_app _ -> from_string "default"
        | Typ_paren (_, src_t, _)
        | Typ_with_sort (src_t, _) -> default_value_inhabited src_t
        | Typ_fn (dom, _, rng) ->
            let v = generate_fresh_name () in
              Output.flat [
                from_string "(fun ("; from_string v; from_string " : "; pat_typ dom;
                from_string ") => "; default_value_inhabited rng; from_string ")"
              ]
        | Typ_backend _ -> from_string "default"
        | _ -> from_string "sorry /- unexpected type form -/"
    and generate_default_value_texp (t: texp) =
      match t with
        | Te_opaque -> from_string "sorry /- DAEMON -/"
        | Te_abbrev (_, src_t) -> default_value_inhabited src_t
        | Te_record (_, _, seplist, _) ->
            let fields = Seplist.to_list seplist in
            let mapped = List.map (fun ((name, _), const_descr_ref, _, src_t) ->
              let name = B.const_ref_to_name name true const_descr_ref in
              let o = lskips_t_to_output name in
              let s = default_value_inhabited src_t in
                Output.flat [
                  o; from_string " := "; s
                ]
              ) fields
            in
            let fields = concat_str ", " mapped in
              Output.flat [
                from_string "{ "; fields; from_string " }"
              ]
        | Te_variant (_, seplist) ->
            (match Seplist.to_list seplist with
              | [] -> raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: empty variant in Inhabited instance generation")
              | x::_xs ->
                let ((name, _l), const_descr_ref, _, src_ts) = x in
                  let name = B.const_ref_to_name name false const_descr_ref in
                  let ys = Seplist.to_list src_ts in
                  let mapped = List.map default_value_inhabited ys in
                  let sep = if List.length mapped = 0 then emp else from_string " " in
                  let mapped = concat_str " " mapped in
                  let o = lskips_t_to_output name in
                    Output.flat [
                      o; sep; mapped
                    ])
    (* Render a constructor call for an Inhabited default value *)
    and render_ctor_default ((ctor_name, _), ctor_ref, _, src_ts) =
      let n = B.const_ref_to_name ctor_name false ctor_ref in
      let ys = Seplist.to_list src_ts in
      let mapped = List.map default_value_inhabited ys in
      let sep = if List.length mapped = 0 then emp else from_string " " in
      let mapped_out = concat_str " " mapped in
      let o = lskips_t_to_output n in
        Output.flat [o; sep; mapped_out]
    (* For mutual types, find a constructor whose args don't reference any mutual types.
       Prefers nullary constructors, then constructors with non-mutual args. *)
    and find_safe_ctor_for_mutual mutual_paths ctors =
      let nullary = List.find_opt (fun (_, _, _, src_ts) ->
        Seplist.to_list src_ts = []
      ) ctors in
      match nullary with
        | Some _ -> nullary
        | None ->
          List.find_opt (fun (_, _, _, src_ts) ->
            let args = Seplist.to_list src_ts in
            not (List.exists (src_t_references_paths mutual_paths) args)
          ) ctors
    and generate_inhabited_instance mutual_paths ((name, _), tnvar_list, path, t, _name_sect_opt) : Output.t =
      let name = B.type_path_to_name name path in
      let o = lskips_t_to_output name in
      let tnvar_list' = default_type_variables tnvar_list in
      let default =
        match t with
          | Te_variant (_, seplist) ->
            let ctors = Seplist.to_list seplist in
            (match find_safe_ctor_for_mutual mutual_paths ctors with
              | Some ctor -> render_ctor_default ctor
              | None -> from_string "sorry /- mutual type -/")
          | _ -> generate_default_value_texp t
      in
      let tnvar_names = concat_str " " @@ List.map (fun x ->
        match x with
          | Typed_ast.Tn_A (_, tv_name, _) -> from_string (Ulib.Text.to_string tv_name)
          | Typed_ast.Tn_N (_, nv_name, _) -> from_string (Ulib.Text.to_string nv_name)
        ) tnvar_list
      in
      let type_args =
        if List.length tnvar_list = 0 then emp
        else Output.flat [from_string " "; tnvar_names]
      in
        Output.flat [
          from_string "instance"; tnvar_list'; from_string " : Inhabited ("; o;
          type_args;
          from_string ") where\n  default := "; default;
        ]
    and generate_default_values ts : Output.t =
      let ts = Seplist.to_list ts in
      (* Treat each single type like a mutual block of one, so self-referential
         constructors (e.g. Unop : op → op0 → op1 → op1) are detected and
         avoided when generating the Inhabited instance. *)
      let mapped = List.map (fun (((_, _), _, path, _, _) as t) ->
        generate_inhabited_instance [path] t) ts in
        concat_str "\n" mapped
    and generate_default_values_mutual ts : Output.t =
      let ts_list = Seplist.to_list ts in
      let mutual_paths = List.map (fun ((_, _), _, path, _, _) -> path) ts_list in
      let mapped = List.map (generate_inhabited_instance mutual_paths) ts_list in
        concat_str "\n" mapped
    (* Default value for L_undefined (DAEMON) context — uses sorry for type variables
       since Inhabited constraints may not be available *)
    and default_value (s : src_t) : Output.t =
      match s.term with
        | Typ_wild _ -> from_string "default"
        | Typ_var _ -> from_string "sorry /- default for type variable -/"
        | Typ_len _ -> from_string "0"
        | Typ_tup seplist ->
            let src_ts = Seplist.to_list seplist in
            let mapped = List.map default_value src_ts in
              Output.flat [
                from_string "("; concat_str ", " mapped; from_string ")"
              ]
        | Typ_app _ -> from_string "default"
        | Typ_paren (_, src_t, _)
        | Typ_with_sort (src_t, _) -> default_value src_t
        | Typ_fn (dom, _, rng) ->
            let v = generate_fresh_name () in
              Output.flat [
                from_string "(fun ("; from_string v; from_string " : "; pat_typ dom;
                from_string ") => "; default_value rng; from_string ")"
              ]
        | Typ_backend _ -> from_string "default"
        | _ -> from_string "sorry /- unexpected type form -/"
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
      lean_auxiliary_opens := [];
      lean_namespace_stack := [];
      let lean_defs = defs false false ds in
      let lean_defs_extra = defs_extra false false ds in
      (* Emit open statements for type/class namespaces so auxiliary file
         can reference constructors and class methods unqualified *)
      let opens = List.map (fun name_str ->
        from_string (String.concat "" ["open "; name_str; "\n"])
      ) !lean_auxiliary_opens in
      let opens_output = Output.flat opens in
        ((to_rope (r"\"") lex_skip need_space @@ lean_defs ^ ws end_lex_skips),
          to_rope (r"\"") lex_skip need_space @@ opens_output ^ lean_defs_extra ^ ws end_lex_skips)
    ;;
  end
