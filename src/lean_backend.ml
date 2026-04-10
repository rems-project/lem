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
    | '\000' -> Buffer.add_string buf "\\x00"
    | '\r' -> Buffer.add_string buf "\\r"
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf
;;

(* Collects type namespace names that need 'open' in the auxiliary file *)
let lean_auxiliary_opens : string list ref = ref []
(* Tracks current namespace nesting for qualified open names *)
(* Lean 4 syntax keywords that cannot be used as bare identifiers.
   When these appear as local variable names, they're escaped with «» guillemets. *)
let lean_syntax_keywords = [
  "def"; "class"; "instance"; "where"; "let"; "match"; "if"; "then"; "else";
  "do"; "return"; "import"; "open"; "namespace"; "structure"; "inductive";
  "theorem"; "example"; "variable"; "section"; "end"; "mutual"; "partial";
  "noncomputable"; "unsafe"; "private"; "protected"; "abbrev"; "fun"; "forall";
  "by"; "have"; "show"; "with"; "at"; "in"; "for"; "macro"; "syntax";
  "deriving"; "extends"; "set_option"; "attribute"; "meta"; "catch";
  "break"; "continue"; "try"; "finally"; "unless"; "suffices";
  "nomatch"; "nofun"; "coinductive"; "axiom"; "opaque"; "universe";
  "scoped"; "local"; "public"; "nonrec"; "omit";
  "notation"; "prefix"; "postfix"; "infixl"; "infixr"; "infix";
  "none"; "some"; "true"; "false"; "default";
  "this"; "rfl"; "calc"; "decide"; "sorry";
  "pure"; "get"; "set"; "throw"; "panic"; "admit"; "trivial"
]
let lean_namespace_stack : string list ref = ref []
(* Record types that ended up in mutual blocks — rendered as inductives, not structures.
   Record construction ({..}) and field projection (.field) don't work for these;
   use constructor syntax and pattern matching instead. *)
let lean_mutual_records : Path.t list ref = ref []
(* Collects import module names — emitted at top of file before any other content *)
let lean_collected_imports : string list ref = ref []
(* Tracks locally-defined module names within the current file (via Module definitions).
   These should not be emitted as imports since they're namespaces, not separate files. *)
let lean_local_modules : string list ref = ref []
(* Fully-qualified paths of nested modules that need 'open' at file level.
   Lean's 'open' inside a namespace is scoped, so nested module opens must
   be deferred to the enclosing top-level scope. *)
let lean_deferred_opens : string list ref = ref []
(* Set by process_file.ml before calling lean_defs — used for namespace wrapping *)
let lean_current_module_name : string ref = ref ""
(* When true, isEqual outputs propositional = instead of BEq ==.
   Set during indreln antecedent processing where Prop is needed.
   Reason: Lean's == requires BEq instances, but function types lack BEq.
   Indreln antecedents live in Prop, so = (propositional equality) is correct. *)
let lean_prop_equality : bool ref = ref false
(* Deferred abbrev definitions for types with TYR_subst target reps.
   These are collected during Comment processing and emitted after the
   next non-Comment definition completes, solving ordering dependencies
   (e.g., abbrev mword depends on class Size which is defined later). *)
let lean_pending_abbrevs : Output.t list ref = ref []
(* Map from const_descr_ref to type parameter names for polymorphic indreln.
   Set during indreln antecedent rendering so that exp inserts type params
   for self-references in premises (Lean requires explicit parameters). *)
let lean_indreln_params : (Types.const_descr_ref * string) list ref = ref []

(* Collect import for a qualified identifier from a target_rep.
   If the identifier has a module prefix (e.g., CerberusImpl.sizeof_ity),
   add the module to lean_collected_imports for the current file. *)
(* Extract a module import from a CR_simple target rep body expression.
   Called via Backend_common.on_cr_simple_applied callback during rendering.
   Only fires for the current file's expressions — giving per-file scoping. *)
let collect_cr_simple_import (is_library : bool) (id_str : string) =
  (* Only collect imports for non-library target reps — library target reps
     reference Lean stdlib or LemLib names already available via import LemLib. *)
  if is_library then ()
  else
  match String.index_opt id_str '.' with
    | Some dot_pos when dot_pos > 0 ->
      let mod_name = String.sub id_str 0 dot_pos in
      if String.length mod_name > 0 &&
         Char.uppercase_ascii mod_name.[0] = mod_name.[0] &&
         not (List.mem mod_name !lean_collected_imports) then
        lean_collected_imports := mod_name :: !lean_collected_imports
    | _ -> ()

(* Extract the name string from a type/numeric variable *)
let tnvar_to_string = function
  | Typed_ast.Tn_A (_, tv, _) -> Ulib.Text.to_string tv
  | Typed_ast.Tn_N (_, nv, _) -> Ulib.Text.to_string nv

(* Check if a constant's Lean target rep is == or != (BEq operators).
   Returns Some true for ==, Some false for !=, None otherwise. *)
let check_beq_target_rep c_descr =
  match Target.Targetmap.apply_target c_descr.target_rep (Target.Target_no_ident Target.Target_lean) with
  | Some (CR_infix (_, _, _, ident)) ->
    let name = Ident.to_string ident in
    if name = "==" || name = " ==" then Some true
    else if name = "!=" || name = " !=" then Some false
    else None
  | _ -> None

(* Library modules live under the LemLib.* namespace (e.g. "LemLib.Set").
   User modules have no namespace prefix. *)
let is_library_module mod_name =
  let prefix = "LemLib." in
  let plen = String.length prefix in
  String.length mod_name >= plen && String.sub mod_name 0 plen = prefix

(* Convert a module name like "LemLib.Set" to a flat namespace name "Lem_Set".
   Non-library modules are unchanged. *)
let lean_ns_name mod_name =
  let prefix = "LemLib." in
  let plen = String.length prefix in
  if is_library_module mod_name then
    String.concat "" ["Lem_"; String.sub mod_name plen (String.length mod_name - plen)]
  else mod_name

let lean_qualified_name name_str =
  match !lean_namespace_stack with
    | [] -> name_str
    | ns -> String.concat "." (List.rev ns @ [name_str])

let wrap_lean_comment x = Ulib.Text.(^^^) (Ulib.Text.(^^^) (r"/- ") x) (r" -/")

let sanitize_tabs r =
  let s = Ulib.Text.to_string r in
  if String.contains s '\t' then
    Ulib.Text.of_string (String.map (fun c -> if c = '\t' then ' ' else c) s)
  else r

let rec lean_comment_to_rope =
  function
    | Ast.Chars r -> sanitize_tabs r
    | Ast.Comment coms -> wrap_lean_comment (Ulib.Text.concat (r"") (List.map lean_comment_to_rope coms))

let lex_skip =
  function
    | Ast.Com r -> lean_comment_to_rope r
    | Ast.Ws r -> sanitize_tabs r
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

(* Lean 4 forbids tab characters. Replace tabs with spaces in whitespace and comment tokens. *)
let ws s =
  let sanitize_skip = function
    | Ast.Ws r -> Ast.Ws (sanitize_tabs r)
    | Ast.Com _ as c -> c  (* Comments sanitized in lean_comment_to_rope *)
    | skip -> skip
  in
  match s with
  | None -> Output.ws None
  | Some ts -> Output.ws (Some (List.map sanitize_skip ts))

let sep x s = ws s ^ x
let path_sep = r"."

(* Lean 4 is whitespace-sensitive, so disable auto-formatting blocks
   which can break indentation of match alternatives *)
let block _ _ t = t
let block_hov _ _ t = t

let flatten_newlines = Output.flatten_newlines

let tyvar (_, tv, _) = id Type_var (Ulib.Text.(^^^) (r"") tv)
let concat_str s = concat (from_string s)

(* Escape a string if it's a Lean syntax keyword, using «» guillemets *)
let lean_escape_keyword s =
  if List.mem s lean_syntax_keywords then
    String.concat "" ["\xC2\xAB"; s; "\xC2\xBB"]  (* «name» *)
  else s

let lskips_t_to_output name =
  let stripped = Name.strip_lskip name in
  let s = Ulib.Text.to_string (Name.to_rope stripped) in
  let escaped = lean_escape_keyword s in
  if escaped <> s then from_string escaped
  else Output.id Term_var (Name.to_rope stripped)
;;

(* Name output for variables with keyword escaping *)
let name_var_output v =
  let s = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip v)) in
  let escaped = lean_escape_keyword s in
  if escaped <> s then
    Output.flat [ws (Name.get_lskip v); from_string escaped]
  else
    Name.to_output Term_var v

(* Check if a type is a record that was rendered as a single-constructor inductive
   due to being in a mutual block. Uses the per-compilation-unit list
   lean_mutual_records which accumulates across files in one lem invocation. *)
let is_mutual_record_type typ =
  match typ.Types.t with
    | Types.Tapp (_, path) ->
        List.exists (fun p -> Path.compare p path = 0) !lean_mutual_records
    | _ -> false

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

let tnvar_to_variable = function
  | Typed_ast.Tn_A _ as tv -> Tyvar (from_string (tnvar_to_string tv))
  | Typed_ast.Tn_N _ as nv -> Nvar (from_string (tnvar_to_string nv))
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

(* Extract (class_name, type_var_name) pairs from @Class.method patterns
   in a TYR_subst RHS src_t. These patterns indicate that the type requires
   a typeclass instance parameter (e.g., @Size.size 'a _ means [Size 'a]). *)
let collect_class_constraints_from_src_t (st : Types.src_t) : (string * string) list =
  let rec collect (t : Types.src_t) = match t.term with
    | Types.Typ_backend (p, args) ->
      let path_str = Path.to_string p.descr in
      let at_constraints =
        if String.length path_str > 1 && path_str.[0] = '@' then
          match String.index_opt path_str '.' with
          | Some dot_pos ->
            let class_name = String.sub path_str 1 (dot_pos - 1) in
            List.filter_map (fun (arg : Types.src_t) ->
              match arg.term with
              | Types.Typ_var (_, v) ->
                Some (class_name, Ulib.Text.to_string (Types.tnvar_to_rope (Types.Ty v)))
              | _ -> None
            ) args
          | None -> []
        else []
      in
      at_constraints @ List.concat_map collect args
    | Types.Typ_app (_, args) -> List.concat_map collect args
    | Types.Typ_paren (_, t', _) -> collect t'
    | Types.Typ_fn (t1, _, t2) -> collect t1 @ collect t2
    | Types.Typ_tup sl -> List.concat_map collect (Seplist.to_list sl)
    | _ -> []
  in
  collect st
;;

(* Collect extra class constraints introduced by TYR_subst type target reps.
   When a type like mword has a TYR_subst mapping to BitVec (@Size.size 'a _),
   any function using mword 'a needs [Size 'a] but the Lem type doesn't
   carry this constraint. This function walks a Lem type and finds all such
   extra constraints by: (1) finding Tapp nodes whose type has a Lean TYR_subst,
   (2) extracting @Class.method patterns from the TYR_subst RHS via
   collect_class_constraints_from_src_t, (3) mapping TYR_subst type variables
   to actual type arguments. *)
let extra_constraints_for_tyr_subst (ty : Types.t) : (string * string) list =
  let l_unk = Ast.Trans (true, "extra_constraints_for_tyr_subst", None) in
  let constraints = ref [] in
  let rec walk (ty : Types.t) =
    match ty.t with
    | Types.Tapp (args, path) ->
      let td_opt = try Some (Types.type_defs_lookup l_unk A.env.t_env path)
                   with _ -> None in
      begin match td_opt with
      | Some td ->
        begin match Target.Targetmap.apply_target td.Types.type_target_rep
                (Target.Target_no_ident Target.Target_lean) with
        | Some (Types.TYR_subst (_, _, tvars, rhs_t)) ->
          let tvar_strs = List.map (fun tv ->
            Ulib.Text.to_string (Types.tnvar_to_rope tv)
          ) tvars in
          let var_map = List.combine tvar_strs args in
          let raw = collect_class_constraints_from_src_t rhs_t in
          List.iter (fun (cls, tv) ->
            match List.assoc_opt tv var_map with
            | Some actual_ty ->
              begin match actual_ty.t with
              | Types.Tvar v' ->
                let actual_tv = Ulib.Text.to_string (Tyvar.to_rope v') in
                if not (List.mem (cls, actual_tv) !constraints) then
                  constraints := (cls, actual_tv) :: !constraints
              | _ -> () (* Concrete type argument — no constraint needed *)
              end
            | None -> ()
          ) raw
        | _ -> ()
        end
      | None -> ()
      end;
      List.iter walk args
    | Types.Tfn (t1, t2) -> walk t1; walk t2
    | Types.Ttup ts -> List.iter walk ts
    | Types.Tbackend (ts, _) -> List.iter walk ts
    | _ -> ()
  in
  walk ty;
  List.rev !constraints
;;

(* Filter out constraints that are already present in Lem's class_constraints. *)
let filter_new_tyr_constraints extras class_constraints =
  let existing = List.map (fun (path, tnvar) ->
    (Name.to_string (B.class_path_to_name path),
     Ulib.Text.to_string (Types.tnvar_to_rope tnvar))
  ) class_constraints in
  List.filter (fun c -> not (List.mem c existing)) extras
;;

(* Format extra TYR_subst constraints as Lean instance parameters: [Class tv] *)
let format_tyr_constraints extras =
  Output.flat (List.map (fun (cls, tv) ->
    Output.flat [from_string " ["; from_string cls; from_string " "; from_string tv; from_string "]"]
  ) extras)
;;

(* Lean-native constraints for default instances.
   Lem's default_instance declarations are unconstrained (forall 'a), but
   their method bodies reference Lean functions requiring typeclass instances:
   - Eq0 body uses == (BEq) and != (BEq)
   - SetType body uses defaultCompare (Ord)
   The other two defaults (OrdMaxMin, MapKeyType) already carry Lem-level
   constraints that provide what Lean needs.
   This extends the extra_constraints_for_tyr_subst pattern (above) to
   handle function target rep constraints in default instances. *)
let lean_default_instance_extra_constraints class_name =
  match class_name with
  | "Eq0" -> ["BEq"]
  | "SetType" -> ["Ord"]
  | _ -> []
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

(* Lean 4's greedy parser extends match/if/let/fun rightward, consuming
   subsequent tokens. These forms must be parenthesized when nested inside:
   - function arguments: f (match ...) instead of f match ...
   - match arm bodies: | p => (match ...) to avoid consuming outer | arms
   - if conditions: if (match ...) then ... to avoid misparsing *)
let needs_parens term =
  match term with
    | Case _ | If _ | Let _ | Fun _ -> true
    | _ -> false

(* Pattern rendering has two modes:
   - FunParam: adds type annotations to variables and wildcards (needed with
     autoImplicit=false), resolves wildcard types, wraps cons/unit in parens
   - MatchArm: bare output for match arms and let bindings *)
type pat_style = FunParam | MatchArm

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
              (* Skip lemma/theorem generation for Lean. These assert inline expansion
                 correctness but contain complex expressions (match, forall) that
                 cause parsing issues, and the proof is by sorry anyway. *)
              Output.flat [
                ws skips; from_string "/- removed theorem "; name_out; from_string " -/"
              ]
          else
            from_string "/- removed lemma intended for another backend -/"
        (* All non-Lemma defs are handled by def, not def_extra.
           Exhaustive match so new def_aux variants trigger a compiler warning. *)
        | Type_def _ | Val_def _ | Module _ | Rename _ | OpenImport _
        | OpenImportTarget _ | Indreln _ | Val_spec _ | Class _ | Instance _
        | Comment _ | Declaration _ -> emp
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
          let (_, is_real_rec, try_term) =
            Typed_ast_syntax.try_termination_proof
              (Target_no_ident Target_lean) A.env.c_env m
          in
          val_def false None is_real_rec try_term def tv_set class_constraints
      | Module (skips, (name, l), mod_binding, skips', skips'', defs, skips''') ->
        let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
        lean_local_modules := name_str :: !lean_local_modules;
        lean_namespace_stack := name_str :: !lean_namespace_stack;
        (* Build fully-qualified path for this module *)
        let fq_path = String.concat "." (List.rev !lean_namespace_stack) in
        let name = lskips_t_to_output name in
        let body = callback defs in
        lean_namespace_stack := (match !lean_namespace_stack with _ :: tl -> tl | [] -> []);
          (* In Lem, module contents are implicitly available after the module
             definition. Lean namespaces are not — we need an explicit 'open'.
             For top-level modules, emit 'open' directly plus any deferred
             opens from nested modules. For nested modules, defer the open
             since Lean's 'open' inside a namespace is scoped to that block. *)
          let is_top_level = !lean_namespace_stack = [] in
          if is_top_level then
            let deferred = !lean_deferred_opens in
            lean_deferred_opens := [];
            let deferred_opens = flat @@ List.map (fun p ->
              from_string (String.concat "" ["\nopen "; p])
            ) deferred in
            Output.flat [
              ws skips; from_string "namespace "; name; ws skips'; ws skips'';
              body; from_string "\nend "; name;
              from_string "\nopen "; name; deferred_opens; ws skips'''
            ]
          else begin
            lean_deferred_opens := fq_path :: !lean_deferred_opens;
            Output.flat [
              ws skips; from_string "namespace "; name; ws skips'; ws skips'';
              body; from_string "\nend "; name;
              from_string "\nopen "; name; ws skips'''
            ]
          end
      | Rename (skips, name, mod_binding, skips', mod_descr) -> emp  (* Module renames not applicable in Lean *)
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
          let is_user_module = not (is_library_module !lean_current_module_name) in
          let handle_mod (sk, md) =
            (if not (List.mem md !lean_local_modules) then
              lean_collected_imports := md :: !lean_collected_imports);
            (* Emit 'open' for:
               - Local modules (defined in this file via Module) — they create namespaces
               - Library modules in library context — they have Lem_X namespaces
               User modules from other files have no namespace; import alone suffices.
               In non-library (user) modules, skip inline opens for library imports —
               transitive_opens will emit them for both main and auxiliary files. *)
            if List.mem md !lean_local_modules then
              Output.flat [
                from_string "open"; ws sk; from_string md; from_string "\n"
              ]
            else if not (is_library_module md) then emp
            else if is_user_module then emp
            else
              let ns = lean_ns_name md in
              Output.flat [
                from_string "open"; ws sk; from_string ns; from_string "\n"
              ]
          in
          if (not (in_target targets)) then emp else Output.flat (List.map handle_mod mod_descrs)
      | OpenImportTarget _ ->
          (* Unreachable: def_trans converts all OI variants to OI_open *)
          raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected non-OI_open OpenImportTarget")
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
          let tv_kind = match tv with Typed_ast.Tn_A _ -> "Type" | Typed_ast.Tn_N _ -> "Nat" in
          let tv = from_string (tnvar_to_string tv) in
          let method_names = ref [] in
          let body_entries =
            List.filter_map (fun (skips, targets_opt, (name, l), const_descr_ref, ascii_rep_opt, skips', src_t) ->
              if in_target targets_opt then
                let name' = B.const_ref_to_name name true const_descr_ref in
                let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name')) in
                  method_names := name_str :: !method_names;
                  Some (Output.flat [
                    ws skips; from_string name_str; from_string " :"; ws skips'; pat_typ src_t
                  ])
              else
                None
            ) body
          in
          let body_out = Output.concat (from_string "\n") body_entries in
          (* If the class has an isEqual method (i.e., this is Lem's Eq class),
             emit a BEq bridge instance so that == works wherever [Eq0 a] is available.
             This is needed because isEqual is mapped to == (BEq) in Lean. *)
          let has_isEqual = List.exists (fun (_, _, (mn, _), cref, _, _, _) ->
            (* Check if any method has target_rep mapped to == (BEq).
               The method's original name might be = with isEqual as alternative,
               so check the const_descr for the Lean target rep. *)
            let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
            match Target.Targetmap.apply_target cd.target_rep
                    (Target.Target_no_ident Target.Target_lean) with
            | Some (CR_infix(_, _, _, op_id)) ->
                Ident.to_string op_id = "=="
            | _ -> false
          ) body in
          (* Check if the class has a comparison method (returns LemOrdering).
             Known: setElemCompare (SetType), mapKeyCompare (MapKeyType).
             If so, derive BEq from the comparison function. *)
          let compare_method_names = ["setElemCompare"; "mapKeyCompare"] in
          let compare_method = List.find_opt (fun n ->
            List.mem n compare_method_names
          ) (List.rev !method_names) in
          let beq_bridge =
            if has_isEqual then
              Output.flat [
                from_string "\ninstance {"; tv; from_string " : "; from_string tv_kind;
                from_string "} ["; name; from_string " "; tv; from_string "] : BEq "; tv;
                from_string " where\n  beq := isEqual\n"
              ]
            else match compare_method with
            | Some cmp_name ->
              Output.flat [
                from_string "\ninstance {"; tv; from_string " : "; from_string tv_kind;
                from_string "} ["; name; from_string " "; tv; from_string "] : BEq "; tv;
                from_string (String.concat "" [" where\n  beq x y := match "; cmp_name; " x y with | .EQ => true | _ => false\n"])
              ]
            | None -> emp
          in
          (* Export class methods so they are visible to importing files.
             Skip names that clash with Lean stdlib globals — a clash here
             causes a Lean compile error (ambiguous name), not silent failure.
             Review this list when upgrading the Lean toolchain. *)
          let lean_global_names = ["max"; "min"; "compare"] in
          let exportable = List.filter (fun n ->
            not (List.mem n lean_global_names)
          ) (List.rev !method_names) in
          let class_export =
            if exportable = [] then
              Output.flat [from_string "\nopen "; name; from_string "\n"]
            else begin
              let names_str = String.concat "" ["("; String.concat " " exportable; ")"] in
              Output.flat [
                from_string "\nexport "; name; from_string " "; from_string names_str; from_string "\n"
              ]
            end
          in
          Output.flat [
            ws skips; from_string "class"; ws skips'; name; from_string " ("; tv; from_string " : "; from_string tv_kind; from_string ") where"
          ; ws skips''; from_string "\n"; body_out
          ; ws skips'''; from_string "\n"; class_export
          ; beq_bridge
          ]
      | Instance ((Ast.Inst_default skips | Ast.Inst_decl skips) as inst_kind, i_ref, inst, vals, skips') ->
        let is_default = match inst_kind with Ast.Inst_default _ -> true | _ -> false in
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
                            (* Use fully qualified paths from the type system
                               rather than parsing unqualified Idents from the AST.
                               The Cs_list Idents may be unqualified (e.g., "Eq"
                               instead of "Basic_classes.Eq"), which fails to look
                               up in t_env for class renaming. *)
                            let cs =
                              Output.concat (from_string " ") (List.map (fun (cpath, tnvar) ->
                                let class_name = B.class_path_to_name cpath in
                                let var = from_string @@ Ulib.Text.to_string @@ Types.tnvar_to_rope tnvar in
                                Output.flat [
                                  from_string "["; from_string (Name.to_string class_name);
                                  from_string " "; var; from_string "]"
                                ]
                              ) instance_info.Types.inst_constraints)
                            in
                            (* Add extra constraints from TYR_subst type target reps *)
                            let extra_tyr = extra_constraints_for_tyr_subst instance_info.Types.inst_type in
                            let new_extras = filter_new_tyr_constraints extra_tyr instance_info.Types.inst_constraints in
                            let cs = cs ^ format_tyr_constraints new_extras in
                            (* Add Lean-native constraints for default instances *)
                            let cs =
                              if is_default then
                                let target_class = Name.to_string (B.class_path_to_name path) in
                                let extra_classes = lean_default_instance_extra_constraints target_class in
                                let pairs = List.concat_map (fun cls ->
                                  List.filter_map (fun t ->
                                    match t with
                                    | Typed_ast.Tn_A (_, var, _) ->
                                      Some (cls, Ulib.Text.to_string var)
                                    | _ -> None
                                  ) tnvar_list
                                ) extra_classes in
                                cs ^ format_tyr_constraints pairs
                              else cs
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
                  (* Wrap the class type argument in parens if it's a type application
                     (e.g., mem_constraint a → (mem_constraint a)). Without this,
                     Lean parses 'Constraints mem_constraint a' as two arguments. *)
                  let type_arg = match src_t.term with
                    | Typ_app (_, _ :: _) ->
                      Output.flat [from_string " ("; pat_typ src_t; from_string ")"]
                    | _ -> pat_typ src_t
                  in
                  Output.flat [
                    ws skips; tyvars_typeset; from_string " "; c; from_string " : "; id
                  ; type_arg
                  ]
          in
          let body =
            Output.concat (from_string "\n") (List.map (fun d -> val_def true (Some i_ref) false true d Types.TNset.empty []) vals)
          in
            let inst_kw = if is_default
              then from_string "instance (priority := low)"
              else from_string "instance" in
            Output.flat [
              ws skips; inst_kw; prefix; from_string " where";
              from_string "\n"; body;
              ws skips'
            ]
      | Comment c ->
        let ((def_aux, skips_opt), l, lenv) = c in
        let skips = match skips_opt with None -> from_string "\n" | Some s -> ws s in
        (* Check if this is a Type_def with a TYR_subst target rep for Lean.
           If so, emit an abbrev definition instead of just a block comment.
           This enables parameterized type mappings like mword 'a → BitVec (Size.size a). *)
        let abbrev_for_target_rep = match def_aux with
          | Type_def (_, sl) when Seplist.length sl = 1 ->
            let ((n0, _), tyvars, t_path, _, _) = Seplist.hd sl in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            begin match Target.Targetmap.apply_target td.Types.type_target_rep
                    (Target.Target_no_ident Target.Target_lean) with
            | Some (Types.TYR_subst (_, _, _, rhs_t)) ->
              let name = B.type_path_to_name n0 t_path in
              let name_out = Name.to_output (Type_ctor (false, false)) name in
              let tyvars_out = type_def_type_variables tyvars in
              let rhs_out = pat_typ rhs_t in
              let class_constraints = collect_class_constraints_from_src_t rhs_t in
              let constraints_out = Output.flat (List.map (fun (cls, tv) ->
                Output.flat [from_string "["; from_string cls; from_string " "; from_string tv; from_string "] "]
              ) class_constraints) in
              Some (Output.flat [
                from_string "\nabbrev "; name_out; from_string " "; tyvars_out;
                constraints_out;
                from_string " := "; rhs_out; from_string "\n"
              ])
            | _ -> None
            end
          | _ -> None
        in
        let comment = Output.flat [
          skips; from_string "/- "; def inside_instance callback inside_module def_aux; from_string " -/"
        ] in
        begin match abbrev_for_target_rep with
        | Some abbrev_out ->
          lean_pending_abbrevs := abbrev_out :: !lean_pending_abbrevs;
          comment
        | None -> comment
        end
      | Declaration _ -> emp  (* Declarations (target_rep, rename, etc.) are processed earlier *)
      | Lemma _ -> emp  (* Lemmas are handled by def_extra, not def *)
    and val_def inside_instance i_ref_opt is_recursive try_term def tv_set class_constraints =
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
          (* Collect extra constraints introduced by TYR_subst type target reps.
             For example, mword 'a → BitVec (@Size.size 'a _) introduces [Size 'a].
             Skip when inside_instance — the instance header already has the constraint. *)
          let extra_tyr = if inside_instance then [] else
            let l_unk = Ast.Trans (true, "lean_tyr_extra", None) in
            let cs = match def with
              | Let_def(_, _, (_, nm, _, _, _)) -> List.map snd nm
              | Let_inline(_,_,_,_,c,_,_,_) -> [c]
              | Fun_def(_, _, _, funs) ->
                Seplist.to_list_map (fun ((_, c, _, _, _, _):funcl_aux) -> c) funs
              | _ -> []
            in
            let cds = List.map (c_env_lookup l_unk A.env.c_env) cs in
            let extras = List.concat_map (fun cd ->
              extra_constraints_for_tyr_subst cd.const_type
            ) cds in
            filter_new_tyr_constraints extras class_constraints
          in
          if List.length class_constraints = 0 && extra_tyr = [] then
            emp
          else
            body ^ format_tyr_constraints extra_tyr
        in
        match def with
          | Let_def (skips, targets, (p, name_map, topt, sk, e)) ->
              if in_target targets then
                (* Lean doesn't support destructuring in 'def' bindings.
                   Emit one def per bound name: def x : T := let PAT := EXPR; x *)
                let pat_out = def_pattern p in
                let exp_out = exp inside_instance e in
                let type_out = match topt with
                  | None -> emp
                  | Some (_, t) -> Output.flat [from_string " :"; pat_typ t]
                in
                let defs = List.map (fun (_orig_name, cref) ->
                  let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
                  let (_, renamed, _) = Typed_ast_syntax.constant_descr_to_name
                    (Target.Target_no_ident Target.Target_lean) cd in
                  let name_str = Name.to_string renamed in
                  let var_type = pat_typ (C.t_to_src_t cd.const_type) in
                  let defn = if inside_instance then emp else from_string "def " in
                  Output.flat [
                    from_string "\n"; defn; from_string name_str; constraints;
                    from_string "  : "; var_type;
                    from_string " :=\n  let "; pat_out; type_out;
                    ws sk; from_string " :="; exp_out;
                    from_string "\n  "; from_string name_str
                  ]
                ) name_map in
                Output.flat (ws skips :: defs)
              else
                ws skips ^ from_string "/- removed value definition intended for another target -/"
          | Fun_def (skips, rec_flag, targets, funcl_skips_seplist) ->
              if in_target targets then
                let skips' = match rec_flag with FR_non_rec -> None | FR_rec sk -> sk in
                let funcls = Seplist.to_list funcl_skips_seplist in
                (* Group clauses by function name, preserving definition order.
                   Lem allows interleaving, but Lean's equation compiler requires
                   all clauses for a function in sequence. Multi-clause groups
                   render as Lean 4 pattern-matching equations. *)
                let get_name ({term = n}, _, _, _, _, _) = Name.to_string (Name.strip_lskip n) in
                let groups =
                  let order = ref [] in
                  let tbl = Hashtbl.create 8 in
                  List.iter (fun fcl ->
                    let key = get_name fcl in
                    (if not (Hashtbl.mem tbl key) then
                      order := key :: !order);
                    let existing = match Hashtbl.find_opt tbl key with Some v -> v | None -> [] in
                    Hashtbl.replace tbl key (existing @ [fcl])
                  ) funcls;
                  List.map (fun key -> Hashtbl.find tbl key) (List.rev !order)
                in
                let num_functions = List.length groups in
                let is_truly_mutual = num_functions > 1 in
                let def_keyword =
                  if inside_instance then emp
                  else if is_recursive && not try_term then
                    from_string "partial def"
                  else
                    from_string "def"
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
                    let n = B.const_ref_to_name n true c in
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
                      let body =
                        if needs_parens (C.exp_to_term e) then
                          Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                        else exp inside_instance e
                      in
                      flatten_newlines (Output.flat [
                        from_string "\n  | "; pat_out; from_string " =>"; ws skips; from_string " "; body
                      ])
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
    (* Inductive relation (indreln) rendering. Phases:
       1. Gather unique relation names with their const_descr_refs
       2. Set lean_indreln_params so exp can insert type parameters for
          polymorphic self-references in premises
       3. Build inductive definitions using renamed names from const_descr
          (handles cross-module collisions like thread_trans → thread_trans0)
       4. Render clauses with lean_prop_equality set so antecedents use
          propositional = instead of BEq ==
       lean_indreln_params is saved/restored so nested indreln blocks don't
       clobber the outer scope. *)
    and clauses (inside_instance: bool) clause_list =
      (* Gather unique relation names from clauses, paired with their
         const_descr_ref so we can look up the renamed name for output *)
      let gather_names clause_list =
        let rec gather_names_aux buffer clauses =
          match clauses with
            | []    -> buffer
            | (Rule(_,_, _, _, _, _, _, name_lskips_annot, c, _),_)::xs ->
              let name = name_lskips_annot.term in
              let name = Name.strip_lskip name in
              if List.exists (fun (n, _) -> Stdlib.compare n name = 0) buffer then
                gather_names_aux buffer xs
              else
                gather_names_aux ((name, c)::buffer) xs
        in
          gather_names_aux [] clause_list
      in
      let gathered = gather_names clause_list in
      (* For polymorphic indreln: compute type parameter names per relation
         and set lean_indreln_params so exp can insert them in premises. *)
      let saved_indreln_params = !lean_indreln_params in
      lean_indreln_params := List.filter_map (fun (_name, c_ref) ->
        let cd = c_env_lookup Ast.Unknown A.env.c_env c_ref in
        let tvs = Types.free_vars cd.const_type in
        if Types.TNset.cardinal tvs = 0 then None
        else
          let params_str = String.concat " " @@
            List.map (fun v -> Name.to_string (Types.tnvar_to_name v))
              (Types.TNset.elements tvs) in
          Some (c_ref, params_str)
      ) gathered;
      Fun.protect ~finally:(fun () -> lean_indreln_params := saved_indreln_params) (fun () ->
      let compare_clauses_by_name name (Rule(_,_, _, _, _, _, _, name', _, _),_) =
        let name' = name'.term in
        let name' = Name.strip_lskip name' in
          Stdlib.compare name name' = 0
      in
      let indrelns =
        List.map (fun (name, c_ref) ->
          (* Use the renamed name from the constant descriptor, not the raw AST name.
             This handles cross-module collisions (e.g., indreln "thread_trans"
             renamed to "thread_trans0" to avoid conflict with imported type). *)
          let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_ref in
          let (_, renamed_name, _) = Typed_ast_syntax.constant_descr_to_name (Target.Target_no_ident Target.Target_lean) c_descr in
          let name_string = Name.to_string renamed_name in
          let matching_clauses = List.filter (compare_clauses_by_name name) clause_list in
          let index_type_parts =
            match matching_clauses with
              | [] -> [from_string "Prop"]
              | (Rule(_,_, _, _, _, _, _, _, _, exp_list),_)::_ ->
                  List.map (fun t ->
                    Output.flat [
                      from_string "("; indreln_typ @@ C.t_to_src_t (Typed_ast.exp_to_typ t); from_string ")"
                    ]
                  ) exp_list
          in
          let clause_outputs =
            List.map (fun (Rule(name_lskips_t, skips0, skips, name_lskips_annot_list, skips', exp_opt, skips'', name_lskips_annot, c, exp_list),_) ->
              let constructor_name = from_string (Name.to_string (Name.strip_lskip name_lskips_t)) in
              let antecedent =
                match exp_opt with
                  | None -> emp
                  | Some e ->
                    match dest_and_exps A.env e with
                    | [] -> emp
                    | ants ->
                      (* Use propositional = in indreln antecedents instead of BEq ==.
                         Functions and other types without BEq need propositional equality. *)
                      let saved = !lean_prop_equality in
                      lean_prop_equality := true;
                      Fun.protect ~finally:(fun () -> lean_prop_equality := saved) (fun () ->
                        flat [
                          concat_str " → "
                            (List.map (fun e ->
                                 flat [ from_string "(";
                                        exp inside_instance e;
                                        from_string ")" ]) ants);
                          from_string " → "
                        ]
                      )
              in
              let bound_variables =
                concat_str " " @@ List.map (fun b ->
                  match b with
                    | QName n -> from_string (lean_escape_keyword (Name.to_string (Name.strip_lskip n.term)))
                    | _ -> raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected binding form in indreln quantifier")
                ) name_lskips_annot_list
              in
              let binder, binder_sep =
                match name_lskips_annot_list with
                  | [] -> emp, emp
                  | _ -> from_string "∀ ", from_string ", "
              in
              let indices = concat_str " " @@ List.map (exp inside_instance) exp_list in
              let index_free_vars_set =
                List.fold_right Types.TNset.union
                  (List.map (fun t -> Types.free_vars (Typed_ast.exp_to_typ t)) exp_list)
                  Types.TNset.empty
              in
              let index_free_vars_typeset = concat_str " " @@ List.map (fun v -> from_string (Name.to_string (Types.tnvar_to_name v))) (Types.TNset.elements index_free_vars_set) in
              let relation_name = from_string name_string in
                Output.flat [
                  from_string "  | "; constructor_name; from_string " : ";
                  binder; bound_variables; binder_sep; antecedent;
                  relation_name; from_string " "; index_free_vars_typeset; from_string " "; indices
                ], index_free_vars_set
            ) matching_clauses
          in
          let all_free_vars =
            Types.TNset.elements @@
            List.fold_right Types.TNset.union (List.map snd clause_outputs) Types.TNset.empty
          in
          let free_vars_typeset =
            concat_str " " @@ List.map (fun v ->
              Output.flat [
                from_string "("; from_string (Name.to_string (Types.tnvar_to_name v)); from_string " : Type)"
              ]) all_free_vars
          in
          let index_type_sig =
            Output.flat [
              concat_str " → " index_type_parts; from_string " → Prop"
            ]
          in
          let clause_body = concat_str "\n" @@ List.map fst clause_outputs in
          Output.flat [
            from_string name_string; from_string " "; free_vars_typeset; from_string " : "; index_type_sig; from_string " where\n";
            clause_body
          ]
        ) gathered
      in
        let is_mutual = List.length indrelns > 1 in
        let prefix = if is_mutual then from_string "\nmutual" else emp in
        let suffix = if is_mutual then from_string "\nend" else emp in
        Output.flat [
          prefix;
          from_string "\ninductive "; concat_str "\ninductive " indrelns;
          suffix
        ]
      )
    and let_body inside_instance i_ref_opt top_level tv_set ((lb, _):letbind) =
      match lb with
        | Let_val (p, topt, skips, e) ->
            (* In Lean 4, `let (x : T) := val; body` is parsed as a pattern-matching
               let where x is NOT bound into body's scope. The correct syntax is
               `let x : T := val; body`. So when the pattern is P_typ at the top level,
               extract the inner pattern and emit the type annotation separately. *)
            let p_out, typ_from_pat = match p.term with
              | P_typ (_skips, inner_p, _skips', t, _skips'') ->
                  def_pattern inner_p, Some t
              | _ ->
                  def_pattern p, None
            in
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
                | None ->
                    (match typ_from_pat with
                      | None -> emp
                      | Some t ->
                          Output.flat [from_string " :"; pat_typ t])
                | Some (s, t) ->
                    Output.flat [
                      ws s; from_string " :"; pat_typ t
                    ]
            in
            let e = exp inside_instance e in
              Output.flat [
                p_out; tv_set_sep; tv_set; topt; ws skips; from_string " :="; e
              ]
        | Let_fun _ ->
            (* Pattern compilation transforms Let_fun into funcl before the backend *)
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected Let_fun in let_body (should be compiled away)")
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
        else begin
          let tv_set =
            if Types.TNset.cardinal tv_set = 0 then
              Types.free_vars (Typed_ast.exp_to_typ e)
            else tv_set
          in
          (* Filter out phantom type variables that don't appear in any explicit
             parameter types or the return type. Lean can't infer these. *)
          let sig_tvs =
            let pat_tvs = List.fold_left (fun acc p ->
              Types.TNset.union acc (Types.free_vars p.typ)
            ) Types.TNset.empty pats in
            let ret_tvs = match typ_opt with
              | None -> Types.free_vars (Typed_ast.exp_to_typ e)
              | Some (_, t) -> Types.free_vars t.typ
            in
            Types.TNset.union pat_tvs ret_tvs
          in
          let tv_set = Types.TNset.inter tv_set sig_tvs in
          if Types.TNset.cardinal tv_set = 0 then
            emp, let_type_variables true tv_set
          else
            from_string " ", let_type_variables true tv_set
        end
      in
      let typ_opt =
        match typ_opt with
          | None -> emp
          | Some (s, t) ->
              Output.flat [
                ws s; from_string " : "; pat_typ t
              ]
      in
        let body = exp inside_instance e in
        (* Inside instance definitions, flatten newlines in the body expression.
           Without this, multiline bodies (e.g., sorry-based opaque type instances)
           can have arguments on a new line at field-name indentation, which Lean
           misparses as a new field definition. *)
        let body = if inside_instance then flatten_newlines body else body in
        Output.flat [
          ws name_skips; from_string " "; name; tv_set_sep; tv_set; constraints_sep; constraints; pat_skips;
          fun_pattern_list inside_instance pats; ws skips; typ_opt; from_string " := "; body
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
                    | _ ->
                      let method_name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
                      raise (Reporting_basic.err_general true Ast.Unknown
                        (String.concat "" ["Lean backend: instance method not found for '"; method_name; "'"]))
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
        from_string " " ^ concat_str " " bindings
    (* Expression rendering. Lean 4 parser-specific rules:
       - Match/if/let/fun in function args or case bodies are parenthesized
         (Lean's greedy rightward match would otherwise consume too much)
       - In indreln antecedents (lean_prop_equality), == and != become = and ≠
       - For polymorphic indreln self-references (lean_indreln_params), explicit
         type parameters are inserted since Lean can't infer them
       - Class method constants get explicit @ type application when used bare *)
    and exp inside_instance e =
      let is_user_exp = Typed_ast_syntax.is_pp_exp e in
        match C.exp_to_term e with
          | Var v ->
              name_var_output v
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
              let trans e_inner =
                if needs_parens (C.exp_to_term e_inner) then
                  Output.flat [from_string "("; exp inside_instance e_inner; from_string ")"]
                else exp inside_instance e_inner
              in
              let sep = from_string " " in
              let oL = begin
              let (e0, args) = strip_app_exp e in
                match C.exp_to_term e0 with
                  | Constant cd ->
                    (* In indreln antecedents (Prop context), == and != applied via
                       App nodes (e.g. from <> decomposition: not (isEqual x y)) must
                       use propositional =/≠ instead of BEq ==/!=. *)
                    let c_descr = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
                    begin match !lean_prop_equality, args, check_beq_target_rep c_descr with
                    | true, [arg0; arg1], Some is_eq ->
                      let l_out = trans arg0 in
                      let r_out = trans arg1 in
                      if is_eq then [Output.flat [l_out; from_string "  =  "; r_out]]
                      else [Output.flat [l_out; meta_utf8 "  \xe2\x89\xa0  "; r_out]]
                    | _ ->
                      (* For polymorphic indreln self-references in antecedents,
                         insert explicit type parameters (Lean requires them). *)
                      begin match List.assoc_opt cd.descr !lean_indreln_params with
                      | Some params_str ->
                        let func_out = trans e0 in
                        let args_out = List.map trans args in
                        [Output.flat ([func_out; from_string " "; from_string params_str]
                          @ List.map (fun a -> Output.flat [from_string " "; a]) args_out)]
                      | None ->
                        B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd.descr)
                      end
                    end
                  | Backend (_, i) when Ident.to_string i = "sorry" ->
                    (* sorry is a term, not a function — drop applied arguments.
                       Annotate with the expression's type so Lean can infer it
                       in contexts like let bindings. *)
                    let typ = Typed_ast.exp_to_typ e in
                    let src_t = C.t_to_src_t typ in
                    [Output.flat [from_string "(sorry : "; pat_typ src_t; from_string ")"]]
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
          | Let (skips, bind, _skips', e) ->
              let body = flatten_newlines (let_body inside_instance None false Types.TNset.empty bind) in
                Output.flat [
                  ws skips; from_string "let "; body; from_string "; "; exp inside_instance e
                ]
          | Constant const ->
              let c_descr = c_env_lookup Ast.Unknown A.env.c_env const.descr in
              let default_const_output () =
                Output.concat emp (B.function_application_to_output (exp_to_locn e) (exp inside_instance) false e const [] (use_ascii_rep_for_const const.descr))
              in
              (* Class method constants used bare (no explicit arguments) need explicit
                 @ type application in Lean 4. Without it, Lean can't infer the class
                 type parameter for nullary methods like `size : {a : Type} → [Size a] → Nat`
                 because the return type `Nat` doesn't mention the type parameter `a`.
                 Using `@size a _` provides the type argument explicitly.
                 Skip this for class methods that have a Lean target rep, since the
                 target rep already handles resolution. *)
              if c_descr.const_class <> [] then begin
                match Target.Targetmap.apply_target c_descr.target_rep
                        (Target.Target_no_ident Target.Target_lean) with
                | Some _ -> default_const_output ()
                | None ->
                  let i = B.const_id_to_ident const false in
                  let sk = Ident.get_lskip i in
                  let type_args = List.map (fun t ->
                    let src_t = C.t_to_src_t t in
                    Output.flat [from_string " ("; pat_typ src_t; from_string ")"]
                  ) const.instantiation in
                  let num_classes = List.length c_descr.const_class in
                  let class_holes = List.init num_classes (fun _ -> from_string " _") in
                  (* Parenthesize the @name (type) _ expression so it can safely
                     appear as an argument to another function *)
                  Output.flat ([ws sk; from_string "(@"; Ident.to_output (Term_const (false, true)) path_sep (Ident.replace_lskip i no_lskips)] @ type_args @ class_holes @ [from_string ")"])
              end else
                default_const_output ()
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
              (* Lem's begin...end is a grouping construct. In Lean, use parens. *)
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; ws skips';
                from_string ")"
              ]
          | Record (skips, fields, skips') ->
            let typ = Typed_ast.exp_to_typ e in
            if is_mutual_record_type typ then
              (* Mutual records are rendered as inductives, not structures.
                 Use constructor syntax: TypeName.mk val1 val2 ... *)
              let field_vals = Seplist.to_list fields in
              let vals = List.map (fun (_, _, e_val, _) ->
                Output.flat [from_string " ("; exp inside_instance e_val; from_string ")"]
              ) field_vals in
              let src_t = C.t_to_src_t typ in
              (* Build TypeName.mk — extract just the type name, ignoring params.
                 This avoids dot-notation parsing issues with parenthesized type args. *)
              let type_name_str = match typ.Types.t with
                | Types.Tapp (_, path) ->
                    let n0 = Name.add_lskip (Path.get_name path) in
                    let n = B.type_path_to_name n0 path in
                    Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n))
                | _ -> assert false  (* unreachable: is_mutual_record_type requires Tapp *)
              in
              Output.flat ([
                ws skips; from_string "("; from_string type_name_str; from_string ".mk"
              ] @ vals @ [
                ws skips'; from_string ")"
              ])
            else begin
              let body = flatten_newlines (flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (field_update inside_instance) (sep @@ from_string ",") fields) in
              (* Add type ascription so Lean can resolve the record type from
                 field names. Without it, { field := value } fails when the
                 expected type isn't known from context (e.g., in a let binding). *)
              let src_t = C.t_to_src_t typ in
                Output.flat [
                  ws skips; from_string "(({ "; body; ws skips'; from_string " } : "; pat_typ src_t; from_string "))"
                ]
            end
          | Field (e, skips, fd) ->
            let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
            (* Dot notation works for both structures (.field accessor) and
               mutual records (we generate explicit accessor functions).
               Parenthesize match/if/let/fun: without parens, .field binds
               to the last arm body, not the whole expression. *)
            let e_out =
              if needs_parens (C.exp_to_term e) then
                Output.flat [from_string "("; exp inside_instance e; from_string ")"]
              else exp inside_instance e
            in
              Output.flat [
                e_out; from_string "."; ws skips; name
              ]
          | Recup (skips, e, skips', fields, skips'') ->
            let e_typ = Typed_ast.exp_to_typ e in
            if is_mutual_record_type e_typ then
              (* Mutual records are inductives — { r with ... } doesn't work.
                 Look up all fields from the type definition, reconstruct with
                 accessor functions for unchanged fields and new values for updated ones. *)
              let updated = Seplist.to_list fields in
              let updated_names = List.map (fun (fd, _, _, _) ->
                let c_descr = c_env_lookup Ast.Unknown A.env.c_env fd.descr in
                Name.to_string (Path.get_name c_descr.const_binding)
              ) updated in
              let updated_map = List.map2 (fun name (_, _, e_val, _) -> (name, e_val)) updated_names updated in
              (* Look up the type's fields from the environment *)
              let src_t = C.t_to_src_t e_typ in
              (match Types.type_defs_lookup_typ Ast.Unknown A.env.t_env e_typ with
                | Some td ->
                  let all_fields = match td.Types.type_fields with
                    | Some fs -> fs | None -> [] in
                  let field_vals = List.map (fun f_ref ->
                    let c_descr = c_env_lookup Ast.Unknown A.env.c_env f_ref in
                    let fname = Name.to_string (
                      Path.get_name c_descr.const_binding) in
                    match List.assoc_opt fname updated_map with
                      | Some e_val -> Output.flat [from_string " ("; exp inside_instance e_val; from_string ")"]
                      | None -> Output.flat [from_string " ("; exp inside_instance e; from_string "."; from_string fname; from_string ")"]
                  ) all_fields in
                  (* Use just the type name, not full type with params, to avoid
                     dot-notation parsing issues: wrapper.mk not wrapper a.mk *)
                  let type_name_str = match e_typ.Types.t with
                    | Types.Tapp (_, path) ->
                        let n0 = Name.add_lskip (Path.get_name path) in
                        let n = B.type_path_to_name n0 path in
                        Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n))
                    | _ -> assert false
                  in
                  Output.flat ([
                    ws skips; from_string "("; from_string type_name_str; from_string ".mk"
                  ] @ field_vals @ [
                    from_string ")"
                  ])
                | None ->
                  raise (Reporting_basic.err_general true (Typed_ast.exp_to_locn e)
                    "Lean backend: mutual record update could not find type definition")
              )
            else begin
              let body = flatten_newlines (flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (field_update inside_instance) (sep @@ from_string ",") fields) in
              let skips'' =
                if skips'' = Typed_ast.no_lskips then
                  from_string " "
                else
                  ws skips''
              in
                Output.flat [
                   ws skips; from_string "{ "; exp inside_instance e; ws skips'; from_string " with "; body; skips''; from_string " }"
                ]
            end
          | Case (_, skips, e, skips', cases, skips'') ->
            let case_sep _ = from_string " " in
            let has_vec = Seplist.exists (fun (p, _, _, _) -> pat_has_vector p) cases in
            (* Use multi-discriminant match for tuple scrutinees:
               match l1, l2 with | [], [] => ... instead of
               match (l1, l2) with | ([], []) => ...
               This lets Lean's termination checker see structural recursion.
               Only apply when ALL case arm patterns are P_tup or P_wild. *)
            let pat_is_tup_or_wild (p, _, _, _) = match p.term with
              | P_tup _ | P_wild _ -> true
              | P_paren (_, p', _) -> (match p'.term with P_tup _ | P_wild _ -> true | _ -> false)
              | _ -> false
            in
            let tup_arity = match C.exp_to_term e with
              | Tup (_, es, _) -> Seplist.length es
              | _ -> 0
            in
            let is_tuple_match =
              tup_arity > 0 && Seplist.for_all pat_is_tup_or_wild cases
            in
            let case_line' =
              if is_tuple_match then case_line_multi inside_instance tup_arity
              else case_line inside_instance
            in
            let body = flat @@ Seplist.to_sep_list_last Seplist.Optional case_line' case_sep cases in
            let match_suffix = if has_vec then from_string ".toList" else emp in
            let match_expr =
              if is_tuple_match then
                match C.exp_to_term e with
                | Tup (_, es, _) ->
                  Output.concat (from_string ", ") (List.map (exp inside_instance) (Seplist.to_list es))
                | _ -> exp inside_instance e
              else
                exp inside_instance e
            in
                Output.flat [
                  ws skips; from_string "match "; match_expr; match_suffix; from_string " with "; body; ws skips''
                ]
          | Infix (l, c, r) ->
              let trans e =
                if needs_parens (C.exp_to_term e) then
                  Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                else exp inside_instance e
              in
              let sep = from_string " " in
              begin
                match C.exp_to_term c with
                  | Constant cd ->
                    begin
                      (* In indreln antecedents (Prop context), == and != must use
                         propositional =/≠. This handles the Infix AST case;
                         the App case above handles decomposed forms like not(isEqual x y). *)
                      let c_descr = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
                      match !lean_prop_equality, check_beq_target_rep c_descr with
                      | true, Some is_eq ->
                        (* Parenthesize both sides to avoid chained = ambiguity *)
                        let l_out = Output.flat [from_string "("; trans l; from_string ")"] in
                        let r_out = Output.flat [from_string "("; trans r; from_string ")"] in
                        if is_eq then Output.flat [l_out; from_string "  =  "; r_out]
                        else Output.flat [l_out; meta_utf8 "  \xe2\x89\xa0  "; r_out]
                      | _ -> begin
                        let pieces = B.function_application_to_output (exp_to_locn e) trans true e cd [l; r] (use_ascii_rep_for_const cd.descr) in
                        Output.concat sep pieces
                      end
                    end
                  | _           ->
                    begin
                      let mapped = List.map trans [l; c; r] in
                      Output.concat sep mapped
                    end
              end
          | If (skips, test, skips', t, skips'', f) ->
              let cond =
                if needs_parens (C.exp_to_term test) then
                  Output.flat [from_string "("; exp inside_instance test; from_string ")"]
                else exp inside_instance test
              in
              Output.flat [
                ws skips; from_string "if";
                from_string " "; cond;
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
                      let name = lean_escape_keyword (Ulib.Text.to_string (Name.to_rope name)) in
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
          | Comp_binding (_, _, _, _, _, _, _, _, _) ->
              (* Set comprehension binding — not directly supported in Lean.
                 Library functions with comprehensions have Lean target reps
                 that bypass this code path. If reached, emit sorry. *)
              from_string "(sorry /- set comprehension binding not supported -/)"
          | Setcomp (_, _, _, _, _, _) ->
              from_string "(sorry /- set comprehension not supported -/)"
          | Nvar_e (skips, nvar) ->
            let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r "") (Nvar.to_rope nvar) in
              Output.flat [
                ws skips; nvar
              ]
          | VectorAcc (e, skips, nexp, skips') ->
              (* Parenthesize match/if/let/fun in function argument position *)
              let e_out =
                if needs_parens (C.exp_to_term e) then
                  Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                else exp inside_instance e
              in
              Output.flat [
                from_string "Vector.get "; e_out;
                from_string " "; src_nexp nexp; ws skips'
              ]
          | VectorSub (e, skips, nexp, skips', nexp', skips'') ->
              let e_out =
                if needs_parens (C.exp_to_term e) then
                  Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                else exp inside_instance e
              in
              Output.flat [
                from_string "Vector.slice "; e_out;
                from_string " "; src_nexp nexp;
                from_string " "; src_nexp nexp'; ws skips''
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
        let body =
          if needs_parens (C.exp_to_term e) then
            Output.flat [from_string "("; exp inside_instance e; from_string ")"]
          else exp inside_instance e
        in
        flatten_newlines (Output.flat [
          from_string "| "; def_pattern p; from_string " => "; body
        ])
    (* Multi-discriminant case line: unwrap P_tup pattern into comma-separated
       elements for match l1, l2, ... with | p1, p2, ... => body syntax.
       P_wild is expanded to arity-many wildcards: _ => _, _, ... *)
    and case_line_multi inside_instance arity (p, skips, e, l) =
        let body =
          if needs_parens (C.exp_to_term e) then
            Output.flat [from_string "("; exp inside_instance e; from_string ")"]
          else exp inside_instance e
        in
        let unwrap_tup p = match p.term with
          | P_tup (_, ps, _) ->
            Output.concat (from_string ", ") (List.map def_pattern (Seplist.to_list ps))
          | P_wild _ ->
            Output.concat (from_string ", ") (List.init arity (fun _ -> from_string "_"))
          | _ -> def_pattern p
        in
        let pat_out = match p.term with
          | P_paren (_, p', _) -> unwrap_tup p'
          | _ -> unwrap_tup p
        in
        flatten_newlines (Output.flat [
          from_string "| "; pat_out; from_string " => "; body
        ])
    and field_update inside_instance (fd, skips, e, _) =
      let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
      (* Flatten newlines in record field values to prevent multiline expressions
         (e.g., lambdas containing match) from breaking record { with } syntax. *)
      let value = flatten_newlines (exp inside_instance e) in
        Output.flat [
          name; ws skips; from_string " := "; value
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
      let style = if inside_instance then MatchArm else FunParam in
        Output.flat [
          from_string " "; (concat_str " " @@ List.map (pattern ~style) ps)
        ]
    and src_t_has_wild t =
      match t.term with
        | Typ_wild _ -> true
        | Typ_fn (t1, _, t2) -> src_t_has_wild t1 || src_t_has_wild t2
        | Typ_tup ts -> Seplist.exists src_t_has_wild ts
        | Typ_app (_, ts) -> List.exists src_t_has_wild ts
        | Typ_paren (_, t, _) -> src_t_has_wild t
        | _ -> false
    and pattern ~(style : pat_style) p =
      let self p = pattern ~style p in
      let bare p = pattern ~style:MatchArm p in
      match p.term with
        | P_wild skips ->
          let skips_out =
            if skips = Typed_ast.no_lskips then
              from_string " "
            else
              ws skips
          in
            (match style with
            | FunParam ->
              let t = C.t_to_src_t p.typ in
              Output.flat [from_string "("; skips_out; from_string "_ : "; pat_typ t; from_string ")"]
            | MatchArm ->
              Output.flat [skips_out; from_string "_"])
        | P_var v ->
            (match style with
            | FunParam ->
              let name = lskips_t_to_output v in
              let t = C.t_to_src_t p.typ in
              Output.flat [from_string "("; name; from_string " : "; pat_typ t; from_string ")"]
            | MatchArm ->
              name_var_output v)
        | P_lit l ->
            (match style, l.term with
            | FunParam, L_unit _ -> from_string "(_ : Unit)"
            | _ -> literal l)
        | P_as (skips, p, skips', (n, l), skips'') ->
          let name = name_var_output n in
            Output.flat [
              ws skips; name; from_string "@("; self p; from_string ")"; ws skips''
            ]
        | P_typ (skips, p, skips', t, skips'') ->
            (match style with
            | FunParam ->
              (* When source type has wildcards, use the resolved type from Lem's
                 type checker instead — Lean can't resolve partial wildcards like
                 `rel _ _` with autoImplicit=false *)
              let actual_t = if src_t_has_wild t then C.t_to_src_t p.typ else t in
              Output.flat [
                ws skips; from_string "("; bare p; ws skips'; from_string " :";
                ws skips''; pat_typ actual_t; from_string ")"
              ]
            | MatchArm ->
              Output.flat [
                ws skips; from_string "("; self p; from_string " : "; pat_typ t; from_string ")"; ws skips'
              ])
        | P_tup (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list self (sep @@ from_string ", ") ps in
            (match style with
            | FunParam ->
              Output.flat [ws skips; from_string "("; body; ws skips'; from_string ")"]
            | MatchArm ->
              Output.flat [ws skips; from_string "("; body; from_string ")"; ws skips'])
        | P_record (_, fields, _) ->
            print_and_fail p.locn "illegal record pattern in code extraction, should have been compiled away"
        | P_cons (p1, skips, p2) ->
            (match style with
            | FunParam ->
              Output.flat [
                from_string "("; bare p1; ws skips; from_string " :: "; bare p2; from_string ")"
              ]
            | MatchArm ->
              Output.flat [
                self p1; ws skips; from_string " :: "; self p2
              ])
        | P_var_annot (n, t) ->
            (match style with
            | FunParam ->
              let name = lskips_t_to_output n in
              Output.flat [from_string "("; name; from_string " : "; pat_typ t; from_string ")"]
            | MatchArm ->
              name_var_output n)
        | P_list (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional self (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_vector (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional self (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_vectorC _ ->
            raise (Reporting_basic.err_general true p.locn
              "Lean backend: vector concatenation patterns are not supported")
        | P_paren (skips, p, skips') ->
            (match style with
            | FunParam ->
              Output.flat [ws skips; from_string "("; self p; ws skips'; from_string ")"]
            | MatchArm ->
              Output.flat [from_string "("; ws skips; self p; ws skips'; from_string ")"])
        | P_const(cd, ps) ->
            let oL = B.pattern_application_to_output p.locn self cd ps (use_ascii_rep_for_const cd.descr) in
            concat (from_string " ") oL
        | P_backend(sk, i, _, ps) ->
            let name = Output.flat [ws sk;
              Ident.to_output (Term_const (false, true)) path_sep (Ident.replace_lskip i Typed_ast.no_lskips)]
            in
            concat (from_string " ") (name :: List.map self ps)
        | P_num_add ((name, l), skips, skips', k) ->
            let name = lskips_t_to_output name in
              Output.flat [
                ws skips; from_string "("; name; from_string " + "; from_string (Z.to_string k); from_string ")"
              ]
    and fun_pattern p = pattern ~style:FunParam p
    and def_pattern p = pattern ~style:MatchArm p
    and src_t_has_fn (t : src_t) : bool =
      match t.term with
        | Typ_fn _ -> true
        | Typ_tup ts -> Seplist.exists src_t_has_fn ts
        | Typ_app (id, ts) ->
          (* Check type arguments for functions *)
          List.exists src_t_has_fn ts ||
          (* Also check if the type itself is an abbreviation expanding to a function type.
             This catches cases like stateM 'a 'st = 'st -> maybe ('a * 'st) where the
             abbreviation hides a function type. *)
          (let l = Ast.Trans (false, "src_t_has_fn", None) in
           try
             let td = Types.type_defs_lookup l A.env.t_env id.descr in
             match td.Types.type_abbrev with
               | Some expanded_t ->
                 (* Check if the expanded type contains a function.
                    Use head_norm to fully expand nested abbreviations
                    (e.g., wrap = fn, fn = nat -> bool). *)
                 let rec types_t_has_fn (ty : Types.t) =
                   let ty = Types.head_norm A.env.t_env ty in
                   match ty.Types.t with
                     | Types.Tfn _ -> true
                     | Types.Ttup ts -> List.exists types_t_has_fn ts
                     | Types.Tapp (ts, _) -> List.exists types_t_has_fn ts
                     | _ -> false
                 in
                 types_t_has_fn expanded_t
               | None -> false
           with _ -> false)
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
    (* --- Type definition rendering ---
       Dispatch by type form:
       - Te_abbrev → type_def_abbreviation (Lean abbrev)
       - Te_record → type_def_record (Lean structure)
       - Te_variant, single type → type_def_variant (Lean inductive)
       - Te_variant, mutual types with equal params → type_def_variant (mutual block)
       - Te_variant, mutual types with unequal params → type_def_indexed
         (parameters promoted to indices, all types in Type 1 universe)
       After each inductive/structure, constructors are exported and
       BEq/Ord/Inhabited instances are generated. *)
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
        | (n, tyvars, path, (Te_record (_, _, fields, _) as ty),_) ->
            let (n', _) = n in
            let n' = B.type_path_to_name n' path in
            let name = Name.to_output (Type_ctor (false, false)) n' in
            let field_list = Seplist.to_list fields in
            let body = concat_str "\n" (List.map field field_list) in
            let tyvars' = type_def_type_variables tyvars in
            let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
            let deriving_clause = if texp_can_derive_beq ty then
              from_string "  deriving BEq, Ord\n"
            else emp in
              Output.flat [
                from_string "structure"; name; tyvar_sep; tyvars';
                from_string " where\n"; body; from_string "\n"; deriving_clause;
              ]
        | _ -> raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected type definition form")
    and type_def inside_module defs =
      (* Collect type names and their constructor names for "export" declarations.
         Using "export" instead of "open" ensures constructors are visible
         in files that import this module, not just in the defining file. *)
      let type_info = List.filter_map (fun ((n0, _), _, t_path, ty, _) ->
        match ty with
          | Te_abbrev _ -> None  (* Abbreviations don't create namespaces *)
          | Te_opaque ->
            (* Opaque types with target_rep become abbrevs — no namespace *)
            let l = Ast.Trans (false, "type_info", None) in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            (match Target.Targetmap.apply_target td.Types.type_target_rep
                    (Target.Target_no_ident Target.Target_lean) with
              | Some (Types.TYR_simple _) -> None
              | _ ->
                let n = B.type_path_to_name n0 t_path in
                Some (Name.to_string (Name.strip_lskip n), []))
          | _ ->
            (* Check if this type has a target_rep — if so, it becomes
               an abbrev and doesn't create a namespace *)
            let l = Ast.Trans (false, "type_info", None) in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            if Target.Targetmap.apply_target td.Types.type_target_rep
                 (Target.Target_no_ident Target.Target_lean) <> None then None
            else
            let n = B.type_path_to_name n0 t_path in
            let name_str = Name.to_string (Name.strip_lskip n) in
            let ctor_names = match ty with
              | Te_variant (_, ctors) ->
                Seplist.to_list_map (fun ((ctor_n, _), ctor_ref, _, _) ->
                  let cn = B.const_ref_to_name ctor_n false ctor_ref in
                  Name.to_string (Name.strip_lskip cn)
                ) ctors
              | _ -> []
            in
            Some (name_str, ctor_names)
      ) (Seplist.to_list defs) in
      let type_names = List.map fst type_info in
      (* Also register these for the auxiliary file (with namespace qualification) *)
      lean_auxiliary_opens := !lean_auxiliary_opens @ List.map lean_qualified_name type_names;
      let open_decls = flat (List.map (fun (name_str, ctor_names) ->
        if ctor_names = [] then
          (* Records/opaque types: just open *)
          from_string (String.concat "" ["\nopen "; name_str])
        else
          (* Inductive types: export constructors for cross-file visibility *)
          let ctors_str = String.concat " " ctor_names in
          from_string (String.concat "" ["\nexport "; name_str; " ("; ctors_str; ")"])
      ) type_info) in
      let n = Seplist.length defs in
      if n > 1 then
        (* Separate abbreviations from the mutual block — they are just type aliases
           and can't participate in mutual recursion. Emit them after the mutual block. *)
        let all_defs = Seplist.to_list defs in
        let is_abbrev_def (_, _, _, ty, _) = match ty with Te_abbrev _ -> true | _ -> false in
        let mutual_defs = List.filter (fun d -> not (is_abbrev_def d)) all_defs in
        let abbrev_defs = List.filter is_abbrev_def all_defs in
        (* Collect mutual type paths to check if abbreviations reference them *)
        let mutual_paths = List.filter_map (fun ((_, _), _, path, _, _) ->
          Some path
        ) mutual_defs in
        (* Split abbreviations: those referencing mutual types go after,
           others go before (they may be needed by the mutual types). *)
        let abbrev_references_mutual (_, _, _, ty, _) = match ty with
          | Te_abbrev (_, t) -> src_t_references_paths mutual_paths t
          | _ -> false
        in
        let abbrevs_before = List.filter (fun d -> not (abbrev_references_mutual d)) abbrev_defs in
        let abbrevs_after = List.filter abbrev_references_mutual abbrev_defs in
        let render_abbrev ((n0, _), tyvars, path, ty, _) = match ty with
          | Te_abbrev (skips, t) ->
            let n = B.type_path_to_name n0 path in
            let name = Name.to_output (Type_ctor (false, false)) n in
            let tyvars' = type_def_type_variables tyvars in
            let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
            Output.flat [
              from_string "\nabbrev"; name; tyvar_sep; tyvars';
              ws skips; from_string " := "; pat_typ t
            ]
          | _ -> assert false  (* unreachable: abbrev_defs is filtered to Te_abbrev only *)
        in
        let abbrevs_before_output = flat @@ List.map render_abbrev abbrevs_before in
        let abbrevs_after_output = flat @@ List.map render_abbrev abbrevs_after in
        let mutual_n = List.length mutual_defs in
        (* Note: mutual record names are pre-collected in lean_defs before the
           main fold_right, so we don't register them here. See lean_mutual_records
           pre-collection near lean_local_modules. *)
        let mutual_output =
          if mutual_n > 1 then
            let mutual_sep = Seplist.from_list_default None mutual_defs in
            (* Check if all types in mutual block have the same number of type params *)
            let param_counts = List.map (fun (_, ty_vars, _, _, _) ->
              List.length ty_vars
            ) mutual_defs in
            let all_same = match param_counts with
              | [] -> true
              | x :: xs -> List.for_all (fun y -> y = x) xs
            in
            if all_same then
              let body = flat @@ Seplist.to_sep_list (type_def_variant false) (sep @@ from_string "\ninductive") mutual_sep in
              Output.flat [ from_string "mutual\ninductive"; body; from_string "\nend" ]
            else
              let body = flat @@ Seplist.to_sep_list type_def_indexed (sep @@ from_string "\ninductive") mutual_sep in
              Output.flat [ from_string "mutual\ninductive"; body; from_string "\nend" ]
          else if mutual_n = 1 then
            let single_sep = Seplist.from_list_default None mutual_defs in
            let body = flat @@ Seplist.to_sep_list (type_def_variant true) (sep @@ from_string "\n") single_sep in
            Output.flat [ from_string "inductive"; body ]
          else
            emp  (* All were abbreviations *)
        in
        (* Generate accessor functions for record types in the mutual block.
           Lean 4 doesn't create .field projectors for inductives in mutual blocks,
           so we emit explicit defs to enable dot notation. *)
        let accessor_defs = flat @@ List.filter_map (fun ((n0, _), ty_vars_raw, path, ty, _) ->
          match ty with
            | Te_record (_, _, fields, _) ->
              let n = B.type_path_to_name n0 path in
              let type_name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
              let tv_decl = String.concat "" @@ List.map (fun tv ->
                let s = tnvar_to_string tv in
                match tv with
                  | Typed_ast.Tn_A _ -> String.concat "" [" {"; s; " : Type}"]
                  | Typed_ast.Tn_N _ -> String.concat "" [" {"; s; " : Nat}"]
              ) ty_vars_raw in
              let tv_applied = String.concat " " @@ List.map tnvar_to_string ty_vars_raw in
              let tv_sep = if List.length ty_vars_raw = 0 then "" else " " in
              let field_list = Seplist.to_list fields in
              let n_fields = List.length field_list in
              let accessors = List.mapi (fun i ((fname, _), f_ref, _, src_t) ->
                let field_name = B.const_ref_to_name fname false f_ref in
                let field_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip field_name)) in
                let pre_wildcards = String.concat "" (List.init i (fun _ -> " _")) in
                let post = if i < n_fields - 1 then " .." else "" in
                Output.flat [
                  from_string (String.concat "" [
                    "\n@[inline] def "; type_name; "."; field_str;
                    tv_decl;
                    " (self : "; type_name; tv_sep; tv_applied;
                    ") : "
                  ]);
                  pat_typ src_t;
                  from_string (String.concat "" [
                    " :=\n  match self with | .mk";
                    pre_wildcards; " "; field_str; post; " => "; field_str
                  ])
                ]
              ) field_list in
              Some (flat accessors)
            | _ -> None
        ) mutual_defs in
        (* Abbreviations that don't reference mutual types go BEFORE (they may be
           needed by the mutual types). Abbreviations that DO reference mutual types
           go AFTER (they alias types defined in the block). *)
        let before_sep = if abbrevs_before = [] then emp else from_string "\n" in
        Output.flat [ abbrevs_before_output; before_sep; mutual_output; abbrevs_after_output; open_decls; accessor_defs; from_string "\n" ]
      else
        (* Check if this type has a Lean target_rep type (TYR_simple).
           If so, emit abbrev instead of inductive — the type is defined
           in external Lean code. Works for both opaque types and types
           with constructors that have their own target_reps. *)
        let ((n0, _), tyvars, t_path, ty, _) = Seplist.hd defs in
        let target_rep_abbrev =
            let l = Ast.Trans (false, "type_def", None) in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            begin match Target.Targetmap.apply_target td.Types.type_target_rep
                    (Target.Target_no_ident Target.Target_lean) with
              | Some (Types.TYR_simple (_, _, target_ident)) ->
                (* Collect import for the type target rep's module *)
                let target_id_str = Ident.to_string target_ident in
                (match String.index_opt target_id_str '.' with
                  | Some dot_pos when dot_pos > 0 ->
                    let mod_name = String.sub target_id_str 0 dot_pos in
                    if String.length mod_name > 0 &&
                       Char.uppercase_ascii mod_name.[0] = mod_name.[0] &&
                       not (List.mem mod_name !lean_collected_imports) then
                      lean_collected_imports := mod_name :: !lean_collected_imports
                  | _ -> ());
                let name = B.type_path_to_name n0 t_path in
                let name_out = Name.to_output (Type_ctor (false, false)) name in
                let tyvars_out = type_def_type_variables tyvars in
                let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
                Some (Output.flat [
                  from_string "abbrev "; name_out; tyvar_sep; tyvars_out;
                  from_string " := ";
                  Ident.to_output (Type_ctor (false, true)) (r".") target_ident;
                  from_string "\n"
                ])
              | _ -> None
            end
        in
        match target_rep_abbrev with
          | Some abbrev_out -> abbrev_out
          | None ->
            let body = flat @@ Seplist.to_sep_list (type_def_variant true) (sep @@ from_string "\n") defs in
            Output.flat [ from_string "inductive"; body; open_decls; from_string "\n" ]
    and type_def_variant emit_deriving ((n0, l), ty_vars, t_path, ty, _) =
      let n = B.type_path_to_name n0 t_path in
      let name = Name.to_output (Type_ctor (false, false)) n in
      let ty_vars =
        List.map tnvar_to_variable ty_vars
      in
        match ty with
          | Te_opaque ->
              Output.flat [
                inductive ty_vars n; from_string " : Type where"
              ]
          | _ ->
            Output.flat [
              inductive ty_vars n; from_string " : Type"; tyexp emit_deriving name ty_vars ty
            ]
    and type_def_indexed ((n0, l), ty_vars, t_path, ty, _) =
      (* Emit type with indices instead of parameters, for heterogeneous mutual blocks.
         Parameters become indices: inductive v : (a : Type) → (b : Type) → Type 1 where *)
      let n = B.type_path_to_name n0 t_path in
      let name = Name.to_output (Type_ctor (false, false)) n in
      let ty_vars_list =
        List.map tnvar_to_variable ty_vars
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
      (* All types in a heterogeneous mutual block must live in the same universe.
         Since at least one type has indices (parameters promoted to indices),
         that type lives in Type 1, so ALL types must be Type 1. *)
      let universe = from_string "Type 1" in
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
        | Te_record (_, _, fields, _) ->
          (* Records in heterogeneous mutual blocks: emit as single-constructor
             indexed inductive with named fields.  Use the same (fname : type) →
             syntax as tyexp's Te_record case but prefix implicit type bindings
             (like constructor_indexed) since parameters are promoted to indices. *)
          let field_list = Seplist.to_list fields in
          let mk_args = flat @@ List.map (fun ((n, _), f_ref, _skips, t) ->
            let fname = Name.add_lskip (Name.strip_lskip (B.const_ref_to_name n false f_ref)) in
            Output.flat [
              from_string "(";
              Name.to_output Term_field fname;
              from_string " :"; pat_typ t;
              from_string ") → "
            ]
          ) field_list in
          let implicit_bindings =
            if List.length ty_vars_list = 0 then emp
            else
              let mapped = List.map (fun v ->
                match v with
                  | Tyvar x -> Output.flat [ from_string "{"; x; from_string " : Type} → " ]
                  | Nvar x -> Output.flat [ from_string "{"; x; from_string " : Nat} → " ]
              ) ty_vars_list in
              concat emp mapped
          in
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where\n";
            from_string "  | mk : "; implicit_bindings; mk_args;
            name; ty_vars_names_space; ty_vars_names
          ]
        | _ ->
          (* Te_abbrev is filtered out before reaching here; this catch-all
             handles any unexpected future type forms. *)
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
    and tyexp emit_deriving name ty_vars ty =
      match ty with
        | Te_opaque ->
            (* Unreachable: type_def_variant handles Te_opaque directly *)
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected Te_opaque in tyexp")
        | Te_abbrev _ ->
            (* Unreachable: def dispatches abbreviations to type_def_abbreviation *)
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected Te_abbrev in tyexp")
        | Te_record (_, _, fields, _) ->
            (* Records in mutual blocks: emit as single-constructor inductive
               (Lean 4 mutual blocks cannot contain structure definitions) *)
            let field_list = Seplist.to_list fields in
            let mk_args = flat @@ List.map (fun ((n, _), f_ref, _skips, t) ->
              let fname = Name.add_lskip (Name.strip_lskip (B.const_ref_to_name n false f_ref)) in
              Output.flat [
                from_string " (";
                Name.to_output Term_field fname;
                from_string " :"; pat_typ t;
                from_string ")"
              ]
            ) field_list in
            (* Build return type with applied type variables: e.g. "statement a" *)
            let ty_vars_applied =
              concat_str " " @@ List.map (fun v ->
                match v with
                  | Tyvar out -> out
                  | Nvar out -> out
              ) ty_vars
            in
            let ty_vars_sep = if List.length ty_vars = 0 then emp else from_string " " in
            Output.flat [
              from_string " where\n  | mk"; mk_args; from_string " : "; name; ty_vars_sep; ty_vars_applied
            ]
        | Te_variant (skips, ctors) ->
          let body = flat @@ Seplist.to_sep_list_first Seplist.Optional (constructor name ty_vars) (sep @@ from_string "\n") ctors in
          let deriving_clause = if emit_deriving && texp_can_derive_beq ty then
            from_string "\n  deriving BEq, Ord"
          else emp in
            Output.flat [
              from_string " where"; ws skips; from_string "\n"; body; deriving_clause
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
    and type_def_type_variables tvs =
      match tvs with
        | [] -> emp
        | [Typed_ast.Tn_A tv] -> from_string "(" ^ tyvar tv ^ from_string " : Type)"
        | tvs ->
          let mapped = List.map (fun t ->
            let name = tnvar_to_string t in
            let kind = match t with Typed_ast.Tn_A _ -> "Type" | Typed_ast.Tn_N _ -> "Nat" in
            Output.flat [from_string "("; from_string name; from_string " : "; from_string kind; from_string ")"]
          ) tvs
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
          (* Use type_app_to_output to handle target reps (e.g. set → List) *)
          let (remaining_ts, name_output) = B.type_app_to_output indreln_typ p ts in
          let args = concat_str " " @@ List.map indreln_typ remaining_ts in
          let args_space = if remaining_ts <> [] then from_string " " else emp in
            Output.flat [
              name_output; args_space; args
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
    and field ((n, _), f_ref, _skips, t) =
      let fname = Name.add_lskip (Name.strip_lskip (B.const_ref_to_name n false f_ref)) in
      Output.flat [
          from_string "  ";
          Name.to_output Term_field fname;
          from_string " :"; pat_typ t
      ]
    (* --- Instance generation ---
       For each type definition, generates:
       1. Inhabited instance (default constructor, or sorry for mutual/recursive types)
       2. BEq + Ord (derived via `deriving` if possible, sorry-based otherwise)
       3. SetType / Eq0 / Ord0 instances (with [BEq]/[Ord] constraints for parameterized types)
       Mutual types use find_safe_ctor_for_mutual to avoid self-referential defaults.
       Library opaque types (phantom types like ty1..ty4096) skip instance generation. *)
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
            let name = from_string (tnvar_to_string t) in
            match t with
              | Typed_ast.Tn_A _ ->
                Output.flat [
                  from_string " {"; name; from_string " : Type}";
                  from_string " [Inhabited "; name; from_string "]"
                ]
              | Typed_ast.Tn_N _ ->
                Output.flat [
                  from_string " {"; name; from_string " : Nat}"
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
        | Te_variant _ ->
            (* Unreachable: generate_inhabited_instance handles Te_variant
               directly via find_safe_ctor_for_mutual before calling this function *)
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: Te_variant in generate_default_value_texp is unreachable")
    (* Render a constructor call for an Inhabited default value *)
    and render_ctor_default ((ctor_name, _), ctor_ref, _, src_ts) =
      let n = B.const_ref_to_name ctor_name false ctor_ref in
      let ys = Seplist.to_list src_ts in
      let mapped = List.map default_value_inhabited ys in
      let sep = if List.length mapped = 0 then emp else from_string " " in
      let mapped_out = concat_str " " mapped in
      let o = lskips_t_to_output n in
        Output.flat [o; sep; mapped_out]
    (* Variant for mutual def blocks: direct references to mutual types use
       TypeName.default_inhabited instead of default (which needs Inhabited
       instances that don't exist yet inside the mutual def block). *)
    and default_value_inhabited_mutual mutual_name_map (s : src_t) : Output.t =
      match s.term with
        | Typ_app (id, _) ->
          (match List.assoc_opt id.descr mutual_name_map with
            | Some type_name_str -> from_string (String.concat "" [type_name_str; ".default_inhabited"])
            | None -> from_string "default")
        | Typ_paren (_, src_t, _)
        | Typ_with_sort (src_t, _) -> default_value_inhabited_mutual mutual_name_map src_t
        | Typ_tup seplist ->
            let src_ts = Seplist.to_list seplist in
            let mapped = List.map (default_value_inhabited_mutual mutual_name_map) src_ts in
              Output.flat [from_string "("; concat_str ", " mapped; from_string ")"]
        | Typ_fn (dom, _, rng) ->
            let v = generate_fresh_name () in
              Output.flat [
                from_string "(fun ("; from_string v; from_string " : "; pat_typ dom;
                from_string ") => "; default_value_inhabited_mutual mutual_name_map rng; from_string ")"
              ]
        | _ -> from_string "default"
    and render_ctor_default_mutual mutual_name_map ((ctor_name, _), ctor_ref, _, src_ts) =
      let n = B.const_ref_to_name ctor_name false ctor_ref in
      let ys = Seplist.to_list src_ts in
      let mapped = List.map (default_value_inhabited_mutual mutual_name_map) ys in
      let sep = if List.length mapped = 0 then emp else from_string " " in
      let mapped_out = concat_str " " mapped in
      let o = lskips_t_to_output n in
        Output.flat [o; sep; mapped_out]
    (* Check if a src_t is directly one of the mutual types (not wrapped
       in List, Option, etc.). Used for Inhabited generation: indirect
       references through containers are safe because List.default = [],
       Option.default = none, etc. — they don't evaluate the element's default. *)
    and src_t_is_directly_mutual mutual_paths (s : src_t) : bool =
      match s.term with
        | Typ_app (id, _) ->
          List.exists (fun p -> Path.compare p id.descr = 0) mutual_paths
        | Typ_paren (_, t, _) -> src_t_is_directly_mutual mutual_paths t
        | Typ_with_sort (t, _) -> src_t_is_directly_mutual mutual_paths t
        | _ -> false
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
    (* Compute whether to skip Inhabited for this type (abbreviations, types with target_rep) *)
    and skip_inhabited_for_type t path =
      match t with
        | Te_abbrev _ -> true
        | Te_opaque ->
          let l = Ast.Trans (false, "generate_inhabited_instance", None) in
          let td = Types.type_defs_lookup l A.env.t_env path in
          Target.Targetmap.apply_target td.Types.type_target_rep
            (Target.Target_no_ident Target.Target_lean) <> None
        | _ ->
          let l = Ast.Trans (false, "generate_inhabited_instance", None) in
          let td = Types.type_defs_lookup l A.env.t_env path in
          Target.Targetmap.apply_target td.Types.type_target_rep
            (Target.Target_no_ident Target.Target_lean) <> None
    (* Compute the default value expression for an Inhabited instance.
       mutual_name_map: (Path.t * string) list mapping mutual type paths to their
       Lean names. When non-empty, uses TypeName.default_inhabited for mutual type
       args (for use inside mutual def blocks where Inhabited instances don't exist yet). *)
    and inhabited_default_expr ?(mutual_name_map=[]) mutual_paths ((name, _), tnvar_list, path, t, _) : Output.t =
      if tnvar_list = [] then
        let render_ctor = if mutual_name_map = [] then render_ctor_default
          else render_ctor_default_mutual mutual_name_map in
        match t with
          | Te_variant (_, seplist) ->
            let ctors = Seplist.to_list seplist in
            (match find_safe_ctor_for_mutual mutual_paths ctors with
              | Some ctor -> render_ctor ctor
              | None ->
                let safe_indirect = List.find_opt (fun (_, _, _, src_ts) ->
                  let args = Seplist.to_list src_ts in
                  not (List.exists (src_t_is_directly_mutual [path]) args)
                ) ctors in
                match safe_indirect with
                  | Some ctor -> render_ctor ctor
                  | None -> from_string "sorry /- directly self-referential type -/")
          | Te_record (_, _, fields, _) when List.length mutual_paths > 1 ->
            let field_list = Seplist.to_list fields in
            let default_fn = if mutual_name_map = [] then default_value_inhabited
              else default_value_inhabited_mutual mutual_name_map in
            let field_defaults = List.map (fun (_, _, _, src_t) -> default_fn src_t) field_list in
            let type_name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
            Output.flat [from_string type_name; from_string ".mk "; concat_str " " field_defaults]
          | _ -> generate_default_value_texp t
      else
        (* Parameterized types: try nullary constructors first. A nullary ctor
           like FNil needs no type variable values, so no [Inhabited a] constraint
           is required. Only fall back to sorry if no nullary ctor exists. *)
        match t with
          | Te_variant (_, seplist) ->
            let ctors = Seplist.to_list seplist in
            let render_ctor = if mutual_name_map = [] then render_ctor_default
              else render_ctor_default_mutual mutual_name_map in
            let nullary = List.find_opt (fun (_, _, _, src_ts) ->
              Seplist.to_list src_ts = []) ctors in
            (match nullary with
              | Some ctor -> render_ctor ctor
              | None -> from_string "sorry")
          | _ -> from_string "sorry"
    (* Type variable binding + type args for Inhabited instance header *)
    and inhabited_type_parts tnvar_list =
      let tnvar_list' =
        if tnvar_list = [] then emp
        else
          let tvs = List.map (fun tv ->
            match tv with
            | Typed_ast.Tn_A (_, r, _) -> Types.Ty (Tyvar.from_rope r)
            | Typed_ast.Tn_N (_, r, _) -> Types.Nv (Nvar.from_rope r)
          ) tnvar_list in
          let_type_variables true (Types.TNset.of_list tvs)
      in
      let tnvar_names = concat_str " " @@ List.map (fun x -> from_string (tnvar_to_string x)) tnvar_list in
      let type_args =
        if List.length tnvar_list = 0 then emp
        else Output.flat [from_string " "; tnvar_names]
      in
      (tnvar_list', type_args)
    (* Generate a single Inhabited instance (non-mutual or single-type blocks) *)
    and generate_inhabited_instance mutual_paths (((name, _), tnvar_list, path, t, _) as td) : Output.t =
      if skip_inhabited_for_type t path then emp
      else
      let name_out = lskips_t_to_output (B.type_path_to_name name path) in
      let default = inhabited_default_expr mutual_paths td in
      let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
        Output.flat [
          from_string "instance"; tnvar_list'; from_string " : Inhabited ("; name_out;
          type_args;
          from_string ") where\n  default := "; default;
        ]
    (* Generate mutual def + instance pairs for Inhabited on mutual type blocks.
       Uses `mutual def ... end` so forward references between defaults are allowed,
       then non-mutual `instance` declarations referencing those defs. *)
    and generate_inhabited_mutual mutual_paths ts_list : Output.t =
      (* Filter to types that need Inhabited *)
      let active = List.filter (fun (_, _, path, t, _) ->
        not (skip_inhabited_for_type t path)) ts_list in
      if active = [] then emp
      else if List.length active = 1 then
        (* Single type remaining: no need for mutual def *)
        generate_inhabited_instance mutual_paths (List.hd active)
      else
      (* Build path → type name mapping for mutual def references.
         Inside the mutual def block, we can't use `default` (Inhabited not defined yet),
         so direct mutual type args use TypeName.default_inhabited instead. *)
      let mutual_name_map = List.map (fun ((name, _), _, path, _, _) ->
        let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
        (path, type_name_str)
      ) active in
      (* Phase 1: mutual def block with default values *)
      let defs = List.map (fun (((name, _), tnvar_list, path, _, _) as td) ->
        let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
        let name_out = lskips_t_to_output (B.type_path_to_name name path) in
        let default = inhabited_default_expr ~mutual_name_map mutual_paths td in
        let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
        Output.flat [
          from_string "def "; from_string type_name_str; from_string ".default_inhabited";
          tnvar_list'; from_string " : "; name_out; type_args;
          from_string " := "; default;
        ]
      ) active in
      (* Phase 2: instance declarations referencing the mutual defs *)
      let instances = List.map (fun ((name, _), tnvar_list, path, _, _) ->
        let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
        let name_out = lskips_t_to_output (B.type_path_to_name name path) in
        let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
        Output.flat [
          from_string "instance"; tnvar_list'; from_string " : Inhabited ("; name_out;
          type_args;
          from_string ") where\n  default := "; from_string type_name_str;
          from_string ".default_inhabited";
        ]
      ) active in
      Output.flat [
        from_string "mutual\n";
        concat_str "\n" defs;
        from_string "\nend\n";
        concat_str "\n" instances;
      ]
    and generate_beq_ord_instances ?(is_type1=false) ?(emit_deriving=true) ((name, _), tnvar_list, path, t, _) : Output.t =
      (* Skip instance generation for abbreviations and opaque types with target reps
         (they inherit instances from the target/aliased type). *)
      let skip_instances = match t with
        | Te_abbrev _ -> true
        | _ ->
          (* Skip for any type with a Lean target_rep (opaque or not) —
             they become abbrevs and inherit instances from the target type. *)
          let l = Ast.Trans (false, "generate_beq_ord_instances", None) in
          let td = Types.type_defs_lookup l A.env.t_env path in
          Target.Targetmap.apply_target td.Types.type_target_rep
            (Target.Target_no_ident Target.Target_lean) <> None
      in
      if skip_instances then emp
      else
      match t with
        | Te_abbrev _ -> emp  (* unreachable due to skip_instances *)
        | _ ->
          let n = B.type_path_to_name name path in
          let o = lskips_t_to_output n in
          let tnvar_names = concat_str " " @@ List.map (fun x -> from_string (tnvar_to_string x)) tnvar_list in
          let type_args =
            if List.length tnvar_list = 0 then emp
            else Output.flat [from_string " "; tnvar_names]
          in
          (* If the type uses deriving BEq, Ord (emitted by tyexp), skip sorry
             BEq/Ord instances. Mutual types can't use deriving (emit_deriving=false). *)
          let has_deriving = emit_deriving && texp_can_derive_beq t in
          let beq_instance, ord_instance =
            if has_deriving then (emp, emp)
            else begin
              (* Standalone BEq instance without [Inhabited] constraint.
                 Ord extends BEq in Lean 4, but Ord instances require [Inhabited a]
                 (since we use sorry for the compare body and Inhabited for the type).
                 Lem-sourced Eq instances may not have [Inhabited], so they need
                 a BEq that's available unconditionally. *)
              let bare_tvs = concat emp @@ List.map (fun t ->
                let name = tnvar_to_string t in
                let kind = match t with Typed_ast.Tn_A _ -> "Type" | Typed_ast.Tn_N _ -> "Nat" in
                Output.flat [from_string " {"; from_string name; from_string " : "; from_string kind; from_string "}"]
              ) tnvar_list in
              (* Low priority so hand-written BEq instances can override sorry *)
              (Output.flat [
                from_string "\ninstance (priority := low)"; bare_tvs; from_string " : BEq ("; o;
                type_args;
                from_string ") where\n  beq _ _ := sorry";
              ],
              (* Ord is universe-polymorphic so it works for Type 1 too.
                 Use bare_tvs (no [Inhabited]) since compare := sorry doesn't need it.
                 This lets downstream types use 'deriving Ord' without extra constraints. *)
              Output.flat [
                from_string "\ninstance (priority := low)"; bare_tvs; from_string " : Ord ("; o;
                type_args;
                from_string ") where\n  compare _ _ := sorry";
              ])
            end
          in
          (* SetType/Eq0/Ord0 are defined for (a : Type) only, skip for Type 1 *)
          if is_type1 then Output.flat [beq_instance; ord_instance]
          else
            (* SetType/Eq0/Ord0: use real implementations when possible.
               For types with deriving BEq/Ord, bridge to the derived instances.
               For types without, use sorry (can't derive or bridge). *)
            let bare_tvs_all = concat emp @@ List.map (fun t ->
              let name = tnvar_to_string t in
              let kind = match t with Typed_ast.Tn_A _ -> "Type" | Typed_ast.Tn_N _ -> "Nat" in
              Output.flat [from_string " {"; from_string name; from_string " : "; from_string kind; from_string "}"]
            ) tnvar_list in
            (* SetType/Eq0/Ord0: use real implementations for monomorphic types
               with deriving (no constraint propagation issue). For parameterized
               types or non-deriving types, use sorry to avoid constraint issues. *)
            let (settype_body, eq0_body, ord0_body) =
              if has_deriving && tnvar_list = [] then
                (* Monomorphic + deriving: bridge to derived BEq/Ord *)
                ("setElemCompare := defaultCompare",
                 "isEqual x y := x == y\n  isInequal x y := !(x == y)",
                 "compare := defaultCompare\n  isLess := defaultLess\n  isLessEqual := defaultLessEq\n  isGreater := defaultGreater\n  isGreaterEqual := defaultGreaterEq")
              else
                (* Parameterized or non-deriving: sorry to avoid constraint propagation *)
                ("setElemCompare _ _ := sorry",
                 "isEqual _ _ := sorry\n  isInequal _ _ := sorry",
                 "compare _ _ := sorry\n  isLess _ _ := sorry\n  isLessEqual _ _ := sorry\n  isGreater _ _ := sorry\n  isGreaterEqual _ _ := sorry")
            in
            let instance_tvs = bare_tvs_all
            in
            let inst_kw = if has_deriving && tnvar_list = []
              then "\ninstance"  (* Real implementations — default priority *)
              else "\ninstance (priority := low)"  (* Sorry — overridable *)
            in
            Output.flat [
              beq_instance;
              ord_instance;
              from_string inst_kw; instance_tvs; from_string " : Lem_Basic_classes.SetType ("; o;
              type_args;
              from_string ") where\n  "; from_string settype_body;
              from_string inst_kw; instance_tvs; from_string " : Lem_Basic_classes.Eq0 ("; o;
              type_args;
              from_string ") where\n  "; from_string eq0_body;
              from_string inst_kw; instance_tvs; from_string " : Lem_Basic_classes.Ord0 ("; o;
              type_args;
              from_string ") where\n  "; from_string ord0_body;
            ]
    and generate_default_values ts : Output.t =
      let ts = Seplist.to_list ts in
      (* In library modules, skip instance generation for opaque types
         (zero-constructor inductives like phantom types ty1..ty4096).
         These types carry only type-level information (e.g., bit widths
         via Size) and are never used as data — sorry-based instances are
         useless and produce compiler warnings.
         In user modules, opaque types (e.g., tid, location in cmm.lem) may
         appear as constructor arguments, so downstream types need their
         BEq/Ord instances for deriving to work. *)
      let is_lib = is_library_module !lean_current_module_name in
      let ts = if is_lib then List.filter (fun (_, _, _, t, _) -> t <> Te_opaque) ts else ts in
      (* Treat each single type like a mutual block of one, so self-referential
         constructors (e.g. Unop : op → op0 → op1 → op1) are detected and
         avoided when generating the Inhabited instance. *)
      let mapped = List.map (fun (((_, _), _, path, _, _) as t) ->
        generate_inhabited_instance [path] t) ts in
      let beq_instances = List.map generate_beq_ord_instances ts in
        Output.flat [concat_str "\n" mapped; concat emp beq_instances]
    and generate_default_values_mutual ts : Output.t =
      let ts_list = Seplist.to_list ts in
      let is_lib = is_library_module !lean_current_module_name in
      let ts_list = if is_lib then List.filter (fun (_, _, _, t, _) -> t <> Te_opaque) ts_list else ts_list in
      (* Filter out abbreviations for mutual_paths, is_type1, and emit_deriving decisions.
         Abbreviations don't participate in mutual recursion or instance generation. *)
      let non_abbrev = List.filter (fun (_, _, _, t, _) ->
        match t with Te_abbrev _ -> false | _ -> true) ts_list in
      let mutual_paths = List.map (fun ((_, _), _, path, _, _) -> path) non_abbrev in
      (* For mutual blocks with >1 type, use mutual def + instance to allow
         forward references between Inhabited defaults. Cyclic dependencies
         between types (common in large mutual blocks like Cabs.lean) make
         topological sorting impossible. mutual def solves this. *)
      let inhabited_output =
        if List.length non_abbrev > 1 then
          generate_inhabited_mutual mutual_paths ts_list
        else
          let mapped = List.map (generate_inhabited_instance mutual_paths) ts_list in
          concat_str "\n" mapped
      in
      (* Check if the non-abbreviation types have heterogeneous param counts *)
      let param_counts = List.map (fun (_, ty_vars, _, _, _) -> List.length ty_vars) non_abbrev in
      let is_type1 = match param_counts with
        | [] -> false
        | x :: xs -> not (List.for_all (fun y -> y = x) xs)
      in
      (* If only 1 non-abbreviation type remains, it was rendered with deriving
         (not as a mutual block), so emit_deriving:true to avoid duplicate instances. *)
      let emit_deriving = List.length non_abbrev <= 1 in
      let beq_instances = List.map (generate_beq_ord_instances ~is_type1 ~emit_deriving) ts_list in
        Output.flat [inhabited_output; from_string "\n"; concat emp beq_instances]
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

    (* Main definition processor: emits def output with location comments.
       Intentionally parallel to defs_extra below — they share the module
       setup but differ in which method they call (C.def vs C.def_extra)
       and whether location comments are prepended. Unifying them would
       require first-class modules which adds more complexity than the
       duplication costs. *)
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
    (* Auxiliary file processor: emits def_extra output without location comments. *)
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

    (* --- Import and namespace management ---
       Library modules: wrapped in 'namespace Lem_ModuleName ... end' with imports at top.
       User modules: no namespace wrapper; automatically open all transitive library
       namespaces so types/classes from Pervasives etc. are in scope.
       Abbrev definitions may be deferred (lean_pending_abbrevs) until after their
       dependencies are defined (e.g., abbrev mword after class Size). *)
    let lean_defs ((ds : def list), end_lex_skips) =
      lean_auxiliary_opens := [];
      lean_namespace_stack := [];
      lean_collected_imports := [];
      lean_pending_abbrevs := [];
      (* Set callback for per-file CR_simple import collection *)
      Backend_common.on_cr_simple_applied := collect_cr_simple_import;
      (* Note: lean_mutual_records is NOT reset — it accumulates across files
         so that cross-file record updates on mutual-block records are detected. *)
      lean_deferred_opens := [];
      (* Pre-collect local module names before main processing, because
         defs uses fold_right (processes last-to-first). Without this,
         'open Operators' would be processed before 'module Operators',
         causing a spurious import. *)
      (* Recursively collect local module names including nested ones *)
      let rec collect_local_modules (ds : def list) : string list =
        List.concat_map (fun (((d, _), _, _) : def) ->
          match d with
          | Module (_, (name, _), _, _, _, defs, _) ->
            let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
            name_str :: collect_local_modules defs
          | _ -> []
        ) ds
      in
      lean_local_modules := collect_local_modules ds;
      (* Pre-collect mutual record type names. Type_def blocks with >1 member
         that contain Te_record entries will render records as inductives.
         We need this list before defs runs (fold_right = last-to-first). *)
      lean_mutual_records := !lean_mutual_records @ List.concat_map (fun (((d, _), _, _) : def) ->
        match d with
        | Type_def (_, defs) when Seplist.length defs > 1 ->
            let all = Seplist.to_list defs in
            let non_abbrev = List.filter (fun (_, _, _, ty, _) ->
              match ty with Te_abbrev _ -> false | _ -> true
            ) all in
            if List.length non_abbrev > 1 then
              List.filter_map (fun (_, _, path, ty, _) ->
                match ty with
                  | Te_record _ -> Some path
                  | _ -> None
              ) non_abbrev
            else []
        | _ -> []
      ) ds;
      let mod_name = !lean_current_module_name in
      let ns_name = lean_ns_name mod_name in
      let is_library = ns_name <> mod_name in
      (* For library modules, push the top-level namespace so that
         lean_qualified_name returns qualified names (e.g. "Lem_Basic_classes.Eq0"
         instead of bare "Eq0"). Auxiliary files need these qualified opens
         since they don't have the namespace wrapper. *)
      if is_library then
        lean_namespace_stack := [ns_name];
      let lean_defs = defs false false ds in
      (* Drain any deferred abbrevs (e.g., abbrev mword after class Size) *)
      let deferred = Output.flat (List.rev !lean_pending_abbrevs) in
      lean_pending_abbrevs := [];
      let lean_defs = lean_defs ^ deferred in
      let lean_defs_extra = defs_extra false false ds in
      (* Ensure LemLib.Pervasives is always imported for non-library modules.
         This guarantees the standard namespace opens (Lem_Basic_classes, etc.)
         are available for auto-generated instances even when the source .lem file
         doesn't explicitly import Pervasives (e.g., linux.lem). *)
      let _ = if not is_library &&
                not (List.mem "LemLib.Pervasives" !lean_collected_imports) then
        lean_collected_imports := "LemLib.Pervasives" :: !lean_collected_imports
      in
      (* Imports for target_rep references are collected per-file during rendering:
         - Function CR_simple target reps: via Backend_common.on_cr_simple_applied callback
         - Type TYR_simple target reps: directly in type_def_variant
         This ensures each file only imports modules it actually references. *)
      (* Prepend collected imports (deduplicated, in order) to main body *)
      let imports = List.rev !lean_collected_imports in
      let seen = Hashtbl.create 16 in
      let unique_imports = List.filter (fun m ->
        if Hashtbl.mem seen m then false
        else (Hashtbl.add seen m true; true)
      ) imports in
      let imports_output = Output.flat (List.map (fun m ->
        from_string (String.concat "" ["import "; m; "\n"])
      ) unique_imports) in
      let ns_start = if is_library then
        from_string (String.concat "" ["\nnamespace "; ns_name; "\n"])
      else emp in
      let ns_end = if is_library then
        from_string (String.concat "" ["\nend "; ns_name; "\n"])
      else emp in
      (* For non-library modules, open all imported library namespaces so that
         class/type names from transitive dependencies are in scope.
         This is needed because Lean namespaces don't re-export opens.
         We scan the imports collected by THIS file and open the corresponding
         library namespaces. For transitive deps that come through Pervasives,
         we derive all library namespaces from the module environment. *)
      let transitive_opens = if not is_library then begin
        let all_imports = List.rev !lean_collected_imports in
        let has_pervasives = List.exists (fun m ->
          m = "LemLib.Pervasives" || m = "LemLib.Pervasives_extra"
        ) all_imports in
        if has_pervasives then
          (* Pervasives imports all core library modules; open their namespaces.
             Also import Pervasives_extra for bridge instances (NumAdd → Add etc.).
             Derive the list of library namespaces from the module environment
             (all modules with a Coq rename are library modules). *)
          let has_pervasives_extra = List.exists (fun m ->
            m = "LemLib.Pervasives_extra"
          ) all_imports in
          let extra_import = if has_pervasives_extra then emp
            else from_string "import LemLib.Pervasives_extra\n" in
          let has_bridges = List.exists (fun m ->
            m = "LemLib.Bridges"
          ) all_imports in
          let bridges_import = if has_bridges then emp
            else from_string "import LemLib.Bridges\n" in
          let lib_namespaces = Types.Pfmap.fold (fun acc _path md ->
            let has_coq_rename =
              Target.Targetmap.apply_target md.Typed_ast.mod_target_rep
                (Target.Target_no_ident Target.Target_coq) <> None in
            if has_coq_rename then begin
              let mod_name = Path.to_string md.Typed_ast.mod_binding in
              let lean_mod = String.concat "" ["LemLib."; String.capitalize_ascii mod_name] in
              let ns = lean_ns_name lean_mod in
              if List.mem ns acc then acc else ns :: acc
            end else acc
          ) [] A.env.e_env in
          let lib_namespaces = List.rev lib_namespaces in
          Output.flat (extra_import :: bridges_import :: List.map (fun ns ->
            from_string (String.concat "" ["open "; ns; "\n"])
          ) lib_namespaces)
        else
          (* Just open namespaces for direct imports *)
          let ns_list = List.filter_map (fun m ->
            let ns = lean_ns_name m in
            if ns <> m then Some ns else None
          ) all_imports in
          Output.flat (List.map (fun ns ->
            from_string (String.concat "" ["open "; ns; "\n"])
          ) ns_list)
      end else emp in
      (* Emit open statements for type/class namespaces so auxiliary file
         can reference constructors and class methods unqualified *)
      let opens = List.map (fun name_str ->
        from_string (String.concat "" ["open "; name_str; "\n"])
      ) !lean_auxiliary_opens in
      let opens_output = Output.flat opens in
        ((to_rope (r"\"") lex_skip need_space @@ imports_output ^ transitive_opens ^ ns_start ^ lean_defs ^ ns_end ^ ws end_lex_skips),
          to_rope (r"\"") lex_skip need_space @@ transitive_opens ^ opens_output ^ lean_defs_extra ^ ws end_lex_skips)
    ;;
  end
