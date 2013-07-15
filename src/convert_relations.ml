(* Converting a relation *)

open Typed_ast
open Types
open Util
open Typed_ast_syntax

module Converter(C : Exp_context) = struct

module C = Exps_in_context(C)
open C

module Nmap = Typed_ast.Nfmap
module Nset = Nmap.S

let loc_trans s l = Ast.Trans(s, Some(l))

let is_true l = match l.term with
  | L_true _ -> true
  | _ -> false

let r = Ulib.Text.of_latin1
let mk_string_path ns n = Path.mk_path (List.map (fun s -> Name.from_rope (r s)) ns) (Name.from_rope (r n))
let and_path = mk_string_path ["Pervasives"] "&&"

let mk_option ty = 
  { Types.t = Types.Tapp([ty], mk_string_path ["Pervasives"] "option") } 

let remove_option ty = 
  match ty.t with
    | Types.Tapp([ty], _) -> ty
    | _ -> failwith "???"

let path_to_string_list p = 
  let (mp,n) = Path.to_name_list p in
  (List.map Name.to_string mp, Name.to_string n)

let mk_const_from_path env l path inst = 
  let (mp,n) = path_to_string_list path in
  mk_const_exp env l mp n inst


let names_get_constructor env mp n = 
  let env' = lookup_env env mp in
  let cname = Name.to_string n in
  match Nfmap.apply env'.v_env n with
    | Some(Constr d) -> d
    | _ -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal(Ast.Unknown, "names_get_constructor env did not contain constructor!" ^ cname)))

let get_constructor env mp n = 
    names_get_constructor env (List.map (fun n -> (Name.from_rope (r n))) mp) (Name.from_rope (r n))

let get_constr_id l env mp n tys =
  { id_path = Id_none None;
    id_locn = l;
    descr = get_constructor env mp n;
    instantiation = tys }

let mk_constr_exp env mp n tys args = 
  let l = Ast.Trans ("mk_constr_exp", None) in
  let c = get_constr_id l env mp n tys in
  List.fold_left (fun fn arg -> mk_app l fn arg None) (mk_constr l c None) args

let mk_pconstr_pat env mp n tys args = 
  let l = Ast.Trans ("mk_pconstr_pat", None) in
  let c = get_constr_id l env mp n tys in
  mk_pconstr l c args None

module LemOptionMonad = struct

  let mk_none env ty = mk_constr_exp env ["Pervasives"] "None" [ty] [] 
  let mk_some env e = mk_constr_exp env ["Pervasives"] "Some" [exp_to_typ e] [e]
  let mk_pnone env ty = mk_pconstr_pat env ["Pervasives"] "None" [ty] []
  let mk_psome env p = mk_pconstr_pat env ["Pervasives"] "Some" [p.typ] [p]
    
  let mk_bind env call pat code = 
    let l = Ast.Trans ("mk_bind", None) in
    mk_case_exp false l call
      [(mk_psome env pat, code);
       (mk_pwild l None (exp_to_typ call), mk_none env (remove_option (exp_to_typ code)))]
      (exp_to_typ code)
      
  let mk_cond env cond code = 
    let l = Ast.Trans ("mk_cond", None) in
    mk_if_exp l cond code (mk_none env (remove_option (exp_to_typ code)))

end


let is_and e = match C.exp_to_term e with
  | Constant c -> Path.compare c.descr.const_binding and_path = 0
  | _ -> false

(* Splits on infix (&&) : ((a && b) && (c && d)) && true -> [a;b;c;d] *)
let rec split_and (e : exp) = match C.exp_to_term e with
  | Infix(e1, op_and, e2) when is_and op_and ->
    split_and e1 @ split_and e2
  | Lit lit_true when is_true lit_true -> []
  | Paren(_,e,_) -> split_and e
  | Typed(_,e,_,_,_) -> split_and e
  | _ -> [e]

(* 
  Group rules by output relation
*)

type ruledescr = {
  rule_name : Name.t;
  rule_vars : (Name.t * Types.t) list;
  rule_conds : exp list;
  rule_args : exp list;
  rule_loc : Ast.l;
} 

type reldescr = {
  rel_name : Name.t;
  rel_type : typschm;
  rel_argtypes : Types.t list;
  rel_witness : Name.t option;
  rel_check : Name.t option;
  rel_indfns : (Name.t * (mode * bool * output_type)) list;
  rel_rules : ruledescr list;
  rel_loc : Ast.l;
}

type relsdescr = reldescr Nfmap.t


let mk_list_type ty = 
  { Types.t = Types.Tapp([ty], Path.listpath) }

let map_option f = function
  | Some(x) -> Some(f x)
  | None -> None

let to_in_out (typ : src_t) : input_or_output = 
  match typ.term with
    | Typ_app({id_path = p}, []) ->
      begin match p with
        | Id_some(i) -> 
          begin match Name.to_string (Name.strip_lskip (Ident.get_name i)) with
            | "input" -> I
            | "output" -> O
            | s -> raise (Invalid_argument ("to_in_out: "^s))
          end
        | _ -> raise (Invalid_argument "to_in_out")
      end
    | _ -> raise (Invalid_argument "to_in_out")

let default_out_mode = Out_pure

let rec src_t_to_mode (typ : src_t) : mode * bool * output_type =
  match typ.term with
    | Typ_paren(_,t,_) -> src_t_to_mode t
    | Typ_fn(x1,_,x2) -> 
      let (mode, wit, out) = src_t_to_mode x2 in
      (to_in_out x1::mode, wit, out)
    | Typ_app({id_path = p },args) ->
      begin 
        try ([to_in_out typ], false, default_out_mode)
        with Invalid_argument _ -> 
          begin match p with
            | Id_some(i) ->
              let n = Name.to_string (Name.strip_lskip (Ident.get_name i)) in
              begin match n with 
                | "unit" | "bool" -> ([], false, default_out_mode)
                | "list" -> ([], args <> [], Out_list)
                | "option" -> ([], args <> [], Out_option)
                | "unique" -> ([], args <> [], Out_unique)
                | _ -> ([], true, default_out_mode)
              end
            | _ -> raise (Invalid_argument "src_t_to_mode")
          end
      end
    | _ -> raise (Invalid_argument "src_t_to_mode")


let rec decompose_rel_type typ = 
  match typ.term with
    | Typ_fn(u,_,v) -> u.typ::decompose_rel_type v
    | _ -> [] (* The return value is assumed to be bool, we don't check it *)

let get_rels (l : Ast.l) (names : indrel_name lskips_seplist) 
    (rules: Typed_ast.rule lskips_seplist) : relsdescr =
  let names = List.fold_left (fun s (RName(_,n,_,t,wit,chk,fn,_)) ->
    let relname = Name.strip_lskip n in
    let witness = map_option (fun (Witness(_,_,n,_)) -> Name.strip_lskip n) wit in 
    let check = map_option (fun (_,n,_) -> Name.strip_lskip n) chk in
    let (_constraints, typ) = t in
    let argtypes = decompose_rel_type typ in
    let fn = match fn with None -> [] | Some(x) -> x in
    let indfns = List.map 
      (fun (Fn(n,_,t,_)) -> (Name.strip_lskip n, src_t_to_mode t)) fn in
    let descr = {
      rel_name = relname;
      rel_type = t;
      rel_argtypes = argtypes; 
      rel_witness = witness;
      rel_check = check;
      rel_indfns = indfns;
      rel_rules = [];
      rel_loc = l; 
    } in
    Nfmap.insert s (relname, descr)
  ) Nfmap.empty (Seplist.to_list names) in
  List.fold_left (fun s (Rule(rulename,_,_,vars,_,cond,_,rel,args),l) ->
    let rulename = Name.strip_lskip rulename in
    let relname = Name.strip_lskip rel.term in
    let l' = loc_trans "get_rels" l in
    let rulecond = match cond with
      | Some x -> x
      | None -> C.mk_lit l'
        {term = L_true None; 
         locn = l'; 
         typ =  {t = Tapp([], Path.boolpath)}; 
         rest = ()
        } None in
    let vars = List.map (function
      | QName(n) -> n
      | Name_typ(_,n,_,_,_) -> n
    ) vars in
    let ruledescr = {
      rule_name = rulename;
      rule_vars = List.map (fun v -> (Name.strip_lskip v.term, v.typ) ) vars;
      rule_conds = split_and rulecond;
      rule_args = args;
      rule_loc = l;
    } in
    match Nfmap.apply s relname with
      | None -> failwith "Relation without description (is this ok ?)" (* TODO *)
      | Some rel -> Nfmap.insert s 
        (relname, {rel with rel_rules = ruledescr::rel.rel_rules})
  ) names (Seplist.to_list rules)

type ('a,'b) choice = Left of 'a | Right of 'b

let map_partition f l = 
  List.fold_right (fun x (ls,rs) ->
    match f x with
      | Left l -> (l::ls,rs)
      | Right r -> (ls,r::rs)
  ) l ([],[])


(* Just a small model of the code we will generate later
   We will need a partial "exp to pattern" function somewhere *)
type code = 
  | IF of exp * code 
  | CALL of (Name.t * Types.t, Path.t) choice * exp list * pat list * code
  | IFEQ of exp * exp * code 
  | RETURN of exp list

exception No_translation of exp option

let no_translation e = raise (No_translation e)

let make_namegen names = 
  let names = ref names in
  let fresh n = 
    let n' = Name.fresh n (fun n -> not (Nset.mem n !names)) in
    names := Nset.add n' !names;
    n'
  in
  fresh

(* Problems : 
   - the user can't shadow relation names
   - we probably rename relation names anyway
*)
let make_renamer quantified_orig rules = 
  let scope = Nset.union quantified_orig rules in
  let gen_name = make_namegen scope in
  let used = ref Nset.empty in
  let gen_eqused () = 
    let seen = ref Nset.empty in 
    let equalities = ref [] in
    let check_rename l v typ =
      let l = loc_trans "make_renamer" l in
      let n = Name.strip_lskip v in
      if not (Nset.mem n quantified_orig)
      then no_translation None
      else 
        begin 
          let varname = 
            if not (Nset.mem n !used)
            then n
            else 
              let n' = gen_name (Name.to_rope n)  in
              let v' =  Name.add_lskip n' in
              equalities := (C.mk_var l v typ,
                             C.mk_var l v' typ) :: !equalities;
              n'
          in
          used := Nset.add varname !used;
          seen := Nset.add varname !seen;
          Name.add_lskip varname
        end
    in
    let transform_exp l e typ = 
      let l = loc_trans "make_renamer" l in
      let n = gen_name (Ulib.Text.of_latin1 "pat") in
      let v = Name.add_lskip n in
      used := Nset.add n !used;
      seen := Nset.add n !seen;
      equalities := (C.mk_var l v typ, e) :: !equalities;
      C.mk_pvar_annot l v (C.t_to_src_t typ) (Some typ)
    in
    (check_rename, transform_exp, seen, equalities)
  in
  gen_eqused

(* Try to convert an expression to a pattern

    `check_rename' checks that the translated vars are forall-bound and not
    relations, and renames them if necessary to make the pattern matching
    linear 
*)


let split_app e = 
  let rec split_app e args = match C.exp_to_term e with
    | App(e1,e2) -> split_app e1 (e2::args)
    | Paren(_,e,_) | Begin(_,e,_) | Typed(_,e,_,_,_) -> split_app e args
    | Infix(e2, e1, e3) -> split_app e1 (e2::e3::args)
    | _ -> (e,args)
  in
  split_app e []

let id x = x

let cons_path = mk_string_path ["Pervasives"] "::"
let is_cons cons = Path.compare cons.descr.const_binding cons_path = 0

let exp_to_pat e check_rename transform_exp  =
  let rec exp_to_pat e = 
    let loc = loc_trans "exp_to_pat" (exp_to_locn e) in
    let typ = Some(exp_to_typ e) in
    let ty = exp_to_typ e in
    let (head, args) = split_app e in
    match C.exp_to_term head, args with
      | Constructor c, args -> mk_pconstr loc c (List.map exp_to_pat args) typ
      | Constant cons, [e1;e2] when is_cons cons -> 
        mk_pcons loc (exp_to_pat e1) None (exp_to_pat e2) typ 
      | Var v, [] ->
            mk_pvar_annot loc (check_rename loc v ty) 
              (C.t_to_src_t ty) typ
      | Record(s1, fields,s2), [] -> 
        let pfields = Seplist.map (fun (field, skip, e, _loc) ->
          (field, skip, exp_to_pat e)) fields in
        mk_precord loc s1 pfields s2 typ 
      | Vector(s1, es, s2), [] -> 
        mk_pvector loc s1 (exps_to_pats es) s2 ty
      | Tup(s1, es, s2), [] -> 
        mk_ptup loc s1 (exps_to_pats es) s2 typ
      | List(s1, es, s2), [] ->
        mk_plist loc s1 (exps_to_pats es) s2 ty
      | Lit l, [] -> mk_plit loc l typ
      | Set(s1, es, s2), [] when Seplist.length es = 1 ->
        (* XXX TODO FIXME XXX: cheat here *)
        let se = Seplist.hd es in
        let pat = exp_to_pat se in
        Reporting.print_debug_exp "Cheated on set expression" [e];
        transform_exp loc e ty
      | _ -> Reporting.print_debug_exp "Untranslatable" [e]; transform_exp loc e ty
  and exps_to_pats es = Seplist.map exp_to_pat es in
  exp_to_pat e

let find_some f l = try Some(List.find f l) with Not_found -> None

let convert_output gen_rn exps mask = 
  let (check_rename, transform_exp, bound, equalities) = gen_rn () in
  let outargs = map_filter id (List.map2 (fun exp inarg ->
    if inarg then None
    else Some (exp_to_pat exp check_rename transform_exp)
  ) exps mask) in
  (outargs, !bound, !equalities)

let report_no_translation rule notok eqconds sideconds =
  Reporting.print_debug_exp "No translation for relation with args" rule.rule_args;
  Reporting.print_debug_exp "Conditions are" rule.rule_conds;
  no_translation None

let sep_no_skips l = Seplist.from_list_default None l

let newline = Some([Ast.Nl])
let space = Some([Ast.Ws(Ulib.Text.of_latin1 " ")])

let sep_newline l = Seplist.from_list_default newline l

let mk_pvar_ty l n t =
  mk_ptyp l space (mk_pvar l n t) None (t_to_src_t t) None None

module type COMPILATION_CONTEXT = sig
  (* lem signature : type a -> type m a) *)
  val mk_type : Types.t -> Types.t
  val remove_type : Types.t -> Types.t

  (* lem signature : type a -> exp m a *)
  val mk_failure : Typed_ast.env -> Ast.l -> Types.t -> Typed_ast.exp

  (* exp a -> exp m a *)
  val mk_return : Typed_ast.env -> Ast.l -> Typed_ast.exp -> Typed_ast.exp

  (* exp m a -> pat a -> exp m b -> exp m b *)
  val mk_bind : Typed_ast.env -> Ast.l -> Typed_ast.exp -> Typed_ast.pat -> Typed_ast.exp -> Typed_ast.exp

  (* exp bool -> exp m a -> exp m a *)
  val mk_cond : Typed_ast.env -> Ast.l -> Typed_ast.exp -> Typed_ast.exp -> Typed_ast.exp

  (* type b -> exp a -> (exp a * exp m b) list -> m b *)
  val mk_choice : Typed_ast.env -> Ast.l -> Types.t -> Typed_ast.exp ->
    (Typed_ast.pat * Typed_ast.exp) list -> Typed_ast.exp
end

module Context_list : COMPILATION_CONTEXT = struct

  let mk_type ty = 
    { Types.t = Types.Tapp([ty], Path.listpath) }

  let remove_type ty = 
    match ty.t with
      | Types.Tapp([ty], _) -> ty
      | _ -> failwith "???"

  let remove_list = remove_type

  let mk_list_map env l fn lst = 
    let l = loc_trans "mk_list_map" l in
    match (exp_to_typ fn).t with
      | Types.Tfn(a,b) ->
        mk_app l (mk_app l (mk_const_exp env l ["List"] "map" [a;b]) fn None) lst None
      | _ -> failwith "???"
        
  let mk_list_concat env l lst = 
    let t = remove_list (remove_list (exp_to_typ lst)) in
    let l = loc_trans "mk_list_concat" l in
    mk_app l (mk_const_exp env l ["List"] "concat" [t]) lst None

  let mk_return env l e =
    mk_list (loc_trans "mk_return" l) None (sep_no_skips [e]) None (mk_type (exp_to_typ e))

  let mk_failure env l t = 
    mk_list (loc_trans "mk_failure" l) None (sep_no_skips []) None (mk_type t)
      
  let mk_bind env l call pat code = 
    let l = loc_trans "mk_bind" l in
    let namegen = make_namegen (Nfmap.domain (exp_to_free code)) in
    let var = Name.add_lskip (namegen (Ulib.Text.of_latin1 "x")) in
    let inty = pat.typ in 
    let fn = mk_fun l None [mk_pvar l var inty] None 
      (mk_case_exp false l (mk_var l var inty) 
         [(pat, code);
          (mk_pwild l None inty, mk_list l None (sep_no_skips []) None (exp_to_typ code))
         ] (exp_to_typ code)) None in
    mk_list_concat env l (mk_list_map env l fn call)
      
  let mk_cond env l cond code = 
    let l = loc_trans "mk_cond" l in
    mk_if_exp l cond code (mk_list l None (sep_no_skips []) None (exp_to_typ code))

  let mk_let env l pat v code = 
    let l = loc_trans "mk_let" l in
    mk_case_exp false l v
      [(pat, code);
       (mk_pwild l None pat.typ, mk_list l None (sep_no_skips []) None (exp_to_typ code))
      ] (exp_to_typ code)

  let mk_choice env l ty input pats = 
    let l = loc_trans "mk_choice" l in
    mk_list_concat env l
      (mk_list l None (sep_newline (List.map (fun (pat, code) -> mk_let env l pat input code) pats)) None (mk_list_type (mk_list_type ty)))

end

module Context_pure : COMPILATION_CONTEXT = struct
  let mk_type x = x
  let remove_type x = x

  let mk_return _ l e = e
  let mk_failure _ l t = mk_undefined_exp (loc_trans "mk_undefined" l)
    "Undef" t

  let mk_bind _ l e pat code =
    let l = loc_trans "mk_bind" l in
    mk_case_exp false l e [(pat, code)] (exp_to_typ code)

  let mk_cond env l cond code =
    let l = loc_trans "mk_cond" l in
    mk_if_exp l cond code (mk_failure env l (remove_type (exp_to_typ code)))

  let mk_choice env l t v pats = 
    let l = loc_trans "mk_choice" l in
    (* Check pattern non-overlap & completeness or emit a warning *)
    let props = Patterns.check_pat_list env (List.map fst pats) in
    (match props with
      | None -> failwith "Pattern matching compilation failed"
      | Some(props) ->
        if not props.Patterns.is_exhaustive
        then Reporting.report_warning 
          (Reporting.Warn_general(true, l, "non-exhaustive patterns in inductive relation"));
        if props.Patterns.overlapping_pats <> []
        then Reporting.report_warning
          (Reporting.Warn_general(true, l, "overlapping patterns in inductive relation")));
    mk_case_exp false l v pats (mk_type t)
end

(* TODO : merge with LemOptionMonad ? *)
module Context_option_pre = struct

  let mk_type ty = 
    { Types.t = Types.Tapp([ty], mk_string_path ["Pervasives"] "option") } 

  let remove_type ty = 
    match ty.t with
      | Types.Tapp([ty], _) -> ty
      | _ -> failwith "???"

  let mk_none env ty = mk_constr_exp env ["Pervasives"] "None" [ty] [] 
  let mk_some env e = mk_constr_exp env ["Pervasives"] "Some" [exp_to_typ e] [e]
  let mk_pnone env ty = mk_pconstr_pat env ["Pervasives"] "None" [ty] []
  let mk_psome env p = mk_pconstr_pat env ["Pervasives"] "Some" [p.typ] [p]

  let mk_return env l e = mk_some env e

  let mk_failure env l ty = mk_none env ty

  let mk_bind env l call pat code = 
    let l = loc_trans "mk_bind" l in
    mk_case_exp false l call
      [(mk_psome env pat, code);
       (mk_pwild l None (exp_to_typ call), mk_none env (remove_option (exp_to_typ code)))]
      (exp_to_typ code)

  let mk_cond env l cond code = 
    let l = loc_trans "mk_cond" l in
    mk_if_exp l cond code (mk_none env (remove_option (exp_to_typ code)))

end

module Context_option : COMPILATION_CONTEXT = struct
  include Context_option_pre

  let mk_choice _ = failwith "Not implemented"
end

module Context_unique : COMPILATION_CONTEXT = struct
  include Context_option_pre

  let mk_choice _ = failwith "Not implemented"
end

let select_module = function
  | Out_list -> (module Context_list : COMPILATION_CONTEXT)
  | Out_pure -> (module Context_pure : COMPILATION_CONTEXT)
  | Out_unique -> (module Context_unique : COMPILATION_CONTEXT)
  | Out_option -> (module Context_option : COMPILATION_CONTEXT)

let out_ty_from_mode env localenv reldescr (mode, wit, _out) = 
  let ret = map_filter (function
    | (O,x) -> Some x
    | _ -> None
  ) (List.map2 (fun x y -> (x,y)) mode reldescr.rel_argtypes) in
  let ret = if wit then 
      let Some(x) = Nfmap.apply localenv.r_env reldescr.rel_name in
      let Some(t,_) = x.ri_witness in
      ret@[{t = Tapp([],t)}]
    else ret 
  in
  {t=Ttup(ret)}
        
let in_tys_from_mode env reldescr (mode, _wit, _out) = 
  map_filter (function
    | (I,x) -> Some x
    | _ -> None
  ) (List.map2 (fun x y -> (x,y)) mode reldescr.rel_argtypes)

let ty_from_mode env localenv reldescr ((_,_,out) as mode) = 
  let args = in_tys_from_mode env reldescr mode in
  let ret = out_ty_from_mode env localenv reldescr mode in
  let module M = (val select_module out : COMPILATION_CONTEXT) in
  List.fold_right (fun a b -> {t=Tfn(a,b)}) args (M.mk_type ret)

module Compile(M : COMPILATION_CONTEXT) = struct
  
  (* FIXME : renaming *)
  let rec compile_code env loc code = 
    let l = loc_trans "compile_code" loc in
    match code with
      | RETURN(exps) -> 
        let ret = mk_tup l None (sep_no_skips exps) None None in
        M.mk_return env l ret
      | IF(cond, code) -> 
        let subexp = compile_code env loc code in 
        M.mk_cond env l cond subexp
      | IFEQ(e1,e2,code) ->
        let subexp = compile_code env loc code in
        let cond = mk_eq_exp env e1 e2 in
        M.mk_cond env l cond subexp
      | CALL(n, inp, outp, code) ->
        let subexp = compile_code env loc code in
        let func = match n with 
          | Left(n,ty) -> mk_var l (Name.add_lskip n) ty 
          | Right(path) -> mk_const_from_path env l path []
        in
        let call = List.fold_left (fun func arg -> mk_app l func arg None) 
          func inp in
        let pat = mk_ptup l None (sep_no_skips outp) None None in
        M.mk_bind env l call pat subexp
          
  let compile_rule env (loc, patterns, code) = 
    let pattern = mk_ptup (loc_trans "compile_rule" loc) None (sep_no_skips patterns) None None in
    let lemcode = compile_code env loc code in
    (pattern, lemcode) 

  let compile_function env localenv fun_names reldescr (n,mode,mty,rules) : funcl_aux =
    let l = loc_trans "compile_function" reldescr.rel_loc in 
    let gen_name = make_namegen fun_names in
    let vars = List.map 
      (fun ty -> Name.add_lskip (gen_name (Ulib.Text.of_latin1 "input")), ty)
      (in_tys_from_mode env reldescr mode) in
    let tuple_of_vars = mk_tup l None (sep_no_skips (List.map (fun (var,ty) -> mk_var l var ty) vars)) None None in
    let pats_of_vars = List.map (fun (var,ty) -> mk_pvar_ty l var ty) vars in
    let cases = List.map (compile_rule env) rules in
    let output_type = out_ty_from_mode env localenv reldescr mode in
    (* Generate a list of binds and concat them ! *)
    let body = M.mk_choice env l output_type tuple_of_vars cases in
    let annot = { term = Name.add_lskip n;
                  locn = l;
                  typ = mty;
                  rest = () } in
    (annot, pats_of_vars, Some(space, t_to_src_t (M.mk_type output_type)), space, body)
end

let compile_function env localenv fun_names reldescr 
    ((_,(_,_,out_mode),_,_) as m) = 
  let module M = (val select_module out_mode) in
  let module C = Compile(M) in
  C.compile_function env localenv fun_names reldescr m


let compile_to_typed_ast env localenv prog =
  let l = Ast.Trans ("compile_to_typed_ast", None) in
  let funcs = Nfmap.fold (fun l _ (_,funcs) -> 
    (List.map (fun (name, _, _, _) -> name) funcs)@l) [] prog in
  let fun_names = List.fold_right Nset.add funcs Nset.empty in
  let defs = Nfmap.map (fun _rel (reldescr, modes) ->
    List.map (compile_function env localenv fun_names reldescr) modes 
  ) prog in
  let defs = sep_newline (Nfmap.fold (fun l _ c -> c@l) [] defs) in
  ((Val_def(Rec_def(newline,None,None,defs), Types.TNset.empty, []), None), l)

module Compile_list = Compile(Context_list)
module Compile_pure = Compile(Context_pure)
module Compile_unique = Compile(Context_unique)
module Compile_option = Compile(Context_option)

open Typecheck_ctxt

let gen_consname relname = Name.from_string (Name.to_string relname ^ "_witness")

let mk_name_l n = (Name.add_lskip n , Ast.Unknown)

let make_typedef tds =
  let tds = Nfmap.fold (fun l _ td -> td::l) [] tds in
  let make_cons (_crule, cname, cargs) = 
    (mk_name_l cname, None, sep_no_skips (List.map snd cargs))
  in
  let make_def (tname,tconses) =
    let texp = Te_variant(None, sep_no_skips (List.map make_cons tconses)) in
    (mk_name_l tname, [], texp, None)
  in
  Type_def(newline, sep_no_skips (List.map make_def tds))

let register_types rel_loc ctxt mod_path tds = 
  Nfmap.fold (fun ctxt relname (tname, tconses) ->
    (* Register a type constructor *)
    let type_path = Path.mk_path mod_path tname in
    let l = loc_trans "register_types" rel_loc in
    let () =
      match Nfmap.apply ctxt.new_defs.p_env tname with
        | None -> ()
        | Some(p, _) ->
          begin
            match Pfmap.apply ctxt.all_tdefs p with
              | None -> assert false
              | Some(Tc_type _) ->
                raise_error l "duplicate type constructor definition"
                  Name.pp tname
              | Some(Tc_class _) ->
                raise_error l "type constructor already defined as a type class" 
                  Name.pp tname
          end
    in
    let ctxt = ctxt_add (fun x -> x.p_env) (fun x y -> { x with p_env = y })
      ctxt (tname, (type_path,l)) in
    let ctxt = add_d_to_ctxt ctxt type_path (Tc_type([],None,None)) in
    (* Register the value constructors FIXME *)
    let cnames = List.fold_left (fun s (_,cname,_) -> NameSet.add cname s) 
      NameSet.empty tconses in
    let mk_descr cname cargs =
        {
                constr_binding = Path.mk_path mod_path cname;
                constr_tparams = [];
                constr_args = List.map fst cargs;
                constr_tconstr = type_path;
                constr_names = cnames;
                constr_l = Ast.Unknown
        } 
    in
    let rule_to_constr = Nfmap.from_list 
      (List.map (fun (crule, cname, cargs) -> (crule, mk_descr cname cargs)) tconses) in
    let ctxt = ctxt_add (fun x -> x.r_env) (fun x y -> { x with r_env = y })
      ctxt (relname, { ri_witness = Some(type_path, rule_to_constr); ri_check = None; ri_fns = [] }) in
    List.fold_left (fun ctxt (crule, cname, cargs) ->
      let () = 
        match Nfmap.apply ctxt.new_defs.v_env cname with
          | None -> ()
          | Some(Constr _) ->
            raise_error l "duplicate constructor definition"
              Name.pp cname
          | Some(Val(c)) ->
            begin
              match c.env_tag with
                | K_method|K_instance ->
                  raise_error l "constructor already defined as a class method name"
                    Name.pp cname
                | K_val | K_let | K_target _ ->
                  raise_error l "constructor already defined as a top-level variable binding" 
                    Name.pp cname
            end
      in
      ctxt_add (fun x -> x.v_env) (fun x y -> { x with v_env = y }) 
        ctxt (cname, Constr(mk_descr cname cargs))
    ) ctxt tconses
  ) ctxt tds 

let rec path_lookup (e : env) (mp : Name.t list) : env option = 
  match mp with
    | [] -> Some(e)
    | n::ns ->
        match Nfmap.apply e.m_env n with
          | None -> None
          | Some(e) -> path_lookup e.mod_env ns

(* TODO : || -> either, && -> *, forall -> (->), exists -> ... *)
(* TODO : remove this get_typepath_from_rel nonsense *)
let gen_witness_type_aux env l get_typepath_from_rel names rules = 
  let rels = get_rels l names rules in
  let reltypes = Nfmap.fold (fun reltypes relname reldescr ->
    match get_typepath_from_rel relname reldescr with
      | None -> reltypes
      | Some(ty) -> Nfmap.insert reltypes (relname, ty)
  ) Nfmap.empty rels in
  (* We want to return a type here *)
  let is_relation e = match exp_to_term e with
    | Var v ->
      begin match Nfmap.apply reltypes (Name.strip_lskip v) with
        | None -> None
        | Some tn -> Some tn
      end
    | Constant c -> 
      let (mpath, n) = Path.to_name_list c.descr.const_binding in
      begin match path_lookup env mpath with
        | Some(env) -> 
          begin match Nfmap.apply env.r_env n with
            | None -> None
            | Some { ri_witness = None } ->
              raise_error Ast.Unknown "no witness for relation"
                Path.pp c.descr.const_binding 
            | Some { ri_witness = Some(tn,_) } -> 
              let t = {t=Tapp([],tn)} in
              Some(t, t_to_src_t t) 
          end
        | None -> 
          (* Then it must be a function from the current module *)
          None
      end
    | _ -> None
  in
  let tds = Nfmap.fold (fun tds relname reldescr ->
    match reldescr.rel_witness with
      | None -> tds
      | Some(typename) ->
        let constructors = List.map (fun rule  ->
          let consname = gen_consname rule.rule_name in
          let vars_ty = List.map (fun x -> (snd x,t_to_src_t (snd x))) rule.rule_vars in
          let conds_ty = map_filter 
            (fun cond -> is_relation (fst (split_app cond))) rule.rule_conds in
          let argstypes = vars_ty @ conds_ty in
          (rule.rule_name, consname, argstypes)
        ) reldescr.rel_rules in
        Nfmap.insert tds (relname, (typename, constructors))
  ) Nfmap.empty rels in
  tds

(* TODO : remove this once the backend is fixed *)
let clean_src_app p = 
  let t = {t=Tapp([],p)} in
  let tn = snd (Path.to_name_list p) in
  let ident = Ident.mk_ident [] (Name.add_lskip tn) Ast.Unknown in
  let pid = {
    id_path = Id_some ident;
    id_locn = Ast.Unknown;
    descr = p;
    instantiation = []
  } in
  let loc = Ast.Trans("clean_src_app", None) in
  (t, mk_tapp loc pid [] (Some t))

let gen_witness_type_info l mod_path ctxt names rules = 
  let tds = gen_witness_type_aux ctxt.cur_env l 
    (fun relname reldescr -> 
      match reldescr.rel_witness with
        | None -> None
        | Some(tn) ->
          let p = Path.mk_path mod_path tn in
          Some(clean_src_app p)
    ) 
    names rules in
  let newctxt = register_types l ctxt mod_path tds in
  newctxt

let gen_witness_type_def env l mpath localenv names rules =
  let l = loc_trans "gen_witness_type_def" l in
  let tds = gen_witness_type_aux env l
    (fun relname _ -> 
      match Nfmap.apply localenv.r_env relname with
        | Some({ri_witness = Some(tn,_)}) -> Some(clean_src_app tn)
        | _ -> None
    )
    names rules in
  if Nfmap.is_empty tds then []
  else [(make_typedef tds, None),  l]

let ctxt_mod update ctxt = 
  { ctxt with
    cur_env = update ctxt.cur_env;
    new_defs = update ctxt.new_defs
  }

let gen_witness_check_info l mod_path ctxt names rules =
  let rels = get_rels l names rules in
  let defs = Nfmap.fold (fun defs relname reldescr ->
    match reldescr.rel_check with
      | None -> defs
      | Some(check_name) -> 
        let rules = reldescr.rel_rules in
        let ret = List.map exp_to_typ (List.hd rules).rule_args in
        let check_path = Path.mk_path mod_path check_name in
        let witness_type = 
          match Nfmap.apply ctxt.cur_env.r_env relname with
            | Some({ri_witness = Some(witness_type,_)}) -> 
              {t = Tapp([],witness_type)}
            | _ -> raise_error l
              "no witness for relation while generating witness-checking function"
              Path.pp check_path
        in
        let check_type = {t=Tfn(witness_type, mk_option {t=Ttup(ret)})} in
        Nfmap.insert defs (relname, (check_name, check_path, check_type))
  ) Nfmap.empty rels in
  (* Register the functions *)
  Nfmap.fold (fun ctxt relname (cname,cpath,ctype) ->
    let const_descr = {
      const_binding = cpath;
      const_tparams = [];
      const_class = [];
      const_ranges = [];
      const_type = ctype;
      env_tag = K_let;
      spec_l = loc_trans "gen_witness_check_info" l;
      substitutions = Targetmap.empty
    } in
    let ctxt = ctxt_add (fun x -> x.v_env) (fun x y -> {x with v_env = y})
      ctxt (cname, Val(const_descr)) in
    ctxt_mod (fun x -> {x with r_env = let Some r_info = Nfmap.apply x.r_env relname in Nfmap.insert x.r_env (relname, {r_info with ri_check = Some cpath})}) ctxt
  ) ctxt defs

let nset_of_list l = List.fold_left (fun set x -> Nset.add x set) Nset.empty l

open LemOptionMonad

let rel_lookup env path = 
  let (mpath, n) = Path.to_name_list path in
  match path_lookup env mpath with
    | None -> None
    | Some(env) -> Nfmap.apply env.r_env n

let gen_witness_check_def env l mpath localenv names rules = 
  let rels = get_rels l names rules in
  let mkloc = loc_trans "gen_witness_check_def" in
  let l = mkloc l in
  let localdefs = Nfmap.fold (fun localdefs relname rules ->
    match Nfmap.apply localenv.r_env relname with
      | Some({ri_witness = Some(witness_info); ri_check = Some(check_path)}) 
        when rules.rel_check <> None ->
        let (_,def_name) = Path.to_name_list check_path in
         Nfmap.insert localdefs (relname,(def_name, witness_info,check_path, rules))
      | _ -> localdefs
  ) Nfmap.empty rels in
  let defs = Nfmap.map (fun relname (def_name, (witness_path, witness_constrs), check_path, reldescr) ->
    let rules = reldescr.rel_rules in
    let witness_ty = {t=Tapp([],witness_path)} in
    let pats = List.map (fun rule ->
      (* Bad indices from get_witness_type_info, sorry *)
      let Some(constr) = Nfmap.apply witness_constrs rule.rule_name in
      (* THIS IS WRONG *)
     (* (* If a var and a localdef share a name, we need to rename the var *)
      let defvars = nset_of_list (Nfmap.fold (fun acc _ (v,_,_) -> v::acc) [] localdefs) in
      let (vars,conds,args) = do_what_i_mean in
      let excludevars = List.map snd vars @
        Nfmap.fold (fun acc _ (v,_,_) -> v::acc) [] localdefs in
      let excludevars = List.fold_right Nset.add excludevars Nset.empty in *)
      let gen_name = make_namegen Nset.empty in
      let l = mkloc rule.rule_loc in
      (* Travailler sur les conds *)
      let is_rel_or_aux e = 
        let (head, args) = split_app e in
        match exp_to_term head with
          | Var v ->
            (* TODO : factorisation *)
            let n = Name.strip_lskip v in
            begin match Nfmap.apply localenv.r_env n with
              | None -> Right e
              (* TODO : adjust ids for local things *)
              | Some {ri_check = Some(check_path);
                      ri_witness = Some(witness_path, witness_constrs)} ->
                let check_exp = match Nfmap.apply localdefs n with
                  | Some(def_name,_,_,_) -> 
                    let witness_ty = {t=Tapp([],witness_path)} in
                    let out_ty = mk_option {t=Ttup(List.map exp_to_typ args)} in
                    mk_var (mkloc (exp_to_locn head)) (Name.add_lskip def_name) {t=Tfn(witness_ty, out_ty)}
                  | None -> mk_const_from_path env (mkloc (exp_to_locn head)) check_path []
                in
                Left(args, witness_path, check_exp)
              | Some _ ->
                raise_error (exp_to_locn e) "no witness checking function for relation"
                  Path.pp check_path
            end
          | Constant c ->
            begin match rel_lookup env c.descr.const_binding with
              | None -> Right e
              | Some { ri_witness = Some(witness_path, _);
                           ri_check = Some(check_path) } ->
                    let check_exp = mk_const_from_path env (mkloc (exp_to_locn head)) check_path [] in
                    Left (args, witness_path, check_exp)
              | Some _ -> 
                raise_error (exp_to_locn e) "no witness checking function for relation"
                  Path.pp check_path
            end
          | _ -> Right e
      in    
      let (relconds,auxconds) = map_partition is_rel_or_aux rule.rule_conds in
      let relconds = List.map (fun (args,witness_path,check_exp) ->
        let witness_ty = {t=Tapp([],witness_path)} in
        let witness_name = gen_name (Ulib.Text.of_latin1 "witness") in
        (args, witness_ty, check_exp, witness_name)
      ) relconds in
      let pvars = List.map 
        (fun (var,typ) -> mk_pvar l (Name.add_lskip var) typ) rule.rule_vars in
      let pconds = List.map
        (fun (_,witness_ty,_,var) -> 
          mk_pvar l (Name.add_lskip var) witness_ty
        ) relconds in
      let constr_id = { id_path = Id_none None;
                        id_locn = l;
                        descr = constr;
                        instantiation = [] } in
      let pattern = mk_pconstr l constr_id (pvars @ pconds) None in
      let ret = mk_some env 
        (mk_tup l None (sep_no_skips rule.rule_args) None None) in
      let genconds_exps = List.map (fun (args,witness_ty,check_fun,witness) ->
        let witness_var = mk_var l (Name.add_lskip witness) witness_ty in
        let rhs = mk_some env (mk_tup l None (sep_no_skips args) None None) in
        let lhs = mk_app l check_fun witness_var None in
        mk_eq_exp env rhs lhs
      ) relconds in
      let ifconds = auxconds @ genconds_exps in
      let lit_true = mk_lit l ({term=L_true(None); locn = l;
                                typ={t=Tapp([],Path.boolpath)};
                                rest=()}) None in
      let cond = List.fold_left (mk_and_exp env) lit_true ifconds in
      let code = mk_if_exp l cond ret (mk_none env (remove_option (exp_to_typ ret))) in
      (pattern, code)
    ) rules in
    let x = Name.add_lskip (make_namegen Nset.empty (Ulib.Text.of_latin1 "x")) in
    let xpat = mk_pvar_ty l x witness_ty in
    let xvar = mk_var l x witness_ty in
    let return_ty = exp_to_typ (snd (List.hd pats))  in
    let body = mk_case_exp false l xvar pats return_ty in
    let annot = { term = Name.add_lskip def_name;
                  locn = l;
                  typ = {t=Tfn(witness_ty,return_ty)};
                  rest = () } in
    (annot, [xpat], Some(space, t_to_src_t return_ty), space, body)
  ) localdefs in
  let defs = Nfmap.fold (fun l _ v -> v::l) [] defs in
  let def = Rec_def(newline,None,None,sep_newline defs) in
  if defs = [] then []
  else [((Val_def(def, Types.TNset.empty, []), None), l)]

open Compile_list

let gen_fns_info l mod_path (ctxt : defn_ctxt) names rules =
  let rels = get_rels l names rules in
  let l = loc_trans "gen_fns_info" l in
  Nfmap.fold (fun ctxt relname reldescr ->
    List.fold_left (fun ctxt (name, mode) ->
      let ty = ty_from_mode ctxt.cur_env ctxt.cur_env reldescr mode in
      let path = Path.mk_path mod_path name in
      let ctxt = ctxt_mod (fun x -> {x with r_env =
          Nfmap.insert x.r_env 
            (relname, 
             let info = match Nfmap.apply x.r_env relname with
              | Some y -> y
              | None -> { ri_witness = None; ri_check = None; ri_fns = [] } in
             {info with ri_fns = (mode, path)::info.ri_fns})}) ctxt in
      let const_descr = {
        const_binding = path;
        const_tparams = [];
        const_class = [];
        const_ranges = [];
        const_type = ty;
        env_tag = K_let;
        spec_l = l;
        substitutions = Targetmap.empty
      } in
      ctxt_add (fun x -> x.v_env) (fun x y -> {x with v_env = y})
        ctxt (name, Val(const_descr))
    ) ctxt reldescr.rel_indfns
  ) ctxt rels

let transform_rule env localenv localrels (mode, need_wit, out_mode) rel (rule : ruledescr) = 
  let l = loc_trans "transform_rule" rule.rule_loc in
  let vars = Nfmap.domain (Nfmap.from_list rule.rule_vars) in
  let avoid = Nfmap.fold (fun avoid relname reldescr ->
    List.fold_left (fun avoid (funname, _) -> Nset.add funname avoid)
      (Nset.add relname avoid) reldescr.rel_indfns
  ) Nset.empty localrels in
  let gen_rn = make_renamer vars avoid in
  let (patterns, initknown, initeqs) = 
    convert_output gen_rn rule.rule_args (List.map (fun x -> x = O) mode) in
  let gen_witness_name = 
    let gen = make_namegen Nset.empty in
    fun () -> gen (Ulib.Text.of_latin1 "witness") in
  let gen_witness_var relinfo =
    match relinfo.ri_witness with
      | None -> None
      | Some(t,_) -> Some(gen_witness_name (), {t=Tapp([],t)})
  in
  let (indconds, sideconds) = 
    map_partition (fun x ->
      let (e,args) = split_app x in
      match exp_to_term e with
        | Var n ->
          begin match Nfmap.apply localrels (Name.strip_lskip n) with
            | Some(rel) ->
              let modes = List.map (fun (name, mode) -> (mode, Left(name,ty_from_mode env localenv rel mode))) rel.rel_indfns in
              let Some(relinfo) = Nfmap.apply localenv.r_env rel.rel_name in
              Left(modes,args,gen_witness_var relinfo)
            | None -> Right(x)
          end
        | Constant c ->
          begin match rel_lookup env c.descr.const_binding with
            | Some(relinfo) ->
              Left(List.map (fun (mode,path) -> (mode, Right(path))) relinfo.ri_fns,args,gen_witness_var relinfo)
            | None -> Right(x)
          end
        | _ -> Right(x)
    ) rule.rule_conds
  in
  (* map_filter drops relations with no witnesses.
     it's not a problem because if our relation has a witness, all these
     relations must have one *)
  let witness_var_order = map_filter (fun (_,_,var) -> var) indconds in
  let returns = map_filter (function
    | (I, _) -> None
    | (O, r) -> Some(r)
  ) (List.map2 (fun x y -> (x,y)) mode rule.rule_args) in
  let returns = 
    if not need_wit then returns
    else
      let Some(rel_info) = Nfmap.apply localenv.r_env rel.rel_name in
      let Some(_, wit_constrs) = rel_info.ri_witness in
      let Some(constr_descr) = Nfmap.apply wit_constrs rule.rule_name in
      let args = rule.rule_vars @ witness_var_order in
      let args = List.map
        (fun (name,ty) -> mk_var l (Name.add_lskip name) ty) args in
      let constr_id = {id_path = Id_none None; id_locn = Ast.Unknown;
                       descr = constr_descr; instantiation = []} in
      let constr = mk_constr l constr_id None in
      let wit = List.fold_left (fun u v -> mk_app l u v None) constr args in
      returns@[wit]
  in
  let rec build_code known indconds sideconds eqconds =
    let exp_known e = Nfmap.fold (fun b v _ -> b && Nset.mem v known) 
      true (C.exp_to_free e) in
    let (selected_eqs,eqconds2) = 
      List.partition (fun (e1,e2) -> exp_known e1 && exp_known e2) eqconds in
    let (selected_side,sideconds2) = 
      List.partition (fun e -> exp_known e) sideconds in
    let add_eq eq x = List.fold_left (fun x (e1,e2) -> IFEQ(e1,e2,x)) x eq in
    let add_side side x = List.fold_left (fun x e -> IF(e,x)) x side in 
    let rec search notok = function
      | [] ->
        begin match eqconds2,sideconds2 with
          | [], [] when notok = [] -> RETURN returns
          | _ -> report_no_translation rule notok eqconds2 sideconds2
        end
      | (modes,args,wit_var) as c::cs ->
        let inargs = List.map exp_known args in
        let mode_matches ((fun_mode, fun_wit, fun_out_mode),_info) = 
          List.for_all (fun x -> x)
            (List.map2 (fun inp m -> inp || m = O) inargs fun_mode)
            && (not need_wit || fun_wit) 
            && (fun_out_mode = out_mode)
        in
        match List.filter mode_matches modes with
          | [] -> search (c::notok) cs
          | ((fun_mode, fun_wit, _out_mode), fun_info) ::ms -> 
            (* Still some work to do to generate witnesses *)
            let (outputs, bound, equalities) = convert_output gen_rn args 
              (List.map (fun m -> m = I) mode) in
            let outputs = 
              if not fun_wit
              then outputs
              else
                let Some(wit_name, wit_ty) = wit_var in
                outputs@[mk_pvar l (Name.add_lskip wit_name) wit_ty]
            in
            let inputs = map_filter id (List.map2 (fun exp m ->
              match m with
                | I -> Some(exp)
                | O -> None
            ) args mode) in
            CALL(fun_info, inputs, outputs,
                 build_code (Nset.union bound known) (cs@notok) 
                   sideconds2 (equalities@eqconds2))
    in
    add_eq selected_eqs (add_side selected_side (search [] indconds))
  in
  (l, patterns, build_code initknown indconds sideconds initeqs)


let transform_rules env localenv localrels mode reldescr =
  List.map (transform_rule env localenv localrels mode reldescr) reldescr.rel_rules

let gen_fns_def env l mpath localenv names rules =
  let rels = get_rels l names rules in
  let transformed_rules = Nfmap.map (fun relname reldescr ->
    (reldescr, List.map (fun (name, mode) ->
      (name, mode, ty_from_mode env localenv reldescr mode,transform_rules env localenv rels mode reldescr)
    ) reldescr.rel_indfns)
  ) rels in
  let code = compile_to_typed_ast env localenv transformed_rules in
  let emptydef = 
    Nfmap.fold (fun b _ (_,l) -> b && [] = l) true transformed_rules in
  if emptydef then []
  else [code]

let gen_witness_type_macro env mpath localenv def =
  match def with
    | (Indreln(x,y,names,rules),z), l ->
      let remove_witness = 
        function RName(a,b,c,d,_witness,f,g,h) ->
          RName(a,b,c,d,None,f,g,h)
      in
      let def = (Indreln(x,y,Seplist.map remove_witness names, rules),z),l in
      let tdefs = gen_witness_type_def env l mpath localenv names rules in
      if tdefs = []
      then None
      else Some(localenv, def::tdefs)
    | _ -> None

let gen_witness_check_macro env mpath localenv def_ =
  match def_ with
    | (Indreln(x,y,names,rules),z), l ->
      let remove_check = 
        function RName(a,b,c,d,e,_check,g,h) ->
          (* TODO : preserve lskips *)
          RName(a,b,c,d,e,None,g,h)
      in
      let def = (Indreln(x,y,Seplist.map remove_check names, rules),z),l in
      let cdefs = gen_witness_check_def env l mpath localenv names rules in
      if cdefs = []
      then None
      else Some(localenv, def::cdefs)
    | _ -> None


let gen_fns_macro env mpath localenv def =
  match def with
    | (Indreln(x,y,names,rules),z), l ->
      let remove_indfns = 
        function RName(a,b,c,d,e,f,_indfns,h) ->
          RName(a,b,c,d,e,f,None,h)
      in
      let def = (Indreln(x,y,Seplist.map remove_indfns names, rules),z),l in
      let fdefs = gen_fns_def env l mpath localenv names rules in
      if fdefs = []
      then None
      else Some(localenv, def::fdefs)
    | _ -> None

end
