(* Converting a relation *)

open Typed_ast
open Types
open Util
open Typed_ast_syntax

(* FIXME *)
let raise_error l m f x = raise (Reporting_basic.err_type_pp l m f x)

module Converter(C : Exp_context) = struct

module C = Exps_in_context(C)
open C

module Nmap = Typed_ast.Nfmap
module Nset = Nmap.S


let sep_no_skips l = Seplist.from_list_default None l


let typ_unit = {t=Tapp([],Path.unitpath)}

let lit_unit l = {
  term = L_unit(None, None);
  locn = l;
  typ = typ_unit;
  rest = ()
}

let mk_tup_unit_exp l : exp list -> exp = function
  | [] -> mk_lit l (lit_unit l) None
  | [e] -> e
  | es -> mk_tup l None (sep_no_skips es) None None

let mk_tup_unit_pat l : pat list -> pat= function
  | [] -> mk_plit l (lit_unit l) None
  | [p] -> p
  | ps -> mk_ptup l None (sep_no_skips ps) None None

let mk_tup_unit_typ = function
  | [] -> typ_unit
  | [t] -> t
  | l -> {t=Ttup(l)}


let loc_trans s l = Ast.Trans(true, s, Some(l))

let is_true l = match l.term with
  | L_true _ -> true
  | _ -> false

let r = Ulib.Text.of_latin1
let mk_string_path ns n = Path.mk_path (List.map (fun s -> Name.from_rope (r s)) ns) (Name.from_rope (r n))

let mk_const_ref (env : env) l (c_ref : const_descr_ref) inst = 
  let id = {id_path = Id_none None; 
            id_locn = l; 
            descr = c_ref; 
            instantiation = inst} in
  let c_d = c_env_lookup l env.c_env c_ref in
  let t = Types.type_subst 
    (Types.TNfmap.from_list2 c_d.const_tparams id.instantiation) 
    c_d.const_type in
  C.mk_const l id (Some t)


let and_const_ref env = fst (get_const env "conjunction")
let eq_const_ref env = fst (get_const env "equality")
let id_const_ref env = fst (get_const env "identity")

let mk_fun_ty args ret =
  List.fold_right (fun a b -> {t=Tfn(a,b)}) args ret

let mk_option ty = 
  { Types.t = Types.Tapp([ty], mk_string_path ["Maybe"] "maybe") } 

let remove_option ty = 
  match ty.t with
    | Types.Tapp([ty], _) -> ty
    | _ -> failwith "???"

let path_to_string_list p = 
  let (mp,n) = Path.to_name_list p in
  (List.map Name.to_string mp, Name.to_string n)

let mk_pconst_pat env l label inst args = 
  let (c, c_d) = get_const_id env l label inst in
  let t = Types.type_subst
    (Types.TNfmap.from_list2 c_d.const_tparams c.instantiation)
    c_d.const_type in
  C.mk_pconst l c args (Some t)

let mk_const_app env l label inst args = 
  let c = mk_const_exp env l label inst in
  List.fold_left (fun u v -> mk_app l u v None) c args


let c_env_lookup_rel_info l c_env c_ref =
  let c_d = c_env_lookup l c_env c_ref in
  match c_d.relation_info with
    | Some(x) -> x
    | None -> {ri_witness = None; ri_check = None; ri_fns = []}

let c_env_update_rel_info l c_env c_ref ri =
  let c_d = c_env_lookup l c_env c_ref in
  c_env_update c_env c_ref {c_d with relation_info = Some(ri)}

module LemOptionMonad = struct

  let mk_none env ty = mk_const_app env Ast.Unknown "maybe_nothing" [ty] []
  let mk_some env e = mk_const_app env Ast.Unknown "maybe_just" [exp_to_typ e] [e]
  let mk_pnone env ty = mk_pconst_pat env Ast.Unknown "maybe_nothing" [ty] []
  let mk_psome env p = mk_pconst_pat env Ast.Unknown "maybe_just" [p.typ] [p]
    
  let mk_bind env call pat code = 
    let l = Ast.Trans (true, "mk_bind", None) in
    mk_case_exp false l call
      [(mk_psome env pat, code);
       (mk_pwild l None (exp_to_typ call), mk_none env (remove_option (exp_to_typ code)))]
      (exp_to_typ code)
      
  let mk_cond env cond code = 
    let l = Ast.Trans (true, "mk_cond", None) in
    mk_if_exp l cond code (mk_none env (remove_option (exp_to_typ code)))

end


let is_and env e = 
  match C.exp_to_term e with
    | Constant c -> c.descr = and_const_ref env
    | _ -> false

(* Splits on infix (&&) : ((a && b) && (c && d)) && true -> [a;b;c;d] *)
let rec split_and (env : env) (e : exp) = 
  match C.exp_to_term e with
    | Infix(e1, op_and, e2) when is_and env op_and ->
      split_and env e1 @ split_and env e2
    | Lit lit_true when is_true lit_true -> []
    | Paren(_,e,_) -> split_and env e
    | Typed(_,e,_,_,_) -> split_and env e
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
  rel_const_ref : const_descr_ref;
  rel_type : typschm;
  rel_argtypes : Types.t list;
  rel_witness : Name.t option;
  rel_check : Name.t option;
  rel_indfns : (Name.t * (rel_mode * bool * rel_output_type)) list;
  rel_rules : ruledescr list;
  rel_loc : Ast.l;
}

type relsdescr = reldescr Nfmap.t


let mk_list_type ty = 
  { Types.t = Types.Tapp([ty], Path.listpath) }

let map_option f = function
  | Some(x) -> Some(f x)
  | None -> None

let to_in_out (typ : src_t) : rel_io = 
  match typ.term with
    | Typ_app({id_path = p}, []) ->
      begin match p with
        | Id_some(i) -> 
          begin match Name.to_string (Name.strip_lskip (Ident.get_name i)) with
            | "input" -> Rel_mode_in
            | "output" -> Rel_mode_out
            | s -> raise (Invalid_argument ("to_in_out: "^s))
          end
        | _ -> raise (Invalid_argument "to_in_out")
      end
    | _ -> raise (Invalid_argument "to_in_out")

let default_out_mode = Out_pure

let rec src_t_to_mode (typ : src_t) : rel_mode * bool * rel_output_type =
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

let get_rels (env : env) (l : Ast.l) (names : indreln_name lskips_seplist) 
    (rules: indreln_rule lskips_seplist) : relsdescr =
  let names = List.fold_left (fun s (RName(_,n,n_c,_,t,wit,chk,fn,_)) ->
    let relname = Name.strip_lskip n in
    let witness = map_option (fun (Indreln_witness(_,_,n,_)) -> Name.strip_lskip n) wit in 
    let check = map_option (fun (_,n,_) -> Name.strip_lskip n) chk in
    let (_constraints, typ) = t in
    let argtypes = decompose_rel_type typ in
    let fn = match fn with None -> [] | Some(x) -> x in
    let indfns = List.map 
      (fun (Indreln_fn(n,_,t,_)) -> (Name.strip_lskip n, src_t_to_mode t)) fn in
    let descr = {
      rel_name = relname;
      rel_const_ref = n_c;
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
  List.fold_left (fun s (Rule(rulename,_,_,vars,_,cond,_,rel,_,args),l) ->
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
      rule_conds = split_and env rulecond;
      rule_args = args;
      rule_loc = l;
    } in
    match Nfmap.apply s relname with
      | None -> failwith "Relation without description"
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
  | CALL of const_descr_ref * exp list * pat list * code
  | LET of pat * exp * code
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

let is_constructor env t c_d = 
  match type_defs_lookup_typ Ast.Unknown env.t_env t with
    | None -> false
    | Some(td) ->
      List.exists (fun cfd ->
        List.mem c_d cfd.constr_list
      ) td.type_constr

let cons_ref env = fst (get_const env "list_cons")


let exp_to_pat env e check_rename transform_exp  =
  let rec exp_to_pat e = 
    let loc = loc_trans "exp_to_pat" (exp_to_locn e) in
    let typ = Some(exp_to_typ e) in
    let ty = exp_to_typ e in
    let (head, args) = split_app e in
    match C.exp_to_term head, args with
      | Constant cons, [e1;e2] when cons.descr = cons_ref env -> 
        mk_pcons loc (exp_to_pat e1) None (exp_to_pat e2) typ 
      | Constant c, args when is_constructor env ty c.descr -> 
        mk_pconst loc c (List.map exp_to_pat args) typ
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
(*        Reporting.print_debug_exp "Cheated on set expression" [e]; *)
        transform_exp loc e ty
      | _ -> (* Reporting.print_debug_exp "Untranslatable" [e]; *)transform_exp loc e ty
  and exps_to_pats es = Seplist.map exp_to_pat es in
  exp_to_pat e

let find_some f l = try Some(List.find f l) with Not_found -> None

let convert_output env gen_rn exps mask = 
  let (check_rename, transform_exp, bound, equalities) = gen_rn () in
  let outargs = map_filter id (List.map2 (fun exp inarg ->
    if inarg then None
    else Some (exp_to_pat env exp check_rename transform_exp)
  ) exps mask) in
  (outargs, !bound, !equalities)

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

  (* pat a -> exp a -> exp m b -> exp m b *)
  val mk_let : Typed_ast.env -> Ast.l -> Typed_ast.pat -> Typed_ast.exp -> Typed_ast.exp -> Typed_ast.exp

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
        mk_app l (mk_app l (mk_const_exp env l "list_map" [a;b]) fn None) lst None
      | _ -> failwith "???"
        
  let mk_list_concat env l lst = 
    let t = remove_list (remove_list (exp_to_typ lst)) in
    let l = loc_trans "mk_list_concat" l in
    mk_app l (mk_const_exp env l "list_concat" [t]) lst None

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

  let mk_let env l p e code = mk_bind env l e p code

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
        then Reporting.report_warning env 
          (Reporting.Warn_general(true, l, "non-exhaustive patterns in inductive relation"));
        if props.Patterns.overlapping_pats <> []
        then Reporting.report_warning env
          (Reporting.Warn_general(true, l, "overlapping patterns in inductive relation")));
    mk_case_exp false l v pats (mk_type t)
end

(* TODO : merge with LemOptionMonad ? *)
module Context_option_pre = struct

  let mk_type ty = 
    { Types.t = Types.Tapp([ty], mk_string_path ["Maybe"] "maybe") } 

  let remove_type ty = 
    match ty.t with
      | Types.Tapp([ty], _) -> ty
      | _ -> failwith "???"

  let mk_none env l ty = mk_const_app env l "maybe_nothing" [ty] [] 
  let mk_some env l e = mk_const_app env l "maybe_just" [exp_to_typ e] [e]
  let mk_pnone env l ty = mk_pconst_pat env l "maybe_nothing" [ty] []
  let mk_psome env l p = mk_pconst_pat env l "maybe_just" [p.typ] [p]

  let mk_return env l e = mk_some env l e

  let mk_failure env l ty = mk_none env l ty

  let mk_let env l pat exp code = 
    let l = loc_trans "mk_let" l in
    mk_case_exp false l exp
      [(pat, code);
       (mk_pwild l None (exp_to_typ exp), 
        mk_none env l (remove_option (exp_to_typ code)))]
      (exp_to_typ code)

  let mk_bind env l call pat code = 
    let l = loc_trans "mk_bind" l in
    mk_case_exp false l call
      [(mk_psome env l pat, code);
       (mk_pwild l None (exp_to_typ call), mk_none env l (remove_option (exp_to_typ code)))]
      (exp_to_typ code)

  let mk_cond env l cond code = 
    let l = loc_trans "mk_cond" l in
    mk_if_exp l cond code (mk_none env l (remove_option (exp_to_typ code)))

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

let get_witness_type env reldescr = 
  let c = c_env_lookup reldescr.rel_loc env.c_env reldescr.rel_const_ref in
  match c.relation_info with
    | Some(ri) -> ri.ri_witness
    | None -> None

let out_ty_from_mode env reldescr (mode, wit, _out) = 
  let ret = map_filter (function
    | (Rel_mode_out,x) -> Some x
    | _ -> None
  ) (List.map2 (fun x y -> (x,y)) mode reldescr.rel_argtypes) in
  let ret = 
    if not wit
    then ret
    else match get_witness_type env reldescr with
      | None -> failwith "Invalid mode, should have been rejected before"
      | Some(t,_) -> ret@[{t=Tapp([],t)}]
  in
  mk_tup_unit_typ ret
        
let in_tys_from_mode env reldescr (mode, _wit, _out) = 
  map_filter (function
    | (Rel_mode_in,x) -> Some x
    | _ -> None
  ) (List.map2 (fun x y -> (x,y)) mode reldescr.rel_argtypes)

let ty_from_mode env reldescr ((_,_,out) as mode) = 
  let args = in_tys_from_mode env reldescr mode in
  let ret = out_ty_from_mode env reldescr mode in
  let module M = (val select_module out : COMPILATION_CONTEXT) in
  mk_fun_ty args (M.mk_type ret)

module Compile(M : COMPILATION_CONTEXT) = struct
  
  let rec compile_code env loc code : exp = 
    let l = loc_trans "compile_code" loc in
    match code with
      | RETURN(exps) -> 
        let ret = mk_tup_unit_exp l exps in
        M.mk_return env l ret
      | IF(cond, code) -> 
        let subexp = compile_code env loc code in 
        M.mk_cond env l cond subexp
      | IFEQ(e1,e2,code) ->
        let subexp = compile_code env loc code in
        let cond = mk_eq_exp env e1 e2 in
        M.mk_cond env l cond subexp
      | LET(p,e,code) ->
        let subexp = compile_code env loc code in
        M.mk_let env l p e subexp
      | CALL(n_ref, inp, outp, code) ->
        let subexp = compile_code env loc code in
        let func = mk_const_ref env l n_ref [] in
        let call = List.fold_left (fun func arg -> mk_app l func arg None) 
          func inp in
        let pat = mk_tup_unit_pat l outp in
        M.mk_bind env l call pat subexp
          
  let compile_rule env (loc, patterns, code) = 
    let pattern = mk_tup_unit_pat (loc_trans "compile_rule" loc) patterns in
    let lemcode = compile_code env loc code in
    (pattern, lemcode) 

  let compile_function env reldescr (n,n_ref,mode,mty,rules) : funcl_aux =
    let l = loc_trans "compile_function" reldescr.rel_loc in 
    let gen_name = make_namegen Nset.empty in
    let vars = List.map 
      (fun ty -> Name.add_lskip (gen_name (Ulib.Text.of_latin1 "input")), ty)
      (in_tys_from_mode env reldescr mode) in
    let tuple_of_vars = mk_tup_unit_exp l (List.map (fun (var,ty) -> mk_var l var ty) vars) in
    let pats_of_vars = List.map (fun (var,ty) -> mk_pvar_ty l var ty) vars in
    let cases = List.map (compile_rule env) rules in
    let output_type = out_ty_from_mode env reldescr mode in
    (* Generate a list of binds and concat them ! *)
    let body = M.mk_choice env l output_type tuple_of_vars cases in
    let annot = { term = Name.add_lskip n;
                  locn = l;
                  typ = mty;
                  rest = () } in
    (annot, n_ref, pats_of_vars, Some(space, t_to_src_t (M.mk_type output_type)), space, body)
end

let compile_function env reldescr 
    ((n,((_,_,out_mode) as mode),mty,rules) as m) = 
  let module M = (val select_module out_mode : COMPILATION_CONTEXT) in
  let module C = Compile(M) in
  let rel_info = c_env_lookup_rel_info reldescr.rel_loc env.c_env reldescr.rel_const_ref in
  let fun_ref = List.assoc mode rel_info.ri_fns in
  C.compile_function env reldescr (n,fun_ref,mode,mty,rules)


let compile_to_typed_ast env prog =
  let l = Ast.Trans (true, "compile_to_typed_ast", None) in
  let defs = Nfmap.map (fun _rel (reldescr, modes) ->
    List.map (compile_function env reldescr) modes 
  ) prog in
  let defs = sep_newline (Nfmap.fold (fun l _ c -> c@l) [] defs) in
  let fdefs = Fun_def(None, FR_rec None, Targets_opt_none, defs) in
  ((Val_def fdefs, None), l)

module Compile_list = Compile(Context_list)
module Compile_pure = Compile(Context_pure)
module Compile_unique = Compile(Context_unique)
module Compile_option = Compile(Context_option)

open Typecheck_ctxt

let gen_consname relname = Name.from_string (Name.to_string relname ^ "_witness")

let mk_name_l n = (Name.add_lskip n , Ast.Unknown)

let make_typedef env loc td_l =
  let loc = loc_trans "make_typedef" loc in
  let t_def_l = Nfmap.fold (fun acc _ (r_ref, t_name, t_path, t_constr_l) ->
    let r_info = c_env_lookup_rel_info loc env.c_env r_ref in
    let c_ref_m = match r_info.ri_witness with
      | Some(_, c_ref_m) -> c_ref_m
      | _ -> failwith "No witness"
    in
    let c_def_l = List.map (fun (c_rule, c_name, c_args) ->
      let Some(c_ref) = Nfmap.apply c_ref_m c_rule in
      let c_args = sep_no_skips (List.map t_to_src_t c_args) in
      (mk_name_l c_name, c_ref, None, c_args)
    ) t_constr_l in
    let t_exp = Te_variant(None, sep_no_skips c_def_l) in
    let (_,t_name) = Path.to_name_list t_path in
    (mk_name_l t_name, [], t_path, t_exp, None)::acc
  ) [] td_l
  in
  Type_def(newline, sep_no_skips t_def_l)

let register_types rel_loc ctxt mod_path tds = 
  Nfmap.fold (fun ctxt relname (rel_ref, tname, type_path, tconstrs) ->
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
    let ctxt = add_p_to_ctxt ctxt (tname, (type_path,l)) in
(*    let cnames = List.fold_left (fun s (_,cname,_) -> NameSet.add cname s) 
      NameSet.empty tconstrs in *)
    let mk_descr c_env cname cargs =
      let ty = mk_fun_ty cargs {t=Tapp([],type_path)} in
      let descr = {
        const_binding = Path.mk_path mod_path cname;
        const_tparams = [];
        const_class = [];
	const_no_class = Target.Targetmap.empty;
        const_ranges = [];
        const_type = ty;
        relation_info = None;
        env_tag = K_constr;
        const_targets = Target.Targetset.empty;
        spec_l = l;
        target_rename = Target.Targetmap.empty;
        target_rep = Target.Targetmap.empty;
        target_ascii_rep =  Target.Targetmap.empty;
        compile_message = Target.Targetmap.empty;
        termination_setting = Target.Targetmap.empty;
      } in
      let (c_env, c_ref) = c_env_store c_env descr in
      (c_env, cname, c_ref)
    in
    let (c_env, constrs) = List.fold_left 
      (fun (c_env, constrs) (crule, cname, cargs) ->
        let (c_env, c_d, c_ref) = mk_descr c_env cname cargs in
        (c_env, (crule, cname, c_ref)::constrs))
      (ctxt.ctxt_c_env, []) tconstrs in
    let ctxt = {ctxt with ctxt_c_env = c_env} in
    let constrs_map = Nfmap.from_list (List.map (fun (u,_,v) -> u,v) constrs) in
    let rel_descr = c_env_lookup_rel_info l ctxt.ctxt_c_env rel_ref in
    let rel_descr = {rel_descr 
                     with ri_witness = Some(type_path, constrs_map)} in
    let ctxt = {ctxt with ctxt_c_env = 
        c_env_update_rel_info l ctxt.ctxt_c_env rel_ref rel_descr } in
    let ctxt = List.fold_left (fun ctxt (crule, cname, c_ref) ->
      let () = 
        match Nfmap.apply ctxt.new_defs.v_env cname with
          | None -> ()
          | Some(_) -> raise_error l "Name already used" Name.pp cname
      in
      let ctxt = add_v_to_ctxt ctxt (cname, c_ref) in
      ctxt
    ) ctxt constrs in
    let constrset = {
      constr_list = List.map (fun (_,_,u) -> u) constrs;
      constr_exhaustive = true;
      constr_case_fun = None;
      constr_default = true;
      constr_targets = Target.all_targets;
    } in
    let tdescr = { type_tparams = []; 
                   type_abbrev = None;
                   type_varname_regexp = None;
                   type_fields = None;
                   type_constr = [constrset];
                   type_rename = Target.Targetmap.empty;
                   type_target_rep = Target.Targetmap.empty
                 }
    in
    let ctxt = add_d_to_ctxt ctxt type_path (Tc_type tdescr) in
    ctxt
  ) ctxt tds 

(* TODO : || -> either, && -> *, forall -> (->), exists -> ... *)
let gen_witness_type_aux (env : env) mod_path l names rules warn_incomplete = 
  let rels = get_rels env l names rules in
  let localrels = Nfmap.fold (fun localrels relname reldescr ->
    Cdmap.insert localrels (reldescr.rel_const_ref, reldescr)
  ) Cdmap.empty rels 
  in
  (* Return (maybe) the witness type for a relation. *)
  let relation_witness e = match exp_to_term e with
    | Constant {descr=c_ref} ->
      begin match Cdmap.apply localrels c_ref with
        | Some r -> 
          begin match r.rel_witness with
            | Some n -> Some({t=Tapp([], Path.mk_path mod_path n)})
            | None -> raise_error l "no witness for relation" Name.pp r.rel_name
          end
        | None ->
          let c_d = c_env_lookup l env.c_env c_ref in
          begin match c_d with
            | {env_tag = K_relation; 
               relation_info = Some({ri_witness = Some(p,_)})} ->
              Some({t = Tapp([], p)})
            | {env_tag = K_relation} -> 
              raise_error l "no witness for relation" Path.pp c_d.const_binding
            | _ -> None
          end
      end
    | _ -> None
  in
  (* Check whether an expression contains the name of an inductive 
     relation and emit a warning in this case *)
  let is_relation c_ref = 
    Cdmap.in_dom c_ref localrels
          || (let c_d = c_env_lookup l env.c_env c_ref in c_d.env_tag = K_relation)
  in
  let check_complete = match warn_incomplete with
    | false -> ignore
    | true -> fun e ->
      let entities = add_exp_entities empty_used_entities e in
      if List.exists is_relation entities.used_consts
      then Reporting.report_warning env
        (Reporting.Warn_general(false, l, "An incomplete witness will be generated"))
  in
  let is_head_relation e =
    let (head, args) = split_app e in
    match relation_witness head with
      | Some v -> List.iter check_complete args; Some v
      | None -> check_complete e; None
  in
  let tds = Nfmap.fold (fun tds relname reldescr ->
    match reldescr.rel_witness with
      | None -> tds
      | Some(typename) ->
        let constructors = List.map (fun rule  ->
          let consname = gen_consname rule.rule_name in
          let vars_ty = List.map (fun (_,t) -> t) rule.rule_vars in
          let conds_ty = map_filter 
            (fun cond -> is_head_relation cond) rule.rule_conds in
          let argstypes = vars_ty @ conds_ty in
          (rule.rule_name, consname, argstypes)
        ) reldescr.rel_rules in
        Nfmap.insert tds (relname, (reldescr.rel_const_ref, typename, Path.mk_path mod_path typename, constructors))
  ) Nfmap.empty rels in
  tds

let gen_witness_type_info l mod_path ctxt names rules = 
  let env = defn_ctxt_to_env ctxt in
  let tds = gen_witness_type_aux env mod_path l 
    names rules true in
  let newctxt = register_types l ctxt mod_path tds in
  newctxt

let gen_witness_type_def env l mpath localenv names rules local =
  let l = loc_trans "gen_witness_type_def" l in
  let tds = gen_witness_type_aux env mpath l
    names rules false in
  let r = if Nfmap.is_empty tds then []
  else [(make_typedef env l tds, None),  l, local] in
  r

let ctxt_mod update ctxt = 
  { ctxt with
    cur_env = update ctxt.cur_env;
    new_defs = update ctxt.new_defs
  }

let gen_witness_check_info l mod_path ctxt names rules =
  let env = defn_ctxt_to_env ctxt in
  let rels = get_rels env l names rules in
  let defs = Nfmap.fold (fun defs relname reldescr ->
    match reldescr.rel_check with
      | None -> defs
      | Some(check_name) -> 
        let rules = reldescr.rel_rules in
        let ret = List.map exp_to_typ (List.hd rules).rule_args in
        let check_path = Path.mk_path mod_path check_name in
        let rel_info = c_env_lookup_rel_info l ctxt.ctxt_c_env reldescr.rel_const_ref in
        let witness_type = match rel_info.ri_witness with
          | Some(p,_) -> {t = Tapp([],p)}
          | None -> raise_error l
            "no witness for relation while generating witness-checking function"
            Path.pp check_path
        in
        let check_type = {t=Tfn(witness_type, mk_option (mk_tup_unit_typ ret))} in
        Cdmap.insert defs (reldescr.rel_const_ref, (check_name, check_path, check_type))
  ) Cdmap.empty rels in
  (* Register the functions *)
  Cdmap.fold (fun ctxt rel_ref (cname,cpath,ctype) ->
    let c_descr = {
      const_binding = cpath;
      const_tparams = [];
      const_class = [];
      const_no_class = Target.Targetmap.empty;
      const_ranges = [];
      const_type = ctype;
      relation_info = None;
      env_tag = K_let;
      const_targets = Target.all_targets;
      spec_l = loc_trans "gen_witness_check_info" l;
      target_rename = Target.Targetmap.empty;
      target_rep = Target.Targetmap.empty;
      target_ascii_rep =  Target.Targetmap.empty;
      compile_message = Target.Targetmap.empty;
      termination_setting = Target.Targetmap.empty;
    } in
    let c_env, c_ref = c_env_store ctxt.ctxt_c_env c_descr in
    let ctxt = { ctxt with ctxt_c_env = c_env } in
    let ctxt = add_v_to_ctxt ctxt (cname, c_ref) in
    let r_info = c_env_lookup_rel_info l ctxt.ctxt_c_env rel_ref in
    let r_info = {r_info with ri_check = Some c_ref} in
    {ctxt with ctxt_c_env = c_env_update_rel_info l ctxt.ctxt_c_env rel_ref r_info }
  ) ctxt defs

let nset_of_list l = List.fold_left (fun set x -> Nset.add x set) Nset.empty l

open LemOptionMonad

let gen_witness_check_def env l mpath localenv names rules local = 
  let rels = get_rels env l names rules in
  let mkloc = loc_trans "gen_witness_check_def" in
  let l = mkloc l in
  let defs = Nfmap.map (fun relname -> function
    | {rel_check = None} -> None
    | {rel_check = Some(def_name)} as reldescr ->
    let rel_info = c_env_lookup_rel_info l env.c_env reldescr.rel_const_ref in
    let (wit_path, wit_constr_m) = match rel_info.ri_witness with
      | Some x -> x
      | None -> failwith "No witness type"
    in
    let wit_ty = {t=Tapp([], wit_path)} in
    let pats = List.map (fun rule ->
      let constr_ref = match Nfmap.apply wit_constr_m rule.rule_name with
        | Some c_ref -> c_ref
        | None -> failwith "No constructor for rule"
      in
      let gen_name = make_namegen Nset.empty in
      let l = mkloc rule.rule_loc in
      let is_rel_or_aux e =
        let (head, args) = split_app e in
        match exp_to_term head with
          | Constant {descr=c_ref} ->
            let c_d = c_env_lookup l env.c_env c_ref in
            begin match c_d with
              | {env_tag = K_relation;
                 relation_info = Some({
                   ri_witness = Some(p, _);
                   ri_check = Some(check_ref)
                 })} ->
                Left(args, p, check_ref)
              | {env_tag = K_relation} -> 
                raise_error (exp_to_locn e)
                  "no witness checking function for relation"
                  Path.pp c_d.const_binding
              | _ -> Right e
            end
          | _ -> Right e
      in
      let (relconds,auxconds) = map_partition is_rel_or_aux rule.rule_conds in
       let relconds = List.map (fun (args,witness_path,check_ref) ->
        let witness_ty = {t=Tapp([],witness_path)} in
        let witness_name = gen_name (Ulib.Text.of_latin1 "witness") in
        (args, witness_ty, check_ref, witness_name)
      ) relconds in
      let pvars = List.map 
        (fun (var,typ) -> mk_pvar l (Name.add_lskip var) typ) rule.rule_vars in
      let pconds = List.map
        (fun (_,witness_ty,_,var) -> 
          mk_pvar l (Name.add_lskip var) witness_ty
        ) relconds in
      let constr_id = { id_path = Id_none None;
                        id_locn = l;
                        descr = constr_ref;
                        instantiation = [] } in
      let pattern = mk_pconst l constr_id (pvars @ pconds) None in
      let ret = mk_some env 
        (mk_tup_unit_exp l rule.rule_args) in
      let genconds_exps = List.map (fun (args,witness_ty,check_ref,witness) ->
        let witness_var = mk_var l (Name.add_lskip witness) witness_ty in
        let rhs = mk_some env (mk_tup_unit_exp l args) in
        let check_id = { id_path = Id_none None; id_locn = l;
                         descr = check_ref; instantiation = [] } in
        let check_fun = mk_const l check_id None in
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
    ) reldescr.rel_rules in
    let x = Name.add_lskip (make_namegen Nset.empty (Ulib.Text.of_latin1 "x")) in
    let xpat = mk_pvar_ty l x wit_ty in
    let xvar = mk_var l x wit_ty in
    let return_ty = exp_to_typ (snd (List.hd pats)) in
    let body = mk_case_exp false l xvar pats return_ty in
    let annot = { term = Name.add_lskip def_name;
                  locn = l;
                  typ = {t=Tfn(wit_ty,return_ty)};
                  rest = () } in
    let c_ref = match rel_info.ri_check with
      | Some c_ref -> c_ref
      | None -> failwith "Checking function not registered"
    in
    Some(annot, c_ref, [xpat], Some(space, t_to_src_t return_ty), space, body)

  ) rels in
  let defs = map_filter id (Nfmap.fold (fun l _ v -> v::l) [] defs) in
  let def = Fun_def(newline, FR_rec None, Targets_opt_none, sep_newline defs) in
  if defs = [] then []
  else [((Val_def def, None), l, local)]

let pp_mode ppf (io, wit, out) = 
  List.iter (function 
    | Rel_mode_in -> Format.fprintf ppf "input -> " 
    | Rel_mode_out -> Format.fprintf ppf "output -> "
  ) io;
  Format.fprintf ppf "%s" 
    (match out with
      | Out_pure -> ""
      | Out_list -> "list"
      | Out_option -> "maybe"
      | Out_unique -> "unique"
    );
  if wit then Format.fprintf ppf " witness"
  else Format.fprintf ppf " unit"


let report_no_translation reldescr ruledescr mode print_debug =
  if print_debug then begin
    Format.eprintf "No transalation for relation %s, mode %a\n"
      (Name.to_string reldescr.rel_name) pp_mode mode;
    Format.eprintf "Blocking rule is %s\n"  (Name.to_string ruledescr.rule_name)
  end;
  no_translation None


let transform_rule env localrels ((mode, need_wit, out_mode) as full_mode) rel (rule : ruledescr) print_debug = 
  let l = loc_trans "transform_rule" rule.rule_loc in
  let vars = Nfmap.domain (Nfmap.from_list rule.rule_vars) in
  (* TODO : we probably don't need localrels here *)
  let avoid = Nfmap.fold (fun avoid relname reldescr ->
    List.fold_left (fun avoid (funname, _) -> Nset.add funname avoid)
      (Nset.add relname avoid) reldescr.rel_indfns
  ) Nset.empty localrels in
  let gen_rn = make_renamer vars avoid in
  let (patterns, initknown, initeqs) = 
    convert_output env gen_rn rule.rule_args (List.map (fun x -> x = Rel_mode_out) mode) in
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
      match exp_to_term e, args with
        | Constant {descr = eq_ref}, [u;v] when eq_ref = eq_const_ref env ->
          Right(Left(u,v))
        | Constant {descr = c_ref}, _ ->
          let c_d = c_env_lookup l env.c_env c_ref in
          begin match c_d with
            | {env_tag = K_relation} ->
              let relinfo = c_env_lookup_rel_info l env.c_env c_ref in
              Left(relinfo.ri_fns , args, gen_witness_var relinfo)
            | _ -> Right(Right(x))
          end
        | _ -> Right(Right(x))
    ) rule.rule_conds
  in
  let (usefuleqs, sideconds) = map_partition id sideconds in
  (* map_filter drops relations with no witnesses.
     it's not a problem because if our relation has a witness, all these
     relations must have one *)
  let witness_var_order = map_filter (fun (_,_,var) -> var) indconds in
  let returns = map_filter (function
    | (Rel_mode_in, _) -> None
    | (Rel_mode_out, r) -> Some(r)
  ) (List.map2 (fun x y -> (x,y)) mode rule.rule_args) in
  let returns = 
    if not need_wit then returns
    else
      let rel_info = c_env_lookup_rel_info l env.c_env rel.rel_const_ref in
      let wit_constrs = match rel_info.ri_witness with
        | None -> failwith "Generating witness for a relation without witness"
        | Some(_,wit_constrs) -> wit_constrs
      in
      let constr_descr_ref = match Nfmap.apply wit_constrs rule.rule_name with
        | None -> failwith "No witness constructor for rule"
        | Some(constr_descr_ref) -> constr_descr_ref
      in
      let args = rule.rule_vars @ witness_var_order in
      let args = List.map
        (fun (name,ty) -> mk_var l (Name.add_lskip name) ty) args in
      let constr_id = {id_path = Id_none None; id_locn = Ast.Unknown;
                       descr = constr_descr_ref; instantiation = []} in
      let constr = mk_const l constr_id None in
      let wit = List.fold_left (fun u v -> mk_app l u v None) constr args in
      returns@[wit]
  in
  let rec build_code known indconds sideconds eqconds usefuleqs =
    let exp_known e = Nfmap.fold (fun b v _ -> b && Nset.mem v known) 
      true (C.exp_to_free e) in
    let (selected_eqs,eqconds2) = 
      List.partition (fun (e1,e2) -> exp_known e1 && exp_known e2) eqconds in
    let (selected_side,sideconds2) = 
      List.partition (fun e -> exp_known e) sideconds in
    let add_eq eq x = List.fold_left (fun x (e1,e2) -> IFEQ(e1,e2,x)) x eq in
    let add_side side x = List.fold_left (fun x e -> IF(e,x)) x side in
    let rec search_ind notok = function
      | [] ->
        begin match eqconds2,sideconds2 with
          | [], [] when notok = [] && List.for_all exp_known returns -> 
            RETURN returns
          | _ -> report_no_translation rel rule full_mode print_debug
        end
      | (modes,args,wit_var) as c::cs ->
        let inargs = List.map exp_known args in
        let mode_matches ((fun_mode, fun_wit, fun_out_mode),_info) = 
          List.for_all (fun x -> x)
            (List.map2 (fun inp m -> inp || m = Rel_mode_out) inargs fun_mode)
            && (not need_wit || fun_wit) 
            && (fun_out_mode = out_mode)
        in
        match List.filter mode_matches modes with
          | [] -> search_ind (c::notok) cs
          | ((fun_mode, fun_wit, _out_mode), fun_ref) ::ms -> 
            let (outputs, bound, equalities) = convert_output env gen_rn args 
              (List.map (fun m -> m = Rel_mode_in) fun_mode) in
            let outputs = match wit_var with
              | Some(wit_name, wit_ty) when fun_wit ->
                outputs @ [mk_pvar l (Name.add_lskip wit_name) wit_ty]
              | _ -> outputs
            in
            let inputs = map_filter id (List.map2 (fun exp m ->
              match m with
                | Rel_mode_in -> Some(exp)
                | Rel_mode_out -> None
            ) args fun_mode) in
            CALL(fun_ref, inputs, outputs,
                 build_code (Nset.union bound known) (cs@notok) 
                   sideconds2 (equalities@eqconds2) usefuleqs)
    in
    let use_eq usefuleqs u v = 
      (* u is known, v is (maybe) unknown *)
      let ([output], bound, equalities) = convert_output env gen_rn [v] [false] in
      LET(output, u, 
          build_code (Nset.union bound known) indconds
            sideconds2 (equalities@eqconds2) usefuleqs)
    in
    let rec search_eq notok = function
      | [] -> search_ind [] indconds
      | (u,v)::es when exp_known u -> use_eq (notok@es) u v
      | (u,v)::es when exp_known v -> use_eq (notok@es) v u
      | e::es -> search_eq (e::notok) es
    in
    add_eq selected_eqs (add_side selected_side (search_eq [] usefuleqs))
  in
  (l, patterns, build_code initknown indconds sideconds initeqs usefuleqs)


let transform_rules env localrels mode reldescr print_debug =
  List.map (fun x -> transform_rule env localrels mode reldescr x print_debug) 
    reldescr.rel_rules


(* env is the globalized env *)
(* For each relation : we assume all modes are possible (via updating reldescr)
   and then try to see what mode can effectively computed from that.
   We then try to get the least fixed point
*)
let join f a b = 
  List.concat (List.map (fun x -> List.map (fun y -> f x y ) b) a)

let gen_fns_info_aux l mod_path ctxt rels =
  let env = defn_ctxt_to_env ctxt in
  Nfmap.fold (fun ctxt relname reldescr ->
    let rel_ref = reldescr.rel_const_ref in
    List.fold_left (fun ctxt (name, mode) ->
      let ty = ty_from_mode env reldescr mode in
      let path = Path.mk_path mod_path name in
      let f_descr = {
        const_binding = path;
        const_tparams = [];
        const_class = [];
	const_no_class = Target.Targetmap.empty;
        const_ranges = [];
        const_type = ty;
        relation_info = None;
        env_tag = K_let;
        const_targets = Target.all_targets;
        spec_l = l;
        target_rep = Target.Targetmap.empty;
        target_rename = Target.Targetmap.empty;
        target_ascii_rep =  Target.Targetmap.empty;
        compile_message = Target.Targetmap.empty;
        termination_setting = Target.Targetmap.empty;
      } in
      let c_env, f_ref = c_env_store ctxt.ctxt_c_env f_descr in
      let ctxt = { ctxt with ctxt_c_env = c_env } in
      let ctxt = add_v_to_ctxt ctxt (name, f_ref) in
      let r_info = c_env_lookup_rel_info l ctxt.ctxt_c_env rel_ref in
      let r_info = {r_info with ri_fns = (mode, f_ref)::r_info.ri_fns} in
      {ctxt with ctxt_c_env = c_env_update_rel_info l ctxt.ctxt_c_env rel_ref r_info }
    ) ctxt reldescr.rel_indfns
  ) ctxt rels


let list_possible_modes mod_path ctxt rels =
  let all_modes =
    let gen_name = make_namegen Nset.empty in
    Nfmap.map (fun _ reldescr ->
      let out_modes = [Out_pure] in
      let wit_modes = if reldescr.rel_witness = None then [false] else [false;true] in
      let io_modes = List.fold_left 
        (fun acc _ -> join (fun x y -> x::y) [Rel_mode_in; Rel_mode_out] acc) 
        [[]] reldescr.rel_argtypes in
      let modes = join (fun (x,y) z -> (gen_name (Ulib.Text.of_latin1 "indfn"), (x,y,z))) (join (fun x y -> (x,y)) io_modes wit_modes) out_modes in
      { reldescr with rel_indfns = modes }
    ) rels
  in
  let modeset_equals rels1 rels2 = 
    Nfmap.fold (fun acc _ x -> acc && x) true
      (Nfmap.merge (fun _ a b -> match a, b with
        | None, None -> Some(true)
        | Some(rd1), Some(rd2) -> 
          Some(List.length rd1.rel_indfns = List.length rd2.rel_indfns 
              && List.for_all (fun e -> List.mem e rd2.rel_indfns) rd1.rel_indfns)
        | _ -> Some(false)) rels1 rels2)
  in
  let shrink_modeset rels =
    let ctxt = gen_fns_info_aux Ast.Unknown mod_path ctxt rels in
    let env = defn_ctxt_to_env ctxt in
    Nfmap.map (fun _ reldescr ->
      { reldescr with rel_indfns = List.filter (fun (_,mode) ->
        try
          ignore (transform_rules env rels mode reldescr false); 
          true
        with _ -> false
      )  reldescr.rel_indfns}
    ) rels
  in
  let rec iter rels = 
    let newrels = shrink_modeset rels in
    if modeset_equals rels newrels
    then rels
    else iter newrels
  in
  let modes = iter all_modes in
  Nfmap.iter (fun _ reldescr ->
    Format.eprintf "** Relation %s :\n" (Name.to_string reldescr.rel_name);
    List.iter (fun (_, mode) -> Format.eprintf "%a\n" pp_mode mode) reldescr.rel_indfns
  ) modes;
  flush stderr;
  modes

let gen_fns_info l mod_path (ctxt : defn_ctxt) names rules =
  let env = defn_ctxt_to_env ctxt in
  let rels = get_rels env l names rules in
  let l = loc_trans "gen_fns_info" l in
(*  list_possible_modes mod_path ctxt rels;  *)
  gen_fns_info_aux l mod_path ctxt rels

let gen_fns_def env l mpath localenv names rules local =
  let rels = get_rels env l names rules in
  let transformed_rules = Nfmap.map (fun relname reldescr ->
    (reldescr, List.map (fun (name, mode) ->
      (name, mode, ty_from_mode env reldescr mode,transform_rules env rels mode reldescr true)
    ) reldescr.rel_indfns)
  ) rels in
  let u,v = compile_to_typed_ast env transformed_rules in
  let code = u,v,local in
  let emptydef = 
    Nfmap.fold (fun b _ (_,l) -> b && [] = l) true transformed_rules in
  if emptydef then []
  else [code]

let gen_witness_type_macro env mpath localenv def =
  match def with
    | (Indreln(x,y,names,rules),z), l, local ->
      let remove_witness = 
        function RName(a,a',b,c,d,_witness,f,g,h) ->
          RName(a,a',b,c,d,None,f,g,h)
      in
      let def = (Indreln(x,y,Seplist.map remove_witness names, rules),z),l,local in
      let tdefs = gen_witness_type_def env l mpath localenv names rules local in
      if tdefs = []
      then None
      else Some(localenv, def::tdefs)
    | _ -> None

let gen_witness_check_macro env mpath localenv def_ =
  match def_ with
    | (Indreln(x,y,names,rules),z), l, local ->
      let remove_check = 
        function RName(a,a',b,c,d,e,_check,g,h) ->
           RName(a,a',b,c,d,e,None,g,h)
      in
      let def = (Indreln(x,y,Seplist.map remove_check names, rules),z),l,local in
      let cdefs = gen_witness_check_def env l mpath localenv names rules local in
      if cdefs = []
      then None
      else Some(localenv, def::cdefs)
    | _ -> None

let gen_fns_macro env mpath localenv def =
  match def with
    | (Indreln(x,y,names,rules),z), l, local ->
      let remove_indfns = 
        function RName(a,a',b,c,d,e,f,_indfns,h) ->
          RName(a,a',b,c,d,e,f,None,h)
      in
      let def = (Indreln(x,y,Seplist.map remove_indfns names, rules),z),l,local in
      let fdefs = gen_fns_def env l mpath localenv names rules local in
      if fdefs = []
      then None
      else Some(localenv, def::fdefs)
    | _ -> None

end
