(* Converting a relation *)

open Typed_ast
open Types
open Util
open Typed_ast_syntax

(* Notes on names :
 Name.strip_lskip
 Name.add_lskip

type ('a,'b) annot = { term : 'a; locn : Ast.l; typ : t; rest : 'b }

*)

module Converter(C : Exp_context) = struct

module C = Exps_in_context(C)
open C

module Nmap = Typed_ast.Nfmap
module Nset = Nmap.S

(* Split on infix (&&) : ((a && b) && (c && d)) && true -> [a;b;c;d] *)

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

(* TODO : Un-Option the name *)
let get_rels (l: Typed_ast.rule lskips_seplist) =
  List.fold_left (fun s (Rule(rulename,_,_,vars,_,cond,_,rel,args)) ->
    let rulename = Name.strip_lskip rulename in
    let relname = Name.strip_lskip rel.term in
    let rulecond = match cond with
      | Some x -> x
      | None -> C.mk_lit Ast.Unknown ({term = L_true None; locn = Ast.Unknown; typ =  {t = Tapp([], Path.boolpath)}; rest = ()}) None in
    let vars = List.map (function
      | QName(n) -> n
      | Name_typ(_,n,_,_,_) -> n
    ) vars in
    let ruledescr = (rulename, List.map (fun v -> (Name.strip_lskip v.term, v.typ) ) vars, split_and rulecond, args) in
    match Nmap.apply s relname with
      | None -> Nmap.insert s (relname, [ruledescr])
      | Some rules -> Nmap.insert s (relname, ruledescr::rules)
  ) Nfmap.empty (Seplist.to_list l)
(*
let get_rels (l : (Name.lskips_t option * lskips * name_lskips_annot list * lskips * exp option * lskips * name_lskips_annot * exp list) lskips_seplist ) = 
  List.fold_left (fun s (rulename,_,vars,_,cond,_,rel,args) ->
    let relname = Name.strip_lskip rel.term in
    let rulecond = match cond with
      | Some x -> x
      | None -> C.mk_lit Ast.Unknown ({term = L_true None; locn = Ast.Unknown; typ =  {t = Tapp([], Path.boolpath)}; rest = ()}) None in
    let ruledescr = (rulename, List.map (fun v -> (Name.strip_lskip v.term, v.typ) ) vars, split_and rulecond, args) in
    match Nmap.apply s relname with
      | None -> Nmap.insert s (relname, [ruledescr])
      | Some rules -> Nmap.insert s (relname, ruledescr::rules)
  ) Nmap.empty (Seplist.to_list l)
*)
type io = I | O
type ep = IExp of exp | OPat of pat
type mode = io list

(* Just a small model of the code we will generate later
   We will need a partial "exp to pattern" function somewhere *)
type code = 
  | IF of exp * code 
  | CALL of Name.t * Types.t * exp list * pat list * code
  | IFEQ of exp * exp * code 
  | LET of pat * exp * code
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
    let check_rename v typ =
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
              equalities := (C.mk_var Ast.Unknown v typ,
                             C.mk_var Ast.Unknown v' typ) :: !equalities;
              n'
          in
          used := Nset.add varname !used;
          seen := Nset.add varname !seen;
          Name.add_lskip varname
        end
    in
    let transform_exp e typ = 
      let n = gen_name (Ulib.Text.of_latin1 "pat") in
      let v = Name.add_lskip n in
      used := Nset.add n !used;
      seen := Nset.add n !seen;
      equalities := (C.mk_var Ast.Unknown v typ, e) :: !equalities;
      C.mk_pvar_annot Ast.Unknown v (C.t_to_src_t typ) (Some typ)
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
    let loc = exp_to_locn e in
    let typ = Some(exp_to_typ e) in
    let ty = exp_to_typ e in
    let (head, args) = split_app e in
    match C.exp_to_term head, args with
      | Constructor c, args -> mk_pconstr loc c (List.map exp_to_pat args) typ
      | Constant cons, [e1;e2] when is_cons cons -> 
        mk_pcons loc (exp_to_pat e1) None (exp_to_pat e2) typ 
      | Var v, [] ->
            mk_pvar_annot loc (check_rename v ty) 
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
        transform_exp e ty
      | _ -> Reporting.print_debug_exp "Untranslatable" [e]; transform_exp e ty
  and exps_to_pats es = Seplist.map exp_to_pat es in
  exp_to_pat e
(* TODO : what is Nvar_e*)

let find_some f l = try Some(List.find f l) with Not_found -> None

let convert_output gen_rn exps mask = 
  let (check_rename, transform_exp, bound, equalities) = gen_rn () in
  let outargs = map_filter id (List.map2 (fun exp inarg ->
    if inarg then None
    else Some (exp_to_pat exp check_rename transform_exp)
  ) exps mask) in
  (outargs, !bound, !equalities)

let report_no_translation rule notok eqconds sideconds =
  let (%) f x = Ulib.Text.to_string (f x) in
  let (_,_,conds,args) = rule in
  Reporting.print_debug_exp "No translation for relation with args" args;
  Reporting.print_debug_exp "Conditions are" conds;
  no_translation None

let transform_rule mode_env _ty mode rule = 
  let (rulename, vars, conds, args) = rule in
  let vars = Nfmap.domain (Nfmap.from_list vars) in
  let gen_rn = make_renamer vars (Nmap.domain mode_env) in
  let (patterns, initknown, initeqs) = 
    convert_output gen_rn args (List.map (fun x -> x = O) mode) in
  (* TODO : we should substitute *)
  let relknowns = 
    Nfmap.fold (fun set rel (_ty,modes) ->
      if List.exists (fun (_n,m,_t) -> List.for_all (fun k -> k = I) m) modes
      then Nset.add rel set
      else set) Nset.empty mode_env in
  let returns = map_filter (function
    | (I, _) -> None
    | (O, r) -> Some(r)
  ) (List.map2 (fun x y -> (x,y)) mode args) in
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
      | (head,modes,args) as c::cs ->
        let inargs = List.map exp_known args in
        let mode_matches (_name,mode,_ty) = 
          List.for_all (fun x -> x) 
            (List.map2 (fun inp m -> inp || m = O) inargs mode) in
        match List.filter mode_matches modes with
          | [] -> search (c::notok) cs
          | (name,mode,ty)::ms -> 
            let (outputs, bound, equalities) = convert_output gen_rn args 
              (List.map (fun m -> m = I) mode) in
            let inputs = map_filter id (List.map2 (fun exp m ->
              match m with
                | I -> Some(exp)
                | O -> None
            ) args mode) in
            CALL(name, ty, inputs, outputs,
                 build_code (Nset.union bound known) (cs@notok) 
                   sideconds2 (equalities@eqconds2))
    in
    add_eq selected_eqs (add_side selected_side (search [] indconds))
  in
  let (indconds, sideconds) = 
    List.fold_left (fun (left, right) x -> 
      let (e, args) = split_app x in
      match Typed_ast_syntax.dest_var_exp e with
        | Some(n) when not (Nset.mem n vars)-> begin
          match Nfmap.apply mode_env n with
            | Some(_ty,modes) -> ((n,modes,args)::left, right)
            | _ -> (left, e::right)
        end
        | _ -> (left, e::right)) ([],[]) conds in
  (patterns, build_code initknown indconds sideconds initeqs)
  


let debug_print_transformed trans = 
  let module B = Backend.Make(struct
    let avoid = (false, (fun _ -> true), Name.fresh)
  end) in
  let (%) f x = Ulib.Text.to_string (f x) in
  let print_compiled (patterns, code) =
    Format.eprintf "PATTERNS: ";
    List.iter (fun pat -> 
      Format.eprintf "[%s] " (B.ident_pat % pat)
    ) patterns;
    Format.eprintf "\n--CODE: \n";
    let rec print_code = function 
      | IF(e,c) -> 
        Format.eprintf "IF [%s]\n" (B.ident_exp % e); 
        print_code c
      | IFEQ(e1,e2,c) -> 
        Format.eprintf "IFEQ [%s] == [%s]\n" (B.ident_exp % e1) (B.ident_exp % e2);
        print_code c
      | CALL(n,ty,inputs, outputs,c) ->
        Format.eprintf "CALL (%s : %s) " (Name.to_rope % n) (B.ident_typ % ty);
        List.iter (fun i->Format.eprintf "[%s] "(B.ident_exp%i)) inputs;
        Format.eprintf "==> ";
        List.iter (fun o->Format.eprintf "[%s] "(B.ident_pat%o)) outputs; 
        Format.eprintf "\n";
        print_code c
      | RETURN returns -> 
        Format.eprintf "RETURN ";
        List.iter (fun exp -> Format.eprintf "[%s] " (B.ident_exp % exp)) returns;
        Format.eprintf "\n"
    in
    print_code code;
    Format.eprintf "--END CODE\n\n";
    Format.pp_print_flush Format.err_formatter ()
  in
  Nfmap.iter (fun rel (_ty, modes) ->
    Format.eprintf "### RELATION : %s\n" (Name.to_rope % rel);
    List.iter (fun (n, mode, _ty, rules) ->
      Format.eprintf "# %s : " (Name.to_rope % n);
      List.iter (function
        | I -> Format.eprintf "I"
        | O -> Format.eprintf "O"
      ) mode;
      Format.eprintf "\n\n";
      List.iter print_compiled rules;
      Format.eprintf "\n\n\n"
    ) modes;
    Format.eprintf "-------------------------------------\n"
  ) trans

let sep_no_skips l = Seplist.from_list_default None l

module Compile_pure_code = struct
(* TODO : not correct (must check excluded & renames) *)
(* TODO : parametrize w/ a monad or something *)
let rec compile_code env excluded renames = function
  | RETURN(exps) -> mk_tup Ast.Unknown None (sep_no_skips exps) None None
  | IF(cond, code) -> 
    let subexp = compile_code env excluded renames code in 
    let undef = mk_undefined_exp Ast.Unknown "Undef" (exp_to_typ subexp) in
    mk_if_exp Ast.Unknown cond subexp undef
  | IFEQ(e1,e2,code) ->
    let subexp = compile_code env excluded renames code in
    let undef = mk_undefined_exp Ast.Unknown "Undef" (exp_to_typ subexp) in
    let cond = mk_eq_exp env e1 e2 in
    mk_if_exp Ast.Unknown cond subexp undef
  | CALL(n, ty, inp, outp, code) ->
    let subexp = compile_code env excluded renames code in
    let undef = mk_undefined_exp Ast.Unknown "Undef" (exp_to_typ subexp) in
    let call = List.fold_left (fun func arg -> mk_app Ast.Unknown func arg None) 
      (mk_var Ast.Unknown (Name.add_lskip n) ty) inp in
    let pat = mk_ptup Ast.Unknown None (sep_no_skips outp) None None in
    mk_case_exp false Ast.Unknown call
      [(pat, subexp);
       (mk_pwild Ast.Unknown None (exp_to_typ call),undef)] 
      (exp_to_typ subexp)

let compile_rule env (patterns, code) = 
  let pattern = mk_ptup Ast.Unknown None (sep_no_skips patterns) None None in
  let lemcode = compile_code env Nset.empty Nfmap.empty code in
  (pattern, lemcode) 


(* TODO : check overlap *)
let compile_to_typed_ast env prog =
  let funcs = Nfmap.fold (fun l _ (_ty,funcs) -> 
    (List.map (fun (name, _, _, _) -> name) funcs)@l) [] prog in
  let fun_names = List.fold_right Nset.add funcs Nset.empty in
  let defs = Nfmap.map (fun _rel (ty,modes) ->
    List.map (fun (n, mode, mty, rules) ->
      let gen_name = make_namegen fun_names in
      let vars = map_filter (function 
        | (I, ty) -> Some(Name.add_lskip (gen_name (Ulib.Text.of_latin1 "input")),
                          ty)
        | (O, _) -> None
      ) (List.combine mode ty) in
      let tuple_of_vars = mk_tup Ast.Unknown None (sep_no_skips (List.map (fun (var,ty) -> mk_var Ast.Unknown var ty) vars)) None None in
      let pats_of_vars = List.map (fun (var,ty) -> mk_pvar Ast.Unknown var ty) vars in
      let cases = List.map (compile_rule env) rules in
      let output_type = {t=Ttup(map_filter (function (O,ty) -> Some ty | _ -> None) (List.combine mode ty))} in
      let case = mk_case_exp false Ast.Unknown tuple_of_vars cases output_type in
      let annot = { term = Name.add_lskip n;
                    locn = Ast.Unknown;
                    typ = mty;
                    rest = () } in
      (annot, pats_of_vars, None, None, case)
    ) modes 
  ) prog in
  let defs = sep_no_skips (Nfmap.fold (fun l _ c -> c@l) [] defs) in
  ((Val_def(Rec_def(None,None,None,defs), Types.TNset.empty, []), None), 
   Ast.Unknown)


let ty_from_mode ty mode = 
  let open Types in
  let inputs = map_filter id (
    List.map2 (fun ty mode -> if mode = I then Some(ty) else None) ty mode) in
  let outputs = map_filter id (
    List.map2 (fun ty mode -> if mode = O then Some(ty) else None) ty mode) in
  let ret = {t=Ttup(outputs)} in
  List.fold_left (fun ret arg -> {t=Tfn(arg,ret)}) (ret) 
    (List.rev inputs)


end

module Compile_option_code = struct

  open LemOptionMonad

(* TODO : not correct (must check excluded & renames) *)
(* TODO : parametrize w/ a monad or something *)
let rec compile_code env excluded renames = function
  | RETURN(exps) -> mk_some env (mk_tup Ast.Unknown None (sep_no_skips exps) None None)
  | IF(cond, code) -> 
    let subexp = compile_code env excluded renames code in 
    mk_cond env cond subexp
  | IFEQ(e1,e2,code) ->
    let subexp = compile_code env excluded renames code in
    let cond = mk_eq_exp env e1 e2 in
    mk_cond env cond subexp
  | CALL(n, ty, inp, outp, code) ->
    let subexp = compile_code env excluded renames code in
    let call = List.fold_left (fun func arg -> mk_app Ast.Unknown func arg None) 
      (mk_var Ast.Unknown (Name.add_lskip n) ty) inp in
    let pat = mk_ptup Ast.Unknown None (sep_no_skips outp) None None in
    mk_bind env call pat subexp

let compile_rule env (patterns, code) = 
  let pattern = mk_ptup Ast.Unknown None (sep_no_skips patterns) None None in
  let lemcode = compile_code env Nset.empty Nfmap.empty code in
  (pattern, lemcode) 



(* TODO : check overlap *)
let compile_to_typed_ast env prog =
  let funcs = Nfmap.fold (fun l _ (_ty,funcs) -> 
    (List.map (fun (name, _, _, _) -> name) funcs)@l) [] prog in
  let fun_names = List.fold_right Nset.add funcs Nset.empty in
  let defs = Nfmap.map (fun _rel (ty,modes) ->
    List.map (fun (n, mode, mty, rules) ->
      let gen_name = make_namegen fun_names in
      let vars = map_filter (function 
        | (I, ty) -> Some(Name.add_lskip (gen_name (Ulib.Text.of_latin1 "input")),
                          ty)
        | (O, _) -> None
      ) (List.combine mode ty) in
      let tuple_of_vars = mk_tup Ast.Unknown None (sep_no_skips (List.map (fun (var,ty) -> mk_var Ast.Unknown var ty) vars)) None None in
      let pats_of_vars = List.map (fun (var,ty) -> mk_pvar Ast.Unknown var ty) vars in
      let cases = List.map (compile_rule env) rules in
      let output_type = {t=Ttup(map_filter (function (O,ty) -> Some ty | _ -> None) (List.combine mode ty))} in
      let lastcase = (mk_pwild Ast.Unknown None (exp_to_typ tuple_of_vars), 
                      mk_none env output_type) in
      let case = mk_case_exp false Ast.Unknown tuple_of_vars 
        (cases @ [lastcase])  (mk_option output_type) in
      let annot = { term = Name.add_lskip n;
                    locn = Ast.Unknown;
                    typ = mty;
                    rest = () } in
      (annot, pats_of_vars, None, None, case)
    ) modes 
  ) prog in
  let defs = sep_no_skips (Nfmap.fold (fun l _ c -> c@l) [] defs) in
  ((Val_def(Rec_def(None,None,None,defs), Types.TNset.empty, []), None), 
   Ast.Unknown)


let ty_from_mode ty mode = 
  let open Types in
  let inputs = map_filter id (
    List.map2 (fun ty mode -> if mode = I then Some(ty) else None) ty mode) in
  let outputs = map_filter id (
    List.map2 (fun ty mode -> if mode = O then Some(ty) else None) ty mode) in
  let ret = {t=Ttup(outputs)} in
  List.fold_left (fun ret arg -> {t=Tfn(arg,ret)}) (mk_option ret) 
    (List.rev inputs)

end

module Compile_list_code = struct

(* XXX *)
let remove_list ty = 
  match ty.t with
    | Types.Tapp([ty], _) -> ty
    | _ -> failwith "???"

let mk_list_type ty = 
  { Types.t = Types.Tapp([ty], Path.listpath) }

let mk_list_map env fn lst = 
  let l = Ast.Trans ("mk_list_map", None) in
  match (exp_to_typ fn).t with
    | Types.Tfn(a,b) ->
      mk_app l (mk_app l (mk_const_exp env l ["List"] "map" [a;b]) fn None) lst None
    | _ -> failwith "???"

let mk_list_concat env lst = 
  let t = remove_list (remove_list (exp_to_typ lst)) in
  let l = Ast.Trans ("mk_list_concat", None) in
  mk_app l (mk_const_exp env l ["List"] "concat" [t]) lst None

let mk_bind env call pat code = 
  let l = Ast.Trans ("mk_bind", None) in
  let namegen = make_namegen (Nfmap.domain (exp_to_free code)) in
  let var = Name.add_lskip (namegen (Ulib.Text.of_latin1 "x")) in
  let inty = pat.typ in 
  let fn = mk_fun l None [mk_pvar l var inty] None 
    (mk_case_exp false l (mk_var l var inty) 
    [(pat, code);
     (mk_pwild l None inty, mk_list l None (sep_no_skips []) None (exp_to_typ code))
    ] (exp_to_typ code)) None in
  mk_list_concat env (mk_list_map env fn call)

let mk_cond env cond code = 
  let l = Ast.Trans ("mk_cond", None) in
  mk_if_exp l cond code (mk_list l None (sep_no_skips []) None (exp_to_typ code))


let rec compile_code env excluded renames code = 
  let l = Ast.Trans ("compile_code", None) in
  match code with
  | RETURN(exps) -> 
    let ret = mk_tup l None (sep_no_skips exps) None None in
    mk_list l None (sep_no_skips [ret]) None (mk_list_type (exp_to_typ ret))
  | IF(cond, code) -> 
    let subexp = compile_code env excluded renames code in 
    mk_cond env cond subexp
  | IFEQ(e1,e2,code) ->
    let subexp = compile_code env excluded renames code in
    let cond = mk_eq_exp env e1 e2 in
    mk_cond env cond subexp
  | CALL(n, ty, inp, outp, code) ->
    let subexp = compile_code env excluded renames code in
    let call = List.fold_left (fun func arg -> mk_app l func arg None) 
      (mk_var l (Name.add_lskip n) ty) inp in
    let pat = mk_ptup l None (sep_no_skips outp) None None in
    mk_bind env call pat subexp

let compile_rule env (patterns, code) = 
  let pattern = mk_ptup (Ast.Trans("compile_rule", None)) None (sep_no_skips patterns) None None in
  let lemcode = compile_code env Nset.empty Nfmap.empty code in
  (pattern, lemcode) 



(* TODO : check overlap *)
let compile_to_typed_ast env prog =
  let l = Ast.Trans ("compile_to_typed_ast", None) in
  let funcs = Nfmap.fold (fun l _ (_ty,funcs) -> 
    (List.map (fun (name, _, _, _) -> name) funcs)@l) [] prog in
  let fun_names = List.fold_right Nset.add funcs Nset.empty in
  let defs = Nfmap.map (fun _rel (ty,modes) ->
    List.map (fun (n, mode, mty, rules) ->
      let gen_name = make_namegen fun_names in
      let vars = map_filter (function 
        | (I, ty) -> Some(Name.add_lskip (gen_name (Ulib.Text.of_latin1 "input")),
                          ty)
        | (O, _) -> None
      ) (List.combine mode ty) in
      let tuple_of_vars = mk_tup l None (sep_no_skips (List.map (fun (var,ty) -> mk_var Ast.Unknown var ty) vars)) None None in
      let pats_of_vars = List.map (fun (var,ty) -> mk_pvar l var ty) vars in
      let cases = List.map (compile_rule env) rules in
      let output_type = {t=Ttup(map_filter (function (O,ty) -> Some ty | _ -> None) (List.combine mode ty))} in
      (* Generate a list of binds and concat them ! *)
      let bcases = List.map 
        (fun (pat,code) -> 
          mk_bind env 
            (mk_list l None (sep_no_skips [tuple_of_vars]) None (mk_list_type (exp_to_typ tuple_of_vars))) 
            pat code)
        cases in
      let body = mk_list_concat env (mk_list l None (sep_no_skips bcases)
                                       None (mk_list_type (mk_list_type output_type))) in
      let annot = { term = Name.add_lskip n;
                    locn = l;
                    typ = mty;
                    rest = () } in
      (annot, pats_of_vars, None, None, body)
    ) modes 
  ) prog in
  let defs = sep_no_skips (Nfmap.fold (fun l _ c -> c@l) [] defs) in
  ((Val_def(Rec_def(None,None,None,defs), Types.TNset.empty, []), None), l)


let ty_from_mode ty mode = 
  let open Types in
  let inputs = map_filter id (
    List.map2 (fun ty mode -> if mode = I then Some(ty) else None) ty mode) in
  let outputs = map_filter id (
    List.map2 (fun ty mode -> if mode = O then Some(ty) else None) ty mode) in
  let ret = {t=Ttup(outputs)} in
  List.fold_left (fun ret arg -> {t=Tfn(arg,ret)}) (mk_list_type ret) 
    (List.rev inputs)


end

open Compile_list_code




let type_rules rels = 
  Nfmap.map (fun _ -> function
    | (_, _, _, args)::_ -> List.map exp_to_typ args
    | [] -> failwith "Impossible") rels
  
let transform_rels env rules def = 
(*  try *)
    let rels = get_rels rules in
    (** During typechecking **)
    let types = type_rules rels in
    (*let mymodes = [ (* ("reduce", [("redtest",[I;I]);("red",[I;O])]);
                    *)   ("GtT", [("typecheck",[I;I;I])]) ] in *)
    let mymodes = [("xinG", [("xinG_fun", [I;I])]);
(*                   ("XinG", [("XinG_fun", [I;I])]);
                   ("tin",  [("tin_fun", [I;I;I]);
                             ("tin_get", [I;O;I])]);
                   ("Gok",  [("Gok_fun", [I])]);
                   ("GT",   [("GT_fun", [I;I])]);
                   ("Ty",   [("Ty_fun", [I;I;I]);
                             ("Ty_get", [I;I;O])]);*)
                  ] in
    let modess = Nfmap.from_list 
      (List.map (fun (rel, modes) -> 
        (Name.from_rope (Ulib.Text.of_latin1 rel),
         List.map (fun (n,m) -> (Name.from_rope (Ulib.Text.of_latin1 n), m)) modes))
         mymodes) in
    match (try 
  let typed_modes = Nfmap.map (fun rel modes ->
    let ty = match Nfmap.apply types rel with Some(ty) -> ty | None -> failwith ("Bad mode for " ^ (Ulib.Text.to_string (Name.to_rope rel))) in
    (ty, List.map (fun (n,mode) -> (n,mode,ty_from_mode ty mode)) modes)
  ) modess in
  Some(typed_modes)
      with _ -> None) with
      | None -> []
      | Some(typed_modes) -> 
  (** After typechecking **)
  let compiled = Nfmap.map (fun rel (ty,modes) ->
    let rules = match Nfmap.apply rels rel with Some(rs) -> rs | None -> failwith "Bad mode" in
    (ty, List.map (fun (n,mode,mty) ->
      (n, mode, mty, List.map (fun rule -> transform_rule typed_modes ty mode rule) rules)
    ) modes)
  ) typed_modes in
  debug_print_transformed compiled;
  let code = compile_to_typed_ast env compiled in
  Reporting.print_debug_def "Generated code" [code];
  [code]
  (* How do I print code ? *)
(*  with _ -> Reporting.print_debug_def "Relation ignored" [def] *)

(* instances ? *)
let rec scan_defs env l = List.concat (List.map (scan_def env) l)
and scan_def env (((d,aa),bb) as def) = match d with
  | Indreln(_,_,_,rules) as r -> def::transform_rels env rules def
  | Module(a,b,c,d,defs,e) -> [((Module(a,b,c,d,scan_defs env defs,e),aa),bb)]
  | u -> [def]

open Typecheck_ctxt

(* Temporary *)
let gen_typename_from_rel relname = Name.from_string (Name.to_string relname ^ "_witness")

(* May not be temporary *)
let gen_consname rulename = gen_typename_from_rel rulename

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
  Type_def(None, sep_no_skips (List.map make_def tds))

let register_types ctxt mod_path tds = 
  Nfmap.fold (fun ctxt relname (tname, tconses) ->
    (* Register a type constructor *)
    let type_path = Path.mk_path mod_path tname in
    let l = Ast.Unknown in
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
    let cdescrs = Nfmap.from_list 
      (List.map (fun (crule, cname, cargs) -> (cname, mk_descr cname cargs)) tconses) in
    let rule_to_constr = Nfmap.from_list 
      (List.map (fun (crule, cname, cargs) -> (crule, mk_descr cname cargs)) tconses) in
    let ctxt = ctxt_add (fun x -> x.r_env) (fun x y -> { x with r_env = y })
      ctxt (relname, { rel_witness = Some(type_path, rule_to_constr); rel_check = None }) in
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
let gen_witness_type_aux env get_typepath_from_rel rules = 
  let rels = get_rels rules in
  let reltypes = Nfmap.map 
    (fun relname rules -> get_typepath_from_rel relname) rels in
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
            | Some { rel_witness = None } ->
              raise_error Ast.Unknown "no witness for relation"
                Path.pp c.descr.const_binding 
            | Some { rel_witness = Some(tn,_) } -> 
              let t = {t=Tapp([],tn)} in
              Some(t, t_to_src_t t) 
          end
        | None -> failwith "Impossible"
      end
    | _ -> None
  in
  let tds = Nfmap.map (fun relname rules ->
    let typename = gen_typename_from_rel relname in
    let constructors = List.map (fun (rulename,vars,conds,_args)  ->
      let consname = gen_consname rulename in
      let vars_ty = List.map (fun x -> (snd x,t_to_src_t (snd x))) vars in
      let conds_ty = map_filter 
        (fun cond -> is_relation (fst (split_app cond))) conds in
      let argstypes = vars_ty @ conds_ty in
      (rulename, consname, argstypes)
    ) rules in
    (typename, constructors)
  ) rels in
  tds

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
  (t, mk_tapp loc pid [] (Some t) (* t_to_src_t t *))

let gen_witness_type_info mod_path ctxt rules = 
  let tds = gen_witness_type_aux ctxt.cur_env 
    (fun relname -> 
      let tn = gen_typename_from_rel relname in
      let p = Path.mk_path mod_path tn in
      clean_src_app p
    ) 
    rules in
  let newctxt = register_types ctxt mod_path tds in
  let defs = newctxt.new_defs.v_env in
  newctxt

let gen_witness_type_def mn env rules =
  let Some(locenv) = Nfmap.apply env.m_env mn in 
  let tds = gen_witness_type_aux env 
    (fun relname -> 
      match Nfmap.apply locenv.mod_env.r_env relname with
      | Some({rel_witness = Some(tn,_)}) -> 
        clean_src_app tn
      | None -> failwith "No witness type ?"
    )
    rules in
  (make_typedef tds, None),  Ast.Unknown

let gen_check_name relname = 
  Name.from_string (Name.to_string relname ^ "_check")

let ctxt_mod update ctxt = 
  { ctxt with
    cur_env = update ctxt.cur_env;
    new_defs = update ctxt.new_defs
  }

let gen_witness_check_info mod_path ctxt rules =
  let rels = get_rels rules in
  let defs = Nfmap.map (fun relname rules ->
    let (_,_,_,args) = List.hd rules in
    let ret = List.map exp_to_typ args in
    let check_name = gen_check_name relname in
    let check_path = Path.mk_path mod_path check_name in
    let witness_type = 
      match Nfmap.apply ctxt.cur_env.r_env relname with
      | Some({rel_witness = Some(witness_type,_)}) -> 
        {t = Tapp([],witness_type)}
      | None -> raise_error Ast.Unknown 
        "no witness for relation while generating witness-checking function"
        Path.pp check_path
    in
    (* TODO : generate option type *)
    let check_type = {t=Tfn(witness_type, mk_option {t=Ttup(List.map exp_to_typ args)})} in
    (check_name, check_path, check_type)
  ) rels in
  (* Register the functions *)
  Nfmap.fold (fun ctxt relname (cname,cpath,ctype) ->
    let const_descr = {
      const_binding = cpath;
      const_tparams = [];
      const_class = [];
      const_ranges = [];
      const_type = ctype;
      env_tag = K_let;
      spec_l = Ast.Unknown;
      substitutions = Targetmap.empty
    } in
    let ctxt = ctxt_add (fun x -> x.v_env) (fun x y -> {x with v_env = y})
      ctxt (cname, Val(const_descr)) in
    ctxt_mod (fun x -> {x with r_env = let Some r_info = Nfmap.apply x.r_env relname in Nfmap.insert x.r_env (relname, {r_info with rel_check = Some cpath})}) ctxt
  ) ctxt defs

let nset_of_list l = List.fold_left (fun set x -> Nset.add x set) Nset.empty l

(* Variable management : 
 - abstract
 - unabstract
*)

type ('a,'b) choice = Left of 'a | Right of 'b

let map_partition f l = 
  List.fold_right (fun x (ls,rs) ->
    match f x with
      | Left l -> (l::ls,rs)
      | Right r -> (ls,r::rs)
  ) l ([],[])

open LemOptionMonad

let path_to_string_list p = 
  let (mp,n) = Path.to_name_list p in
  let (n::mp) = List.map Name.to_string (n::mp) in
  (mp, n)

let mk_const_from_path env l path inst = 
  let (mp,n) = path_to_string_list path in
  mk_const_exp env l mp n inst

let gen_witness_check_def mn env rules = 
  let rels = get_rels rules in
  let Some(localenv) = Nfmap.apply env.m_env mn in
  let localenv = localenv.mod_env in
  let localdefs = Nfmap.map (fun relname rules ->
    match Nfmap.apply localenv.r_env relname with
      | Some({rel_witness = Some(witness_info); rel_check = Some(check_path)}) ->
        let (_,def_name) = Path.to_name_list check_path in
        (def_name, witness_info,check_path, rules)
      | None -> failwith "Need map_filter here"
  ) rels in
  let defs = Nfmap.map (fun relname (def_name, (witness_path, witness_constrs), check_path, rules) ->
    let witness_ty = {t=Tapp([],witness_path)} in
    let pats = List.map (fun (rulename, vars, conds, args) ->
      (* Bad indices from get_witness_type_info, sorry *)
      let Some(constr) = Nfmap.apply witness_constrs rulename in
      (* THIS IS WRONG *)
     (* (* If a var and a localdef share a name, we need to rename the var *)
      let defvars = nset_of_list (Nfmap.fold (fun acc _ (v,_,_) -> v::acc) [] localdefs) in
      let (vars,conds,args) = do_what_i_mean in
      let excludevars = List.map snd vars @
        Nfmap.fold (fun acc _ (v,_,_) -> v::acc) [] localdefs in
      let excludevars = List.fold_right Nset.add excludevars Nset.empty in *)
      let gen_name = make_namegen Nset.empty in
      (* Travailler sur les conds *)
      let is_rel_or_aux e = 
        let (head, args) = split_app e in
        (* COMPLETELY WRONG : references to things defined in THIS binding
           should be VARIABLES, not CONSTANTS *)
        match exp_to_term head with
          | Var v ->
            (* TODO : factorisation *)
            let n = Name.strip_lskip v in
            begin match Nfmap.apply localenv.r_env n with
              | None -> Right e
              (* TODO : adjust ids for local things *)
              | Some {rel_check = Some(check_path);
                      rel_witness = Some(witness_path, witness_constrs)} ->
                let check_exp = match Nfmap.apply localdefs n with
                  | Some(def_name,_,_,_) -> 
                    let witness_ty = {t=Tapp([],witness_path)} in
                    let out_ty = mk_option {t=Ttup(List.map exp_to_typ args)} in
                    mk_var Ast.Unknown (Name.add_lskip def_name) {t=Tfn(witness_ty, out_ty)}
                  | None -> mk_const_from_path env Ast.Unknown check_path []
                in
                Left(args, witness_path, check_exp)
              | Some _ ->
                raise_error Ast.Unknown "no witness checking function for relation"
                  Path.pp check_path
            end
          | Constant c ->
            let (mpath, n) = Path.to_name_list c.descr.const_binding in
            begin match path_lookup env mpath with
              | Some(env) ->
                begin match Nfmap.apply env.r_env n with
                  | None -> Right e
                  | Some { rel_witness = Some(witness_path, _);
                           rel_check = Some(check_path) } ->
                    let check_exp = mk_const_from_path env Ast.Unknown check_path [] in
                    Left (args, witness_path, check_exp)
                  | Some _ ->
                    raise_error Ast.Unknown "no witness checking function for relation"
                      Path.pp check_path
                end
              | None -> failwith "Impossible"
            end
          | _ -> Right e
      in    
      let (relconds,auxconds) = map_partition is_rel_or_aux conds in
      let relconds = List.map (fun (args,witness_path,check_exp) ->
        let witness_ty = {t=Tapp([],witness_path)} in
        let witness_name = gen_name (Ulib.Text.of_latin1 "witness") in
        (args, witness_ty, check_exp, witness_name)
      ) relconds in
      let pvars = List.map 
        (fun (var,typ) -> mk_pvar Ast.Unknown (Name.add_lskip var) typ) vars in
      let pconds = List.map
        (fun (_,witness_ty,_,var) -> 
          mk_pvar Ast.Unknown (Name.add_lskip var) witness_ty
        ) relconds in
      let constr_id = { id_path = Id_none None;
                        id_locn = Ast.Unknown;
                        descr = constr;
                        instantiation = [] } in
      let pattern = mk_pconstr Ast.Unknown constr_id (pvars @ pconds) None in
      let ret = mk_some env 
        (mk_tup Ast.Unknown None (sep_no_skips args) None None) in
      let genconds_exps = List.map (fun (args,witness_ty,check_fun,witness) ->
        let witness_var = mk_var Ast.Unknown (Name.add_lskip witness) witness_ty in
        let rhs = mk_some env (mk_tup Ast.Unknown None (sep_no_skips args) None None) in
        let lhs = mk_app Ast.Unknown check_fun witness_var None in
        mk_eq_exp env rhs lhs
      ) relconds in
      let ifconds = auxconds @ genconds_exps in
      let lit_true = mk_lit Ast.Unknown ({term=L_true(None); locn = Ast.Unknown;
                                          typ={t=Tapp([],Path.boolpath)};
                                          rest=()}) None in
      let cond = List.fold_left (mk_and_exp env) lit_true ifconds in
      let code = mk_if_exp Ast.Unknown cond ret (mk_none env (remove_option (exp_to_typ ret))) in
      (pattern, code)
    ) rules in
    let x = Name.add_lskip (make_namegen Nset.empty (Ulib.Text.of_latin1 "x")) in
    let xpat = mk_pvar Ast.Unknown x witness_ty in
    let xvar = mk_var Ast.Unknown x witness_ty in
    let return_ty = exp_to_typ (snd (List.hd pats))  in
    let body = mk_case_exp false Ast.Unknown xvar pats return_ty in
    let annot = { term = Name.add_lskip def_name;
                  locn = Ast.Unknown;
                  typ = {t=Tfn(witness_ty,return_ty)};
                  rest = () } in
    (annot, [xpat], None, None, body)
  ) localdefs in
  let defs = Nfmap.fold (fun l _ v -> v::l) [] defs in
  let def = Rec_def(None,None,None,sep_no_skips defs) in
  ((Val_def(def, Types.TNset.empty, []), None), Ast.Unknown)

(* Rec_def of lskips * sips * targtets_opt * funcl_aux lskips_seplist 
and funcl_aux = name_lskips_annot * pat list * (lskips * src_t) option * lskips * exp
*)

let rec gen_type_scan_defs mn env l = List.concat (List.map (gen_type_scan_def mn env) l)
and gen_type_scan_def mn env (((d,aa), bb) as def) = match d with
  | Indreln(_,_,_,rules) -> [def;gen_witness_type_def mn env rules;
                           gen_witness_check_def mn env rules]
  | Module(a,b,c,d,defs,e) -> failwith "Modules not supported"
  | _ -> [def]

end











