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

module Nmap = Typed_ast.Nfmap
module Nset = Nmap.S

(* Split on infix (&&) : ((a && b) && (c && d)) && true -> [a;b;c;d] *)

let is_true l = match l.term with
  | L_true _ -> true
  | _ -> false

let r = Ulib.Text.of_latin1
let mk_string_path ns n = Path.mk_path (List.map (fun s -> Name.from_rope (r s)) ns) (Name.from_rope (r n))
let and_path = mk_string_path ["Pervasives"] "&&"

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

let get_rels (l : (Name.lskips_t option * lskips * name_lskips_annot list * lskips * exp option * lskips * name_lskips_annot * exp list) lskips_seplist ) = 
  List.fold_left (fun s (rulename,_,vars,_,cond,_,rel,args) ->
    let relname = Name.strip_lskip rel.term in
    let rulecond = match cond with
      | Some x -> x
      | None -> C.mk_lit Ast.Unknown ({term = L_true None; locn = Ast.Unknown; typ =  {t = Tapp([], Path.boolpath)}; rest = ()}) None in
    let ruledescr = (rulename, Nmap.domain (Nmap.from_list (List.map (fun v -> (Name.strip_lskip v.term, ()) ) vars)), split_and rulecond, args) in
    match Nmap.apply s relname with
      | None -> Nmap.insert s (relname, [ruledescr])
      | Some rules -> Nmap.insert s (relname, ruledescr::rules)
  ) Nmap.empty (Seplist.to_list l)

type io = I | O
type ep = IExp of exp | OPat of pat
type mode = io list

(* Just a small model of the code we will generate later
   We will need a partial "exp to pattern" function somewhere *)
type code = 
  | IF of exp * code 
  | CALL of Name.t * Types.t * exp list * pat list * code
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
  let open C in
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

let transform_rule mode_env _ty mode rule = 
  let (rulename, vars, conds, args) = rule in
  let gen_rn = make_renamer vars (Nmap.domain mode_env) in
  let (patterns, initknown, initeqs) = 
    convert_output gen_rn args (List.map (fun x -> x = O) mode) in
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
          | [], [] -> RETURN returns
          | _ -> no_translation None
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
        Format.eprintf "CALL %s : %s" (Name.to_rope % n) (B.ident_typ % ty);
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

open C

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


let type_rules rels = 
  Nfmap.map (fun _ -> function
    | (_, _, _, args)::_ -> List.map exp_to_typ args
    | [] -> failwith "Impossible") rels

let ty_from_mode ty mode = 
  let open Types in
  let inputs = map_filter id (
    List.map2 (fun ty mode -> if mode = I then Some(ty) else None) ty mode) in
  let outputs = map_filter id (
    List.map2 (fun ty mode -> if mode = O then Some(ty) else None) ty mode) in
  let ret = {t=Ttup(outputs)} in
  List.fold_left (fun ret arg -> {t=Tfn(arg,ret)}) ret inputs
  
let transform_rels env rules = 
  let rels = get_rels rules in
  (** During typechecking **)
  let types = type_rules rels in
  let modess = Nfmap.from_list 
    [(Name.from_rope (Ulib.Text.of_latin1 "add"), 
      List.map (fun (n, m) -> (Name.from_rope (Ulib.Text.of_latin1 n),m)) 
        [("addIIO",[I;I;O]);("addIII",[I;I;I]);("addOII",[O;I;I])]
    )] in
  let typed_modes = Nfmap.map (fun rel modes ->
    let ty = match Nfmap.apply types rel with Some(ty) -> ty | None -> failwith "Bas mode" in
    (ty, List.map (fun (n,mode) -> (n,mode,ty_from_mode ty mode)) modes)
  ) modess in
  (** After typechecking **)
  let compiled = Nfmap.map (fun rel (ty,modes) ->
    let rules = match Nfmap.apply rels rel with Some(rs) -> rs | None -> failwith "Bad mode" in
    (ty, List.map (fun (n,mode,mty) ->
      (n, mode, mty, List.map (fun rule -> transform_rule typed_modes ty mode rule) rules)
    ) modes)
  ) typed_modes in
  debug_print_transformed compiled;
  let code = compile_to_typed_ast env compiled in
  Reporting.print_debug_def "Generated code" [code]
  (* How do I print code ? *)

(* instances ? *)
let rec scan_defs env l = List.iter (scan_def env) l
and scan_def env ((d,_),_) = match d with
  | Indreln(_,_,rules) -> ignore (transform_rels env rules); ()
  | Module(_,_,_,_,defs,_) -> scan_defs env defs
  | _ -> ()

end











