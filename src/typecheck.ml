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

open Format
open Types
open Typed_ast

let raise_error = Ident.raise_error

let r = Ulib.Text.of_latin1

module Namel = struct
  type t = Name.t * Ast.l
  let compare (n1,_) (n2,_) =
    Name.compare n1 n2
end

module NamelSet = Set.Make(Namel)

module DupNames = Util.Duplicate(NamelSet)
module DupTvs = Util.Duplicate(TNset)

type pat_env = (t * Ast.l) Nfmap.t
let empty_pat_env = Nfmap.empty

(* Non-top level binders map to a type, not a type scheme, method or constructor
 * *) 
type lex_env = (t * Ast.l) Nfmap.t
let empty_lex_env = Nfmap.empty

let annot_name n l env = 
  { term = n;
    locn = l;
    typ = 
      begin
        match Nfmap.apply env (Name.strip_lskip n) with
          | Some((x,l)) -> x 
          | None -> assert false
      end;
    rest = (); }

let xl_to_nl xl = (Name.from_x xl, Ast.xl_to_l xl)

let id_to_identl id =
  (Ident.from_id id, match id with | Ast.Id(mp,xl,l) -> l)

(* Assume that the names in mp must refer to modules.  Corresponds to judgment
 * look_m 'E1(x1..xn) gives E2' *)
let rec path_lookup (e : env) (mp : (Name.lskips_t * Ast.l) list) : env = 
  match mp with
    | [] -> e
    | (n,l)::nls ->
        match Nfmap.apply e.m_env (Name.strip_lskip n) with
          | None -> 
              raise_error l "unknown module"
                Name.pp (Name.strip_lskip n)
          | Some(e) -> path_lookup e.mod_env nls

(* Assume that the names in mp must refer to modules. Corresponds to judgment
 * look_m_id 'E1(id) gives E2' *)
let lookup_mod (e : env) (Ast.Id(mp,xl,l'')) : mod_descr = 
  let e = path_lookup e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
    match Nfmap.apply e.m_env (Name.strip_lskip (Name.from_x xl)) with
      | None -> 
          raise_error (Ast.xl_to_l xl) "unknown module"
            Name.pp (Name.strip_lskip (Name.from_x xl))
      | Some(e) -> e

(* Assume that the names in mp must refer to modules. Corresponds to judgment
 * look_tc 'E(id) gives p' *)
let lookup_p msg (e : env) (Ast.Id(mp,xl,l) as i) : Path.t =
  let e = path_lookup e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
    match Nfmap.apply e.p_env (Name.strip_lskip (Name.from_x xl)) with
      | None ->
          raise_error l (Printf.sprintf "unbound type %s" msg)
            Ident.pp (Ident.from_id i)
      | Some(p, _) -> p

(* Assume that the names in mp must refer to modules. Looksup a name, not
   knowing what this name refers to. *)
let lookup_name (e : env) (Ast.Id(mp,xl,l) as i) : Path.t =
  let e = path_lookup e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
    match env_apply e (Name.strip_lskip (Name.from_x xl)) with
      | None ->
          raise_error l (Printf.sprintf "unbound name")
            Ident.pp (Ident.from_id i)
      | Some(_, p, _) -> p


(* Lookup in the lex env.  A formula in the formal type system *)
let lookup_l (l_e : lex_env) mp n : (t * Ast.l * Name.lskips_t) option =
  match mp with
    | [] -> 
        begin
          match Nfmap.apply l_e (Name.strip_lskip n) with
            | None -> None
            | Some((t,l)) -> Some((t,l,n))
        end
    | _ -> None

(* Checks the well-formedness of a type that appears in the source.  Corresponds
 * to judgment convert_typ 'Delta, E |- typ ~> t'.  The wild_f function is used
 * for an underscore/wildcard type (which should be allowed in type annotations,
 * but not in type definitions).  The do_tvar function is called on each type
 * variable in the type, for its side effect (e.g., to record the tvars that
 * occur in the type. *)

let rec nexp_to_src_nexp (do_nvar : Nvar.t -> unit) (Ast.Length_l(nexp,l)) : src_nexp =
  match nexp with
   | Ast.Nexp_var((sk,nv)) ->
     do_nvar(Nvar.from_rope nv);
     { nterm = Nexp_var(sk,Nvar.from_rope(nv)); 
       nloc =l; 
       nt = {nexp=Nvar(Nvar.from_rope(nv)); };}
   | Ast.Nexp_constant(sk,i) ->
     { nterm = Nexp_const(sk,i); 
       nloc=l; 
       nt = {nexp=Nconst(i);};}
   | Ast.Nexp_times(n1,sk,n2) ->
     let n1' = nexp_to_src_nexp do_nvar n1 in
     let n2' = nexp_to_src_nexp do_nvar n2 in
     { nterm = Nexp_mult(n1',sk,n2'); 
       nloc =l; 
       nt = {nexp=Nmult(n1'.nt,n2'.nt);};}
   | Ast.Nexp_sum(n1,sk,n2) ->
     let n1' = nexp_to_src_nexp do_nvar n1 in
     let n2' = nexp_to_src_nexp do_nvar n2 in
     { nterm = Nexp_add(n1',sk,n2');
       nloc =l;
       nt = {nexp=Nadd(n1'.nt,n2'.nt);}; }
   | Ast.Nexp_paren(sk1,n,sk2) ->
     let n' = nexp_to_src_nexp do_nvar n in
     { nterm = Nexp_paren(sk1,n',sk2);
       nloc = l;
       nt = n'.nt }

let tnvar_app_check l i tnv (t: src_t) : unit =
  match tnv, t.typ with
   | Nv _ , {t = Tne _} -> ()
   | Ty _ , {t = Tne _} -> 
     raise_error l (Printf.sprintf "type constructor expected type argument, given a length")
         Ident.pp (Ident.from_id i)
     (* TODO KG: Improve this type error location and add variable name *)
   | Nv _ , _ -> 
     raise_error l (Printf.sprintf "type constructor expected length argument, given a type")
         Ident.pp (Ident.from_id i)
   | Ty _ , _ -> ()

let rec typ_to_src_t (wild_f : Ast.l -> lskips -> src_t) 
      (do_tvar : Tyvar.t -> unit) (do_nvar : Nvar.t -> unit) (d : type_defs) (e : env) (Ast.Typ_l(typ,l)) 
      : src_t = 
  match typ with
    | Ast.Typ_wild(sk) -> 
        wild_f l sk
    | Ast.Typ_var(Ast.A_l((sk,tv),l')) -> 
        do_tvar (Tyvar.from_rope tv);
        { term = Typ_var(sk,Tyvar.from_rope tv); 
          locn = l'; 
          typ = { t = Tvar(Tyvar.from_rope tv); }; 
          rest = (); }
    | Ast.Typ_fn(typ1, sk, typ2) ->
        let st1 = typ_to_src_t wild_f do_tvar do_nvar d e typ1 in
        let st2 = typ_to_src_t wild_f do_tvar do_nvar d e typ2 in
          { term = Typ_fn(st1, sk, st2);
            locn = l; 
            typ = { t = Tfn(st1.typ,st2.typ) };
            rest = (); }
    | Ast.Typ_tup(typs) ->
        let typs = Seplist.from_list typs in
        let sts = Seplist.map (typ_to_src_t wild_f do_tvar do_nvar d e) typs in
          { term = Typ_tup(sts); 
            locn = l; 
            typ = { t = Ttup(Seplist.to_list_map annot_to_typ sts) };
            rest = (); }
    | Ast.Typ_app(i,typs) ->
        let p = lookup_p "constructor" e i in
          begin
            match Pfmap.apply d p with
              | None -> assert false
              | Some(Tc_type(tvs,_,_)) ->
                  if List.length tvs = List.length typs then
                    let sts = 
                      List.map (typ_to_src_t wild_f do_tvar do_nvar d e) typs 
                    in
                    let id = {id_path = Id_some (Ident.from_id i); 
                              id_locn = (match i with Ast.Id(_,_,l) -> l);
                              descr = p;
                              instantiation = []; }
                    in
		      (List.iter2 (tnvar_app_check l i) tvs sts);
                      { term = Typ_app(id,sts);
                        locn = l;
                        typ = { t = Tapp(List.map annot_to_typ sts,p) };
                        rest = (); }
                  else
                    raise_error l (Printf.sprintf "type constructor expected %d type arguments, given %d" 
                                   (List.length tvs)
                                   (List.length typs))
                      Ident.pp (Ident.from_id i)
              | Some(Tc_class _) ->
                  raise_error l "type class used as type constructor" 
                    Ident.pp (Ident.from_id i)
          end
    | Ast.Typ_paren(sk1,typ,sk2) ->
        let st = typ_to_src_t wild_f do_tvar do_nvar d e typ in
        { term = Typ_paren(sk1,st,sk2); 
          locn = l; 
          typ = st.typ; 
          rest = (); }
    | Ast.Typ_Nexps(nexp) -> 
        let nexp' = nexp_to_src_nexp do_nvar nexp in
        { term = Typ_len(nexp');
          locn = l;
          typ = {t = Tne(nexp'.nt);};
          rest=(); }

(* Corresponds to judgment check_lit '|- lit : t' *)
let check_lit (Ast.Lit_l(lit,l)) =
  let annot (lit : lit_aux) (t : t) : lit = 
    { term = lit; locn = l; typ = t; rest = (); } 
  in 
  match lit with
    | Ast.L_true(sk) -> annot (L_true(sk)) { t = Tapp([], Path.boolpath) }
    | Ast.L_false(sk) -> annot (L_false(sk)) { t = Tapp([], Path.boolpath) }
    | Ast.L_num(sk,i) -> annot (L_num(sk,i)) { t = Tapp([], Path.numpath) }
    | Ast.L_string(sk,i) ->
        annot (L_string(sk,i)) { t = Tapp([], Path.stringpath) }
    | Ast.L_unit(sk1,sk2) ->
        annot (L_unit(sk1,sk2)) { t = Tapp([], Path.unitpath) }
    | Ast.L_bin(sk,i) ->
        let bit = { t = Tapp([], Path.bitpath) } in
        let len = { t = Tne( { nexp = Nconst(String.length i)} ) } in
        annot (L_vector(sk,"0b",i)) { t = Tapp([bit;len], Path.vectorpath) }
    | Ast.L_hex(sk,i) ->
        let bit = { t = Tapp([], Path.bitpath) } in
        let len = { t = Tne( { nexp = Nconst(String.length i * 4)} ) } in
        annot (L_vector(sk, "0x", i)) { t = Tapp([bit;len], Path.vectorpath) }
    | Ast.L_zero(sk) -> annot (L_zero(sk)) { t = Tapp([], Path.bitpath) }
    | Ast.L_one(sk) -> annot (L_one(sk)) { t = Tapp([], Path.bitpath) }

let check_dup_field_names (fns : (Name.t * Ast.l) list) : unit = 
  match DupNames.duplicates fns with
    | DupNames.Has_dups(fn) ->
        raise_error (snd fn) "duplicate field name" 
          (fun fmt x -> Format.fprintf fmt "%a" Name.pp x)
          (fst fn)
    | _ -> ()

(* We split the environment between top-level and lexically nested binders, and
 * inside of expressions, only the lexical environment can be extended, we
 * parameterize the entire expression-level checking apparatus over the
 * top-level environment.  This contrasts with the formal type system where
 * Delta and E get passed around.  The Make_checker functor also instantiates
 * the state for type inference, so checking of different expressions doesn't
 * interfere with each other.  We also imperatively collect class constraints
 * instead of passing them around as the formal type system does *)

module type Expr_checker = sig
  val check_lem_exp : lex_env -> Ast.l -> Ast.exp -> Types.t -> (exp * typ_constraints)

  val check_letbind : 
    (* Should be None, unless checking a method definition in an instance.  Then
     * it should contain the type that the instance is at.  In this case the
     * returned constraints and type variables must be empty. *)
    t option ->
    (* The set of targets that this definition is for *)
    Targetset.t option ->
    Ast.l ->
    Ast.letbind -> 
    letbind * 
    (* The types of the bindings *)
    pat_env * 
    (* The type variabes, and class constraints on them used in typechecking the
     * let binding.  Must be empty when the optional type argument is Some *)
    typ_constraints

  (* As in the comments on check letbind above *)
  val check_funs : 
    t option ->
    Targetset.t option ->
    Ast.l ->
    Ast.funcl lskips_seplist -> 
    funcl_aux lskips_seplist * 
    pat_env * 
    typ_constraints

  (* As in the comments on check letbind above, but cannot be an instance
   * method definition *)
  val check_indrels : 
    Targetset.t option ->
    Ast.l ->
    (Ast.rule * lskips) list -> 
    (Name.lskips_t option * lskips * name_lskips_annot list * lskips * exp option * lskips * name_lskips_annot * exp list) lskips_seplist * 
    pat_env *
    typ_constraints
end

module Make_checker(T : sig 
                      (* The backend targets that each identifier use must be
                       * defined for *)
                      val targets : Targetset.t
                      (* The current top-level environment *)
                      val e : env 
                      (* The environment so-far of the module we're defining *)
                      val new_module_env : env
                      include Global_defs 
                    end) : Expr_checker = struct

  module C = Constraint(T)
  module A = Exps_in_context(struct let check = None let avoid = None end)
          
  (* An identifier instantiated to fresh type variables *)
  let make_new_id ((id : Ident.t), l) (tvs : Types.tnvar list) (descr : 'a) : 'a id =
    let ts_inst = List.map (fun v -> match v with | Ty _ -> C.new_type () | Nv _ -> {t = Tne(C.new_nexp ())}) tvs in
      { id_path = Id_some id; 
        id_locn = l;
        descr = descr; 
        instantiation = ts_inst; }

  (* Assumes that mp refers to only modules and xl a field name.  Corresponds to
   * judgment inst_field 'Delta,E |- field id : t_args p -> t gives (x of
   * names)'.  Instantiates the field descriptor with fresh type variables, also
   * calculates the type of the field as a function from the record type to the
   * field's type.
   *)
  let check_field (Ast.Id(mp,xl,l) as i) 
        : (field_descr id * t * Name.t * Name.t list) * Ast.l =
    let env = path_lookup T.e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
      match Nfmap.apply env.f_env (Name.strip_lskip (Name.from_x xl)) with
        | None ->
            begin
              match Nfmap.apply env.v_env (Name.strip_lskip (Name.from_x xl)) with
                | None ->
                    raise_error l "unbound field name" 
                      Ident.pp (Ident.from_id i)
                | Some(Constr(c)) ->
                    raise_error l "constructor name used as a field name"
                      Ident.pp (Ident.from_id i)
                | Some(Val(c)) ->
                    if c.env_tag = K_method then
                      raise_error l "method name used as a field name"
                        Ident.pp (Ident.from_id i)
                    else
                      raise_error l "top level variable binding used as a field name"
                        Ident.pp (Ident.from_id i)
            end
        | Some(f) ->
            let id_l = id_to_identl i in
            let new_id = make_new_id id_l f.field_tparams f in
            let trec = { t = Tapp(new_id.instantiation,f.field_tconstr) } in
            let subst = 
              TNfmap.from_list2 f.field_tparams new_id.instantiation 
            in
            let tfield = type_subst subst f.field_arg in
            let t = { t = Tfn(trec,tfield) } in
            let a = C.new_type () in
              C.equate_types new_id.id_locn a t;
              ((new_id, a, Path.get_name f.field_binding, f.field_names), l)

  (* Instantiates a constructor descriptor with fresh type variables, also
   * calculates the type of the constructor as a function.  Corresponds to
   * judgment inst_ctor 'Delta,E |- ctor id : t_multi -> t_args p gives (x of
   * names)', except that that also looks up the descriptor *)
  let inst_constr id_l (c : constr_descr) : constr_descr id * t * int =
    let new_id = make_new_id id_l c.constr_tparams c in
    let subst = TNfmap.from_list2 c.constr_tparams new_id.instantiation in
    let t = multi_fun 
              (List.map (type_subst subst) c.constr_args)
              { t = Tapp(new_id.instantiation,c.constr_tconstr) }
    in
    let a = C.new_type () in
      C.equate_types new_id.id_locn a t;
      (new_id, a, List.length c.constr_args)

  (* Instantiates a top-level constant descriptor with fresh type variables,
   * also calculates its type.  Corresponds to judgment inst_val 'Delta,E |- val
   * id : t gives Sigma', except that that also looks up the descriptor *)
  let inst_const id_l (c : const_descr) : const_descr id * t =
    let new_id = make_new_id id_l c.const_tparams c in
    let subst = TNfmap.from_list2 c.const_tparams new_id.instantiation in
    let t = type_subst subst c.const_type in
    let a = C.new_type () in
      C.equate_types new_id.id_locn a t;
      List.iter 
        (fun (p, tv) -> 
           C.add_constraint p (type_subst subst (tnvar_to_type tv))) 
        c.const_class;
      List.iter
         (fun r -> C.add_length_constraint (range_with r (nexp_subst subst (range_of_n r)))) 
         c.const_ranges; 
      (new_id, a)

  let add_binding (pat_e : pat_env) ((v : Name.lskips_t), (l : Ast.l)) (t : t) 
        : pat_env =
    if Nfmap.in_dom (Name.strip_lskip v) pat_e then
      raise_error l "duplicate binding" Name.pp (Name.strip_lskip v)
    else
      Nfmap.insert pat_e (Name.strip_lskip v,(t,l))

  let build_wild l sk =
    { term = Typ_wild(sk); locn = l; typ = C.new_type (); rest = (); }

  (* Corresponds to judgment check_pat 'Delta,E,E_l1 |- pat : t gives E_l2' *)
  let rec check_pat (l_e : lex_env) (Ast.Pat_l(p,l)) (acc : pat_env) 
        : pat * pat_env = 
    let ret_type = C.new_type () in
    let rt = Some(ret_type) in
      match p with
        | Ast.P_wild(sk) -> 
            let a = C.new_type () in
              C.equate_types l ret_type a;
              (A.mk_pwild l sk ret_type, acc)
        | Ast.P_as(s1,p, s2, xl,s3) -> 
            let nl = xl_to_nl xl in
            let (pat,pat_e) = check_pat l_e p acc in
            let ax = C.new_type () in
              C.equate_types (snd nl) ax pat.typ;
              C.equate_types l pat.typ ret_type;
              (A.mk_pas l s1 pat s2 nl s3 rt, add_binding pat_e nl ax)
        | Ast.P_typ(sk1,p,sk2,typ,sk3) ->
            let (pat,pat_e) = check_pat l_e p acc in
            let src_t = 
              typ_to_src_t build_wild C.add_tyvar C.add_nvar T.d T.e typ
            in
              C.equate_types l src_t.typ pat.typ;
              C.equate_types l src_t.typ ret_type;
              (A.mk_ptyp l sk1 pat sk2 src_t sk3 rt, pat_e)
        | Ast.P_app(Ast.Id(mp,xl,l'') as i, ps) ->
            let l' = Ast.xl_to_l xl in
            let e = path_lookup T.e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
              begin
                match Nfmap.apply e.v_env (Name.strip_lskip (Name.from_x xl)) with
                  | Some(Constr(c)) when (lookup_l l_e mp (Name.from_x xl) = None) ->
                      (* i is bound to a constructor that is not lexically
                       * shadowed, this corresponds to the
                       * check_pat_aux_ident_constr case *)
                      let (id,t,num_args) = inst_constr (id_to_identl i) c in
                      let (pats,pat_e) = check_pats l_e acc ps in
                        if List.length pats <> num_args then
                          raise_error l' 
                            (Printf.sprintf "constructor pattern expected %d arguments, given %d"
                               num_args
                               (List.length pats))
                            Ident.pp (Ident.from_id i); 
                        C.equate_types l'' t 
                          (multi_fun (List.map annot_to_typ pats) ret_type);
                        (A.mk_pconstr l id pats rt, pat_e)
                  | _ ->
                      (* the check_pat_aux_var case *)
                      match mp with
                        | [] ->
                            if ps <> [] then
                              raise_error l' "non-constructor pattern given arguments" 
                                Ident.pp (Ident.from_id i)
                            else
                              let ax = C.new_type () in
                              let n = Name.from_x xl in
                                C.equate_types l'' ret_type ax;
                                (A.mk_pvar l n ret_type, 
                                 add_binding acc (n,l') ax)
                        | _ ->
                            raise_error l' "non-constructor pattern has a module path" 
                              Ident.pp (Ident.from_id i)
              end
        | Ast.P_record(sk1,ips,sk2,term_semi,sk3) ->
            let fpats = Seplist.from_list_suffix ips sk2 term_semi in
            let a = C.new_type () in
            let (checked_pats, pat_e) = 
              Seplist.map_acc_left (check_fpat a l_e) acc fpats 
            in
              check_dup_field_names 
                (Seplist.to_list_map snd checked_pats);
              C.equate_types l a ret_type;
              (A.mk_precord l sk1 (Seplist.map fst checked_pats) sk3 rt,
               pat_e)
        | Ast.P_tup(sk1,ps,sk2) -> 
            let pats = Seplist.from_list ps in
            let (pats,pat_e) = 
              Seplist.map_acc_left (check_pat l_e) acc pats
            in
              C.equate_types l ret_type 
                { t = Ttup(Seplist.to_list_map annot_to_typ pats) };
              (A.mk_ptup l sk1 pats sk2 rt, pat_e)
        | Ast.P_list(sk1,ps,sk2,semi,sk3) -> 
            let pats = Seplist.from_list_suffix ps sk2 semi in
            let (pats,pat_e) = 
              Seplist.map_acc_left (check_pat l_e) acc pats
            in
            let a = C.new_type () in
              Seplist.iter (fun pat -> C.equate_types l a pat.typ) pats;
              C.equate_types l ret_type { t = Tapp([a], Path.listpath) };
              (A.mk_plist l sk1 pats sk3 ret_type, pat_e)
	| Ast.P_vector(sk1,ps,sk2,semi,sk3) -> 
           let pats = Seplist.from_list_suffix ps sk2 semi in
           let (pats,pat_e) = 
             Seplist.map_acc_left (check_pat l_e) acc pats
           in
           let a = C.new_type () in
             Seplist.iter (fun pat -> C.equate_types l a pat.typ) pats;
             let len = { t = Tne({ nexp = Nconst( Seplist.length pats )} ) } in
             C.equate_types l ret_type { t = Tapp([a;len], Path.vectorpath) };
             (A.mk_pvector l sk1 pats sk3 ret_type, pat_e)
        | Ast.P_vectorC(sk1,ps,sk2) -> 
            let (pats,pat_e) = List.fold_left (fun (l,acc) p ->
                                                 let (p,a) = (check_pat l_e) p acc in
                                                 (p::l, a)) ([], acc) ps in
            let pats = List.rev pats in
            let a = C.new_type() in
            let lens =
              List.fold_left (fun lens pat -> 
                                let c = C.new_nexp () in
                                C.equate_types l { t = Tapp([a;{t=Tne(c)}],Path.vectorpath) } pat.typ;
                                c::lens) [] pats in
              let len = { t = Tne( nexp_from_list (List.rev lens) ) } in
              C.equate_types l ret_type { t = Tapp([a;len],Path.vectorpath) };
              (A.mk_pvectorc l sk1 pats sk2 ret_type, pat_e)
        | Ast.P_paren(sk1,p,sk2) -> 
            let (pat,pat_e) = check_pat l_e p acc in
              C.equate_types l ret_type pat.typ;
              (A.mk_pparen l sk1 pat sk2 rt, pat_e)
        | Ast.P_cons(p1,sk,p2) ->
            let (pat1,pat_e) = check_pat l_e p1 acc in
            let (pat2,pat_e) = check_pat l_e p2 pat_e in
              C.equate_types l ret_type { t = Tapp([pat1.typ], Path.listpath) };
              C.equate_types l ret_type pat2.typ;
              (A.mk_pcons l pat1 sk pat2 rt, pat_e)
        | Ast.P_num_add(xl,sk1,sk2,i) ->
            let nl = xl_to_nl xl in
            let ax = C.new_type () in
            C.equate_types l ret_type { t = Tapp([], Path.numpath) };
            C.equate_types (snd nl) ax ret_type;
          (A.mk_pnum_add l nl sk1 sk2 i rt, add_binding acc nl ax)
        | Ast.P_lit(lit) ->
            let lit = check_lit lit in
              C.equate_types l ret_type lit.typ;
              (A.mk_plit l lit rt, acc)

  and check_fpat a (l_e : lex_env) (Ast.Fpat(id,sk,p,l)) (acc : pat_env)  
                : (((field_descr id * lskips * pat) * (Name.t * Ast.l)) * pat_env)=
    let (p,acc) = check_pat l_e p acc in
    let ((id,t,n,_),l') = check_field id in
      C.equate_types l t { t = Tfn(a,p.typ) };
      (((id,sk,p),(n,l')), acc)

  and check_pats (l_e : lex_env) (acc : pat_env) (ps : Ast.pat list) 
                : pat list * pat_env =
    List.fold_right 
      (fun p (pats,pat_e) -> 
         let (pat,pat_e) = check_pat l_e p pat_e in
           (pat::pats,pat_e))
      ps
      ([],acc) 

  (* Given an identifier, start at the left and follow it as a module path until
   * the first field/value reference (according to for_field) is encountered.
   * Return the prefix including that reference as a separate identifier.  If a
   * lex_env is supplied, check for value reference in it for the first name
   * only.
   *
   * In the formal type system, we don't calculate this split, but instead use
   * the id_field 'E |- id field' and id_value 'E |- id value' judgments to
   * ensure that the id is one that would be returned by this function.  That
   * is, the id follows the module reference whenever there is ambiguity.  *)
  let rec get_id_mod_prefix (for_field : bool) (check_le : lex_env option) 
        (env : env) (Ast.Id(mp,xl,l_add)) 
        (prefix_acc : (Ast.x_l * Ast.lex_skips) list) : Ast.id * (Ast.lex_skips * Ast.id) option =
    match mp with
      | [] -> 
          let n = Name.strip_lskip (Name.from_x xl) in
          let unbound = 
            if for_field then 
              Nfmap.apply env.f_env n = None 
            else 
              (Nfmap.apply env.v_env n = None &&
               (match check_le with 
                  | None -> true 
                  | Some(le) -> Nfmap.apply le n = None))
          in
          let id = Ast.Id(List.rev prefix_acc,xl,l_add) in
            if unbound then
              raise_error (Ast.xl_to_l xl) 
                (if for_field then "unbound field name" else "unbound variable")
                Ident.pp (Ident.from_id id)
            else
              (id, None)
      | (xl',sk)::mp' ->
          let n = Name.strip_lskip (Name.from_x xl') in
          let unbound = 
            if for_field then 
              Nfmap.apply env.f_env n = None 
            else 
              (Nfmap.apply env.v_env n = None &&
               (match check_le with 
                  | None -> true 
                  | Some(le) -> Nfmap.apply le n = None))
          in
          let id = Ast.Id(List.rev prefix_acc,xl',l_add) in
            if unbound then
              begin
                match Nfmap.apply env.m_env n with
                  | None ->
                      raise_error (Ast.xl_to_l xl') 
                        ("unbound module name or " ^
                         if for_field then "field name" else "variable")
                        Ident.pp (Ident.from_id id)
                  | Some(md) ->
                      get_id_mod_prefix for_field None md.mod_env
                        (Ast.Id(mp',xl,l_add)) 
                        ((xl',sk)::prefix_acc)
              end
            else
              (id, Some(sk,Ast.Id(mp',xl,l_add)))


  (* Chop up an identifier into a list of record projections.  Each projection
   * can be an identifier with a non-empty module path *)
  let rec disambiguate_projections sk (id : Ast.id) 
        : (Ast.lex_skips * Ast.id) list =
    match get_id_mod_prefix true None T.e id [] with
      | (id,None) -> [(sk,id)]
      | (id1,Some(sk',id2)) -> (sk,id1)::disambiguate_projections sk' id2

  (* Figures out which '.'s in an identifier are actually record projections.
   * This is ambiguous in the source since field names can be '.' separated
   * module paths *)
  let disambiguate_id (le : lex_env) (id : Ast.id) 
        : Ast.id * (Ast.lex_skips * Ast.id) list =
    match get_id_mod_prefix false (Some(le)) T.e id [] with
      | (id,None) -> (id, [])
      | (id1,Some(sk,id2)) ->
          (id1, disambiguate_projections sk id2)

  let rec check_all_fields (exp : Typed_ast.exp) 
        (fids : (Ast.lex_skips * Ast.id) list) =
    match fids with
      | [] ->
          exp
      | (sk,fid)::fids ->
          let ((id,t,fname,all_names),l) = check_field fid in
          let ret_type = C.new_type () in
            C.equate_types l t { t = Tfn(exp_to_typ exp, ret_type) };
            check_all_fields (A.mk_field l exp sk id (Some ret_type)) fids

  (* Corresponds to inst_val 'D,E |- val id : t gives S' and the 
  * var and val cases of check_exp_aux *)
  let check_val (l_e : lex_env) (mp : (Ast.x_l * Ast.lex_skips) list) 
        (n : Name.lskips_t) (l : Ast.l) : exp =
    match lookup_l l_e mp n with
      | Some(t,l,n) ->
          A.mk_var l n t
      | None -> 
          let mp' = List.map (fun (xl,_) -> xl_to_nl xl) mp in
          let mp'' = List.map (fun (xl,skips) -> (Name.from_x xl, skips)) mp in
          let e = path_lookup T.e mp' in
            match Nfmap.apply e.v_env (Name.strip_lskip n) with
              | None ->
                  if Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) = "Coq.TYPE_EQ" then
                    prerr_endline "Coq.TYPE_EQ HERE!";
                  raise_error l "unbound variable" Name.pp (Name.strip_lskip n)
              | Some(Constr(c)) ->
                  let (id,t,num_args) = 
                    inst_constr (Ident.mk_ident mp'' n l, l) c 
                  in
                    C.equate_types l t (C.new_type());
                    A.mk_constr l id (Some(t))
              | Some(Val(c)) ->
                  begin
                    match c.env_tag with
                      | K_method -> ()
                      | K_instance -> ()
                      | K_val ->
                          if not (Targetset.is_empty T.targets) then
                            raise_error l "unbound variable (has a val specification, but no definition)"
                              Name.pp (Name.strip_lskip n)
                          else
                            ()
                      | K_let -> ()
                      | K_target(letdef,defined_targets) ->
                          let undefined_targets = 
                            Targetset.diff T.targets defined_targets
                          in
                            if not letdef && 
                               not (Targetset.is_empty undefined_targets) then
                              raise_error l 
                                (Pp.pp_to_string
                                   (fun ppf -> 
                                      Format.fprintf ppf
                                        "unbound variable for targets {%a}"
                                        (Pp.lst ";" (fun ppf t -> Pp.pp_str ppf (target_to_string t)))
                                        (Targetset.elements undefined_targets)))
                                Name.pp (Name.strip_lskip n)
                            else
                              ()
                  end;
                  let (id,t) = 
                    inst_const (Ident.mk_ident mp'' n l, l) c 
                  in
                    C.equate_types l t (C.new_type());
                    A.mk_const l id (Some(t))

  let check_id (l_e : lex_env) (Ast.Id(mp,xl,l_add) as id) : exp =
    (* We could type check and disambiguate at the same time, but that would
     * have a more complicated implementation, so we don't *)
    let (Ast.Id(mp,xl,l), fields) = disambiguate_id l_e id in
    let exp = check_val l_e mp (Name.from_x xl) l in
      check_all_fields exp fields

  (* Corresponds to judgment check_exp 'Delta,E,E_ |- exp : t gives Sigma' *)
  let rec check_exp (l_e : lex_env) (Ast.Expr_l(exp,l)) : exp =
    let ret_type = C.new_type () in
    let rt = Some(ret_type) in 
      match exp with
        | Ast.Ident(i) -> 
            let exp = check_id l_e i in
              C.equate_types l ret_type (exp_to_typ exp);
              exp
        | Ast.Nvar((sk,n)) -> 
            let nv = Nvar.from_rope(n) in
            C.add_nvar nv;
            A.mk_nvar_e l sk nv  { t = Tapp([], Path.numpath) }
        | Ast.Fun(sk,pse) -> 
            let (param_pats,sk',body_exp,t) = check_psexp l_e pse in
              C.equate_types l t ret_type;
              A.mk_fun l sk param_pats sk' body_exp rt
        | Ast.Function(sk,bar_sk,bar,pm,end_sk) -> 
            let pm = Seplist.from_list_prefix bar_sk bar pm in
            let res = 
              Seplist.map
                (fun pe ->
                   let (res,t) = check_pexp l_e pe in
                     C.equate_types l t ret_type;
                     res)
                pm
            in
              A.mk_function l sk res end_sk rt
        | Ast.App(fn,arg) ->
            let fnexp = check_exp l_e fn in
            let argexp = check_exp l_e arg in
              C.equate_types l { t = Tfn(exp_to_typ argexp,ret_type) } (exp_to_typ fnexp);
              A.mk_app l fnexp argexp rt
        | Ast.Infix(e1, xl, e2) ->
            let n = Name.from_ix xl in
            let id = check_val l_e [] n (Ast.ixl_to_l xl) in
            let arg1 = check_exp l_e e1 in
            let arg2 = check_exp l_e e2 in
              C.equate_types l 
                { t = Tfn(exp_to_typ arg1, { t = Tfn(exp_to_typ arg2,ret_type) }) }
                (exp_to_typ id);
              A.mk_infix l arg1 id arg2 rt
        | Ast.Record(sk1,r,sk2) ->
            let (res,t,given_names,all_namesL) = check_fexps l_e r in
            let all_names = List.fold_left (fun s e -> NameSet.add e s) NameSet.empty all_namesL in
              if not (NameSet.subset all_names given_names) then
                raise_error l "missing field"
                  Name.pp
                  (NameSet.choose (NameSet.diff all_names given_names));
              C.equate_types l t ret_type;
              A.mk_record l sk1 res sk2 rt
        | Ast.Recup(sk1,e,sk2,r,sk3) ->
            let exp = check_exp l_e e in
            let (res,t,_,_) = check_fexps l_e r in
              C.equate_types l (exp_to_typ exp) t;
              C.equate_types l t ret_type;
              A.mk_recup l sk1 exp sk2 res sk3 rt
        | Ast.Field(e,sk,fid) ->
            let exp = check_exp l_e e in
            let fids = disambiguate_projections sk fid in
            let new_exp = check_all_fields exp fids in
              C.equate_types l ret_type (exp_to_typ new_exp);
              new_exp
        | Ast.Case(sk1,e,sk2,bar_sk,bar,pm,l',sk3) ->
            let pm = Seplist.from_list_prefix bar_sk bar pm in
            let exp = check_exp l_e e in
            let a = C.new_type () in
            let res = 
              Seplist.map
                (fun pe ->
                   let (res,t) = check_pexp l_e pe in
                     C.equate_types l' t a;
                     res)
                pm
            in
              C.equate_types l a { t = Tfn(exp_to_typ exp,ret_type) };
              A.mk_case false l sk1 exp sk2 res sk3 rt
        | Ast.Typed(sk1,e,sk2,typ,sk3) ->
            let exp = check_exp l_e e in
            let src_t = typ_to_src_t build_wild C.add_tyvar C.add_nvar T.d T.e typ in
              C.equate_types l src_t.typ (exp_to_typ exp);
              C.equate_types l src_t.typ ret_type;
              A.mk_typed l sk1 exp sk2 src_t sk3 rt
        | Ast.Let(sk1,lb,sk2, body) -> 
            let (lb,pat_env) = check_letbind_internal l_e lb in
            let body_exp = check_exp (Nfmap.union l_e pat_env) body in
              C.equate_types l ret_type (exp_to_typ body_exp);
              A.mk_let l sk1 lb sk2 body_exp rt
        | Ast.Tup(sk1,es,sk2) ->
            let es = Seplist.from_list es in
            let exps = Seplist.map (check_exp l_e) es in
              C.equate_types l ret_type 
                { t = Ttup(Seplist.to_list_map exp_to_typ exps) };
              A.mk_tup l sk1 exps sk2 rt
        | Ast.List(sk1,es,sk3,semi,sk2) -> 
            let es = Seplist.from_list_suffix es sk3 semi in
            let exps = Seplist.map (check_exp l_e) es in
            let a = C.new_type () in
              Seplist.iter (fun exp -> C.equate_types l a (exp_to_typ exp)) exps;
              C.equate_types l ret_type { t = Tapp([a], Path.listpath) };
              A.mk_list l sk1 exps sk2 ret_type
        | Ast.Vector(sk1,es,sk3,semi,sk2) -> 
            let es = Seplist.from_list_suffix es sk3 semi in
            let exps = Seplist.map (check_exp l_e) es in
            let a = C.new_type () in
            let len = {t = Tne( { nexp=Nconst(Seplist.length exps)} ) }in
              Seplist.iter (fun exp -> C.equate_types l a (exp_to_typ exp)) exps;
              C.equate_types l ret_type { t = Tapp([a;len], Path.vectorpath) };
              A.mk_vector l sk1 exps sk2 ret_type
        | Ast.VAccess(e,sk1,nexp,sk2) -> 
            let exp = check_exp l_e e in
            let n = nexp_to_src_nexp C.add_nvar nexp in
            let vec_n = C.new_nexp () in
            let t = exp_to_typ exp in
              C.equate_types l { t = Tapp([ ret_type;{t = Tne(vec_n)}],Path.vectorpath) } t;
              C.in_range l vec_n n.nt;
              A.mk_vaccess l exp sk1 n sk2 ret_type
        | Ast.VAccessR(e,sk1,n1,sk2,n2,sk3) -> 
            let exp = check_exp l_e e in
            let n1 = nexp_to_src_nexp C.add_nvar n1 in
            let n2 = nexp_to_src_nexp C.add_nvar n2 in
            let vec_n = C.new_nexp () in
            let vec_t = C.new_type () in
            let t = exp_to_typ exp in
              C.equate_types l { t=Tapp([vec_t;{t = Tne(vec_n)}], Path.vectorpath) } t;
              C.in_range l n2.nt n1.nt;
              C.in_range l vec_n n2.nt;
              C.equate_types l ret_type { t =Tapp([vec_t;{t = Tne({ nexp=Nadd(n2.nt,{nexp=Nneg(n1.nt)})})}], Path.vectorpath)};
              A.mk_vaccessr l exp sk1 n1 sk2 n2 sk3 ret_type 
        | Ast.Paren(sk1,e,sk2) ->
            let exp = check_exp l_e e in
              C.equate_types l ret_type (exp_to_typ exp);
              A.mk_paren l sk1 exp sk2 rt
        | Ast.Begin(sk1,e,sk2) ->
            let exp = check_exp l_e e in
              C.equate_types l ret_type (exp_to_typ exp);
              A.mk_begin l sk1 exp sk2 rt
        | Ast.If(sk1,e1,sk2,e2,sk3,e3) ->
            let exp1 = check_exp l_e e1 in
            let exp2 = check_exp l_e e2 in
            let exp3 = check_exp l_e e3 in
              C.equate_types l ret_type (exp_to_typ exp2);
              C.equate_types l ret_type (exp_to_typ exp3);
              C.equate_types l (exp_to_typ exp1) { t = Tapp([], Path.boolpath) };
              A.mk_if l sk1 exp1 sk2 exp2 sk3 exp3 rt
        | Ast.Cons(e1,sk,e2) ->
            let e = 
              check_exp l_e 
                (Ast.Expr_l(Ast.Infix(e1,Ast.SymX_l((sk,r"::"), l),e2), l))
            in 
              C.equate_types l ret_type (exp_to_typ e);
              e
        | Ast.Lit(lit) ->
            let lit = check_lit lit in
              C.equate_types l ret_type lit.typ;
              A.mk_lit l lit rt
        | Ast.Set(sk1,es,sk2,semi,sk3) -> 
            let es = Seplist.from_list_suffix es sk2 semi in
            let exps = Seplist.map (check_exp l_e) es in
            let a = C.new_type () in
              Seplist.iter (fun exp -> C.equate_types l a (exp_to_typ exp)) exps;
              C.equate_types l ret_type { t = Tapp([a], Path.setpath) };
              A.mk_set l sk1 exps sk3 ret_type
        | Ast.Setcomp(sk1,e1,sk2,e2,sk3) ->
            let not_shadowed n =
              not (Nfmap.in_dom n l_e) &&
              not (Nfmap.in_dom n T.e.v_env)
            in
            let vars = Ast_util.setcomp_bindings not_shadowed e1 in
            let new_vars = 
              NameSet.fold
                (fun v m -> Nfmap.insert m (v, (C.new_type (),l)))
                vars
                Nfmap.empty
            in
            let env = Nfmap.union l_e new_vars in
            let exp1 = check_exp env e1 in
            let exp2 = check_exp env e2 in
            let a = C.new_type () in
              C.equate_types l (exp_to_typ exp2) { t = Tapp([], Path.boolpath) };
              C.equate_types l (exp_to_typ exp1) a;
              C.equate_types l ret_type { t = Tapp([a], Path.setpath) };
              A.mk_setcomp l sk1 exp1 sk2 exp2 sk3 vars rt
        | Ast.Setcomp_binding(sk1,e1,sk2,sk5,qbs,sk3,e2,sk4) ->
            let (quant_env,qbs) = check_qbs false l_e qbs in
            let env = Nfmap.union l_e quant_env in
            let exp1 = check_exp env e1 in
            let exp2 = check_exp env e2 in
            let a = C.new_type () in
              C.equate_types l (exp_to_typ exp2) { t = Tapp([], Path.boolpath) };
              C.equate_types l (exp_to_typ exp1) a;
              C.equate_types l ret_type { t = Tapp([a], Path.setpath) };
              A.mk_comp_binding l false sk1 exp1 sk2 sk5 
                (List.rev qbs) sk3 exp2 sk4 rt
        | Ast.Quant(q,qbs,s,e) ->
            let (quant_env,qbs) = check_qbs false l_e qbs in
            let et = check_exp (Nfmap.union l_e quant_env) e in
              C.equate_types l ret_type { t = Tapp([], Path.boolpath) };
              C.equate_types l ret_type (exp_to_typ et);
              A.mk_quant l q (List.rev qbs) s et rt
        | Ast.Listcomp(sk1,e1,sk2,sk5,qbs,sk3,e2,sk4) ->
            let (quant_env,qbs) = check_qbs true l_e qbs in
            let env = Nfmap.union l_e quant_env in
            let exp1 = check_exp env e1 in
            let exp2 = check_exp env e2 in
            let a = C.new_type () in
              C.equate_types l (exp_to_typ exp2) { t = Tapp([], Path.boolpath) };
              C.equate_types l (exp_to_typ exp1) a;
              C.equate_types l ret_type { t = Tapp([a], Path.listpath) };
              A.mk_comp_binding l true sk1 exp1 sk2 sk5 
                (List.rev qbs) sk3 exp2 sk4 rt

  (* Corresponds to check_quant_binding or check_listquant_binding
   * 'D,E,EL |- qbind .. qbind gives EL2,S' depending on is_list *)
  and check_qbs (is_list : bool) (l_e : lex_env) (qbs : Ast.qbind list)=
    List.fold_left
      (fun (env,lst) -> 
         function
           | Ast.Qb_var(xl) ->
               if is_list then
                 raise_error (Ast.xl_to_l xl) "unrestricted quantifier in list comprehension"
                   Name.pp (Name.strip_lskip (Name.from_x xl));
               let a = C.new_type () in
               let n = Name.from_x xl in
                 (add_binding env (n, Ast.xl_to_l xl) a,
                  Qb_var({ term = n; locn = Ast.xl_to_l xl; typ = a; rest = (); })::lst)
           | Ast.Qb_list_restr(s1,p,s2,e,s3) ->
               let et = check_exp (Nfmap.union l_e env) e in
               let (pt,p_env) = check_pat (Nfmap.union l_e env) p env in
               let a = C.new_type () in
                 C.equate_types pt.locn pt.typ a;
                 C.equate_types (exp_to_locn et) (exp_to_typ et)
                   { t = Tapp([a], Path.listpath) };
                 (p_env,
                  Qb_restr(true,s1, pt, s2, et, s3)::lst)
           | Ast.Qb_restr(s1,(Ast.Pat_l(_,l) as p),s2,e,s3) ->
               if is_list then
                 raise_error l "set-restricted quantifier in list comprehension"
                   (* TODO: Add a pretty printer *)
                   (fun _ _ -> ()) p;
               let et = check_exp (Nfmap.union l_e env) e in
               let (pt,p_env) = check_pat (Nfmap.union l_e env) p env in
               let a = C.new_type () in
                 C.equate_types pt.locn pt.typ a;
                 C.equate_types (exp_to_locn et) (exp_to_typ et) 
                   { t = Tapp([a], Path.setpath) };
                 (p_env,
                  Qb_restr(false,s1, pt, s2, et, s3)::lst))
      (empty_lex_env,[])
      qbs

  and check_fexp (l_e : lex_env) (Ast.Fexp(i,sk1,e,l)) 
                 : (field_descr id * lskips * exp * Ast.l) * t *
                                           Name.t * Ast.l * Name.t list =
    let ((id,t,fname,all_names),l') = check_field i in
    let exp = check_exp l_e e in
    let ret_type = C.new_type () in
      C.equate_types l t { t = Tfn(ret_type, exp_to_typ exp) };
      ((id,sk1,exp,l), ret_type, fname, l', all_names)

  and check_fexps (l_e : lex_env) (Ast.Fexps(fexps,sk,semi,l)) 
        : (field_descr id * lskips * exp * Ast.l) lskips_seplist * t * 
                                             NameSet.t * Name.t list =
    let fexps = Seplist.from_list_suffix fexps sk semi in
    let stuff = Seplist.map (check_fexp l_e) fexps in
    let ret_type = C.new_type () in
      check_dup_field_names (Seplist.to_list_map (fun (_,_,n,l,_) -> (n,l)) stuff);
      Seplist.iter (fun (_,t,_,_,_) -> C.equate_types l t ret_type) stuff;
      (Seplist.map (fun (x,_,_,_,_) -> x) stuff,
       ret_type,
       List.fold_right 
         NameSet.add
         (Seplist.to_list_map (fun (_,_,n,_,_) -> n) stuff)
         NameSet.empty, 
       (match Seplist.to_list_map (fun (_,_,_,_,x) -> x) stuff with
          | x::_ -> x
          | _ -> assert false))

  and check_psexp_help l_e ps ot sk e l
        : pat list * (lskips * src_t) option * lskips * exp * t = 
    let ret_type = C.new_type () in
    let (param_pats,pat_env) = check_pats l_e empty_pat_env ps in
    let body_exp = check_exp (Nfmap.union l_e pat_env) e in
    let t = multi_fun (List.map annot_to_typ param_pats) (exp_to_typ body_exp) in
    let annot = 
      match ot with
        | Ast.Typ_annot_none -> 
            None
        | Ast.Typ_annot_some(sk',typ) ->
            let src_t' = typ_to_src_t build_wild C.add_tyvar C.add_nvar T.d T.e typ in
              C.equate_types l src_t'.typ (exp_to_typ body_exp);
              Some (sk',src_t')
    in
      C.equate_types l ret_type t;
      (param_pats,annot,sk,body_exp,ret_type)

  and check_psexp (l_e : lex_env) (Ast.Patsexp(ps,sk,e,l)) 
        : pat list * lskips * exp * t = 
    let (a,b,c,d,e) = check_psexp_help l_e ps Ast.Typ_annot_none sk e l in
      (a,c,d,e)

  and check_pexp (l_e : lex_env) (Ast.Patexp(p,sk1,e,l)) 
        : (pat * lskips * exp * Ast.l) * t = 
    match check_psexp l_e (Ast.Patsexp([p],sk1,e,l)) with
      | ([pat],_,exp,t) -> ((pat,sk1,exp,l),t)
      | _ -> assert false 

  and check_funcl (l_e : lex_env) (Ast.Funcl(xl,ps,topt,sk,e)) l =
    let (ps,topt,s,e,t) = check_psexp_help l_e ps topt sk e l in
      ({ term = Name.from_x xl;
         locn = Ast.xl_to_l xl;
         typ = t;
         rest = (); },
       (ps,topt,s,e,t))

  and check_letbind_internal (l_e : lex_env) (Ast.Letbind(lb,l)) 
        : letbind * pat_env = 
    match lb with
      | Ast.Let_val(p,topt,sk',e) ->
          let (pat,pat_env) = check_pat l_e p empty_pat_env in
          let exp = check_exp l_e e in
          let annot = 
            match topt with
              | Ast.Typ_annot_none -> 
                  None
              | Ast.Typ_annot_some(sk',typ) ->
                  let src_t' = typ_to_src_t build_wild C.add_tyvar C.add_nvar T.d T.e typ in
                    C.equate_types l src_t'.typ pat.typ;
                    Some (sk',src_t')
          in
            C.equate_types l pat.typ (exp_to_typ exp);
            ((Let_val(pat,annot,sk',exp),l), pat_env)
      | Ast.Let_fun(funcl) ->
          let (xl, (a,b,c,d,t)) = check_funcl l_e funcl l in
            ((Let_fun(xl,a,b,c,d),l),
             add_binding empty_pat_env (xl.term, xl.locn) t)

  (* Check lemmata expressions that must have type ret, which is expected to be bool but 
     for flexibility can be provided.
   *)
  let check_lem_exp (l_e : lex_env) l e ret =
    let exp = check_exp l_e e in
    C.equate_types l ret (exp_to_typ exp);
    let Tconstraints(tnvars,constraints,length_constraints) = C.inst_leftover_uvars l in
    (exp,Tconstraints(tnvars,constraints,length_constraints))

  let check_constraint_subset l cs1 cs2 = 
    unsat_constraint_err l
      (List.filter
         (fun (p,tv) ->
            not (List.exists 
                   (fun (p',tv') -> 
                      Path.compare p p' = 0 && tnvar_compare tv tv' = 0)
                   cs2))
         cs1)

  let check_constraint_redundancies l csl csv =
    List.iter (fun c -> C.check_numeric_constraint_implication l c csv) csl

  (* Check that a value definition has the right type according to previous
   * definitions of that name in the same module.
   * def_targets is None if the definitions is not target specific, otherwise it
   * is the set of targets that the definition is for.  def_env is the name and
   * types of all of the variables defined *)
  let apply_specs_for_def (def_targets : Targetset.t option) (l:Ast.l) 
    (def_env :  (Types.t * Ast.l) Typed_ast.Nfmap.t)  =
    Nfmap.iter
      (fun n (t,l) ->
         let const_data = Nfmap.apply T.new_module_env.v_env n in
           match const_data with
             | None ->
                 begin
                   match def_targets with
                     | Some _ -> 
                         raise_error l
                           "target-specific definition without preceding 'val' specification"
                           Name.pp n
                     | None -> ()
                 end
             | Some(Val(c)) ->
                 begin
                   match (c.env_tag,def_targets) with
                     | ((K_method|K_instance),_) ->
                         raise_error l "defined variable is already defined as a class method" 
                           Name.pp n
                     | (K_val,_) ->
                         ()
                     | (K_let,None) | (K_target(true,_),None)->
                         raise_error l
                           "defined variable is already defined"
                           Name.pp n
                     | (K_let,Some _) ->
                         raise_error l
                           "target-specific definition without preceding 'val' specification"
                           Name.pp n
                     | (K_target(false,_), None) -> 
                         ()
                     | (K_target(_,prior_targets),Some(def_targets)) ->
                         let duplicate_targets = 
                           Targetset.inter prior_targets def_targets
                         in
                         let relevant_duplicate_targets =
                           Targetset.inter duplicate_targets T.targets
                         in
                           if not (Targetset.is_empty relevant_duplicate_targets) then
                             raise_error l
                               (Printf.sprintf "defined variable already has a %s-specific definition" 
                                  (target_to_string 
                                     (Targetset.choose relevant_duplicate_targets)))
                               Name.pp n 
                 end;
                 let a = C.new_type () in
                   C.equate_types c.spec_l a c.const_type;
                   C.equate_types l a t
             | Some(Constr _) ->
                 raise_error l "defined variable is already defined as a constructor"
                   Name.pp n)
      def_env;
    let Tconstraints(tnvars, constraints,l_constraints) = C.inst_leftover_uvars l in
      Nfmap.iter
        (fun n (_,l') ->
           match Nfmap.apply T.e.v_env n with
             | None -> ()
             | Some(Val(c)) ->
                 check_constraint_subset l constraints c.const_class;
                 check_constraint_redundancies l l_constraints c.const_ranges
             | _ -> assert false)
        def_env;
      Tconstraints(tnvars, constraints,l_constraints)

  let apply_specs_for_method def_targets l def_env inst_type =
    Nfmap.iter
      (fun n (t,l) ->
         if not (def_targets = None) then
           raise_error l "instance method must not be target specific"
             Name.pp n;
         let const_data = Nfmap.apply T.e.v_env n in
           match const_data with
             | Some(Val(c)) when c.env_tag = K_method ->
                 (* assert List.length c.const_tparams = 1 *)
                 let tv = List.hd c.const_tparams in 
                 let subst = TNfmap.from_list [(tv, inst_type)] in
                 let spec_typ = type_subst subst c.const_type in
                 let a = C.new_type () in
                   C.equate_types c.spec_l a spec_typ;
                   C.equate_types l a t
             | _ -> 
                 raise_error l "instance method not bound to class method"
                   Name.pp n)
      def_env;
    let Tconstraints(tnvars, constraints,l_constraints) = C.inst_leftover_uvars l in
      unsat_constraint_err l constraints;
      Tconstraints(tnvars, [], l_constraints)

  let apply_specs for_method (def_targets : Targetset.t option) l env = 
    match for_method with
      | None -> apply_specs_for_def def_targets l env
      | Some(t) -> apply_specs_for_method def_targets l env t

  (* See Expr_checker signature above *)
  let check_letbind for_method (def_targets : Targetset.t option) l lb =
    let (lb,pe) = check_letbind_internal empty_lex_env lb in
      (lb, pe, apply_specs for_method def_targets l pe)

  (* See Expr_checker signature above *)
  let check_funs for_method (def_targets : Targetset.t option) l funcls =
    let env =
      List.fold_left
        (fun l_e (Ast.Rec_l(Ast.Funcl(xl,_,_,_,_),_)) ->
           let n = Name.strip_lskip (Name.from_x xl) in
             if Nfmap.in_dom n l_e then
               l_e
             else
               add_binding l_e (xl_to_nl xl) (C.new_type ()))
        empty_lex_env
        (Seplist.to_list funcls)
      in
      let funcls = 
        Seplist.map
          (fun (Ast.Rec_l(funcl,l')) -> 
             let (n,(a,b,c,d,t)) = check_funcl env funcl l' in
               C.equate_types l' t 
                 (match Nfmap.apply env (Name.strip_lskip n.term) with
                    | Some(t,_) -> t
                    | None -> assert false);
               (n,a,b,c,d))
          funcls
      in
        (funcls, env, apply_specs for_method def_targets l env)

  (* See Expr_checker signature above *)
  let check_indrels (def_targets : Targetset.t option) l clauses =
    let rec_env =
      List.fold_left
        (fun l_e (Ast.Rule_l(Ast.Rule(_,_,_,_,_,_,xl,_), _), _) ->
           let n = Name.strip_lskip (Name.from_x xl) in
             if Nfmap.in_dom n l_e then
               l_e
             else
               add_binding l_e (xl_to_nl xl) (C.new_type ()))
        empty_lex_env
        clauses
    in
    let clauses = Seplist.from_list clauses in
    let c =
      Seplist.map
        (fun (Ast.Rule_l(Ast.Rule(xl,s1,ns,s2,e,s3,xl',es), l2)) ->
           let quant_env =
             List.fold_left
               (fun l_e xl -> add_binding l_e (xl_to_nl xl) (C.new_type ()))
               empty_lex_env
               ns
           in
           let extended_env = Nfmap.union rec_env quant_env in
           let et = check_exp extended_env e in
           let ets = List.map (check_exp extended_env) es in
           let new_name =
              match xl with
                | Ast.X_l_none -> None
                | Ast.X_l_some (xl, _) -> Some (Name.from_x xl)
           in
           let new_name' = annot_name (Name.from_x xl') (Ast.xl_to_l xl') rec_env in
             C.equate_types l2 (exp_to_typ et) { t = Tapp([], Path.boolpath) };
             C.equate_types l2 
               new_name'.typ 
               (multi_fun 
                  (List.map exp_to_typ ets) 
                  { t = Tapp([], Path.boolpath) });
             (new_name,
              s1,
              List.map 
                (fun xl -> annot_name (Name.from_x xl) (Ast.xl_to_l xl) quant_env)
                ns,
              s2,
              Some et,
              s3,
              new_name',
              ets))
        clauses
    in
      (c,rec_env, apply_specs None def_targets l rec_env)

end

let tvs_to_set (tvs : (Types.tnvar * Ast.l) list) : TNset.t =
  match DupTvs.duplicates (List.map fst tvs) with
    | DupTvs.Has_dups(tv) ->
        let (tv',l) = 
          List.find (fun (tv',_) -> TNvar.compare tv tv' = 0) tvs
        in
          raise_error l "duplicate type variable" TNvar.pp tv'
    | DupTvs.No_dups(tvs_set) ->
        tvs_set

let anon_error l = 
  raise (Ident.No_type(l, "anonymous types not permitted here: _"))

let rec check_free_tvs (tvs : TNset.t) (Ast.Typ_l(t,l)) : unit =
  match t with
    | Ast.Typ_wild _ ->
        anon_error l
    | Ast.Typ_var(Ast.A_l((t,x),l)) ->
       if TNset.mem (Ty (Tyvar.from_rope x)) tvs then
        ()
       else
        raise_error l "unbound type variable" 
          Tyvar.pp (Tyvar.from_rope x)
    | Ast.Typ_fn(t1,_,t2) -> 
        check_free_tvs tvs t1; check_free_tvs tvs t2
    | Ast.Typ_tup(ts) -> 
        List.iter (check_free_tvs tvs) (List.map fst ts)
    | Ast.Typ_Nexps(n) -> check_free_ns tvs n
    | Ast.Typ_app(_,ts) -> 
        List.iter (check_free_tvs tvs) ts
    | Ast.Typ_paren(_,t,_) -> 
        check_free_tvs tvs t
and check_free_ns (nvs: TNset.t) (Ast.Length_l(nexp,l)) : unit =
  match nexp with
   | Ast.Nexp_var((_,x)) ->
       if TNset.mem (Nv (Nvar.from_rope x)) nvs then
        ()
       else
        raise_error l "unbound length variable" Nvar.pp (Nvar.from_rope x)
   | Ast.Nexp_constant _ -> ()
   | Ast.Nexp_sum(n1,_,n2) | Ast.Nexp_times(n1,_,n2) -> check_free_ns nvs n1 ; check_free_ns nvs n2
   | Ast.Nexp_paren(_,n,_) -> check_free_ns nvs n


(* As we process definitions, we need to keep track of the type definitions
 * (type_defs), class instance definitions (instance list Pfmap.t) and
 * function/value/module/field (env) definitions we encounter. *)
type defn_ctxt = { 
  (* All type definitions ever seen *) 
  all_tdefs : type_defs; 
  (* All types defined in this sequence of definitions *)
  new_tdefs : type_defs;

  (* All class instances ever seen *)
  all_instances : instance list Pfmap.t;
  (* All class instances defined in this sequence of definitions *)
  new_instances : instance list Pfmap.t;

  (* The current value/function/module/field/type_name environment *)
  cur_env : env;
  (* The value/function/module/field/type_names defined in this sequence of
   * definitions *)
  new_defs : env;

  (* The names of all assertions / lemmata defined. Used only to avoid using names multiple times. *)
  lemmata_labels : NameSet.t; }

(* Update the new and cumulative environment with new
 * function/value/module/field/path definitions according to set and select *)
let ctxt_add (select : env -> 'a Nfmap.t) (set : env -> 'a Nfmap.t -> env) 
      (ctxt : defn_ctxt) (m : Name.t * 'a)
      : defn_ctxt =
  { ctxt with 
        cur_env = set ctxt.cur_env (Nfmap.insert (select ctxt.cur_env) m);
        new_defs = set ctxt.new_defs (Nfmap.insert (select ctxt.new_defs) m); } 

(* Update new and cumulative enviroments with a new module definition, after
 * first checking that its name doesn't clash with another module definition in
 * the same definition sequence.  It can have the same name as another module
 * globally. *)
let add_m_to_ctxt (l : Ast.l) (ctxt : defn_ctxt) (k : Name.lskips_t) (v : mod_descr)
      : defn_ctxt = 
  let k = Name.strip_lskip k in
    if Nfmap.in_dom k ctxt.new_defs.m_env then
      raise_error l "duplicate module definition" Name.pp k
    else
      ctxt_add 
        (fun x -> x.m_env) 
        (fun x y -> { x with m_env = y }) 
        ctxt 
        (k,v)

(* Add a new type definition to the global and local contexts *)
let add_d_to_ctxt (ctxt : defn_ctxt) (p : Path.t) (d : tc_def) =
  { ctxt with all_tdefs = Pfmap.insert ctxt.all_tdefs (p,d);
              new_tdefs = Pfmap.insert ctxt.new_tdefs (p,d) }

(* Support for maps from paths to lists of things *)
let insert_pfmap_list (m : 'a list Pfmap.t) (k : Path.t) (v : 'a) 
      : 'a list Pfmap.t =
  match Pfmap.apply m k with
    | None -> Pfmap.insert m (k,[v])
    | Some(l) -> Pfmap.insert m (k,v::l)

(* Add a lemma name to the context *)
let add_lemma_to_ctxt (ctxt : defn_ctxt) (n : Name.t)  
      : defn_ctxt =
  { ctxt with lemmata_labels = NameSet.add n ctxt.lemmata_labels; }

(* Add a new instance the the new instances and the global instances *)
let add_instance_to_ctxt (ctxt : defn_ctxt) (p : Path.t) (i : instance) 
      : defn_ctxt =
  { ctxt with all_instances = insert_pfmap_list ctxt.all_instances p i;
              new_instances = insert_pfmap_list ctxt.new_instances p i; }

let add_let_defs_to_ctxt 
      (* The path of the enclosing module *)
      (mod_path : Name.t list)
      (ctxt : defn_ctxt)
      (* The type and length variables that were generalised for this definition *)
      (tnvars : Types.tnvar list) 
      (* The class constraints that the definition's type variables must satisfy
      *) 
      (constraints : (Path.t * Types.tnvar) list)
      (* The length constraints that the definition's length variables must satisfy *) 
      (lconstraints : Types.range list)
      (* The status for just this definition, must be either K_let or
       * K_target(false, ts), and if it is K_target, there must be a preceding
       * K_val *)
      (env_tag : env_tag) 
      (* If this definition should be inlined for a target, give that target,
       * the parameters and the body *)
      (substitution : (Targetset.t * ((Name.t,unit) annot list * exp)) option)
      (l_env : lex_env) 
      : defn_ctxt =
  let add_subst =
    match substitution with
      | None -> (fun c -> c)
      | Some(ts,s) ->
          (fun c -> 
             { c with substitutions = 
                 Targetset.fold
                   (fun t r -> Targetmap.insert r (t,s))
                   ts 
                   c.substitutions 
             })
  in
  let new_env =
    Nfmap.map
      (fun n (t,l) ->
        match Nfmap.apply ctxt.new_defs.v_env n with
          | None ->
              Val(add_subst
                    { const_binding = Path.mk_path mod_path n;
                      const_tparams = tnvars;
                      const_class = constraints;
                      const_ranges = lconstraints;
                      const_type = t;
                      spec_l = l;
                      env_tag = env_tag;
                      substitutions = Targetmap.empty })
          | Some(Val(c)) ->
              (* The definition is already in the context.  Here we just assume
               * it is compatible with the existing definition, having
               * previously checked it. *) 
              let tag =
                match (c.env_tag, env_tag) with
                  | (K_val, K_val) | (K_let,K_let) | ((K_method|K_instance),_) 
                  | (_,(K_method|K_instance)) | (K_let, K_val) | (K_target _, K_val) -> 
                      assert false
                  | (K_val, K_let) -> K_target(true, Targetset.empty)
                  | (K_val, K_target(letdef,targets)) -> 
                      K_target(letdef,targets)
                  | (K_let, K_target(_,targets)) -> K_target(true,targets)
                  | (K_target(_,targets),K_let) -> K_target(true,targets)
                  | (K_target(letdef1,targets1), K_target(letdef2,targets2)) ->
                      K_target(letdef1||letdef2, 
                               Targetset.union targets1 targets2)
              in
                Val(add_subst { c with env_tag = tag })
          | _ -> assert false)
      l_env
  in
  { ctxt with 
        cur_env = 
          { ctxt.cur_env with v_env = Nfmap.union ctxt.cur_env.v_env new_env };
        new_defs = 
          { ctxt.new_defs with 
                v_env = Nfmap.union ctxt.new_defs.v_env new_env } }

let tnvar_to_flat (tnvar : Ast.tnvar) : Typed_ast.tnvar =
  match tnvar with
    | (Ast.Avl(Ast.A_l((sk,tv),l))) -> Tn_A(sk,tv,l)
    | (Ast.Nvl(Ast.N_l((sk,nv),l))) -> Tn_N(sk,nv,l)

let tnvar_to_tnvar2 (tnvar:Ast.tnvar) =
   match tnvar with
    | (Ast.Avl(Ast.A_l((sk,tv),l))) -> (Ty(Tyvar.from_rope tv),l)
    | (Ast.Nvl(Ast.N_l((sk,nv),l))) -> (Nv(Nvar.from_rope nv),l)

(* Check a type definition and add it to the context.  mod_path is the path to
 * the enclosing module.  Ignores any constructors or fields, just handles the
 * type constructors. *)
let build_type_def_help (mod_path : Name.t list) (context : defn_ctxt) 
      (tvs : Ast.tnvar list) ((type_name,l) : name_l) (regex : name_sect option) (type_abbrev : Ast.typ option) 
      : defn_ctxt = 
  let tvs = List.map tnvar_to_tnvar2 tvs in
  let tn = Name.strip_lskip type_name in
  let type_path = Path.mk_path mod_path tn in
  let () =
    match Nfmap.apply context.new_defs.p_env tn with
      | None -> ()
      | Some(p, _) ->
          begin
            match Pfmap.apply context.all_tdefs p with
              | None -> assert false
              | Some(Tc_type _) ->
                  raise_error l "duplicate type constructor definition"
                    Name.pp tn
              | Some(Tc_class _) ->
                  raise_error l "type constructor already defined as a type class" 
                    Name.pp tn
          end
  in
  let regex = match regex with | Some(Name_restrict(_,_,_,_,r,_)) -> Some r | _ -> None in
  let new_ctxt = 
    ctxt_add 
      (fun x -> x.p_env) 
      (fun x y -> { x with p_env = y })
      context 
      (tn, (type_path, l))
  in
    begin
      match type_abbrev with
        | Some(typ) ->
            check_free_tvs (tvs_to_set tvs) typ;
            let src_t = 
              typ_to_src_t anon_error ignore ignore context.all_tdefs context.cur_env typ 
            in
              if (regex = None)
                then add_d_to_ctxt new_ctxt type_path 
                        (Tc_type((List.map fst tvs), Some(src_t.typ),None))
                else raise_error l "Type abbreviations may not restrict identifier names" Name.pp tn
        | None ->
            add_d_to_ctxt new_ctxt type_path 
              (Tc_type((List.map fst tvs), None, regex))
    end

let build_type_name_regexp (name: Ast.name_opt) : (name_sect option) =
  match name with
    | Ast.Name_sect_none -> None
    | Ast.Name_sect_name( sk1,name,sk2,sk3, regex,sk4) -> 
      let (n,l) = xl_to_nl name in
      if ((Name.to_string (Name.strip_lskip n)) = "name")
         then Some(Name_restrict(sk1,(n,l),sk2,sk3,regex,sk4))
      else raise_error l "Type name restrictions must begin with 'name'" Name.pp (Name.strip_lskip n)

(* Check a type definition and add it to the context.  mod_path is the path to
 * the enclosing module.  Ignores any constructors or fields, just handles the
 * type constructors. *)
let build_type_def (mod_path : Name.t list) (context : defn_ctxt) (td : Ast.td)
      : defn_ctxt = 
  match td with
    | Ast.Td(xl, tvs, regex, _, td) ->
        build_type_def_help mod_path context tvs (xl_to_nl xl) (build_type_name_regexp regex)
          (match td with
             | Ast.Te_abbrev(t) -> Some(t)
             | _ -> None)
    | Ast.Td_opaque(xl,tvs, regex) ->
        build_type_def_help mod_path context tvs (xl_to_nl xl) (build_type_name_regexp regex) None

(* Check a type definition and add it to the context.  mod_path is the path to
 * the enclosing module.  Ignores any constructors or fields, just handles the
 * type constructors. *)
let build_type_defs (mod_path : Name.t list) (ctxt : defn_ctxt) 
      (tds : Ast.td lskips_seplist) : defn_ctxt =
  List.fold_left (build_type_def mod_path) ctxt (Seplist.to_list tds)

let build_record tvs_set (ctxt : defn_ctxt) 
      (recs : (Ast.x_l * lskips * Ast.typ) lskips_seplist) 
      : (name_l * lskips * src_t) lskips_seplist =
  Seplist.map
    (fun (field_name,sk1,typ) ->
       let l' = Ast.xl_to_l field_name in
       let fn = Name.from_x field_name in
       let src_t = 
         typ_to_src_t anon_error ignore ignore ctxt.all_tdefs ctxt.cur_env typ 
       in
         check_free_tvs tvs_set typ;
         ((fn,l'),sk1,src_t))
    recs

let add_record_to_ctxt build_descr (ctxt : defn_ctxt) 
      (recs : (name_l * lskips * t) lskips_seplist) 
      : defn_ctxt  =
  snd
    (Seplist.map_acc_left
      (fun ((fn,l'),sk1,t) ctxt ->
         let fn' = Name.strip_lskip fn in
         let field_descr = build_descr fn' l' t in
         let () = 
           match Nfmap.apply ctxt.new_defs.f_env fn' with
             | None -> ()
             | Some _ ->
                 raise_error l' "duplicate field name definition"
                   Name.pp fn'
         in
         let ctxt =
           ctxt_add 
             (fun x -> x.f_env) 
             (fun x y -> { x with f_env = y })
             ctxt 
             (fn', field_descr)
         in
           ((), ctxt))
      ctxt
      recs)

let rec build_variant build_descr tvs_set (ctxt : defn_ctxt) 
      (vars : Ast.ctor_def lskips_seplist) 
      : (name_l * lskips * src_t lskips_seplist) lskips_seplist * defn_ctxt =
  Seplist.map_acc_left
    (fun (Ast.Cte(ctor_name,sk1,typs)) ctxt ->
       let l' = Ast.xl_to_l ctor_name in 
       let src_ts =
         Seplist.map 
           (fun t ->
              typ_to_src_t anon_error ignore ignore ctxt.all_tdefs ctxt.cur_env t) 
           (Seplist.from_list typs)
        in
        let ctn = Name.from_x ctor_name in
        let ctn' = Name.strip_lskip ctn in
        let constr_descr = build_descr ctn' l' src_ts in
        let () = 
          match Nfmap.apply ctxt.new_defs.v_env ctn' with
            | None -> ()
            | Some(Constr _) ->
                raise_error l' "duplicate constructor definition"
                  Name.pp ctn'
            | Some(Val(c)) ->
                begin
                  match c.env_tag with
                    | K_method|K_instance ->
                        raise_error l' "constructor already defined as a class method name"
                          Name.pp ctn'
                    | K_val | K_let | K_target _ ->
                       raise_error l' "constructor already defined as a top-level variable binding" 
                         Name.pp ctn'
                end
        in
        let ctxt =
          ctxt_add 
            (fun x -> x.v_env) 
            (fun x y -> { x with v_env = y })
            ctxt 
            (ctn', constr_descr)
        in
          List.iter (fun (t,_) -> check_free_tvs tvs_set t) typs;
          (((ctn,l'),sk1,src_ts), ctxt))
    ctxt
    vars

let build_ctor_def (mod_path : Name.t list) (context : defn_ctxt)
      type_name (tvs : Ast.tnvar list)  (regexp : name_sect option) td
      : (name_l * tnvar list * texp * name_sect option) * defn_ctxt= 
  let l = Ast.xl_to_l type_name in
  let tnvs = List.map tnvar_to_flat tvs in
  let tvs_set = tvs_to_set (List.map tnvar_to_types_tnvar tnvs) in
  let tn = Name.from_x type_name in
  let type_path = Path.mk_path mod_path (Name.strip_lskip tn) in
    match td with
      | None -> 
          (((tn,l),tnvs,Te_opaque, regexp), context)
      | Some(sk3, Ast.Te_abbrev(t)) -> 
          (* Check and throw error if there's a regexp here *)
          (((tn,l), tnvs, 
            Te_abbrev(sk3,
                      typ_to_src_t anon_error ignore ignore context.all_tdefs context.cur_env t), None),
           context)
      | Some(sk3, Ast.Te_record(sk1',ntyps,sk2',semi,sk3')) ->
          let ntyps = Seplist.from_list_suffix ntyps sk2' semi in
          let field_names = 
            List.map
              (fun (field_name,_,_) -> 
                 Name.strip_lskip (Name.from_x field_name))
              (Seplist.to_list ntyps)
          in
          let recs = build_record tvs_set context ntyps in
          let ctxt =
            add_record_to_ctxt 
              (fun fname l t ->
                 { field_binding = Path.mk_path mod_path fname;
                   field_tparams = List.map (fun tnv -> fst (tnvar_to_types_tnvar tnv)) tnvs;
                   field_tconstr = type_path;
                   field_arg = t;
                   field_names = field_names; 
                   field_l = l})
              context
              (Seplist.map (fun (x,y,src_t) -> (x,y,src_t.typ)) recs)
          in
            (((tn,l), tnvs, Te_record(sk3,sk1',recs,sk3'), regexp), ctxt)
      | Some(sk3, Ast.Te_variant(sk_init_bar,bar,ntyps)) ->
          let ntyps = Seplist.from_list_prefix sk_init_bar bar ntyps in
          let ctor_names = 
            List.fold_right 
              (fun (Ast.Cte(ctor_name,_,_)) s -> 
                 NameSet.add (Name.strip_lskip (Name.from_x ctor_name)) s) 
              (Seplist.to_list ntyps)
              NameSet.empty 
          in
          let (vars,ctxt) =
            build_variant
              (fun cname l ts ->
                 Constr({ constr_binding = Path.mk_path mod_path cname;
                          constr_tparams =
                            List.map (fun tnv -> fst (tnvar_to_types_tnvar tnv)) tnvs;
                          constr_args = 
                            Seplist.to_list_map (fun t -> annot_to_typ t) ts;
                          constr_tconstr = type_path;
                          constr_names = ctor_names;
                          constr_l = l }))
              tvs_set
              context
              ntyps
          in
            (((tn,l),tnvs, Te_variant(sk3,vars), regexp), ctxt)

(* Builds the constructors and fields for a type definition, and the typed AST
 * *) 
let rec build_ctor_defs (mod_path : Name.t list) (ctxt : defn_ctxt) 
      (tds : Ast.td lskips_seplist) 
      : ((name_l * tnvar list * texp * name_sect option) lskips_seplist * defn_ctxt) =
  Seplist.map_acc_left
    (fun td ctxt -> 
       match td with
         | Ast.Td(type_name, tnvs, name_sec, sk3, td) ->
             build_ctor_def mod_path ctxt type_name tnvs (build_type_name_regexp name_sec) (Some (sk3,td))
         | Ast.Td_opaque(type_name, tnvs, name_sec) ->
             build_ctor_def mod_path ctxt type_name tnvs (build_type_name_regexp name_sec) None)
    ctxt
    tds

(* Finds a type class's path, and its methods, in the current enviroment, given
 * its name. *)
let lookup_class_p (ctxt : defn_ctxt) (id : Ast.id) : Path.t * Types.tnvar * (Name.t * t) list = 
  let p = lookup_p "class" ctxt.cur_env id in
    match Pfmap.apply ctxt.all_tdefs p with
      | None -> assert false
      | Some(Tc_class(tv,methods)) -> (p, tv,methods)
      | Some(Tc_type _) ->
          raise_error (match id with Ast.Id(_,_,l) -> l)
            "type constructor used as type class" Ident.pp (Ident.from_id id)

(* Process the "forall 'a. (C 'a) =>" part of a type,  Returns the bound
 * variables both as a list and as a set *)
let check_constraint_prefix (ctxt : defn_ctxt) 
      : Ast.c_pre -> 
        constraint_prefix option * 
        Types.tnvar list * 
        TNset.t * 
        ((Path.t * Types.tnvar) list * Types.range list) =
  let check_class_constraints c env =
   List.map
    (fun (Ast.C(id, tnv),sk) ->
    let tnv' = tnvar_to_flat tnv in
    let (tnv'',l) = tnvar_to_tnvar2 tnv in
    let (p,_,_) = lookup_class_p ctxt id in
    begin
      if TNset.mem tnv'' env then
         ()
      else
         raise_error l "unbound type variable" pp_tnvar tnv''
    end;
      (((Ident.from_id id, tnv'), sk),
       (p, tnv'')))
    c
  in
  let check_range_constraints rs env =
   List.map (fun (Ast.Range_l(r,l),sk) -> 
      match r with
       | Ast.Bounded(n1,sk1,n2) -> 
         let n1,n2 = nexp_to_src_nexp ignore n1, nexp_to_src_nexp ignore n2 in
         ((GtEq(l,n1,sk1,n2),sk),mk_gt_than l n1.nt n2.nt)
       | Ast.Fixed(n1,sk1,n2) -> 
         let n1,n2 = nexp_to_src_nexp ignore n1, nexp_to_src_nexp ignore n2 in
         ((Eq(l,n1,sk1,n2),sk),mk_eq_to l n1.nt n2.nt))
   rs
  in                        
  function
    | Ast.C_pre_empty ->
        (None, [], TNset.empty, ([],[]))
    | Ast.C_pre_forall(sk1,tvs,sk2,Ast.Cs_empty) ->
        let tnvars = List.map tnvar_to_tnvar2 tvs in
          (Some(Cp_forall(sk1, 
                          List.map tnvar_to_flat tvs, 
                          sk2, 
                          None)),  
           List.map fst tnvars,
           tvs_to_set (List.map (fun tn -> tnvar_to_types_tnvar (tnvar_to_flat tn)) tvs),
           ([],[]))
    | Ast.C_pre_forall(sk1,tvs,sk2,crs) ->
        let tyvars = List.map tnvar_to_tnvar2 tvs in
        let tnvarset = tvs_to_set tyvars in
        let (c,sk3,r,sk4) = match crs with 
                             | Ast.Cs_empty -> assert false
                             | Ast.Cs_classes(c,sk3) -> c,None,[],sk3
                             | Ast.Cs_lengths(r,sk3) -> [], None, r, sk3
                             | Ast.Cs_both(c,sk3,r,sk4) -> c, Some sk3, r, sk4 in
        let constraints = 
          let cs = check_class_constraints c tnvarset in
          let rs = check_range_constraints r tnvarset in
            (Cs_list(Seplist.from_list (List.map fst cs),sk3,Seplist.from_list (List.map fst rs),sk4), (List.map snd cs, List.map snd rs))
        in
          (Some(Cp_forall(sk1, 
                          List.map tnvar_to_flat tvs, 
                          sk2, 
                          Some(fst constraints))),
           List.map fst tyvars,
           tnvarset,
           snd constraints)
   

(* Check a "val" declaration. The name must not be already defined in the
 * current sequence of definitions (e.g., module body) *)
let check_val_spec l (mod_path : Name.t list) (ctxt : defn_ctxt)
      (Ast.Val_spec(sk1, xl, sk2, Ast.Ts(cp,typ))) =
  let l' = Ast.xl_to_l xl in
  let n = Name.from_x xl in
  let n' = Name.strip_lskip n in
  let (src_cp, tyvars, tnvarset, (sem_cp,sem_rp)) = check_constraint_prefix ctxt cp in 
  let () = check_free_tvs tnvarset typ in
  let src_t = typ_to_src_t anon_error ignore ignore ctxt.all_tdefs ctxt.cur_env typ in
  let () = 
    match Nfmap.apply ctxt.new_defs.v_env n' with
      | None -> ()
      | Some(Constr _) ->
          raise_error l' "specified variable already defined as a constructor"
            Name.pp n'
      | Some(Val(c)) ->
          begin 
            match c.env_tag with
            | K_method | K_instance->
                  raise_error l' "specified variable already defined as a class method name"
                    Name.pp n'
              | K_val | K_target _ -> 
                  raise_error l' "specified variable already specified"
                    Name.pp n'
              | K_let -> 
                  raise_error l' "specified variable already defined"
                    Name.pp n'
          end
  in
  let v =
    { const_binding = Path.mk_path mod_path n';
      const_tparams = tyvars;
      const_class = sem_cp;
      const_ranges = sem_rp;
      const_type = src_t.typ;
      spec_l = l;
      env_tag = K_val;
      substitutions = Targetmap.empty }
  in
    (ctxt_add 
       (fun x -> x.v_env) 
       (fun x y -> { x with v_env = y })
       ctxt (n',Val(v)),
     (sk1, (n,l'), sk2, (src_cp, src_t)))

(* Check a method definition in a type class.  mod_path is the path to the
 * enclosing module. class_p is the path to the enclosing type class, and tv is
 * its type parameter. *)
let check_class_spec l (mod_path : Name.t list) (ctxt : defn_ctxt)
      (class_p : Path.t) (tv : Types.tnvar) (sk1,xl,sk2,typ) 
      : const_descr * defn_ctxt * _ =
  let l' = Ast.xl_to_l xl in
  let n = Name.from_x xl in
  let n' = Name.strip_lskip n in
  let tnvars = TNset.add tv TNset.empty in
  let () = check_free_tvs tnvars typ in
  let src_t = typ_to_src_t anon_error ignore ignore ctxt.all_tdefs ctxt.cur_env typ in
  let () = 
    match Nfmap.apply ctxt.new_defs.v_env n' with
      | None -> ()
      | Some(Constr _) ->
          raise_error l' "class method already defined as a constructor"
            Name.pp n'
      | Some(Val(c)) ->
          begin
            match c.env_tag with
              | K_method | K_instance ->
                  raise_error l' "duplicate class method definition"
                    Name.pp n'
              | K_val | K_let | K_target _ ->
                  raise_error l' "class method already defined as a top-level variable"
                    Name.pp n'
          end
  in
  let v =
    { const_binding = Path.mk_path mod_path n';
      const_tparams = [tv];
      const_class = [(class_p, tv)];
      const_ranges = [];
      const_type = src_t.typ;
      spec_l = l;
      env_tag = K_method;
      substitutions = Targetmap.empty }
  in
  let ctxt =
    (ctxt_add 
       (fun x -> x.v_env) 
       (fun x y -> { x with v_env = y })
       ctxt (n',Val(v)))
  in
    (v, ctxt, (sk1, (n,l'), sk2, src_t))

let ast_targ_to_targ : Ast.target -> target = function
  | Ast.Target_ocaml _ -> Target_ocaml
  | Ast.Target_hol _ -> Target_hol
  | Ast.Target_isa _ -> Target_isa
  | Ast.Target_coq _ -> Target_coq
  | Ast.Target_tex _ -> Target_tex
  | Ast.Target_html _ -> Target_html

let target_opt_to_set : Ast.targets option -> Targetset.t option = function
  | None -> None
  | Some(Ast.Targets_concrete(_,targs,_)) ->
      Some(List.fold_right
             (fun (t,_) ks -> Targetset.add (ast_targ_to_targ t) ks)
             targs
             Targetset.empty)

let target_opt_to_env_tag : Targetset.t option -> env_tag = function
  | None -> K_let
  | Some(ts) -> K_target(false,ts)

let check_target_opt : Ast.targets option -> _ = function
  | None -> None
  | Some(Ast.Targets_concrete(s1,targs,s2)) -> 
      Some(s1,Seplist.from_list targs,s2)

let pat_to_name p = 
  match p.term with
    | P_var n -> { term = n; typ= p.typ; locn = p.locn; rest = (); }
    (* TODO error messages *)
    | _ -> assert false

(* check "let" definitions.  for_method should be None, unless checking a method
 * definition in an instance.  When checking an instance it should contain the
 * type that the instance is at.  In this case the returned env_tag must be
 * K_method, and the returned constraints and type variables must be empty. 
 * ts is the set of targets for which all variables must be defined (i.e., the
 * current backends, not the set of targets that this definition if for) *)
let check_val_def (ts : Targetset.t) (for_method : Types.t option) (l : Ast.l) 
      (ctxt : defn_ctxt) 
      : Ast.val_def -> 
        (* An environment representing the names bound by the definition *)
        pat_env * 
        val_def * 
        (* The type and length variables the definion is generalised over, and class constraints on the type variables, and length constraints on the length variables *)
        typ_constraints *
        (* Which targets the binding is for *)
        env_tag =
  let module T = struct 
    let d = ctxt.all_tdefs 
    let i = ctxt.all_instances 
    let e = ctxt.cur_env 
    let new_module_env = ctxt.new_defs
    let targets = ts
  end 
  in
  let module Checker = Make_checker(T) in
    function
      | Ast.Let_def(sk,target_opt,lb) ->
          let target_set = target_opt_to_set target_opt in
          let env_tag = target_opt_to_env_tag target_set in
          let target_opt = check_target_opt target_opt in
          let (lbs,e_v,constraints) = 
            Checker.check_letbind for_method target_set l lb 
          in 
            (e_v, (Let_def(sk,target_opt,lbs)), constraints, env_tag)
      | Ast.Let_rec(sk1,sk2,target_opt,funcls) ->
          let funcls = Seplist.from_list funcls in
          let target_set = target_opt_to_set target_opt in
          let (lbs,e_v,constraints) = 
            Checker.check_funs for_method target_set l funcls 
          in
          let env_tag = target_opt_to_env_tag target_set in
          let target_opt = check_target_opt target_opt in
            (e_v, (Rec_def(sk1,sk2,target_opt,lbs)), constraints, env_tag)
      | _ -> assert false

let check_lemma l ts (ctxt : defn_ctxt) 
      : Ast.lemma_decl -> 
        defn_ctxt *
        lskips *
        Ast.lemma_typ * 
        targets_opt *
        (name_l * lskips) option * 
        lskips * exp * lskips =
  let module T = struct 
    let d = ctxt.all_tdefs 
    let i = ctxt.all_instances 
    let e = ctxt.cur_env 
    let new_module_env = ctxt.new_defs
    let targets = ts
  end 
  in
  let bool_ty = { Types.t = Types.Tapp ([], Path.boolpath) } in
  let module Checker = Make_checker(T) in
  let lty_get_sk = function
    | Ast.Lemma_theorem sk -> (sk, Ast.Lemma_theorem None)
    | Ast.Lemma_assert sk -> (sk, Ast.Lemma_assert None)
    | Ast.Lemma_lemma sk -> (sk, Ast.Lemma_lemma None) in
  let module C = Constraint(T) in
    function
      | Ast.Lemma_unnamed (lty, target_opt, sk1, e, sk2) ->
          let (exp,constraints) = Checker.check_lem_exp empty_lex_env l e bool_ty in
          let (sk0, lty') = lty_get_sk lty in
          let target_opt = check_target_opt target_opt in
              (ctxt, sk0, lty', target_opt, None, sk1, exp, sk2) 
      | Ast.Lemma_named (lty, target_opt, name, sk1, sk2, e, sk3) ->
          let (exp,Tconstraints(tnvars,constraints,lconstraints)) = Checker.check_lem_exp empty_lex_env l e bool_ty in
          (* TODO It's ok for tnvars to have variables (polymorphic lemma), but typed ast should keep them perhaps? Not sure if it's ok for constraints to be unconstrained or if we need length constraints kept *)
          let target_opt = check_target_opt target_opt in
          let (sk0, lty') = lty_get_sk lty in
          let (n, l) = xl_to_nl name in
          let n_s = Name.strip_lskip n in
          let _ = if (NameSet.mem n_s ctxt.lemmata_labels) then 
                      raise_error l
                        "lemmata-label already used"
                         Name.pp n_s
                   else () in
          (add_lemma_to_ctxt ctxt n_s,  sk0, lty', target_opt, Some ((n,l), sk1), sk2, exp, sk3)

(* Check that a type can be an instance.  That is, it can be a type variable, a
 * function between type variables, a tuple of type variables or the application
 * of a (non-abbreviation) type constructor to variables.  Returns the
 * variables, and which kind of type it was. *)
let rec check_instance_type_shape (ctxt : defn_ctxt) (src_t : src_t)
      : TNset.t * Ulib.Text.t =
  let l = src_t.locn in 
  let err () = 
    raise_error l "class instance type must be a type constructor applied to type variables"
      pp_type src_t.typ
  in
  let to_tnvar src_t = 
    match src_t.term with
      | Typ_var(_,t) -> (Ty(t),src_t.locn)
      | Typ_len(n) -> (match n.nterm with 
                         | Nexp_var(_,n) -> (Nv(n),src_t.locn) 
                         | _ -> err ())
      | _ -> err ()
  in
  match src_t.term with
    | Typ_wild _ -> err ()
    | Typ_var(_,tv) -> (tvs_to_set [(Ty(tv),src_t.locn)], r"var")
    | Typ_fn(t1,_,t2) ->
        (tvs_to_set [to_tnvar t1; to_tnvar t2], r"fun")
    | Typ_tup(ts) ->
        (tvs_to_set (Seplist.to_list_map to_tnvar ts), r"tup")
    | Typ_app(p,ts) ->
        begin
          match Pfmap.apply ctxt.all_tdefs p.descr with
            | Some(Tc_type(_,Some _, _)) ->
                raise_error p.id_locn "type abbreviation in class instance type"
                  Ident.pp (match p.id_path with | Id_some id -> id | Id_none _ -> assert false)
            | _ -> 
                (tvs_to_set (List.map to_tnvar ts),
                 Name.to_rope (Path.to_name p.descr))
        end
    | Typ_len(n) ->
        begin
          match n.nterm with
            | Nexp_var(_,n) -> (tvs_to_set [(Nv(n),src_t.locn)], r"nvar")
            | Nexp_const(_,i) -> (tvs_to_set [], r"const")
            | _ -> err ()
        end
    | Typ_paren(_,t,_) -> check_instance_type_shape ctxt t

(* If a definition is target specific, we only want to check it with regards to
 * the backends that we are both translating to, and that it is for *)
let ast_def_to_target_opt = function
    | Ast.Val_def(Ast.Let_def(_,target_opt,_) |
                  Ast.Let_inline(_,_,target_opt,_) |
                  Ast.Let_rec(_,_,target_opt,_)) -> Some target_opt
    | Ast.Indreln(_,target_opt,_) -> Some target_opt
    | Ast.Lemma(Ast.Lemma_unnamed(_,target_opt,_,_,_)) -> Some target_opt
    | Ast.Lemma(Ast.Lemma_named(_,target_opt,_,_,_,_,_)) -> Some target_opt
    | Ast.Type_def _ -> None
    | Ast.Ident_rename _ -> None
    | Ast.Module _ -> None
    | Ast.Rename _ -> None
    | Ast.Open _ -> None
    | Ast.Spec_def _ -> None
    | Ast.Class _ -> None
    | Ast.Instance _ -> None


let change_effective_backends (backend_targets : Targetset.t) (Ast.Def_l(def,l)) = 
  match (ast_def_to_target_opt def) with 
    | None -> None
    | Some target_opt ->
        begin
          match target_opt_to_set target_opt with
            | None -> None
            | Some(ts) -> 
                Some(Targetset.inter ts backend_targets)
        end

(* backend_targets is the set of targets for which all variables must be defined
 * (i.e., the current backends, not the set of targets that this definition if
 * for) *)
let rec check_def (backend_targets : Targetset.t) (mod_path : Name.t list) 
      (ctxt : defn_ctxt) (Ast.Def_l(def,l)) semi_sk semi 
      : defn_ctxt * def_aux =
  let module T = 
    struct 
      let d = ctxt.all_tdefs 
      let i = ctxt.all_instances 
      let e = ctxt.cur_env 
      let new_module_env = ctxt.new_defs
    end 
  in
    match def with
      | Ast.Type_def(sk,tdefs) ->
          let tdefs = Seplist.from_list tdefs in
          let new_ctxt = build_type_defs mod_path ctxt tdefs in
          let (res,new_ctxt) = build_ctor_defs mod_path new_ctxt tdefs in
            (new_ctxt,Type_def(sk,res))
      | Ast.Val_def(Ast.Let_inline(sk1,sk2,target_opt,lb)) ->
          let (e_v,vd,Tconstraints(tnvs,constraints,lconstraints), env_tag) = 
            check_val_def backend_targets None l ctxt 
              (Ast.Let_def(sk1,target_opt,lb))
          in 
          let _ = unsat_constraint_err l constraints in
          let (sk1,sk2,target_opt,n,args,sk3,et) = 
            match vd with
              | Let_def(sk1, target_opt, (Let_val(p,src_t,sk3,e),l)) ->
                  (sk1,sk2,target_opt,pat_to_name p,[],sk3,e)
              | Let_def(sk1, target_opt, (Let_fun(n,ps,src_t,sk3,e),l)) ->
                  (sk1,sk2,target_opt,n, List.map pat_to_name ps,sk3,e)
              | _ ->
                  assert false
          in
          let sub = 
            (List.map 
               (fun x -> {x with term = Name.strip_lskip x.term})
               args, 
             et)
          in
          let ctxt = 
            add_let_defs_to_ctxt mod_path ctxt (TNset.elements tnvs)
              constraints lconstraints env_tag 
              (Some(((match env_tag with K_target(_,ts) -> ts | _ -> assert false), sub)))
              e_v
          in
            (ctxt, Val_def(Let_inline(sk1,sk2,target_opt,n,args,sk3,et), tnvs, constraints))
      | Ast.Val_def(val_def) ->
          let (e_v,vd,Tconstraints(tnvs,constraints,lconstraints), env_tag) = 
            check_val_def backend_targets None l ctxt val_def 
          in
            (add_let_defs_to_ctxt mod_path ctxt (TNset.elements tnvs)
               constraints lconstraints env_tag None e_v,
             Val_def(vd,tnvs, constraints))
      | Ast.Lemma(lem) ->
            let (ctxt', sk, lty, targs, name_opt, sk2, e, sk3) = check_lemma l backend_targets ctxt lem in
            (ctxt', Lemma(sk, lty, targs, name_opt, sk2, e, sk3))
      | Ast.Ident_rename(sk1,target_opt,id,sk2,xl') ->        
          let l' = Ast.xl_to_l xl' in
          let n' = Name.from_x xl' in 
          let env = ctxt.cur_env in
          let id' = Ident.from_id id in
          let p = lookup_name env id in
             (ctxt,
             (Ident_rename(sk1, check_target_opt target_opt,
                     p, id', 
                     sk2, (n', l'))))
      | Ast.Module(sk1,xl, sk2,sk3,Ast.Defs(defs),sk4) ->
          let l' = Ast.xl_to_l xl in
          let n = Name.from_x xl in 
          let n' = Name.strip_lskip n in 
          let ctxt1 = { ctxt with new_defs = empty_env } in
          let (new_ctxt,ds) = 
            check_defs backend_targets (mod_path @ [Name.strip_lskip n]) ctxt1 defs 
          in
          let ctxt2 = 
            { ctxt with all_tdefs = new_ctxt.all_tdefs;
                        new_tdefs = new_ctxt.new_tdefs; 
                        all_instances = new_ctxt.all_instances;
                        new_instances = new_ctxt.new_instances; }
          in
            (add_m_to_ctxt l' ctxt2 n { mod_binding = Path.mk_path mod_path n'; mod_env = new_ctxt.new_defs },
             Module(sk1,(n,l'),sk2,sk3,ds,sk4))
      | Ast.Rename(sk1,xl',sk2,i) ->
          let l' = Ast.xl_to_l xl' in
          let n = Name.from_x xl' in 
          let mod_descr = lookup_mod ctxt.cur_env i in
            (add_m_to_ctxt l' ctxt n mod_descr,
             (Rename(sk1,
                     (n,l'), 
                     sk2,
                     { id_path = Id_some (Ident.from_id i);
                       id_locn = l;
                       descr = mod_descr;
                       instantiation = []; })))
      | Ast.Open(sk,i) -> 
          let mod_descr = lookup_mod ctxt.cur_env i in
          let env = mod_descr.mod_env in
            ({ ctxt with cur_env = env_union ctxt.cur_env env },
             (Open(sk,
                   { id_path = Id_some (Ident.from_id i);
                     id_locn = l;
                     descr = mod_descr;
                     instantiation = []; })))
      | Ast.Indreln(sk, target_opt, clauses) ->
          let module T = struct include T let targets = backend_targets end in
          let module Checker = Make_checker(T) in
          let target_opt_checked = check_target_opt target_opt in
          let target_set = target_opt_to_set target_opt in
          let (cls,e_v,Tconstraints(tnvs,constraints,lconstraints)) = 
            Checker.check_indrels target_set l clauses 
          in 
            (add_let_defs_to_ctxt mod_path ctxt (TNset.elements tnvs) 
               constraints lconstraints
               (target_opt_to_env_tag target_set) None e_v, 
             (Indreln(sk,target_opt_checked,cls)))
      | Ast.Spec_def(val_spec) ->
          let (ctxt,vs) = check_val_spec l mod_path ctxt val_spec in
            (ctxt, Val_spec(vs))
      | Ast.Class(sk1,sk2,xl,tnv,sk4,specs,sk5) ->
          let (tv, _)  = tnvar_to_tnvar2 tnv in
          let l' = Ast.xl_to_l xl in
          let cn = Name.from_x xl in
          let cn' = Name.strip_lskip cn in
          let p = Path.mk_path mod_path cn' in
          let () = 
            match Nfmap.apply ctxt.new_defs.p_env cn' with
              | None -> ()
              | Some(p, _) ->
                  begin
                    match Pfmap.apply ctxt.all_tdefs p with
                      | None -> assert false
                      | Some(Tc_class _) ->
                          raise_error l' "duplicate type class definition" 
                            Name.pp cn'
                      | Some(Tc_type _) ->
                          raise_error l' "type class already defined as a type constructor" 
                            Name.pp cn'
                  end
          in
          let ctxt =
            ctxt_add 
              (fun x -> x.p_env) 
              (fun x y -> { x with p_env = y })
              ctxt 
              (cn', (p, l'))
          in
          let (ctxt',vspecs,methods) = 
            List.fold_left
              (fun (ctxt,vs,methods) (a,b,c,d,l) ->
                 let (tc,ctxt,v) = 
                   check_class_spec l mod_path ctxt p tv 
                     (a,b,c,d)
                 in
                   (ctxt,
                    v::vs,
                    ((Path.get_name tc.const_binding, l), tc.const_type)::methods))
              (ctxt,[],[])
              specs
          in
          let tnvar = tnvar_to_flat tnv in 
          let tnvar' = fst (tnvar_to_types_tnvar tnvar) in
          (* Build a record type for the class's dictionaries *)
          let build_field_name n = 
            Name.rename (fun x -> Ulib.Text.(^^^) x (r"_method")) n 
          in
          let dict_type_name = (Name.lskip_rename (fun x -> Ulib.Text.(^^^) x (r"_class")) cn) in
          let ctxt'' =
            build_type_def_help mod_path ctxt' [tnv] (dict_type_name, l') None None
          in
          let ctxt''' =
            add_record_to_ctxt 
              (fun fname l t ->
                 { field_binding = Path.mk_path mod_path fname;
                   field_tparams = [tnvar'];
                   field_tconstr = Path.mk_path mod_path (Name.strip_lskip dict_type_name);
                   field_arg = t;
                   field_names = List.map (fun ((n,_),_) -> build_field_name n) methods; 
                   field_l = l})
              ctxt''
              (Seplist.from_list (List.map 
                                    (fun ((n,l),t) -> 
                                       (((Name.add_lskip (build_field_name n),l), None, t),None)) 
                                    methods))
          in
          (add_d_to_ctxt ctxt''' p 
             (Tc_class(tnvar', List.map (fun ((n,l), t) -> (n,t)) methods)),
           Class(sk1,sk2,(cn,l'),tnvar, sk4,List.rev vspecs, sk5))
      | Ast.Instance(sk1,Ast.Is(cs,sk2,id,typ,sk3),vals,sk4) ->
          (* TODO: Check for duplicate instances *)
          let (src_cs, tyvars, tnvarset, (sem_cs,sem_rs)) =
            check_constraint_prefix ctxt cs 
          in
          let () = check_free_tvs tnvarset typ in
          let src_t = 
            typ_to_src_t anon_error ignore ignore ctxt.all_tdefs ctxt.cur_env typ
          in
          let (used_tvs, type_path) = check_instance_type_shape ctxt src_t in
          let unused_tvs = TNset.diff tnvarset used_tvs in
          let _ = 
            if not (TNset.is_empty unused_tvs) then
              raise_error l "instance type does not use all type variables"
                TNset.pp unused_tvs
          in
          let (p, tv, methods) = lookup_class_p ctxt id in
          let instance_name = 
            Name.from_rope
              (Ulib.Text.concat (r"_")
                 [r"Instance";
                  Name.to_rope (Path.to_name p);
                  type_path])
          in
          let instance_path = mod_path @ [instance_name] in
          let tmp_all_inst = 
            List.fold_left 
              (fun instances (p, tv) -> 
                 insert_pfmap_list instances p ([], [], tnvar_to_type tv, instance_path)) 
              ctxt.all_instances
              sem_cs
          in
          let tmp_ctxt = 
            { ctxt with all_instances = tmp_all_inst }
          in
          (* TODO: lexical bindings hide class methods *)
          let (e_v,vdefs) = 
            List.fold_left
              (fun (e_v,vs) (v,l) ->
                 let (e_v',v,Tconstraints(tnvs,constraints,lconstraints),_) = 
                   check_val_def backend_targets (Some(src_t.typ)) l tmp_ctxt v 
                 in
                 let _ = assert (constraints = []) in
                 let _ = assert (lconstraints = []) in
                 let _ = assert (TNset.is_empty tnvs) in
                 let new_e_v = 
                    match Nfmap.domains_overlap e_v e_v' with
                      | Some(v) ->
                          let l = 
                            match Nfmap.apply e_v v with
                              | Some(_,l) -> l
                              | _ -> assert false
                          in
                            raise_error l "duplicate definition in an instance" 
                              Name.pp v
                      | None ->
                          Nfmap.union e_v' e_v
                 in
                   (new_e_v, v::vs))
              (Nfmap.empty,[])
              vals
          in
          let _ = 
            List.iter
              (fun (n,t) ->
                 match Nfmap.apply e_v n with
                   | None ->
                       raise_error l "missing class method" Name.pp n
                   | Some(t) ->
                       ())
              methods
          in
          let env = 
            Nfmap.map
              (fun n (t,l) -> 
                 Val({ const_binding = Path.mk_path instance_path n;
                       const_tparams = tyvars;
                       const_class = sem_cs;
                       const_ranges = sem_rs;
                       const_type = t;
                       (* TODO: check the following *)
                       env_tag = K_instance;
                       spec_l = l;
                       substitutions = Targetmap.empty; }))
              e_v
          in
          let sem_info = 
            { inst_env = env;
              inst_name = instance_name;
              inst_class = p;
              inst_tyvars = tyvars;
              inst_constraints = sem_cs;
              inst_methods = methods; }
          in
            (*Format.fprintf Format.std_formatter "%a@\n" pp_env { empty_env with v_env = env};*)
            (add_instance_to_ctxt ctxt p (tyvars, sem_cs, src_t.typ, instance_path),
             Instance(sk1,(src_cs,sk2,Ident.from_id id, src_t, sk3), List.rev vdefs, sk4, 
                      sem_info))


and check_defs (backend_targets : Targetset.t) (mod_path : Name.t list)
              (ctxt : defn_ctxt) defs
              : defn_ctxt * def list =
  match defs with
    | [] -> (ctxt, [])
    | (Ast.Def_l(_,l) as d,sk,semi)::ds ->
        let s = if semi then Some(sk) else None in
          match change_effective_backends backend_targets d with
            | None ->
                let (ctxt,d) = 
                  check_def backend_targets mod_path ctxt d sk semi
                in
                let (ctxt,ds) = check_defs backend_targets mod_path ctxt ds in
                  (ctxt, ((d,s),l)::ds)
            | Some(new_backend_targets) ->
                if Targetset.is_empty new_backend_targets then
                  check_defs backend_targets mod_path ctxt ds
                else
                  let (ctxt,d) = 
                    check_def new_backend_targets mod_path ctxt d sk semi 
                  in
                  let (ctxt,ds) = 
                    check_defs backend_targets mod_path ctxt ds 
                  in
                    (ctxt, ((d,s),l)::ds)

(* Code to check that identifiers in type checked program conform to regular expressions specified in type definitions *)

let check_id_restrict_e ctxt (e : Typed_ast.exp) : Typed_ast.exp option =
 let module C = Exps_in_context(struct let check = None let avoid = None end) in
  match C.exp_to_term e with
  | Var(n) -> let id = Name.to_string (Name.strip_lskip n) in
              let head_norm_type = Types.head_norm ctxt.all_tdefs (exp_to_typ e) in
              begin
              match head_norm_type.t with
                 | Tapp(_,p) -> (match Pfmap.apply ctxt.all_tdefs p with
                    | None | Some(Tc_class _) -> assert false
                    | Some(Tc_type(_,_,None)) -> None
                    | Some(Tc_type(_,_,Some(restrict))) -> 
                       if (Str.string_match (Str.regexp restrict) id 0) 
                         then None
                         else  raise_error (exp_to_locn e) 
                               ("variables with type " ^ t_to_string (exp_to_typ e) ^ " are restricted to names matching the regular expression " ^ restrict)
                               Name.pp (Name.strip_lskip n))
                 | _ -> None
              end
  | _ -> None

let check_id_restrict_p ctxt p = match p.term with
  | P_var(n) -> let id = Name.to_string (Name.strip_lskip n) in
              let head_norm_type = Types.head_norm ctxt.all_tdefs p.typ in
              begin
              match head_norm_type.t with
                 | Tapp(_,path) -> (match Pfmap.apply ctxt.all_tdefs path with
                    | None | Some(Tc_class _) -> assert false
                    | Some(Tc_type(_,_,None)) -> None
                    | Some(Tc_type(_,_,Some(restrict))) -> 
                       if (Str.string_match (Str.regexp restrict) id 0) 
                         then None
                         else  raise_error p.locn 
                               ("variables with type " ^t_to_string p.typ ^ " are restricted to names matching the regular expression " ^ restrict)
                               Name.pp (Name.strip_lskip n) )
                 | _ -> None
              end
  | _ -> None

let rec check_ids env ctxt defs = 
    let module Ctxt = struct let avoid = None let check = None end in
    let module M = Macro_expander.Expander(Ctxt) in
    let emac = (fun env -> (check_id_restrict_e ctxt)) in
    let pmac = (fun env -> fun ppos -> (check_id_restrict_p ctxt)) in
    let defs = M.expand_defs defs
                     (Macro_expander.list_to_mac [(emac env)],
                      (fun ty -> ty),
                      (fun ty -> ty),
                      Macro_expander.list_to_bool_mac []) in
     let _ = M.expand_defs defs
                     (Macro_expander.list_to_mac [],
                      (fun ty -> ty),
                      (fun ty -> ty),
                      Macro_expander.list_to_bool_mac [(pmac env)])
    in ()

(*  List.iter (fun d -> match d with
               | ((Val_def(Let_def(_,_,letbind),tnvs,consts), _),_) -> () (*TODO check in letbind*)
               | ((Val_def(Rec_def(_,_,_,funcdefs),tnvs,consts),_),_) -> () (*TODO check in funcdefs*)
               | ((Module(_,name,_,_,defs,_), _),_) -> check_ids ctxt defs
(*Indreln of lskips * targets_opt * 
               (Name.lskips_t option * lskips * name_lskips_annot list * lskips * exp option * lskips * name_lskips_annot * exp list) lskips_seplist*)
               | ((Indreln(_,_,reltns),_),_) -> () (*TODO check in reltns *)
               | ((Val_spec v,_),_) -> () (* TODO check in v *)
               | ((Class(_,_,_,_,_,spec_list,_),_),_) -> () (*TODO check in spec_list*)
               | _ -> ())
            defs
*)

let check_defs backend_targets mod_path (tdefs, instances) env 
      (Ast.Defs(defs)) =
  let ctxt = { all_tdefs = tdefs;
               new_tdefs = Pfmap.empty;  
               all_instances = instances;
               new_instances = Pfmap.empty;
               cur_env = env;
               new_defs = empty_env;
               lemmata_labels = NameSet.empty }
  in
  let (ctxt,b) = check_defs backend_targets mod_path ctxt defs in
  let _ = List.map Syntactic_tests.check_decidable_equality_def b in
  let _ = List.map Syntactic_tests.check_positivity_condition_def b in
    check_ids env ctxt b;    
    ((ctxt.all_tdefs, ctxt.all_instances, ctxt.new_instances), ctxt.new_defs, b)

