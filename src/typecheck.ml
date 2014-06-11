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
open Typed_ast_syntax
open Target
open Typecheck_ctxt




(* -------------------------------------------------------------------------- *)
(* auxiliary functions                                                        *)
(* -------------------------------------------------------------------------- *)


let r = Ulib.Text.of_latin1

module Refl = struct
  type t = const_descr_ref * Ast.l
  let compare (r1,_) (r2,_) =
    Pervasives.compare r1 r2
end

module ReflSet = Set.Make(Refl)

module DupRefs = Util.Duplicate(ReflSet)
module DupTvs = Util.Duplicate(TNset)



let anon_error l = 
  raise (Reporting_basic.err_type l "anonymous types not permitted here: _")

let check_backend_quote l s =
  let (sl, s) = Util.string_split '.' s in
  Ident.mk_ident_strings sl s


(***************************************)
(* simple translations of Ast-types    *)
(***************************************)

let xl_to_nl (xl : Ast.x_l) : Name.lskips_t * Ast.l = (Name.from_x xl, Ast.xl_to_l xl)

let id_to_identl (id : Ast.id) : (Ident.t * Ast.l) = 
  (Ident.from_id id, match id with | Ast.Id(mp,xl,l) -> l)

let ast_tnvar_to_tnvar (tnvar : Ast.tnvar) : Typed_ast.tnvar =
  match tnvar with
    | (Ast.Avl(Ast.A_l((sk,tv),l))) -> Tn_A(sk,tv,l)
    | (Ast.Nvl(Ast.N_l((sk,nv),l))) -> Tn_N(sk,nv,l)

let tvs_to_set (tvs : (Types.tnvar * Ast.l) list) : TNset.t =
  match DupTvs.duplicates (List.map fst tvs) with
    | DupTvs.Has_dups(tv) ->
        let (tv',l) = 
          List.find (fun (tv',_) -> TNvar.compare tv tv' = 0) tvs
        in
          raise (Reporting_basic.err_type_pp l "duplicate type variable" TNvar.pp tv')
    | DupTvs.No_dups(tvs_set) ->
        tvs_set

(***************************************)
(* target stuff                        *)
(***************************************)

let targets_to_set : Ast.targets -> Targetset.t = function
  | (Ast.Targets_concrete(_,targs,_)) ->
      (List.fold_right
             (fun (t,_) ks -> Targetset.add (ast_target_to_target t) ks)
             targs
             Targetset.empty)
  | (Ast.Targets_neg_concrete(_,targs,_)) ->
      (List.fold_right
             (fun (t,_) ks -> Targetset.remove (ast_target_to_target t) ks)
             targs
             all_targets_non_explicit)
  | (Ast.Targets_non_exec _) ->
      (List.fold_right
             (fun t ks -> Targetset.remove t ks)
             all_targets_only_exec_list
             all_targets_non_explicit)

let targets_opt_to_set_opt = Util.option_map targets_to_set 

let targets_opt_to_set x = Util.option_default Target.all_targets_non_explicit (targets_opt_to_set_opt x)

let check_target_opt : Ast.targets option -> Typed_ast.targets_opt = function
  | None -> Targets_opt_none
  | Some(Ast.Targets_concrete(s1,targs,s2)) -> 
      Targets_opt_concrete(s1,Seplist.from_list targs,s2)
  | Some(Ast.Targets_neg_concrete(s1,targs,s2)) -> 
      Targets_opt_neg_concrete(s1,Seplist.from_list targs,s2)
  | Some(Ast.Targets_non_exec s) -> 
      Targets_opt_non_exec s


(* If a definition is target specific, we only want to check it with regards to
 * the backends that we are both translating to, and that it is for *)
let ast_def_to_target_opt : Ast.def_aux -> Ast.targets option = function
    | Ast.Val_def(Ast.Let_def(_,target_opt,_) |
                  Ast.Let_inline(_,_,target_opt,_) |
                  Ast.Let_transform(_,_,target_opt,_) |
                  Ast.Let_rec(_,_,target_opt,_)) -> target_opt
    | Ast.Indreln(_,target_opt,_,_) -> target_opt
    | Ast.Lemma(Ast.Lemma_named(Ast.Lemma_assert _,None,_,_,_)) -> None
    | Ast.Lemma(Ast.Lemma_named(_,None,_,_,_)) -> Some (Ast.Targets_non_exec None)
    | Ast.Lemma(Ast.Lemma_named(_,Some targets,_,_,_)) -> Some targets
    | Ast.Type_def _ -> None
    | Ast.Declaration _ -> None
    | Ast.Module _ -> None
    | Ast.Open_import _ -> None
    | Ast.Open_import_target(_, target_opt, _) -> target_opt
    | Ast.Spec_def _ -> None
    | Ast.Class _ -> None
    | Ast.Rename _ -> None
    | Ast.Instance _ -> None


(* given the set of backends [backend_targets] Lem is currently generating output for and
   a definition, this function restricts [backend_targets] to the set of targets, this
   definition should be generated for. *)
let get_effective_backends (backend_targets : Targetset.t) def = 
  match (ast_def_to_target_opt def) with 
    | None -> (* definition is defined for all targets, so no restriction *) backend_targets
    | Some targets -> (Targetset.inter (targets_to_set targets) backend_targets)
;;


(***************************************)
(* lexing environments                 *)
(***************************************)

(* Non-top level binders map to a type, not a type scheme, method or constructor 
   lex_env is used to map these local binders (in patterns or expressions) to
   their first location and their type. *) 

type lex_env = (Types.t * Ast.l) Nfmap.t
let empty_lex_env = Nfmap.empty

(** [annot_name n l env] looks up the type of name [n] in lex-environment [env] and
    constructs an annotated name with type-information. It fails, if [n] is not present in [env]. *)
let annot_name (n : Name.lskips_t) (l : Ast.l) (env : lex_env) : name_lskips_annot = 
  { term = n;
    locn = l;
    typ = 
      begin
        match Nfmap.apply env (Name.strip_lskip n) with
          | Some((x,l)) -> x 
          | None -> raise (Reporting_basic.err_general true l "invariant in annotating names broken, name not present in environment")
      end;
    rest = (); }


let add_binding (lex_e : lex_env) ((v : Name.lskips_t), (l : Ast.l)) (t : t) : lex_env =
  if Nfmap.in_dom (Name.strip_lskip v) lex_e then
    raise (Reporting_basic.err_type_pp l "duplicate binding" Name.pp (Name.strip_lskip v))
  else
    Nfmap.insert lex_e (Name.strip_lskip v,(t,l))


(*****************************************)
(* looking up names in local environment *)
(*****************************************)

(* Assume that the names in mp must refer to modules.  Corresponds to judgment
 * look_m 'E1(x1..xn) gives E2' *)
let rec path_lookup l (e : env) (mp : (Name.lskips_t * Ast.l) list) : local_env =   
  let mp_names = List.map (fun (n, _) -> Name.strip_lskip n) mp in
  match lookup_env_opt e mp_names with
    | Some lenv -> lenv
    | None -> 
      let mp_rev = List.rev mp_names in
      let p = Path.mk_path (List.rev (List.tl mp_rev)) (List.hd mp_rev) in
      raise (Reporting_basic.err_type_pp l "unknown module" Path.pp p)

(* Assume that the names in mp must refer to modules. Corresponds to judgment
 * look_m_id 'E1(id) gives E2' *)
let lookup_mod (e : env) (Ast.Id(mp,xl,l'')) : mod_descr = 
  let mp' = List.map (fun (xl,_) -> Name.strip_lskip (Name.from_x xl)) mp in
  let n = Name.strip_lskip (Name.from_x xl) in 
  match lookup_mod_descr_opt e mp' n with
      | None -> 
          raise (Reporting_basic.err_type_pp (Ast.xl_to_l xl) "unknown module"
            Name.pp (Name.strip_lskip (Name.from_x xl)))
      | Some(e) -> e

(* Assume that the names in mp must refer to modules. Corresponds to judgment
 * look_tc 'E(id) gives p' *)
let lookup_p msg (env : env) (Ast.Id(mp,xl,l) as i) : Path.t =
  let e = path_lookup l env (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
    match Nfmap.apply e.p_env (Name.strip_lskip (Name.from_x xl)) with
      | None ->
          raise (Reporting_basic.err_type_pp l (Printf.sprintf "unbound type%s" msg)
            Ident.pp (Ident.from_id i))
      | Some(p, _) -> p

(* Assume that the names in mp must refer to modules. Looks up a name, not
   knowing what this name refers to. It might be a type, a constant, a module ... *)
let lookup_name (e : env) (comp_opt : Ast.component option) (Ast.Id(mp,xl,l) as i) : (name_kind * Path.t) =
  let e_l = path_lookup l e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
  let e = {e with local_env = e_l} in
    match env_apply e comp_opt (Name.strip_lskip (Name.from_x xl)) with
      | None ->
          raise (Reporting_basic.err_type_pp l (Printf.sprintf "unbound name")
            Ident.pp (Ident.from_id i))
      | Some(nk, p, _) -> (nk, p)


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


(* Finds a type class's path, and its methods, in the current enviroment, given
 * its name. *)
let lookup_class_p (env : env) (id : Ast.id) : Path.t * class_descr = 
  let p = lookup_p " class" env id in
    match Pfmap.apply env.t_env p with
      | None -> raise (Reporting_basic.err_general true Ast.Unknown "invariant in finding type class path broken")
      | Some(Tc_class d) -> (p, d)
      | Some(Tc_type _) ->
          raise (Reporting_basic.err_type_pp (match id with Ast.Id(_,_,l) -> l)
            "type constructor used as type class" Ident.pp (Ident.from_id id))



(* -------------------------------------------------------------------------- *)
(* checking types                                                             *)
(* -------------------------------------------------------------------------- *)

(* Checks the well-formedness of a type that appears in the source.  Corresponds
 * to judgment convert_typ 'Delta, E |- typ ~> t'.  The wild_f function is used
 * for an underscore/wildcard type (which should be allowed in type annotations,
 * but not in type definitions).  The do_tvar function is called on each type
 * variable in the type, for its side effect (e.g., to record the tvars that
 * occur in the type). 
 *)

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
     raise (Reporting_basic.err_type_pp l (Printf.sprintf "type constructor expected type argument, given a length")
         Ident.pp (Ident.from_id i))
     (* TODO KG: Improve this type error location and add variable name *)
   | Nv _ , _ -> 
     raise (Reporting_basic.err_type_pp l (Printf.sprintf "type constructor expected length argument, given a type")
         Ident.pp (Ident.from_id i))
   | Ty _ , _ -> ()

let check_backend_allowed allowed l =
    if allowed then () else
    raise (Reporting_basic.err_type l "backend-quotation not permitted here")

let rec typ_to_src_t backend_quot_allowed (wild_f : Ast.l -> lskips -> src_t) 
      (do_tvar : Tyvar.t -> unit) (do_nvar : Nvar.t -> unit) (e : env) (Ast.Typ_l(typ,l)) 
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
        let st1 = typ_to_src_t backend_quot_allowed wild_f do_tvar do_nvar e typ1 in
        let st2 = typ_to_src_t backend_quot_allowed wild_f do_tvar do_nvar e typ2 in
          { term = Typ_fn(st1, sk, st2);
            locn = l; 
            typ = { t = Tfn(st1.typ,st2.typ) };
            rest = (); }
    | Ast.Typ_tup(typs) ->
        let typs = Seplist.from_list typs in
        let sts = Seplist.map (typ_to_src_t backend_quot_allowed wild_f do_tvar do_nvar e) typs in
          { term = Typ_tup(sts); 
            locn = l; 
            typ = { t = Ttup(Seplist.to_list_map annot_to_typ sts) };
            rest = (); }
    | Ast.Typ_app(i,typs) ->
        let p = lookup_p " constructor" e i in
          begin
            match Pfmap.apply e.t_env p with
              | None ->
                  raise (Reporting_basic.err_general true l "invariant in checking type application broken")
              | Some(Tc_type(td)) ->
                  if List.length td.type_tparams = List.length typs then
                    let sts = 
                      List.map (typ_to_src_t backend_quot_allowed wild_f do_tvar do_nvar e) typs 
                    in
                    let id = {id_path = Id_some (Ident.from_id i); 
                              id_locn = (match i with Ast.Id(_,_,l) -> l);
                              descr = p;
                              instantiation = []; }
                    in
		      (List.iter2 (tnvar_app_check l i) td.type_tparams sts);
                      { term = Typ_app(id,sts);
                        locn = l;
                        typ = { t = Tapp(List.map annot_to_typ sts,p) };
                        rest = (); }
                  else
                    raise (Reporting_basic.err_type_pp l (Printf.sprintf "type constructor expected %d type arguments, given %d" 
                                   (List.length td.type_tparams)
                                   (List.length typs))
                      Ident.pp (Ident.from_id i))
              | Some(Tc_class _) ->
                  raise (Reporting_basic.err_type_pp l "type class used as type constructor" 
                    Ident.pp (Ident.from_id i))
          end
    | Ast.Typ_backend(sk,q,typs) ->
        let _ = check_backend_allowed backend_quot_allowed l in
        let i = Ident.replace_lskip (check_backend_quote l q) sk in
        let p = Path.from_id i in
        let sts = List.map (typ_to_src_t backend_quot_allowed wild_f do_tvar do_nvar e) typs in
        let id = {id_path = Id_some i; 
                  id_locn = l;
                  descr = p;
                  instantiation = []; }
        in
          { term = Typ_backend(id,sts);
            locn = l;
            typ = { t = Tbackend(List.map annot_to_typ sts,p) };
            rest = (); }
    | Ast.Typ_paren(sk1,typ,sk2) ->
        let st = typ_to_src_t backend_quot_allowed wild_f do_tvar do_nvar e typ in
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

(*Permits only in, out, and the type of the witness, and enforces that it otherwise matches the relation type *)

(* It's easier if we realise that there are two very distinct cases :
  - either we are in the "spine" composed of in, out, ...
  - or we are in the last part, containing extra information
*)
let typ_to_src_t_indreln wit (d : type_defs) (e : env) (typt : Types.t) typ : src_t =
  let dest_id (Ast.Id(path,xl,l0) as i) =
    let n = Name.strip_lskip (Name.from_x xl) in
    (Name.to_string n,
     {id_path = Id_some (Ident.from_id i);
      id_locn = l0;
      descr = Path.mk_path [] n;
      instantiation = []; })
  in
  let rec compare_spine typt (Ast.Typ_l(typ,l) as typ') =
    match typt.t, typ with
      | Tfn(t1,t2), Ast.Typ_fn(typ1, sk, typ2) -> 
        let st1 = compare_io t1 typ1 in
        let st2 = compare_spine t2 typ2 in
        { term = Typ_fn(st1, sk, st2);
          locn = l;
          typ = { t = Tfn(st1.typ, st2.typ) };
          rest = (); }
      | Tfn(_,{t=Tfn(_,_)}), _ ->
        raise (Reporting_basic.err_type l "Too few arguments in indrel function specification (expecting an arrow here)")
      | Tfn(t1, _t2), _ -> compare_io t1 typ' (* _t2 is assumed to be bool *)
      | _ -> compare_end typt typ'
  and compare_io _ (Ast.Typ_l(typ,l)) = 
    match typ with
      | Ast.Typ_app(i, []) ->
        let n, id = dest_id i in
        let p = Path.mk_path [] (Name.from_string n) in
        if n = "input" || n = "output"
        then { term = Typ_app(id, []);
               locn = l;
               typ = { t = Tapp([], p) };
               rest = (); }
        else raise (Reporting_basic.err_type l "Only input or output may be used here") 
      | _ -> raise (Reporting_basic.err_type l "Only input or output may be used here")
  and compare_wu (Ast.Typ_l(typ,l)) =
      match typ with
      | Ast.Typ_app(i, []) -> 
        let n, id = dest_id i in
        let p = lookup_p " constructor" e i in
        begin match wit with
          | _ when Path.compare p Path.unitpath = 0 -> ()
          | Some(wit_p) when Path.compare p wit_p = 0 -> ()
          | _ -> raise (Reporting_basic.err_type_pp l "Expected unit or the witness" Path.pp p)
        end;
        { term = Typ_app({id with descr = p},[]);
          locn = l;
          typ = { t = Tapp([],p) };
          rest = (); }
      | _ -> raise (Reporting_basic.err_type l "Expected unit or the witness")
  and compare_end _ (Ast.Typ_l(typ,l) as typ') = 
   (* The other type should be bool, we don't check that *) 
   try compare_wu typ' 
    with _ -> 
      match typ with
        | Ast.Typ_app(i, (([] | [_]) as typs)) ->
          begin match dest_id i with
            | ("list"|"unique"|"pure"|"option") as n , id ->
              let sub = List.map compare_wu typs in
              { term = Typ_app(id, sub);
                locn = l;
                typ = { t = Tapp(List.map (fun x -> x.typ) sub, 
                                 Path.mk_path [] (Name.from_string n)) }; 
                rest = (); }
            | _ -> raise (Reporting_basic.err_type l "Expected list, unique, pure, option, unit or witness")
          end
        | _ -> raise (Reporting_basic.err_type l "Expected list, unique, pure, option, unit or witness")
  in
  compare_spine typt typ


(* -------------------------------------------------------------------------- *)
(* checking constraints                                                       *)
(* -------------------------------------------------------------------------- *)

(* Process the "forall 'a. (C 'a) =>" part of a type,  Returns the bound
 * variables both as a list and as a set *)
let check_constraint_prefix (ctxt : defn_ctxt) 
      : Ast.c_pre -> 
        constraint_prefix option * 
        Types.tnvar list * 
        TNset.t * 
        ((Path.t * Types.tnvar) list * Types.range list) = 
begin
  let check_class_constraints c env =
   List.fold_right 
    (fun (Ast.C(id, tnv),sk) result ->
    let tnv' = ast_tnvar_to_tnvar tnv in
    let (tnv'',l) = tnvar_to_types_tnvar tnv' in
    let (p,_) = lookup_class_p (defn_ctxt_to_env ctxt) id in
    begin
      match (Pfmap.apply ctxt.all_tdefs p) with
        | (None | Some (Tc_type _)) -> raise (Reporting_basic.err_unreachable l "not a class constraint")
        | Some (Tc_class cd) -> if cd.class_is_inline then
            raise (Reporting_basic.err_type_pp l "inline class used as explicit constraint" Types.pp_class_constraint (p,tnv''))
    end;
    begin
      if TNset.mem tnv'' env then
         ()
      else
         raise (Reporting_basic.err_type_pp l "unbound type variable" pp_tnvar tnv'')
    end;
    begin
      if List.mem (p, tnv'') (List.map snd result) then 
         raise (Reporting_basic.err_type_pp l "duplicate constraint" Types.pp_class_constraint (p,tnv''))
      else ()
    end;
      ((((Ident.from_id id, tnv'), sk),
       (p, tnv'')) :: result))
    c []
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
        let tnvars = List.map ast_tnvar_to_tnvar tvs in
        let tnvars_types = List.map tnvar_to_types_tnvar tnvars in
          (Some(Cp_forall(sk1, 
                          tnvars, 
                          sk2, 
                          None)),  
           List.map fst tnvars_types,
           tvs_to_set tnvars_types,
           ([],[]))
    | Ast.C_pre_forall(sk1,tvs,sk2,crs) ->
        let tnvars = List.map ast_tnvar_to_tnvar tvs in
        let tnvars_types = List.map tnvar_to_types_tnvar tnvars in
        let tnvarset = tvs_to_set tnvars_types in
        let (c,sk3,r,sk4) = match crs with 
                             | Ast.Cs_empty ->
                                raise (Reporting_basic.err_general true Ast.Unknown "invariant in checking checking range constraints broken")
                             | Ast.Cs_classes(c,sk3) -> c,None,[],sk3
                             | Ast.Cs_lengths(r,sk3) -> [], None, r, sk3
                             | Ast.Cs_both(c,sk3,r,sk4) -> c, Some sk3, r, sk4 in
        let (constraints_tast, constraints) = 
          let cs = check_class_constraints c tnvarset in
          let rs = check_range_constraints r tnvarset in
            (Cs_list(Seplist.from_list (List.map fst cs),sk3,Seplist.from_list (List.map fst rs),sk4), (List.map snd cs, List.map snd rs)) 
        in
          (Some(Cp_forall(sk1, 
                          tnvars, 
                          sk2, 
                          Some(constraints_tast))),
           List.map fst tnvars_types,
           tnvarset,
           constraints)
end


(** [unsat_class_constraint_err m l cs] skips, if [cs] is empty, otherwise, it throws a type-error exception, with
     message [m] and the pretty printed class-constraints [cs]. *)
let check_class_constraints_err m l = function
  | [] -> ()
  | cs ->
      let t1 = 
        Pp.pp_to_string 
          (fun ppf -> 
             (Pp.lst "@\n  and@\n    " pp_class_constraint) ppf cs)
      in
        raise (Reporting_basic.err_type l (m ^ ":\n    " ^ t1))


let unsat_constraint_err l cs = 
  let m = Util.message_singular_plural ("constraint", "constraints") cs in
  check_class_constraints_err ("unsatisfied type class " ^ m) l cs

(* checks, whether [cs1] is a subset of [cs2] and raises an exception, if this is not the case. *)
let check_constraint_subset l cs1 cs2 = 
  unsat_constraint_err l
    (List.filter
       (fun (p,tv) ->
          not (List.exists 
                 (fun (p',tv') -> 
                    Path.compare p p' = 0 && tnvar_compare tv tv' = 0)
                 cs2))
       cs1)

(* checks, whether [cs] contains no inline contraints *)
let check_constraint_no_inline l env cs = 
  let cs' =  
    (List.filter
       (fun (p,_) ->
          match (Pfmap.apply env.t_env p) with
            | (None | Some (Tc_type _)) -> raise (Reporting_basic.err_unreachable l "not a class constraint")
            | Some (Tc_class cd) -> cd.class_is_inline)
       cs) in
  let m = Util.message_singular_plural ("constraint", "constraints") cs' in
  check_class_constraints_err ("unresolved inlined class constraint " ^ m) l cs'





(* -------------------------------------------------------------------------- *)
(* sanity checks                                                              *)
(* -------------------------------------------------------------------------- *)

let check_dup_field_names (c_env : c_env) (fns : (const_descr_ref * Ast.l) list) : unit = 
  match DupRefs.duplicates fns with
    | DupRefs.Has_dups(f, l) ->
        let fd = c_env_lookup l c_env f in
        let n = Path.get_name fd.const_binding in
        raise (Reporting_basic.err_type_pp l "duplicate field name" 
          (fun fmt x -> Format.fprintf fmt "%a" Name.pp x)
          n)
    | _ -> ()


(* Ensures that a monad operator is bound to a value constant that has no
 * class or length constraints and that has no length type parameters *)
let check_const_for_do (mid : Path.t id) (c_env : c_env) (v_env : v_env) (name : string) : 
  Tyvar.t list * t =
  let error_path = mid.descr in    
    match Nfmap.apply v_env (Name.from_rope (r name)) with
      | None ->
          raise (Reporting_basic.err_type_pp mid.id_locn (Printf.sprintf "monad module missing %s" name)
            Path.pp error_path)
      | Some(c) ->
          let c_d = c_env_lookup mid.id_locn c_env c in


          (* no constructors ... *)
          let _ = match c_d.env_tag with 
            | K_constr -> 
                 raise (Reporting_basic.err_type_pp  mid.id_locn (Printf.sprintf "monad module %s bound to constructor" name)
                    Path.pp error_path)
            | _ -> ()
          in

          if c_d.const_class <> [] then
            raise (Reporting_basic.err_type_pp mid.id_locn (Printf.sprintf "monad operator %s has class constraints" name) 
              Path.pp error_path)
          else if c_d.const_ranges <> [] then
            raise (Reporting_basic.err_type_pp mid.id_locn (Printf.sprintf "monad operator %s has length constraints" name) 
              Path.pp error_path)
          else
            (List.map
               (function 
                 | Nv _ -> 
                     raise (Reporting_basic.err_type_pp mid.id_locn (Printf.sprintf "monad operator %s has length variable type parameters" name) 
                       Path.pp error_path)
                 | Ty(v) -> v)
               c_d.const_tparams,
             c_d.const_type)

let rec check_free_tvs (tvs : TNset.t) (Ast.Typ_l(t,l)) : unit =
  match t with
    | Ast.Typ_wild _ ->
        anon_error l
    | Ast.Typ_var(Ast.A_l((t,x),l)) ->
       if TNset.mem (Ty (Tyvar.from_rope x)) tvs then
        ()
       else
        raise (Reporting_basic.err_type_pp l "unbound type variable" 
          Tyvar.pp (Tyvar.from_rope x))
    | Ast.Typ_fn(t1,_,t2) -> 
        check_free_tvs tvs t1; check_free_tvs tvs t2
    | Ast.Typ_tup(ts) -> 
        List.iter (check_free_tvs tvs) (List.map fst ts)
    | Ast.Typ_Nexps(n) -> check_free_ns tvs n
    | (Ast.Typ_app(_,ts) | Ast.Typ_backend (_, _, ts)) -> 
        List.iter (check_free_tvs tvs) ts
    | Ast.Typ_paren(_,t,_) -> 
        check_free_tvs tvs t

and check_free_ns (nvs: TNset.t) (Ast.Length_l(nexp,l)) : unit =
  match nexp with
   | Ast.Nexp_var((_,x)) ->
       if TNset.mem (Nv (Nvar.from_rope x)) nvs then
        ()
       else
        raise (Reporting_basic.err_type_pp l "unbound length variable" Nvar.pp (Nvar.from_rope x))
   | Ast.Nexp_constant _ -> ()
   | Ast.Nexp_sum(n1,_,n2) | Ast.Nexp_times(n1,_,n2) -> check_free_ns nvs n1 ; check_free_ns nvs n2
   | Ast.Nexp_paren(_,n,_) -> check_free_ns nvs n

(* [check_free_tvs_exp tvs e] check that all the type-variables used in expression [e]
   are part of the set [tvs]. If not, an appropriate type-error is raised. *)
let check_free_tvs_exp l (tvs : TNset.t) e : unit =
  let free_tnvars = (add_exp_entities empty_used_entities e).used_tnvars in
  let unbound_tnvars = TNset.diff free_tnvars tvs in
  if (TNset.is_empty unbound_tnvars) then () else begin
     raise (Reporting_basic.err_type_pp l "unbound type variables"
               (Pp.lst ";" Types.pp_tnvar) (TNset.elements unbound_tnvars))
  end

let check_free_tvs_letbind (lb : Typed_ast.letbind) : unit =
  match lb with
    | (Let_val(pat,_,_,exp), l) ->
        check_free_tvs_exp l (Types.free_vars pat.typ) exp
    | (Let_fun (na, _, _, _, exp), l) ->
        check_free_tvs_exp l (Types.free_vars (annot_to_typ na)) exp


(* -------------------------------------------------------------------------- *)
(* expression checking                                                        *)
(* -------------------------------------------------------------------------- *)

(* We split the environment between top-level and lexically nested binders, and
 * inside of expressions, only the lexical environment can be extended, we
 * parameterize the entire expression-level checking apparatus over the
 * top-level environment.  This contrasts with the formal type system where
 * Delta and E get passed around.  The Make_checker functor also instantiates
 * the state for type inference, so checking of different expressions doesn't
 * interfere with each other.  We also imperatively collect class constraints
 * instead of passing them around as the formal type system does *)

module type Expr_checker = sig
  val check_lem_exp : lex_env -> Ast.l -> Ast.exp -> Types.t option -> (exp * typ_constraints)

  val check_letbind : 
    (* Should be None, unless checking a method definition in an instance.  Then
     * it should contain the type that the instance is at.  In this case the
     * returned constraints and type variables must be empty. *)
    t option ->
    bool (* is it an inline letbind? *) ->
    (* The set of targets that this definition is for *)
    Targetset.t option ->
    Ast.l ->
    Ast.letbind -> 
    letbind * 
    (* The types of the bindings *)
    lex_env * 
    (* The type variabes, and class constraints on them used in typechecking the
     * let binding.  Must be empty when the optional type argument is Some *)
    typ_constraints

  (* As in the comments on check letbind above *)
  val check_funs : 
    t option ->
    Targetset.t option ->
    Ast.l ->
    Ast.funcl lskips_seplist -> 
    (name_lskips_annot * pat list * (lskips * src_t) option * lskips * exp) lskips_seplist * 
    lex_env * 
    typ_constraints

  (* As in the comments on check letbind above, but cannot be an instance
   * method definition *)
  val check_indrels : 
    defn_ctxt ->
    Name.t list -> 
    Targetset.t option ->
    Ast.l ->
    (Ast.indreln_name * lskips) list ->
    (Ast.rule * lskips) list -> 
    indreln_name lskips_seplist *
    indreln_rule lskips_seplist * 
    lex_env *
    typ_constraints

end


(* -------------------------------------------------------------------------- *)
(* disambigate fields ids and general ids                                     *)
(* -------------------------------------------------------------------------- *)

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
            Nfmap.apply env.local_env.f_env n = None 
          else 
            (Nfmap.apply env.local_env.v_env n = None &&
             (match check_le with 
                | None -> true 
                | Some(le) -> Nfmap.apply le n = None))
        in
        let id = Ast.Id(List.rev prefix_acc,xl,l_add) in
          if unbound then
            raise (Reporting_basic.err_type_pp (Ast.xl_to_l xl) 
              (if for_field then "unbound field name" else "unbound variable")
              Ident.pp (Ident.from_id id))
          else
            (id, None)
    | (xl',sk)::mp' ->
        let n = Name.strip_lskip (Name.from_x xl') in
        let unbound = 
          if for_field then 
            Nfmap.apply env.local_env.f_env n = None 
          else 
            (Nfmap.apply env.local_env.v_env n = None &&
             (match check_le with 
                | None -> true 
                | Some(le) -> Nfmap.apply le n = None))
        in
        let id = Ast.Id(List.rev prefix_acc,xl',l_add) in
          if unbound then
            begin
              let mp_opt = Nfmap.apply env.local_env.m_env n in
              let md_opt = Util.option_bind (Pfmap.apply env.e_env) mp_opt in
              match md_opt with
                | None ->
                    raise (Reporting_basic.err_type_pp (Ast.xl_to_l xl') 
                      ("unbound module name or " ^
                       if for_field then "field name" else "variable")
                      Ident.pp (Ident.from_id id))
                | Some(md) ->
                    get_id_mod_prefix for_field None {env with local_env = md.mod_env}
                      (Ast.Id(mp',xl,l_add)) 
                      ((xl',sk)::prefix_acc)
            end
          else
            (id, Some(sk,Ast.Id(mp',xl,l_add)))


(* Chop up an identifier into a list of record projections.  Each projection
 * can be an identifier with a non-empty module path *)
let rec disambiguate_projections sk (env : env) (id : Ast.id) 
      : (Ast.lex_skips * Ast.id) list =
  match get_id_mod_prefix true None env id [] with
    | (id,None) -> [(sk,id)]
    | (id1,Some(sk',id2)) -> (sk,id1)::disambiguate_projections sk' env id2

(* Figures out which '.'s in an identifier are actually record projections.
 * This is ambiguous in the source since field names can be '.' separated
 * module paths *)
let disambiguate_id (le : lex_env) (env : env) (id : Ast.id) 
      : Ast.id * (Ast.lex_skips * Ast.id) list =
  match get_id_mod_prefix false (Some(le)) env id [] with
    | (id,None) -> (id, [])
    | (id1,Some(sk,id2)) ->
        (id1, disambiguate_projections sk env id2)



module Make_checker(T : sig 
                      (* The backend targets that each identifier use must be
                       * defined for *)
                      val targets : Targetset.t
                      (* The current top-level environment *)
                      val e : env 
                      (* The environment so-far of the module we're defining *)
                      val new_module_env : local_env

                      (* allow backticked expressions, patterns and types in the checked places *)
                      val allow_backend_quots : bool
                    end) : Expr_checker = struct

  module C = Constraint(struct let d = T.e.t_env let i = T.e.i_env end)
  module A = Exps_in_context(struct let env_opt = None let avoid = None end)


  (* -------------------------------------------------------------------------- *)
  (* checking literals                                                          *)
  (* -------------------------------------------------------------------------- *)

  (* Corresponds to judgment check_lit '|- lit : t' *)
  let check_lit is_pattern t_ret (Ast.Lit_l(lit,l)) =
    let annot (lit : lit_aux) (t : t) : lit = 
      { term = lit; locn = l; typ = t; rest = (); } 
    in 
    match lit with
      | Ast.L_true(sk) -> annot (L_true(sk)) { t = Tapp([], Path.boolpath) }
      | Ast.L_false(sk) -> annot (L_false(sk)) { t = Tapp([], Path.boolpath) }
      | Ast.L_num(sk,i) -> 
          C.add_constraint (External_constants.class_label_to_path "class_numeral") t_ret;
          if is_pattern then C.add_constraint (External_constants.class_label_to_path "class_ord") t_ret else ();
          if is_pattern then C.add_constraint (External_constants.class_label_to_path "class_num_minus") t_ret else ();
          let i_int = try int_of_string i with Failure "int_of_string" ->
            raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax_locn (l, "couldn't parse integer "^i))) in
          annot (L_num(sk,i_int, Some i)) t_ret 
      | Ast.L_string(sk,i) ->
          annot (L_string(sk, Util.unescaped i, Some i)) { t = Tapp([], Path.stringpath) }
      | Ast.L_char(sk,i) ->
          annot (L_char(sk,String.get (Util.unescaped i) 0, Some i)) { t = Tapp([], Path.charpath) }
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
        : (const_descr_ref id * Types.t) * Ast.l =
    let env = path_lookup l T.e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
    match Nfmap.apply env.f_env (Name.strip_lskip (Name.from_x xl)) with
        | None ->
            begin
              match Nfmap.apply env.v_env (Name.strip_lskip (Name.from_x xl)) with
                | None ->
                    raise (Reporting_basic.err_type_pp l "unbound field name" 
                      Ident.pp (Ident.from_id i))
                | Some(c) ->
                    let c_d = c_env_lookup l T.e.c_env c in
                    if c_d.env_tag = K_method then
                      raise (Reporting_basic.err_type_pp l "method name used as a field name"
                        Ident.pp (Ident.from_id i))
                    else if c_d.env_tag = K_constr then
                      raise (Reporting_basic.err_type_pp l "constructor name used as a field name"
                      Ident.pp (Ident.from_id i))
                    else
                      raise (Reporting_basic.err_type_pp l "top level variable binding used as a field name"
                        Ident.pp (Ident.from_id i))
            end
        | Some(f) ->
          begin
            let id_l = id_to_identl i in
            let (f_field_arg, f_tconstr, f_d) = dest_field_types l T.e f in
            let new_id = make_new_id id_l f_d.const_tparams f in
            let trec = { t = Tapp(new_id.instantiation,f_tconstr) } in
            let subst = 
              TNfmap.from_list2 f_d.const_tparams new_id.instantiation 
            in
            let tfield = type_subst subst f_field_arg in
            let t = { t = Tfn(trec, tfield) } in
            let a = C.new_type () in
              C.equate_types new_id.id_locn "field expression 1" a t;
              ((new_id, a), l)
          end

  (* Instantiates a top-level constant descriptor with fresh type variables,
   * also calculates its type.  Corresponds to judgment inst_val 'Delta,E |- val
   * id : t gives Sigma', except that that also looks up the descriptor. Moreover,
   * it computes the number of arguments this constant expects *)
  let inst_const id_l (env : env) (c : const_descr_ref) : const_descr_ref id * t =
    let cd = c_env_lookup (snd id_l) env.c_env c in
    let new_id = make_new_id id_l cd.const_tparams c in
    let subst = TNfmap.from_list2 cd.const_tparams new_id.instantiation in
    let t = type_subst subst cd.const_type in
    let a = C.new_type () in
      C.equate_types new_id.id_locn "constant use" a t;
      List.iter 
        (fun (p, tv) -> 
           C.add_constraint p (type_subst subst (tnvar_to_type tv))) 
        cd.const_class;
      List.iter
         (fun r -> C.add_length_constraint (range_with r (nexp_subst subst (range_of_n r)))) 
         cd.const_ranges;
      (new_id, a)

  let build_wild l sk =
    { term = Typ_wild(sk); locn = l; typ = C.new_type (); rest = (); }

  (* Corresponds to judgment check_pat 'Delta,E,E_l1 |- pat : t gives E_l2' *)
  let rec check_pat (l_e : lex_env) (Ast.Pat_l(p,l)) (acc : lex_env) 
        : pat * lex_env = 
    let ret_type = C.new_type () in
    let rt = Some(ret_type) in
      match p with
        | Ast.P_wild(sk) -> 
            let a = C.new_type () in
              C.equate_types l "underscore pattern" ret_type a;
              (A.mk_pwild l sk ret_type, acc)
        | Ast.P_as(s1,p, s2, xl,s3) -> 
            let nl = xl_to_nl xl in
            let (pat,pat_e) = check_pat l_e p acc in
            let ax = C.new_type () in
              C.equate_types (snd nl) "as pattern" ax pat.typ;
              C.equate_types l "as pattern" pat.typ ret_type;
              (A.mk_pas l s1 pat s2 nl s3 rt, add_binding pat_e nl ax)
        | Ast.P_typ(sk1,p,sk2,typ,sk3) ->
            let (pat,pat_e) = check_pat l_e p acc in
            let src_t = 
              typ_to_src_t T.allow_backend_quots build_wild C.add_tyvar C.add_nvar T.e typ
            in
              C.equate_types l "type-annotated pattern" src_t.typ pat.typ;
              C.equate_types l "type-annotated pattern" src_t.typ ret_type;
              (A.mk_ptyp l sk1 pat sk2 src_t sk3 rt, pat_e)
        | Ast.P_app(Ast.Id(mp,xl,l'') as i, ps) ->
            let l' = Ast.xl_to_l xl in
            let e = path_lookup l' T.e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
            let const_lookup_res = Nfmap.apply e.v_env (Name.strip_lskip (Name.from_x xl)) in

            (** Try to handle it as a construtor, if success, then return Some, otherwise None
                and handle as variable *)
            let constr_res_opt = begin
                match const_lookup_res with
                   | Some(c) when (lookup_l l_e mp (Name.from_x xl) = None) ->
                      (* i is bound to a constructor that is not lexically
                       * shadowed, this corresponds to the
                       * check_pat_aux_ident_constr case *)

                      let cd = c_env_lookup (snd (id_to_identl i)) T.e.c_env c in
                      let (arg_ts, base_t) = Types.strip_fn_type (Some T.e.t_env) cd.const_type in
                      let is_constr = Pattern_syntax.is_constructor l' T.e Target.Target_ident c in
                      let (pats,pat_e) = check_pats l_e acc ps in
                        if (List.length pats <> List.length arg_ts) || (not is_constr) then (
                          if (List.length pats == 0) then (*handle as var*) None else
                          raise (Reporting_basic.err_type_pp l' 
                             (if is_constr then
                               (Printf.sprintf "constructor pattern expected %d arguments, given %d"
                                 (List.length arg_ts) (List.length pats)) 
                              else "non-constructor pattern given arguments")
                            Ident.pp (Ident.from_id i))
                        ) else (
                          let (id,t) = inst_const (id_to_identl i) T.e c in
                          C.equate_types l'' "constructor pattern" t 
                            (multi_fun (List.map annot_to_typ pats) ret_type);
                          Some (A.mk_pconst l id pats rt, pat_e)
                        )
                   | _ -> None
              end in
            begin 
                match constr_res_opt with 
                   | Some res -> res 
                   | None -> begin
                      (* the check_pat_aux_var case *)
                      match mp with
                        | [] ->
                            if ps <> [] then
                              raise (Reporting_basic.err_type_pp l' "non-constructor pattern given arguments" 
                                Ident.pp (Ident.from_id i))
                            else
                              let ax = C.new_type () in
                              let n = Name.from_x xl in
                                C.equate_types l'' "constructor pattern" ret_type ax;
                                (A.mk_pvar l n ret_type, 
                                 add_binding acc (n,l') ax)
                        | _ ->
                            raise (Reporting_basic.err_type_pp l' "non-constructor pattern has a module path" 
                              Ident.pp (Ident.from_id i))
                      end
              end
        | Ast.P_record(sk1,ips,sk2,term_semi,sk3) ->
            let fpats = Seplist.from_list_suffix ips sk2 term_semi in
            let a = C.new_type () in
            let (checked_pats, pat_e) = 
              Seplist.map_acc_left (check_fpat a l_e) acc fpats 
            in
              check_dup_field_names T.e.c_env
                (Seplist.to_list_map snd checked_pats);
              C.equate_types l "record pattern" a ret_type;
              (A.mk_precord l sk1 (Seplist.map fst checked_pats) sk3 rt,
               pat_e)
        | Ast.P_tup(sk1,ps,sk2) -> 
            let pats = Seplist.from_list ps in
            let (pats,pat_e) = 
              Seplist.map_acc_left (check_pat l_e) acc pats
            in
              C.equate_types l "tuple pattern" ret_type 
                { t = Ttup(Seplist.to_list_map annot_to_typ pats) };
              (A.mk_ptup l sk1 pats sk2 rt, pat_e)
        | Ast.P_list(sk1,ps,sk2,semi,sk3) -> 
            let pats = Seplist.from_list_suffix ps sk2 semi in
            let (pats,pat_e) = 
              Seplist.map_acc_left (check_pat l_e) acc pats
            in
            let a = C.new_type () in
              Seplist.iter (fun pat -> C.equate_types l "list pattern" a pat.typ) pats;
              C.equate_types l "list pattern" ret_type { t = Tapp([a], Path.listpath) };
              (A.mk_plist l sk1 pats sk3 ret_type, pat_e)
	| Ast.P_vector(sk1,ps,sk2,semi,sk3) -> 
           let pats = Seplist.from_list_suffix ps sk2 semi in
           let (pats,pat_e) = 
             Seplist.map_acc_left (check_pat l_e) acc pats
           in
           let a = C.new_type () in
             Seplist.iter (fun pat -> C.equate_types l "vector pattern" a pat.typ) pats;
             let len = { t = Tne({ nexp = Nconst( Seplist.length pats )} ) } in
             C.equate_types l "vector pattern" ret_type { t = Tapp([a;len], Path.vectorpath) };
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
                                C.equate_types l "vector concatenation pattern" { t = Tapp([a;{t=Tne(c)}],Path.vectorpath) } pat.typ;
                                c::lens) [] pats in
              let len = { t = Tne( nexp_from_list (List.rev lens) ) } in
              C.equate_types l "vector concatenation pattern" ret_type { t = Tapp([a;len],Path.vectorpath) };
              (A.mk_pvectorc l sk1 pats sk2 ret_type, pat_e)
        | Ast.P_paren(sk1,p,sk2) -> 
            let (pat,pat_e) = check_pat l_e p acc in
              C.equate_types l "paren pattern" ret_type pat.typ;
              (A.mk_pparen l sk1 pat sk2 rt, pat_e)
        | Ast.P_cons(p1,sk,p2) ->
            let (pat1,pat_e) = check_pat l_e p1 acc in
            let (pat2,pat_e) = check_pat l_e p2 pat_e in
              C.equate_types l ":: pattern" ret_type { t = Tapp([pat1.typ], Path.listpath) };
              C.equate_types l ":: pattern" ret_type pat2.typ;
              (A.mk_pcons l pat1 sk pat2 rt, pat_e)
        | Ast.P_num_add(xl,sk1,sk2,i) ->
            let nl = xl_to_nl xl in
            let _ = C.add_constraint (External_constants.class_label_to_path "class_numeral") ret_type in
            let _ = C.add_constraint (External_constants.class_label_to_path "class_ord") ret_type in
            let _ = C.add_constraint (External_constants.class_label_to_path "class_num_minus") ret_type in
          (A.mk_pnum_add l nl sk1 sk2 i rt, add_binding acc nl ret_type)
        | Ast.P_lit(lit) ->
            let lit = check_lit true ret_type lit in
              C.equate_types l "literal pattern" ret_type lit.typ;
              (A.mk_plit l lit rt, acc)

  and check_fpat a (l_e : lex_env) (Ast.Fpat(id,sk,p,l)) (acc : lex_env)  
                : (((const_descr_ref id * lskips * pat) * (const_descr_ref * Ast.l)) * lex_env)=
    let (p,acc) = check_pat l_e p acc in
    let ((id,t),l') = check_field id in
      C.equate_types l "field pattern" t { t = Tfn(a,p.typ) };
      (((id,sk,p),(id.descr, l')), acc)

  and check_pats (l_e : lex_env) (acc : lex_env) (ps : Ast.pat list) 
                : pat list * lex_env =
    List.fold_right 
      (fun p (pats,pat_e) -> 
         let (pat,pat_e) = check_pat l_e p pat_e in
           (pat::pats,pat_e))
      ps
      ([],acc) 

  let rec check_all_fields (exp : Typed_ast.exp) 
        (fids : (Ast.lex_skips * Ast.id) list) =
    match fids with
      | [] ->
          exp
      | (sk,fid)::fids ->
          let ((id,t),l) = check_field fid in
          let ret_type = C.new_type () in
            C.equate_types l "field access" t { t = Tfn(exp_to_typ exp, ret_type) };
            check_all_fields (A.mk_field l exp sk id (Some ret_type)) fids

  (* Corresponds to inst_val 'D,E |- val id : t gives S' and the 
  * var and val cases of check_exp_aux *)
  let check_val (l_e : lex_env) (mp : (Ast.x_l * Ast.lex_skips) list) 
        (n : Name.lskips_t) (l : Ast.l) : exp =    
    match lookup_l l_e mp n with
      | Some(t,l,n) -> 
          (* The name is bound to a local variable, so return a variable *)
          A.mk_var l n t
      | None -> 
          (* check whether the name is bound to a constant (excluding fields) *)
          let mp' = List.map (fun (xl,_) -> xl_to_nl xl) mp in
          let e = path_lookup l T.e mp' in
            match Nfmap.apply e.v_env (Name.strip_lskip n) with
              | None    -> 
                  (* not bound to a constant either, so it's unbound *)
                  raise (Reporting_basic.err_type_pp l "unbound variable" Name.pp (Name.strip_lskip n))
              | Some(c) ->
                  (* its bound, but is it bound for the necessary targets? *)
                  let cd = c_env_lookup l T.e.c_env c in
                  let undefined_targets = Targetset.diff T.targets cd.const_targets in
                  if not (Targetset.is_empty undefined_targets) then
                     raise (Reporting_basic.err_type_pp l (Pp.pp_to_string (fun ppf -> 
                        Format.fprintf ppf
                           "unbound variable for targets {%a}"
                           (Pp.lst ";" (fun ppf t -> Pp.pp_str ppf (non_ident_target_to_string t)))
                           (Targetset.elements undefined_targets)
                        )) Name.pp (Name.strip_lskip n))                     
                  else ();

                  (* its bound for all the necessary targets, so lets return the constant *)
                  let mp'' = List.map (fun (xl,skips) -> (Name.from_x xl, skips)) mp in
                  let (id,t) = inst_const (Ident.mk_ident_ast mp'' n l, l) T.e c in
                    C.equate_types l "top-level binding use" t (C.new_type());
                    A.mk_const l id (Some(t))

  let check_id (l_e : lex_env) (Ast.Id(mp,xl,l_add) as id) : exp =
    (* We could type check and disambiguate at the same time, but that would
     * have a more complicated implementation, so we don't *)
    let (Ast.Id(mp,xl,l), fields) = disambiguate_id l_e T.e id in
    let exp = check_val l_e mp (Name.from_x xl) l in
      check_all_fields exp fields

  (* Corresponds to judgment check_exp 'Delta,E,E_ |- exp : t gives Sigma' *)
  let rec check_exp (l_e : lex_env) (Ast.Expr_l(exp,l)) : exp =
    let ret_type = C.new_type () in
    let rt = Some(ret_type) in 
      match exp with
        | Ast.Ident(i) -> 
            let exp = check_id l_e i in
              C.equate_types l "identifier use" ret_type (exp_to_typ exp);
              exp
        | Ast.Backend(sk,s) ->
            let _ = check_backend_allowed T.allow_backend_quots l in
            let id = check_backend_quote l s in
              A.mk_backend l sk id ret_type
        | Ast.Nvar((sk,n)) -> 
            let nv = Nvar.from_rope(n) in
            C.add_nvar nv;
            A.mk_nvar_e l sk nv  { t = Tapp([], Path.natpath) }
        | Ast.Fun(sk,pse) -> 
            let (param_pats,sk',body_exp,t) = check_psexp l_e pse in
              C.equate_types l "fun expression" t ret_type;
              A.mk_fun l sk param_pats sk' body_exp rt
        | Ast.Function(sk,bar_sk,bar,pm,end_sk) -> 
            let pm = Seplist.from_list_prefix bar_sk bar pm in
            let res = 
              Seplist.map
                (fun pe ->
                   let (res,t) = check_pexp l_e pe in
                     C.equate_types l "function expression" t ret_type;
                     res)
                pm
            in
              A.mk_function l sk res end_sk rt
        | Ast.App(fn,arg) ->
            let fnexp = check_exp l_e fn in
            let argexp = check_exp l_e arg in
              C.equate_types l "application expression" { t = Tfn(exp_to_typ argexp,ret_type) } (exp_to_typ fnexp);
              A.mk_app l fnexp argexp rt
        | Ast.Infix(e1, xl, e2) ->
            let n = Name.from_ix xl in
            let id = check_val l_e [] n (Ast.ixl_to_l xl) in
            let arg1 = check_exp l_e e1 in
            let arg2 = check_exp l_e e2 in
              C.equate_types l 
                "infix expression"
                { t = Tfn(exp_to_typ arg1, { t = Tfn(exp_to_typ arg2,ret_type) }) }
                (exp_to_typ id);
              A.mk_infix l arg1 id arg2 rt
        | Ast.Record(sk1,r,sk2) ->
            let (res,t,given_fields) = check_fexps l_e r in
            let one_field = match given_fields with [] -> raise (Reporting_basic.err_type l "empty records, no fields given") | f::_ -> f in
            let all_fields = get_field_all_fields l T.e one_field in
            let missing_fields = Util.list_diff all_fields given_fields in
            if (Util.list_longer 0 missing_fields) then
              begin
                  (* get names of missing fields for error message *)
                  let field_get_name f_ref = begin
                     let f_d = c_env_lookup l T.e.c_env f_ref in
                     let f_path = f_d.const_binding in
                     Path.get_name f_path
                  end in
                  let names = List.map field_get_name missing_fields in
                  let names_string = Pp.pp_to_string (fun ppf -> (Pp.lst ", " Name.pp) ppf names) in
                  let message = Printf.sprintf "missing %s: %s" (if Util.list_longer 1 missing_fields then "fields" else "field") names_string in
                  raise (Reporting_basic.err_type l message)
              end;
              C.equate_types l "record expression" t ret_type;
              A.mk_record l sk1 res sk2 rt
        | Ast.Recup(sk1,e,sk2,r,sk3) ->
            let exp = check_exp l_e e in
            let (res,t,_) = check_fexps l_e r in
              C.equate_types l "record update expression" (exp_to_typ exp) t;
              C.equate_types l "record update expression" t ret_type;
              A.mk_recup l sk1 exp sk2 res sk3 rt
        | Ast.Field(e,sk,fid) ->
            let exp = check_exp l_e e in
            let fids = disambiguate_projections sk T.e fid in
            let new_exp = check_all_fields exp fids in
              C.equate_types l "field expression 2" ret_type (exp_to_typ new_exp);
              new_exp
        | Ast.Case(sk1,e,sk2,bar_sk,bar,pm,l',sk3) ->
            let pm = Seplist.from_list_prefix bar_sk bar pm in
            let exp = check_exp l_e e in
            let a = C.new_type () in
            let res = 
              Seplist.map
                (fun pe ->
                   let (res,t) = check_pexp l_e pe in
                     C.equate_types l' "match expression" t a;
                     res)
                pm
            in
              C.equate_types l "match expression" a { t = Tfn(exp_to_typ exp,ret_type) };
              A.mk_case false l sk1 exp sk2 res sk3 rt
        | Ast.Typed(sk1,e,sk2,typ,sk3) ->
            let exp = check_exp l_e e in
            let src_t = typ_to_src_t T.allow_backend_quots build_wild C.add_tyvar C.add_nvar T.e typ in
              C.equate_types l "type-annotated expression" src_t.typ (exp_to_typ exp);
              C.equate_types l "type-annotated expression" src_t.typ ret_type;
              A.mk_typed l sk1 exp sk2 src_t sk3 rt
        | Ast.Let(sk1,lb,sk2, body) -> 
            let (lb,lex_env) = check_letbind_internal l_e lb in
            let body_exp = check_exp (Nfmap.union l_e lex_env) body in
              C.equate_types l "let expression" ret_type (exp_to_typ body_exp);
              A.mk_let l sk1 lb sk2 body_exp rt
        | Ast.Tup(sk1,es,sk2) ->
            let es = Seplist.from_list es in
            let exps = Seplist.map (check_exp l_e) es in
              C.equate_types l "tuple expression" ret_type 
                { t = Ttup(Seplist.to_list_map exp_to_typ exps) };
              A.mk_tup l sk1 exps sk2 rt
        | Ast.Elist(sk1,es,sk3,semi,sk2) -> 
            let es = Seplist.from_list_suffix es sk3 semi in
            let exps = Seplist.map (check_exp l_e) es in
            let a = C.new_type () in
              Seplist.iter (fun exp -> C.equate_types l "list expression" a (exp_to_typ exp)) exps;
              C.equate_types l "list expression" ret_type { t = Tapp([a], Path.listpath) };
              A.mk_list l sk1 exps sk2 ret_type
        | Ast.Vector(sk1,es,sk3,semi,sk2) -> 
            let es = Seplist.from_list_suffix es sk3 semi in
            let exps = Seplist.map (check_exp l_e) es in
            let a = C.new_type () in
            let len = {t = Tne( { nexp=Nconst(Seplist.length exps)} ) }in
              Seplist.iter (fun exp -> C.equate_types l "vector expression" a (exp_to_typ exp)) exps;
              C.equate_types l "vector expression" ret_type { t = Tapp([a;len], Path.vectorpath) };
              A.mk_vector l sk1 exps sk2 ret_type
        | Ast.VAccess(e,sk1,nexp,sk2) -> 
            let exp = check_exp l_e e in
            let n = nexp_to_src_nexp C.add_nvar nexp in
            let vec_n = C.new_nexp () in
            let t = exp_to_typ exp in
              C.equate_types l "vector access expression" { t = Tapp([ ret_type;{t = Tne(vec_n)}],Path.vectorpath) } t;
              C.in_range l vec_n n.nt;
              A.mk_vaccess l exp sk1 n sk2 ret_type
        | Ast.VAccessR(e,sk1,n1,sk2,n2,sk3) -> 
            let exp = check_exp l_e e in
            let n1 = nexp_to_src_nexp C.add_nvar n1 in
            let n2 = nexp_to_src_nexp C.add_nvar n2 in
            let vec_n = C.new_nexp () in
            let vec_t = C.new_type () in
            let t = exp_to_typ exp in
              C.equate_types l "vector access expression" { t=Tapp([vec_t;{t = Tne(vec_n)}], Path.vectorpath) } t;
              C.in_range l n2.nt n1.nt;
              C.in_range l vec_n n2.nt;
              C.equate_types l "vector access expression" ret_type { t =Tapp([vec_t;{t = Tne({ nexp=Nadd(n2.nt,{nexp=Nneg(n1.nt)})})}], Path.vectorpath)};
              A.mk_vaccessr l exp sk1 n1 sk2 n2 sk3 ret_type 
        | Ast.Paren(sk1,e,sk2) ->
            let exp = check_exp l_e e in
              C.equate_types l "parenthesized expression" ret_type (exp_to_typ exp);
              A.mk_paren l sk1 exp sk2 rt
        | Ast.Begin(sk1,e,sk2) ->
            let exp = check_exp l_e e in
              C.equate_types l "begin expression" ret_type (exp_to_typ exp);
              A.mk_begin l sk1 exp sk2 rt
        | Ast.If(sk1,e1,sk2,e2,sk3,e3) ->
            let exp1 = check_exp l_e e1 in
            let exp2 = check_exp l_e e2 in
            let exp3 = check_exp l_e e3 in
              C.equate_types l "if expression" ret_type (exp_to_typ exp2);
              C.equate_types l "if expression" ret_type (exp_to_typ exp3);
              C.equate_types l "if expression" (exp_to_typ exp1) { t = Tapp([], Path.boolpath) };
              A.mk_if l sk1 exp1 sk2 exp2 sk3 exp3 rt
        | Ast.Cons(e1,sk,e2) ->
            let e = 
              check_exp l_e 
                (Ast.Expr_l(Ast.Infix(e1,Ast.SymX_l((sk,r"::"), l),e2), l))
            in 
              C.equate_types l ":: expression" ret_type (exp_to_typ e);
              e
        | Ast.Lit(lit) ->
            let lit = check_lit false ret_type lit in
              C.equate_types l "literal expression" ret_type lit.typ;
              A.mk_lit l lit rt
        | Ast.Set(sk1,es,sk2,semi,sk3) -> 
            let es = Seplist.from_list_suffix es sk2 semi in
            let exps = Seplist.map (check_exp l_e) es in
            let a = C.new_type () in
              C.add_constraint (External_constants.class_label_to_path "class_set_type") a;
              Seplist.iter (fun exp -> C.equate_types l "set expression" a (exp_to_typ exp)) exps;
              C.equate_types l "set expression" ret_type { t = Tapp([a], Path.setpath) };
              A.mk_set l sk1 exps sk3 ret_type
        | Ast.Setcomp(sk1,e1,sk2,e2,sk3) ->
            let not_shadowed n =
              not (Nfmap.in_dom n l_e) &&
              not (Nfmap.in_dom n T.e.local_env.v_env)
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
              C.equate_types l "set comprehension expression" (exp_to_typ exp2) { t = Tapp([], Path.boolpath) };
              C.equate_types l "set comprehension expression" (exp_to_typ exp1) a;
              C.add_constraint (External_constants.class_label_to_path "class_set_type") a;
              C.equate_types l "set comprehension expression" ret_type { t = Tapp([a], Path.setpath) };
              A.mk_setcomp l sk1 exp1 sk2 exp2 sk3 vars rt
        | Ast.Setcomp_binding(sk1,e1,sk2,sk5,qbs,sk3,e2,sk4) ->
            let (quant_env,qbs) = check_qbs false l_e qbs in
            let env = Nfmap.union l_e quant_env in
            let exp1 = check_exp env e1 in
            let exp2 = check_exp env e2 in
            let a = C.new_type () in
              C.equate_types l "set comprehension expression" (exp_to_typ exp2) { t = Tapp([], Path.boolpath) };
              C.equate_types l "set comprehension expression" (exp_to_typ exp1) a;
              C.add_constraint (External_constants.class_label_to_path "class_set_type") a;
              C.equate_types l "set comprehension expression" ret_type { t = Tapp([a], Path.setpath) };
              A.mk_comp_binding l false sk1 exp1 sk2 sk5 
                (List.rev qbs) sk3 exp2 sk4 rt
        | Ast.Quant(q,qbs,s,e) ->
            let (quant_env,qbs) = check_qbs false l_e qbs in
            let et = check_exp (Nfmap.union l_e quant_env) e in
              C.equate_types l "quantified expression" ret_type { t = Tapp([], Path.boolpath) };
              C.equate_types l "quantified expression" ret_type (exp_to_typ et);
              A.mk_quant l q (List.rev qbs) s et rt
        | Ast.Listcomp(sk1,e1,sk2,sk5,qbs,sk3,e2,sk4) ->
            let (quant_env,qbs) = check_qbs true l_e qbs in
            let env = Nfmap.union l_e quant_env in
            let exp1 = check_exp env e1 in
            let exp2 = check_exp env e2 in
            let a = C.new_type () in
              C.equate_types l "list comprehension expression" (exp_to_typ exp2) { t = Tapp([], Path.boolpath) };
              C.equate_types l "list comprehension expression" (exp_to_typ exp1) a;
              C.equate_types l "list comprehension expression" ret_type { t = Tapp([a], Path.listpath) };
              A.mk_comp_binding l true sk1 exp1 sk2 sk5 
                (List.rev qbs) sk3 exp2 sk4 rt
        | Ast.Do(sk1,mn,lns,sk2,e,sk3) ->
            let mod_descr = lookup_mod T.e mn in
            let mod_env = mod_descr.mod_env in
            let mod_id = 
              { id_path = Id_some (Ident.from_id mn);
                id_locn = (match mn with Ast.Id(_,_,l) -> l);
                descr = mod_descr.mod_binding;
                instantiation = []; }
            in
            let monad_type_ctor = 
              match Nfmap.apply mod_env.p_env (Name.from_rope (r "t")) with
                | None ->
                    raise (Reporting_basic.err_type_pp mod_id.id_locn "monad module missing type t"
                      Ident.pp (Ident.from_id mn))
                | Some((p,l)) -> p
            in
            let () =
              (* Check that the module contains an appropriate type "t" to be
               * the monad. *)
              match Pfmap.apply T.e.t_env monad_type_ctor with
                | None ->
                    raise (Reporting_basic.err_general true l "invariant in checking module contains monad structure broken")
                | Some(Tc_class _) ->
                    raise (Reporting_basic.err_type_pp mod_id.id_locn "type class used as monad" 
                      Path.pp monad_type_ctor)
                | Some(Tc_type(td)) -> begin
                    match td.type_tparams with
                     | [Nv _] ->
                         raise (Reporting_basic.err_type_pp mod_id.id_locn "monad type constructor with a number parameter" 
                          Path.pp monad_type_ctor)
                     | [Ty _] -> ()
                     | tnvars ->
                          raise (Reporting_basic.err_type_pp mod_id.id_locn 
                            (Printf.sprintf "monad type constructor with %d parameters" 
                              (List.length tnvars))
                            Path.pp monad_type_ctor)
                  end
            in
            let (return_tvs, return_type) = 
              check_const_for_do mod_id T.e.c_env mod_env.v_env "return" in
            let build_monad_type tv = {t = Tapp([{t = Tvar(tv)}], monad_type_ctor)} in
            let () =
              match return_tvs with
                | [tv] ->
                    assert_equal mod_id.id_locn "do/return"
                      T.e.t_env return_type 
                      { t = Tfn({t = Tvar(tv)}, build_monad_type tv) }
                | tvs ->
                    raise (Reporting_basic.err_type_pp mod_id.id_locn (Printf.sprintf "monad return function with %d type parameters" (List.length tvs))
                      Path.pp mod_id.descr)
            in
            let (bind_tvs, bind_type) = 
              check_const_for_do mod_id T.e.c_env mod_env.v_env "bind" in
            let build_bind_type tv1 tv2 =
              { t = Tfn(build_monad_type tv1, 
                        { t = Tfn({t = Tfn({ t = Tvar(tv1)}, 
                                           build_monad_type tv2)},
                                  build_monad_type tv2)})}
            in
            let direction =
              match bind_tvs with
                | [tv1;tv2] ->
                    (try
                      assert_equal mod_id.id_locn "do/>>="
                        T.e.t_env bind_type
                        (build_bind_type tv1 tv2);
                      BTO_input_output
                    with
                      Reporting_basic.Fatal_error (Reporting_basic.Err_type _) ->
                        assert_equal mod_id.id_locn "do/>>="
                          T.e.t_env bind_type
                          (build_bind_type tv2 tv1);
                      BTO_output_input )
                | tvs ->
                    raise (Reporting_basic.err_type_pp mod_id.id_locn (Printf.sprintf "monad >>= function with %d type parameters" (List.length tvs))
                      Path.pp mod_id.descr)
            in
            let (lns_env,lns) = check_lns l_e monad_type_ctor lns in
            let lns = List.rev lns in
            let env = Nfmap.union l_e lns_env in
            let exp = check_exp env e in
            let a = C.new_type () in
              C.equate_types l "do expression" (exp_to_typ exp)
                { t = Tapp([a], monad_type_ctor) };
              C.equate_types l "do expression" (exp_to_typ exp) ret_type;
              A.mk_do l sk1 mod_id lns sk2 exp sk3 (a, direction) rt


  and check_lns (l_e : lex_env) 
                (monad_type_ctor : Path.t)
                (lns : (Ast.pat*Ast.lex_skips*Ast.exp*Ast.lex_skips) list)
                =
    List.fold_left
      (fun (env,lst) -> 
         function
           | (p,s1,e,s2) ->
               let et = check_exp (Nfmap.union l_e env) e in
               let (pt,p_env) = check_pat (Nfmap.union l_e env) p Nfmap.empty in
               let p_env = Nfmap.union env p_env in
               let a = C.new_type () in
                 C.equate_types pt.locn "do expression" pt.typ a;
                 C.equate_types (exp_to_locn et) "do expression" (exp_to_typ et)
                   { t = Tapp([a], monad_type_ctor) };
                 (p_env,
                  Do_line(pt, s1, et, s2)::lst))
      (empty_lex_env,[])
      lns


  (* Corresponds to check_quant_binding or check_listquant_binding
   * 'D,E,EL |- qbind .. qbind gives EL2,S' depending on is_list *)
  and check_qbs (is_list : bool) (l_e : lex_env) (qbs : Ast.qbind list)=
    List.fold_left
      (fun (env,lst) -> 
         function
           | Ast.Qb_var(xl) ->
               if is_list then
                 raise (Reporting_basic.err_type_pp (Ast.xl_to_l xl) "unrestricted quantifier in list comprehension"
                   Name.pp (Name.strip_lskip (Name.from_x xl)));
               let a = C.new_type () in
               let n = Name.from_x xl in
                 (add_binding env (n, Ast.xl_to_l xl) a,
                  Qb_var({ term = n; locn = Ast.xl_to_l xl; typ = a; rest = (); })::lst)
           | Ast.Qb_list_restr(s1,p,s2,e,s3) ->
               let et = check_exp (Nfmap.union l_e env) e in
               let (pt,p_env) = check_pat (Nfmap.union l_e env) p env in
               let a = C.new_type () in
                 C.equate_types pt.locn "quantifier binding" pt.typ a;
                 C.equate_types (exp_to_locn et) "quantifier binding" (exp_to_typ et)
                   { t = Tapp([a], Path.listpath) };
                 (p_env,
                  Qb_restr(true,s1, pt, s2, et, s3)::lst)
           | Ast.Qb_restr(s1,(Ast.Pat_l(_,l) as p),s2,e,s3) ->
               if is_list then
                 raise (Reporting_basic.err_type_pp l "set-restricted quantifier in list comprehension"
                   (* TODO: Add a pretty printer *)
                   (fun _ _ -> ()) p);
               let et = check_exp (Nfmap.union l_e env) e in
               let (pt,p_env) = check_pat (Nfmap.union l_e env) p env in
               let a = C.new_type () in
                 C.equate_types pt.locn "quantifier binding" pt.typ a;
                 C.equate_types (exp_to_locn et) "quantifier binding" (exp_to_typ et)
                   { t = Tapp([a], Path.setpath) };
                 (p_env,
                  Qb_restr(false,s1, pt, s2, et, s3)::lst))
      (empty_lex_env,[])
      qbs

  and check_fexp (l_e : lex_env) (Ast.Fexp(i,sk1,e,l)) 
                 : (const_descr_ref id * lskips * exp * Ast.l) * t *
                                           const_descr_ref * Ast.l =
    let ((id,t),l') = check_field i in
    let exp = check_exp l_e e in
    let ret_type = C.new_type () in
      C.equate_types l "field expression 3" t { t = Tfn(ret_type, exp_to_typ exp) };
      ((id,sk1,exp,l), ret_type,id.descr, l')

  and check_fexps (l_e : lex_env) (Ast.Fexps(fexps,sk,semi,l)) 
        : (const_descr_ref id * lskips * exp * Ast.l) lskips_seplist * t * const_descr_ref list =
    let fexps = Seplist.from_list_suffix fexps sk semi in
    let stuff = Seplist.map (check_fexp l_e) fexps in
    let ret_type = C.new_type () in
      check_dup_field_names T.e.c_env (Seplist.to_list_map (fun (_,_,n,l) -> (n,l)) stuff);
      Seplist.iter (fun (_,t,_,_) -> C.equate_types l "field expression 4" t ret_type) stuff;
      (Seplist.map (fun (x,_,_,_) -> x) stuff,
       ret_type,
       Seplist.to_list_map (fun (_,_,n,_) -> n) stuff)

  and check_psexp_help l_e ps ot sk e l
        : pat list * (lskips * src_t) option * lskips * exp * t = 
    let ret_type = C.new_type () in
    let (param_pats,lex_env) = check_pats l_e empty_lex_env ps in
    let body_exp = check_exp (Nfmap.union l_e lex_env) e in
    let t = multi_fun (List.map annot_to_typ param_pats) (exp_to_typ body_exp) in
    let annot = 
      match ot with
        | Ast.Typ_annot_none -> 
            None
        | Ast.Typ_annot_some(sk',typ) ->
            let src_t' = typ_to_src_t T.allow_backend_quots build_wild C.add_tyvar C.add_nvar T.e typ in
              C.equate_types l "pattern/expression list" src_t'.typ (exp_to_typ body_exp);
              Some (sk',src_t')
    in
      C.equate_types l "pattern/expression list" ret_type t;
      (param_pats,annot,sk,body_exp,ret_type)

  and check_psexp (l_e : lex_env) (Ast.Patsexp(ps,sk,e,l)) 
        : pat list * lskips * exp * t = 
    let (a,b,c,d,e) = check_psexp_help l_e ps Ast.Typ_annot_none sk e l in
      (a,c,d,e)

  and check_pexp (l_e : lex_env) (Ast.Patexp(p,sk1,e,l)) 
        : (pat * lskips * exp * Ast.l) * t = 
    match check_psexp l_e (Ast.Patsexp([p],sk1,e,l)) with
      | ([pat],_,exp,t) -> ((pat,sk1,exp,l),t)
      | _ -> raise (Reporting_basic.err_general true l "invariant in checking pexp broken")

  and check_funcl (l_e : lex_env) (Ast.Funcl(xl,ps,topt,sk,e)) l =
    let (ps,topt,s,e,t) = check_psexp_help l_e ps topt sk e l in
      ({ term = Name.from_x xl;
         locn = Ast.xl_to_l xl;
         typ = t;
         rest = (); },
       (ps,topt,s,e,t))

  and check_letbind_internal (l_e : lex_env) (Ast.Letbind(lb,l)) 
        : letbind * lex_env = 
    match lb with
      | Ast.Let_val(p,topt,sk',e) ->
          let (pat,lex_env) = check_pat l_e p empty_lex_env in
          let exp = check_exp l_e e in
          let annot = 
            match topt with
              | Ast.Typ_annot_none -> 
                  None
              | Ast.Typ_annot_some(sk',typ) ->
                  let src_t' = typ_to_src_t T.allow_backend_quots build_wild C.add_tyvar C.add_nvar T.e typ in
                    C.equate_types l "let expression" src_t'.typ pat.typ;
                    Some (sk',src_t')
          in
          let _ = C.equate_types l "let expression" pat.typ (exp_to_typ exp) in
            ((Let_val(pat,annot,sk',exp),l), lex_env)
      | Ast.Let_fun(Ast.Funcl(xl,ps,topt,sk,e)) ->
          (* This might be a pattern match or a local function definition. So check, whether
             xl is already bound to a constructor in the context *)
          let l' = Ast.xl_to_l xl in
          let xl_is_constructor = begin
            let const_lookup_res = Nfmap.apply T.e.local_env.v_env (Name.strip_lskip (Name.from_x xl)) in
              match const_lookup_res with
                | None -> false
                | Some c ->
                    Pattern_syntax.is_constructor l' T.e Target.Target_ident c
          end in
          if not (xl_is_constructor) then begin
            (** add a new local function *)
            let (xl, (a,b,c,d,t)) = check_funcl l_e (Ast.Funcl(xl,ps,topt,sk,e)) l in
              ((Let_fun(xl,a,b,c,d),l),
               add_binding empty_lex_env (xl.term, xl.locn) t)
          end else begin
            (* Pattern match *)
            let _ = Reporting.report_warning T.e (Reporting.Warn_ambiguous_code (l, "let-pattern uses same syntax as function definition; consider adding parenthesis")) in
            let p = Ast.Pat_l (Ast.P_app (Ast.Id([],xl,l'), ps), l) in
            let lb' = Ast.Let_val(p,topt,sk,e) in
            check_letbind_internal (l_e : lex_env) (Ast.Letbind(lb',l)) 
          end

  (* Check lemmata expressions that must have type ret, which is expected to be bool but 
     for flexibility can be provided.
   *)
  let check_lem_exp (l_e : lex_env) l e ret_opt =
    let exp = check_exp l_e e in
    (match ret_opt with
      | None -> ()
      | Some ret -> C.equate_types l "top-level expression" ret (exp_to_typ exp));
    let Tconstraints(tnvars,constraints,length_constraints) = C.inst_leftover_uvars l in
    (exp,Tconstraints(tnvars,constraints,length_constraints))


  let check_constraint_redundancies l csl csv =
    List.iter (fun c -> C.check_numeric_constraint_implication l c csv) csl

  (* Check that a value definition has the right type according to previous
   * definitions of that name in the same module.
   * def_targets is None if the definitions is not target specific, otherwise it
   * is the set of targets that the definition is for.  def_env is the name and
   * types of all of the variables defined *)
  let apply_specs_for_def is_inline (def_targets : Targetset.t option) (l:Ast.l) 
    (def_env :  (Types.t * Ast.l) Typed_ast.Nfmap.t)  =
    Nfmap.iter
      (fun n (t,l) ->
         let const_data = Nfmap.apply T.new_module_env.v_env n in
           match const_data with
             | None -> () (*
                 (* The constant is not defined yet. Check whether the definition is target
                    specific and raise an exception in this case. *)
                 begin
                   match def_targets with
                     | Some _ -> 
                         raise (Reporting_basic.err_type_pp l
                           "target-specific definition without preceding 'val' specification"
                           Name.pp n)
                     | None -> ()
                 end *)
             | Some(c) ->
                 (* The constant is defined. Check, whether we are alowed to add another, target specific
                    definition. *)
                 let cd = c_env_lookup l T.e.c_env c in
                 begin
                   match cd.env_tag with
                     | (K_let | K_method) ->
                         (* only let's (and vals) can aquire more targets,
                            check whether only new targets are added *)
                         let duplicate_targets = (match def_targets with
                            | None -> cd.const_targets
                            | Some dt -> Targetset.inter cd.const_targets dt) in
                         let _ = if not (is_inline || Targetset.is_empty duplicate_targets) then
                             if Targetset.subset Target.all_targets_non_explicit duplicate_targets then
                               raise (Reporting_basic.err_type l
                                 (Printf.sprintf "defined variable '%s' is already defined for all targets"  (Name.to_string n))) 
                             else
                               raise (Reporting_basic.err_type_pp l
                                 (Printf.sprintf "defined variable '%s' is already defined for targets"  (Name.to_string n))
                                   (Pp.lst ", " (fun ppf t -> Pp.pp_str ppf (non_ident_target_to_string t)))
                                   (Targetset.elements duplicate_targets)) in                        
                         (* enforce that the already defined constant and the new one have the same type. *)
                         let a = C.new_type () in begin
                           C.equate_types cd.spec_l "applying val specification" a cd.const_type;
                           C.equate_types l "applying val specification" a t
                         end
                     | _ -> 
                         (* everything else can't be extended, so raise an exception *)
                         raise (Reporting_basic.err_type_pp l ("defined variable is already defined as a " ^ 
                              (env_tag_to_string cd.env_tag))
                           Name.pp n)
                 end
      ) def_env;
    let Tconstraints(tnvars, constraints,l_constraints) = C.inst_leftover_uvars l in
      check_constraint_no_inline l T.e constraints;
      Nfmap.iter
        (fun n (_,l') ->
           match Nfmap.apply T.e.local_env.v_env n with
             | None -> ()
             | Some(c) ->
                 let cd = c_env_lookup l T.e.c_env c in (
                 check_constraint_subset l constraints cd.const_class;
                 check_constraint_redundancies l l_constraints cd.const_ranges))
        def_env;
      Tconstraints(tnvars, constraints,l_constraints)

  let apply_specs_for_method def_targets l def_env inst_type =
    Nfmap.iter
      (fun n (t,l) ->
         let const_ref = Nfmap.apply T.e.local_env.v_env n in
         let const_data = Util.option_map (fun c -> c_env_lookup l T.e.c_env c) const_ref in
         match const_data with
             | Some(cd) when cd.env_tag = K_method ->
                 (* assert List.length c.const_tparams = 1 *)
                 let tv = List.hd cd.const_tparams in 
                 let subst = TNfmap.from_list [(tv, inst_type)] in
                 let spec_typ = type_subst subst cd.const_type in
                 let a = C.new_type () in
                   C.equate_types cd.spec_l "applying val specification" a spec_typ;
                   C.equate_types l "applying val specification" a t
             | _ -> 
                 raise (Reporting_basic.err_type_pp l "instance method not bound to class method"
                   Name.pp n))
      def_env;
    let Tconstraints(tnvars, constraints,l_constraints) = C.inst_leftover_uvars l in
      unsat_constraint_err l constraints;
      Tconstraints(tnvars, [], l_constraints)

  let apply_specs for_method is_inline (def_targets : Targetset.t option) l env = 
    match for_method with
      | None ->    apply_specs_for_def is_inline def_targets l env
      | Some(t) -> apply_specs_for_method def_targets l env t

  (* See Expr_checker signature above *)
  let check_letbind for_method is_inline (def_targets : Targetset.t option) l lb =
    let (lb,pe) = check_letbind_internal empty_lex_env lb in
    (lb, pe, apply_specs for_method is_inline def_targets l pe)

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
               C.equate_types l' "top-level function" t 
                 (match Nfmap.apply env (Name.strip_lskip n.term) with
                    | Some(t,_) -> t
                    | None ->
                        raise (Reporting_basic.err_general true l "invariant in checking functions broken"));
               (n,a,b,c,d))
          funcls
      in
        (funcls, env, apply_specs for_method false def_targets l env)


  (* See Expr_checker signature above *)
  let check_indrels (ctxt : defn_ctxt) (mod_path : Name.t list) (def_targets : Targetset.t option) l names clauses =
(* This is the old call to build rec_env that doesn't add the type information, so likely not necessary due to name information available below. However, left here at Nov 10 in case a type variable is actually needed instead *)
(*    let rec_env =
      List.fold_left
        (fun l_e (Ast.Name_l (Ast.Inderln_name_Name(_,x_l,_,_,_,_,_,_),_),_) ->
          let n = Name.strip_lskip (Name.from_x x_l) in
              if Nfmap.in_dom n l_e then 
                raise (Reporting_basic.err_general true l "invariant in checking duplicate definition in indrelns broken")
              else
                add_binding l_e (xl_to_nl x_l) (C.new_type ())) 
         empty_lex_env
         names
    in *)
    let names = Seplist.from_list names in
    let n = 
      Seplist.map 
         (fun (Ast.Name_l(Ast.Inderln_name_Name(s0,xl,s1,Ast.Ts(cp,typ),witness_opt,check_opt,functions_opt,s2), l1)) ->
            let (src_cp, tyvars, tnvarset, (sem_cp,sem_rp)) = check_constraint_prefix ctxt cp in 
            let () = check_free_tvs tnvarset typ in
            let src_t = typ_to_src_t T.allow_backend_quots anon_error ignore ignore (defn_ctxt_to_env ctxt) typ in
            let r_t = src_t.typ in
            (* Todo add checks and processing of witness_opt, check_opt, and funcitons_opt *)
            let witness,wit_path,ctxt  = (match witness_opt with
                            | Ast.Witness_none -> None,None,ctxt
                            | Ast.Witness_some (s0,s1,xl,s2) -> 
                              let n = Name.from_x xl in
                              let tn = Name.strip_lskip n in
                              let type_path = Path.mk_path mod_path tn in
                              let new_ctxt = add_p_to_ctxt ctxt (tn, (type_path, (Ast.xl_to_l xl))) in
                              Some( Indreln_witness(s0,s1,n,s2)), 
                                    Some type_path, 
                                    add_d_to_ctxt new_ctxt type_path (mk_tc_type [] None)) in
            let check = (match check_opt with 
                            | Ast.Check_none -> None
                            | Ast.Check_some(s0,xl,s1) -> Some(s0,Name.from_x xl,s1)) in
            let to_src_t = typ_to_src_t_indreln wit_path ctxt.all_tdefs (defn_ctxt_to_env ctxt) r_t in
            let rec mk_functions fo =
                match fo with
                  | Ast.Functions_none -> None
                  | Ast.Functions_one(xl,s1,t) -> Some([Indreln_fn(Name.from_x xl,s1,to_src_t t,None)])
                  | Ast.Functions_some(xl,s1,t,s2,fs) -> 
                     (match (mk_functions fs) with
                      | None -> Some([Indreln_fn(Name.from_x xl, s1, to_src_t t, Some s2)])
                      | Some fs -> Some((Indreln_fn(Name.from_x xl,s1, to_src_t t, Some s2))::fs)) in
            (xl,RName(s0,Name.from_x xl,nil_const_descr_ref,s1,(src_cp,src_t),witness, check, mk_functions functions_opt,s2)))
         names 
    in
    let rec_env =
      List.fold_left
        (fun l_e (xl,(RName(_,x,_,_,(src_cp,src_t),_,_,_,_))) ->
          let n = Name.strip_lskip x in
              if Nfmap.in_dom n l_e then 
                raise (Reporting_basic.err_general true l "invariant in checking duplicate definition in indrelns broken")
              else
                add_binding l_e (xl_to_nl xl) (src_t.typ)) 
         empty_lex_env
         (Seplist.to_list n)
    in 
    let n = Seplist.map snd n in
    let clauses = Seplist.from_list clauses in
    let c =
      Seplist.map
        (fun (Ast.Rule_l(Ast.Rule(xl,s0,s1,ns,s2,e,s3,xl',es), l2)) ->
           let quant_env =
             List.fold_left
               (fun l_e nt -> match nt with
                              | Ast.Name_t_name xl -> add_binding l_e (xl_to_nl xl) (C.new_type ())
                              | Ast.Name_t_nt (_,xl,_,t,_) -> add_binding l_e (xl_to_nl xl) (C.new_type ()) (*Need to equate this type to t*))
               empty_lex_env
               ns
           in
           let extended_env = Nfmap.union rec_env quant_env in
           let et = check_exp extended_env e in
           let ets = List.map (check_exp extended_env) es in
           let new_name = Name.from_x xl in
           let new_name' = annot_name (Name.from_x xl') (Ast.xl_to_l xl') rec_env in
             C.equate_types l2 "inductive relation" (exp_to_typ et) { t = Tapp([], Path.boolpath) };
             C.equate_types l2 "inductive relation"
               new_name'.typ 
               (multi_fun 
                  (List.map exp_to_typ ets) 
                  { t = Tapp([], Path.boolpath) });
             (Rule(new_name,
              s0,
              s1,
              List.map 
                (fun n ->
                  match n with
                    | Ast.Name_t_name xl -> QName (annot_name (Name.from_x xl) (Ast.xl_to_l xl) quant_env)
                    | Ast.Name_t_nt (sk1, xl, sk2, typ, sk3) ->
                      let src_t = typ_to_src_t T.allow_backend_quots build_wild C.add_tyvar C.add_nvar T.e typ in
                        Name_typ (sk1, annot_name (Name.from_x xl) (Ast.xl_to_l xl) quant_env, sk2, src_t, sk3))
                ns,
              s2,
              Some et,
              s3,
              new_name',
              nil_const_descr_ref,
              ets),l2))
        clauses
    in
      (n,c,rec_env, apply_specs None false def_targets l rec_env)

end (* end of Expr_checker *)



(* -------------------------------------------------------------------------- *)
(* parsing top-level defs                                                     *)
(* -------------------------------------------------------------------------- *)


let add_let_defs_to_ctxt 
      (* The path of the enclosing module *)
      (mod_path : Name.t list)
      (ctxt : defn_ctxt)
      (* The type and length variables that were generalised for this definition *)
      (tnvars : Types.tnvar list) 
      (* The class constraints that the definition's type variables must satisfy *) 
      (constraints : (Path.t * Types.tnvar) list)
      (* The length constraints that the definition's length variables must satisfy *) 
      (lconstraints : Types.range list)
      (env_tag : env_tag) 
      (new_targs_opt : Targetset.t option) 
      (l_env : lex_env) 
      : defn_ctxt =
  let new_targs = Util.option_default all_targets_non_explicit new_targs_opt in
  let (c_env, new_env) =
    Nfmap.fold
      (fun (c_env, new_env) n (t,l) ->
        match Nfmap.apply ctxt.new_defs.v_env n with
          | None ->
              (* not present yet, so insert a new one *)
              let c_d = 
                    { const_binding = Path.mk_path mod_path n;
                      const_tparams = tnvars;
                      const_class = constraints;
                      const_no_class = Targetmap.empty;
                      const_ranges = lconstraints;
                      const_type = t;
                      spec_l = l;
                      env_tag = env_tag;
                      const_targets = new_targs;
		      relation_info = None;
                      target_rename = Targetmap.empty;
                      target_rep = Targetmap.empty;
                      target_ascii_rep = Targetmap.empty;
                      termination_setting = Target.Targetmap.empty;
                      compile_message = Targetmap.empty } in
              let (c_env', c) = c_env_save c_env None c_d in
              (c_env', Nfmap.insert new_env (n, c))
          | Some(c) -> 
              (* The definition is already in the context.  Here we just assume
               * it is compatible with the existing definition, having
               * previously checked it. So, we only need to update the set of targets. *) 
              let c_d = c_env_lookup l c_env c in
              let targs = Targetset.union c_d.const_targets new_targs in
              let (c_env', c) = c_env_save c_env (Some c) { c_d with const_targets = targs } in
              (c_env', Nfmap.insert new_env (n, c)))
      (ctxt.ctxt_c_env, Nfmap.empty) l_env
  in  
  union_v_ctxt { ctxt with ctxt_c_env = c_env } new_env

(* Check a type definition and add it to the context.  mod_path is the path to
 * the enclosing module.  Ignores any constructors or fields, just handles the
 * type constructors. *)
let build_type_def_help (mod_path : Name.t list) (context : defn_ctxt) 
      (tvs : Ast.tnvar list) ((type_name,l) : name_l) (regex : name_sect option) (type_abbrev : Ast.typ option) 
      : defn_ctxt = 
  let tvs = List.map (fun tv -> tnvar_to_types_tnvar (ast_tnvar_to_tnvar tv)) tvs in
  let tn = Name.strip_lskip type_name in
  let type_path = Path.mk_path mod_path tn in
  let () =
    match Nfmap.apply context.new_defs.p_env tn with
      | None -> ()
      | Some(p, _) ->
          begin
            match Pfmap.apply context.all_tdefs p with
              | None -> raise (Reporting_basic.err_general true l "invariant in checking type definition broken")
              | Some(Tc_type _) ->
                  raise (Reporting_basic.err_type_pp l "duplicate type constructor definition"
                    Name.pp tn)
              | Some(Tc_class _) ->
                  raise (Reporting_basic.err_type_pp l "type constructor already defined as a type class" 
                    Name.pp tn)
          end
  in
  let regex = match regex with | Some(Name_restrict(_,_,_,_,r,_)) -> Some r | _ -> None in
  let new_ctxt = add_p_to_ctxt context (tn, (type_path, l))
  in
    begin
      match type_abbrev with
        | Some(typ) ->
            check_free_tvs (tvs_to_set tvs) typ;
            let src_t = 
              typ_to_src_t false anon_error ignore ignore (defn_ctxt_to_env context) typ 
            in
              if (regex = None)
                then add_d_to_ctxt new_ctxt type_path 
                        (mk_tc_type_abbrev (List.map fst tvs) src_t.typ)
                else raise (Reporting_basic.err_type_pp l "Type abbreviations may not restrict identifier names" Name.pp tn)
        | None ->
            add_d_to_ctxt new_ctxt type_path 
              (mk_tc_type (List.map fst tvs) regex)
    end

let build_type_name_regexp (name: Ast.name_opt) : (name_sect option) =
  match name with
    | Ast.Name_sect_none -> None
    | Ast.Name_sect_name( sk1,name,sk2,sk3, regex,sk4) -> 
      let (n,l) = xl_to_nl name in
      if ((Name.to_string (Name.strip_lskip n)) = "name")
         then Some(Name_restrict(sk1,(n,l),sk2,sk3,regex,sk4))
      else 
         raise (Reporting_basic.err_type_pp l "Type name restrictions must begin with 'name'" Name.pp (Name.strip_lskip n))

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
         typ_to_src_t false anon_error ignore ignore (defn_ctxt_to_env ctxt) typ 
       in
         check_free_tvs tvs_set typ;
         ((fn,l'),sk1,src_t))
    recs

let add_record_to_ctxt build_descr (ctxt : defn_ctxt) 
      (recs : (name_l * lskips * src_t * Targetset.t) lskips_seplist) 
      : ((name_l * const_descr_ref * lskips * src_t) lskips_seplist * defn_ctxt)  =
   Seplist.map_acc_left
      (fun ((fn,l'),sk1,src_t,targs) ctxt ->
         let fn' = Name.strip_lskip fn in
         let field_descr = build_descr fn' l' src_t.typ targs in
         let () = 
           match Nfmap.apply ctxt.new_defs.f_env fn' with
             | None -> ()
             | Some _ ->
                 raise (Reporting_basic.err_type_pp l' "duplicate field name definition"
                   Name.pp fn')
         in
         let (c_env', f) = c_env_save ctxt.ctxt_c_env None field_descr in
         let ctxt = {ctxt with ctxt_c_env = c_env'} in
         let ctxt = add_f_to_ctxt ctxt (fn', f)
         in
           ((fn, l'),f,sk1,src_t), ctxt)
      ctxt
      recs

let rec build_variant build_descr tvs_set (ctxt : defn_ctxt) 
      (vars : Ast.ctor_def lskips_seplist) 
      : (name_l * const_descr_ref * lskips * src_t lskips_seplist) lskips_seplist * (const_descr_ref list * defn_ctxt) =
  let (sl, (cl, ctxt)) =
  Seplist.map_acc_left
    (fun (Ast.Cte(ctor_name,sk1,typs)) (cl, ctxt) ->
       let l' = Ast.xl_to_l ctor_name in 
       let src_ts =
         Seplist.map 
           (fun t ->
              typ_to_src_t false anon_error ignore ignore (defn_ctxt_to_env ctxt) t) 
           (Seplist.from_list typs)
        in
        let ctn = Name.from_x ctor_name in
        let ctn' = Name.strip_lskip ctn in
        let constr_descr : const_descr = build_descr ctn' l' src_ts in        
        let () = (* check, whether the constructor name is already used *)
          match Nfmap.apply ctxt.new_defs.v_env ctn' with
            | None -> (* not used, so everything OK*) ()
            | Some(c) ->
                begin (* already used, produce the right error message *)
                  let c_d = c_env_lookup l' ctxt.ctxt_c_env c in
                  let err_msg = begin
                    match c_d.env_tag with
                      | K_constr -> "duplicate constructor definition"
                      | _ -> "constructor already defined as a " ^ (env_tag_to_string c_d.env_tag)
                  end in
                  raise (Reporting_basic.err_type_pp l' err_msg Name.pp ctn')
                end
        in
        let (c_env', c) = c_env_save ctxt.ctxt_c_env None constr_descr in
        let ctxt : defn_ctxt = {ctxt with ctxt_c_env = c_env'} in
        let ctxt = add_v_to_ctxt ctxt (ctn', c)
        in
          List.iter (fun (t,_) -> check_free_tvs tvs_set t) typs;
          (((ctn,l'),c,sk1,src_ts), (c :: cl, ctxt)))
    ([], ctxt)
    vars in
  (sl, (List.rev cl, ctxt));;


let build_ctor_def (mod_path : Name.t list) (context : defn_ctxt)
      type_name (tvs : Ast.tnvar list)  (regexp : name_sect option) td
      : (name_l * tnvar list * Path.t * texp * name_sect option) * defn_ctxt= 
  let l = Ast.xl_to_l type_name in
  let tnvs = List.map ast_tnvar_to_tnvar tvs in
  let tvs_set = tvs_to_set (List.map tnvar_to_types_tnvar tnvs) in
  let tn = Name.from_x type_name in
  let type_path = Path.mk_path mod_path (Name.strip_lskip tn) in
  begin
    match td with
      | None -> 
          (((tn,l),tnvs,type_path, Te_opaque, regexp), context)
      | Some(sk3, Ast.Te_abbrev(t)) -> 
          (* Check and throw error if there's a regexp here *)
          (((tn,l), tnvs, type_path,
            Te_abbrev(sk3,
                      typ_to_src_t false anon_error ignore ignore (defn_ctxt_to_env context) t), None),
           context)
      | Some(sk3, Ast.Te_record(sk1',ntyps,sk2',semi,sk3')) ->
          let ntyps = Seplist.from_list_suffix ntyps sk2' semi in
          let recs = build_record tvs_set context ntyps in
          let tparams = List.map (fun tnv -> fst (tnvar_to_types_tnvar tnv)) tnvs in
          let tparams_t = List.map tnvar_to_type tparams in
          let (recs', ctxt) =
            add_record_to_ctxt 
              (fun fname l t targs ->
                 { const_binding = Path.mk_path mod_path fname;
                   const_tparams = tparams;
                   const_class = [];
                   const_no_class = Targetmap.empty;
                   const_ranges = [];
                   const_type = { t = Tfn ({ t = Tapp (tparams_t, type_path) }, t) };
                   spec_l = l;
                   env_tag = K_field;
                   relation_info = None;
                   const_targets = targs;
                   target_rename = Targetmap.empty;
                   target_rep = Targetmap.empty;
                   target_ascii_rep = Targetmap.empty;
                   termination_setting = Targetmap.empty;
                   compile_message = Targetmap.empty })
              context
              (Seplist.map (fun (x,y,src_t) -> (x,y,src_t,all_targets)) recs)
          in
          let field_refs = Seplist.to_list_map (fun (_, f, _, _) -> f) recs' in
          let ctxt = {ctxt with all_tdefs = type_defs_update_fields l ctxt.all_tdefs type_path field_refs} in 
            (((tn,l), tnvs, type_path, Te_record(sk3,sk1',recs',sk3'), regexp), ctxt)
      | Some(sk3, Ast.Te_variant(sk_init_bar,bar,ntyps)) ->
          let ntyps = Seplist.from_list_prefix sk_init_bar bar ntyps in
          let tparams = List.map (fun tnv -> fst (tnvar_to_types_tnvar tnv)) tnvs in
          let tparams_t = List.map tnvar_to_type tparams in
          let (vars,(cl, ctxt)) =
            build_variant
              (fun cname l ts ->
                 { const_binding = Path.mk_path mod_path cname;
                   const_tparams = tparams;
                   const_class = [];
                   const_no_class = Targetmap.empty;
                   const_ranges = [];
                   const_type = multi_fun (Seplist.to_list_map (fun t -> annot_to_typ t) ts) { t = Tapp (tparams_t, type_path) };
                   spec_l = l;
                   env_tag = K_constr;
                   relation_info = None;
                   const_targets = all_targets;
                   target_rename = Targetmap.empty;
                   target_rep = Targetmap.empty;
                   target_ascii_rep = Targetmap.empty;
                   termination_setting = Targetmap.empty;
                   compile_message = Targetmap.empty })
              tvs_set
              context
              ntyps
          in
          let constr_family = {constr_list = cl; constr_case_fun = None; constr_exhaustive = true; constr_default = true; constr_targets = Target.all_targets} in
          let _ = check_constr_family l (defn_ctxt_to_env ctxt) { t = Tapp (tparams_t, type_path) } constr_family in
          let ctxt = {ctxt with all_tdefs = type_defs_add_constr_family l ctxt.all_tdefs type_path constr_family} in 
            (((tn,l),tnvs, type_path, Te_variant(sk3,vars), regexp), ctxt)
  end;;


(* Builds the constructors and fields for a type definition, and the typed AST
 * *) 
let rec build_ctor_defs (mod_path : Name.t list) (ctxt : defn_ctxt) 
      (tds : Ast.td lskips_seplist) 
      : ((name_l * tnvar list * Path.t * texp * name_sect option) lskips_seplist * defn_ctxt) =
  Seplist.map_acc_left
    (fun td ctxt -> 
       match td with
         | Ast.Td(type_name, tnvs, name_sec, sk3, td) ->
             build_ctor_def mod_path ctxt type_name tnvs (build_type_name_regexp name_sec) (Some (sk3,td))
         | Ast.Td_opaque(type_name, tnvs, name_sec) ->
             build_ctor_def mod_path ctxt type_name tnvs (build_type_name_regexp name_sec) None)
    ctxt
    tds  

let check_ascii_rep_opt l = function
  | Ast.Ascii_opt_none -> (Targetmap.empty, None)
  | Ast.Ascii_opt_some (_, _, s, _) -> begin
       let _ = if (Util.is_simple_ident_string s) then () else
            raise (Reporting_basic.err_type l "invalid ascii-representation") in
       let n = Name.from_string s in
       (List.fold_left (fun tm t -> 
           Targetmap.insert tm (t, (l, n))) Targetmap.empty Target.all_targets_list,
        Some n) 
    end

(* Check a "val" declaration. The name must not be already defined in the
 * current sequence of definitions (e.g., module body) *)
let check_val_spec l (mod_path : Name.t list) (ctxt : defn_ctxt)
      (Ast.Val_spec(sk1, xl, ascii_rep_opt, sk2, Ast.Ts(cp,typ))) =
  let l' = Ast.xl_to_l xl in
  let n = Name.from_x xl in
  let n' = Name.strip_lskip n in
  let (src_cp, tyvars, tnvarset, (sem_cp,sem_rp)) = check_constraint_prefix ctxt cp in 
  let () = check_free_tvs tnvarset typ in
  let src_t = typ_to_src_t false anon_error ignore ignore (defn_ctxt_to_env ctxt) typ in
  let () = (* check that the name is really fresh *)
    match Nfmap.apply ctxt.new_defs.v_env n' with
      | None -> ()
      | Some(c) -> (* not fresh, so raise an exception *)
          begin 
            let c_d = c_env_lookup l' ctxt.ctxt_c_env c in
            let err_message = "specified variable already defined as a " ^ (env_tag_to_string c_d.env_tag) in
            raise (Reporting_basic.err_type_pp l' err_message Name.pp n')
          end
  in
  let (ascii_rep_map, ascii_name_opt) = check_ascii_rep_opt l ascii_rep_opt in
  let v_d =
    { const_binding = Path.mk_path mod_path n';
      const_tparams = tyvars;
      const_class = sem_cp;
      const_no_class = Targetmap.empty;
      const_ranges = sem_rp;
      const_type = src_t.typ;
      spec_l = l;
      env_tag = K_let;
      const_targets = Targetset.empty;
      relation_info = None;
      target_rename = Targetmap.empty;
      target_rep = Targetmap.empty;
      target_ascii_rep = ascii_rep_map;
      termination_setting = Targetmap.empty;
      compile_message = Targetmap.empty }
  in
  let (c_env', v) = c_env_save ctxt.ctxt_c_env None v_d in
  let ctxt = { ctxt with ctxt_c_env = c_env' } in
  let ctxt = add_v_to_ctxt ctxt (n',v) in
  let ctxt = Util.option_default_map ascii_name_opt ctxt 
        (fun an -> add_v_to_ctxt ctxt (an,v)) in
    (ctxt, (sk1, (n,l'), v, ascii_rep_opt, sk2, (src_cp, src_t)))


(* Check a method definition in a type class.  mod_path is the path to the
 * enclosing module. class_p is the path to the enclosing type class, and tv is
 * its type parameter. *)
let check_class_spec l (mod_path : Name.t list) (ctxt : defn_ctxt)
      (class_p : Path.t) (tv : Types.tnvar) (sk1,targs,xl,ascii_rep_opt,sk2,typ) 
      : const_descr_ref * const_descr * defn_ctxt * src_t * Targetset.t * class_val_spec =
  let l' = Ast.xl_to_l xl in
  let n = Name.from_x xl in
  let n' = Name.strip_lskip n in
  let target_opt = check_target_opt targs in
  let target_set = targets_opt_to_set targs in
  let tnvars = TNset.add tv TNset.empty in
  let () = check_free_tvs tnvars typ in
  let src_t = typ_to_src_t false anon_error ignore ignore (defn_ctxt_to_env ctxt) typ in
  let () = 
    match Nfmap.apply ctxt.new_defs.v_env n' with
      | None -> ()
      | Some(c) ->
          begin
            let c_d = c_env_lookup l' ctxt.ctxt_c_env c in
            let err_message = 
              match c_d.env_tag with
                | (K_method | K_instance) -> "duplicate class method definition"
                | _ -> "class method already defined as a " ^ (env_tag_to_string c_d.env_tag)
            in
            raise (Reporting_basic.err_type_pp l' err_message Name.pp n')
          end
  in
  let (ascii_rep_map, ascii_name_opt) = check_ascii_rep_opt l ascii_rep_opt in
  let v_d =
    { const_binding = Path.mk_path mod_path n';
      const_tparams = [tv];
      const_class = [(class_p, tv)];
      const_no_class = Targetmap.empty;
      const_ranges = [];
      const_type = src_t.typ;
      spec_l = l;
      env_tag = K_method;
      const_targets = target_set;
      relation_info = None;
      termination_setting = Target.Targetmap.empty;
      target_rename = Targetmap.empty;
      target_rep = Targetmap.empty;
      target_ascii_rep = ascii_rep_map;
      compile_message = Targetmap.empty }
  in
  let (c_env', v) = c_env_save ctxt.ctxt_c_env None v_d in
  let ctxt = { ctxt with ctxt_c_env = c_env' } in
  let ctxt = add_v_to_ctxt ctxt (n',v) in
  let ctxt = Util.option_default_map ascii_name_opt ctxt 
        (fun an -> add_v_to_ctxt ctxt (an,v)) 
  in
    (v, v_d, ctxt, src_t, target_set, (sk1, target_opt, (n,l'), v, ascii_rep_opt, sk2, src_t))



let letbind_to_funcl_aux_dest (ctxt : defn_ctxt) (lb_aux, l) = begin
  let l = Ast.Trans(false, "letbind_to_funcl_aux_dest", Some l) in
  let module C = Exps_in_context(struct let env_opt = None let avoid = None end) in
  let get_const_exp_from_name (nls : name_lskips_annot) : (const_descr_ref * exp) = begin
    let n = Name.strip_lskip nls.term in
    let n_ref =  match Nfmap.apply ctxt.cur_env.v_env n with
      | Some(r) -> r
      | _ -> raise (Reporting_basic.err_unreachable l "n should have been added just before") in
    let n_d = c_env_lookup l ctxt.ctxt_c_env n_ref in
    let id = { id_path = Id_some (Ident.mk_ident None [] n); id_locn = l; descr = n_ref; instantiation = List.map tnvar_to_type n_d.const_tparams } in
    let e = C.mk_const l id (Some (annot_to_typ nls)) in
    (n_ref, e)
  end in
  let (nls, pL, ty_opt, sk, e) = begin match lb_aux with
    | Let_val (p, ty_opt, sk, e) -> begin
         let nls = match Pattern_syntax.pat_to_ext_name p with 
                  | None -> raise (Reporting_basic.err_type l "unsupported pattern in top-level let definition")
                  | Some nls -> nls in
         (nls, [], ty_opt, sk, e)
      end
    | Let_fun (nls, pL, ty_opt, sk, e) -> (nls, pL, ty_opt, sk, e)
  end in
  let (n_ref, n_exp) = get_const_exp_from_name nls in
  (nls, n_ref, n_exp, pL, ty_opt, sk, e)
end 

let letbind_to_funcl_aux sk0 target_opt ctxt (lb : letbind) : val_def = begin
  let l = Ast.Trans (false, "letbind_to_funcl_aux", None) in
  let create_fun_def = match lb with
     | (Let_val (p, _, _, _), _) -> Pattern_syntax.is_ext_var_pat p
     | _ -> true
  in
  if create_fun_def then begin
     let (nls, n_ref, n_exp, pL, ty_opt, sk, e) = letbind_to_funcl_aux_dest ctxt lb in
     let sl = Seplist.sing (nls, n_ref, pL, ty_opt, sk, e) in
     Fun_def(sk0, FR_non_rec, target_opt, sl)
  end else begin
    let get_const_from_name_annot (nls : name_lskips_annot) : (Name.t * const_descr_ref) = begin
      let n = Name.strip_lskip nls.term in
      let n_ref =  match Nfmap.apply ctxt.cur_env.v_env n with
        | Some(r) -> r
        | _ -> raise (Reporting_basic.err_unreachable l "n should have been added just before") in
      (n, n_ref)
    end in
    let (p, ty_opt, sk, e) =
      match lb with
        | (Let_val (p, ty_opt, sk, e), _) -> (p, ty_opt, sk, e)
        | _ -> raise (Reporting_basic.err_general true l "invariant in checking letbind broken")
    in
    let pvars = Pattern_syntax.pat_vars_src p in
    let name_map = List.map get_const_from_name_annot pvars in
    Let_def(sk0, target_opt,  (p, name_map, ty_opt, sk, e))
  end

end

let letbinds_to_funcl_aux_rec l ctxt (lbs : (_ Typed_ast.lskips_seplist)) : funcl_aux Typed_ast.lskips_seplist =
  let lbs' = Seplist.map (fun (nls, pL, ty_opt, sk, e) -> letbind_to_funcl_aux_dest ctxt (Let_fun (nls, pL, ty_opt, sk, e), l)) lbs in

  let var_subst = Seplist.fold_left (fun (nls, _, n_exp, _, _, _, _) subst -> Nfmap.insert subst (Name.strip_lskip nls.term, Sub n_exp)) Nfmap.empty lbs' in
  let sub = (TNfmap.empty, var_subst) in
  let module C = Exps_in_context(struct let env_opt = None let avoid = None end) in
  let res = Seplist.map (fun (nls, n_ref, n_exp, pL, ty_opt, sk, e) -> (nls, n_ref, pL, ty_opt, sk, C.exp_subst sub e)) lbs' in
  res


let lb_to_inline l ctxt' is_transform target_set_opt lb =
    let (nls, n_ref, _, pL, ty_opt, sk3, et) = letbind_to_funcl_aux_dest ctxt' lb in
    let args = match Util.map_all Pattern_syntax.pat_to_ext_name pL with
                 | None -> raise (Reporting_basic.err_type l "non-variable pattern in inline")
                 | Some a -> a in         
    let all_targets = (match target_set_opt with None -> true | _ -> false) in
    let new_tr = CR_inline (l, all_targets, args, et) in
    let ts = Util.option_default (if is_transform then Target.all_targets else Target.all_targets_non_explicit) target_set_opt in

    let ctxt'' = Targetset.fold (fun t ctxt -> fst (ctxt_c_env_set_target_rep l ctxt n_ref t new_tr)) ts ctxt' in
    (ctxt'', args)


(* check "let" definitions. ts is the set of targets for which all variables must be defined (i.e., the
 * current backends, not the set of targets that this definition if for) *)
let check_val_def (ts : Targetset.t) (mod_path : Name.t list) (l : Ast.l) 
      (ctxt : defn_ctxt) 
      (vd : Ast.val_def) :
        (* The updated environment *)
        defn_ctxt * 
        (* The names of the defined values *) lex_env *
        val_def *
        (* The type and length variables the definion is generalised over, and class constraints on the type variables, and length constraints on the length variables *)
        typ_constraints =
  let module T = struct 
    let e = defn_ctxt_to_env ctxt
    let new_module_env = ctxt.new_defs
    let targets = ts
    let allow_backend_quots = false
  end in
  let module Checker = Make_checker(T) in
  let target_opt_ast = ast_def_to_target_opt (Ast.Val_def vd) in
  let target_set_opt = targets_opt_to_set_opt target_opt_ast in
  let target_opt = check_target_opt target_opt_ast in

  match vd with
      | Ast.Let_def(sk,_,lb) ->
          let (lb,e_v,Tconstraints(tnvs,constraints,lconstraints)) = Checker.check_letbind None false target_set_opt l lb in 
          let _ = check_free_tvs_letbind lb in
          let ctxt' = add_let_defs_to_ctxt mod_path ctxt (TNset.elements tnvs) constraints lconstraints K_let target_set_opt e_v in
          let (vd : val_def) = letbind_to_funcl_aux sk target_opt ctxt' lb in
          (ctxt', e_v, vd, Tconstraints(tnvs,constraints,lconstraints))
      | Ast.Let_rec(sk1,sk2,_,funcls) ->
          let funcls = Seplist.from_list funcls in
          let (lbs,e_v,Tconstraints(tnvs,constraints,lconstraints)) = Checker.check_funs None target_set_opt l funcls in 
          let _ = Seplist.iter (fun (a,b,c,d,e) -> check_free_tvs_letbind (Let_fun (a,b,c,d,e), l)) lbs in
          let ctxt' = add_let_defs_to_ctxt mod_path ctxt (TNset.elements tnvs) constraints lconstraints K_let target_set_opt e_v in
          let fauxs = letbinds_to_funcl_aux_rec l ctxt' lbs in
            (ctxt', e_v, (Fun_def(sk1,FR_rec sk2,target_opt,fauxs)), Tconstraints(tnvs,constraints,lconstraints))
      | (Ast.Let_inline (sk1,sk2,_,lb) | Ast.Let_transform (sk1,sk2,_,lb)) -> 
          let (lb,e_v,Tconstraints(tnvs,constraints,lconstraints)) = Checker.check_letbind None true target_set_opt l lb in 
          let _ = check_free_tvs_letbind lb in
          let ctxt' = add_let_defs_to_ctxt mod_path ctxt (TNset.elements tnvs) constraints lconstraints K_let target_set_opt e_v in
          let (nls, n_ref, _, _, _, sk3, et) = letbind_to_funcl_aux_dest ctxt' lb in
          let is_transform = match vd with Ast.Let_transform _ -> true | _ -> false in
          let _ = match (is_transform, target_opt) with
              | (false, _) -> ()
              | (_, Targets_opt_none) -> ()
              | _ ->   raise (Reporting_basic.err_type l "lem_transform does not permit target-options") in
          let (ctxt'', args) = lb_to_inline l ctxt' is_transform target_set_opt lb in
            (ctxt'', e_v, Let_inline(sk1,sk2,target_opt,nls,n_ref,args,sk3,et), Tconstraints(tnvs,constraints,lconstraints))


(* val_defs inside an instance. This call gets compared to [check_val_def] an extra
   type as argument. Functions are looked up in the corresponding class. This class is instantiated
   with the type and then the function is parsed as a function with the intended target type.
   Since instance methods should not refer to each other, in contrast to [check_val_def] the
   ctxt.cur_env is not modified. However, the new definitions are available in ctxt.new_defs. *)
let check_val_def_instance (ts : Targetset.t) (mod_path : Name.t list) (instance_type : Types.t) (l : Ast.l) 
      (ctxt : defn_ctxt) 
      (vd : Ast.val_def) :
        (* The updated environment *)
        defn_ctxt * 
        (* The names of the defined values *) lex_env *
        val_def *
        (* The type and length variables the definion is generalised over, and class constraints on the type variables, and length constraints on the length variables *)
        typ_constraints =

  (* check whether the definition is allowed inside an instance. Only simple, non-target specific let expressions are allowed. *)
  let ts' = match vd with
      | Ast.Let_def(_,None,Ast.Letbind(lb,_)) -> 
        (* try to find the method defined and if successful perhaps restrict the target_set *)
        begin
          let xl_opt =      
            match lb with
              | Ast.Let_fun (Ast.Funcl (xl, _, _, _, _)) -> Some xl
              | Ast.Let_val (Ast.Pat_l(Ast.P_app(Ast.Id([],xl,_), []), _), _, _, _) -> Some xl
              | _ -> None
          in
          let c_opt = Util.option_bind (fun xl -> Nfmap.apply ctxt.cur_env.v_env (Name.strip_lskip (Name.from_x xl))) xl_opt in
          match c_opt with
            | None -> ts
            | Some c -> begin
              let cd = c_env_lookup l ctxt.ctxt_c_env c in
              Targetset.inter ts cd.const_targets
          end
        end 
      | Ast.Let_def(_,Some _,_) -> raise (Reporting_basic.err_type l "instance method must not be target specific");
      | Ast.Let_rec(_,_,_,_) -> raise (Reporting_basic.err_type l "instance method must not be recursive");
      | Ast.Let_inline (_,_,target_opt,_) -> raise (Reporting_basic.err_type l "instance method must not be inlined");
      | Ast.Let_transform (_,_,target_opt,_) -> raise (Reporting_basic.err_type l "instance method must not be transformed");
  in

  (* Instantiate the checker. In contrast to check_val_def *)
  let module T = struct 
    let e = defn_ctxt_to_env ctxt
    let new_module_env = ctxt.new_defs
    let targets = ts'
    let allow_backend_quots = false
  end 
  in

  let module Checker = Make_checker(T) in
  match vd with
      | Ast.Let_def(sk,_,lb) ->
          let (lb,e_v,Tconstraints(tnvs,constraints,lconstraints)) = Checker.check_letbind (Some instance_type) false (Some Targetset.empty) l lb in 

          (* check, whether contraints are satisfied and only simple variable arguments are used (in order to allow simple inlining of
             instance methods. *)
          let _ = unsat_constraint_err l constraints in
          let _ = match lb with
             | (Let_fun (_, pL, _, _, _), _) ->
               if (List.for_all Pattern_syntax.is_ext_var_pat pL) then () else 
                  raise (Reporting_basic.err_type l "instance method must not have non-variable arguments");
             | (Let_val _, _) -> ()
          in

          let ctxt' = add_let_defs_to_ctxt mod_path ctxt (TNset.elements tnvs) constraints lconstraints K_instance None e_v in
          let (ctxt'', _) = lb_to_inline l ctxt' false None lb in

          let (vd : val_def) = letbind_to_funcl_aux sk Targets_opt_none ctxt'' lb in

          (* instance methods should not refer to each other. Therefore, remove the bindings added by add_let_defs_to_ctxt from
             ctxt.cur_env. They are still in ctxt.new_defs *)
          let ctxt''' = {ctxt'' with cur_env = ctxt.cur_env} in
          (ctxt''', e_v, vd, Tconstraints(tnvs,constraints,lconstraints))

      | _ -> raise (Reporting_basic.err_unreachable l "if vd is not a simple let, an exception should have already been raised.")


let check_lemma l ts (ctxt : defn_ctxt) 
      : Ast.lemma_decl -> 
        defn_ctxt *
        lskips *
        Ast.lemma_typ * 
        targets_opt *
        name_l * 
        lskips * exp =
  let module T = struct 
    let d = ctxt.all_tdefs 
    let i = ctxt.all_instances 
    let e = defn_ctxt_to_env ctxt
    let new_module_env = ctxt.new_defs
    let targets = ts
    let allow_backend_quots = false
  end 
  in
  let bool_ty = { Types.t = Types.Tapp ([], Path.boolpath) } in
  let module Checker = Make_checker(T) in
  let lty_get_sk = function
    | Ast.Lemma_theorem sk -> (sk, Ast.Lemma_theorem None)
    | Ast.Lemma_assert sk -> (sk, Ast.Lemma_assert None)
    | Ast.Lemma_lemma sk -> (sk, Ast.Lemma_lemma None) in
  let aux (lty, target_opt, e) =
     let module C = Exps_in_context(struct let env_opt = (Some T.e) let avoid = None end) in
     let (exp,Tconstraints(_, constraints,_)) = Checker.check_lem_exp empty_lex_env l e (Some bool_ty) in
(*   let _ = unsat_constraint_err l constraints in  *)
     let (sk0, lty') = lty_get_sk lty in
     let target_opt = check_target_opt target_opt in
     let _ = match lty with
       | Ast.Lemma_assert _ -> begin 
           let free_vars = C.exp_to_free exp in
           if (Nfmap.is_empty free_vars) then () else
              raise (Reporting_basic.err_type l "assertion contains free variables");

           let free_tnvars = (add_exp_entities empty_used_entities exp).used_tnvars in
           if (TNset.is_empty free_tnvars) then () else
             raise (Reporting_basic.err_type l "assertion contains free type variables")
           end
       | _ -> ()
     in
     (sk0, lty', target_opt, exp) 
  in
  let module C = Constraint(T) in
    function
      | Ast.Lemma_named (lty, target_opt, name, sk1, e) ->
          let (sk0, lty', target_opt, exp) = aux (lty, target_opt, e) in
          let (n, l) = xl_to_nl name in
          let n_s = Name.strip_lskip n in
          let _ = if (NameSet.mem n_s ctxt.lemmata_labels) then 
                      raise (Reporting_basic.err_type_pp l
                        "lemmata-label already used"
                         Name.pp n_s)
                   else () in
          (add_lemma_to_ctxt ctxt n_s,  sk0, lty', target_opt, (n,l), sk1, exp)

(* Check that a type can be an instance.  That is, it can be a type variable, a
 * function between type variables, a tuple of type variables or the application
 * of a (non-abbreviation) type constructor to variables.  Returns the
 * variables, and which kind of type it was. *)
let rec check_instance_type_shape (ctxt : defn_ctxt) (src_t : src_t)
      : TNset.t * Ulib.Text.t =
  let l = src_t.locn in 
  let err () = 
    raise (Reporting_basic.err_type_pp l "class instance type must be a type constructor applied to type variables"
      pp_type src_t.typ)
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
        (tvs_to_set (Seplist.to_list_map to_tnvar ts), r ("tup" ^ (string_of_int (Seplist.length ts))))
    | Typ_backend(p,_) -> raise (Reporting_basic.err_type p.id_locn "backend-type in class instance type")
    | Typ_app(p,ts) ->
        begin
          match Pfmap.apply ctxt.all_tdefs p.descr with
            | Some(Tc_type {type_abbrev = Some _}) ->
                raise (Reporting_basic.err_type_pp p.id_locn "type abbreviation in class instance type"
                  Ident.pp (
                    match p.id_path with
                      | Id_some id -> id
                      | Id_none _ -> raise (Reporting_basic.err_general true l "invariant in checking instance type shapes broken")
                  ))
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



let check_declare_target_rep_term_rhs (l : Ast.l) ts targ (ctxt : defn_ctxt) c id args (rhs_ty : Types.t) (rhs : Ast.target_rep_rhs) : (defn_ctxt * Typed_ast.target_rep_rhs) = 
  let module T = struct 
    let d = ctxt.all_tdefs 
    let i = ctxt.all_instances 
    let e = defn_ctxt_to_env ctxt
    let new_module_env = ctxt.new_defs
    let targets = ts
    let allow_backend_quots = true
  end in 
  let module Checker = Make_checker(T) in
  let (rhs, new_rep) = match rhs with
   | Ast.Target_rep_rhs_term_replacement e_org -> begin
       let rhs_lex_env = List.fold_left (fun env ap -> add_binding env (ap.term, ap.locn) ap.typ) empty_lex_env args in
       let (e, Tconstraints(tnvars, constraints,l_constraints)) = Checker.check_lem_exp rhs_lex_env l e_org (Some rhs_ty) in
       let _ = unsat_constraint_err l constraints in
       (Target_rep_rhs_term_replacement e, CR_simple (l, false, args, e))
     end
   | Ast.Target_rep_rhs_type_replacement _ ->
       raise (Reporting_basic.err_unreachable l "check_declare_target_rep_***term***_rhs is only called with terms, not types")
   | Ast.Target_rep_rhs_infix (sk1, infix_decl, sk2, id) ->
       let _ = if (List.length args = 0) then () else
                 raise (Reporting_basic.err_type l "infix target declaration with arguments") in
       let i = check_backend_quote l id in
       (Target_rep_rhs_infix (sk1, infix_decl, sk2, i), CR_infix(l, false, infix_decl, i))
   | Ast.Target_rep_rhs_undefined ->
       (Target_rep_rhs_undefined, CR_undefined (l, false))
   | Ast.Target_rep_rhs_special (sk1, sk2, sp, sargs) ->      
       let rhs_lex_env = List.fold_left (fun env ap -> add_binding env (ap.term, ap.locn) ap.typ) empty_lex_env args in
       let sargs' = List.map (fun sarg_org -> 
          let (e, Tconstraints(tnvars, constraints,l_constraints)) = Checker.check_lem_exp rhs_lex_env l sarg_org None in
          let _ = unsat_constraint_err l constraints in
          e) sargs
       in
       
       (* split sp into chunks with the whole in the middle *)
       let sp_list = Str.split_delim (Str.regexp_string "%e") sp in
       let _ = if not (List.length sp_list = List.length sargs + 1) then
           raise (Reporting_basic.err_type l "number of arguments and holes do not match in target representation")
	 else ()
       in
       (Target_rep_rhs_special(sk1, sk2, sp, sargs'), CR_special (l, false, CR_special_rep (sp_list, sargs'), args)) 
  in
  let (ctxt', _) = ctxt_c_env_set_target_rep l ctxt c targ new_rep in
  (ctxt', rhs)


let component_term_id_lookup (l : Ast.l) (ctxt : defn_ctxt) (comp : Ast.component) (id : Ast.id) =
    let Ast.Id(mp,xl,_) = id in
    let e = path_lookup l (defn_ctxt_to_env ctxt) (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
    let map = match comp with
      | Ast.Component_function _ -> e.v_env
      | Ast.Component_field _ -> e.f_env 
      | _ ->  raise (Reporting_basic.err_type l "Invalid component! Only fields and constants / constructors are allowed here.")
    in
    let c = match Nfmap.apply map (Name.strip_lskip (Name.from_x xl)) with
      | None -> raise (Reporting_basic.err_type_pp l "unbound name" Ident.pp (Ident.from_id id))
      | Some c -> c
    in
    let c_descr = c_env_lookup l ctxt.ctxt_c_env c in
    let c_id = { id_path = Id_some (Ident.from_id id); 
                 id_locn = l; 
                 descr = c; 
                 instantiation = List.map tnvar_to_type c_descr.const_tparams } in
    (c_id, c_descr)


(* [check_declare_target_rep_term ts mod_path l ctxt comp id args rhs] checks
   the statement

   declare target_rep id args = rhs
*)
let check_declare_target_rep_term 
   (ts : Targetset.t) 
   (mod_path : Name.t list) 
   (l : Ast.l) 
   (ctxt : defn_ctxt) 
   sk1
   (target : Ast.target)
   sk2
   (comp : Ast.component) 
   (id : Ast.id) 
   (args : Ast.x_l list)
   sk3
   (rhs : Ast.target_rep_rhs) : 
   (Typecheck_ctxt.defn_ctxt * Typed_ast.def_aux option) = 
begin
  (* lookup the constant for the id *)
  let (c_id, c_descr) = component_term_id_lookup l ctxt comp id in

  (* parse the arguments / get the correct type *)
  let rec get_arg_types acc cur_ty args = match args with
    | [] -> (cur_ty, List.rev acc)
    | x_l :: args' ->
      begin
        match dest_fn_type (Some ctxt.all_tdefs) cur_ty with
          | None -> raise (Reporting_basic.err_type_pp l "to many arguments given in target representation declaration" Ident.pp (Ident.from_id id))
          | Some (ty_arg, ty_rest) -> begin
              let processed_arg : name_lskips_annot = 
                { term = Name.from_x x_l;
                  locn = Ast.xl_to_l x_l;
                  typ = ty_arg;
                  rest = (); }
              in
              get_arg_types (processed_arg::acc) ty_rest args'
          end
      end
  in
  let ((rhs_ty : Types.t), (args_parsed : name_lskips_annot list)) = get_arg_types [] c_descr.const_type args in

  (* now parse the rhs, this also updates the context *)
  let (ctxt', rhs_parsed) = check_declare_target_rep_term_rhs l ts (Target.ast_target_to_target target) ctxt c_id.descr (Ident.from_id id) args_parsed rhs_ty rhs in

  let def_aux = Decl_target_rep_term (sk1, target, sk2, comp, c_id, 
                   args_parsed, sk3, rhs_parsed) in
  (ctxt', Some (Declaration def_aux))
end


let check_declare_target_rep_type 
   (ts : Targetset.t) 
   (mod_path : Name.t list) 
   (l : Ast.l) 
   (ctxt : defn_ctxt) 
   sk1
   target
   sk2
   sk3
   type_id
   tnvars 
   sk4
   (rhs : Ast.typ) : 
   (Typecheck_ctxt.defn_ctxt * Typed_ast.def_aux option) = 
begin
  let tvs_tast = List.map ast_tnvar_to_tnvar tnvars in
  let tvs = List.map tnvar_to_types_tnvar tvs_tast in
  let p = lookup_p "" (defn_ctxt_to_env ctxt) type_id in
  let p_id = {id_path = Id_some (Ident.from_id type_id); 
              id_locn = l;
              descr = p;
              instantiation = []; } in  

  let td = match Pfmap.apply ctxt.all_tdefs p with
            | Some(Tc_type(td)) -> td 
            | _ -> raise (Reporting_basic.err_general true l "invariant in checking type broken") in

  let _ = check_free_tvs (tvs_to_set tvs) rhs in
  let rhs_src_t = typ_to_src_t true anon_error ignore ignore (defn_ctxt_to_env ctxt) rhs in 
  let (rhs_src_t, _) = typ_alter_init_lskips remove_init_ws rhs_src_t in

 
  let decl_def = Decl_target_rep_type (sk1, target, sk2, sk3, p_id, tvs_tast, 
                   sk4, rhs_src_t) in

  let new_rep = match (tvs, rhs_src_t.term) with
     | ([], Typ_backend (p, [])) -> TYR_simple(l, true, Path.to_ident None p.descr)
     | _ -> if (List.length td.type_tparams = List.length tvs) then
              TYR_subst (l, true, List.map fst tvs, rhs_src_t) 
            else 
              raise (Reporting_basic.err_type_pp l (Printf.sprintf "type constructor expected %d type arguments, given %d" 
                          (List.length td.type_tparams)
                          (List.length tvs))
                     Ident.pp (Ident.from_id type_id))
  in 
  let targ = (Target.ast_target_to_target target) in
  let (ctxt', old_rep_opt) = ctxt_all_tdefs_set_target_rep l ctxt p targ new_rep in
  let _ =  match old_rep_opt with
      | None -> (* no representation present before, so OK *) ()
      | Some old_rep -> if type_target_rep_allow_override old_rep then () else begin
          let loc_s = Reporting_basic.loc_to_string true (type_target_rep_to_loc old_rep) in
          let msg = Format.sprintf 
                      "a %s target representation for type '%s' has already been given at\n    %s" 
                      (Target.non_ident_target_to_string targ) (Path.to_string p) loc_s in
          raise (Reporting_basic.err_type l msg)
      end in
  (ctxt', Some (Declaration decl_def))
end


(***************************************)
(* The main function for defs          *)
(***************************************)

(* backend_targets is the set of targets for which all variables must be defined
 * (i.e., the current backends, not the set of targets that this definition if
 * for) *)
let rec check_def (backend_targets : Targetset.t) (mod_path : Name.t list) 
      (ctxt : defn_ctxt) (Ast.Def_l(def,l)) semi_sk semi 
      : defn_ctxt * (def_aux option) =
  let module T = 
    struct 
      let d = ctxt.all_tdefs 
      let i = ctxt.all_instances 
      let e = defn_ctxt_to_env ctxt
      let new_module_env = ctxt.new_defs
      let allow_backend_quots = false
    end 
  in
    match def with
      | Ast.Type_def(sk,tdefs) ->
          let tdefs = Seplist.from_list tdefs in
          let new_ctxt = build_type_defs mod_path ctxt tdefs in
          let (res,new_ctxt) = build_ctor_defs mod_path new_ctxt tdefs in
            (new_ctxt, Some (Type_def(sk,res)))
      | Ast.Val_def(val_def) ->
          let (ctxt',c,vd,Tconstraints(_,constraints,lconstraints)) = 
            check_val_def backend_targets mod_path l ctxt val_def 
          in
            (ctxt', Some (Val_def vd))
      | Ast.Lemma(lem) ->
            let (ctxt', sk, lty, targs, name, sk2, e) = check_lemma l backend_targets ctxt lem in
            (ctxt', Some (Lemma(sk, lty, targs, name, sk2, e)))
      | Ast.Declaration(Ast.Decl_rename_decl(sk1, target_opt, sk2, component, id, sk3, xl')) ->
          let n' = Name.from_x xl' in
          let targs = check_target_opt target_opt in

          (* do the renaming *)
          let (nk, p) = lookup_name (defn_ctxt_to_env ctxt) (Some component) id in
          let nk_id = { id_path = Id_some (Ident.from_id id); 
                        id_locn = l; 
                        descr = nk; 
                        instantiation = [] } in
          let def' = Some (Declaration (Decl_rename (sk1, targs, sk2, component, nk_id, sk3, n'))) in
          let ctxt' = begin
            match nk with
              | (Nk_field c | Nk_constr c | Nk_const c) ->
                  begin 
                    let cd = c_env_lookup l ctxt.ctxt_c_env c in
                    let cd' = List.fold_left (fun cd t -> fst (constant_descr_rename t (Name.strip_lskip n') l cd)) cd (targets_opt_to_list targs) in
                    let c_env' = c_env_update ctxt.ctxt_c_env c cd' in
                    {ctxt with ctxt_c_env = c_env'}
                  end
             | (Nk_typeconstr p | Nk_class p) -> 
                begin 
                  let td' = List.fold_left (fun td t -> type_defs_rename_type l td p t (Name.strip_lskip n'))
                     ctxt.all_tdefs (targets_opt_to_list targs)
                  in
                  {ctxt with all_tdefs = td'}
                end
            | Nk_module m ->
                let mod_descr = lookup_mod (defn_ctxt_to_env ctxt) id in
                let mod_name = Path.to_string mod_descr.mod_binding in
                let tr' = List.fold_left (fun tr t -> mod_target_rep_rename t mod_name (Name.strip_lskip n') l tr) mod_descr.mod_target_rep (targets_opt_to_list targs) in
                let e_env' = Pfmap.insert ctxt.ctxt_e_env (mod_descr.mod_binding, {mod_descr with mod_target_rep = tr'}) in
                {ctxt with ctxt_e_env = e_env'}
          end in
          (ctxt', def')
      | Ast.Declaration(Ast.Decl_rename_current_module_decl(sk1, target_opt, sk2, component_sk, sk3, xl')) ->
          let n' = Name.from_x xl' in
          let targs = check_target_opt target_opt in
          let def' = Some (Declaration (Decl_rename_current_module (sk1, targs, sk2, component_sk, sk3, n'))) in
          let mod_name = Path.to_string (Path.mk_path_list (List.rev mod_path)) in
          let tr' = List.fold_left (fun tr t -> mod_target_rep_rename t mod_name (Name.strip_lskip n') l tr) ctxt.ctxt_mod_target_rep (targets_opt_to_list targs) in
          ({ctxt with ctxt_mod_target_rep = tr'}, def') 
      | Ast.Declaration(Ast.Decl_pattern_match_decl (sk1, target_opt, sk2, ex_set, type_id, tnvars, sk3, sk4, constrs, sk5, semi, sk6, elim_opt)) ->
          let targs = check_target_opt target_opt in
          let tvs_tast = List.map ast_tnvar_to_tnvar tnvars in
          let tparams_t = List.map (fun tnv -> tnvar_to_type (fst (tnvar_to_types_tnvar tnv))) tvs_tast in

          let p = lookup_p "" (defn_ctxt_to_env ctxt) type_id in
          let p_id = {id_path = Id_some (Ident.from_id type_id); 
              id_locn = l;
              descr = p;
              instantiation = []; } in  
          let constr_ids = List.map (fun (id, sk) -> (fst (component_term_id_lookup l ctxt (Ast.Component_function None) id), sk)) constrs in
          let constr_ids_seplist = Seplist.from_list_suffix constr_ids sk5 semi in

          let elim_id_opt = begin match elim_opt with 
              Ast.Elim_opt_none     -> None
            | Ast.Elim_opt_some(id) -> Some (fst (component_term_id_lookup l ctxt (Ast.Component_function None) id))
          end in
          let def' = Some (Declaration (Decl_pattern_match_decl (sk1, targs, sk2, ex_set, p_id, tvs_tast, sk3, sk4, constr_ids_seplist, sk6, elim_id_opt))) in

          let constr_family = {
            constr_list = List.map (fun (id, _) -> id.descr) constr_ids;
            constr_case_fun = Util.option_map (fun id -> id.descr) elim_id_opt;
            constr_exhaustive = (match ex_set with
              | Ast.Exhaustivity_setting_exhaustive   _ -> true
              | Ast.Exhaustivity_setting_inexhaustive _ -> false);
            constr_default = false;
            constr_targets = targets_opt_to_set target_opt;
          } in
          let _ = check_constr_family l (defn_ctxt_to_env ctxt) { t = Tapp (tparams_t, p) } constr_family in
          let ctxt' = {ctxt with all_tdefs = type_defs_add_constr_family l ctxt.all_tdefs p constr_family} in 
          (ctxt', def')	  
      | Ast.Declaration(Ast.Decl_termination_argument_decl (sk1, target_opt, sk2, id, sk3, term_setting)) ->
          let targs = check_target_opt target_opt in
          let (c_id, c_descr) = component_term_id_lookup l ctxt (Ast.Component_function None) id in

          let ts = targets_opt_to_set target_opt in
          let tsm = Targetset.fold (fun t r -> Targetmap.insert r (t,term_setting)) ts c_descr.termination_setting in
          let c_env' = c_env_update ctxt.ctxt_c_env c_id.descr {c_descr with termination_setting = tsm} in

          let def' = Some (Declaration (Decl_termination_argument (sk1, targs, sk2, c_id, sk3, term_setting))) in
          ({ctxt with ctxt_c_env = c_env'}, def') 
      | Ast.Declaration(Ast.Decl_target_rep_decl (sk1, target, sk2, Ast.Target_rep_lhs_term(sk3, comp, id, args), sk4, rhs)) ->
          check_declare_target_rep_term backend_targets mod_path l ctxt sk1 target (Ast.combine_lex_skips sk2 sk3) comp id args sk4 rhs
      | Ast.Declaration(Ast.Decl_target_rep_decl (sk1, target, sk2, Ast.Target_rep_lhs_type(sk3, Ast.Component_type sk4, x, tnvars), sk5, Ast.Target_rep_rhs_type_replacement typ)) ->
          check_declare_target_rep_type backend_targets mod_path l ctxt sk1 target (Ast.combine_lex_skips sk2 sk3) sk4 x tnvars sk5 typ 
      | Ast.Declaration(Ast.Decl_target_rep_decl _) ->
          raise (Reporting_basic.err_type l "illformed target-representation declaration")
      | Ast.Declaration(Ast.Decl_set_flag_decl (_, _, _, _, _)) ->
          let _ = prerr_endline "set flag declaration encountered" in
            ctxt, None
      | Ast.Declaration(Ast.Decl_compile_message_decl (sk1, targets_opt, sk2, id, sk3, sk4, msg)) ->
        begin
          let (c_id, c_descr) = component_term_id_lookup l ctxt (Ast.Component_function None) id in

          let ts = targets_opt_to_set targets_opt in
          let tr = Targetset.fold (fun t r -> Targetmap.insert r (t, msg)) ts c_descr.compile_message in
          let c_descr' = {c_descr with compile_message = tr} in
          let ctxt' = {ctxt with ctxt_c_env = c_env_update ctxt.ctxt_c_env c_id.descr c_descr'} in

          let def' = Declaration (Decl_compile_message (sk1, check_target_opt targets_opt, sk2, c_id, sk3, sk4, msg)) in
          (ctxt', Some def')
        end
      | Ast.Declaration(Ast.Decl_ascii_rep_decl(sk1, targets_opt, sk2, component, source_id, sk3, sk4, target_name)) ->
          let target_name = Name.from_string target_name in
          
          let _ = (if Util.is_simple_ident_string (Name.to_string target_name) then () else
                     raise (Reporting_basic.err_type l "non-ascii ascii representation provided")) in
          let (nk, p) = lookup_name (defn_ctxt_to_env ctxt) (Some component) source_id in
          let nk_id = { id_path = Id_some (Ident.from_id source_id); 
                        id_locn = l; 
                        descr = nk; 
                        instantiation = [] } in
          let def' = Declaration (Decl_ascii_rep (sk1, check_target_opt targets_opt, sk2, component, nk_id, sk3, sk4, target_name)) in
          let ctxt' = (* update context *) begin
            match nk with
              | (Nk_field const_descr_ref | Nk_constr const_descr_ref | Nk_const const_descr_ref) ->
                  let ctxt' = if (targets_opt = None) then begin
                    match component with 
                      | Ast.Component_function _ -> 
                          add_v_to_ctxt ctxt (target_name, const_descr_ref) 
                      | _ -> add_f_to_ctxt ctxt (target_name, const_descr_ref)
                  end else ctxt in

                  let const_descr = Typed_ast.c_env_lookup Ast.Unknown ctxt.ctxt_c_env const_descr_ref in
                  let tr = Targetset.fold (fun t r -> Targetmap.insert r (t,(l, target_name))) (targets_opt_to_set targets_opt) const_descr.target_ascii_rep in
                  let const_descr = { const_descr with target_ascii_rep = tr } in
                  let cenv = Typed_ast.c_env_update ctxt.ctxt_c_env const_descr_ref const_descr in
                  { ctxt' with ctxt_c_env = cenv} 

              | (Nk_module _) ->
                    raise (Reporting_basic.err_todo true l "ascii representation for modules not implemented yet")
              | (Nk_typeconstr p | Nk_class p) ->
                    raise (Reporting_basic.err_todo true l "ascii representation for types not implemented yet")
          end in
          (ctxt', Some def')
      | Ast.Module(sk1,xl,sk2,sk3,Ast.Defs(defs),sk4) ->
          let l' = Ast.xl_to_l xl in
          let n' = Name.from_x xl in
          let n = Name.strip_lskip n' in 
          let ctxt1 = ctxt_begin_submodule ctxt in
          let (new_ctxt,ds) = check_defs_internal backend_targets (mod_path @ [n]) ctxt1 defs in
          let ctxt2 = ctxt_end_submodule l' ctxt mod_path n new_ctxt in
            (ctxt2,
             Some (Module(sk1,(n',l'),Path.mk_path mod_path n,sk2,sk3,ds,sk4)))
      | Ast.Rename(sk1, xl', sk2, id) ->
          let l' = Ast.xl_to_l xl' in
          let n = Name.from_x xl' in 
          let mod_descr = lookup_mod (defn_ctxt_to_env ctxt) id in
          
            add_m_alias_to_ctxt l' ctxt (Name.strip_lskip n) mod_descr.mod_binding,
              Some (Rename(sk1,
                          (n,l'), 
                          Path.mk_path mod_path (Name.strip_lskip n),
                          sk2,
                          { id_path = Id_some (Ident.from_id id);
                            id_locn = l;
                            descr = mod_descr.mod_binding;
                            instantiation = []; }))
      | Ast.Open_import_target(oi,target_opt, ml) ->  
          let targs = check_target_opt target_opt in
          (ctxt, Some (OpenImportTarget(oi, targs, ml)))
      | Ast.Open_import(oi,is) -> 
          let mod_descrs = List.map (lookup_mod (defn_ctxt_to_env ctxt)) is in

          let mod_descr_ids = List.map2 (fun i descr -> (
              { id_path = Id_some (Ident.from_id i);
                id_locn = l;
                descr = descr.mod_binding;
                instantiation = []; })) is mod_descrs in

          let (do_open, do_include) = match oi with
            | Ast.OI_open _ -> (true, false)
            | Ast.OI_import _ -> (false, false)
            | Ast.OI_open_import _ -> (true, false)
            | Ast.OI_include _ -> (true, true)
            | Ast.OI_include_import _ -> (true, true)
          in
          let ctxt' = if do_open then 
                        { ctxt with cur_env = List.fold_left (fun cur_env descr -> local_env_union cur_env descr.mod_env) ctxt.cur_env mod_descrs} 
                      else ctxt in
          let ctxt'' = if do_include then 
                        { ctxt' with export_env = List.fold_left (fun cur_env descr -> local_env_union cur_env descr.mod_env) ctxt'.export_env mod_descrs} 
                      else ctxt' in

          (ctxt'', Some (OpenImport(oi, mod_descr_ids)))
      | Ast.Indreln(sk, target_opt, names, clauses) ->
          let module T = struct include T let targets = backend_targets end in
          let module Checker = Make_checker(T) in
          let target_opt_checked = check_target_opt target_opt in
          let target_set_opt = targets_opt_to_set_opt target_opt in
          let (ns,cls,e_v,Tconstraints(tnvs,constraints,lconstraints)) = 
            Checker.check_indrels ctxt mod_path target_set_opt l names clauses 
          in 
          let module Conv = Convert_relations.Converter(struct let env_opt = None let avoid = None end) in
          let module C = Exps_in_context(struct let env_opt = None let avoid = None end) in
          let newctxt = add_let_defs_to_ctxt mod_path ctxt (TNset.elements tnvs)
            constraints lconstraints
            K_relation target_set_opt e_v in

          let add_const_ns (RName(sk1, rel_name, _, sk2, rel_type, witness_opt, check_opt, indfns_opt, sk3)) = begin
              let n = Name.strip_lskip rel_name in
              let n_ref =  match Nfmap.apply newctxt.cur_env.v_env n with
                 | Some(r) -> r
                 | _ -> raise (Reporting_basic.err_unreachable l "n should have been added just before") in
             (RName(sk1, rel_name, n_ref, sk2, rel_type, witness_opt, check_opt, indfns_opt, sk3))
          end in 
          let ns' = Seplist.map add_const_ns ns in

          (* build substitution *)
          let sub = begin
            let var_subst = Seplist.fold_left (fun (RName(_,name,r_ref,_,typschm, _,_,_,_)) subst ->
              begin
    	        let name = Name.strip_lskip name in
                let name_d = c_env_lookup l newctxt.ctxt_c_env r_ref in
                let id = { id_path = Id_some (Ident.mk_ident None [] name); 
                           id_locn = l; descr = r_ref; 
                           instantiation = List.map tnvar_to_type name_d.const_tparams } in
                let name_exp = C.mk_const l id (Some (name_d.const_type)) in
                Nfmap.insert subst (name, Sub name_exp)
              end) Nfmap.empty ns' in
            (TNfmap.empty, var_subst) 
          end in

          let add_const_rule (Rule (name_opt, s1, s1b, qnames, s2, e_opt, s3, rname, _, es), l) = begin
              let n = Name.strip_lskip rname.term in
              let n_ref =  match Nfmap.apply newctxt.cur_env.v_env n with
                 | Some(r) -> r
                 | _ -> raise (Reporting_basic.err_unreachable l "n should have been added just before") in
              let e_opt' = Util.option_map (C.exp_subst sub) e_opt in
             (Rule (name_opt, s1, s1b, qnames, s2, e_opt', s3, rname, n_ref, es), l)
          end in 
          let cls' = Seplist.map add_const_rule cls in
          let newctxt = Conv.gen_witness_type_info l mod_path newctxt ns' cls' in
          let newctxt = Conv.gen_witness_check_info l mod_path newctxt ns' cls' in
          let newctxt = Conv.gen_fns_info l mod_path newctxt ns' cls' in
            (newctxt,
             (Some (Indreln(sk,target_opt_checked,ns',cls'))))
      | Ast.Spec_def(val_spec) ->
          let (ctxt,vs) = check_val_spec l mod_path ctxt val_spec in
            (ctxt, Some (Val_spec(vs)))
      | Ast.Class(class_decl,sk2,xl,tnv,sk4,specs,sk5) ->
          (* extract class_name cn / cn', the free type variable tv, location l' and full class path p *)
          let l' = Ast.xl_to_l xl in
          let tnvar = ast_tnvar_to_tnvar tnv in 
          let (tnvar_types, _) = tnvar_to_types_tnvar tnvar in

          let cn = Name.from_x xl in
          let cn' = Name.strip_lskip cn in
          let p = Path.mk_path mod_path cn' in

          (* check whether the name of the type class is already used. It lives in the same namespace as types. *)
          let () = 
            match Nfmap.apply ctxt.new_defs.p_env cn' with
              | None -> ()
              | Some(p, _) ->
                  begin
                    match Pfmap.apply ctxt.all_tdefs p with
                      | None ->
                          raise (Reporting_basic.err_general true l "invariant in typechecking type classes broken")
                      | Some(Tc_class _) ->
                          raise (Reporting_basic.err_type_pp l' "duplicate type class definition" 
                            Name.pp cn')
                      | Some(Tc_type _) ->
                          raise (Reporting_basic.err_type_pp l' "type class already defined as a type constructor" 
                            Name.pp cn')
                  end
          in

          (* typecheck the methods inside the type class declaration *)
          let (ctxt',vspecs,methods) = 
            List.fold_left
              (fun (ctxt,vs,methods) (a,b,c,d,e,f,l) ->
                 let (tc,tc_d,ctxt,src_t,targs,v) = check_class_spec l mod_path ctxt p tnvar_types (a,b,c,d,e,f)
                 in
                   (ctxt,
                    v::vs,
                    ((Path.get_name tc_d.const_binding, l), tc, src_t, targs)::methods))
              (ctxt,[],[])
              specs
          in

          (****************************************************************************************)
          (* Build a record type for the class's dictionaries                                     *)
          (* The record is defined here. It is used by the dictionary passing style macros.       *)
          (* It could - logically - be introduced by the class_to_record macro. However, this     *)
          (* would prevent the user from referring the the fields manually. For example,          *)
          (* renaming such a field for a certain backend would not be possible, since the field   *)
          (* just does not exist, when the renaming is processed.                                 *)
          (****************************************************************************************)

          let build_field_name_name n = Name.rename (fun x -> Ulib.Text.(^^^) x (r"_method")) n in
          let build_field_name c = build_field_name_name (const_descr_ref_to_ascii_name ctxt'.ctxt_c_env c) in

          let dict_type_name = (Name.lskip_rename (fun x -> Ulib.Text.(^^^) x (r"_class")) cn) in
         
          let tparams = [tnvar_types] in
          let tparams_t = List.map tnvar_to_type tparams in
          let type_path = Path.mk_path mod_path (Name.strip_lskip dict_type_name) in

          let ctxt'' = build_type_def_help mod_path ctxt' [tnv] (dict_type_name, l') None None in
          let (recs', ctxt'') =
            add_record_to_ctxt 
              (fun fname l t targs ->
                 { const_binding = Path.mk_path mod_path fname;
                   const_tparams = tparams;
                   const_class = [];
                   const_no_class = Targetmap.empty;
                   const_ranges = [];
                   const_type = { t = Tfn ({ t = Tapp (tparams_t, type_path) }, t) };
                   spec_l = l;
                   env_tag = K_field;
                   const_targets = targs;
                   relation_info = None;
                   termination_setting = Targetmap.empty;
                   target_rename = Targetmap.empty;
                   target_rep = Targetmap.empty;
                   target_ascii_rep = Targetmap.empty;
                   compile_message = Targetmap.empty })
              ctxt''
              (Seplist.from_list (List.map 
                                    (fun ((n,l),c,src_t,targs) -> 
                                       (((Name.add_lskip (build_field_name c),l), None, src_t, targs),None)) 
                                    methods))
          in
          let field_refs = Seplist.to_list_map (fun (_, f, _, _) -> f) recs' in
          let ctxt''' = {ctxt'' with all_tdefs = type_defs_update_fields l ctxt''.all_tdefs type_path (List.rev field_refs)} in 


          (* add the class as a type to the local environment *)
          let class_d = { 
             class_tparam = tnvar_types;
             class_record = type_path; 
             class_methods = List.combine (List.map (fun (_,r,_,_) -> r) methods) field_refs;
             class_rename = Targetmap.empty;
             class_target_rep = Targetmap.empty;
     	     class_is_inline = (match class_decl with
                                 | Ast.Class_decl _ -> false
                                 | Ast.Class_inline_decl _ -> true)
          } in

          let ctxt''' = add_d_to_ctxt ctxt''' p (Tc_class class_d) in
          let ctxt''' = add_p_to_ctxt ctxt''' (cn', (p, l')) in

          (* all done, return the result *)
          (ctxt''', Some (Class(class_decl,sk2,(cn,l'),tnvar,p,sk4,List.rev vspecs,sk5)))
      | Ast.Instance(inst_decl,Ast.Is(cs,sk2,id,typ,sk3),vals,sk4) ->
          let (src_cs, tyvars, tnvarset, (sem_cs,sem_rs)) =
            check_constraint_prefix ctxt cs 
          in
          let () = check_free_tvs tnvarset typ in
          let src_t = 
            typ_to_src_t false anon_error ignore ignore (defn_ctxt_to_env ctxt) typ
          in


          let (used_tvs, type_path) = check_instance_type_shape ctxt src_t in
          let unused_tvs = TNset.diff tnvarset used_tvs in
          let _ = 
            if not (TNset.is_empty unused_tvs) then
              raise (Reporting_basic.err_type_pp l "instance type does not use all type variables"
                TNset.pp unused_tvs)
          in
          let (p, p_d) = lookup_class_p (defn_ctxt_to_env ctxt) id in
          let class_methods = (* Instantiate the type of methods and get their name*)
            begin
              let subst = TNfmap.insert TNfmap.empty (p_d.class_tparam, src_t.typ) in
              let format_method (method_ref, _ (* field_ref *)) = begin
		let m_d = c_env_lookup l ctxt.ctxt_c_env method_ref in
                let m_n = Path.get_name m_d.const_binding in
                let ty = type_subst subst m_d.const_type in
                (method_ref, m_n, ty)
              end in
              List.map format_method p_d.class_methods
            end
          in

          (* consistency checks for default instances *)
          let is_default_inst = (match inst_decl with Ast.Inst_default _ -> true | Ast.Inst_decl _ -> false) in
          let is_default_inst_real = is_var_type (src_t_to_t src_t) in
          let is_allowed_instance = is_var_type (src_t_to_t src_t) || is_instance_type (src_t_to_t src_t) in

          let _ = if (is_default_inst && (not is_default_inst_real)) then
                    raise (Reporting_basic.err_type l "instance not general enough for a default instance") else () in
          let _ = if ((not is_default_inst) && is_default_inst_real) then
                    raise (Reporting_basic.err_type l "instance too general; consider declaring as default instance") else () in
          let _ = if (not is_allowed_instance) then
                    raise (Reporting_basic.err_type l "instance type too special") else () in

          (* check that there is no instance already *)
          let _ =  match Types.get_matching_instance ctxt.all_tdefs (p, src_t.typ) ctxt.all_instances  with
                     | Some (i, _) -> begin
                        if i.inst_is_default then () else
                        (Reporting.report_warning (defn_ctxt_to_env ctxt) (Reporting.Warn_overriden_instance (l, src_t, i)))
                     end
                     | None -> ()
          in

          let instance_name = 
            Name.from_rope
              (Ulib.Text.concat (r"_")
                 [r"Instance";
                  Name.to_rope (Path.to_name p);
                  type_path])
          in
          let instance_path = mod_path @ [instance_name] in

          (** Make instances defined in the header of the instance declaration available during checking methods *)
          let mk_temp_instance p tv = {
             inst_l = Ast.Trans (false, "Internal Instance", Some l);
             inst_binding = Path.mk_path instance_path (Name.from_string "temp");
             inst_is_default = false;
	     inst_tyvars = [];
	     inst_constraints = [];
	     inst_class = p;
	     inst_methods = (* this violates the invariant that instances should implement all the methods of their parent class. However, this should not matter much, since it is only temporary and used during typechecking*) [(nil_const_descr_ref, nil_const_descr_ref)];
	     inst_type = tnvar_to_type tv;
	     inst_dict = nil_const_descr_ref (* only temporary *);
          } in
          let tmp_all_inst = 
            List.fold_left 
              (fun instances (p, tv) -> 
                 fst (i_env_add instances (mk_temp_instance p tv)))
              ctxt.all_instances
              sem_cs in
          let ctxt_inst0 = { (ctxt_begin_submodule ctxt) with all_instances = tmp_all_inst } in

          (* typecheck the inside of the instance declaration *)
          let (v_env_inst,ctxt_inst,vdefs) = 
            List.fold_left
              (fun (v_env_inst,ctxt,vs) (v,l) ->
                 (* use the val-def normal checking. Notice however, that check_val_def gets the argument
                    [Some src_t.typ] here, while it gets [None] in all *)
                 let (ctxt',e_v',vd,Tconstraints(tnvs,constraints,lconstraints)) = 
                   check_val_def_instance backend_targets instance_path (src_t.typ) l ctxt v 
                 in

                 (* make sure there are no extra contraints and no extra free type variables*)
                 let _ = assert (constraints = []) in
                 let _ = assert (lconstraints = []) in
                 let _ = assert (TNset.is_empty tnvs) in

                 (* we used normal typechecking via check_val_def, so no lets adapt the 
                    resulting functions and check that they have the expected type. *)
                 let fix_def_in_ctxt (ctxt,v_env) n (t, l) = begin
                   let n_ref = match Nfmap.apply ctxt.new_defs.v_env n with
                     | Some r -> r
                     | _ -> raise (Reporting_basic.err_unreachable l "n should have been added by check_val_def_instance, it is in e_v' after all")
                   in
                   let n_d = c_env_lookup l ctxt.ctxt_c_env n_ref in

                   (* check that [n] has the right type / check whether it is in the set of methods *)
                   let _ = try
  		       let (_, _, n_class_ty) = List.find (fun (_, n', _) -> Name.compare n n' = 0) class_methods in
                       if Types.check_equal ctxt.all_tdefs n_class_ty n_d.const_type then 
                          (* type matches, everything OK *) ()
                       else begin
                         let t_should = Types.t_to_string n_class_ty in
                         let t_is = Types.t_to_string  n_d.const_type in
                         let err_message = ("Instance method '" ^ Name.to_string n ^ "' is excepted to have type\n   " ^
                               t_should^"\nbut has type\n   "^t_is) in
                         raise (Reporting_basic.err_type l err_message)
                       end
                     with Not_found -> raise (Reporting_basic.err_type_pp l "unknown class method" Name.pp n)
                   in

                   let _ = if not (Nfmap.in_dom n v_env) then () else raise (Reporting_basic.err_type_pp l "duplicate definition in an instance" Name.pp n) in
                   let v_env' = Nfmap.insert v_env (n, n_ref) in
                   
                   let n_d' = {n_d with const_tparams = tyvars;
                                        const_class = sem_cs;
					const_ranges = sem_rs;
                                        env_tag = K_instance}
                   in
                   let c_env' = c_env_update ctxt.ctxt_c_env n_ref n_d' in
		     ({ctxt with ctxt_c_env = c_env'}, v_env')
                 end in
                 let (ctxt'',v_env_inst') = Nfmap.fold fix_def_in_ctxt (ctxt',v_env_inst) e_v' in
                   (v_env_inst', ctxt'', vd::vs))
              (Nfmap.empty, ctxt_inst0,[])              
              vals
          in
          let ctxt_inst = {ctxt_inst with all_instances = ctxt.all_instances} in
          let inst_methods = (* All methods present? If not, raise an exception. As well build a associative list that maps class methods to instance ones. *)
            List.map (fun (cm_ref,n,_) ->
                 match Nfmap.apply v_env_inst n with
                   | Some im_ref -> (cm_ref, im_ref)
                   | None -> raise (Reporting_basic.err_type_pp l "missing class method" Name.pp n)
               ) class_methods in


          (* add a dictionary constant *)
          let dict_name = Name.from_string (String.uncapitalize (Name.to_string instance_name) ^ "_dict") in

          let dict_type = class_descr_get_dict_type p_d src_t.typ in

          let dict_d =
            { const_binding = Path.mk_path mod_path dict_name;
              const_tparams = tyvars;
              const_class = sem_cs;
              const_no_class = Targetmap.empty;
              const_ranges = [];
              const_type = dict_type;
              env_tag = K_let;
              spec_l = Ast.Trans(true, "instance_to_module", Some l);
              const_targets = Target.all_targets;
              relation_info = None;
              termination_setting = Targetmap.empty;
              target_rename = Targetmap.empty;
              target_rep = Targetmap.empty;
              target_ascii_rep = Targetmap.empty;
              compile_message = Targetmap.empty;
            }
          in
          let (c_env',dict_ref) = Typed_ast_syntax.c_env_store ctxt_inst.ctxt_c_env dict_d in
          let ctxt_inst = {ctxt_inst with ctxt_c_env = c_env'} in
 
          (* move new definitions into special module, since here the old context is thrown away and ctxt.new_defs is used,
             it afterwards becomes irrelevant thet ctxt_inst.new_defs contains more definitions than ctxt. *)
          let ctxt = ctxt_end_submodule l ctxt mod_path instance_name ctxt_inst in
          let ctxt = add_v_to_ctxt ctxt (dict_name, dict_ref) in

          (* store everything *)
          let inst = {
	      inst_l = l;
	      inst_binding = Path.mk_path mod_path instance_name;
              inst_is_default = is_default_inst;
	      inst_class = p;
	      inst_type = src_t.typ;
	      inst_tyvars = tyvars;
	      inst_constraints = sem_cs;
	      inst_methods = inst_methods;
	      inst_dict = dict_ref;
     	  } in
          let (ctxt', i_ref) = add_instance_to_ctxt ctxt inst in
            (ctxt',
             Some (Instance(inst_decl,i_ref,(src_cs,sk2,Ident.from_id id, p, src_t, sk3), List.rev vdefs, sk4)))


and check_defs_internal (backend_targets : Targetset.t) (mod_path : Name.t list)
              (ctxt : defn_ctxt) defs
              : defn_ctxt * def list =
  match defs with
    | [] -> (ctxt, [])
    | (Ast.Def_l(d_aux,l) as d,sk,semi)::ds ->
        let s = if semi then Some(sk) else None in
        let new_backend_targets = get_effective_backends backend_targets d_aux in 
        let (ctxt',d) = check_def new_backend_targets mod_path ctxt d sk semi in
        let (ctxt'',ds) = check_defs_internal backend_targets mod_path ctxt' ds in
        begin
          match d with
            | None -> (ctxt'', ds)
            | Some d -> (ctxt'', ((d,s),l,ctxt'.cur_env)::ds)
        end


(* -------------------------------------------------------------------------- *)
(* the interface                                                              *)
(* -------------------------------------------------------------------------- *)

let check_defs backend_targets mod_name filename mod_in_output (env : env) (Ast.Defs(defs), end_lex_skips) =
  let ctxt = { all_tdefs = env.t_env;
               new_tdefs = [];  
               all_instances = env.i_env;
               new_instances = [];
               cur_env = env.local_env;
               new_defs = empty_local_env;
               export_env = empty_local_env;
               lemmata_labels = NameSet.empty;
               ctxt_c_env = env.c_env;
               ctxt_mod_target_rep = Targetmap.empty;
               ctxt_e_env = env.e_env;
               ctxt_mod_in_output = mod_in_output }
  in
  let (ctxt,checked_defs) = check_defs_internal backend_targets [mod_name] ctxt defs in

  let new_env = begin
    (* let ctxt only modify the gloabl environment *)
    let env' = { (defn_ctxt_to_env ctxt) with local_env = env.local_env} in 

    (* put the local environment into a new module *)
    let mod_binding = Path.mk_path [] mod_name in
    let md = { mod_env = ctxt.export_env; 
               mod_binding = mod_binding; 
               mod_target_rep = ctxt.ctxt_mod_target_rep;
               mod_in_output = mod_in_output;
               mod_filename = Some filename } in

    (* add the module *)
    let new_e_env = Pfmap.insert env'.e_env (mod_binding, md) in
    let new_local' = { env'.local_env with m_env = Nfmap.insert env'.local_env.m_env (mod_name,mod_binding) } in
    {env' with local_env = new_local'; e_env = new_e_env}
  end in

  (new_env, (checked_defs, end_lex_skips))

