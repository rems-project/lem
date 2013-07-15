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

(* Support for changing the names of top-level definitions, including removal of
 * nested modules.  We also figure out how much of each path needs to be
 * printed.
 *) 

open Typed_ast
open Util

module NKmap = 
  Finite_map.Fmap_map(struct 
                        type t = name_kind
                        let compare = Pervasives.compare 
                      end)

type top_level_renames = (Name.t list * Name.t) Types.Pfmap.t NKmap.t 

let add_rename (renames : (top_level_renames * Typed_ast.NameSet.t)) (nk : name_kind) 
  (old_p : Path.t) (new_p : (Name.t list * Name.t)) :
  (top_level_renames * Typed_ast.NameSet.t) =
  let r = 
    match NKmap.apply (fst renames) nk with
      | None -> Types.Pfmap.empty
      | Some(r) -> r
  in
  let new_r = Types.Pfmap.insert r (old_p, new_p) in
  let new_renames = NKmap.insert (fst renames) (nk,new_r) in
  let new_used_names = NameSet.add (snd new_p) (snd renames) in
    (new_renames, new_used_names)

let add_renames (renames : (top_level_renames * Typed_ast.NameSet.t))
  (newL : (name_kind * Path.t * Path.t) list) =
  List.fold_left (fun r (nk, old_p, new_p) -> add_rename r nk old_p (Path.to_name_list new_p)) renames
  newL


let compute_rename (path : Name.t list) 
      (f : Ast.l -> name_kind -> Name.t list -> Name.t -> NameSet.t -> (Name.t list * Name.t) option)
      (renames : (top_level_renames * Typed_ast.NameSet.t)) (l : Ast.l) (nk : name_kind) (n : Name.t)
      : top_level_renames * Typed_ast.NameSet.t =
  match f l nk path n (snd renames) with
    | None -> renames
    | Some(new_p) -> add_rename renames nk (Path.mk_path path n) new_p

(* given a constant description and a target option, return whether this
   constant might appear in output for this target. It cannot apear
   if it is inlined or not defined for this target *)
let constant_used_for_target targ d =
  match targ with 
    None -> false 
  | Some t -> 
      if (Targetmap.in_dom t d.substitutions) then false else
     (match d.env_tag with
       | K_method -> true
       | K_instance -> true
       | K_let -> true
       | K_val -> false
       | K_target (let_def, defined_targets) -> let_def || Targetset.mem t defined_targets
     )

let compute_renames_v targ path f renames e_v =
  Nfmap.fold 
    (fun renames n v -> 
       let (nk, l, do_it) =
         match v with
           | Constr d -> (Nk_constr, d.constr_l, true)
           | Val d -> (Nk_const, d.spec_l, constant_used_for_target targ d)
       in
         (if do_it then compute_rename path f renames l nk n else renames))
    renames
    e_v

let compute_renames_f targ path f renames e_f =
  Nfmap.fold 
    (fun renames n d -> compute_rename path f renames d.field_l Nk_field n)
    renames
    e_f

(* TODO: classes in here too *)
let compute_renames_p targ path f renames e_p =
  Nfmap.fold 
    (fun renames n (_, l) -> compute_rename path f renames l Nk_typeconstr n)
    renames
    e_p

let rec compute_renames_m targ path f renames e_m =
  Nfmap.fold 
    (fun renames n e -> 
       if path = [] && 
          (Name.compare n (target_to_mname (Target_ocaml)) = 0 ||
           Name.compare n (target_to_mname (Target_hol))  = 0 ||
           Name.compare n (target_to_mname (Target_isa)) = 0)
       then
         renames
       else
         let renames = compute_rename path f renames Ast.Unknown Nk_module n in
           compute_renames targ (path @ [n]) f renames e.mod_env)
    renames
    e_m

and compute_renames targ path f renames e =
  let renames = compute_renames_v targ path f renames e.v_env in
  let renames = compute_renames_f targ path f renames e.f_env in
  let renames = compute_renames_p targ path f renames e.p_env in
  let renames = compute_renames_m targ path f renames e.m_env in
    renames

let apply_raw_rename_opt (renames : top_level_renames) k path (n : Name.t) =
  match NKmap.apply renames k with 
    | None -> None
    | Some(m) -> Types.Pfmap.apply m (Path.mk_path path n)

let apply_def_rename_opt (renames : top_level_renames) k path (n : Name.lskips_t) =
  match NKmap.apply renames k with 
    | None -> None
    | Some(m) -> 
        begin
          match Types.Pfmap.apply m (Path.mk_path path (Name.strip_lskip n)) with
            | None -> None
            | Some((new_p,new_n)) ->
                let new_r = Name.to_rope new_n in
                Some(Name.lskip_rename (fun _ -> new_r) n)
        end

let apply_def_rename renames k path n =
  match apply_def_rename_opt renames k path n with
    | None -> n
    | Some(n) -> n

(* The path argument here and below is the path to the binding before renaming *)
let apply_rename_opt (renames : top_level_renames) k path (n : Name.lskips_t) =
  match NKmap.apply renames k with 
    | None -> None
    | Some(m) -> 
        begin
          match Types.Pfmap.apply m (Path.mk_path path (Name.strip_lskip n)) with
            | None -> None
            | Some((new_p,new_n)) ->
                let new_r = Name.to_rope new_n in
                Some(Name.lskip_rename (fun _ -> new_r) n)
        end

let apply_def_rename renames k path n =
  match apply_def_rename_opt renames k path n with
    | None -> n
    | Some(n) -> n

let apply_rename_opt path (renames : top_level_renames) k binding set_binding id =
  match NKmap.apply renames k with 
    | None -> None
    | Some(m) ->
        begin
          match Types.Pfmap.apply m binding with
            | None -> None
            | Some((new_p,new_n)) ->
                (* TODO: be smarter about this *)
                let p = Path.mk_path new_p new_n in
                let local_new_p = 
                  match new_p with
                    | [] -> []
                    | x::y ->
                        if Name.compare x (List.hd path) = 0 then
                          y
                        else
                          x::y
                in
                let i = 
                  Ident.mk_ident (List.map (fun x -> (Name.add_lskip x, None)) local_new_p)
                    (Name.add_lskip new_n)
                    Ast.Unknown
                in
                  Some({ id with id_path = Id_some i;
                                 descr = set_binding id.descr p })
        end

let apply_rename path renames k binding set_binding id =
  match apply_rename_opt path renames k binding set_binding id with
    | None -> id
    | Some(n) -> n

let rec rename_type_opt renames src_t =
  let new_term =
    match src_t.term with
      | Typ_wild(sk) -> None
      | Typ_var(sk,tv) -> None
      | Typ_len(n) -> None (* On same principle as above *)
      | Typ_fn(t1,sk,t2) -> 
          changed2
            (fun new_t1 new_t2 -> Typ_fn(new_t1,sk,new_t2))
            (rename_type_opt renames)
            t1
            (rename_type_opt renames)
            t2
      | Typ_tup(ts) ->
          option_map
            (fun new_ts -> Typ_tup(new_ts))
            (Seplist.map_changed (rename_type_opt renames) ts)
      | Typ_app(id,ts) ->
          (* TODO: Actually rename the id *)
          changed2
            (fun new_ts new_id -> Typ_app(new_id,new_ts))
            (Util.map_changed (rename_type_opt renames))
            ts
            (fun id -> (let (id_path, id_name) = (Ident.to_name_list (Path.to_ident id.descr)) in
                        apply_rename_opt id_path renames Nk_typeconstr id.descr (fun _ x -> x) id))
            id
      | Typ_paren(sk1,t,sk2) ->
          option_map
            (fun new_t -> Typ_paren(sk1,new_t,sk2))
            (rename_type_opt renames t)
  in
    option_map
      (fun new_term -> { src_t with term = new_term })
      new_term

let rec rename_type renames src_t =
  match rename_type_opt renames src_t with
    | None -> src_t
    | Some(x) -> x

let rec rename_types_type_opt renames (texp : Types.t) =    
  let new_aux =
    match texp.Types.t with
      | Types.Tvar(n) -> None
      | Types.Tfn(te1,te2) -> 
          changed2
            (fun new_t1 new_t2 -> Types.Tfn(new_t1,new_t2))
            (rename_types_type_opt renames)
            te1
            (rename_types_type_opt renames)
            te2
      | Types.Ttup(tys) -> 
          let typs_opt = Util.map_changed (rename_types_type_opt renames) tys in 
          Util.option_map (fun x -> Types.Ttup x) typs_opt
      | Types.Tapp(tys,p) -> 
          changed2
            (fun new_tys new_p -> Types.Tapp(new_tys,new_p))
            (Util.map_changed (rename_types_type_opt renames)) 
            tys
            (fun p -> let (path, n) = Ident.to_name_list (Path.to_ident p) in
                      let n_new_opt = apply_raw_rename_opt renames Nk_typeconstr path n in
                      Util.option_map (fun (p, n) -> Path.mk_path p n) n_new_opt) 
            p
      | _ -> None
  in
    option_map
      (fun new_ty -> { Types.t = new_ty })
      new_aux

let rec rename_types_type renames t =
  match rename_types_type_opt renames t with
    | None -> t
    | Some(x) -> x

let name_to_lower n = 
  if Name.starts_with_upper_letter n then
    Some(Name.uncapitalize n)
  else 
    None

let name_to_upper n = 
  if Name.starts_with_lower_letter n then
    Some(Name.capitalize n)
  else 
    None

(* TODO: add checking *)
let compute_ocaml_rename_f nk path n =
  let new_n n = 
    match nk with
      | Nk_typeconstr -> name_to_lower n
      | Nk_const -> name_to_lower n
      | Nk_constr -> name_to_upper n
      | Nk_field -> name_to_lower n
      | Nk_module -> name_to_upper n
      | Nk_class -> None
  in
    changed2
      (fun x y -> (x,y))
      (map_changed name_to_upper)
      path
      new_n
      n

let compute_target_rename_f targ =
  match targ with 
    | Some Target_ocaml -> compute_ocaml_rename_f
    | _ -> (fun nk path n -> None)

let r = Ulib.Text.of_latin1

(* TODO: Check that the new names are good *)
let compute_module_rename_f _ nk path n _ =
  match path with
    | [] | [_] -> None
    | x::y -> 
        let new_n = 
          Name.from_rope (Ulib.Text.concat (r"_") (List.map Name.to_rope (y @ [n])))
        in
          Some([x],new_n)

module Ctxt = struct
  let check = None
  let avoid = None
end

module E = Exps_in_context(Ctxt)
(* TODO: This I is back-end specific *)
module M = Macro_expander.Expander(Ctxt)

let rename_def_pat_macro path (renames : top_level_renames) top_level p = 
  let l = p.locn in
  let t = rename_types_type renames p.typ in
    match p.term with
      | P_as(sk1,p,sk,(n,l'),sk2) ->
          option_map 
            (fun n -> E.mk_pas l sk1 p sk (n,l') sk2 (Some(t)))
            (apply_def_rename_opt renames Nk_const path n)
      | P_var(n) ->
          option_map
            (fun n -> E.mk_pvar l n t)
            (apply_def_rename_opt renames Nk_const path n)
      | _ -> None
             
let set_constr_binding c p = { c with constr_binding = p }
let set_field_binding c p = { c with field_binding = p }
let set_const_binding c p = { c with const_binding = p }


let rename_pat_macro path renames top_level p =
  let t = rename_types_type renames p.typ in
  let l = p.locn in
    match p.term with
      | P_constr(c,ps) ->
          option_map
            (fun c -> E.mk_pconstr l c ps (Some(t)))
            (apply_rename_opt path renames Nk_constr c.descr.constr_binding set_constr_binding c)
      | P_record(sk1,fields,sk2) ->
          option_map
            (fun new_fields -> 
               E.mk_precord l sk1 new_fields sk2 (Some(t)))
            (Seplist.map_changed
               (fun (fid,sk,p) ->
                  option_map
                    (fun new_fid -> (new_fid,sk,p))
                    (apply_rename_opt path renames Nk_field 
                       fid.descr.field_binding set_field_binding fid))
               fields)
      | P_typ(sk1,p,sk2,src_t,sk3) ->
          option_map 
            (fun new_t -> E.mk_ptyp l sk1 p sk2 new_t sk3 (Some(t)))
            (rename_type_opt renames src_t)
      | _ -> None

let rename_def_pat path renames p =
  M.expand_pat (Macro_expander.Top_level,Macro_expander.Bind) p 
    (rename_types_type renames,
     rename_type renames,
     Macro_expander.list_to_bool_mac 
       [rename_def_pat_macro path renames;
        rename_pat_macro path renames])

let rename_pat path renames p =
  M.expand_pat (Macro_expander.Top_level,Macro_expander.Param) p 
    (rename_types_type renames, rename_type renames, rename_pat_macro path renames)

let rename_exp_macro vars path renames (e : exp) : exp option =
  let do_fields fields =
    Seplist.map_changed
      (fun (fid,sk,e,l) ->
         option_map
           (fun new_fid -> (new_fid,sk,e,l))
           (apply_rename_opt path renames Nk_field fid.descr.field_binding 
              set_field_binding fid))
      fields
  in
  let l = exp_to_locn e in
  let t = rename_types_type renames (exp_to_typ e) in
    match E.exp_to_term e with
      | Var(v) ->
          if not (NameSet.mem (Name.strip_lskip v) vars) then None else
          option_map
            (fun n -> E.mk_var l n t)
            (apply_def_rename_opt renames Nk_const path v)         
      | Constant(c) ->
          option_map
            (fun new_c -> E.mk_const l new_c (Some(t)))
            (apply_rename_opt path renames Nk_const c.descr.const_binding set_const_binding c)
      | Constructor(c) ->
          option_map
            (fun c -> E.mk_constr l c (Some(t)))
            (apply_rename_opt path renames Nk_constr c.descr.constr_binding 
               set_constr_binding c)
      | Tup_constructor(c,sk1,es,sk2) ->
          option_map
            (fun c -> E.mk_tup_ctor l c sk1 es sk2 (Some(t)))
            (apply_rename_opt path renames Nk_constr c.descr.constr_binding 
               set_constr_binding c)
      | Record(sk1,fields,sk2) ->
          option_map
            (fun new_fields -> 
               E.mk_record l sk1 new_fields sk2 (Some(t)))
            (do_fields fields)
      | Record_coq(_, sk1, fields, sk2) ->
          (* TODO: is this right *)
          option_map
            (fun new_fields -> 
               E.mk_record_coq l sk1 new_fields sk2 (Some(t)))
            (do_fields fields)
      | Recup(sk1,e,sk2,fields,sk3) ->
          option_map
            (fun new_fields -> 
               E.mk_recup l sk1 e sk2 new_fields sk3 (Some(t)))
            (do_fields fields)
      | Field(e,sk,fid) ->
          option_map
            (fun new_fid ->
               E.mk_field l e sk new_fid (Some(t)))
            (apply_rename_opt path renames Nk_field fid.descr.field_binding 
               set_field_binding fid)
      | Typed(sk1,e,sk2,src_t,sk3) ->
          option_map 
            (fun new_t -> E.mk_typed l sk1 e sk2 new_t sk3 (Some(t)))
            (rename_type_opt renames src_t)
      | _ -> None

let rename_exp vars path renames = 
  M.expand_exp (rename_exp_macro vars path renames, rename_types_type renames, rename_type renames, rename_pat_macro path renames)

let rec rename_def renames path ((d,s),l) =
  (*let l_unk = Ast.Trans("fix_ocaml_names_defs") in*)
  let do_fields fields =
    Seplist.map
      (fun ((n,l),sk,t) ->
         ((apply_def_rename renames Nk_field path n, l),sk,rename_type renames t))
      fields
  in
  let res = 
    match d with
      | Type_def(s,tdefs) ->
          let new_tdefs = 
            Seplist.map
              (fun ((n,l),tvs,texp,tregexp) ->
                 let new_texp = 
                   match texp with
                     | Te_opaque -> Te_opaque
                     | Te_abbrev(s,t) ->
                         Te_abbrev(s, rename_type renames t)
                     | Te_record(s3,s1,fields,s2) ->
                         Te_record(s3,s1,do_fields fields,s2)
                     | Te_record_coq(s3,(n,l),s1,fields,s2) ->
                         (* TODO: Is this right for n? *)
                         let new_n = 
                           apply_def_rename renames Nk_constr path n
                         in
                           Te_record_coq(s2,(new_n,l),s1, do_fields fields, s2)
                     | Te_variant(s,vars) ->
                         let new_vars = 
                           Seplist.map
                             (fun ((n,l),s1,t) ->
                                let new_n = apply_def_rename renames Nk_constr path n in
                                let new_t = Seplist.map (rename_type renames) t 
                                in
                                  ((new_n,l),s1,new_t))
                             vars
                         in
                           Te_variant(s,new_vars)
                     | Te_variant_coq(s,vars) ->
                         (* FZ asks: this should never happen...  not implemented *)
                         failwith "Cannot happen in ocaml_fix_names_defs - variant"
                 in
                   ((apply_def_rename renames Nk_typeconstr path n,l),
                    tvs,
                    new_texp,
                    tregexp))
              tdefs
          in
            Type_def(s,new_tdefs)
      | Val_def(Let_def(s1,targets,(Let_val(p,topt,sk,e),l)),tnvs,class_constraints) ->
          let new_p = rename_def_pat path renames p in
          let new_topt =
            option_map
              (fun (sk,t) -> (sk, rename_type renames t))
              topt
          in
          let new_e = rename_exp NameSet.empty path renames e in
            Val_def(Let_def(s1,targets,(Let_val(new_p,new_topt,sk,new_e),l)),tnvs, class_constraints)
      | Val_def(Let_def(s1,targets,(Let_fun(n,ps,topt,s2,e),l)),tnvs,class_constraints) ->
          let new_n = 
            { n with term = apply_def_rename renames Nk_const path n.term } 
          in
          let new_ps = List.map (rename_pat path renames) ps in
          let new_e = rename_exp NameSet.empty path renames e in
          let new_t = 
            option_map
              (fun (sk,t) -> (sk,rename_type renames t))
              topt 
          in
            Val_def(Let_def(s1,targets,(Let_fun(new_n,new_ps,new_t,s2,new_e),l)),tnvs,class_constraints)
      | Val_def(Rec_def(s1,s2,targets,clauses),tnvs,class_constraints) ->
          let rec_defined_consts = List.fold_left (fun s (n, _, _, _, _) -> NameSet.add (Name.strip_lskip n.term) s) NameSet.empty (Seplist.to_list clauses) in
          let new_clauses =
              Seplist.map              
              (fun (n,ps,topt,s1,e) -> 
                 let new_n = 
                   { n with term = apply_def_rename renames Nk_const path n.term } 
                 in
                 let new_ps = List.map (rename_pat path renames) ps in
                 let new_t = 
                   option_map
                     (fun (sk,t) -> (sk, rename_type renames t))
                     topt 
                 in
                 let new_e = rename_exp rec_defined_consts path renames e in
                   (new_n,new_ps,new_t,s1,new_e))
              clauses
          in
            Val_def(Rec_def(s1,s2,targets,new_clauses),tnvs,class_constraints)
      | Lemma(sk,lty,targets,n_opt,sk2,e,sk3) -> 
        let new_e = rename_exp NameSet.empty path renames e in
        Lemma(sk,lty,targets,n_opt,sk2,new_e,sk3)
      | Open(s1,m) ->
          (* TODO: open*)
          Open(s1,m)
      | Module(s1,(n,l),s2,s3,ds,s4) ->
          let new_n = apply_def_rename renames Nk_module path n in
          let new_ds = 
            rename_defs renames (path @ [Name.strip_lskip n]) ds 
          in
            Module(s1,(new_n,l),s2,s3,new_ds,s4)
    | Indreln(s1,targets,names,c) ->
        let rename_annot_name (n : name_lskips_annot) = 
             let t' = rename_types_type renames n.typ in
             let n' = apply_def_rename renames Nk_const path n.term in 
             { n with typ = t'; term = n' }
        in
        Indreln(s1,
                targets,
                names, (* TODO Indreln. THis should name wihtin the names *)
                Seplist.map
                  (fun (Rule(name_opt,s0,s1,ns,s2,e_opt,s3,n,es),l) ->
                     (Rule(name_opt,
                      s0,
                      s1,
                      List.map (fun n -> QName n) (List.map rename_annot_name (List.map (fun (QName n) -> n) ns)),
                      s2,
                      Util.option_map (rename_exp NameSet.empty path renames) e_opt, 
                      s3, 
                      rename_annot_name n, 
                      List.map (rename_exp NameSet.empty path renames) es),l))
                  c)
    | x -> x (* TODO *)
  in
    ((res,s),l)

and rename_defs renames path defs =
  match defs with
    | [] -> []
    | d::ds ->
        rename_def renames path d :: rename_defs renames path ds

let get_fresh_name consts n = 
  let is_good n = not (NameSet.mem n consts) in
  if (is_good n) then None else
  Some (Name.fresh (Name.to_rope n) is_good)


(* TODO: Fix this hack for recognising library functions!*)
let library_pathL : Name.t list = 
  let targetsL = List.map target_to_mname (Targetset.elements all_targets) in
  let extraL = ["Pervasives"; "Pmap"; "Int"; "List"; "Vector"; "Set"] in
  let extranL = List.map Name.from_string extraL in
  targetsL @ extranL  

let is_lib_path path = 
  match path with 
    | [] -> true
    | p :: _ ->  List.exists (fun p' -> (Name.compare p p' = 0)) library_pathL

let prevent_lib_renames path n =
  let exceptions = [] in
  let path_n_s = (List.map Name.to_string path, Name.to_string n) in
  if (List.mem path_n_s exceptions) then false else is_lib_path path

let extend_rename_fun fix_f pre_f f targ l nk path n_org usedN = 
  match fix_f path n_org with
      Some (_, p) -> Some (Path.to_name_list p)
    | None -> begin

  (* abort if a library function should be renamed*)
  if (prevent_lib_renames path n_org) then None else

  (* first apply the user supplied renaming, pre_f *)
  let (path_user, n_user, user_rename_l_opt) = match (pre_f path n_org) with
      None -> (path, n_org, None)
    | Some (l, p) -> let (ns, n) = Path.to_name_list p in (ns, n, Some l) in

  (* then apply a target specific renaming function like
     compute_ocaml_rename_f. For example, use only capital
     constructor names in Ocaml. This might change the path as well. *)     
  let n_target_opt = 
     let n_opt = f nk path_user n_user in
       match n_opt with Some _ -> n_opt  
                      | None -> option_map (fun n -> (path_user, n_user)) user_rename_l_opt in  
  let (new_path, n_target) = match n_target_opt with Some (path_user, n) -> (path, n) | None -> (path_user, n_user) in

  (* check whether the computed name is fresh and 
     enforce it if necessary *)
  let (is_auto_renamed, n_fresh_opt) = 
     match get_fresh_name usedN n_target with
         None -> (false, n_target_opt)
       | Some n -> (true, Some (new_path, n)) in

  (* Print warning if auto renaming occured *)    
  let _ = if (not is_auto_renamed) then () else begin
          let n_new = match n_fresh_opt with Some (_, n') -> n' | None -> assert false in
          let via_opt = match user_rename_l_opt with 
               None -> None 
             | Some l' -> Some (Name.to_string n_user, l') in
          (Reporting.report_warning (Reporting.Warn_rename (l, Name.to_string n_org, via_opt, Name.to_string n_new, targ))) end 
  in
    n_fresh_opt
  end

let rename_defs_target targ consts (fixed_ren : (name_kind * Path.t * Path.t) list) p env defs =
  let fixed_renames : (Path.t * ( Ast.l * Path.t)) list = List.map (fun (_, p, n) -> (p, (Ast.Unknown, n))) fixed_ren in
  let explicit_renames : (Path.t * ( Ast.l * Path.t)) list = get_renames_of_defs targ [] defs in
  let explicit_renames_fun (rL : (Path.t * ( Ast.l * Path.t)) list) path n = 
     (try 
        let p = Path.mk_path path n in
        let compare_f (p', _) = (Path.compare p' p = 0)  in
        let (_, (l, r)) = List.find compare_f rL
      in Some (l, r) with Not_found -> None) in
  let f_ext = extend_rename_fun (explicit_renames_fun fixed_renames) (explicit_renames_fun explicit_renames) (compute_target_rename_f targ) targ in 

  (* remove the library constants from the set of names to avoid *)
  let renames_comp = compute_renames targ [] f_ext (NKmap.empty, consts) env in
  let (renames, _) = add_renames renames_comp fixed_ren in
    rename_defs renames p defs


let rename_nested_module p env defs =
  let (renames, _) = compute_renames None [] compute_module_rename_f (NKmap.empty, NameSet.empty) env in
    rename_defs renames p defs

let flatten_modules_macro path env ((d,s),l) =
  let l_unk = Ast.Trans("flatten_modules", Some l) in
    match d with
      | Module(sk1,n,sk2,sk3,ds,sk4) ->
          let mod_shell = ((Module(sk1,n,sk2,sk3,[],sk4),s),l) in
          let com = ((Comment(mod_shell),None),l_unk) in
            Some((env,com::ds))
      | _ -> None

let flatten_modules n e d = 
  snd (Def_trans.process_defs [] flatten_modules_macro n e d)
