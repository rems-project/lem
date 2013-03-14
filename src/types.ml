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

type tnvar = 
  | Ty of Tyvar.t
  | Nv of Nvar.t

let pp_tnvar ppf tnv =
  match tnv with
  | Ty(v) -> Tyvar.pp ppf v
  | Nv(v) -> Nvar.pp ppf v

let tnvar_to_rope tnv =
  match tnv with
  | Ty(v) -> Tyvar.to_rope v
  | Nv(v) -> Nvar.to_rope v

let tnvar_compare tn1 tn2 = match (tn1,tn2) with
  | (Ty v1,Ty v2) -> Tyvar.compare v1 v2
  | (Ty _ , _) -> 1
  | (_ , Ty _) -> -1
  | (Nv v1, Nv v2) -> Nvar.compare v1 v2

let tnvar_to_name = function
     Ty v -> Name.from_rope (Tyvar.to_rope v)
   | Nv v -> Name.from_rope (Nvar.to_rope v)

module TNvar = struct
  type t = tnvar
  let compare tn1 tn2 = tnvar_compare tn1 tn2
  let pp ppf tnv = pp_tnvar ppf tnv
end

module TNfmap = Finite_map.Fmap_map(TNvar)
module TNset' = Set.Make(TNvar)
module TNset = struct
  include TNset'
  let pp ppf tvset =
    Format.fprintf ppf "{@[%a@]}"
      (Pp.lst ",@ " TNvar.pp)
      (TNset'.elements tvset)
end

module Pfmap = Finite_map.Fmap_map(Path)

type t = { mutable t : t_aux }
and t_aux =
  | Tvar of Tyvar.t
  | Tfn of t * t
  | Ttup of t list
  | Tapp of t list * Path.t
  | Tne of nexp
  | Tuvar of t_uvar
and t_uvar = { index : int; mutable subst : t option }

and nexp = { mutable nexp : nexp_aux }
and nexp_aux = 
  | Nvar of Nvar.t
  | Nconst of int
  | Nadd of nexp * nexp
  | Nmult of nexp *nexp
  | Nneg of nexp
  | Nuvar of n_uvar
and n_uvar = { nindex : int; mutable nsubst : nexp option }

let free_vars t =
  let rec f t acc =
    match t.t with
      | Tvar(tv) -> TNset.add (Ty tv) acc
      | Tfn(t1,t2) -> f t2 (f t1 acc)
      | Ttup(ts) -> 
          List.fold_left (fun acc t -> f t acc) acc ts
      | Tapp(ts,_) ->
          List.fold_left (fun acc t -> f t acc) acc ts
      | Tne n -> f_n n acc
      | Tuvar _ -> assert false (*TVset.empty*)
   and f_n n acc = 
    match n.nexp with
      | Nvar(nv) -> TNset.add (Nv nv) acc
      | Nconst _ -> acc
      | Nadd(n1,n2) | Nmult(n1,n2) -> f_n n1 (f_n n2 acc)
      | Nneg(n) -> f_n n acc
      | Nuvar _ -> assert false
  in
    f t TNset.empty

let rec tnvar_to_tyvar_lst tnlst =
  match tnlst with 
    | [] -> []
    | Ty(tv)::tnlst -> tv::(tnvar_to_tyvar_lst tnlst)
    | Nv _ ::tnlst -> (tnvar_to_tyvar_lst tnlst)

let rec tnvar_to_nvar_lst tnlst =
  match tnlst with 
    | [] -> []
    | Ty _ ::tnlst -> (tnvar_to_nvar_lst tnlst)
    | Nv(n)::tnlst -> n::(tnvar_to_nvar_lst tnlst)

let rec tnvarp_to_tvarp_lst tplst =
   match tplst with
     | [] -> []
     | (p,Ty(tv))::tplst -> (p,tv)::(tnvarp_to_tvarp_lst tplst)
     | (_ , Nv _ )::tplst -> (tnvarp_to_tvarp_lst tplst)

let rec compare_nexp n1 n2 =
  if n1 = n2 then
    0
  else
    match (n1.nexp,n2.nexp) with
     | (Nvar(v1), Nvar(v2)) -> Nvar.compare v1 v2
     | (Nvar _ , _) -> 1
     | (_ , Nvar _) -> -1
     | (Nconst(c1),Nconst(c2)) -> 
       if c1 = c2 then 0
       else if c1 > c2 then 1 else -1
     | (Nconst _, _) -> 1
     | (_, Nconst _) -> -1
     | (Nadd(n1,n2),Nadd(n1',n2')) | (Nmult(n1,n2),Nmult(n1',n2')) ->
        let c = compare_nexp n1 n1' in
        if c = 0 then compare_nexp n2 n2'
        else c
     | (Nadd _, _) -> 1
     | (_,Nadd _) -> -1
     | (Nmult _ , _) -> 1
     | (_ , Nmult _) -> -1
     | (Nneg(n1),Nneg(n2)) -> compare_nexp n2 n1
     | (Nneg _, _) -> 1
     | (_,Nneg _) -> -1
     | (Nuvar(u1), Nuvar(u2)) -> 
        if u1 == u2 then
          0
        else
          match (u1.nsubst, u2.nsubst) with
            | (Some(n1), Some(n2)) ->
                compare_nexp n1 n2
            | (Some _, None) -> 1
            | (None, Some _) -> -1
            | (None, None) -> (*0*) compare u1.nindex u2.nindex

let rec compare t1 t2 =
  if t1 == t2 then
    0
  else
    match (t1.t,t2.t) with
    | (Tvar(tv1), Tvar (tv2)) ->
        Tyvar.compare tv1 tv2
    | (Tvar _, _) -> 1
    | (_, Tvar _) -> -1
    | (Tfn(t1,t2), Tfn(t3,t4)) ->
        let c = compare t1 t3 in
          if c = 0 then
            compare t2 t4
          else
            c
    | (Tfn _, _) -> 1
    | (_, Tfn _) -> -1
    | (Ttup(ts1), Ttup(ts2)) ->
        Util.compare_list compare ts1 ts2
    | (Ttup _, _) -> 1
    | (_, Ttup _) -> -1
    | (Tapp(ts1,p1), Tapp(ts2,p2)) -> 
        let c = Util.compare_list compare ts1 ts2 in
          if c = 0 then
            Path.compare p1 p2
          else
            c
    | (Tapp _, _) -> 1
    | (_, Tapp _) -> -1
    | (Tne(n1),Tne(n2)) -> compare_nexp n1 n2
    | (Tne _, _) -> 1
    | (_, Tne _) -> -1
    | (Tuvar(u1), Tuvar(u2)) -> 
        if u1 == u2 then
          0
        else
          match (u1.subst, u2.subst) with
            | (Some(t1), Some(t2)) ->
                compare t1 t2
            | (Some _, None) -> 1
            | (None, Some _) -> -1
            | (None, None) -> 0

module PT = struct
  type u = t
  type t = Path.t * u
  let compare (p1,t1) (p2,t2) =
    let c = Path.compare p1 p2 in
      if c = 0 then
        compare t1 t2
      else
        c
end

module PTset = Set.Make(PT)

let multi_fun (ts : t list) (t : t) : t =
  List.fold_right (fun t1 t2 -> { t = Tfn(t1,t2); }) ts t

let tnvar_to_type tnv =
 match tnv with
 | Ty(v) -> { t = Tvar(v) }
 | Nv(v) -> { t = Tne( { nexp = Nvar(v) } ) }

let rec tnvar_split tnvs = 
  match tnvs with
  | [] -> [],[]
  | (Ty v)::tnvs -> let (nvars,tvars) = tnvar_split tnvs in
     (nvars,(Ty v)::tvars)
  | (Nv v)::tnvs -> let (nvars,tvars) = tnvar_split tnvs in
     ((Nv v)::nvars,tvars)

let rec type_subst_aux (substs : t TNfmap.t) (t : t) = 
  match t.t with
    | Tvar(s) ->
        (match TNfmap.apply substs (Ty s) with
           | Some(t) -> Some(t)
           | None -> assert false)
    | Tfn(t1,t2) -> 
        begin
          match (type_subst_aux substs t1, type_subst_aux substs t2) with
            | (None,None) -> None
            | (Some(t),None) -> Some({ t = Tfn(t, t2) })
            | (None,Some(t)) -> Some({ t = Tfn(t1, t) })
            | (Some(t1),Some(t2)) -> Some({ t = Tfn(t1, t2) })
        end
    | Ttup(ts) -> 
        begin
          match Util.map_changed (type_subst_aux substs) ts with
            | None -> None
            | Some(ts) -> Some({ t = Ttup(ts) })
        end
    | Tapp(ts,p) -> 
        begin
          match Util.map_changed (type_subst_aux substs) ts with
            | None -> None
            | Some(ts) -> Some({ t = Tapp(ts,p) })
        end
    | Tne(n) -> 
        begin
          match (nexp_subst substs n) with
            | n,false -> None
            | n,true -> Some({t = Tne(n)})
        end
    | Tuvar _ -> 
        assert false

and nexp_subst_aux (substs : t TNfmap.t) (n: nexp) =
  match n.nexp with
    | Nvar(s) ->
        (match TNfmap.apply substs (Nv s) with
           | Some({t = Tne(n)}) -> Some(n)
           | _ -> assert false)
    | Nconst _ -> None
    | Nadd(n1,n2) -> 
        begin
          match (nexp_subst_aux substs n1, nexp_subst_aux substs n2) with
            | (None,None) -> None
            | (Some(n),None) -> Some({ nexp = Nadd(n, n2) })
            | (None,Some(n)) -> Some({ nexp = Nadd(n1, n) })
            | (Some(n1),Some(n2)) -> Some({ nexp = Nadd(n1, n2) })
        end
    | Nmult(n1,n2) -> 
        begin
          match (nexp_subst_aux substs n1, nexp_subst_aux substs n2) with
            | (None,None) -> None
            | (Some(n),None) -> Some({ nexp = Nmult(n, n2) })
            | (None,Some(n)) -> Some({ nexp = Nmult(n1, n) })
            | (Some(n1),Some(n2)) -> Some({ nexp = Nmult(n1, n2) })
        end
    | Nneg(n) ->
        begin
        match nexp_subst_aux substs n with
         | None -> None
         | Some(n) -> Some({nexp = Nneg(n)})
        end
    | Nuvar _ -> assert false

and nexp_subst (substs : t TNfmap.t) (n : nexp) : nexp * bool = 
  if TNfmap.is_empty substs then
    n, false
  else
    match nexp_subst_aux substs n with
      | None -> n,false
      | Some(n) -> n,true

let type_subst (substs : t TNfmap.t) (t : t) : t = 
  if TNfmap.is_empty substs then
    t
  else
    match type_subst_aux substs t with
      | None -> t
      | Some(t) -> t

let rec resolve_subst (t : t) : t = match t.t with
  | Tuvar({ subst=Some(t') } as u) ->
      let t'' = resolve_subst t' in
        (match t''.t with
           | Tuvar(_) ->
               u.subst <- Some(t'');
               t''
           | x -> 
               t.t <- x;
               t)
  | _ ->
      t

let rec resolve_nexp_subst (n : nexp) : nexp = match n.nexp with
  | Nuvar({ nsubst = Some(n')} as u) ->
     let n'' = resolve_nexp_subst n' in
      (match n''.nexp with
        | Nuvar(_) -> 
          u.nsubst <- Some(n'');
          n''
        | x -> n.nexp <- x; n)
   | _ -> n

type tc_def = 
  | Tc_type of tnvar list * t option * string option
  | Tc_class of tnvar * (Name.t * t) list

type type_defs = tc_def Pfmap.t

type instance = tnvar list * (Path.t * tnvar) list * t * Name.t list

module IM = Map.Make(struct type t = int let compare = Pervasives.compare end)
open Format
open Pp

let rec pp_type ppf t =
  pp_open_box ppf 0;
  (match t.t with
     | Tvar(tv) ->
         Tyvar.pp ppf tv
     | Tfn(t1,t2) ->
         fprintf ppf "(@[%a@])@ ->@ %a"
           pp_type t1
           pp_type t2
     | Ttup(ts) ->
         fprintf ppf "(@[%a@])"
           (lst "@ *@ " pp_type) ts
     | Tapp([],p) ->
         Path.pp ppf p
     | Tapp([t],p) ->
         fprintf ppf "%a@ %a"
           Path.pp p
           pp_type t
     | Tapp(ts,p) ->
         fprintf ppf "%a @[%a@]"
           Path.pp p
           (lst "@ " pp_type) ts
     | Tne(n) -> fprintf ppf "%a" 
                   pp_nexp n
     | Tuvar(u) ->
         fprintf ppf "_");
         (*
         fprintf ppf "<@[%d,@ %a@]>" 
           u.index
           (opt pp_type) u.subst);
          *)
  pp_close_box ppf ()
and
 pp_nexp ppf n =
  pp_open_box ppf 0;
  (match n.nexp with
     | Nuvar nu -> fprintf ppf "_"(*  fprintf ppf "_ (%d)" nu.nindex *)
     | Nvar(nv) ->
         Nvar.pp ppf nv
     | Nconst(i) ->
         fprintf ppf "%d" i
     | Nadd(i,j) ->
         fprintf ppf "%a + %a"
             pp_nexp i
             pp_nexp j
     | Nmult(i,j) ->
         fprintf ppf "%a * %a" 
            pp_nexp i
            pp_nexp j
     | Nneg(n) -> fprintf ppf "- %a"
            pp_nexp n);
  pp_close_box ppf ()


let pp_tc ppf = function
  | Tc_type(tvs, topt, _) ->
      begin
        match topt with
          | None -> fprintf ppf "%s" (string_of_int (List.length tvs))
          | Some(t) -> fprintf ppf "%a" pp_type t
      end
  | Tc_class _ ->
      (*TODO*)
      ()

let pp_tdefs ppf tds =
  Pfmap.pp_map Path.pp pp_tc ppf tds

let pp_class_constraint ppf (p, tv) =
  fprintf ppf "(@[%a@ %a@])"
    Path.pp p
    pp_tnvar tv

let pp_instance_constraint ppf (p, t) =
  fprintf ppf "(@[%a@ %a@])"
    Path.pp p
    pp_type t

let pp_instance ppf (tyvars, constraints, t, p) =
  fprintf ppf "@[<2>forall@ (@[%a@]).@ @[%a@]@ =>@ %a@]@ (%a)"
    (lst ",@," pp_tnvar) tyvars
    (lst "@ " pp_class_constraint) constraints
    pp_type t
    (lst "." Name.pp) p

let t_to_string t =
  pp_to_string (fun ppf -> pp_type ppf t)

let t_to_var_name t =
  let aux t = match t.t with
     | Tvar(tv) -> "x"
     | Tfn(t1,t2) -> "f"
     | Ttup(ts) -> "p"
     | Tapp(ts,p) -> Name.to_string (Path.get_name p)
     | Tne(n) -> "x"
     | Tuvar(u) -> "x"
  in 
  let n_s = String.sub (aux t) 0 1 in
  let n_s' = let c = Char.code (String.get n_s 0) in 
             if 96 < c && c < 123 then n_s else "x" in
  Name.from_rope (Ulib.Text.of_string n_s')

let nexp_to_string n =
  pp_to_string (fun ppf -> pp_nexp ppf n)

let rec head_norm (d : type_defs) (t : t) : t = 
  let t = resolve_subst t in
    match t.t with
      | Tapp(ts,p) ->
          (match Pfmap.apply d p with
             | None ->
                 (*
                 Path.pp Format.std_formatter p;
                 Format.fprintf Format.std_formatter "@\n";
                 pp_tdefs Format.std_formatter d;
                 Format.fprintf Format.std_formatter "@\n";
                  *)
                 assert false
             | Some(Tc_type(_,None,_)) -> t
             | Some(Tc_type(tvs,Some(t),_)) ->
                 head_norm d (type_subst (TNfmap.from_list2 tvs ts) t)
             | Some(Tc_class _) ->
                 assert false)
      | _ -> 
          t

let t_to_tnv t =
  match t.t with
    | Tvar(tv) -> Ty tv
    | Tne({ nexp = Nvar(nv)}) -> Nv nv
    | _ -> assert false

let nexps_match n_pat n =
 (* TODO think about when and where to normalize *)
 match (n_pat.nexp,n.nexp) with
  | (Nvar(n),_) -> true
  | (Nconst(n),Nconst(n')) -> n=n'
  | _ -> false

let types_match t_pat t =
  match (t_pat.t,t.t) with
    | (Tvar(tv), _) -> true
    | (Tfn(tv1,tv2), Tfn(t1,t2)) -> true
    | (Ttup(tvs), Ttup(ts)) ->
        List.length tvs = List.length ts
    | (Tapp(tvs,p), Tapp(ts,p')) ->
        Path.compare p p' = 0
    | (Tne(n),Tne(n')) -> nexps_match n n'
    | (Tuvar _, _) -> assert false
    | _ -> false

let do_nexp_match n_pat n =
  (* TODO think about when and where to normalize *)
  match (n_pat.nexp,n.nexp) with
    | (Nvar(n'),_) -> TNfmap.from_list [(Nv n'),{t = Tne(n)}]
    | (Nconst(n),_) -> TNfmap.empty
    | _ -> assert false

let do_type_match t_pat t =
  match (t_pat.t,t.t) with
    | (Tvar(tv), _) -> TNfmap.from_list [(Ty tv),t]
    | (Tfn(tv1,tv2), Tfn(t1,t2)) ->
        TNfmap.from_list [(t_to_tnv tv1,t1); (t_to_tnv tv2,t2)]
    | (Ttup(tvs), Ttup(ts)) ->
        TNfmap.from_list2 (List.map t_to_tnv tvs) ts
    | (Tapp(tvs,p), Tapp(ts,p')) ->
        TNfmap.from_list2 (List.map t_to_tnv tvs) ts
    | (Tne(n),Tne(n')) -> do_nexp_match n n'
    | _ -> assert false

let rec get_matching_instance d (p,t) instances = 
  let t = head_norm d t in 
    match Pfmap.apply instances p with
      | None -> None
      | Some(possibilities) ->
          try
            let (tvs,cs,t',p) = 
              List.find (fun (tvs,cs,t',p) -> types_match t' t) possibilities
            in
            let subst = do_type_match t' t in
              Some(p,
                   subst,
                   List.map (fun (p, tnv) ->
                               (p, 
                                match TNfmap.apply subst tnv with
                                  | Some(t) -> t
                                  | None -> assert false))
                     cs)
          with
              Not_found -> None

let type_mismatch l m t1 t2 = 
  let t1 = t_to_string t1 in
  let t2 = t_to_string t2 in
    raise (Ident.No_type(l, "type mismatch:\n" (* ^ m ^ "\n"*) ^ t1 ^ "\nand\n" ^ t2))

let nexp_mismatch l n1 n2 =
  let n1 = nexp_to_string n1 in
  let n2 = nexp_to_string n2 in
    raise (Ident.No_type(l, "numeric expression mismatch:\n" ^ n1 ^ "\nand\n" ^ n2))

(* Converts to linear normal form, summation of (optionally constant-multiplied) variables, with the "smallest" variable on the right *)
let normalize nexp =
 let make_n n = {nexp = n} in
  let make_mul n i = match i with 
                    | 0 -> make_n (Nconst 0)
                    | 1 -> n
                    | _ -> (make_n (Nmult (n,make_n (Nconst i)))) in 
  let make_ordered cl cr nl nr i v =
    match (compare_nexp cl cr) with
      | -1 -> (make_n (Nadd(nr,nl)))
      | 0 -> make_mul v i
      | _ -> (make_n (Nadd(nl,nr))) in
 let rec norm nexp = 
    (* let _ = fprintf std_formatter "norm of %a@ \n" pp_nexp nexp in *)
    match nexp.nexp with
    | Nvar _ | Nconst _ | Nuvar _ -> nexp
    | Nneg(n) -> (
       let n' = norm n in
       match n'.nexp with
        | Nconst(i) -> make_n (Nconst(-1 * i))
        | _ -> norm (make_n (Nmult(n',(make_n (Nconst (-1)))))))
    | Nmult(n1,n2) -> (
       let n1',n2' = norm n1,norm n2 in
       let n1',n2' = sort n1',sort n2' in 
       match n1'.nexp,n2'.nexp with
        | Nconst i, Nconst j -> make_n (Nconst (i*j))
        | Nconst 1, _ -> n2' | _, Nconst 1 -> n1'
        | Nvar _ , Nconst _ | Nuvar _ , Nconst _  -> make_n (Nmult(n1',n2'))
        | Nconst _ , Nvar _ | Nconst _ , Nuvar _ -> make_n (Nmult(n2',n1'))
        | (Nconst i as n) , Nadd(n1,n2) | Nadd(n1,n2), (Nconst i as n) ->
          let n1 = norm (make_n (Nmult((make_n n),n1))) in
          let n2 = norm (make_n (Nmult((make_n n),n2))) in
          let n1 = sort n1 in
          let n2 = sort n2 in
          make_n (Nadd(n1,n2))
        | (Nconst i as n) , Nmult(n1,n2) | Nmult(n1,n2), (Nconst i as n) ->
          (match n1.nexp with
            | Nvar _ | Nuvar _ -> let n2 = norm (make_n (Nmult((make_n n), n2))) in
                                  let n2 = sort n2 in
                                  make_n (Nmult(n1,n2))
            | _ -> assert false)
        | _ -> assert false ) (*TODO KG Needs to be an actualy error, as must mean that a variable is multiplied by a variable, somewhere *)
    | Nadd(n1,n2) -> (
      let n1',n2' = norm n1,norm n2 in
      let n1',n2' = sort n1',sort n2' in 
      match n1'.nexp,n2'.nexp with
        | Nconst i, Nconst j -> make_n (Nconst(i+j))
        | _,_ -> make_n (Nadd(n1',n2')))
  and
    sort nexp = 
     (* let _ = fprintf std_formatter "sort of %a@ \n" pp_nexp nexp in *)
     match nexp.nexp with 
     | Nvar _ | Nconst _ | Nuvar _ | Nmult _ | Nneg _ -> nexp
     | Nadd(n1,n2) ->
       let n1,n2 = sort n1, sort n2 in
        begin match n1.nexp,n2.nexp with
         | Nconst i , Nconst j -> make_n (Nconst (i+j))
         | Nconst 0 , n | n , Nconst 0 -> make_n n
         | Nconst _ , _ -> make_n (Nadd(n1,n2))
         | _ , Nconst _ -> make_n (Nadd(n2,n1))
         | Nuvar _ , Nuvar _ | Nuvar _ , Nvar _ | Nvar _ , Nuvar _ | Nvar _ , Nvar _ -> 
           make_ordered n1 n2 n1 n2 2 n1
         | Nvar _, Nmult(v,n) | Nuvar _, Nmult(v,n) ->
           (match v.nexp,n.nexp with 
            | Nvar _,Nconst i | Nuvar _,Nconst i -> 
              make_ordered n1 v n1 n2 (i+1) n1
             | _ -> assert false)
         | Nmult(v,n), Nvar _ | Nmult(v,n), Nuvar _ ->
              (match v.nexp,n.nexp with 
               | Nvar _ ,Nconst i | Nuvar _, Nconst i -> 
                 make_ordered v n2 n1 n2 (i+1) n2
               | _ -> assert false)
         | Nmult(var1,nc1),Nmult(var2,nc2) ->
              (match var1.nexp,nc1.nexp,var2.nexp,nc2.nexp with 
               | _, Nconst i1, _, Nconst i2 ->
                 make_ordered var1 var2 n1 n2 (i1+i2) var1  
               | _ -> assert false)
         | Nadd(n1l,n1r),Nadd(n2l,n2r) ->
               (match compare_nexp n1r n2r with
                 | -1 -> let sorted = sort (make_n (Nadd(n1l,n2))) in
                         (match sorted.nexp with
                          | Nconst 0 -> n1r
                          | _ -> sort (make_n ( Nadd(sorted, n1r))))
                | 0 -> let rightmost = sort (make_n (Nadd(n1r,n2r))) in
                       let sorted = sort (make_n (Nadd(n1l,n2l))) in
                         (match rightmost.nexp,sorted.nexp with
                           | Nconst 0, n | n, Nconst 0 -> make_n n
                           | _ -> sort (make_n (Nadd (sorted,rightmost))))
                | _ -> let sorted = sort (make_n (Nadd(n1,n2l))) in
                        (match sorted.nexp with
                         | Nconst 0 -> n2r
                         | _ -> sort (make_n ( Nadd (sorted, n2r)))))
         | Nadd(n1l,n1r),n | n, Nadd(n1l,n1r)->
              let sorted = sort (make_n (Nadd(n1r,(make_n n)))) in
              (match sorted.nexp with 
                 | Nadd(nb,ns) -> 
                   let sorted_left = sort (make_n (Nadd (n1l, nb))) in
                   (match sorted_left.nexp with
                     | Nconst 0 -> ns
                     | _ -> make_n (Nadd(sorted_left,ns)))
                 | Nconst 0 -> n1l
                 | _ -> make_n(Nadd(n1l, sorted))
              )
         | Nneg _ , _ | _ , Nneg _ -> assert false (*Should have been removed in norm*)
       end
  in 
  let normal = norm nexp in
(*  let _  =  fprintf std_formatter "normal unsorted is %a@ \n" pp_nexp normal in*)
  let sorted = sort normal in
(*  let _ = fprintf std_formatter "sorted normal is %a@ \n" pp_nexp sorted in *)
  sorted

let rec assert_equal l m (d : type_defs) (t1 : t) (t2 : t) : unit =
  if t1 == t2 then
    ()
  else
    let t1 = head_norm d t1 in
    let t2 = head_norm d t2 in
      match (t1.t,t2.t) with
        | (Tuvar _, _) -> type_mismatch l m t1 t2
        | (_, Tuvar _) -> type_mismatch l m t1 t2
        | (Tvar(s1), Tvar(s2)) ->
            if Tyvar.compare s1 s2 = 0 then
              ()
            else
              type_mismatch l m t1 t2
        | (Tfn(t1,t2), Tfn(t3,t4)) ->
            assert_equal l m d t1 t3;
            assert_equal l m d t2 t4
        | (Ttup(ts1), Ttup(ts2)) -> 
            if List.length ts1 = List.length ts2 then
              assert_equal_lists l m d ts1 ts2
            else 
              type_mismatch l m t1 t2
        | (Tapp(args1,p1), Tapp(args2,p2)) ->
            if Path.compare p1 p2 = 0 && List.length args1 = List.length args2 then
              assert_equal_lists l m d args1 args2
            else
              type_mismatch l m t1 t2
        | (Tne(n1),Tne(n2)) -> assert_equal_nexp l n1 n2
        | _ -> 
            type_mismatch l m t1 t2

and assert_equal_lists l m d ts1 ts2 =
  List.iter2 (assert_equal l m d) ts1 ts2

and assert_equal_nexp l n1 n2 =
  if n1 == n2 then
    ()
  else let n1 = normalize n1 in
       let n2 = normalize n2 in
       assert_equal_nexp_help l n1 n2

and assert_equal_nexp_help l n1 n2 =
  match (n1.nexp,n2.nexp) with
    | (Nuvar _ , _ ) -> nexp_mismatch l n1 n2
    | (_ , Nuvar _ ) -> nexp_mismatch l n1 n2
    | (Nvar(s1),Nvar(s2)) ->
      if Nvar.compare s1 s2 = 0 then
         ()
         else nexp_mismatch l n1 n2
    | (Nconst(i),Nconst(j)) -> if i = j then () else nexp_mismatch l n1 n2
    | (Nadd(n11,n12),Nadd(n21,n22)) | (Nmult(n11,n12),Nmult(n21,n22)) ->
       assert_equal_nexp l n11 n21;
       assert_equal_nexp l n12 n22
    | (Nneg(n1),Nneg(n2)) -> assert_equal_nexp l n1 n2
    | _ -> nexp_mismatch l n1 n2

let rec nexp_from_list nls = match nls with
    | [] -> assert false
    | [n] -> n
    | [n1;n2] -> {nexp = Nadd(n1,n2)}
    | n1::nls -> {nexp = Nadd(n1,(nexp_from_list nls))}

type range =
  | LtEq of nexp * nexp
  | EqZero of nexp
  | GtEq of nexp  * nexp

module type Constraint = sig
  val new_type : unit -> t
  val new_nexp : unit -> nexp
  val equate_types : Ast.l -> t -> t -> unit
  val in_range : Ast.l -> nexp -> nexp -> unit
  val add_constraint : Path.t -> t -> unit
  val add_length_constraint : range -> unit
  (*
  val equate_type_lists : Ast.l -> t list -> t list -> unit
   *)
  val add_tyvar : Tyvar.t -> unit 
  val add_nvar : Nvar.t -> unit
  (*
  val same_types : Ast.l -> t list -> t
  val dest_fn_type : Ast.l -> t -> t * t
   *)
  val inst_leftover_uvars : Ast.l -> TNset.t * (Path.t * tnvar) list
end

module type Global_defs = sig
  val d : type_defs 
  val i : (instance list) Pfmap.t 
end 

module Constraint (T : Global_defs) : Constraint = struct

  let next_uvar : int ref = ref 0
  let uvars : t list ref = ref []
  let tvars : TNset.t ref = ref TNset.empty

  let next_nuvar : int ref = ref 0
  let nuvars : nexp list ref = ref []
  let nvars : TNset.t ref = ref TNset.empty

  let class_constraints : (Path.t * t) list ref = ref []
  let length_constraints : range list ref = ref []

  let add_length_constraint r =
   length_constraints := r :: (!length_constraints)

  let new_type () : t =
    let i = !(next_uvar) in
      incr next_uvar;
      let t = { t = Tuvar({ index=i; subst=None }); } in
        uvars := t::!uvars;
        t

  let new_nexp () : nexp =
    let i = !(next_nuvar) in
      incr next_nuvar;
      let n = { nexp = Nuvar({ nindex = i; nsubst=None }); } in
        nuvars := n::!nuvars;
        n

  let add_tyvar (tv : Tyvar.t) : unit =
    tvars := TNset.add (Ty tv) (!tvars)

  let add_nvar (nv : Nvar.t) : unit = 
    nvars := TNset.add (Nv nv) (!nvars)

  let rec occurs_check (t_box : t) (t : t) : unit =
    let t = resolve_subst t in
      if t_box == t then
        raise (Ident.No_type(Ast.Unknown, "Failed occurs check"))
      else
        match t.t with
          | Tfn(t1,t2) ->
              occurs_check t_box t1;
              occurs_check t_box t2
          | Ttup(ts) ->
              List.iter (occurs_check t_box) ts
          | Tapp(ts,_) ->
              List.iter (occurs_check t_box) ts
          | _ ->
              ()

  let rec occurs_nexp_check (n_box : nexp) (n : nexp) : unit =
     let n = resolve_nexp_subst n in 
       if n_box == n then
          raise (Ident.No_type(Ast.Unknown, "Nexpressions failed occurs check"))
       else
          match n.nexp with
            | Nadd(n1,n2) | Nmult(n1,n2) -> 
                occurs_nexp_check n_box n1;
                occurs_nexp_check n_box n2;
            | Nneg(n) -> occurs_nexp_check n_box n;
            | _ -> ()

  let prim_equate_types (t_box : t) (t : t) : unit =
    let t = resolve_subst t in
      if t_box == t then
        ()
      else
        (occurs_check t_box t;
         match t.t with
           | Tuvar(_) ->
               (match t_box.t with
                  | Tuvar(u) ->
                      u.subst <- Some(t)
                  | _ ->
                      assert false)
           | _ ->
               t_box.t <- t.t)

  let rec equate_types (l : Ast.l) (t1 : t) (t2 : t) : unit =
    if t1 == t2 then
      ()
    else
    let t1 = head_norm T.d t1 in
    let t2 = head_norm T.d t2 in
      match (t1.t,t2.t) with
        | (Tuvar _, _) -> 
            prim_equate_types t1 t2
        | (_, Tuvar _) -> 
            prim_equate_types t2 t1
        | (Tvar(s1), Tvar(s2)) ->
            if Tyvar.compare s1 s2 = 0 then
              ()
            else
              type_mismatch l "equate_types" t1 t2
        | (Tfn(t1,t2), Tfn(t3,t4)) ->
            equate_types l t1 t3;
            equate_types l t2 t4
        | (Ttup(ts1), Ttup(ts2)) -> 
            if List.length ts1 = List.length ts2 then
              equate_type_lists l ts1 ts2
            else 
              type_mismatch l "equate_types" t1 t2
        | (Tapp(args1,p1), Tapp(args2,p2)) ->
            if Path.compare p1 p2 = 0 && List.length args1 = List.length args2 then
              equate_type_lists l args1 args2
            else
              type_mismatch l "equate_types" t1 t2
        | (Tne(n1),Tne(n2)) ->
           equate_nexps l n1 n2;
        | _ -> 
            type_mismatch l "equate_types" t1 t2

  and equate_type_lists l ts1 ts2 =
    List.iter2 (equate_types l) ts1 ts2

  and prim_equate_nexps (n_box : nexp) (n : nexp) : unit =
    let n = resolve_nexp_subst n in 
      if n_box == n then
        ()
      else
        (occurs_nexp_check n_box n; 
         match n.nexp with
           | Nuvar(_) ->
               (match n_box.nexp with
                  | Nuvar(u) ->
                      u.nsubst <- Some(n)
                  | _ ->
                      assert false)
           | _ ->
               n_box.nexp <- n.nexp)

  and equate_nexps_help l nexp1 nexp2 =
     match (nexp1.nexp,nexp2.nexp) with
       | (Nuvar _, _) -> prim_equate_nexps nexp1 nexp2
       | (_, Nuvar _) -> prim_equate_nexps nexp2 nexp1
       | Nvar(nv1),Nvar(nv2) -> if (Nvar.compare nv1 nv2) = 0 then () else nexp_mismatch l nexp1 nexp2
       | Nconst(i),Nconst(j) -> if i=j then () else nexp_mismatch l nexp1 nexp2
       | Nmult(nl1,nl2),Nmult(nr1,nr2) | Nadd(nl1,nl2),Nadd(nr1,nr2) ->
           equate_nexps_help l nl1 nr1;
           equate_nexps_help l nl2 nr2;
       | (Nneg(n1),Nneg(n2)) -> equate_nexps_help l n1 n2;
       | _ -> nexp_mismatch l nexp1 nexp2

  and equate_nexps l nexp1 nexp2 =
    if nexp1 == nexp2
      then ()
    else 
      let n1 = normalize nexp1 in
      let n2 = normalize nexp2 in
      let n3 = normalize { nexp = Nadd(n1, {nexp= Nneg n2}) } in
      match n3.nexp with
       | Nconst 0 -> ()
       | _ -> add_length_constraint (EqZero n3)
              ; equate_nexps_help l n1 n2 (*TODO remove me because this is a temporary solution until constraint solving is fully operational*)
       
  let in_range l vec_n n =
    let (len,ind) = (normalize vec_n,normalize n) in
    match (len.nexp,ind.nexp) with
     | (Nconst n, Nconst i) -> if ((i < n) && (i > 0)) then () else nexp_mismatch l len ind
     | (_,_) -> () (* Need to make these constraints *)

(*
  let equate_types l t1 t2 =
    fprintf std_formatter "%a@ =@ %a@\n"
      pp_type t1
      pp_type t2;
    equate_types l t1 t2;
    fprintf std_formatter "%a@ =@ %a@\n@\n"
      pp_type t1
      pp_type t2
 *)

  let add_constraint p t =
    class_constraints := (p,t) :: (!class_constraints)

  let cur_tyvar = ref 0

  let rec get_next_tvar (i : int) : (int * tnvar) =
    let tv = Ty (Tyvar.nth i) in
      if TNset.mem tv (!tvars) then
        get_next_tvar (i + 1) 
      else
        (i,tv)

  let next_tyvar () : tnvar =
    let (i,tv) = get_next_tvar !cur_tyvar in
      cur_tyvar := i+1;
      tv

  let cur_nvar = ref 0

  let rec get_next_nvar (i : int) : (int * tnvar) =
    let nv = Nv (Nvar.nth i) in
      if TNset.mem nv (!nvars) then
         get_next_nvar (i + 1)
      else
         (i,nv)

  let next_nvar () : tnvar =
    let (i,nv) = get_next_nvar !cur_nvar in
      cur_nvar := i+1;
      nv

  let rec num_nuvars n =
    match n.nexp with
    | Nuvar _ -> 1
    | Nadd (n1, n2) | Nmult(n1,n2) -> (num_nuvars n1) + (num_nuvars n2)
    | Nneg n -> num_nuvars n
    | _ -> 0

 let rec divide n i =
   let div i j v = if ((j mod i) = 0)
                   then {nexp = Nmult({nexp = Nconst (j/i)},v) }
                   else assert false (* case which needs fractions *) in
   match n.nexp with
   | Nvar _ -> assert false (* case which needs fractions *)
   | Nmult(n1,n2) -> (match n2.nexp with
                     | Nconst j -> div i j n1
                     | _ -> assert false)
   | Nadd(n1,n2) -> { nexp = Nadd((divide n1 i),(divide n2 i)) }
   | _ -> assert false (* normalizing says we shouldn't get here *)

  (*Solves a normalized constraint with one nuvar which must be equal to the rest of the term.
    The Nuvar should therefore be the rightmost term in a plus or solo *)
  let simple_solver n =
    match n.nexp with
    | Nuvar _ | Nmult _ -> () (* In these cases the nuvar is solo, nothing to solve *)
    | Nadd(n1,n2) -> (* Must be nuvar or multiplication of on right *)
      begin match n2.nexp with
        | Nuvar _ -> let n1 = normalize {nexp = (Nneg n1)} in
                     (n2.nexp <- n1.nexp)
        | Nmult(v,n2) -> (* v must be the nuvar *)
          begin match n2.nexp with
                | Nconst i -> let ni = fun _ -> { nexp = Nneg (if (i = 1) then n1 else (divide n1 i))} in
                              let n1 = if (i= -1) then n1 else normalize (ni ()) in
                  (v.nexp <- n1.nexp)
                | _ -> assert false
          end
        | _ -> assert false
       end
     | _ -> assert false

  let rec solve_numeric_constraints unresolved = function
    | [] -> unresolved
    | (EqZero n) :: n_constraints -> if (1 = (num_nuvars n)) (* Add case for zero (because nuvars have been constrained), term should now normalize to 0 or error *)
                                        then begin (simple_solver n); unresolved end
                                        else unresolved
    | LtEq(n1,n2):: n_constraints -> unresolved
    | GtEq(n1,n2):: n_constraints -> unresolved 

  let rec solve_constraints instances (unsolvable : PTset.t)= function
    | [] -> unsolvable 
    | (p,t) :: constraints ->
        match get_matching_instance T.d (p,t) instances with
          | None ->
              solve_constraints instances (PTset.add (p,t) unsolvable) constraints
          | Some((_,_,new_cs)) ->
              solve_constraints instances unsolvable (new_cs @ constraints)

  let check_constraint l (p,t) =
    match t.t with
      | Tvar(tv) -> (p,Ty tv)
      | Tne(n) -> (match n.nexp with
                   | Nvar(nv) -> (p, Nv nv)
                   | _ -> let t1 = Pp.pp_to_string (fun ppf -> pp_instance_constraint ppf (p, t)) in
                      raise (Ident.No_type(l, "unsatisfied type class constraint:\n" ^t1)))
      | _ -> 
          let t1 = 
            Pp.pp_to_string (fun ppf -> pp_instance_constraint ppf (p, t))
          in 
            raise (Ident.No_type(l, "unsatisfied type class constraint:\n" ^ t1))

  let inst_leftover_uvars l =  
    let used_tvs = ref TNset.empty in
    let inst t =
      let t' = resolve_subst t in
        match t'.t with
          | Tuvar(u) ->
              let nt = next_tyvar () in
                used_tvs := TNset.add nt !used_tvs;
                t'.t <- (match nt with | Ty nt -> Tvar(nt) | _ -> assert false);
                ignore (resolve_subst t)
          | _ -> ()
    in
    let used_nvs = ref TNset.empty in
    let inst_n n = 
      let n' = resolve_nexp_subst n in
        match n'.nexp with
          | Nuvar(u) ->
             let nn = next_nvar () in
               used_nvs := TNset.add nn !used_nvs;
               n'.nexp <- (match nn with | Nv nn -> Nvar(nn) | _ -> assert false);
               ignore (resolve_nexp_subst n)
          | _ -> ()
    in
      let ns = solve_numeric_constraints [] !length_constraints in
      List.iter inst (!uvars);
      List.iter inst_n (!nuvars);
      let cs = solve_constraints T.i PTset.empty !class_constraints in
        (TNset.union (TNset.union !tvars !used_tvs) 
                     (TNset.union !nvars !used_nvs), 
         List.map (check_constraint l) (PTset.elements cs))
end

let rec ftvs (ts : t list) (acc : TNset.t) : TNset.t = match ts with
  | [] -> acc
  | t::ts -> ftvs ts (ftv t acc)
and ftv (t : t) (acc : TNset.t) : TNset.t = match t.t with
  | Tvar(x) -> 
      TNset.add (Ty x) acc
  | Tfn(t1,t2) -> 
      ftv t2 (ftv t1 acc)
  | Ttup(ts) -> 
      ftvs ts acc
  | Tapp(ts,_) ->
      ftvs ts acc
  | Tne(n) -> fnv n acc
  | Tuvar(_) -> 
      acc
and fnv (n:nexp) (acc : TNset.t) : TNset.t = match n.nexp with
  | Nvar(x) ->
     TNset.add (Nv x) acc
  | Nadd(n1,n2) | Nmult(n1,n2) -> fnv n1 (fnv n2 acc)
  | Nneg(n) -> fnv n acc
  | Nconst _ | Nuvar _ -> acc

