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

open Types
open Typed_ast
open Coq_backend_utils



(* -------------------------------------------------------------------------- *)
(* check names of ids                                                         *)
(* -------------------------------------------------------------------------- *)

(* Code to check that identifiers in type checked program conform to regular expressions specified in type definitions *)
let check_id_restrict_e env (e : Typed_ast.exp) : unit =
 let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  match C.exp_to_term e with
  | Var(n) -> let id = Name.to_string (Name.strip_lskip n) in
              let head_norm_type = Types.head_norm env.t_env (exp_to_typ e) in
              begin
              match head_norm_type.t with
                 | Tapp(_,p) -> (match Pfmap.apply env.t_env p with
                    | None | Some(Tc_class _) ->
                        raise (Reporting_basic.err_general true Ast.Unknown "invariant in typechecking identifier broken")
                    | Some(Tc_type { type_varname_regexp = None }) -> ()
                    | Some(Tc_type { type_varname_regexp = Some(restrict, regexp) }) ->
                       if (Str.string_match regexp id 0)
                         then ()
                         else  raise (Reporting_basic.err_type_pp (exp_to_locn e) 
                               ("variables with type " ^ t_to_string (exp_to_typ e) ^ " are restricted to names matching the regular expression " ^ restrict)
                               Name.pp (Name.strip_lskip n)))
                 | _ -> ()
              end
  | _ -> ()


let check_id_restrict_p env p = match p.term with
  | P_var(n) -> let id = Name.to_string (Name.strip_lskip n) in
              let head_norm_type = Types.head_norm env.t_env p.typ in
              begin
              match head_norm_type.t with
                 | Tapp(_,path) -> (match Pfmap.apply env.t_env path with
                    | None | Some(Tc_class _) -> raise (Reporting_basic.err_general true Ast.Unknown "invariant broken when checking id_restrict_p")
                    | Some(Tc_type { type_varname_regexp = None }) -> ()
                    | Some(Tc_type { type_varname_regexp = Some(restrict, regexp) }) ->
                       if (Str.string_match regexp id 0)
                         then ()
                         else  raise (Reporting_basic.err_type_pp p.locn 
                               ("variables with type " ^t_to_string p.typ ^ " are restricted to names matching the regular expression " ^ restrict)
                               Name.pp (Name.strip_lskip n) ))
                 | _ -> ()
              end
  | _ -> ()



(** Checks whether a src_t has a decidable equality.  Function types are
    the only types which do not.
 *)
let rec has_decidable_equality_src_t (src_t : src_t) : bool =
  match src_t.term with
    | Typ_wild _ -> true
    | Typ_var (_, _) -> true
    | Typ_len _ -> true
    | Typ_fn (_, _, _) -> false
    | Typ_tup src_ts ->
        let seplist = Seplist.to_list src_ts in
          List.for_all has_decidable_equality_src_t seplist
    | Typ_app (_, src_ts) -> List.for_all has_decidable_equality_src_t src_ts
    | Typ_backend (_, src_ts) -> List.for_all has_decidable_equality_src_t src_ts
    | Typ_paren (_, src_t, _) -> has_decidable_equality_src_t src_t
;;

(** Checks whether a type expression has a decidable equality.  [in_module_scope]
    signals whether we are inside a module or not, [true] if we are inside a module,
    [false] when we are not.
 *)
let has_decidable_equality_texp (t : texp) (in_module_scope : bool) : bool =
  match t with
    | Te_opaque -> in_module_scope
    | Te_abbrev (_, src_t) -> has_decidable_equality_src_t src_t
    | Te_record (_, _, seplist, _) ->
        let src_ts = Seplist.to_list seplist in
          List.for_all (fun (_, _, _, z) -> has_decidable_equality_src_t z) src_ts
    | Te_variant (_, seplist) ->
        let src_t_seplist = Seplist.to_list seplist in
          List.for_all (fun (_, _, _, seplist) ->
            let src_ts = Seplist.to_list seplist in
              List.for_all has_decidable_equality_src_t src_ts
          ) src_t_seplist
;;

(** Checks whether a definition has a decidable equality (only interesting
    cases are for type definitions and modules, which may also define a
    type).
 *)
let rec check_decidable_equality_def' env (((d, _), l, _) : def) (in_module_scope : bool) : unit =
  match d with
    | Type_def (_, seplist) ->
        let texps = Seplist.to_list seplist in
        let _ =
          List.map (fun ((name, _), _, _, z, _) ->
            if has_decidable_equality_texp z in_module_scope then
              ()
            else
              let name = Name.strip_lskip name in
              let sname = Name.to_string name in
                Reporting.report_warning env (Reporting.Warn_no_decidable_equality (l, sname))
          ) texps
        in
          ()
    | Module (_, _, _, _, _, defs, _) ->
        let _ =
          List.map (fun x -> check_decidable_equality_def' env x true)
        in
          ()
    | _ -> ()
;;

let check_decidable_equality_def env (d : def) : unit =
  check_decidable_equality_def' env d false
;;

(** Definition of strict positivity, a la Coq, for an inductive data type X.
 *)

(** Utilities for working with paths.
 *)

let path_eq (x : Name.t) (p : Path.t) : bool =
  let (tail, head) = Path.to_name_list p in
    x = head && tail = []
;;

(** Checks whether a name [x] occurs in a src_t [s].
 *)
let rec occurs_src_t (x : Name.t) (s : src_t) : bool =
  match s.term with
    | Typ_wild _ -> false
    | Typ_var _ -> false
    | Typ_len _ -> false
    | Typ_fn (dom, _, rng) ->
        occurs_src_t x dom ||
          occurs_src_t x rng
    | Typ_tup src_ts ->
        let src_ts = Seplist.to_list src_ts in
          List.exists (occurs_src_t x) src_ts
    | Typ_app (path, src_ts) ->
        let (tail, head) = Path.to_name_list path.descr in
          if head = x && tail = [] then
            true
          else
            List.exists (occurs_src_t x) src_ts
    | Typ_backend (_, src_ts) ->
        List.exists (occurs_src_t x) src_ts
    | Typ_paren (_, src_t, _) -> occurs_src_t x src_t
;;

module InductiveMap = Map.Make (
  struct
    type t = Name.t
    let compare = Pervasives.compare
  end)
;;

(**
    The type of a constructor T satisfies the nested positivity condition for X if:

    * T = (U -> V) with X occurring strictly positively in U and V satisfying the
      nested positivity condition for X.
 *)

let rec nested_positivity_condition (inductive_types : src_t list InductiveMap.t) (x : Name.t) (s : src_t) : bool =
  match s.term with
    | Typ_fn (dom, _, rng) ->
        occurs_strictly_positively inductive_types x dom &&
          nested_positivity_condition inductive_types x rng
    | _ -> true

(**
    X occurs strictly positively in T if:

    * X does not occur in T.
    * T = (X t1 ... tn) and X does not occur in ti for any i.
    * T = (U -> V) with X not occuring in U but occurs only strictly positively in V.
    * T = (I a1 ... an) an inductive type with constructors (Ci : p1i -> ... pni -> ci)
      and the instantiated types of the constructor (Ci[an := pn]) satisfy the nested
      positivity condition for X.
*)

and occurs_strictly_positively (inductive_types : src_t list InductiveMap.t) (x : Name.t) (s : src_t) : bool =
  match s.term with
    | Typ_wild _ -> true
    | Typ_var _ -> true
    | Typ_len _ -> true
    | Typ_fn (dom, _, rng) ->
        if occurs_src_t x dom then
          false
        else
          occurs_strictly_positively inductive_types x rng
    | Typ_tup src_ts -> true
    | Typ_app (path, src_ts) ->
        let (tail, head) = Path.to_name_list path.descr in
          if InductiveMap.mem head inductive_types then
            let ctors = InductiveMap.find head inductive_types in
              List.for_all (nested_positivity_condition inductive_types x) ctors
          else
            List.for_all (fun y -> not (occurs_src_t x y)) src_ts
    | Typ_backend (path, src_ts) ->
          List.for_all (fun y -> not (occurs_src_t x y)) src_ts
    | Typ_paren (_, src_t, _) -> occurs_strictly_positively inductive_types x src_t

(**
    A constructor type T satisfies the strict positivity condition if:

    * T = (X t1 ... tn) and T does not occur freely in ti for any i.
    * T = (U -> V) with X occurring strictly positively in U and V satisfies
      the strict positivity condition.
 *)

and strict_positivity_condition (inductive_types : src_t list InductiveMap.t) (x : Name.t) (s : src_t) : bool =
  match s.term with
    | Typ_wild _ -> true
    | Typ_var _ -> true
    | Typ_len _ -> true
    | Typ_fn (dom, _, rng) ->
        occurs_strictly_positively inductive_types x dom &&
          strict_positivity_condition inductive_types x rng
    | Typ_tup seplist -> true (* ??? how do you handle tuples in a ctor type?
        let src_ts = Seplist.to_list seplist in
          List.for_all (strict_positivity_condition x) src_ts *)
    | (Typ_app (_, src_ts) | Typ_backend (_, src_ts)) ->
        List.for_all (fun y -> not (occurs_src_t x y)) src_ts
    | Typ_paren (_, src_t, _) -> strict_positivity_condition inductive_types x src_t
;;

let check_positivity_condition_texp (inductive_types : src_t list InductiveMap.t) (x : Name.t) (t : texp) : bool =
  match t with
    | Te_opaque -> true
    | Te_abbrev _ -> true
    | Te_record _ -> true
    | Te_variant (_, seplist) ->
      let seplist = Seplist.to_list seplist in
        List.for_all (fun (_, _, _, z) ->
          let src_ts = Seplist.to_list z in
            List.for_all (strict_positivity_condition inductive_types x) src_ts
        ) seplist
;;

let gather_inductive_types_texp (name : Name.t) (t : texp) : src_t list InductiveMap.t =
  match t with
    | Te_variant (_, seplist) ->
        let src_ts = Seplist.to_list seplist in
        let mapped =
          List.map (fun (_, _, _, src_ts) ->
            let src_ts = Seplist.to_list src_ts in
              InductiveMap.add name src_ts InductiveMap.empty
          ) src_ts
        in
          List.fold_right (InductiveMap.merge (fun key left right -> left)) mapped InductiveMap.empty
    | _ -> InductiveMap.empty
;;

let gather_inductive_types (((d, _), _, _) : def) : src_t list InductiveMap.t =
  match d with
    | Type_def (_, seplist) ->
      let texps = Seplist.to_list seplist in
      let mapped =
        List.map (fun ((name, _), _, _, texp, _) ->
          let name = Name.strip_lskip name in
            gather_inductive_types_texp name texp
        ) texps
      in
        List.fold_right (InductiveMap.merge (fun key left right -> left)) mapped InductiveMap.empty
    | _ -> InductiveMap.empty
;;

let check_positivity_condition_def (d : def) : unit =
  let inductive_types = gather_inductive_types d in
  let ((d, _), _, _) = d in
    match d with
      | Type_def (_, seplist) ->
          let texps = Seplist.to_list seplist in
          let _ =
            List.map (fun ((name, _), _, _, texp, _) ->
              let name = Name.strip_lskip name in
              let sname = Name.to_string name in
                if check_positivity_condition_texp inductive_types name texp then
                  ()
                else
                  prerr_endline ("Warning: inductive type " ^ sname ^ " is not strictly positive.")
            ) texps
          in
            ()
      (* XXX: inductive relations too? *)
      | _ -> ()
;;
